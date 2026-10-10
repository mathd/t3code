import type { Certificate, Session, WebContents } from "electron";
import { BrowserWindow, session } from "electron";
import { writeFileStringAtomically } from "@t3tools/shared/atomicWrite";
import * as HostProcess from "@t3tools/shared/HostProcess";
import * as Context from "effect/Context";
import * as Crypto from "effect/Crypto";
import * as DateTime from "effect/DateTime";
import * as Effect from "effect/Effect";
import * as Hex from "effect/encoding/Hex";
import * as FileSystem from "effect/FileSystem";
import * as Layer from "effect/Layer";
import * as Option from "effect/Option";
import * as Path from "effect/Path";
import * as PlatformError from "effect/PlatformError";
import * as Result from "effect/Result";
import * as Schema from "effect/Schema";
import * as Semaphore from "effect/Semaphore";
import * as SynchronizedRef from "effect/SynchronizedRef";

import * as ElectronApp from "../electron/ElectronApp.ts";
import * as ElectronDialog from "../electron/ElectronDialog.ts";

const PREVIEW_PARTITION_PREFIX = "persist:t3code-preview-";
/**
 * Incognito partitions deliberately omit the `persist:` prefix, which is what
 * makes Chromium keep them in memory and discard them with the process. They
 * still carry the product prefix so `isPartition` can admit them — the
 * `will-attach-webview` gate rejects anything it does not recognise.
 */
const PREVIEW_EPHEMERAL_PARTITION_PREFIX = "t3code-preview-ephemeral-";
const PROFILE_PARTITION_MARKER = "profile-";

export type BrowserSessionPartitionNamespace = "profile";

// Permissions granted to preview web content. `clipboard-sanitized-write` is the
// Electron permission behind `navigator.clipboard.writeText()` — note it is NOT
// `clipboard-write`, which is not a valid Electron permission name. Async
// clipboard writes are gated by the permission *check* handler (not only the
// request handler), so both handlers must allow it; otherwise built-in "Copy"
// buttons — e.g. the Next.js / Vercel error overlay — fail with
// `Failed to execute 'writeText' on 'Clipboard': Write permission denied`.
const ALLOWED_PREVIEW_PERMISSIONS: ReadonlySet<string> = new Set([
  "clipboard-read",
  "clipboard-sanitized-write",
  "notifications",
  "geolocation",
  // The Fullscreen API. `DesktopWindow` disables HTML fullscreen window resizing
  // for the app window and every preview guest, so a page that goes fullscreen
  // fills its own webview instead of taking over the whole T3 window.
  "fullscreen",
  // Deliberately NOT local-fonts: preview sessions run untrusted web content,
  // and silently granting it would hand every page the user's installed-font
  // fingerprint (and font file bytes via FontData.blob()). The app's own font
  // picker runs in the main window session, which is unaffected by this list.
]);

/**
 * Schemes a preview page may never hand to the OS, even with the user's
 * consent: they read local files, run script, or are web pages that belong in
 * the preview itself.
 */
const NEVER_EXTERNAL_PROTOCOLS: ReadonlySet<string> = new Set([
  "about:",
  "blob:",
  "chrome:",
  "data:",
  "devtools:",
  "file:",
  "filesystem:",
  "http:",
  "https:",
  "javascript:",
  "view-source:",
]);

/**
 * The URL to offer the user when a preview page navigates to a custom scheme
 * such as `slack://` or `zoom://`, or `null` when it must stay denied.
 */
const externalProtocolPromptUrl = (rawUrl: string | undefined): string | null => {
  if (!rawUrl) return null;
  try {
    const url = new URL(rawUrl);
    return NEVER_EXTERNAL_PROTOCOLS.has(url.protocol) ? null : url.href;
  } catch {
    return null;
  }
};

const MAX_PROMPT_URL_LENGTH = 300;

/**
 * Certificate errors a user may accept for a preview page, with the reason the
 * prompt shows. Electron denies every other error.
 */
const OVERRIDABLE_CERTIFICATE_ERRORS: ReadonlyMap<string, string> = new Map([
  ["net::ERR_CERT_AUTHORITY_INVALID", "No trusted authority issued this certificate."],
  ["net::ERR_CERT_COMMON_NAME_INVALID", "This certificate is not for this address."],
  ["net::ERR_CERT_DATE_INVALID", "This certificate has expired or is not valid yet."],
]);

/**
 * The origin a certificate exception covers. A `wss:` socket uses the same TLS
 * endpoint as the page, so it shares the `https:` origin.
 */
const certificateOrigin = (rawUrl: string): string | null => {
  try {
    const url = new URL(rawUrl);
    return url.protocol === "https:" || url.protocol === "wss:" ? `https://${url.host}` : null;
  } catch {
    return null;
  }
};

/** One certificate a user accepted for a site. */
const CertificateApproval = Schema.Struct({
  origin: Schema.String.check(Schema.makeFilter((origin) => certificateOrigin(origin) === origin)),
  fingerprint: Schema.String.check(Schema.isPattern(/^\S+$/)),
  error: Schema.String.check(
    Schema.makeFilter((error) => OVERRIDABLE_CERTIFICATE_ERRORS.has(error)),
  ),
});
type CertificateApproval = typeof CertificateApproval.Type;

/** The key of an approval in memory. JSON keeps the three fields apart. */
const certificateApprovalKey = ({ origin, fingerprint, error }: CertificateApproval): string =>
  JSON.stringify([origin, fingerprint, error]);

/**
 * The approvals of a persistent profile, saved in its Session's storage folder.
 * A file with one invalid entry grants nothing, so the browser asks again.
 */
const CERTIFICATE_APPROVALS_FILE = "t3code-certificate-approvals.json";
const CertificateApprovalsFile = Schema.fromJsonString(
  Schema.Struct({ version: Schema.Literal(1), approvals: Schema.Array(CertificateApproval) }),
  { space: 2 },
);
const decodeCertificateApprovalsFile = Schema.decodeEffect(CertificateApprovalsFile);
const encodeCertificateApprovalsFile = Schema.encodeEffect(CertificateApprovalsFile);

const MAX_PROMPT_CERTIFICATE_NAME_LENGTH = 120;

/**
 * The server chooses its certificate names, so they cannot add lines or
 * control characters to the prompt.
 */
const promptCertificateName = (name: string): string => {
  const flat = name.replace(/[\p{Cc}\p{Cf}\s]+/gu, " ").trim();
  if (flat.length === 0) return "Unknown";
  return flat.length > MAX_PROMPT_CERTIFICATE_NAME_LENGTH
    ? `${flat.slice(0, MAX_PROMPT_CERTIFICATE_NAME_LENGTH)}…`
    : flat;
};

const promptCertificateDate = (seconds: number): string =>
  Option.match(DateTime.make(seconds * 1000), {
    onNone: () => "unknown",
    onSome: DateTime.formatIsoDateUtc,
  });

/** A tab that waits for the user's decision on a certificate. */
interface CertificateWaiter {
  readonly callback: (trusted: boolean) => void;
  /** Removes the listeners that drop this waiter when its navigation goes away. */
  readonly release: () => void;
}

/** The certificate approvals of one preview Session. */
interface CertificateTrust {
  /** By `certificateApprovalKey`. */
  readonly approvals: Map<string, CertificateApproval>;
  /** Where the approvals are saved, or `null` for incognito: its approvals end with the Session. */
  readonly file: string | null;
  /** Orders approval writes and clears, so that one cannot undo the other. */
  readonly lock: Semaphore.Semaphore;
  /** Clears that have not ended. While one runs, the Session trusts no certificate error. */
  clearing: number;
}

/** One open certificate prompt. Tabs that hit the same error share it. */
interface CertificatePrompt {
  /** The trust of the Session the prompt is for. */
  readonly trust: CertificateTrust;
  readonly approval: CertificateApproval;
  readonly key: string;
  readonly dialog: AbortController;
  readonly waiters: Set<CertificateWaiter>;
}

export class BrowserSessionPartitionDerivationError extends Schema.TaggedError<BrowserSessionPartitionDerivationError>()(
  "BrowserSessionPartitionDerivationError",
  {
    scope: Schema.String,
    cause: Schema.instanceOf(PlatformError.PlatformError),
  },
) {
  override get message(): string {
    return `Failed to derive a desktop preview browser partition for scope ${this.scope}.`;
  }
}

export class BrowserSessionCreationError extends Schema.TaggedError<BrowserSessionCreationError>()(
  "BrowserSessionCreationError",
  {
    scope: Schema.String,
    partition: Schema.String,
    cause: Schema.Defect(),
  },
) {
  override get message(): string {
    return `Failed to create a desktop preview browser session for scope ${this.scope} (partition ${this.partition}).`;
  }
}

export class BrowserSessionStorageClearError extends Schema.TaggedError<BrowserSessionStorageClearError>()(
  "BrowserSessionStorageClearError",
  {
    partition: Schema.String,
    /** Set when storage was cleared and a remaining cleanup step failed. */
    operation: Schema.optional(Schema.Literals(["closeConnections", "certificateApprovals"])),
    cause: Schema.Defect(),
  },
) {
  override get message(): string {
    if (this.operation === "closeConnections") {
      return `Cleared desktop preview browser storage for partition ${this.partition}, but failed to close its open connections.`;
    }
    if (this.operation === "certificateApprovals") {
      return `Cleared desktop preview browser storage for partition ${this.partition}, but failed to remove its saved certificate approvals.`;
    }
    return `Failed to clear desktop preview browser storage for partition ${this.partition}.`;
  }
}

export class BrowserSessionCacheClearError extends Schema.TaggedError<BrowserSessionCacheClearError>()(
  "BrowserSessionCacheClearError",
  {
    partition: Schema.String,
    cause: Schema.Defect(),
  },
) {
  override get message(): string {
    return `Failed to clear the desktop preview browser cache for partition ${this.partition}.`;
  }
}

export const BrowserSessionGetSessionError = Schema.Union([
  BrowserSessionPartitionDerivationError,
  BrowserSessionCreationError,
]);
export type BrowserSessionGetSessionError = typeof BrowserSessionGetSessionError.Type;

export const BrowserSessionError = Schema.Union([
  BrowserSessionPartitionDerivationError,
  BrowserSessionCreationError,
  BrowserSessionStorageClearError,
  BrowserSessionCacheClearError,
]);
export type BrowserSessionError = typeof BrowserSessionError.Type;

export class BrowserSession extends Context.Service<
  BrowserSession,
  {
    readonly getPartition: (
      scope?: string,
      persistent?: boolean,
      namespace?: BrowserSessionPartitionNamespace,
    ) => Effect.Effect<string, BrowserSessionPartitionDerivationError>;
    readonly isPartition: (partition: string) => boolean;
    readonly getSession: (
      scope?: string,
      persistent?: boolean,
      namespace?: BrowserSessionPartitionNamespace,
    ) => Effect.Effect<Session, BrowserSessionGetSessionError>;
    /** Omit `partitions` to clear every known partition. */
    readonly clearCookies: (
      partitions?: ReadonlyArray<string>,
    ) => Effect.Effect<void, BrowserSessionStorageClearError>;
    /** Clears a managed tab's cookies and certificate approvals, leaving its other storage. */
    readonly clearTabCookies: (
      contents: WebContents,
    ) => Effect.Effect<boolean, BrowserSessionStorageClearError>;
    readonly clearCache: (
      partitions?: ReadonlyArray<string>,
    ) => Effect.Effect<void, BrowserSessionCacheClearError>;
  }
>()("@t3tools/desktop/preview/BrowserSession") {}

/**
 * Restricts a clear to the given partitions. Omitting them keeps the historical
 * "every partition" behaviour, which callers now only use for an explicit
 * "all profiles" action — a per-profile clear must never reach across profiles.
 */
const selectSessions = (
  sessions: ReadonlyMap<string, Session>,
  partitions: ReadonlyArray<string> | undefined,
): ReadonlyArray<readonly [string, Session]> =>
  [...sessions.entries()].filter(
    ([partition]) => partitions === undefined || partitions.includes(partition),
  );

/**
 * Scope bytes for the partition digest.
 *
 * `TextEncoder` replaces a lone UTF-16 surrogate with U+FFFD, so `"p\ud800"`
 * and `"p\ufffd"` would hash to the same partition and share cookies. Those
 * are distinct, supported ids, so lone surrogates are escaped to `\uXXXX`
 * first — and a literal backslash is doubled so the escape cannot be forged.
 * Every well-formed scope passes through byte-for-byte unchanged, which keeps
 * existing partitions (and the logins in them) where they are.
 */
const encodeScopeForDigest = (scope: string): Uint8Array =>
  new TextEncoder().encode(
    scope
      .replace(/\\/g, "\\\\")
      .replace(
        /[\ud800-\udbff](?![\udc00-\udfff])|(?<![\ud800-\udbff])[\udc00-\udfff]/g,
        (unit) => `\\u${unit.charCodeAt(0).toString(16).padStart(4, "0")}`,
      ),
  );

/**
 * The window showing a preview guest. A `<webview>` guest has no window of its
 * own, so look it up through the page that embeds it.
 */
const previewHostWindow = (guest: WebContents | null): BrowserWindow | undefined => {
  if (guest === null || guest.isDestroyed()) return undefined;
  const host = guest.hostWebContents ?? guest;
  if (host.isDestroyed()) return undefined;
  return BrowserWindow.fromWebContents(host) ?? undefined;
};

/** @public Service construction is part of the canonical Effect module API. */
export const make = Effect.gen(function* BrowserSessionMake() {
  const crypto = yield* Crypto.Crypto;
  const electronApp = yield* ElectronApp.ElectronApp;
  const electronDialog = yield* ElectronDialog.ElectronDialog;
  const platform = yield* HostProcess.Platform;
  const fs = yield* FileSystem.FileSystem;
  const path = yield* Path.Path;
  const runFork = Effect.runForkWith(yield* Effect.context<FileSystem.FileSystem | Path.Path>());
  // One prompt at a time, so a page cannot stack dialogs by looping a deep link.
  let externalPromptOpen = false;
  /**
   * Electron grants an external-protocol navigation through the `openExternal`
   * permission and then launches the OS handler itself. Ask first: previews run
   * untrusted pages, and a silent grant would let any of them launch apps.
   */
  const confirmOpenExternal = (
    requester: WebContents | null,
    rawUrl: string | undefined,
    callback: (granted: boolean) => void,
  ): void => {
    const url = externalProtocolPromptUrl(rawUrl);
    if (url === null || externalPromptOpen) {
      callback(false);
      return;
    }
    externalPromptOpen = true;
    const settle = (granted: boolean) =>
      Effect.sync(() => {
        externalPromptOpen = false;
        callback(granted);
      });
    const shownUrl =
      url.length > MAX_PROMPT_URL_LENGTH ? `${url.slice(0, MAX_PROMPT_URL_LENGTH)}…` : url;
    runFork(
      electronDialog
        .showMessageBox(
          {
            type: "question",
            buttons: ["Open", "Cancel"],
            defaultId: 0,
            cancelId: 1,
            message: `Open this ${new URL(url).protocol.slice(0, -1)} link?`,
            detail: `A page in the browser wants to open another application:\n\n${shownUrl}`,
          },
          previewHostWindow(requester),
        )
        .pipe(
          Effect.map(({ response }) => response === 0),
          Effect.orElseSucceed(() => false),
          Effect.flatMap(settle),
          Effect.onInterrupt(() => settle(false)),
        ),
    );
  };

  /**
   * The preview Sessions this service created, each with the certificates the
   * user accepted in it. An approval covers one origin, certificate, and error.
   * It lasts until the profile's cookies are cleared. A persistent profile saves
   * its approvals, so they stay after a restart. Electron has no Chromium SSL
   * host state store, so without this map a reload would prompt again and page
   * resources would fail.
   */
  const certificateTrust = new WeakMap<Session, CertificateTrust>();
  const certificatePrompts = new Set<CertificatePrompt>();
  /** Reads a profile's saved approvals. A missing or invalid file grants none. */
  const loadCertificateApprovals = (file: string) =>
    fs.readFileString(file).pipe(
      Effect.flatMap(decodeCertificateApprovalsFile),
      Effect.map(
        ({ approvals }) =>
          new Map(approvals.map((approval) => [certificateApprovalKey(approval), approval])),
      ),
      Effect.catch((error) =>
        (error._tag === "PlatformError" && error.reason._tag === "NotFound"
          ? Effect.void
          : Effect.logWarning("Ignored the saved certificate approvals. The browser asks again.", {
              file,
              error,
            })
        ).pipe(Effect.as(new Map<string, CertificateApproval>())),
      ),
    );
  const makeCertificateTrust = (browserSession: Session) => {
    const file =
      browserSession.storagePath === null
        ? null
        : path.join(browserSession.storagePath, CERTIFICATE_APPROVALS_FILE);
    return (
      file === null
        ? Effect.succeed(new Map<string, CertificateApproval>())
        : loadCertificateApprovals(file)
    ).pipe(
      Effect.map((approvals): CertificateTrust => ({
        approvals,
        file,
        lock: Semaphore.makeUnsafe(1),
        clearing: 0,
      })),
    );
  };
  /**
   * Resolves every waiting callback once. A prompt closes when its last tab
   * leaves, so a late answer finds the prompt gone and trusts nothing.
   */
  const settleCertificatePrompt = (prompt: CertificatePrompt, trusted: boolean) => {
    if (!certificatePrompts.delete(prompt)) return;
    for (const waiter of prompt.waiters) {
      waiter.release();
      waiter.callback(trusted);
    }
    prompt.waiters.clear();
  };
  const cancelCertificatePrompt = (prompt: CertificatePrompt) => {
    prompt.dialog.abort();
    settleCertificatePrompt(prompt, false);
  };
  const dropCertificateWaiter = (prompt: CertificatePrompt, waiter: CertificateWaiter) => {
    if (!prompt.waiters.delete(waiter)) return;
    waiter.release();
    waiter.callback(false);
    if (prompt.waiters.size === 0) cancelCertificatePrompt(prompt);
  };
  // In a user's test on Windows, a box owned by the host window blocked all
  // mouse input, its own buttons included, until it closed. The keyboard still
  // worked. So Windows shows certificate boxes without an owner.
  const certificateDialogOwner = (contents: WebContents) =>
    platform === "win32" ? undefined : previewHostWindow(contents);
  /**
   * Saves the approval, then trusts it. The decision is final once its write
   * starts: a tab that leaves during the write is denied, but the approval
   * stays. A failed write trusts nothing and tells the user.
   */
  const approveCertificate = (prompt: CertificatePrompt, contents: WebContents) => {
    const { trust } = prompt;
    return trust.lock
      .withPermits(1)(
        Effect.gen(function* () {
          // Every tab left, or a clear cancelled the prompt, while it waited for the lock.
          if (!certificatePrompts.has(prompt)) return;
          const file = trust.file;
          if (file !== null) {
            const approvals = new Map(trust.approvals).set(prompt.key, prompt.approval);
            const encoded = yield* encodeCertificateApprovalsFile({
              version: 1,
              approvals: [...approvals.values()],
            });
            yield* writeFileStringAtomically({ filePath: file, contents: encoded });
          }
          // A clear that started during the write removes the file after it.
          if (trust.clearing === 0) trust.approvals.set(prompt.key, prompt.approval);
          settleCertificatePrompt(prompt, true);
        }),
      )
      .pipe(
        Effect.catch((error) =>
          Effect.gen(function* () {
            settleCertificatePrompt(prompt, false);
            yield* Effect.logWarning("Could not save a certificate approval.", {
              file: trust.file,
              error,
            });
            yield* electronDialog
              .showMessageBox(
                {
                  type: "error",
                  buttons: ["OK"],
                  message: "T3 Code could not save your approval.",
                  detail: `The page at ${prompt.approval.origin} did not open. Try again. If the problem continues, make sure T3 Code can write to its data folder.`,
                },
                certificateDialogOwner(contents),
              )
              .pipe(Effect.ignore({ log: true }));
          }),
        ),
      );
  };
  /**
   * Holds the navigation until the user decides. Closing the tab or starting a
   * new page in it denies the waiting navigation.
   */
  const confirmCertificate = (
    contents: WebContents,
    trust: CertificateTrust,
    approval: CertificateApproval,
    key: string,
    details: {
      readonly reason: string;
      readonly certificate: Certificate;
    },
    callback: (trusted: boolean) => void,
  ): void => {
    const shared = [...certificatePrompts].find(
      (prompt) => prompt.trust === trust && prompt.key === key,
    );
    const prompt: CertificatePrompt = shared ?? {
      trust,
      approval,
      key,
      dialog: new AbortController(),
      waiters: new Set(),
    };
    const drop = () => dropCertificateWaiter(prompt, waiter);
    const navigationStarted = (
      event: Electron.Event<Electron.WebContentsDidStartNavigationEventParams>,
    ) => {
      if (event.isMainFrame && !event.isSameDocument) drop();
    };
    const waiter: CertificateWaiter = {
      callback,
      release: () => {
        contents.off("destroyed", drop);
        contents.off("did-start-navigation", navigationStarted);
      },
    };
    contents.on("destroyed", drop);
    contents.on("did-start-navigation", navigationStarted);
    prompt.waiters.add(waiter);
    if (shared !== undefined) return;

    certificatePrompts.add(prompt);
    const { certificate } = details;
    runFork(
      electronDialog
        .showMessageBox(
          {
            type: "warning",
            buttons: [trust.file === null ? "Trust Until Quit" : "Trust and Remember", "Cancel"],
            defaultId: 1,
            cancelId: 1,
            noLink: true,
            message: `The certificate for ${approval.origin} is not trusted.`,
            detail: [
              details.reason,
              "",
              trust.file === null
                ? "Trust this certificate only if you know the device at this address. Incognito tabs trust it for this site until you quit T3 Code or clear their cookies."
                : "Trust this certificate only if you know the device at this address. T3 Code saves your approval for this browser profile. The approval stays after you restart T3 Code. To remove it, clear the profile's cookies.",
              "",
              `Subject: ${promptCertificateName(certificate.subjectName)}`,
              `Issuer: ${promptCertificateName(certificate.issuerName)}`,
              `Valid: ${promptCertificateDate(certificate.validStart)} to ${promptCertificateDate(certificate.validExpiry)}`,
              `Fingerprint: ${certificate.fingerprint}`,
            ].join("\n"),
            signal: prompt.dialog.signal,
          },
          certificateDialogOwner(contents),
        )
        .pipe(
          Effect.map(({ response }) => response === 0),
          Effect.orElseSucceed(() => false),
          Effect.flatMap((trusted) =>
            trusted
              ? approveCertificate(prompt, contents)
              : Effect.sync(() => settleCertificatePrompt(prompt, false)),
          ),
          Effect.onInterrupt(() => Effect.sync(() => cancelCertificatePrompt(prompt))),
        ),
    );
  };
  // Registered on `app` when the service starts, so a tab's first request is
  // covered before the renderer registers its webview. Errors from other
  // Sessions return without `preventDefault`, which keeps Electron's denial.
  yield* electronApp.on(
    "certificate-error",
    (
      event: Electron.Event,
      contents: WebContents,
      url: string,
      error: string,
      certificate: Certificate,
      callback: (trusted: boolean) => void,
      isMainFrame: boolean,
    ) => {
      if (contents.isDestroyed()) return;
      const trust = certificateTrust.get(contents.session);
      const origin = certificateOrigin(url);
      // While its cookies are cleared, a Session trusts nothing and asks nothing.
      if (trust === undefined || trust.clearing > 0 || origin === null) return;
      const approval = { origin, fingerprint: certificate.fingerprint, error };
      const key = certificateApprovalKey(approval);
      if (trust.approvals.has(key)) {
        event.preventDefault();
        callback(true);
        return;
      }
      // Only a page navigation asks. A page resource with a certificate the
      // user has not accepted stays blocked.
      const reason = OVERRIDABLE_CERTIFICATE_ERRORS.get(error);
      if (!isMainFrame || reason === undefined) return;
      event.preventDefault();
      confirmCertificate(contents, trust, approval, key, { reason, certificate }, callback);
    },
  );
  yield* Effect.addFinalizer(() =>
    Effect.sync(() => {
      for (const prompt of certificatePrompts) cancelCertificatePrompt(prompt);
    }),
  );

  const sessionsRef = yield* SynchronizedRef.make<ReadonlyMap<string, Session>>(new Map());

  const getPartition = Effect.fn("BrowserSession.getPartition")(function* (
    scope = "shared",
    persistent = true,
    namespace?: BrowserSessionPartitionNamespace,
  ) {
    const digest = yield* crypto.digest("SHA-256", encodeScopeForDigest(scope)).pipe(
      Effect.mapError(
        (cause) =>
          new BrowserSessionPartitionDerivationError({
            scope,
            cause,
          }),
      ),
    );
    const prefix = persistent ? PREVIEW_PARTITION_PREFIX : PREVIEW_EPHEMERAL_PARTITION_PREFIX;
    // Legacy/default partitions are prefix + hex digest. The non-hex profile
    // marker creates a disjoint namespace while leaving every legacy default
    // partition byte-for-byte unchanged.
    return `${prefix}${namespace === "profile" ? PROFILE_PARTITION_MARKER : ""}${Hex.encode(digest).slice(0, 20)}`;
  });

  const getSession = Effect.fn("BrowserSession.getSession")(function* (
    scope = "shared",
    persistent = true,
    namespace?: BrowserSessionPartitionNamespace,
  ) {
    const partition = yield* getPartition(scope, persistent, namespace);
    return yield* SynchronizedRef.modifyEffect(sessionsRef, (sessions) => {
      const existing = sessions.get(partition);
      if (existing) return Effect.succeed([existing, sessions] as const);
      return Effect.try({
        try: () => {
          const browserSession = session.fromPartition(partition);
          // The guest keeps Electron's native User-Agent. Rewriting it in any
          // form — even variants that keep the Electron token — makes Cloudflare
          // Turnstile fail its integrity check with error 600010 and recreate
          // the challenge every few seconds, so logins behind it never complete
          // (#5002). Re-setting the unchanged native string is harmless, so it
          // is the rewritten string itself that trips the check.
          browserSession.setPermissionRequestHandler(
            (webContents, permission, callback, details) => {
              if (permission === "openExternal") {
                confirmOpenExternal(
                  webContents,
                  "externalURL" in details ? details.externalURL : undefined,
                  callback,
                );
                return;
              }
              callback(ALLOWED_PREVIEW_PERMISSIONS.has(permission));
            },
          );
          browserSession.setPermissionCheckHandler((_webContents, permission) =>
            ALLOWED_PREVIEW_PERMISSIONS.has(permission),
          );
          return browserSession;
        },
        catch: (cause) =>
          new BrowserSessionCreationError({
            scope,
            partition,
            cause,
          }),
      }).pipe(
        // Until its approvals are loaded, Electron denies the Session's certificate errors.
        Effect.flatMap((browserSession) =>
          Effect.map(makeCertificateTrust(browserSession), (trust) => {
            certificateTrust.set(browserSession, trust);
            const next = new Map(sessions);
            next.set(partition, browserSession);
            return [browserSession, next] as const;
          }),
        ),
      );
    });
  });

  /** Removes a Session's saved approvals, after any approval write that started first. */
  const removeSavedCertificateApprovals = (trust: CertificateTrust) =>
    trust.lock.withPermits(1)(
      Effect.suspend(() => {
        return trust.file === null ? Effect.void : fs.remove(trust.file, { force: true });
      }),
    );
  /** Clears one Session's site data. Returns the failure to report, if any. */
  const clearSessionCookies = (
    partition: string,
    browserSession: Session,
    storages: NonNullable<Electron.ClearStorageDataOptions["storages"]>,
  ) => {
    const trust = certificateTrust.get(browserSession);
    // Run all three, so one failure does not stop the others. In this order,
    // the first failure is the one to report.
    return Effect.forEach(
      [
        Effect.tryPromise({
          try: () => browserSession.clearStorageData({ storages }),
          catch: (cause) => new BrowserSessionStorageClearError({ partition, cause }),
        }),
        // Retry the removal even after a previous clear emptied the approvals in memory.
        (trust === undefined ? Effect.void : removeSavedCertificateApprovals(trust)).pipe(
          Effect.mapError(
            (cause) =>
              new BrowserSessionStorageClearError({
                partition,
                operation: "certificateApprovals",
                cause,
              }),
          ),
        ),
        // Retry closing connections even after a previous clear dropped the approvals.
        Effect.tryPromise({
          try: () => browserSession.closeAllConnections(),
          catch: (cause) =>
            new BrowserSessionStorageClearError({
              partition,
              operation: "closeConnections",
              cause,
            }),
        }),
      ],
      Effect.result,
      { concurrency: "unbounded" },
    ).pipe(Effect.map((results) => results.find(Result.isFailure)?.failure));
  };

  const clearSessions = Effect.fn("BrowserSession.clearSessions")(function* (
    selected: ReadonlyArray<readonly [string, Session]>,
    storages: NonNullable<Electron.ClearStorageDataOptions["storages"]>,
  ) {
    const trusts = selected.flatMap(([, browserSession]) => {
      const trust = certificateTrust.get(browserSession);
      return trust === undefined ? [] : [trust];
    });
    const failures = yield* Effect.acquireUseRelease(
      // Certificate approvals are site data. Drop them from memory first, so
      // a failed clear cannot leave them in place.
      Effect.sync(() => {
        for (const trust of trusts) {
          trust.clearing += 1;
          trust.approvals.clear();
          for (const prompt of certificatePrompts) {
            if (prompt.trust === trust) cancelCertificatePrompt(prompt);
          }
        }
      }),
      () =>
        Effect.forEach(
          selected,
          ([partition, browserSession]) => clearSessionCookies(partition, browserSession, storages),
          { concurrency: "unbounded" },
        ),
      () =>
        Effect.sync(() => {
          for (const trust of trusts) trust.clearing -= 1;
        }),
    );
    const failure = failures.find((error) => error !== undefined);
    if (failure !== undefined) return yield* failure;
  });

  return BrowserSession.of({
    getPartition,
    isPartition: (partition) =>
      partition.startsWith(PREVIEW_PARTITION_PREFIX) ||
      partition.startsWith(PREVIEW_EPHEMERAL_PARTITION_PREFIX),
    getSession,
    clearCookies: Effect.fn("BrowserSession.clearCookies")(function* (partitions?) {
      yield* clearSessions(selectSessions(yield* SynchronizedRef.get(sessionsRef), partitions), [
        "cookies",
        "localstorage",
        "indexdb",
        "serviceworkers",
      ]);
    }),
    clearTabCookies: Effect.fn("BrowserSession.clearTabCookies")(function* (contents) {
      const selected = [...(yield* SynchronizedRef.get(sessionsRef))].filter(
        ([, browserSession]) => browserSession === contents.session,
      );
      if (selected.length === 0) return false;
      yield* clearSessions(selected, ["cookies"]).pipe(
        Effect.tapError(() =>
          Effect.sync(() => {
            runFork(
              electronDialog
                .showMessageBox(
                  {
                    type: "error",
                    buttons: ["OK"],
                    message: "T3 Code could not clear this profile's cookies.",
                    detail:
                      "Some data can stay, such as certificates that you accepted. Try again. If the problem continues, make sure T3 Code can write to its data folder.",
                  },
                  certificateDialogOwner(contents),
                )
                .pipe(Effect.ignore({ log: true })),
            );
          }),
        ),
      );
      return true;
    }),
    clearCache: Effect.fn("BrowserSession.clearCache")(function* (partitions?) {
      const sessions = yield* SynchronizedRef.get(sessionsRef);
      yield* Effect.forEach(
        selectSessions(sessions, partitions),
        ([partition, browserSession]) =>
          Effect.tryPromise({
            try: () => browserSession.clearCache(),
            catch: (cause) =>
              new BrowserSessionCacheClearError({
                partition,
                cause,
              }),
          }),
        { concurrency: "unbounded", discard: true },
      );
    }),
  });
}).pipe(Effect.withSpan("BrowserSession.make"));

export const layer = Layer.effect(BrowserSession, make);
