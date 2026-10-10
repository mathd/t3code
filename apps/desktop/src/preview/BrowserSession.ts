import type { Certificate, Session, WebContents } from "electron";
import { BrowserWindow, session } from "electron";
import * as HostProcess from "@t3tools/shared/HostProcess";
import * as Context from "effect/Context";
import * as Crypto from "effect/Crypto";
import * as DateTime from "effect/DateTime";
import * as Effect from "effect/Effect";
import * as Hex from "effect/encoding/Hex";
import * as Layer from "effect/Layer";
import * as Option from "effect/Option";
import * as PlatformError from "effect/PlatformError";
import * as Schema from "effect/Schema";
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

/** One open certificate prompt. Tabs that hit the same error share it. */
interface CertificatePrompt {
  /** The exceptions of the Session the prompt is for. */
  readonly exceptions: Set<string>;
  readonly exception: string;
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
    /** Set when storage was cleared and only closing the open connections failed. */
    operation: Schema.optional(Schema.Literal("closeConnections")),
    cause: Schema.Defect(),
  },
) {
  override get message(): string {
    return this.operation === "closeConnections"
      ? `Cleared desktop preview browser storage for partition ${this.partition}, but failed to close its open connections.`
      : `Failed to clear desktop preview browser storage for partition ${this.partition}.`;
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
  const runFork = Effect.runForkWith(yield* Effect.context<never>());
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
   * The preview Sessions this service created, each with the certificate
   * exceptions the user accepted in it. An exception is
   * `origin fingerprint error`. It lasts until the profile's cookies are
   * cleared or the app quits. Electron has no Chromium SSL host state store, so
   * without this map a reload would prompt again and page resources would fail.
   */
  const certificateExceptions = new WeakMap<Session, Set<string>>();
  const certificatePrompts = new Set<CertificatePrompt>();
  /**
   * Resolves every waiting callback once. A prompt closes when its last tab
   * leaves, so a late answer finds the prompt gone and trusts nothing.
   */
  const settleCertificatePrompt = (prompt: CertificatePrompt, trusted: boolean) => {
    if (!certificatePrompts.delete(prompt)) return;
    if (trusted) prompt.exceptions.add(prompt.exception);
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
  /**
   * Holds the navigation until the user decides. Closing the tab or starting a
   * new page in it denies the waiting navigation.
   */
  const confirmCertificate = (
    contents: WebContents,
    exceptions: Set<string>,
    exception: string,
    details: {
      readonly origin: string;
      readonly reason: string;
      readonly certificate: Certificate;
    },
    callback: (trusted: boolean) => void,
  ): void => {
    const shared = [...certificatePrompts].find(
      (prompt) => prompt.exceptions === exceptions && prompt.exception === exception,
    );
    const prompt: CertificatePrompt = shared ?? {
      exceptions,
      exception,
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
            buttons: ["Continue", "Cancel"],
            defaultId: 1,
            cancelId: 1,
            noLink: true,
            message: `The certificate for ${details.origin} is not trusted.`,
            detail: [
              details.reason,
              "",
              "Continue only if you know the device at this address. If you continue, this browser profile trusts this certificate for this site until you clear its cookies or quit T3 Code.",
              "",
              `Subject: ${promptCertificateName(certificate.subjectName)}`,
              `Issuer: ${promptCertificateName(certificate.issuerName)}`,
              `Valid: ${promptCertificateDate(certificate.validStart)} to ${promptCertificateDate(certificate.validExpiry)}`,
              `Fingerprint: ${certificate.fingerprint}`,
            ].join("\n"),
            signal: prompt.dialog.signal,
          },
          // In a user's test on Windows, a box owned by the host window blocked
          // all mouse input, its own buttons included, until it closed. The
          // keyboard still worked. So Windows shows the box without an owner.
          platform === "win32" ? undefined : previewHostWindow(contents),
        )
        .pipe(
          Effect.map(({ response }) => response === 0),
          Effect.orElseSucceed(() => false),
          Effect.flatMap((trusted) => Effect.sync(() => settleCertificatePrompt(prompt, trusted))),
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
      const exceptions = certificateExceptions.get(contents.session);
      const origin = certificateOrigin(url);
      if (exceptions === undefined || origin === null) return;
      const exception = `${origin} ${certificate.fingerprint} ${error}`;
      if (exceptions.has(exception)) {
        event.preventDefault();
        callback(true);
        return;
      }
      // Only a page navigation asks. A page resource with a certificate the
      // user has not accepted stays blocked.
      const reason = OVERRIDABLE_CERTIFICATE_ERRORS.get(error);
      if (!isMainFrame || reason === undefined) return;
      event.preventDefault();
      confirmCertificate(
        contents,
        exceptions,
        exception,
        { origin, reason, certificate },
        callback,
      );
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
          certificateExceptions.set(browserSession, new Set());
          const next = new Map(sessions);
          next.set(partition, browserSession);
          return [browserSession, next] as const;
        },
        catch: (cause) =>
          new BrowserSessionCreationError({
            scope,
            partition,
            cause,
          }),
      });
    });
  });

  return BrowserSession.of({
    getPartition,
    isPartition: (partition) =>
      partition.startsWith(PREVIEW_PARTITION_PREFIX) ||
      partition.startsWith(PREVIEW_EPHEMERAL_PARTITION_PREFIX),
    getSession,
    clearCookies: Effect.fn("BrowserSession.clearCookies")(function* (partitions?) {
      const selected = selectSessions(yield* SynchronizedRef.get(sessionsRef), partitions);
      // Certificate exceptions are site data. Drop them first, so a failed
      // storage clear cannot leave them in place.
      for (const [, browserSession] of selected) {
        const exceptions = certificateExceptions.get(browserSession);
        if (exceptions === undefined) continue;
        exceptions.clear();
        for (const prompt of certificatePrompts) {
          if (prompt.exceptions === exceptions) cancelCertificatePrompt(prompt);
        }
      }
      yield* Effect.forEach(
        selected,
        ([partition, browserSession]) =>
          // Run both, so a failed close still clears storage. A storage failure
          // is the one to report when both fail.
          Effect.promise(() =>
            Promise.allSettled([
              (async () => {
                // Retry closing connections even after a previous clear dropped the exceptions.
                await browserSession.closeAllConnections();
              })(),
              (async () =>
                browserSession.clearStorageData({
                  storages: ["cookies", "localstorage", "indexdb", "serviceworkers"],
                }))(),
            ]),
          ).pipe(
            Effect.flatMap(([connections, storage]) => {
              if (storage.status === "rejected") {
                return Effect.fail(
                  new BrowserSessionStorageClearError({ partition, cause: storage.reason }),
                );
              }
              if (connections.status === "rejected") {
                return Effect.fail(
                  new BrowserSessionStorageClearError({
                    partition,
                    operation: "closeConnections",
                    cause: connections.reason,
                  }),
                );
              }
              return Effect.void;
            }),
          ),
        { concurrency: "unbounded", discard: true },
      );
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
