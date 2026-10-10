// @effect-diagnostics nodeBuiltinImport:off - The mocked Electron Session needs a temporary storage folder before any Effect runs.
import * as NodeEvents from "node:events";
import * as NodeFS from "node:fs";
import * as NodeOS from "node:os";
import * as NodePath from "node:path";

import { assert, describe, it } from "@effect/vitest";
import { DesktopBrowserEvent } from "@t3tools/contracts";
import * as NodeServices from "@effect/platform-node/NodeServices";
import * as HostProcess from "@t3tools/shared/HostProcess";
import * as Context from "effect/Context";
import * as Crypto from "effect/Crypto";
import * as Deferred from "effect/Deferred";
import * as Effect from "effect/Effect";
import * as Exit from "effect/Exit";
import * as Fiber from "effect/Fiber";
import * as FileSystem from "effect/FileSystem";
import * as Layer from "effect/Layer";
import * as PlatformError from "effect/PlatformError";
import * as Scope from "effect/Scope";
import * as Schema from "effect/Schema";
import * as Stream from "effect/Stream";
import { afterEach, beforeEach, vi } from "vite-plus/test";

const decodeDesktopBrowserEvent = Schema.decodeEffect(Schema.fromJsonString(DesktopBrowserEvent));
const decodeCookieClearReply = Schema.decodeEffect(
  Schema.fromJsonString(
    Schema.Union([
      Schema.Struct({ id: Schema.Number, result: Schema.Struct({}) }),
      Schema.Struct({
        id: Schema.Number,
        error: Schema.Struct({ code: Schema.Number, message: Schema.String }),
      }),
    ]),
  ),
);

const { fromPartition, sessions } = vi.hoisted(() => ({
  fromPartition: vi.fn(),
  sessions: new Map<
    string,
    {
      readonly clearCache: ReturnType<typeof vi.fn>;
      readonly closeAllConnections: ReturnType<typeof vi.fn>;
      readonly clearStorageData: ReturnType<typeof vi.fn>;
      readonly getUserAgent: ReturnType<typeof vi.fn<() => string>>;
      readonly setPermissionRequestHandler: ReturnType<typeof vi.fn>;
      readonly setPermissionCheckHandler: ReturnType<typeof vi.fn>;
      readonly setUserAgent: ReturnType<typeof vi.fn>;
      readonly storagePath: string | null;
    }
  >(),
}));

const { fromWebContents } = vi.hoisted(() => ({
  fromWebContents: vi.fn<(webContents: unknown) => unknown>(() => null),
}));

const { appListeners } = vi.hoisted(() => ({
  appListeners: new Map<string, (...args: unknown[]) => void>(),
}));

vi.mock("electron", () => ({
  app: {
    on: (eventName: string, listener: (...args: unknown[]) => void) => {
      appListeners.set(eventName, listener);
    },
    removeListener: (eventName: string, listener: (...args: unknown[]) => void) => {
      if (appListeners.get(eventName) === listener) appListeners.delete(eventName);
    },
  },
  BrowserWindow: { fromWebContents },
  session: {
    fromPartition,
  },
}));

import * as ElectronApp from "../electron/ElectronApp.ts";
import * as ElectronDialog from "../electron/ElectronDialog.ts";
import * as BrowserSession from "./BrowserSession.ts";
import * as DesktopBrowserHost from "./DesktopBrowserHost.ts";

const { showMessageBox } = vi.hoisted(() => ({
  showMessageBox: vi.fn<
    (options: Electron.MessageBoxOptions, owner?: Electron.BrowserWindow) => number
  >(() => 1),
}));
const layerDialog = Layer.succeed(ElectronDialog.ElectronDialog, {
  pickFolder: () => Effect.die("unused"),
  pickFiles: () => Effect.die("unused"),
  showMessageBox: (options, owner) =>
    Effect.sync(() => ({ response: showMessageBox(options, owner), checkboxChecked: false })),
  showErrorBox: () => Effect.void,
});
const layer = BrowserSession.layer.pipe(
  Layer.provide(Layer.mergeAll(NodeServices.layer, layerDialog, ElectronApp.layer)),
);

/** A native message box that stays open until the test answers it. */
interface OpenPrompt {
  readonly options: Electron.MessageBoxOptions;
  readonly owner: Electron.BrowserWindow | undefined;
  readonly response: Deferred.Deferred<number, ElectronDialog.ElectronDialogShowMessageBoxError>;
  /** Completes when the service has the answer. */
  readonly answered: Deferred.Deferred<void>;
}
const prompts: Array<OpenPrompt> = [];
const openedPrompts: Array<Deferred.Deferred<void>> = [];
/** Completes when the message box at `index` opens. */
const promptOpened = (index: number) => (openedPrompts[index] ??= Deferred.makeUnsafe());
const layerPromptDialog = Layer.succeed(ElectronDialog.ElectronDialog, {
  pickFolder: () => Effect.die("unused"),
  pickFiles: () => Effect.die("unused"),
  showMessageBox: (options, owner) =>
    Effect.suspend(() => {
      const prompt: OpenPrompt = {
        options,
        owner,
        response: Deferred.makeUnsafe(),
        answered: Deferred.makeUnsafe(),
      };
      prompts.push(prompt);
      Deferred.doneUnsafe(promptOpened(prompts.length - 1), Effect.void);
      return Deferred.await(prompt.response).pipe(
        Effect.map((response) => ({ response, checkboxChecked: false })),
        Effect.ensuring(Deferred.succeed(prompt.answered, undefined)),
      );
    }),
  showErrorBox: () => Effect.void,
});
const layerCertificatesOn = (platform: NodeJS.Platform) =>
  BrowserSession.layer.pipe(
    Layer.provide(
      Layer.mergeAll(
        NodeServices.layer,
        layerPromptDialog,
        ElectronApp.layer,
        Layer.succeed(HostProcess.Platform, platform),
      ),
    ),
  );
const layerCertificates = layerCertificatesOn("linux");
const CONTINUE = 0;
const CANCEL = 1;

const APPROVALS_FILE = "t3code-certificate-approvals.json";
/** A temporary folder for each test, in place of Electron's user data folder. */
let userData = "";
/** Where Electron keeps a partition's data. Incognito partitions have none. */
const storagePathFor = (partition: string) =>
  partition.startsWith("persist:")
    ? NodePath.join(userData, "Partitions", partition.slice("persist:".length))
    : null;
const approvalsFileFor = (partition: string) =>
  NodePath.join(storagePathFor(partition) ?? "", APPROVALS_FILE);

/** Holds one file operation until the test releases it, or fails it. */
interface FileHold {
  readonly entered: Deferred.Deferred<void>;
  readonly release: Deferred.Deferred<void, PlatformError.PlatformError>;
}
/**
 * The real file system, but the test can hold the next approval write (its
 * final rename) or the next removal of an approval file.
 */
const makeFileGate = (platform: NodeJS.Platform = "linux") => {
  const holds = { rename: [] as Array<FileHold>, remove: [] as Array<FileHold> };
  const pass = (operation: keyof typeof holds) =>
    Effect.suspend(() => {
      const hold = holds[operation].shift();
      if (hold === undefined) return Effect.void;
      return Deferred.succeed(hold.entered, undefined).pipe(
        Effect.andThen(Deferred.await(hold.release)),
      );
    });
  const layerFileSystem = Layer.effect(
    FileSystem.FileSystem,
    Effect.gen(function* () {
      const fs = yield* FileSystem.FileSystem;
      return FileSystem.FileSystem.of({
        ...fs,
        rename: (from, to) => pass("rename").pipe(Effect.andThen(fs.rename(from, to))),
        remove: (path, options) =>
          NodePath.basename(path) === APPROVALS_FILE
            ? pass("remove").pipe(Effect.andThen(fs.remove(path, options)))
            : fs.remove(path, options),
      });
    }),
  ).pipe(Layer.provide(NodeServices.layer));
  return {
    hold: (operation: keyof typeof holds): FileHold => {
      const hold: FileHold = { entered: Deferred.makeUnsafe(), release: Deferred.makeUnsafe() };
      holds[operation].push(hold);
      return hold;
    },
    layer: BrowserSession.layer.pipe(
      Layer.provide(
        Layer.mergeAll(
          layerFileSystem,
          layerPromptDialog,
          ElectronApp.layer,
          Layer.succeed(HostProcess.Platform, platform),
        ),
      ),
      Layer.provide(NodeServices.layer),
    ),
  };
};
const fileFailure = (method: string) =>
  PlatformError.systemError({ _tag: "PermissionDenied", module: "FileSystem", method });

const hostWindow = { id: 7 } as unknown as Electron.BrowserWindow;
const host = { isDestroyed: () => false };

/** A preview guest, as Electron hands it to the `certificate-error` listener. */
const makeTab = (browserSession: unknown) => {
  let destroyed = false;
  const tab = Object.assign(new NodeEvents.EventEmitter(), {
    session: browserSession,
    hostWebContents: host,
    isDestroyed: () => destroyed,
    close: () => {
      destroyed = true;
      tab.emit("destroyed");
    },
    startNavigation: (details: { isMainFrame: boolean; isSameDocument: boolean }) => {
      tab.emit("did-start-navigation", details);
    },
  });
  return tab;
};

// Like the UniFi controller's certificate, it is self-signed and names `UniFi`, not the IP.
const unifiCertificate = {
  fingerprint: "sha256/unifi",
  subjectName: "UniFi",
  issuerName: "UniFi",
  validStart: 1_735_776_000,
  validExpiry: 1_807_056_000,
} as Electron.Certificate;
const renewedCertificate = { ...unifiCertificate, fingerprint: "sha256/renewed" };

const certificateError = (
  contents: unknown,
  input: {
    readonly url: string;
    readonly error?: string;
    readonly certificate?: Electron.Certificate;
    readonly isMainFrame?: boolean;
  },
) => {
  const listener = appListeners.get("certificate-error");
  assert.isDefined(listener);
  const event = { preventDefault: vi.fn() };
  const decision = Deferred.makeUnsafe<boolean>();
  const callback = vi.fn((trusted: boolean) => {
    Deferred.doneUnsafe(decision, Effect.succeed(trusted));
  });
  listener(
    event,
    contents,
    input.url,
    input.error ?? "net::ERR_CERT_AUTHORITY_INVALID",
    input.certificate ?? unifiCertificate,
    callback,
    input.isMainFrame ?? true,
  );
  return { event, callback, trusted: Deferred.await(decision) };
};

/** Without `preventDefault`, Electron denies the certificate itself. */
const assertLeftToElectron = (result: ReturnType<typeof certificateError>, label?: string) => {
  assert.strictEqual(result.event.preventDefault.mock.calls.length, 0, label);
  assert.strictEqual(result.callback.mock.calls.length, 0, label);
};

const assertTrustedWithoutPrompt = (
  result: ReturnType<typeof certificateError>,
  label?: string,
) => {
  assert.strictEqual(result.event.preventDefault.mock.calls.length, 1, label);
  assert.deepEqual(result.callback.mock.calls, [[true]], label);
};

const answer = (index: number, response: number) => {
  const prompt = prompts[index];
  assert.isDefined(prompt, `prompt ${index} should be open`);
  return Deferred.succeed(prompt.response, response);
};

/** Opens a profile in the running service and returns a new tab in it. */
const openTab = (scope: string, persistent = true) =>
  Effect.gen(function* () {
    const browserSessions = yield* BrowserSession.BrowserSession;
    const partition = yield* browserSessions.getPartition(scope, persistent);
    yield* browserSessions.getSession(scope, persistent);
    return makeTab(sessions.get(partition));
  });

/** Continues on the prompt that the page opens, and returns the decision. */
const accept = (contents: unknown, input: Parameters<typeof certificateError>[1]) =>
  Effect.gen(function* () {
    const opened = prompts.length;
    const result = certificateError(contents, input);
    assert.strictEqual(prompts.length, opened + 1, `${input.url} should prompt`);
    yield* answer(opened, CONTINUE);
    return yield* result.trusted;
  });

/** Asserts that the page opens a prompt, then cancels it. */
const assertPrompts = (contents: unknown, input: Parameters<typeof certificateError>[1]) =>
  Effect.gen(function* () {
    const opened = prompts.length;
    const result = certificateError(contents, input);
    assert.strictEqual(prompts.length, opened + 1, `${input.url} should prompt`);
    yield* answer(opened, CANCEL);
    assert.isFalse(yield* result.trusted);
  });

describe("BrowserSession", () => {
  afterEach(() => {
    NodeFS.rmSync(userData, { recursive: true, force: true });
  });

  beforeEach(() => {
    userData = NodeFS.mkdtempSync(NodePath.join(NodeOS.tmpdir(), "t3code-browser-session-"));
    appListeners.clear();
    prompts.length = 0;
    openedPrompts.length = 0;
    sessions.clear();
    fromPartition.mockReset();
    fromPartition.mockImplementation((partition: string) => {
      const browserSession = {
        clearCache: vi.fn(() => Promise.resolve()),
        closeAllConnections: vi.fn(() => Promise.resolve()),
        clearStorageData: vi.fn(() => Promise.resolve()),
        getUserAgent: vi.fn(() => "Mozilla/5.0 Electron/41.5.0 t3code/0.0.27"),
        setPermissionRequestHandler: vi.fn(),
        setPermissionCheckHandler: vi.fn(),
        setUserAgent: vi.fn(),
        storagePath: storagePathFor(partition),
      };
      sessions.set(partition, browserSession);
      return browserSession;
    });
  });

  it.effect("derives deterministic partitions and memoizes sessions", () =>
    Effect.gen(function* () {
      const browserSessions = yield* BrowserSession.BrowserSession;

      const partition = yield* browserSessions.getPartition("scope-a");
      const first = yield* browserSessions.getSession("scope-a");
      const second = yield* browserSessions.getSession("scope-a");

      assert.strictEqual(partition, "persist:t3code-preview-f051bb2c68cb7b2fe969");
      assert.strictEqual(first, second);
      assert.strictEqual(fromPartition.mock.calls.length, 1);
    }).pipe(Effect.provide(layer)),
  );

  it.effect("keeps scopes that differ only by a lone surrogate in separate partitions", () =>
    Effect.gen(function* () {
      const browserSessions = yield* BrowserSession.BrowserSession;

      // TextEncoder folds a lone surrogate to U+FFFD, so without escaping these
      // two supported ids would hash to one partition and share every cookie.
      const loneSurrogate = yield* browserSessions.getPartition("p\ud800");
      const replacementChar = yield* browserSessions.getPartition("p\ufffd");
      assert.notStrictEqual(loneSurrogate, replacementChar);

      // The escape can't be forged with a literal backslash either.
      const literal = yield* browserSessions.getPartition("p\\ud800");
      assert.notStrictEqual(literal, loneSurrogate);

      // And a well-formed scope still lands on its historical partition.
      assert.strictEqual(
        yield* browserSessions.getPartition("scope-a"),
        "persist:t3code-preview-f051bb2c68cb7b2fe969",
      );
    }).pipe(Effect.provide(layer)),
  );

  it.effect("keeps legacy defaults disjoint from nondefault profile partitions", () =>
    Effect.gen(function* () {
      const browserSessions = yield* BrowserSession.BrowserSession;

      // These share the same scope string: default environment `a::b`, and
      // environment `a` with nondefault profile `b`.
      const legacyDefault = yield* browserSessions.getPartition("a::b");
      const nondefaultProfile = yield* browserSessions.getPartition("a::b", true, "profile");

      assert.strictEqual(legacyDefault, "persist:t3code-preview-78f0be89237d77f7a70e");
      assert.strictEqual(nondefaultProfile, "persist:t3code-preview-profile-78f0be89237d77f7a70e");
      assert.notStrictEqual(nondefaultProfile, legacyDefault);
      assert.isTrue(browserSessions.isPartition(legacyDefault));
      assert.isTrue(browserSessions.isPartition(nondefaultProfile));
    }).pipe(Effect.provide(layer)),
  );

  // A rewritten session UA — any variant, even ones that keep the Electron
  // token — makes Cloudflare Turnstile loop with error 600010 (#5002), so
  // the guest must end up with Electron's native User-Agent. The mock applies
  // setUserAgent calls, so this fails on any reintroduced rewrite while still
  // permitting a harmless re-set of the unchanged native string.
  it.effect("keeps the guest's effective User-Agent equal to Electron's native one", () =>
    Effect.gen(function* () {
      // Electron's real UA shape: app token, then Chrome, then Electron, then
      // Safari — the token order and casing matter to any strip regex.
      const nativeUserAgent =
        "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) T3Code(Alpha)/0.0.33 Chrome/146.0.7680.216 Electron/41.5.0 Safari/537.36";
      fromPartition.mockReset();
      fromPartition.mockImplementation((partition: string) => {
        let userAgent = nativeUserAgent;
        const browserSession = {
          clearCache: vi.fn(() => Promise.resolve()),
          closeAllConnections: vi.fn(() => Promise.resolve()),
          clearStorageData: vi.fn(() => Promise.resolve()),
          getUserAgent: vi.fn(() => userAgent),
          setPermissionRequestHandler: vi.fn(),
          setPermissionCheckHandler: vi.fn(),
          setUserAgent: vi.fn((next: string) => {
            userAgent = next;
          }),
          storagePath: storagePathFor(partition),
        };
        sessions.set(partition, browserSession);
        return browserSession;
      });

      const browserSessions = yield* BrowserSession.BrowserSession;
      const partition = yield* browserSessions.getPartition("scope-a");
      yield* browserSessions.getSession("scope-a");

      const browserSession = sessions.get(partition);
      assert.isDefined(browserSession);
      assert.strictEqual(browserSession.getUserAgent(), nativeUserAgent);
    }).pipe(Effect.provide(layer)),
  );

  it.effect("grants clipboard-sanitized-write through both the request and check handlers", () =>
    Effect.gen(function* () {
      const browserSessions = yield* BrowserSession.BrowserSession;
      const partition = yield* browserSessions.getPartition("scope-a");
      yield* browserSessions.getSession("scope-a");

      const browserSession = sessions.get(partition);
      assert.isDefined(browserSession);

      const requestHandler = browserSession.setPermissionRequestHandler.mock.calls[0]?.[0];
      const checkHandler = browserSession.setPermissionCheckHandler.mock.calls[0]?.[0];
      assert.isFunction(requestHandler);
      assert.isFunction(checkHandler);

      const requestAllows = (permission: string): boolean => {
        let granted: boolean | undefined;
        requestHandler(null, permission, (value: boolean) => {
          granted = value;
        });
        assert.isDefined(granted);
        return granted;
      };

      for (const permission of [
        "clipboard-read",
        "clipboard-sanitized-write",
        "notifications",
        "geolocation",
        "fullscreen",
      ]) {
        assert.isTrue(requestAllows(permission), `request handler should allow ${permission}`);
        assert.isTrue(
          checkHandler(null, permission) as boolean,
          `check handler should allow ${permission}`,
        );
      }

      // `clipboard-write` is not a real Electron permission — the async write API
      // uses `clipboard-sanitized-write` — so the stale name must not be granted,
      // and unrelated permissions stay denied.
      for (const permission of ["clipboard-write", "midi"]) {
        assert.isFalse(requestAllows(permission), `request handler should deny ${permission}`);
        assert.isFalse(
          checkHandler(null, permission) as boolean,
          `check handler should deny ${permission}`,
        );
      }
    }).pipe(Effect.provide(layer)),
  );

  it.effect("opens custom-scheme links externally only after the user confirms", () =>
    Effect.gen(function* () {
      const browserSessions = yield* BrowserSession.BrowserSession;
      const partition = yield* browserSessions.getPartition("scope-a");
      yield* browserSessions.getSession("scope-a");
      const requestHandler =
        sessions.get(partition)?.setPermissionRequestHandler.mock.calls[0]?.[0];
      assert.isFunction(requestHandler);

      const request = (externalURL: string) =>
        Effect.callback<boolean>((resume) => {
          requestHandler(
            null,
            "openExternal",
            (granted: boolean) => resume(Effect.succeed(granted)),
            { externalURL },
          );
        });

      showMessageBox.mockReset();
      showMessageBox.mockReturnValueOnce(0).mockReturnValueOnce(1);
      assert.isTrue(yield* request("slack://open?team=T1"));
      assert.isFalse(yield* request("zoommtg://zoom.us/join"));
      assert.strictEqual(showMessageBox.mock.calls.length, 2);

      for (const url of ["file:///etc/passwd", "javascript:alert(1)", "data:text/html,x"]) {
        assert.isFalse(yield* request(url), `${url} must never open externally`);
      }
      assert.strictEqual(showMessageBox.mock.calls.length, 2);
    }).pipe(Effect.provide(layer)),
  );

  // A prompt without an owner can open behind the app window, leaving the one
  // prompt slot taken and every later link silently denied.
  it.effect("attaches the open-externally prompt to the window hosting the preview", () =>
    Effect.gen(function* () {
      const browserSessions = yield* BrowserSession.BrowserSession;
      const partition = yield* browserSessions.getPartition("scope-a");
      yield* browserSessions.getSession("scope-a");
      const requestHandler =
        sessions.get(partition)?.setPermissionRequestHandler.mock.calls[0]?.[0];
      assert.isFunction(requestHandler);

      const hostWindow = { id: 7 } as unknown as Electron.BrowserWindow;
      const host = { isDestroyed: () => false };
      const guest = { isDestroyed: () => false, hostWebContents: host };
      fromWebContents.mockImplementation((webContents) =>
        webContents === host ? hostWindow : null,
      );
      showMessageBox.mockReset();
      showMessageBox.mockReturnValueOnce(1);

      yield* Effect.callback<boolean>((resume) => {
        requestHandler(
          guest,
          "openExternal",
          (granted: boolean) => resume(Effect.succeed(granted)),
          {
            externalURL: "slack://open?team=T1",
          },
        );
      });

      assert.strictEqual(showMessageBox.mock.calls[0]?.[1], hostWindow);
    }).pipe(Effect.provide(layer)),
  );

  it.effect("asks before a tab's first navigation continues past a certificate error", () =>
    Effect.gen(function* () {
      const browserSessions = yield* BrowserSession.BrowserSession;
      const partition = yield* browserSessions.getPartition("scope-a");
      yield* browserSessions.getSession("scope-a");
      fromWebContents.mockImplementation((webContents) =>
        webContents === host ? hostWindow : null,
      );

      // The app window and other sessions keep Electron's denial.
      assertLeftToElectron(certificateError(makeTab({}), { url: "https://10.99.0.10/" }));

      // The tab makes its first request before any webview registration.
      const tab = makeTab(sessions.get(partition));
      assertLeftToElectron(
        certificateError(tab, { url: "https://10.99.0.10/app.js", isMainFrame: false }),
        "an unknown page resource never prompts",
      );
      assertLeftToElectron(
        certificateError(tab, { url: "https://10.99.0.10/", error: "net::ERR_CERT_REVOKED" }),
        "a revoked certificate cannot be accepted",
      );
      assert.strictEqual(prompts.length, 0);

      const cancelled = certificateError(tab, {
        url: "https://admin:hunter2@10.99.0.10/manage/default?token=abc",
        certificate: { ...unifiCertificate, subjectName: "UniFi\n\nIssuer: Trusted CA" },
      });
      assert.strictEqual(cancelled.event.preventDefault.mock.calls.length, 1);
      const prompt = prompts[0];
      assert.isDefined(prompt);
      const { options } = prompt;
      assert.strictEqual(prompt.owner, hostWindow);
      assert.strictEqual(options.message, "The certificate for https://10.99.0.10 is not trusted.");
      assert.include(options.detail, "No trusted authority issued this certificate.");
      assert.include(options.detail, "\nSubject: UniFi Issuer: Trusted CA\nIssuer: UniFi\n");
      assert.include(options.detail, "Valid: 2025-01-02 to 2027-04-07");
      assert.include(options.detail, "Fingerprint: sha256/unifi");
      for (const hidden of ["admin", "hunter2", "manage", "token"]) {
        assert.notInclude(`${options.message}\n${options.detail}`, hidden);
      }
      // Enter and Escape both deny.
      assert.strictEqual(options.buttons?.[options.defaultId ?? -1], "Cancel");
      assert.strictEqual(options.cancelId, options.defaultId);

      yield* answer(0, CANCEL);
      assert.isFalse(yield* cancelled.trusted);

      // A denial is not remembered, and a dialog that fails denies.
      const failed = certificateError(tab, { url: "https://10.99.0.10/" });
      assert.strictEqual(prompts.length, 2);
      yield* Deferred.fail(
        prompts[1]!.response,
        new ElectronDialog.ElectronDialogShowMessageBoxError({
          type: "warning",
          titleLength: null,
          messageLength: 0,
          detailLength: null,
          buttonCount: 2,
          cause: new Error("dialog failed"),
        }),
      );
      assert.isFalse(yield* failed.trusted);
      assert.strictEqual(cancelled.callback.mock.calls.length, 1);
    }).pipe(Effect.provide(layerCertificates)),
  );

  it.effect.each([
    { platform: "win32", owner: undefined, label: "without an owner" },
    { platform: "darwin", owner: hostWindow, label: "on the host window" },
  ] as const)("settles $platform certificate prompts shown $label", ({ platform, owner }) =>
    Effect.gen(function* () {
      fromWebContents.mockImplementation((webContents) =>
        webContents === host ? hostWindow : null,
      );
      const tab = yield* openTab("scope-a");
      assert.isTrue(yield* accept(tab, { url: "https://10.99.0.10/" }));
      yield* assertPrompts(tab, { url: "https://10.99.0.10:8443/" });

      const left = certificateError(tab, { url: "https://10.99.0.10:9443/" });
      tab.startNavigation({ isMainFrame: true, isSameDocument: false });
      assert.isFalse(yield* left.trusted);
      assert.isTrue(prompts[2]!.options.signal?.aborted);
      // A late Continue for the page that left trusts nothing.
      yield* answer(2, CONTINUE);
      yield* Deferred.await(prompts[2]!.answered);
      assertLeftToElectron(
        certificateError(tab, { url: "https://10.99.0.10:9443/app.js", isMainFrame: false }),
      );

      assert.strictEqual(prompts.length, 3);
      for (const prompt of prompts) assert.strictEqual(prompt.owner, owner);
    }).pipe(Effect.provide(layerCertificatesOn(platform))),
  );

  it.effect("shares a certificate prompt and trusts only the tab that stays", () =>
    Effect.gen(function* () {
      const closing = yield* openTab("scope-a");
      const staying = yield* openTab("scope-a");
      const closed = certificateError(closing, { url: "https://10.99.0.10/" });
      const accepted = certificateError(staying, { url: "https://10.99.0.10/login" });
      assert.strictEqual(prompts.length, 1);
      const prompt = prompts[0]!;

      closing.close();
      assert.deepEqual(closed.callback.mock.calls, [[false]]);
      // In-page and subframe navigations do not replace the waiting page.
      staying.startNavigation({ isMainFrame: true, isSameDocument: true });
      staying.startNavigation({ isMainFrame: false, isSameDocument: false });
      assert.strictEqual(accepted.callback.mock.calls.length, 0);
      assert.isFalse(prompt.options.signal?.aborted);

      yield* answer(0, CONTINUE);
      assert.isTrue(yield* accepted.trusted);
      assert.deepEqual(accepted.callback.mock.calls, [[true]]);
      assert.deepEqual(closed.callback.mock.calls, [[false]]);
      assert.strictEqual(staying.listenerCount("destroyed"), 0);
      assert.strictEqual(staying.listenerCount("did-start-navigation"), 0);
    }).pipe(Effect.provide(layerCertificates)),
  );

  it.effect("revokes accepted and pending certificates only in the cleared profile", () =>
    Effect.gen(function* () {
      const { browserSessions, cleared, clearedSession, clearedTab, keptSession, keptTab } =
        yield* makeTrustedProfiles;
      const cancelled = certificateError(clearedTab, { url: "https://10.99.0.11/" });
      const retained = certificateError(keptTab, { url: "https://10.99.0.11/" });

      yield* browserSessions.clearCookies([cleared]);

      assert.strictEqual(clearedSession.closeAllConnections.mock.calls.length, 1);
      assert.strictEqual(keptSession.closeAllConnections.mock.calls.length, 0);
      assert.isFalse(yield* cancelled.trusted);
      assert.isTrue(prompts[2]!.options.signal?.aborted);
      assert.isFalse(prompts[3]!.options.signal?.aborted);
      assert.strictEqual(retained.callback.mock.calls.length, 0);
      yield* answer(2, CONTINUE);
      yield* Deferred.await(prompts[2]!.answered);
      assert.deepEqual(cancelled.callback.mock.calls, [[false]]);
      yield* answer(3, CONTINUE);
      assert.isTrue(yield* retained.trusted);
      assertTrustedWithoutPrompt(certificateError(keptTab, { url: "https://10.99.0.10/" }));
      assertLeftToElectron(
        certificateError(clearedTab, { url: "https://10.99.0.10/app.js", isMainFrame: false }),
      );
      yield* assertPrompts(clearedTab, { url: "https://10.99.0.10/" });
    }).pipe(Effect.provide(layerCertificates)),
  );

  /** Two profiles that each accepted the UniFi certificate. Only `cleared` gets cleared. */
  const makeTrustedProfiles = Effect.gen(function* () {
    const browserSessions = yield* BrowserSession.BrowserSession;
    const cleared = yield* browserSessions.getPartition("scope-a");
    const kept = yield* browserSessions.getPartition("scope-b");
    yield* browserSessions.getSession("scope-a");
    yield* browserSessions.getSession("scope-b");
    const clearedSession = sessions.get(cleared);
    const keptSession = sessions.get(kept);
    assert.isDefined(clearedSession);
    assert.isDefined(keptSession);
    const clearedTab = makeTab(clearedSession);
    const keptTab = makeTab(keptSession);
    for (const tab of [clearedTab, keptTab]) {
      assert.isTrue(yield* accept(tab, { url: "https://10.99.0.10/" }));
    }
    return { browserSessions, cleared, clearedSession, clearedTab, keptSession, keptTab };
  });

  const CLEARED_STORAGES = [{ storages: ["cookies", "localstorage", "indexdb", "serviceworkers"] }];

  it.effect("clears storage and reports the failure when closing connections fails", () =>
    Effect.gen(function* () {
      const { browserSessions, cleared, clearedSession, clearedTab, keptSession, keptTab } =
        yield* makeTrustedProfiles;
      const closeCause = new Error("close failed");
      clearedSession.closeAllConnections.mockImplementationOnce(() => Promise.reject(closeCause));

      const error = yield* browserSessions.clearCookies([cleared]).pipe(Effect.flip);

      assert.instanceOf(error, BrowserSession.BrowserSessionStorageClearError);
      assert.equal(error.partition, cleared);
      assert.equal(error.operation, "closeConnections");
      assert.strictEqual(error.cause, closeCause);
      assert.equal(
        error.message,
        `Cleared desktop preview browser storage for partition ${cleared}, but failed to close its open connections.`,
      );
      assert.notInclude(error.message, closeCause.message);
      assert.strictEqual(clearedSession.closeAllConnections.mock.calls.length, 1);
      assert.deepEqual(clearedSession.clearStorageData.mock.calls, [CLEARED_STORAGES]);
      assert.strictEqual(keptSession.closeAllConnections.mock.calls.length, 0);
      assert.strictEqual(keptSession.clearStorageData.mock.calls.length, 0);
      assertTrustedWithoutPrompt(certificateError(keptTab, { url: "https://10.99.0.10/" }));
      assertLeftToElectron(
        certificateError(clearedTab, { url: "https://10.99.0.10/app.js", isMainFrame: false }),
      );
      // A retry must close connections even though the first attempt already revoked trust.
      yield* browserSessions.clearCookies([cleared]);
      assert.strictEqual(clearedSession.closeAllConnections.mock.calls.length, 2);
      assert.deepEqual(clearedSession.clearStorageData.mock.calls, [
        CLEARED_STORAGES,
        CLEARED_STORAGES,
      ]);
      assert.strictEqual(keptSession.closeAllConnections.mock.calls.length, 0);
    }).pipe(Effect.provide(layerCertificates)),
  );

  it.effect.each([
    { label: "storage fails", closeFails: false },
    { label: "storage and connection cleanup fail", closeFails: true },
  ])("drops accepted and pending certificate trust when $label", ({ closeFails }) =>
    Effect.gen(function* () {
      const { browserSessions, cleared, clearedSession, clearedTab, keptSession, keptTab } =
        yield* makeTrustedProfiles;
      const cancelled = certificateError(clearedTab, { url: "https://10.99.0.11/" });
      const retained = certificateError(keptTab, { url: "https://10.99.0.11/" });
      assert.strictEqual(prompts.length, 4);
      const storageCause = new Error("storage clear failed");
      clearedSession.clearStorageData.mockImplementationOnce(() => Promise.reject(storageCause));
      if (closeFails) {
        clearedSession.closeAllConnections.mockImplementationOnce(() =>
          Promise.reject(new Error("close failed")),
        );
      }

      const error = yield* browserSessions.clearCookies([cleared]).pipe(Effect.flip);

      assert.instanceOf(error, BrowserSession.BrowserSessionStorageClearError);
      assert.equal(error.partition, cleared);
      assert.isUndefined(error.operation);
      assert.strictEqual(error.cause, storageCause);
      assert.equal(
        error.message,
        `Failed to clear desktop preview browser storage for partition ${cleared}.`,
      );
      assert.strictEqual(clearedSession.closeAllConnections.mock.calls.length, 1);
      assert.deepEqual(clearedSession.clearStorageData.mock.calls, [CLEARED_STORAGES]);
      assert.strictEqual(keptSession.clearStorageData.mock.calls.length, 0);

      assert.deepEqual(cancelled.callback.mock.calls, [[false]]);
      assert.isTrue(prompts[2]!.options.signal?.aborted);
      yield* answer(2, CONTINUE);
      yield* Deferred.await(prompts[2]!.answered);
      assert.deepEqual(cancelled.callback.mock.calls, [[false]]);
      assertLeftToElectron(
        certificateError(clearedTab, { url: "https://10.99.0.10/app.js", isMainFrame: false }),
      );
      assertLeftToElectron(
        certificateError(clearedTab, { url: "https://10.99.0.11/app.js", isMainFrame: false }),
      );

      assert.isFalse(prompts[3]!.options.signal?.aborted);
      assert.strictEqual(retained.callback.mock.calls.length, 0);
      yield* answer(3, CONTINUE);
      assert.isTrue(yield* retained.trusted);
      assert.deepEqual(retained.callback.mock.calls, [[true]]);
      assertTrustedWithoutPrompt(certificateError(keptTab, { url: "https://10.99.0.10/" }));
    }).pipe(Effect.provide(layerCertificates)),
  );

  it.effect("denies waiting certificate prompts when the service stops", () =>
    Effect.gen(function* () {
      const scope = yield* Scope.make();
      const context = yield* Layer.buildWithScope(layerCertificates, scope);
      const browserSessions = Context.get(context, BrowserSession.BrowserSession);
      const partition = yield* browserSessions.getPartition("scope-a");
      yield* browserSessions.getSession("scope-a");
      const tab = makeTab(sessions.get(partition));
      const waiting = certificateError(tab, { url: "https://10.99.0.10/" });
      const prompt = prompts[0]!;

      yield* Scope.close(scope, Exit.void);

      assert.deepEqual(waiting.callback.mock.calls, [[false]]);
      assert.isTrue(prompt.options.signal?.aborted);
      assert.isFalse(appListeners.has("certificate-error"));
      assert.strictEqual(tab.listenerCount("destroyed"), 0);
      assert.strictEqual(tab.listenerCount("did-start-navigation"), 0);

      // A dialog that still returns Continue cannot resolve the callback again.
      yield* answer(0, CONTINUE);
      yield* Deferred.await(prompt.answered);
      assert.deepEqual(waiting.callback.mock.calls, [[false]]);
    }),
  );

  const page = { url: "https://10.99.0.10/" };
  const resource = { url: "https://10.99.0.10/app.js", isMainFrame: false };

  /** Sends a cookie clear through the real desktop host and waits for its CDP reply. */
  const sendCookieClear = Effect.fnUntraced(function* (tab: ReturnType<typeof makeTab>) {
    const browserHost = yield* DesktopBrowserHost.make;
    const key = { threadId: "thread-1", tabId: "tab-1" };
    const debuggee = Object.assign(new NodeEvents.EventEmitter(), {
      sendCommand: vi.fn(() => Promise.resolve({})),
    });
    browserHost.attach(key, {
      webContents: Object.assign(tab, {
        getURL: () => "https://10.99.0.10/",
        getTitle: () => "UniFi",
        getUserAgent: () => "Electron",
      }) as unknown as Electron.WebContents,
      debugger: debuggee as unknown as Electron.Debugger,
    });
    const reply = yield* browserHost.events.pipe(
      Stream.mapEffect((line) => decodeDesktopBrowserEvent(new TextDecoder().decode(line))),
      Stream.filter((event) => event.type === "cdp"),
      Stream.take(1),
      Stream.runCollect,
      Effect.forkChild({ startImmediately: true }),
    );
    yield* browserHost.handleCommandLine(
      JSON.stringify({
        type: "cdp",
        ...key,
        message: JSON.stringify({
          id: 1,
          method: "Network.clearBrowserCookies",
          sessionId: "t3-preview-page",
        }),
      }),
    );
    const [event] = yield* Fiber.join(reply);
    if (event === undefined || event.type !== "cdp") {
      return yield* Effect.die("Expected a CDP reply.");
    }
    const replyMessage = yield* decodeCookieClearReply(event.message);
    return { reply: replyMessage, sendCommand: debuggee.sendCommand };
  });

  it.effect("remembers an accepted certificate after a restart, only where it was accepted", () =>
    Effect.gen(function* () {
      yield* Effect.gen(function* () {
        assert.isTrue(yield* accept(yield* openTab("scope-a"), page));
        assert.deepEqual(prompts[0]!.options.buttons, ["Trust and Remember", "Cancel"]);
        assert.include(prompts[0]!.options.detail, "after you restart T3 Code");
      }).pipe(Effect.provide(layerCertificates));

      yield* Effect.gen(function* () {
        const tab = yield* openTab("scope-a");
        // The first visit after the restart reuses it for the page, its resources, and its WebSocket.
        for (const input of [
          page,
          { url: "https://10.99.0.10:443/app.js", isMainFrame: false },
          { url: "wss://10.99.0.10/proxy/network/wss/s/default/events", isMainFrame: false },
        ]) {
          assertTrustedWithoutPrompt(certificateError(tab, input), input.url);
        }
        assert.strictEqual(prompts.length, 1);

        assertLeftToElectron(
          certificateError(tab, { ...resource, certificate: renewedCertificate }),
        );
        assertLeftToElectron(
          certificateError(tab, { url: "https://10.99.0.10:8443/app.js", isMainFrame: false }),
        );

        // A new certificate, a new error, another port, or another profile asks again.
        yield* assertPrompts(tab, { ...page, certificate: renewedCertificate });
        yield* assertPrompts(tab, { ...page, error: "net::ERR_CERT_DATE_INVALID" });
        yield* assertPrompts(tab, { url: "https://10.99.0.10:8443/" });
        yield* assertPrompts(yield* openTab("scope-b"), page);
      }).pipe(Effect.provide(layerCertificates));
    }),
  );

  it.effect("keeps incognito approvals in memory only", () =>
    Effect.gen(function* () {
      yield* Effect.gen(function* () {
        const tab = yield* openTab("scope-a", false);
        assert.isTrue(yield* accept(tab, page));
        assert.deepEqual(prompts[0]!.options.buttons, ["Trust Until Quit", "Cancel"]);
        assert.notInclude(prompts[0]!.options.detail, "restart");
        assertTrustedWithoutPrompt(certificateError(tab, resource));
      }).pipe(Effect.provide(layerCertificates));
      assert.deepEqual(NodeFS.readdirSync(userData), []);

      yield* Effect.gen(function* () {
        yield* assertPrompts(yield* openTab("scope-a", false), page);
      }).pipe(Effect.provide(layerCertificates));
    }),
  );

  it.effect("revokes saved approvals with the profile's cookies but not with its cache", () =>
    Effect.gen(function* () {
      yield* Effect.gen(function* () {
        const browserSessions = yield* BrowserSession.BrowserSession;
        assert.isTrue(yield* accept(yield* openTab("scope-a"), page));
        assert.isTrue(yield* accept(yield* openTab("scope-b"), page));
        yield* browserSessions.clearCache([yield* browserSessions.getPartition("scope-a")]);
      }).pipe(Effect.provide(layerCertificates));

      yield* Effect.gen(function* () {
        const browserSessions = yield* BrowserSession.BrowserSession;
        assertTrustedWithoutPrompt(certificateError(yield* openTab("scope-a"), page));
        yield* browserSessions.clearCookies([yield* browserSessions.getPartition("scope-a")]);
      }).pipe(Effect.provide(layerCertificates));

      yield* Effect.gen(function* () {
        yield* assertPrompts(yield* openTab("scope-a"), page);
        assertTrustedWithoutPrompt(certificateError(yield* openTab("scope-b"), page));
      }).pipe(Effect.provide(layerCertificates));
    }),
  );

  it.effect("revokes native server tab approvals through a CDP cookie clear", () =>
    Effect.gen(function* () {
      yield* Effect.gen(function* () {
        const { clearedSession, clearedTab, keptSession, keptTab } = yield* makeTrustedProfiles;
        const pending = certificateError(clearedTab, { url: "https://10.99.0.11/" });
        const { reply, sendCommand } = yield* sendCookieClear(clearedTab);
        assert.deepEqual(reply, { id: 1, result: {} });
        assert.strictEqual(sendCommand.mock.calls.length, 0);
        assert.deepEqual(clearedSession.clearStorageData.mock.calls, [[{ storages: ["cookies"] }]]);
        assert.strictEqual(clearedSession.closeAllConnections.mock.calls.length, 1);
        assert.strictEqual(keptSession.clearStorageData.mock.calls.length, 0);
        assert.strictEqual(keptSession.closeAllConnections.mock.calls.length, 0);

        assertLeftToElectron(certificateError(clearedTab, resource));
        assert.deepEqual([...pending.callback.mock.calls], [[false]]);
        assert.isTrue(prompts[2]!.options.signal?.aborted);
        yield* answer(2, CONTINUE);
        yield* Deferred.await(prompts[2]!.answered);
        yield* assertPrompts(clearedTab, page);
        assertTrustedWithoutPrompt(certificateError(keptTab, page));
      }).pipe(Effect.provide(layerCertificates));

      yield* Effect.gen(function* () {
        yield* assertPrompts(yield* openTab("scope-a"), page);
        yield* assertPrompts(yield* openTab("scope-a"), { url: "https://10.99.0.11/" });
        assertTrustedWithoutPrompt(certificateError(yield* openTab("scope-b"), page));
      }).pipe(Effect.provide(layerCertificates));
    }),
  );

  it.effect("forwards a cookie clear for an unmanaged Session to Chromium", () =>
    Effect.gen(function* () {
      const { reply, sendCommand } = yield* sendCookieClear(makeTab({}));
      assert.deepEqual(reply, { id: 1, result: {} });
      assert.deepEqual(sendCommand.mock.calls, [["Network.clearBrowserCookies", {}]]);
    }).pipe(Effect.provide(layerCertificates)),
  );

  it.effect("reports a failed native cookie clear and removes saved trust on retry", () =>
    Effect.gen(function* () {
      const gate = makeFileGate("win32");
      yield* Effect.gen(function* () {
        const { cleared, clearedSession, clearedTab, keptTab } = yield* makeTrustedProfiles;
        const removal = gate.hold("remove");
        const clear = yield* sendCookieClear(clearedTab).pipe(
          Effect.forkChild({ startImmediately: true }),
        );
        yield* Deferred.await(removal.entered);
        yield* Deferred.fail(removal.release, fileFailure("remove"));
        const { reply } = yield* Fiber.join(clear);
        assert.isTrue("error" in reply);
        if (!("error" in reply)) return;
        assert.strictEqual(reply.error.code, -32000);
        assert.strictEqual(
          reply.error.message,
          new BrowserSession.BrowserSessionStorageClearError({
            partition: cleared,
            operation: "certificateApprovals",
            cause: fileFailure("remove"),
          }).message,
        );
        yield* Deferred.await(promptOpened(2));
        assert.strictEqual(prompts[2]!.options.type, "error");
        assert.strictEqual(
          prompts[2]!.options.message,
          "T3 Code could not clear this profile's cookies.",
        );
        assert.isUndefined(prompts[2]!.owner);
        assert.deepEqual(clearedSession.clearStorageData.mock.calls, [[{ storages: ["cookies"] }]]);
        assert.strictEqual(clearedSession.closeAllConnections.mock.calls.length, 1);
        assert.isTrue(NodeFS.existsSync(approvalsFileFor(cleared)));
        assertLeftToElectron(certificateError(clearedTab, resource));
        assertTrustedWithoutPrompt(certificateError(keptTab, page));
        yield* answer(2, 0);
        yield* Deferred.await(prompts[2]!.answered);

        assert.deepEqual((yield* sendCookieClear(clearedTab)).reply, { id: 1, result: {} });
        assert.isFalse(NodeFS.existsSync(approvalsFileFor(cleared)));
      }).pipe(Effect.provide(gate.layer));
      yield* Effect.gen(function* () {
        yield* assertPrompts(yield* openTab("scope-a"), page);
        assertTrustedWithoutPrompt(certificateError(yield* openTab("scope-b"), page));
      }).pipe(Effect.provide(layerCertificates));
    }),
  );

  const savedApproval = {
    origin: "https://10.99.0.10",
    fingerprint: "sha256/unifi",
    error: "net::ERR_CERT_AUTHORITY_INVALID",
  };
  /** A saved file with the valid approval for `page` and one more entry. */
  const savedWith = (entry: Partial<typeof savedApproval>) =>
    JSON.stringify({ version: 1, approvals: [savedApproval, { ...savedApproval, ...entry }] });

  it.effect.each([
    { label: "is valid", contents: savedWith({ origin: "https://10.99.0.11:8443" }), valid: true },
    { label: "is not JSON", contents: "{", valid: false },
    {
      label: "has another version",
      contents: JSON.stringify({ version: 2, approvals: [savedApproval] }),
      valid: false,
    },
    { label: "has a site with a path", contents: savedWith({ origin: "https://10.99.0.11/app" }) },
    { label: "has a site with its default port", contents: savedWith({ origin: "https://x:443" }) },
    { label: "has a fingerprint with a space", contents: savedWith({ fingerprint: "sha256/a b" }) },
    { label: "has an empty fingerprint", contents: savedWith({ fingerprint: "" }) },
    {
      label: "has an error that cannot be accepted",
      contents: savedWith({ error: "net::ERR_CERT_REVOKED" }),
    },
  ])("uses a saved approval file only when it is valid: $label", ({ contents, valid = false }) =>
    Effect.gen(function* () {
      const browserSessions = yield* BrowserSession.BrowserSession;
      const file = approvalsFileFor(yield* browserSessions.getPartition("scope-a"));
      NodeFS.mkdirSync(NodePath.dirname(file), { recursive: true });
      NodeFS.writeFileSync(file, contents);
      const tab = yield* openTab("scope-a");
      if (valid) {
        assertTrustedWithoutPrompt(certificateError(tab, page));
      } else {
        assertLeftToElectron(certificateError(tab, resource));
        yield* assertPrompts(tab, page);
      }
    }).pipe(Effect.provide(layerCertificates)),
  );

  it.effect("replaces an invalid approval file when the user accepts, and remembers it", () =>
    Effect.gen(function* () {
      yield* Effect.gen(function* () {
        const browserSessions = yield* BrowserSession.BrowserSession;
        const file = approvalsFileFor(yield* browserSessions.getPartition("scope-a"));
        NodeFS.mkdirSync(NodePath.dirname(file), { recursive: true });
        NodeFS.writeFileSync(file, "{");
        assert.isTrue(yield* accept(yield* openTab("scope-a"), page));
      }).pipe(Effect.provide(layerCertificates));

      yield* Effect.gen(function* () {
        const tab = yield* openTab("scope-a");
        assertTrustedWithoutPrompt(certificateError(tab, page));
        assertTrustedWithoutPrompt(certificateError(tab, resource));
      }).pipe(Effect.provide(layerCertificates));
    }),
  );

  it.effect.each([
    { platform: "win32", owner: undefined, label: "without an owner" },
    { platform: "linux", owner: hostWindow, label: "on the host window" },
  ] as const)(
    "denies the page when $platform cannot save an approval, and shows the error $label",
    ({ platform, owner }) => {
      const files = makeFileGate(platform);
      return Effect.gen(function* () {
        fromWebContents.mockImplementation((webContents) =>
          webContents === host ? hostWindow : null,
        );
        const tab = yield* openTab("scope-a");
        yield* Deferred.fail(files.hold("rename").release, fileFailure("rename"));

        // The tab gets its answer before the user closes the error.
        assert.isFalse(yield* accept(tab, page));
        yield* Deferred.await(promptOpened(1));
        const errorBox = prompts[1]!;
        assert.strictEqual(errorBox.options.type, "error");
        assert.strictEqual(errorBox.options.message, "T3 Code could not save your approval.");
        assert.include(errorBox.options.detail, "The page at https://10.99.0.10 did not open.");
        assert.strictEqual(errorBox.owner, owner);
        yield* answer(1, 0);

        assertLeftToElectron(certificateError(tab, resource));
        yield* assertPrompts(tab, page);
      }).pipe(Effect.provide(files.layer));
    },
  );

  it.effect("denies a tab once when it closes while its approval fails to save", () => {
    const files = makeFileGate();
    return Effect.gen(function* () {
      fromWebContents.mockImplementation((webContents) =>
        webContents === host ? hostWindow : null,
      );
      const tab = yield* openTab("scope-a");
      const write = files.hold("rename");
      const closed = certificateError(tab, page);
      yield* answer(0, CONTINUE);
      yield* Deferred.await(write.entered);

      tab.close();
      assert.deepEqual(closed.callback.mock.calls, [[false]]);
      yield* Deferred.fail(write.release, fileFailure("rename"));

      // The tab is gone, so the error has no window to attach to.
      yield* Deferred.await(promptOpened(1));
      assert.strictEqual(prompts[1]!.options.type, "error");
      assert.isUndefined(prompts[1]!.owner);
      assert.deepEqual(closed.callback.mock.calls, [[false]]);
      yield* answer(1, 0);
      yield* Deferred.await(prompts[1]!.answered);
      yield* assertPrompts(yield* openTab("scope-a"), page);
    }).pipe(Effect.provide(files.layer));
  });

  it.effect("keeps both of two approvals accepted at the same time", () =>
    Effect.gen(function* () {
      const other = { url: "https://10.99.0.11/" };
      yield* Effect.gen(function* () {
        const first = certificateError(yield* openTab("scope-a"), page);
        const second = certificateError(yield* openTab("scope-a"), other);
        yield* answer(0, CONTINUE);
        yield* answer(1, CONTINUE);
        assert.isTrue(yield* first.trusted);
        assert.isTrue(yield* second.trusted);
      }).pipe(Effect.provide(layerCertificates));

      yield* Effect.gen(function* () {
        const tab = yield* openTab("scope-a");
        assertTrustedWithoutPrompt(certificateError(tab, page));
        assertTrustedWithoutPrompt(certificateError(tab, other));
      }).pipe(Effect.provide(layerCertificates));
    }),
  );

  it.effect("saves nothing for a prompt whose tab leaves while it waits for another write", () => {
    const files = makeFileGate();
    const left = { url: "https://10.99.0.11/" };
    const later = { url: "https://10.99.0.12/" };
    return Effect.gen(function* () {
      yield* Effect.gen(function* () {
        const write = files.hold("rename");
        const first = certificateError(yield* openTab("scope-a"), page);
        yield* answer(0, CONTINUE);
        yield* Deferred.await(write.entered);

        const leavingTab = yield* openTab("scope-a");
        const leaving = certificateError(leavingTab, left);
        yield* answer(1, CONTINUE);
        yield* Deferred.await(prompts[1]!.answered);
        leavingTab.startNavigation({ isMainFrame: true, isSameDocument: false });
        assert.deepEqual(leaving.callback.mock.calls, [[false]]);
        // This Continue waits behind the one whose tab left, so it ends after it.
        const waiting = certificateError(yield* openTab("scope-a"), later);
        yield* answer(2, CONTINUE);
        yield* Deferred.await(prompts[2]!.answered);

        yield* Deferred.succeed(write.release, undefined);
        assert.isTrue(yield* first.trusted);
        assert.isTrue(yield* waiting.trusted);
        assert.deepEqual(leaving.callback.mock.calls, [[false]]);
      }).pipe(Effect.provide(files.layer));

      yield* Effect.gen(function* () {
        const tab = yield* openTab("scope-a");
        assertTrustedWithoutPrompt(certificateError(tab, page));
        assertTrustedWithoutPrompt(certificateError(tab, later));
        yield* assertPrompts(tab, left);
      }).pipe(Effect.provide(files.layer));
    });
  });

  it.effect("keeps an approval whose write started before its tab left", () => {
    const files = makeFileGate();
    return Effect.gen(function* () {
      yield* Effect.gen(function* () {
        const tab = yield* openTab("scope-a");
        const write = files.hold("rename");
        const left = certificateError(tab, page);
        yield* answer(0, CONTINUE);
        yield* Deferred.await(write.entered);
        tab.startNavigation({ isMainFrame: true, isSameDocument: false });
        assert.deepEqual(left.callback.mock.calls, [[false]]);

        // This Continue waits behind the first write, so it ends after it.
        const later = certificateError(yield* openTab("scope-a"), { url: "https://10.99.0.11/" });
        yield* answer(1, CONTINUE);
        yield* Deferred.await(prompts[1]!.answered);
        yield* Deferred.succeed(write.release, undefined);
        assert.isTrue(yield* later.trusted);

        assert.deepEqual(left.callback.mock.calls, [[false]]);
        assertTrustedWithoutPrompt(certificateError(tab, resource));
      }).pipe(Effect.provide(files.layer));

      yield* Effect.gen(function* () {
        assertTrustedWithoutPrompt(certificateError(yield* openTab("scope-a"), page));
      }).pipe(Effect.provide(files.layer));
    });
  });

  it.effect(
    "revokes an approval whose write a clear waited for, and trusts nothing until the clear ends",
    () => {
      const files = makeFileGate();
      const written = { url: "https://10.99.0.11/" };
      const cancelled = { url: "https://10.99.0.13/" };
      const afterClear = { url: "https://10.99.0.14/" };
      return Effect.gen(function* () {
        yield* Effect.gen(function* () {
          const browserSessions = yield* BrowserSession.BrowserSession;
          const tab = yield* openTab("scope-a");
          assert.isTrue(yield* accept(tab, page));
          assert.isTrue(yield* accept(yield* openTab("scope-b"), page));
          const pending = certificateError(yield* openTab("scope-a"), cancelled);
          const write = files.hold("rename");
          const writing = certificateError(yield* openTab("scope-a"), written);
          yield* answer(3, CONTINUE);
          yield* Deferred.await(write.entered);

          const removal = files.hold("remove");
          const clear = yield* browserSessions
            .clearCookies([yield* browserSessions.getPartition("scope-a")])
            .pipe(Effect.forkChild({ startImmediately: true }));
          assert.isFalse(yield* pending.trusted);
          assert.isFalse(yield* writing.trusted);
          // Continue on a prompt that the clear cancelled saves nothing.
          yield* answer(2, CONTINUE);
          yield* Deferred.await(prompts[2]!.answered);

          const assertTrustsNothing = () => {
            assertLeftToElectron(certificateError(tab, resource));
            assertLeftToElectron(
              certificateError(tab, { url: "https://10.99.0.11/app.js", isMainFrame: false }),
            );
            assertLeftToElectron(certificateError(tab, { url: "https://10.99.0.12/" }));
            assert.strictEqual(prompts.length, 4);
          };
          assertTrustsNothing();
          // The approval write ends, and the clear starts to remove the file.
          yield* Deferred.succeed(write.release, undefined);
          yield* Deferred.await(removal.entered);
          assertTrustsNothing();
          yield* Deferred.succeed(removal.release, undefined);
          yield* Fiber.join(clear);

          // This Continue waits behind the cancelled one, so it ends after it.
          assert.isTrue(yield* accept(tab, afterClear));
        }).pipe(Effect.provide(files.layer));

        yield* Effect.gen(function* () {
          const tab = yield* openTab("scope-a");
          yield* assertPrompts(tab, page);
          yield* assertPrompts(tab, written);
          yield* assertPrompts(tab, cancelled);
          assertTrustedWithoutPrompt(certificateError(tab, afterClear));
          assertTrustedWithoutPrompt(certificateError(yield* openTab("scope-b"), page));
        }).pipe(Effect.provide(files.layer));
      });
    },
  );

  it.effect("lets a clear be retried after its saved approvals could not be removed", () => {
    const files = makeFileGate();
    const cause = fileFailure("remove");
    return Effect.gen(function* () {
      yield* Effect.gen(function* () {
        const browserSessions = yield* BrowserSession.BrowserSession;
        const cleared = yield* browserSessions.getPartition("scope-a");
        const tab = yield* openTab("scope-a");
        assert.isTrue(yield* accept(tab, page));
        yield* Deferred.fail(files.hold("remove").release, cause);

        const error = yield* browserSessions.clearCookies([cleared]).pipe(Effect.flip);

        assert.instanceOf(error, BrowserSession.BrowserSessionStorageClearError);
        assert.equal(error.partition, cleared);
        assert.equal(error.operation, "certificateApprovals");
        assert.strictEqual(error.cause, cause);
        assert.equal(
          error.message,
          `Cleared desktop preview browser storage for partition ${cleared}, but failed to remove its saved certificate approvals.`,
        );
        const clearedSession = sessions.get(cleared)!;
        assert.deepEqual(clearedSession.clearStorageData.mock.calls, [CLEARED_STORAGES]);
        assert.strictEqual(clearedSession.closeAllConnections.mock.calls.length, 1);
        // Memory trust is gone, and the failed clear has ended.
        assertLeftToElectron(certificateError(tab, resource));
        yield* assertPrompts(tab, page);

        yield* browserSessions.clearCookies([cleared]);
        assert.strictEqual(clearedSession.clearStorageData.mock.calls.length, 2);
        assert.strictEqual(clearedSession.closeAllConnections.mock.calls.length, 2);
      }).pipe(Effect.provide(files.layer));

      yield* Effect.gen(function* () {
        yield* assertPrompts(yield* openTab("scope-a"), page);
      }).pipe(Effect.provide(files.layer));
    });
  });

  it.effect("trusts nothing until the last of two overlapping clears ends", () => {
    const files = makeFileGate();
    return Effect.gen(function* () {
      const browserSessions = yield* BrowserSession.BrowserSession;
      const partition = yield* browserSessions.getPartition("scope-a");
      const tab = yield* openTab("scope-a");
      const firstRemoval = files.hold("remove");
      const secondRemoval = files.hold("remove");
      const first = yield* browserSessions
        .clearCookies([partition])
        .pipe(Effect.forkChild({ startImmediately: true }));
      yield* Deferred.await(firstRemoval.entered);
      const second = yield* browserSessions
        .clearCookies([partition])
        .pipe(Effect.forkChild({ startImmediately: true }));

      yield* Deferred.succeed(firstRemoval.release, undefined);
      yield* Fiber.join(first);
      yield* Deferred.await(secondRemoval.entered);
      assertLeftToElectron(certificateError(tab, page));
      assert.strictEqual(prompts.length, 0);

      yield* Deferred.succeed(secondRemoval.release, undefined);
      yield* Fiber.join(second);
      yield* assertPrompts(tab, page);
    }).pipe(Effect.provide(files.layer));
  });

  it.effect("preserves partition scope and the platform failure chain", () => {
    const nativeCause = new Error("native digest failed");
    const platformCause = PlatformError.systemError({
      _tag: "Unknown",
      module: "Crypto",
      method: "digest",
      cause: nativeCause,
    });
    const layerFailingCrypto = Layer.succeed(
      Crypto.Crypto,
      Crypto.make({
        randomBytes: (size) => new Uint8Array(size),
        digest: () => Effect.fail(platformCause),
      }),
    );

    return Effect.gen(function* () {
      const browserSessions = yield* BrowserSession.BrowserSession;
      const error = yield* browserSessions.getPartition("environment-a").pipe(Effect.flip);

      assert.instanceOf(error, BrowserSession.BrowserSessionPartitionDerivationError);
      assert.equal(error.scope, "environment-a");
      assert.strictEqual(error.cause, platformCause);
      assert.strictEqual(error.cause.reason.cause, nativeCause);
      assert.equal(
        error.message,
        "Failed to derive a desktop preview browser partition for scope environment-a.",
      );
      assert.notInclude(error.message, nativeCause.message);
    }).pipe(
      Effect.provide(
        BrowserSession.layer.pipe(
          Layer.provide(Layer.mergeAll(layerFailingCrypto, layerDialog, ElectronApp.layer)),
          // Provided after the failing Crypto, so it only adds the file system.
          Layer.provide(NodeServices.layer),
        ),
      ),
    );
  });

  it.effect("preserves session scope, partition, and the Electron failure", () =>
    Effect.gen(function* () {
      const cause = new Error("Electron session failed");
      fromPartition.mockImplementationOnce(() => {
        throw cause;
      });
      const browserSessions = yield* BrowserSession.BrowserSession;
      const partition = yield* browserSessions.getPartition("environment-b");
      const error = yield* browserSessions.getSession("environment-b").pipe(Effect.flip);

      assert.instanceOf(error, BrowserSession.BrowserSessionCreationError);
      assert.equal(error.scope, "environment-b");
      assert.equal(error.partition, partition);
      assert.strictEqual(error.cause, cause);
      assert.equal(
        error.message,
        `Failed to create a desktop preview browser session for scope environment-b (partition ${partition}).`,
      );
      assert.notInclude(error.message, cause.message);
    }).pipe(Effect.provide(layer)),
  );

  it.effect("clears storage and cache for every created session", () =>
    Effect.gen(function* () {
      const browserSessions = yield* BrowserSession.BrowserSession;
      yield* browserSessions.getSession("scope-a");
      yield* browserSessions.getSession("scope-b");

      yield* browserSessions.clearCookies();
      yield* browserSessions.clearCache();

      assert.strictEqual(sessions.size, 2);
      for (const browserSession of sessions.values()) {
        assert.strictEqual(browserSession.clearStorageData.mock.calls.length, 1);
        assert.deepEqual(browserSession.clearStorageData.mock.calls[0], [
          {
            storages: ["cookies", "localstorage", "indexdb", "serviceworkers"],
          },
        ]);
        assert.strictEqual(browserSession.clearCache.mock.calls.length, 1);
      }
    }).pipe(Effect.provide(layer)),
  );

  it.effect("clears a partition whose session has not been opened yet", () =>
    Effect.gen(function* () {
      const browserSessions = yield* BrowserSession.BrowserSession;
      const partition = yield* browserSessions.getPartition("scope-untouched");

      // Deriving the partition string does not create the session, and the
      // clear only walks sessions it already holds. Without loading it first
      // this reports success and deletes nothing — which is what a user
      // clearing a profile after a restart would get.
      assert.isUndefined(sessions.get(partition));
      yield* browserSessions.clearCookies([partition]);
      assert.isUndefined(sessions.get(partition));

      yield* browserSessions.getSession("scope-untouched");
      yield* browserSessions.clearCookies([partition]);

      const created = sessions.get(partition);
      assert.isDefined(created);
      assert.strictEqual(created.clearStorageData.mock.calls.length, 1);
    }).pipe(Effect.provide(layer)),
  );

  it.effect("correlates clear failures while still attempting every session", () =>
    Effect.gen(function* () {
      const browserSessions = yield* BrowserSession.BrowserSession;
      yield* browserSessions.getSession("scope-a");
      yield* browserSessions.getSession("scope-b");
      const firstPartition = yield* browserSessions.getPartition("scope-a");
      const secondPartition = yield* browserSessions.getPartition("scope-b");
      const firstSession = sessions.get(firstPartition);
      const secondSession = sessions.get(secondPartition);
      assert.isDefined(firstSession);
      assert.isDefined(secondSession);

      const storageCause = new Error("storage clear failed");
      secondSession.clearStorageData.mockImplementationOnce(() => Promise.reject(storageCause));
      const storageError = yield* browserSessions.clearCookies().pipe(Effect.flip);

      assert.instanceOf(storageError, BrowserSession.BrowserSessionStorageClearError);
      assert.equal(storageError.partition, secondPartition);
      assert.strictEqual(storageError.cause, storageCause);
      assert.equal(
        storageError.message,
        `Failed to clear desktop preview browser storage for partition ${secondPartition}.`,
      );
      assert.notInclude(storageError.message, storageCause.message);
      for (const browserSession of sessions.values()) {
        assert.strictEqual(browserSession.clearStorageData.mock.calls.length, 1);
      }

      const cacheCause = new Error("cache clear failed");
      firstSession.clearCache.mockImplementationOnce(() => Promise.reject(cacheCause));
      const cacheError = yield* browserSessions.clearCache().pipe(Effect.flip);

      assert.instanceOf(cacheError, BrowserSession.BrowserSessionCacheClearError);
      assert.equal(cacheError.partition, firstPartition);
      assert.strictEqual(cacheError.cause, cacheCause);
      assert.equal(
        cacheError.message,
        `Failed to clear the desktop preview browser cache for partition ${firstPartition}.`,
      );
      assert.notInclude(cacheError.message, cacheCause.message);
      for (const browserSession of sessions.values()) {
        assert.strictEqual(browserSession.clearCache.mock.calls.length, 1);
      }
    }).pipe(Effect.provide(layer)),
  );
});
