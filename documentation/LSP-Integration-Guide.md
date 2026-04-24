---
layout: default
title: OpenJML LSP Integration Guide
---
# OpenJML Language Server Integration Guide

David R. Cok -- April 2026 (cf. https://github.com/OpenJML/OpenJML)

This document describes how to connect an LSP client to the OpenJML language server.
It covers the server's capabilities, configuration, wire protocol, and known limitations.
The intended audience is a developer integrating the server into an editor, IDE, or
build tool. Note that some such integrations are available as companion projects to this one
in the OpenJML github project; as of this writing these are VSCode and Eclipse.

---

## Overview

The OpenJML language server provides Java Modeling Language (JML) checking for Java
source files.  The OpenJML tool is built on OpenJDK, so this server is also an
OpenJDK language server, with JML capability included.

Besides conventional LSP services (e.g., syntax coloring),
the server enables some OpenJML capabilities. These are the same capabilities that
are available in the OpenJML command-line tool.

- **`--check`** — JML type-checking. Fast; runs on every edit or save. Reports syntax
  errors, type errors, and JML annotation errors as LSP diagnostics.

- **`--esc`** — Extended Static Checking. Slower; invokes an SMT solver to prove or
  disprove JML specifications such as method postconditions and invariants. Reports verification failures as LSP
  diagnostics and updates per-method status badges (code lenses).

- **`--rac`** — Compile Java code with JML assertions as .class files with runtime checks ("Runtime-Assertion-Checking").

The language server links in OpenJML and they run together in a single JVM process, using separate, concurrent threads for long-running processes.
The server process may spawn one or more subprocesses to execute SMT proof checks.
Any diagnostics, perhaps accumulated,
are sent to the client using a `textDocument/publishDiagnostics` notification.

---

## OpenJML

The server requires an installation of OpenJML, which can be downloaded from https://github.com/openjml/openjml/releases/latest.
The download, when unzipped into a clean directory, contains a full working version of OpenJML.
At the top-level of the installation is a bash script named `openjml-lsp`; executing it launches the server,
 as described below.
 
## Starting the Server

### Transport

The server communicates with the client exclusively over **stdio** (JSON-RPC on stdin/
stdout). There is no TCP socket or named-pipe option.

Stdout (except for JSON-RPC communications) and stderr from the server and openjml are redirected to a log file by the launcher script, so Java
stack traces and internal debug messages go there, not to the client.
In the development mode, the log is `/tmp/openjml-lsp-debug.log`, truncated on each restart.
In a release installation the log is `~/.openjml/logs/openjml-lsp-<pid>.log`, unique per server instance.
Either default can be overridden by setting `OPENJML_LSP_LOG` before starting the server. The server also, on startup,
deletes old logs that are not in current use.

### Launcher Script

The server is started by the `openjml-lsp` bash script in the installation root:

```
openjml-lsp
```

No arguments are required or supported on the command line; all configuration is passed
through LSP initialization options or `workspace/didChangeConfiguration` or environment variables.
The script may not be moved because it expects other installed components to be in specific relative locations
with respect to the script itself.

The server is released as part of an OpenJML release and
requires an installation of OpenJML to operate. 

The script expects one of two layouts:

- **Release layout** (`jdk/` sibling directory present): uses `jdk/`, `openjml-lsp.jar`,
  and `lsp/org.eclipse.lsp4j-*.jar` relative to the installation directory. A public OpenJML release,
  unzipped into some empty directory, will have the correct layout.
- **Development layout** (sibling `OpenJMLsrc/` folder): uses the build output from
  `OpenJMLsrc/build/*/jdk` and `build/openjml-lsp.jar` from the `OpenJMLlsp` directory.
  An OpenJML development environment, as described in the OpenJML wiki pages, has this layout.

FIXME: double-check all the above paths

### Required Files

| File | Purpose |
|---|---|
| `openjml-lsp` | Server launcher script |
| `lsp/openjml-lsp.jar` | Server logic |
| `lsp/org.eclipse.lsp4j-1.0.0.jar` | LSP4J protocol library |
| `lsp/org.eclipse.lsp4j.jsonrpc-1.0.0.jar` | JSON-RPC transport |
| `jdk/bin/java` | JDK used to run the server (bundled with OpenJML) |

### Environment Variables

The launcher sets these if not already present in the environment:

| Variable | Default | Purpose |
|---|---|---|
| `OPENJML_INSTALL` | Directory containing `openjml-lsp` script | Root of the OpenJML installation |
| `OPENJML_SPECS` | `$OPENJML_INSTALL/specs` | Path to bundled JML specification files |
| `OPENJML_SOLVERS` | `$OPENJML_INSTALL` | Directory containing SMT solver binaries |
| `OPENJML_LSP_LOG` | fixed value (cf. "Error Handling and Logging") | Destination file for server log messages |
| `OPENJML_SERVER_PATH` | _(unset)_ | Client-side: when set, overrides all other server-path discovery and points directly to the `openjml-lsp` script; useful during extension development (e.g. via `launch.json`) |

The default values of the environment variables are sufficient in nearly all circumstances.
A client may override any of these before spawning the server process.

### Eclipse-only: Server Path System Property

The Eclipse plugin resolves the `openjml-lsp` launcher path in this order:

1. The Java system property `openjml.lsp.server.path` — intended for the test harness
   and development setups where modifying workspace preferences is inconvenient.
2. The value stored in the OpenJML Preferences page (`openjml.lspServerPath`), which is an absolute path to either an installation folder or to an instanceof `openjml-lsp` in an installation folder.
3. `openjml-lsp` on `PATH` (last resort).

To use option 1, pass `-Dopenjml.lsp.server.path=/path/to/openjml-lsp` in the Eclipse
JVM arguments (e.g., in `eclipse.ini` or a launch configuration).

### JVM Notes

The server's JVM requires several --add-exports flags to expose OpenJDK compiler internals (com.sun.tools.javac.*, org.jmlspecs.openjml.*) to the unnamed     
module. Gson does not require any flags: it is unconditionally exported from jdk.compiler via its module-info.java. 
All required flags are set automatically by the launcher script via $OPENJML_EXPORTS; client integrators do not need to set them.

Do **not** put a separate Gson jar on the classpath; that creates a split-package that the JVM
will refuse to load.

---

## LSP Handshake

### `initialize` Request

The server reads configuration from `initializationOptions` in the `initialize` request.
The value is deserialized directly as an `OpenJMLSettings` object (no enclosing key).

Example:

```json
{
  "initializationOptions": {
    "specsPath": "/path/to/Specs/specs",
    "checkTriggerOn": "edit",
    "escTriggerOn": "manual"
  }
}
```

See the [Configuration](#configuration) section for all recognized fields.

### `initialize` Response (ServerCapabilities)

The server advertises the following capabilities:

| Capability | Value |
|---|---|
| `textDocumentSync` | `2` (Incremental) by default; `1` (Full) when `incrementalSync` is `false` |
| `hoverProvider` | `true` |
| `codeLensProvider` | `{ "resolveProvider": false }` |
| `completionProvider` | trigger characters: `\`, `@` |
| `documentSymbolProvider` | `true` |
| `foldingRangeProvider` | `true` |
| `workspaceSymbolProvider` | `true` |
| `definitionProvider` | `true` |
| `declarationProvider` | `true` |
| `referencesProvider` | `true` |
| `documentHighlightProvider` | `true` — returns the ranges of all occurrences of the symbol under the cursor in the current file; the client performs the visual highlighting |
| `renameProvider` | `{ "prepareProvider": true }` |
| `signatureHelpProvider` | trigger characters: `(`, `,` |
| `semanticTokensProvider` | full-file; see legend in response |
| `inlayHintProvider` | `{ "resolveProvider": false }` — shows inferred types of `var`-declared locals |

`textDocumentSync: Incremental` (default) means the client sends only the changed
ranges on each `textDocument/didChange` notification; the server applies them
internally and passes the reconstructed full text to OpenJML.  Setting
`incrementalSync: false` reverts to `Full` (client sends entire file each time).

---

## Configuration

Settings arrive via two channels:

1. **`initializationOptions`** in the `initialize` request — values applied once at
   startup. The JSON object is deserialized directly as an `OpenJMLSettings` object.

2. **`workspace/didChangeConfiguration`** — runtime updates. The notification's
   `settings` object must have an `"openjml"` key; the value is an `OpenJMLSettings`-
   shaped JSON object. Only non-null fields overwrite the current settings, so partial
   updates are safe.

Example `workspace/didChangeConfiguration` payload:

```json
{
  "settings": {
    "openjml": {
      "specsPath": "/path/to/Specs/specs",
      "checkTriggerOn": "save"
    }
  }
}
```

### Global Settings Reference

These fields apply to the server as a whole (default settings used when no per-project
settings match a given file):

| Field | Type | Default | Description |
|---|---|---|---|
| `specsPath` | string | env `OPENJML_SPECS` | Path to JML specification files, passed as `--specs-path` |
| `sourcePath` | string | none | Source root(s) for cross-file references (see note on effective sourcepath below) |
| `classPath` | string | none | Classpath for pre-compiled dependencies, passed as `-classpath`; also used as a sourcepath fallback (see note) |
| `checkTriggerOn` | string | `"edit"` | When to run `--check`: `"edit"`, `"save"`, or `"manual"` |
| `escTriggerOn` | string | `"manual"` | When to run `--esc`: `"manual"` or `"save"` |
| `incrementalSync` | boolean | `true` | When `true`, advertise `Incremental` sync and apply ranged edits internally; when `false`, revert to `Full` sync |
| `javaMode` | string | `"full"` | Java-capability mode: `"full"` enables all Java+JML capabilities; `"jml-only"` suppresses capabilities that duplicate a co-present Java language server (e.g. JDT, Red Hat Java). See note below. |
| `client` | string | `"generic"` | Known-client hint for default tuning. Values: `"generic"` (no assumptions), `"eclipse-jdt"`, `"vscode-java"`, `"intellij"`. When set to a known Java-capable client, `javaMode` defaults to `"jml-only"` unless explicitly overridden. |
| `escThreads` | integer | `5` | Size of the shared ESC thread pool; bounds how many concurrent ESC tasks (and SMT solver subprocesses) may run simultaneously |
| `syntaxColoringScope` | string | `"preserve Java coloring"` | Which tokens the semantic-token response covers. `"preserve Java coloring"` — only JML-specific tokens are emitted (use when a co-present Java LS handles Java tokens). `"overwrite Java coloring"` — all tokens (Java + JML) are emitted by the OpenJML server. |
| `escEngine` | string | `"fresh"` | ESC execution mode. `"fresh"` (default) — spawns a fresh OpenJML process with `--esc`. `"concurrent"` — calls `IAPI.doESC` in-process on the cached AST from the last `--check`; methods within a file are serialized, methods across files run concurrently. |
| `toolOptions` | string array | `[]` | Project-independent OpenJML command-line options prepended verbatim to every tool invocation. See [Tool Options](#tool-options) below. |
| `projects` | array | none | Per-project configuration objects; see [Multi-Project Support](#multi-project-support) below. |

`null` or absent fields leave the current value unchanged.

### Multi-Project Support

The server supports multiple independent projects within a single workspace.  Each
project has a unique identifier as a project id.
Each project is a separate compilation domain with its own source folders, classpath, and specs
path.
Clients that only support a single, unpartitioned workspace are considered to have a single project with an empty string as the project id.

Per-project settings are conveyed in a **`projects`** array inside the top-level
`OpenJMLSettings` object (either in `initializationOptions` or `workspace/didChangeConfiguration`).
Each element is a `ProjectConfig` object:

| Field | Type | Description |
|---|---|---|
| `id` | string | Unique project identifier (alphanumeric, no path separators, no whitespace, non-empty). Used as the lookup key in command arguments. The Eclipse plugin uses the Eclipse project name (`IProject.getName()`). |
| `rootPaths` | list | This project's own source folder paths (not including dependency sources). Used to map a file URI to its owning project. |
| `sourcePath` | string | Path-separator-separated list of source roots, including own source folders **and** transitive dependency source folders. Passed as `-sourcepath` to OpenJML. |
| `classPath` | string | Path-separator-separated list of compiled dependency output directories and any additional user classpath entries. Passed as `-classpath` to OpenJML. |
| `specsPath` | string | OpenJML specs path for this project (`--specs-path`). If absent, the global `specsPath` is used. |
| `outputDir` | string | Directory for RAC-compiled `.class` files (`-d`). Defaults to the IDE project's build output folder. |

A project id that is an empoty string may mean the single default projecdt or that the command applies to all projects.

Example:

```json
{
  "settings": {
    "openjml": {
      "projects": [
        {
          "id": "MyLibrary",
          "rootPaths": ["/workspace/MyLibrary/src"],
          "sourcePath": "/workspace/MyLibrary/src",
          "classPath": "/workspace/deps/commons.jar",
          "specsPath": "/path/to/Specs/specs",
          "outputDir": "/workspace/MyLibrary/bin"
        },
        {
          "id": "MyApp",
          "rootPaths": ["/workspace/MyApp/src"],
          "sourcePath": "/workspace/MyApp/src:/workspace/MyLibrary/src",
          "classPath": "/workspace/MyLibrary/bin:/workspace/deps/commons.jar",
          "specsPath": "/path/to/Specs/specs",
          "outputDir": "/workspace/MyApp/bin"
        }
      ]
    }
  }
}
```

When a project list is configured:
- The server maps each incoming file URI to the project whose `rootPaths` contains
  the file's path.  If no project matches, global settings are used.
- File-watcher events are scoped to the union of all projects' `rootPaths`.
- Commands that name a `projectId` are dispatched using that project's settings.

If a client does not support multiple projects, the configuration information is used to
create a single project with a default id (an empty string).


### Notes on Settings

**Note on `javaMode` and `client`:** OpenJML's LSP server implements capabilities that
overlap with those of full Java language servers (JDT, Red Hat Java, etc.).  By default
all capabilities are active (`javaMode: "full"`).  If another Java LS is active for the
same workspace, clients can avoid duplicate hints, signature help, etc. by setting
`javaMode: "jml-only"` or by naming the client (`client: "eclipse-jdt"`).

Integrators building a plugin that co-exists with a known Java LS should set `client`
in `initializationOptions` — the server then applies the appropriate defaults
automatically.  For example, the OpenJMLUI Eclipse plugin sets `client: "eclipse-jdt"`
so that Java-overlapping features are suppressed by default, with no configuration
required from the end user.

**Note on effective `-sourcepath`:** The server does not pass `sourcePath` directly
to OpenJML. It constructs an effective sourcepath by joining (in order, omitting
empty parts): a temp directory holding any in-memory file content; the workspace
folder roots reported at `initialize` time (only when `sourcePath` is absent, to
avoid duplicate-class issues); the user-supplied `sourcePath` (when present, this
is used alone — workspace folders are excluded); and `classPath` as a final fallback
when `sourcePath` is absent. `--specs-path` and `-classpath` are passed through
unchanged.

When `specsPath` is null or empty, the server falls back to the `OPENJML_SPECS`
environment variable set by the launcher. If that is also unset, OpenJML derives
the specs path from `OPENJML_INSTALL`; for standard installations the variable
should therefore be left unset.

The SMT solvers path is not configurable at runtime. It is fixed at JVM startup
from `OPENJML_SOLVERS` (set by the launcher script), falling back to
`OPENJML_INSTALL`. Client integrators cannot override it via `initializationOptions`
or `workspace/didChangeConfiguration`; set `OPENJML_SOLVERS` before launching the
server if a non-default location is required.

### Tool Options

`toolOptions` is a string array of raw OpenJML command-line arguments that are
prepended verbatim to every tool invocation (`--check`, `--esc`, `--rac`).  It is
project-independent: the same options are applied regardless of which project owns
the file being processed.  Project-dependent settings (source path, class path,
specs path) belong in the named settings fields, not in `toolOptions`.
Project-specific options are a potential future feature.

Clients may use `toolOptions` in two ways:

**Individual flags:**
```json
"toolOptions": ["--keys", "MYKEY", "--require-white-space"]
```

**Properties file:** Write any number of options to a `.properties` file and pass
`--properties <path>` as two consecutive elements:
```json
"toolOptions": ["--properties", "/path/to/openjml.properties"]
```

The properties file is read by OpenJML on each invocation.  If the file changes,
the new values are picked up automatically on the next `--check` or `--esc` run —
no additional configuration notification is required.

When both styles are combined, the flags in `toolOptions` before `--properties` take
effect before the file is processed; flags after it take effect after.  In practice,
clients typically use one style or the other.

`toolOptions` is global-only; there is no per-project equivalent (at present).  Options that vary
by project (e.g. different warning levels per project) should be placed in per-project
properties files, each referenced via a separate `toolOptions` entry, or handled by
the client via project-specific `workspace/didChangeConfiguration` updates.


---

## Document Synchronization

Sync kind is **Incremental** (`TextDocumentSyncKind.Incremental`) by default.
Each `textDocument/didChange` notification carries a list of ranged edits; the
server applies them in the order given (each range refers to the document state
after all preceding changes in the same event) and reconstructs the full text
before passing it to OpenJML.  Set `incrementalSync: false` in
`initializationOptions` to revert to **Full** sync, where every notification
must contain the complete document text in `contentChanges[0].text`.

### `textDocument/didOpen`

- Stores the document content.
- Runs `--check` immediately (no debounce).
- Does **not** run `--esc` or `--rac` automatically on open.

### `textDocument/didChange`

- Stores the updated content.
- **Marks the file dirty** (adds the URI to an internal dirty-URI set). While a file is
  marked dirty, check or ESC invocations (e.g. `openjml.checkJML` or
  `openjml.runEsc` on a directory) use the in-memory content for this file instead of
  reading it from disk. This ensures that unsaved edits are included in context-aware
  cross-file checks even before the file is saved.
- If `checkTriggerOn` is `"edit"`: schedules `--check` with a 500 ms debounce.
  A new change before 500 ms resets the timer.
- If `checkTriggerOn` is `"save"` or `"manual"`: no `--check` is triggered by change.

### `textDocument/didSave`

- **Clears the dirty mark** for the URI (removes it from the dirty-URI set). After save,
  the file's in-memory content matches the disk, so subsequent checks may read
  the file from disk directly and no longer need to mock it from memory.
- Cancels any pending debounced check or ESC.
- Runs `--check` immediately.
- Runs `--esc` if `escTriggerOn` not `"manual"`. Because the LSP protocol does not carry
  a save reason, the server cannot distinguish manual saves from auto-saves and fires
  on every `didSave`. Users who save frequently (e.g. Eclipse auto-save-on-compile,
  or VS Code `files.autoSave: afterDelay`) should use `escTriggerOn: "manual"` to
  avoid unwanted, overly frequent ESC runs.

### `textDocument/didClose`

- **Clears the dirty mark** for the URI — unsaved changes are gone when the editor closes.
- **Removes the in-memory editor buffer** — subsequent operations read from disk.
- **Retains all pending and running checks, proof results, AST cache, and diagnostics.** Closing an editor does not affect project-level analysis state; checks may still be in progress for the file and their results remain valid in the client's Problems panel until a fresh run updates or clears them.

---

## Diagnostics

### Publication

Diagnostics are sent via `textDocument/publishDiagnostics`. Parsing/typechecking diagnostics and
verification diagnostics
are maintained separately per URI and merged before each publication.


The merging policy is:

- When `--esc` runs it subsumes `--check` (ESC performs all the same type and
  annotation checks), so an ESC result replaces the `--check` diagnostics entirely,
  eliminating duplication. An ESC result will replace older ESC results. ESC results
  can also be cleared using the 'Clear markers' command.
- When `--check` runs after a previous ESC (e.g. triggered by an edit), it replaces
  check-level diagnostics but retains ESC verification failures (postcondition
  violations, assertion failures). Those may be stale after the edit, but remain
  useful until a fresh ESC run either confirms or clears them.

ESC verification failures are identified by the `data` field of the LSP `Diagnostic`
object: the server sets `data` to `"esc-verification"` on any diagnostic produced
from a proof obligation failure.

### Diagnostic Format

Each diagnostic has the following fields (LSP `Diagnostic` type):

| Field | Value |
|---|---|
| `range.start/end` | Zero-based line number and zero-based character offset within the line (UTF-16 code units, per the LSP `Position` type) |
| `severity` | `1` (Error) or `2` (Warning) |
| `source` | `"openjml.check"` for `--check` results; `"openjml.esc"` for `--esc` results |
| `message` | Human-readable error or warning text from OpenJML |
| `code` | OpenJML diagnostic code string (e.g., `"jml.message"`) |
| `data` | `"esc-verification"` for diagnostics produced by a proof obligation failure (`--esc`); absent for `--check` diagnostics |

### OpenJML Exit Codes

These exit codes are logged to stderr and influence how the server interprets results:

| Code | Meaning |
|---|---|
| 0 | Success — no parse, type, or verification errors (warnings may still be present) |
| 1 | Syntax or type errors |
| 2 | Bad command-line arguments (typically indicates an invalid setting) |
| 3 or 4 | Catastrophic error — resource exhaustion (e.g. out of memory), significant misconfiguration, or internal bug |
| 5 | The ESC task was cancelled from another thread |
| 6 | ESC verification failures (postcondition or assertion violations) |

---

## Implemented LSP Features

### Hover — `textDocument/hover`

Two cases are handled:

1. **`var` declaration** — if the cursor is on the `var` keyword or the variable name
   of a `var`-declared local, the server returns the inferred type as a plain-text
   string of the form `: TypeName` (e.g. `: int`, `: String`).  Type names are
   shortened by stripping `java.lang.`, `org.jmlspecs.lang.internal.` (JML built-in
   types appear as `\bigint`, <code>\real</code>, etc.), and the containing file's own package
   prefix.  This hover is always active regardless of `javaMode`.

2. **Method declaration / JML spec** — if the cursor is anywhere else inside a method declaration or specs, the
   server returns the JML specification for the method, formatted as a Markdown code block.

Returns null if none of the above conditions are met (e.g. cursor is outside any
method, or the method has no JML annotations).

### Inlay Hints — `textDocument/inlayHint`

Returns `InlayHint` objects of kind `Type` for `var`-declared local variables,
showing the inferred type immediately after the variable name in the form `: TypeName`.
Type names are shortened identically to the hover case above.

**`javaMode` interaction:**
- `"full"` (default): hints are returned for all `var`-declared variables.
- `"jml-only"`: hints for plain Java `var` declarations are suppressed (a co-present
  Java LS such as JDT or Red Hat Java already provides those).  Hints for JML
  `ghost` and `model` `var` declarations are always emitted regardless of `javaMode`,
  because no other language server is aware of them.

**Client notes:**
- Standard LSP clients (VS Code, Neovim, Helix, etc.) display these as inline
  annotations natively.
- **VS Code with vscode-java**: `client: "vscode-java"` defaults `javaMode` to
  `"jml-only"`, so only JML ghost/model var hints are shown (vscode-java handles
  Java vars itself).
- **IntelliJ**: IntelliJ has its own built-in Java type inference display.  Whether
  LSP inlay hints from OpenJML are also shown depends on the LSP plugin in use;
  `client: "intellij"` defaults to `"jml-only"` as a conservative default.
- **Eclipse with OpenJMLUI**: LSP4E does not route `textDocument/inlayHint` responses
  to the JDT Java editor.  The OpenJMLUI plugin works around this via a direct call
  from a code mining provider, but `LineContentCodeMining` does not visually render
  in the JDT Java editor from external providers.  The inferred type is accessible
  instead via the hover described above.  `client: "eclipse-jdt"` defaults to
  `"jml-only"`.

### Code Lens Refresh — `workspace/codeLens/refresh` (server → client)

Sent by the server whenever per-method ESC status changes — for example when ESC
begins (status → CHECKING), completes (status → Verified / Not verified), or is
cancelled. The client should respond by re-requesting `textDocument/codeLens` for
any open documents of interest.

### Log Message — `window/logMessage` (server → client)

Sent by the server for verbose operational messages such as CheckRunner timing lines
and internal warnings. Notifications are type 4 (Log) and are typically routed to an
output panel rather than shown as dialogs. Clients that declare
`supportsActionMessages: true` in `initializationOptions` still receive
`window/logMessage` for purely informational output; advisory and error messages that
warrant a dialog are routed through `$/openjml/actionMessage` instead (see below).

### Show Message Request — `window/showMessageRequest` (server → client)

The server uses `window/showMessageRequest` as a general mechanism to present the
user with a question and wait for a response before proceeding.  Clients should
support this notification for any server feature, not only the ones listed below.

If the client does not support `window/showMessageRequest` (returns `null`), the
server treats the response as if the user chose the default (affirmative) action and
continues.  Clients that ignore the request will therefore see the operation proceed
without user confirmation.

**Current uses:**

- **Rename pre-flight** — sent during `textDocument/rename` when the file has
  outstanding type-check errors.  The server asks whether to proceed with the rename
  despite errors.  If the user selects No, the rename is aborted and an empty
  `WorkspaceEdit` is returned.

### Code Lens — `textDocument/codeLens`

Returns one code lens per detected method in the document. Each lens shows the current
ESC verification status for that method together with an inline action button. The label
format is:

| Status | Label |
|---|---|
| Not run or Unknown | `OpenJML: — ▶ Run ESC` |
| In progress | `OpenJML: ⧗ Checking… ✕ Cancel` |
| Verified | `OpenJML: ✓ Verified ↺ Re-run` |
| Infeasible precondition | `OpenJML: Infeasible ↺ Re-run` |
| Not verified | `OpenJML: ✗ Not verified (N issue(s)) ↺ Re-run` |
| Skipped | `OpenJML: Skipped ▶ Run ESC` |
| Solver timeout | `OpenJML: Timeout ↺ Re-run` |
| Cancelled | `OpenJML: Cancelled ▶ Run ESC` |
| Type/check error | `OpenJML: Check error ↺ Re-run` |
| Check error in deps | `OpenJML: Check error in other files ↺ Re-run` |

Each code lens embeds the command `openjml.runEscForMethod` with arguments
`[uri, "name"]`, where `name` is a string that is unique across all methods in
the project, including methods of anonymous and local classes. A client that supports code lens
execution can invoke (or cancel) ESC on a single method by sending
`workspace/executeCommand` with this command and argument.

The command is always `openjml.runEscForMethod` regardless of the current status; when
the method is already CHECKING the server aborts the in-flight proof (via
`openjml.abortCurrentProof` semantics) instead of starting a new one, so a single
command handles both Run and Cancel without VS Code treating a command change as a new
lens and showing duplicates.  Aborting the current proof does not stop a whole-file or
project ESC run from continuing to the next method.

The server sends a `workspace/codeLens/refresh` notification whenever method ESC status
changes (including when a check moves from CHECKING to a final state). A client should
re-query `textDocument/codeLens` on receiving this notification.

### Completion — `textDocument/completion`

Provides JML keyword and backslash-token completions inside JML annotations
(`//@ ...` and `/*@ ... */`). Trigger characters are `\` and `@`.

Two categories of items are offered:

- **JML keywords** — clause and modifier names (`requires`, `ensures`, `ghost`,
  `invariant`, etc.) — offered when the cursor is inside a JML annotation and the
  partial word does not start with `\`.
- **Backslash tokens** — built-in JML expressions (`\result`, `\old`, `\forall`,
  `\nothing`, etc.) — offered when the partial word starts with `\`.

Completions are only offered when the cursor is inside a JML annotation context;
positions in regular Java code return an empty list.

### Document Symbols — `textDocument/documentSymbol`

Returns a hierarchical symbol tree for the document. When `useIntegratedOutline` is
`true` (the default), all Java and JML symbols are returned together — classes,
methods, fields, and JML ghost/model declarations — giving an integrated view.
When `false`, only JML-specific symbols are returned, intended to complement a
competing Java outline provider.

The handler waits for any in-flight `--check` to complete before returning, so the
outline reflects the current source rather than a stale AST. For `.jml` spec files,
symbols are looked up under the companion `.java` URI.

### Folding Ranges — `textDocument/foldingRange`

Returns folding ranges for JML annotation blocks (consecutive `//@ ...` or `/*@ ... */`
comment sequences that span multiple lines) and Java text blocks (`""" ... """`).
The implementation is a pure character scan — no AST is required — so folding is
available immediately, even before the first `--check` run.  Java structural folds
(class bodies, method bodies, imports) are provided by the client's own Java language
support, not by this server.

If the document has not yet been opened (content not in memory), the server reads it
from disk.

**Eclipse plugin note:** The OpenJMLUI Eclipse plugin does not use this LSP request for
its folding support.  LSP4E's folding reconciling strategy requires projection (fold
annotation) support to be enabled on the editor before the reconciler is installed, and
there is no suitable extension point to guarantee that ordering for either the JDT Java
editor or the Generic Editor.  Instead, the plugin installs `JmlFoldingManager` directly
on each editor's `ProjectionViewer` via a part listener, running the same character-scan
algorithm locally without a server round-trip.  For `.java` files, `JmlFoldingManager`
folds (JML annotation blocks) coexist with JDT's built-in structural folds (methods,
imports, Javadoc) in the same `ProjectionAnnotationModel` without interfering.  For
`.jml` files opened in the Generic Editor, `JmlFoldingManager` provides all folding.
Other clients that do not have this constraint can use `textDocument/foldingRange`
normally.

**Implications for generic clients:** None. Generic clients use `textDocument/foldingRange`
through the standard LSP protocol. The Eclipse plugin's local algorithm is a workaround
for LSP4E's projection-ordering constraint and does not represent a UX difference from
what generic clients receive via the server.

### Semantic Tokens — `textDocument/semanticTokens/full`

Returns full-file semantic token data.  The server's token legend (returned in
`ServerCapabilities.semanticTokensProvider.legend`) is:

| Index | Token type | Used for |
|---|---|---|
| 0 | <code>namespace</code> | Package names |
| 1 | <code>class</code> | Class declarations and references |
| 2 | <code>interface</code> | Interface declarations and references |
| 3 | <code>enum</code> | Enum type declarations and references |
| 4 | <code>struct</code> | Record declarations and references |
| 5 | <code>typeParameter</code> | Generic type parameters (<code>&lt;T&gt;</code>) |
| 6 | <code>type</code> | Primitive types (<code>int</code>, <code>boolean</code>, …) and JML built-in types (<code>\bigint</code>, <code>\real</code>, <code>\locset</code>, …) |
| 7 | <code>parameter</code> | Method and constructor parameters |
| 8 | <code>variable</code> | Local variables |
| 9 | <code>property</code> | Fields (instance and static) |
| 10 | <code>enumMember</code> | Enum constants |
| 11 | <code>method</code> | Method declarations and call sites |
| 12 | <code>function</code> | JML backslash expressions (<code>\result</code>, <code>\old</code>, <code>\forall</code>, <code>\nothing</code>, <code>\fresh</code>, …) |
| 13 | <code>macro</code> | Reserved — declared in legend but not currently emitted (potentially used for some JML backslash tokens) |
| 14 | <code>keyword</code> | JML structural and behavioral keywords (<code>requires</code>, <code>ensures</code>, <code>invariant</code>, <code>ghost</code>, <code>model</code>, <code>also</code>, <code>behavior</code>, …); Java keywords (<code>return</code>, <code>if</code>, <code>for</code>, <code>new</code>, <code>instanceof</code>, <code>null</code>, <code>true</code> …) in full mode |
| 15 | <code>modifier</code> | JML modifier annotations: <code>pure</code>, <code>spec_public</code>, <code>spec_protected</code>, <code>nullable</code>, <code>non_null</code>, <code>helper</code>, <code>strictly_pure</code>, … |
| 16 | <code>decorator</code> | Java and JML annotations (<code>@Override</code>, <code>@NonNull</code>, …) |
| 17 | <code>comment</code> | Reserved — declared in legend but not emitted (JML comment delimiters <code>//@&nbsp;</code> and <code>/*@ */</code> do not appear in the AST) |
| 18 | <code>string</code> | String literals and text blocks |
| 19 | <code>number</code> | Numeric and character literals |
| 20 | <code>operator</code> | Java binary, unary, and assignment operators; JML-specific operators (<code>==&gt;</code>, <code>&lt;==</code>, <code>&lt;==&gt;</code>, <code>&lt;:</code>, …) |

All 21 token types are declared in the legend even if not currently emitted (e.g. `macro`,
`comment`), so that clients have a stable index-to-name mapping and themes can
pre-configure colors for the full vocabulary.

The token modifiers legend is:

| Index | Modifier | Bit mask | Applied to |
|---|---|---|---|
| 0 | <code>declaration</code> | 1 | Declaration sites of symbols |
| 1 | <code>definition</code> | 2 | Reserved |
| 2 | <code>readonly</code> | 4 | <code>final</code> fields and local variables |
| 3 | <code>static</code> | 8 | <code>static</code> fields and methods |
| 4 | <code>deprecated</code> | 16 | Symbols annotated <code>@Deprecated</code> |
| 5 | <code>abstract</code> | 32 | Abstract classes and methods |
| 6 | <code>async</code> | 64 | Reserved |
| 7 | <code>modification</code> | 128 | Reserved |
| 8 | <code>documentation</code> | 256 | Reserved |
| 9 | <code>defaultLibrary</code> | 512 | Standard-library symbols |

All token type names and modifier names are drawn from the LSP standard semantic token
vocabulary, so clients that follow the specification will have default theme colors for
them without requiring JML-specific configuration.

#### Operating modes

**Token scope** is controlled by the `syntaxColoringScope` setting:

- **`"preserve Java coloring"`** (default) — only JML constructs are emitted: JML clause
  keywords, JML modifier keywords, JML backslash expressions, annotations and modifiers on
  Java declarations that carry JML annotation tokens, and all Java constructs appearing
  *inside* JML contexts (e.g., identifiers, operators, and literals inside `requires`
  or `ensures` expressions and inside model method bodies).  Java constructs outside JML
  context are not emitted, leaving them to a co-present Java extension.

- **`"overwrite Java coloring"`** — all Java and JML constructs are highlighted.  Use when
  no other Java semantic token provider is installed.

**LSP capability scope** is controlled separately by the `javaMode` setting (see
[Configuration](#configuration) and the inlay hints section).  `javaMode` determines which
LSP capabilities are advertised (hover, inlay hints, completions, etc.) and is independent
of `syntaxColoringScope`.

#### Coloring strategies

Two strategies are available via the `openjml.syntaxColoringStrategy` setting:

- **`"ast"`** (default) — AST-based coloring when a `--check` result is cached.
  Uses the attributed AST to emit tokens for genuine JML nodes only (no false positives
  for Java identifiers that share a name with a JML keyword).  Falls back to regex
  before the first `--check` completes.

- **`"regex"`** — always uses regex-based line scanning (instant, no AST required, but
  may color Java identifiers that happen to match JML keyword names).

The AST strategy uses `cu.lineMap` (populated during lexing, always present after
a `--check` pass) for O(1) character-offset → line:column conversion.

Non-VS Code clients should use this standard request. See
[`openjml.getSemanticTokens`](#openjmlgetsemantictokens) for the VS Code-specific
alternative.

**Implications for generic clients:** None for the standard semantic token request.
Generic clients receive JML semantic tokens via `textDocument/semanticTokens/full`
through the normal LSP negotiation path. The Eclipse plugin's `JmlColorizer` is a
workaround for JDT's presentation layer intercepting LSP4E's token delivery for `.java`
files, and for LSP4E's semantic token reconciler not re-firing after `publishDiagnostics`.
A generic client with proper semantic token support gets the equivalent result through
the standard path. One potential improvement: the server could send
`workspace/semanticTokens/refresh` after each `--check` completes, signaling
well-behaved clients to re-request tokens without needing a client-side workaround.
This is not yet implemented.

### Go to Definition — `textDocument/definition`

Resolves the declaration of the identifier under the cursor. Works for identifiers
in both regular Java code and JML clauses (`//@ requires`, `//@ ensures`, etc.).
Requires a cached AST from a prior `--check` run for the document.

### Go to Declaration — `textDocument/declaration`

For Java and JML identifiers, declaration and definition are the same location.
Delegates to the same logic as `textDocument/definition`.

### Find References — `textDocument/references`

Finds all references to the symbol under the cursor across every AST currently in
the cache (i.e., all files that have been opened and checked in the current session).
Symbol identity is used for matching, which is correct within a single OpenJML
compilation context.

Note: the search is limited to files whose ASTs are cached. Files that have not been
opened or checked since the server started are not searched.

### Rename — `textDocument/rename` / `textDocument/prepareRename`

`prepareRename` validates that the cursor is on a renameable symbol (a valid Java
identifier character) and signals that rename is supported. It returns
`defaultBehavior: true` so the client infers the rename range from the identifier
word boundary.

`rename` validates the new name, finds all references across cached ASTs, applies
the edits in memory, then validates the result by running `--check` on the modified
content and comparing the before and after diagnostic sets. The comparison is non-trivial: it
must account for cases where the new name shadows — or no longer shadows — another
identifier, silently changing the meaning of existing references without necessarily
producing new errors. If the rename is judged unsafe, or the new name is syntactically
invalid, a descriptive error is returned rather than applying the edits.

### Signature Help — `textDocument/signatureHelp`

Triggered when the cursor is inside a method call argument list. The server scans
backward from the cursor position to find the enclosing `(` and counts commas to
determine the active parameter index. It then looks up the matching method declaration
in the cached AST and returns a `SignatureHelp` response containing one
`SignatureInformation` entry with labelled `ParameterInformation` items.

Trigger characters: `(` and `,`.

If the source file has not yet been type-checked (no AST cached), an empty
`SignatureHelp` is returned gracefully. Only the first matching overload is returned;
overload resolution across multiple signatures is not yet supported.

**Method lookup scope and known limitations**

The server searches for method declarations only within the current file's
`JmlCompilationUnit` and its sibling `.jml` specs file (if any). This covers:

- Regular Java methods declared in the same source file.
- JML model methods (`//@ model public int foo(int x);`) declared in the same
  file or in the companion `.jml` file.
- Accessor methods synthesised for JML model fields
  (`//@ model public int size;`), stored in `typeSpecs.modelFieldMethods`.

**Cross-class calls are not supported.** When the receiver of a call is an
object of another class (e.g. `list.isEmpty(`, `Collections.max(`), the server
cannot resolve the receiver type and returns an empty result. Full cross-class
support would require resolving the receiver expression using OpenJML's
`Resolve`/`Symtab` infrastructure. Eclipse's own JDT parameter hints
(`Ctrl+Shift+Space`) handle cross-class calls for Java code.

**Eclipse behavior in `.java` files.** Eclipse's JDT Java editor suppresses
LSP4E's automatic `(` / `,` trigger inside comment partitions
(`__java_singleline_comment`, `__java_multiline_comment`).  The OpenJML Eclipse
plugin works around this by installing `JmlAutoEditStrategy` on every `.java`
editor when it is first activated.  This strategy intercepts `(` and `,`
keystrokes inside JML regions (lines beginning with `//@` or inside open `/*@`
blocks) and sends a `textDocument/signatureHelp` request directly, displaying the
result in a popup adjacent to the cursor.  This restores automatic popup behavior
for JML annotations such as `//@ assert m(` or `/*@ requires foo(bar,`.

If the popup does not appear automatically (for example, outside a recognized JML
region), the user can invoke the `Jml Parameter Hints`
Eclipse command directly by binding a key combination to it in the Eclipse key
preferences.

Standalone `.jml` files are opened in the Generic Editor where LSP4E's standard
trigger characters fire normally without any workaround.

**Implications for generic clients:** Standard LSP clients honor `(` and `,` as
trigger characters in all editing contexts, including inside comment-like regions,
so the workaround above is not needed.  JDT's comment partition suppression is an
Eclipse-specific limitation; no server-side change is required.

### Workspace Symbols — `workspace/symbol`

Returns declarations from the AST cache whose simple name contains the query string
(case-insensitive substring match). An empty query returns all indexed declarations.
Without a project filter, all indexed projects are searched.

**Project-filtered query encoding:** To restrict results to a single project without
using a custom command, encode the project root into the query string as
`"<projectRoot>\n<identifier>"` (project path, a newline character, then the actual
search term). The server detects the newline and limits the search to that project's
nav section. Generic clients that search all projects should pass a plain query string.
For multi-project clients, prefer `openjml.symbolsForProject`, which takes an explicit
project ID and avoids the encoding convention.

### Configuration — `workspace/didChangeConfiguration`

Handled as described in the [Configuration](#configuration) section.

### `workspace/didChangeWatchedFiles`

The server registers two file watchers during `initialized()` via
`client/registerCapability`, using a single registration ID so they can be
atomically unregistered and re-registered when workspace roots change:

| Glob | Events subscribed |
|------|------------------|
| `**/*.jml` | Created, Changed, Deleted |
| `**/*.java` | Created, Deleted only — Changed events are **not** subscribed |

**`.jml` events** — if the file is currently open in the editor, the event
is ignored (the `textDocument/did*` path handles it).  Otherwise:

- **Created or Changed**: the server reads the updated `.jml` content from
  disk, locates the companion `.java` file from the spec's package/class
  declaration, and schedules a `--check` on the companion.  If the companion
  `.java` is open in the editor with unsaved (dirty) content, that dirty
  content is used for the check rather than the on-disk version.
- **Deleted**: the `.jml` AST cache entry and the companion `.java` AST cache
  entry are both removed, diagnostics for the companion `.java` are cleared,
  and the navigation cache is marked dirty.  No client action is needed: the
  nav cache is refreshed automatically before the next navigation operation
  (Go to Definition, Find References, etc.) or can be expedited with
  `openjml.indexProject`.

**`.java` events** — if the file is currently open in the editor, the event
is ignored.  Otherwise:

- **Created**: the navigation cache is marked dirty.  The new file is **not**
  immediately indexed; it is covered by the next project check, which is
  triggered automatically by the next navigation operation (Go to Definition,
  Find References, etc.) or explicitly via `openjml.indexProject`.
- **Deleted**: the AST cache entry and diagnostics for the file are cleared.
- **Changed**: not subscribed; the client does not send Changed events for
  `.java` files.  The user opens the file to trigger a re-check.

**Root filtering** — events are filtered in the handler regardless of the
glob scope.  When per-project settings are configured (via the `projects`
array), only events for files under the union of all projects' `rootPaths`
are processed; others are silently dropped.  When no per-project settings are
configured, the filter falls back to the global `rootPaths` setting; if that
is also absent, all events are processed.

**Watcher re-registration** — when the effective workspace roots change
(because `workspace/didChangeConfiguration` delivers an updated `projects`
array, or because `workspace/didChangeWorkspaceFolders` fires), the server
unregisters the current watchers and immediately re-registers them with the
same globs.  The brief gap between unregister and re-register is harmless
because all events are root-filtered in the handler anyway.


---

## Custom Commands — `workspace/executeCommand`

Commands are dispatched via `workspace/executeCommand`.

### Argument format

All commands use the same argument layout:

```
args[0]  projectId   -- registered project name, or "" for global/single-project settings
args[1+]             -- command-specific paths / URIs
```

Path configuration (`sourcePath`, `classPath`, `specsPath`, etc.) is sent once at
initialization via `initializationOptions` and updated via
`workspace/didChangeConfiguration`; it is not repeated in command arguments.
Project-independent OpenJML flags are passed via `toolOptions` (see
[Tool Options](#tool-options)) rather than in command arguments.

### `openjml.checkJML`

Run `--check` on one or more files or directories.

```
command:   "openjml.checkJML"
arguments: ["<projectId>", "<path1>", "<path2>", ...]
```

`path1..N` are file-system paths (files or directories). All `.java` files under a
directory are checked recursively.

### `openjml.runEsc`

Run `--esc` on one or more files or directories.

```
command:   "openjml.runEsc"
arguments: ["<projectId>", "<path1>", "<path2>", ...]
```

Cancels any currently running ESC for the same URIs. Marks all methods as CHECKING
immediately. As each method's proof finishes, its code lens is updated in real time
(via `IProofResultListener`) so the user sees individual methods flip from
⧗ Checking… to their final state rather than all updating at once. Accumulated
diagnostics are also published progressively per file. A final pass after the run
reconciles any remaining state.

A path that starts with `file://` is treated as a document URI and checked against
in-memory content rather than the on-disk file.

### `openjml.runEscForMethod`

Run `--esc` on a single named method. Marks only the target method as CHECKING;
other methods' statuses are left unchanged. On completion, only that method's
diagnostics and code lens are updated; other methods are unaffected.

```
command:   "openjml.runEscForMethod"
arguments (standard):   ["<projectId>", "<file-uri>", "<method-fqn>"]
arguments (code-lens):  ["<file-uri>", "<method-fqn>"]
```

**Standard format**: three elements where `args[0]` is the project ID (or `""`),
`args[1]` is the file URI, and `args[2]` is the method FQN.

**Code-lens format**: exactly two elements where the first starts with `file://`.
This is the format emitted directly by `textDocument/codeLens` responses and is
detected automatically.

**Method FQN**: the unique per-project identifier produced by
`Utils.uniqueSymbolName`, e.g. `com.example.MyClass.add(int,int)`.  It includes
the fully qualified class name and the erased parameter types, so overloaded
methods are always distinguished.

**`@line` fallback**: if the client does not have the FQN (e.g. before the first
type-check, so no code lenses have been issued), pass `@<line>` (e.g. `@12`) as
the method argument.  The server resolves the containing method from the AST.
If no AST is available yet the request is silently ignored.  Clients that can
obtain the FQN from `textDocument/codeLens` should prefer it.

### `openjml.runEscSplitByFile`

Run `--esc` on a set of files, launching a separate ESC invocation per file (in
parallel). Each file's result is published as it completes, rather than waiting for
all files to finish.

```
command:   "openjml.runEscSplitByFile"
arguments: ["<projectId>", "<path1>", "<path2>", ...]
```

### `openjml.runEscSplitByMethod`

Run `--esc` on a set of files, launching a separate ESC invocation per method (in
parallel). Per-method code lens updates arrive in real time as each proof completes.

```
command:   "openjml.runEscSplitByMethod"
arguments: ["<projectId>", "<path1>", "<path2>", ...]
```

### `openjml.runRac`

Compile one or more files or directories with JML assertions as runtime checks.
The output directory for compiled class files is taken from the project's `ProjectConfig`.

```
command:   "openjml.runRac"
arguments: ["<projectId>", "<path1>", "<path2>", ...]
```

### `openjml.saveAndRunEsc` (VS Code extension UI command — not a server command)

This is a VS Code extension-level command registered in `package.json` and bound to
menu items and keyboard shortcuts. When the user triggers it, the VS Code extension
saves the document (equivalent to `textDocument/didSave`) and then sends
`workspace/executeCommand` with `openjml.runEsc` to the server. The string
`openjml.saveAndRunEsc` is **never sent to the server**; it is handled entirely
client-side by the VS Code extension. Other clients (Eclipse, generic LSP clients)
should implement the same pattern: save first, then call `openjml.runEsc`.
The command is most relevant to the user when automatically running ESC on 
a Save is turned off (set to "manual") and the user wants a one-shot way 
to save a file and start an ESC operation.

### `openjml.cancelEsc`

Cancel one or more in-progress ESC runs.  **Stops all remaining proofs** in the
targeted run — no further methods are attempted after cancellation.

```
command:   "openjml.cancelEsc"
arguments: ["<target>"]
```

`target` controls what is cancelled:

| Value | Effect |
|-------|--------|
| `null` / absent / `""` | Cancel all ESC runs |
| A plain file URI (e.g. `file:///…/Foo.java`) | Cancel the whole-file ESC for that URI |
| `"<uri>#<methodName>"` | Cancel the per-method ESC for the named method |

Cancelled methods have their code lens status set to `Cancelled`; other methods are
unaffected.

Use `openjml.abortCurrentProof` instead when the intent is to skip only the
currently-running proof and continue proving the remaining methods.

### `openjml.abortCurrentProof`

Abort only the currently-running method proof, then allow the ESC loop to continue
with the next method.  The in-progress SMT solver invocation is killed immediately
and the method is reported `Cancelled`, but no further proofs are prevented.

```
command:   "openjml.abortCurrentProof"
arguments: ["<target>"]
```

`target` uses the same format as `openjml.cancelEsc`.  If the target identifies a
whole-file or project run, only the single method currently being proved is aborted;
the remaining methods in the queue are unaffected.

| Situation | `openjml.cancelEsc` | `openjml.abortCurrentProof` |
|-----------|--------------------|-----------------------------|
| Current method | CANCELLED | CANCELLED |
| Remaining methods | not attempted | continue normally |
| Overall run exit code | CANCELLED (5) | determined by remaining proofs |

The code lens "✕ Cancel" action uses `openjml.abortCurrentProof` semantics so
that cancelling one method in a whole-file run does not discard all pending proofs.

### `openjml.getRunningEscTasks`

Returns the list of currently running ESC task keys as a JSON array of strings.
Each entry is either a plain file URI (whole-file ESC) or a `"<uri>#<method-fqn>"`
string (per-method ESC), where `<method-fqn>` is the same FQN used in
`openjml.runEscForMethod` arguments. Returns an empty array when no ESC is in progress.

```
command:   "openjml.getRunningEscTasks"
arguments: []
```

Clients can use this to populate a cancellation UI (e.g. a checklist dialog or
Quick Pick) before calling `openjml.cancelEsc` or `openjml.abortCurrentProof`.

### `openjml.indexProject`

Trigger a `--check` pass on all source directories of the specified project.
For every file the check touches, diagnostics and the nav-tier AST cache entry
are replaced; files not reached retain their previous values.  The nav-tier AST
cache takes highest precedence for navigation operations (Go to Definition,
Find References, `workspace/symbol`).  Use `openjml.clearAndReindex` for a full
reset that clears all tiers first.

```
command:   "openjml.indexProject"
arguments: ["<projectId>"]
```

When `projectId` matches a project registered via the `projects` settings array, only
that project's `rootPaths` are indexed.  An absent or empty `projectId` indexes all
configured projects.

**Eclipse plugin:** exposed as the "Index Project" item in the OpenJML main menu,
editor popup, and Package Explorer context menu.  Intended for use before "Find All
Declarations" to ensure files that have not yet been opened are covered by the index.

### `openjml.symbolsForProject`

Return `workspace/symbol`-style declarations filtered to a single project.  This is the
preferred API for multi-project clients: pass the project ID directly instead of encoding
a project root into the `workspace/symbol` query string.

```
command:   "openjml.symbolsForProject"
arguments: ["<query>", "<projectId>"]
```

| Argument | Description |
|---|---|
| `query` | Symbol name substring to search (case-insensitive; empty = return all). |
| `projectId` | Project identifier from the `projects` settings array.  When absent or empty, symbols from all projects are returned.  An unknown ID is reported as an error. |

Returns a JSON array of `SymbolInformation` objects (same format as `workspace/symbol`).
Matching behavior is identical to `workspace/symbol`: case-insensitive substring match
on the simple symbol name.

**Eclipse plugin:** the "Find All Declarations" handler uses this command, passing
`IProject.getName()` as the project ID.  `workspace/symbol` with the encoded-query
form remains supported for generic LSP clients that cannot issue custom commands.

### `openjml.focusFile`

Notify the server that the user has switched focus to an already-open file. Triggers
a `--check` recheck so that stale diagnostics from fixed dependencies are cleared.

```
command:   "openjml.focusFile"
arguments: ["<file-uri>"]
```

**Implications for generic clients:** This is a real UX gap for clients that do not
implement it. Without `openjml.focusFile`, a client that edits file A, switches to
file B, then returns to file A will see stale diagnostics on A until the next edit or
save triggers a new `--check`. The Eclipse plugin sends the focus command on every
editor tab switch (200 ms debounced) to keep diagnostics current proactively.

Client authors should implement the equivalent:
- **VS Code:** already implemented via `onDidChangeActiveTextEditor` with a 200 ms
  debounce (see the VS Code extension source).
- **IntelliJ / other IDEs:** hook the "file editor gained focus" event and send
  `openjml.focusFile` with the same debounce.
- **Bare LSP clients** that do not implement this get degraded-but-functional behavior:
  diagnostics are correct after the next edit or save, just not updated proactively
  on focus change.

### `openjml.getSemanticTokens`

This command is a VS Code-specific workaround. It returns JML semantic token data directly as the command
result rather than via `textDocument/semanticTokens/full`. The VS Code extension uses
this because it registers its own `DocumentSemanticTokensProvider` directly (to avoid
being overwritten by the Red Hat Java extension), bypassing the standard LSP
negotiation.

**Non-VS Code clients should use `textDocument/semanticTokens/full` instead.** The
server advertises `semanticTokensProvider` in `ServerCapabilities` and handles the
standard request; both paths call the same underlying token computation. The Eclipse
plugin uses the standard protocol via LSP4E's `SemanticTokensClient`.

```
command:   "openjml.getSemanticTokens"
arguments: ["<file-uri>"]
```

### `openjml.clearAndReindex`

Clear all server-side caches (AST cache, diagnostics, ESC status) and reindex the
workspace from disk.  Takes no arguments.

The server cancels all pending work, clears its internal caches, and publishes empty
diagnostics for every previously-marked URI.  It then re-indexes all configured
projects from disk.  **The server does not re-check open editors from its internal
content cache** — that cache is cleared by the reset.  Clients must restore open-editor
content using one of these protocols:

- **Save-then-clear**: save all dirty open editors before issuing `clearAndReindex`.
  The workspace index picks up the saved content from disk.
- **Clear-then-resend**: issue `clearAndReindex`, then send a full-text
  `textDocument/didChange` for every dirty open editor in JML-natured projects
  (both `.java` and `.jml` files).  The `didChange` must carry the complete current
  buffer text, not an incremental delta.

If project configuration has also changed, send `workspace/didChangeConfiguration`
**before** `clearAndReindex`; the server rebuilds its project registry at the start
of the reset, so configuration sent after the command arrives too late to influence
the disk scan.

### `openjml.clearMarkers`

Clears all OpenJML diagnostics without scheduling any new checks. The server clears
its internal diagnostic state and sends `textDocument/publishDiagnostics` with an
empty list for every URI that currently has diagnostics; the client's normal handling
of those notifications removes the visible annotations. A client that already knows
its display is stale (e.g. after a workspace rebuild) may also clear its own
annotations independently, before or without waiting for the server's response —
both approaches are valid and complementary. Takes no arguments.

### `openjml.clearMarkersSelected` (VS Code extension UI command — not a server command)

Clears OpenJML diagnostics for a specific set of files or folders selected in the
Explorer, rather than workspace-wide.  This is a VS Code extension–level command;
the string `openjml.clearMarkersSelected` is **never sent to the server**.

When the user triggers it from the Explorer context menu, the extension resolves the
selected URIs (including multi-select) into a flat list of file-system paths via
`resolveTargetPaths`, then sends a single `workspace/executeCommand` with
`openjml.clearMarkers` and those paths as arguments.  Other clients should implement
the same pattern: call `openjml.clearMarkers` with the desired paths.

---

## Unimplemented LSP Features

The following standard LSP features are not implemented. Entries marked *not relevant*
are outside the server's intended scope and will not be added; all others may be added
in the future. Sorted alphabetically by method name.

| Feature | Notes |
|---|---|
| `textDocument/prepareCallHierarchy`, `callHierarchy/incomingCalls`, `callHierarchy/outgoingCalls` | Not relevant — complex to implement; provides no JML-specific value beyond what Java IDEs already provide natively |
| `codeLens/resolve` | Not relevant — lazy-loads additional data for a code lens returned with incomplete information; OpenJML lenses are fully populated (label, command, arguments) on first request, so resolution is never needed. The server advertises `resolveProvider: false` in `CodeLensOptions` |
| `telemetry/event` | Not relevant — server-to-client telemetry notification used to forward analytics events to the client for reporting; OpenJML does not collect or emit telemetry |
| `textDocument/codeAction` | Quick fixes for JML errors (e.g. inserting a missing `requires`); code lens is currently used for ESC invocation instead |
| `textDocument/codeAction/resolve` | Not relevant — lazy-resolves additional detail for a previously returned code action; not applicable while `textDocument/codeAction` itself is unimplemented |
| `textDocument/colorPresentation`, `textDocument/documentColor` | Not relevant — color-picker protocol for CSS/HTML; Java and JML source files contain no color values |
| `textDocument/completion/resolve` | Not relevant — lazy-resolves additional detail (e.g. documentation) for a completion item that was intentionally left sparse; OpenJML completion items are fully populated on first request, so resolution is never needed |
| `textDocument/diagnostic`, `workspace/diagnostic`, `workspace/diagnostic/refresh` | Not relevant — pull-model diagnostics (LSP 3.17); OpenJML publishes diagnostics proactively via `textDocument/publishDiagnostics` (push model), making the pull model redundant |
| `textDocument/documentLink`, `textDocument/documentLink/resolve` | Not relevant — highlights navigable URLs and file links inside source; not applicable to Java/JML compilation workflows |
| `textDocument/formatting` | Code formatting; must be JML-comment-aware to avoid corrupting `//@ ` lines |
| `textDocument/implementation` | Go to implementation |
| `workspace/inlayHint/refresh` | Server-initiated hint refresh; would complement `workspace/semanticTokens/refresh` |
| `textDocument/inlayHint/resolve` | Not relevant — lazy-loads additional hint detail for complex hints; OpenJML hints are simple type strings and contain complete data on first request |
| `textDocument/linkedEditingRange` | Not relevant — simultaneous editing of matched tag pairs (e.g. HTML open/close tags); not applicable to Java/JML |
| `textDocument/moniker` | Not relevant — cross-repository symbol package identifiers for code-intelligence platforms (LSIF/SCIP); not applicable to IDE tooling |
| `textDocument/onTypeFormatting` | Not relevant — live formatting as the user types; Java formatting is the responsibility of the client's Java language server |
| `window/progress`, `$/progress`, `window/workDoneProgress/create`, `window/workDoneProgress/cancel` | Progress reporting for long-running check and ESC operations. `window/workDoneProgress/create` / `cancel` are the server-initiated variants for client-managed progress tokens; neither is currently sent |
| `window/showDocument` | Not relevant — server-to-client request to open an arbitrary URI in the client editor or browser; OpenJML has no need to programmatically open documents on behalf of the user |
| `textDocument/rangeFormatting` | Range-based formatting |
| `textDocument/selectionRange` | Expand selection to the enclosing syntactic range; could be implemented using the cached AST |
| `textDocument/semanticTokens/full/delta` | Incremental token diff; an optimization that avoids retransmitting unchanged tokens on each edit |
| `textDocument/semanticTokens/range` | Viewport-range token request; useful for very large files where full tokenization would be expensive |
| `workspace/semanticTokens/refresh` | Server-initiated token refresh; would signal clients to re-request tokens after `--check` completes, eliminating the need for client-side workarounds |
| `textDocument/typeDefinition` | Go to type definition |
| `textDocument/prepareTypeHierarchy`, `typeHierarchy/supertypes`, `typeHierarchy/subtypes` | Not relevant — complex to implement; Java IDEs provide structural type hierarchy natively; JML spec-inheritance tracing does not yet warrant a dedicated implementation |
| `textDocument/willSave`, `textDocument/willSaveWaitUntil` | Not relevant — pre-save hooks for server-side processing before disk write; `textDocument/didSave` covers all post-save check needs |
| `workspace/applyEdit` | Not relevant — server-initiated bulk edit applied by the client; OpenJML returns rename edits directly in the `textDocument/rename` response rather than pushing them via `workspace/applyEdit` |
| `workspace/configuration` | Not relevant — client-initiated pull of per-section configuration; OpenJML uses a push model (`workspace/didChangeConfiguration`) so the server never requests configuration from the client |
| `workspace/didChangeWorkspaceFolders` | Not implemented — the server reads workspace folders once from `workspaceFolders` in `initialize` and does not update them dynamically; clients that add or remove workspace folders must reconnect or send `workspace/didChangeConfiguration` with updated `rootPaths` |
| `workspace/didCreateFiles`, `workspace/didDeleteFiles`, `workspace/didRenameFiles` | Not relevant — file-system operation notifications; file changes are handled via `workspace/didChangeWatchedFiles` |
| `workspace/willCreateFiles`, `workspace/willDeleteFiles`, `workspace/willRenameFiles` | Not relevant — pre-operation file-system hooks; no server-side processing is needed before file creation, deletion, or OS-level rename |
| `workspaceSymbol/resolve` | Not relevant — lazy-resolves additional detail (e.g. `location`) for a workspace symbol that was returned with partial data; OpenJML workspace symbol results are fully populated on first request |

---

## Threading and Concurrency

The server uses a single-threaded LSP dispatch thread (managed by LSP4J) and a
cached thread pool for check and ESC tasks. Debouncing uses a single-threaded
scheduled executor.

Within a single file, starting a new ESC cancels the previous one via
`Future.cancel(true)`. A generation counter ensures that results from a superseded
ESC run are silently discarded if they arrive after a newer run has already started.

Separate ESC runs for different files, methods, or projects may overlap concurrently —
all tasks share a single fixed thread pool (default size: 5, configurable via the
`escThreads` setting).

The `--check` runner never updates method ESC status or requests a code lens refresh,
so in-progress edits do not disturb the ESC status badges visible to the user.

---

## Error Handling and Logging

All diagnostic output goes to the log file described above
(`~/.openjml/logs/openjml-lsp-<pid>.log` in production, `/tmp/openjml-lsp-debug.log` in dev).
The JSON-RPC stream on stdout is protected by two complementary redirections:

1. The launcher script redirects the process's stderr to the log file
   (`exec 2>>"$LOG"`) before starting Java.
2. `ServerLauncher.main()` captures the real stdout as the LSP wire stream, then calls
   `System.setOut(System.err)` so that any subsequent `System.out.println` calls —
   from OpenJML, from javac, or from the server itself — are routed to stderr and
   therefore to the log file, never to the JSON-RPC channel.

OpenJML's compiler text output is additionally captured via the `PrintWriter` argument
to `IAPI.make()`, which wraps `System.err` in the server, so compiler messages also
appear in the log file alongside the server's own debug output.

If OpenJML exits with code 3 or 4 (catastrophic error), the server marks all methods
as `Check error` and publishes whatever diagnostics were collected before the failure.

If OpenJML exits with code 2 (bad command-line arguments), a message is written to
the debug log; this always indicates a bug in the server.

---

## Custom Notifications: `$/openjml/actionMessage`

The server uses a custom notification to deliver advisory and error messages to clients
that can act on them (e.g. open a preferences page).  Generic clients that do not
support this extension continue to receive plain `window/logMessage` instead.

### Capability advertisement

Declare support in `initializationOptions`:

```json
{ "supportsActionMessages": true }
```

When the server sees this flag it routes advisory and error messages through
`$/openjml/actionMessage` exclusively — it does **not** also send a duplicate
`window/logMessage`.  Clients that omit the flag receive only `window/logMessage`
and see the text but no action dialog.

### Notification shape

```json
{
  "jsonrpc": "2.0",
  "method": "$/openjml/actionMessage",
  "params": {
    "type": 2,
    "message": "In --(no-)warn, 'asdasd' is not a valid warning key.",
    "actions": [
      { "kind": "openPreferences", "target": "toolOptions", "title": "Open Preferences" },
      { "kind": "dismiss",                                   "title": "OK" }
    ]
  }
}
```

| Field | Type | Description |
|---|---|---|
| `type` | integer | LSP `MessageType`: 1=Error, 2=Warning, 3=Info, 4=Log |
| `message` | string | Human-readable text to log and (if actions present) display in the dialog |
| `actions` | array? | Optional; if absent or empty, log only — no dialog |

#### Action kinds

| `kind` | `target` values | Meaning |
|---|---|---|
| `openPreferences` | `"settings"` | Open the top-level OpenJML settings/preferences page |
| `openPreferences` | `"toolOptions"` | Open the OpenJML tool-options page (--warn, --esc flags, etc.) |
| `dismiss` | — | No-op; use as the cancel/close button |

Clients should silently ignore any `kind` value they do not recognise, treating it
the same as `dismiss`.

### Expected client behavior

1. **Log** `message` to the client's output/console surface using `type` for severity-
   appropriate coloring (e.g. Error/Warning in red, Info normal).
2. **Show a dialog** if `actions` is non-empty, presenting one button per action item.
3. **Execute** the action when the user clicks a button:
   - `openPreferences` / `target: "settings"` → open top-level OpenJML settings
   - `openPreferences` / `target: "toolOptions"` → open tool-options settings
   - `dismiss` → close dialog, no further action

### Message categories

| Scenario | `type` | `actions` |
|---|---|---|
| CheckRunner progress/timing | Log (4) | — (still sent as `window/logMessage`) |
| Check/RAC summary | Info (3) | none |
| ESC could not run (type errors in dependency) | Info (3) | none |
| Unexpected runtime exception (Check/RAC failed) | Error (1) | `[dismiss]` |
| Unknown project ID / .jml companion mismatch | Error (1) | `[dismiss]` |
| Bad `--warn`/`--no-warn` key | Warning (2) | `[openPreferences/toolOptions, dismiss]` |
| openjml rejected CLI option (exit code 2) | Error (1) | `[openPreferences/settings, dismiss]` |

> **Note:** `CheckRunner` log output (verbose invocation lines, timing) is always sent
> as `window/logMessage` type 4 (Log) regardless of the `supportsActionMessages` flag,
> because it never warrants a dialog.

---

## VS Code Extension Notes

The bundled VS Code extension (`OpenJMLlsp/vscode-extension/`) has several design decisions that differ from a generic LSP client. This section documents them for extension maintainers and third-party client authors.

### Client identifier and `javaMode` default

The extension passes `client: "vscode-java"` in `initializationOptions`. This causes the server to default `javaMode` to `"jml-only"`, which suppresses features that overlap with the Red Hat Java extension (`documentSymbol` Java members, Java hover, Java inlay hints). The `openjml.javaMode` and `openjml.client` settings in `package.json` let users override these if they want full coverage (e.g., when Red Hat Java is not installed).

### Semantic tokens — additive merge with Red Hat Java

The vscode-languageclient library's built-in semantic tokens feature competes with the Red Hat Java extension's semantic tokens provider via a provider race that VS Code resolves non-deterministically. To avoid this:

1. The LSP-channel semantic tokens response is suppressed in middleware:
   ```js
   provideDocumentSemanticTokens: (_document, _token, _next) =>
       new vscode.SemanticTokens(new Uint32Array([]))
   ```
2. A separate `DocumentSemanticTokensProvider` is registered directly with VS Code via `vscode.languages.registerDocumentSemanticTokensProvider`. It fetches tokens by calling the `openjml.getSemanticTokens` custom command and returns them as a `vscode.SemanticTokens` object.

This approach merges the JML tokens additively on top of whatever Red Hat produces.
The legend registered with VS Code **must exactly match the server's legend** — all 21
token type names in index order, then the 10 modifier names in index order
(see the [Semantic Tokens](#semantic-tokens----textdocumentsemantictokensfull) section
above for the full table).  A mismatch causes incorrect colors for any token type whose
index differs between client and server legends.

In `jml-only` mode (the default when `client: "vscode-java"` is sent), the server
emits tokens only for JML constructs, so Red Hat's Java coloring is not disturbed for
ordinary Java code.

### `prepareRename` middleware

The extension overrides `prepareRename` in middleware to return the word range at the cursor immediately for Java identifiers, bypassing the server round-trip. This is required because the Red Hat extension's rename provider would otherwise race with ours and win. For non-identifier positions the call falls through to the server.

### `java.format.enabled` caveat

The Red Hat Java formatter rewrites `//@ ` to `// @` (inserts a space after `//`), silently disabling all JML annotations. The extension warns once per workspace on activation and offers to disable `java.format.enabled`. Users who need formatting can still invoke it manually via Shift+Alt+F; they should configure a formatter profile that excludes line-comment reformatting.

### Outline duplication caveat

With `useIntegratedOutline: true` (the default), the Outline panel receives symbol
contributions from both the Red Hat Java extension (Java symbols only) and the OpenJML
extension (Java + JML symbols together), producing duplicate Java entries.  Users can
either fold/close the Java contribution in the Outline panel, or set
`openjml.useIntegratedOutline` to `false` so OpenJML emits only JML-specific symbols
and defers Java symbols entirely to the Red Hat extension.

### `dirtyFileAction` — unsaved-file handling before ESC

`dirtyFileAction` is a VS Code extension–only setting (not forwarded to the server)
that controls what the extension does when **Run ESC** is invoked on a file with
unsaved edits:

| Value | Behavior |
|---|---|
| `"ask"` (default) | Prompt the user each time: save and run, or run on the saved disk copy |
| `"save"` | Always save silently first, then run ESC on the saved content |
| `"run"` | Always run ESC on the saved disk copy without saving the unsaved edits |

This setting interacts with `openjml.saveAndRunEsc`: that command always saves first
regardless of `dirtyFileAction`, making it the preferred shortcut when the user wants
a one-shot save-then-verify flow with `dirtyFileAction: "run"` in effect.

### Keybindings

Default keybindings contributed by the extension:

| Command | Mac | Windows / Linux |
|---|---|---|
| `openjml.runEsc` | `Cmd+E` | `Ctrl+E` |
| `openjml.runEscForMethod` | `Cmd+Alt+E` | `Ctrl+Alt+E` |
| `openjml.saveAndRunEsc` | `Ctrl+Cmd+E` | `Ctrl+Shift+E` |

All bindings are scoped to `(editorLangId == java || editorLangId == jml) && editorFocus`
so they fire only when a Java or JML file is active.  Users can rebind them in the
standard VS Code keyboard shortcuts editor.

### Type-checking triggers

`--check` (JML type-check) trigger depends on `checkTriggerOn`:

| `checkTriggerOn` | `didOpen` | `didChange` | `didSave` | focus (`openjml.focusFile`) |
|---|---|---|---|---|
| `"edit"` (default) | yes | yes, debounced 500 ms | yes | yes, debounced 200 ms |
| `"save"` | yes | no | yes | yes |
| `"manual"` | no | no | no | no |

In `"manual"` mode, `--check` only runs when explicitly requested via the `openjml.checkJml` command. This mode is intended for codebases where automatic checking is slow or causes problems. ESC (`--esc`) is separate and has its own trigger setting (`openjml.escTriggerOn`).

### Status bar — ESC progress indicator

While any ESC task is running, the extension shows a status bar item at the bottom of the window:

```
OpenJML N ESC task(s) running …
```

where `N` is the count of currently running tasks (queried every 800 ms via
`openjml.getRunningEscTasks`). Clicking the item invokes `openjml.cancelEsc`.  The item
is hidden when no tasks are running and on any query error.

### Code-lens-based method FQN for `runEscForMethod`

When the user invokes **Run ESC for Method** from the keyboard, the extension calls
`vscode.executeCodeLensProvider` to retrieve the current document's code lenses and finds
the lens whose range starts at or above the cursor line with command
`openjml.runEscForMethod`.  The method FQN is taken directly from that lens's
arguments (the `Utils.uniqueSymbolName` form, e.g. `com.example.MyClass.add(int,int)`),
which the server's AST scanner computed and embedded when building the code lenses.
This approach correctly resolves methods in secondary classes and nested classes without
any client-side regex.  Generic clients can use the same mechanism or read the FQN from
the code lens command arguments directly.

### Explorer context menu

The extension contributes menu items to the `explorer/context` menu for file and folder
nodes, including `runEscSplitByFile`, `runEscSplitByMethod`, and `indexProject`.
Explorer multi-select (the `explorerSelection` argument VS Code passes as the second
argument to Explorer context commands) is handled by `resolveTargetPaths`, which unions
all selected URIs into a single path list for the server command.


---

## Known Limitations

- **Single-file scope**: Each check or ESC invocation processes one file at a time.
  Cross-file type information (e.g., specs for imported classes) is available if
  `sourcePath` is configured, but the server does not automatically re-check
  dependent files when a spec file changes.

- **ESC-on-save**: When `escTriggerOn` is `"save"`, the server triggers ESC from
  `textDocument/didSave`. The LSP protocol does not carry a save reason, so the
  server fires on every save (manual or auto). Users who save frequently should
  use `escTriggerOn: "manual"` instead.

- **Method detection**: Code lens placement uses an AST-based scanner after the first
  `--check` completes.  The scanner covers methods in all class types — primary and
  secondary top-level classes, member nested classes, local classes, and anonymous
  classes — using `Utils.uniqueSymbolName` as the canonical FQN key, which matches
  the key used by `--method` filtering.  Lambda bodies are not scanned.  Before the
  first `--check` completes no code lenses are shown; trigger a check (manually or by
  opening the file) to populate them.

- **Workspace folders**: The server accepts workspace folder roots (from
  `workspaceFolders` in `initialize` and the `workspaceFolderPaths` setting) and
  uses them as a fallback `-sourcepath` when no explicit source path is configured.
  However, per-folder configuration, cross-folder dependency tracking, and
  `workspace/didChangeWorkspaceFolders` are not implemented.

