%{
  title: "Cure v0.27.0 :: The CLI, One Command at a Time",
  author: "Aleksei Matiushkin",
  description: "A tour of every subcommand exposed by the `cure` escript in v0.27.0: what each one does, the exact argument shape it accepts, and a real session showing what it prints when you actually run it.",
  tags: ~w(cli tooling tour reference)
}
---
Every release post so far has described what landed in the language
and the runtime. This one is different. It sits down with the
single user-facing surface almost everyone meets first --- the
`cure` escript --- and walks every subcommand `./cure help` knows
about, in the order the help text lists them. Each section below
explains the command, pins down the exact invocation shape, and
shows a real session captured on a live v0.27.0 checkout.

Every transcript below was produced against:

```bash
$ ./cure version
Cure 0.27.0
```

The scratch projects used for the examples are scaffolded inline
so you can reproduce every step. Nothing has been hand-edited.

## The shape of the CLI

The top-level contract is the same for every subcommand:

```text
cure <command> [options] [arguments]
```

Running `cure` with no arguments, or with `help`, prints the
canonical usage block that the rest of this post walks through:

```bash
$ ./cure help
Cure 0.27.0 -- Dependently-typed language for the BEAM

Usage: cure <command> [options] [arguments]

Commands:
  compile <file|dir>   Compile .cure files to BEAM bytecode
  run <file>           Compile and execute a .cure file
  check <file>         Type-check without compiling
  ...
```

Unknown commands produce a single-line error and exit with a
non-zero status:

```bash
$ ./cure bogus
error: Unknown command: bogus. Run 'cure help' for usage.
```

With the preamble out of the way, here is every command in order.

## `cure compile` --- source to BEAM

```text
cure compile <file|dir> [-o DIR] [--no-type-check] [--optimize]
```

`compile` is the bread and butter of the CLI. Pointed at a file, it
type-checks, lowers through the compiler pipeline, and emits one
`.beam` per module into the output directory (default
`_build/cure/ebin`). Pointed at a directory, it walks every
`**/*.cure` under it.

```bash
$ ./cure compile examples/hello.cure -o /tmp/hello_build
  -> Cure.Hello

$ ls /tmp/hello_build
Cure.Hello.beam
```

`--no-type-check` still parses and lowers, but skips the type
checker. Handy when iterating on a broken branch; not something you
want on CI. An FSM declaration produces a single `.beam` under the
`Cure.FSM.*` namespace:

```bash
$ ./cure compile examples/traffic_light.cure -o /tmp/tl_build
  -> Cure.FSM.TrafficLight
$ ls /tmp/tl_build
Cure.FSM.TrafficLight.beam
```

## `cure run` --- compile and execute

```text
cure run <file>
```

`run` is `compile` followed by invoking the module's `main/0` (if
any) in a fresh BEAM node. The return value is printed verbatim via
`inspect/1`:

```bash
$ ./cure run examples/hello.cure
42
```

The source it runs is the three-liner you would expect:

```cure
mod Hello
  fn greet(name: String) -> String = "Hello, " <> name <> "!"
  fn main() -> Int = 42
```

## `cure check` --- type-check only

```text
cure check <file>
```

Pure type-check: no code is emitted. Fast feedback loop for
"is this tree still well-typed?":

```bash
$ ./cure check examples/hello.cure
/opt/Proyectos/Cure/cure/examples/hello.cure: OK

$ ./cure check examples/traffic_light.cure
/opt/Proyectos/Cure/cure/examples/traffic_light.cure: OK
```

Unlike `compile` and `run`, `check` always type-checks; the
`--no-type-check` flag has no effect here.

## `cure lsp` --- Language Server Protocol

```text
cure lsp
```

Boots the LSP server on stdio. There is no interactive output ---
editors talk to it via Content-Length-framed JSON-RPC. Full
capabilities (`textDocumentSync`, `hoverProvider`, semantic
tokens, formatting, rename, code actions, completion) are declared
up front. Launching it by hand just sits waiting for a peer:

```bash
$ ./cure lsp
# (silent; the server is reading stdin for LSP frames)
```

This is the entry point `vscode-cure`, `vicure`, and the Zed
extension all speak to.

## `cure stdlib` --- compile the standard library

```text
cure stdlib
```

Compiles every module under `lib/std/` into the shared ebin
directory. Run it once from the Cure checkout before any downstream
project depends on `Std.*`:

```bash
$ ./cure stdlib
Compiling Cure standard library (34 modules)
  access -> Cure.Std.Access
  actor -> Cure.Std.Actor
  app -> Cure.Std.App
  core -> Cure.Std.Core
  crdt -> Cure.Std.CRDT
  ...
  vector -> Cure.Std.Vector
Output: _build/cure/ebin
```

## `cure doc` --- HTML documentation

```text
cure doc [path|dir]
```

Extracts module-level and function-level doc comments from `.cure`
sources and emits a styled static site under `_build/cure/doc/`.

```bash
$ cd /tmp/cure_blog_demo/demo_lib
$ ../../cure/cure doc lib/
Generating documentation for 1 files
Documentation written to _build/cure/doc/ (1 modules)

$ ls _build/cure/doc
demo_lib.html  index.html  style.css
```

Pointed at a single file it does the obvious thing:

```bash
$ ./cure doc examples/hello.cure
Generating documentation for 1 files
Documentation written to _build/cure/doc/ (1 modules)
```

## `cure fmt` --- formatter with four gears

```text
cure fmt [path|dir] [--safe | --aggressive | --check]
```

The default (v0.21.0+) is the algebra pretty-printer with
round-trip verification --- any rewrite that would change the AST is
silently reverted. `--safe` is the legacy byte-level formatter;
`--aggressive` rewrites from the AST and warns loudly first;
`--check` is a dry-run used by CI.

```bash
$ ./cure fmt --check lib/
All files are formatted

$ ./cure fmt --aggressive /tmp/messy.cure
warning: `cure fmt --aggressive` rewrites from the AST: plain `#` comments
and non-canonical whitespace will be stripped. Make sure the target files
are committed before continuing.
```

When `--check` finds something out of shape, it lists the files and
exits non-zero; when nothing is out of shape, it prints
`All files are formatted` and exits clean (as above).

## `cure repl` --- interactive session

```text
cure repl
```

A raw-mode line editor with Makeup-highlighted prompts, persistent
history at `~/.cure_history`, incremental search, Tab completion,
and a Marcli-rendered `:help`. The prompt counts submissions; the
echo arrow `=>` carries the return value of `main/0`.

```text
$ ./cure repl
Cure REPL v0.27.0  (type :help for commands, :quit to exit)
cure(1)> 1 + 2
=> 3
cure(2)> :t 3 + 4
3 + 4 : Int
cure(2)> :quit
Bye.
```

Meta-commands (`:t`, `:effects`, `:load`, `:time`, `:bench`,
`:doc`, `:history`, `:theme`, `:mode`, ...) live outside the
expression grammar and are documented end-to-end under
[`docs/REPL.md`](https://github.com/cure-lang/cure-lang/blob/main/docs/REPL.md).

## `cure watch` --- recompile on every save

```text
cure watch [path] [--action compile|check|test]
          [--poll-ms N] [--debounce N]
```

Polls the given path (default `.`) for `.cure` changes and re-runs
the selected action on every save. First pass is immediate so you
always see at least one compile cycle on startup:

```bash
$ ./cure watch lib/ --action check
watching lib/ (action: check)
press Ctrl-C to stop
[06:54:18] checking lib/
  lib/main.cure: OK
  lib/messy.cure: OK
```

The loop coalesces rapid changes via the debounce window so a
flurry of saves only triggers one run.

## `cure new` and `cure init` --- project scaffolding

```text
cure new <name> [--lib | --app | --fsm]
cure init <name>                             # alias for `new --lib`
```

`--lib` (the default) creates a bare `mod` + test skeleton.
`--app` adds an OTP `app` container, a root supervisor, and a
`[release]` table. `--fsm` adds a toy FSM.

```bash
$ ./cure new demo_lib
Created project 'demo_lib' (template: lib)

$ ./cure new demo_app --app
Created project 'demo_app' (template: app)

$ ./cure new demo_fsm --fsm
Created project 'demo_fsm' (template: fsm)

$ ./cure init demo_init
Created project 'demo_init' with Cure.toml, lib/main.cure
```

The `app` template produces three source files and a `Cure.toml`
with all five tables wired up:

```cure
app Demo_app
  vsn         = "0.1.0"
  description = "Demo_app"
  root        = sup Demo_app.Root

mod Demo_app
  fn hello() -> String = "hello from demo_app"

sup Demo_app.Root
  strategy = :one_for_one
  intensity = 3
  period = 5
  children
```

## `cure deps` --- resolve dependencies

```text
cure deps
```

Reads `[dependencies]` from `Cure.toml`, fetches transitive
manifests from the registry, and writes `Cure.lock`. With no
dependencies declared, it is a single round trip that prints a
confirmation:

```bash
$ cd demo_lib
$ ./cure deps
Resolving dependencies for demo_lib...
Dependencies resolved. Cure.lock written.
```

## `cure test` --- run `.cure` tests

```text
cure test [--filter PATTERN] [--doctests] [--cover]
```

Walks `test/**/*.cure`, compiles every file in-memory, and invokes
every zero-arity `test_*` export. `--filter` narrows by substring,
`--doctests` also runs examples lifted from doc comments, `--cover`
enables BEAM code coverage and writes an HTML report.

```bash
$ cd demo_lib
$ ./cure test
  PASS test/main_test.cure: test_math
1 passed, 0 failed

$ ./cure test --cover
  PASS test/main_test.cure: test_math
1 passed, 0 failed
Coverage summary
========================================
----------------------------------------
total: 100.0% (0/0)
Coverage HTML written to _build/cure/cover/index.html
```

Failures render as a `FAIL` line and force a non-zero exit:

```bash
$ ./cure test
error:   FAIL test/main_test.cure: test_hello -- :undef
0 passed, 1 failed
```

## `cure bench` --- micro-benchmarks

```text
cure bench [path]
```

Same discovery rules as `test`, but looks for `bench/**/*.cure` and
`test/**/*_bench.cure`, and invokes every zero-arity `bench_*` export
under `:timer.tc/1`. Wall time is reported per benchmark in
milliseconds:

```bash
$ ./cure bench
  bench/main_bench.cure:bench_greet  0.0 ms
```

With no bench files on disk:

```bash
$ ./cure bench
No benchmark files found. Place benchmarks under bench/*.cure
```

## `cure explain` and `cure why` --- error codes

```text
cure explain <Eddd>
cure why <Eddd>          # alias for explain
```

The Cure compiler emits diagnostics keyed to an `Eddd` code. Each
code has a short explainer shipping with the compiler:

```bash
$ ./cure explain E001
E001: Type Mismatch

A function's body type does not match its declared return type,
or an argument type does not match the parameter type.

Example:
  fn add(a: Int, b: Int) -> String = a + b
  # Error: declared return type String but body has type Int

Fix: change the return type annotation or the function body.

$ ./cure why E002
E002: Unbound Variable

A variable is referenced that has not been defined in the current scope.

Example:
  fn foo() -> Int = x + 1
  # Error: undefined variable 'x'

Fix: define the variable with let, or check for typos.
```

Unknown codes surface as a terse error:

```bash
$ ./cure why E099
error: Unknown error code: E099. Run 'cure explain' for a list.
```

## `cure doctor` --- health check

```text
cure doctor
```

A one-shot environment + project + source audit. Prints a report
keyed by `DOC-ENV-*` and `DOC-PROJ-*` tags, then exits non-zero if
any `[error]` findings accumulated.

```bash
$ cd demo_lib
$ ./cure doctor
Cure Doctor report
========================================
[ ok ]  DOC-ENV-01
     Elixir 1.20.0-rc.4 / OTP 29

[ ok ]  DOC-ENV-Z3
     Z3 at /usr/bin/z3

[ ok ]  DOC-ENV-REG
     Registry URL: https://registry.cure-lang.org

[ ok ]  DOC-ENV-TEL
     :telemetry library loaded; pipeline events are exported.

[ ok ]  DOC-PROJ-01 (./Cure.toml)
     demo_lib 0.1.0 (0 deps)

OK -- nothing to fix.
```

Run outside of a project, it flags the missing `Cure.toml` as a
warning:

```text
[warn]  DOC-PROJ-NOFILE (.)
     No Cure.toml found under ..
     fix: Run `cure new <name>` to scaffold a project.

Issues: warnings=1 errors=0
```

## `cure fix` --- conservative project-wide rewrites

```text
cure fix [--dry-run]
```

Walks `lib/**/*.cure` and `test/**/*.cure` and applies a fixed set
of structural rewrites (line-ending normalisation, trailing
whitespace stripping, tab expansion, blank-line collapse, trailing
newline). Anything that would change the parse tree is reverted.
`--dry-run` prints the plan without writing.

```bash
$ ./cure fix --dry-run
  would fix lib/messy.cure: strip_trailing_whitespace, collapse_blank_lines

$ ./cure fix
  fixed lib/messy.cure: strip_trailing_whitespace, collapse_blank_lines
cure fix: 1 file(s) rewritten.

$ ./cure fix
cure fix: nothing to change.
```

## `cure publish` --- to the registry

```text
cure publish [--dry-run] [--hex]
             [--handle HANDLE] [--token TOKEN]
             [--registry URL]
```

Three modes sit under the same command. `--dry-run` builds the
tarball, reports its hash and size, and exits. Good last-check
before pushing:

```bash
$ ./cure publish --dry-run
Would upload demo_lib 0.1.0
  sha256 = 1dd169b0a82b3fe4af1bd25af2a1e35b3db1ddb1d7641a5d9b5706d781065246
  size   = 399 bytes
  files  = 0 declared deps
```

`--hex` emits a Hex-compatible tarball at
`_build/cure/publish/hex.tar` so existing Elixir release tooling can
do the final push:

```bash
$ ./cure publish --hex
Hex-compatible tarball written to _build/cure/publish/hex.tar
Next: `mix hex.publish package --replace` with the tarball above.
```

The plain form signs the tarball with the key bound to `--handle`
(or `CURE_HANDLE`) and POSTs it to the registry with the bearer
token in `--token` (or `CURE_TOKEN`). See
[`docs/PUBLISHING.md`](https://github.com/cure-lang/cure-lang/blob/main/docs/PUBLISHING.md)
for the full lifecycle.

## `cure search` --- registry substring search

```text
cure search <query> [--registry URL]
```

HTTP-backed `GET /packages?q=<query>` against the configured
registry. The hit format is
`  <name> <version> -- <description>`. Without a reachable
registry, you see the raw transport error:

```bash
$ ./cure search list
error: cure search failed: {:fetch_failed, "/packages?q=list", {:failed_connect, ...}}
```

Against a live registry (or the test-suite mock), a successful run
prints one result per line.

## `cure info` --- manifest and version listing

```text
cure info <name[:ver]> [--registry URL]
```

Without a version, lists every published version of `name` as
`<ver>  (sha256: ...)`. With a version, prints the full manifest as
pretty-printed JSON. The plumbing lives in
`Cure.Project.Registry.{list_versions/1, fetch_manifest/2}`:

```bash
$ ./cure info std.list
error: cure info failed: {:fetch_failed, "/packages/std.list", {:failed_connect, ...}}
```

Same caveat as `search`: this one needs the registry to be up. When
the registry responds, the output shape is documented in
[`docs/PACKAGE_REGISTRY.md`](https://github.com/cure-lang/cure-lang/blob/main/docs/PACKAGE_REGISTRY.md).

## `cure keys` --- Ed25519 publisher keys

```text
cure keys generate <handle>
cure keys list
```

`generate` produces a fresh Ed25519 keypair under
`~/.cure/keys/`: `<handle>.sec` (mode `0600`), `<handle>.pub`, and
an appended line in `trusted.toml`. `list` prints every handle the
local client trusts and the first 16 hex characters of its public
key.

```bash
$ ./cure keys generate aleksei
Generated keypair for 'aleksei' under ~/.cure/keys/

$ ./cure keys list
  aleksei  b0d2d73255237b8e...
  alice  66d322a6667ac901...
  bob  b6eb8f937f56df00...
  eve  e45a482f3ff4fe7a...
```

The private key is used by `cure publish` to sign the tarball
envelope; the public key is shared with downstream consumers so
they can verify uploads. Treat the `.sec` file like an SSH private
key.

## `cure release` --- BEAM release builder

```text
cure release [--include-erts] [--overwrite] [-o DIR]
```

Assembles a standalone BEAM release from a project that declares an
`app` container. Reads `[release]` from `Cure.toml` for the release
name, version, extra applications, and optional overrides for
`vm.args` / `sys.config`. Writes the standard ERTS layout to
`_build/cure/rel/<name>/`.

In the escript build used for this post (v0.27.0 shipping tarball),
`cure release` bails out when it cannot locate the Elixir
application bundle from its own install path:

```bash
$ ./cure release
** (File.Error) could not list directory ".../cure/elixir/ebin": not a directory
    (cure 0.27.0) lib/cure/release.ex:276: Cure.Release.copy_application/4
    ...
```

Driven from `mix`, the same `Cure.Release.build/2` entry point
assembles `lib/<app>-<vsn>/ebin/`, a `.rel`, a boot script,
`sys.config`, `vm.args`, and a launcher. The command surface itself
is the right one --- the resolution of dependent apps is what needs
a Mix-provided context on this machine.

## `cure top` --- live runtime snapshot

```text
cure top
```

Single-shot snapshot of the Cure runtime: supervisors, actors, and
FSMs currently registered. Reads the live ETS tables owned by
`Cure.Sup.Runtime`, `Cure.Actor.Runtime`, and `Cure.FSM.Runtime`.
When no release is running, you still see the header:

```bash
$ ./cure top
cure top  2026-04-22T04:51:01.039362Z              procs=115  reductions=2392984

Supervisors (0)
  (no supervisors running)

Actors (0)
  (no actors running)

FSMs (0)
  (no FSMs running)
```

Against a booted release the three sections fill in; shape is
documented in the v0.27.0 announcement under _Observability_.

## `cure trace` --- typed tracer

```text
cure trace <M.f/a> [--duration N]
```

Hooks `:dbg` onto `{Mod, Fn, Arity}`, prints every call and return,
and annotates arguments with their compile-time Cure types when the
signature is known. The tracer stops after `--duration` seconds
(default 10):

```bash
$ ./cure trace --duration 1 Cure.Std.List.map/2
Tracing Cure.Std.List.map/2 for 1s...
Trace stopped.
```

Calls observed during the window render as:

```text
call #PID<0.212.0> Cure.Std.List.map/2([1, 2, 3] : List(Int), #Function<...>)  [pure]
return #PID<0.212.0> Cure.Std.List.map/2 -> [2, 4, 6] : List(Int)
```

## `cure synth` --- typed-hole synthesis

```text
cure synth --goal <type> --ctx "x=T,y=T,..."
```

Given a goal type and a typed context, produces a ranked list of
well-typed expressions that fit the hole. The ordering is
shorter-beats-longer, pure-beats-effectful, local-vars-beat-stdlib:

```bash
$ ./cure synth --goal Int --ctx "n=Int,xs=List(Int)"
goal: Int
ctx:  %{"n" => "Int", "xs" => "List(Int)"}

Candidates:
  1. n  (cost 1, pure)
  2. n |> Std.Core.identity  (cost 3, pure)
  3. n |> Std.Math.abs  (cost 3, pure)

$ ./cure synth --goal String --ctx "s=String,n=Int"
goal: String
ctx:  %{"n" => "Int", "s" => "String"}

Candidates:
  1. s  (cost 1, pure)
  2. n |> Std.Core.identity  (cost 3, pure)
  3. s |> Std.Core.identity  (cost 3, pure)
```

If the depth budget is exhausted without any match, the compiler
raises `E061 Synthesis Budget Exhausted` and the CLI walks away
with an empty result.

## `cure version` --- version stamp

```text
cure version
```

Prints `Cure <semver>` and exits:

```bash
$ ./cure version
Cure 0.27.0
```

## `cure help` --- the table of contents

```text
cure help       # or `cure`, or `cure -h`
```

The canonical usage block. Every command shown above was read
straight off that output.

## Cross-reference: option index

A few options recur across commands. For convenience:

- `-o DIR`  ---  `compile`, `release`, `doc` output directory.
- `--no-type-check`  ---  `compile` / `run` only (never bypasses
  `check`).
- `--optimize`  ---  enables the compiler's optimisation passes.
- `--filter PATTERN`  ---  `test` substring filter.
- `--cover`  ---  `test` coverage HTML at
  `_build/cure/cover/index.html`.
- `--dry-run`  ---  `fix` and `publish` dry-run modes.
- `--hex`  ---  `publish` Hex-compatible tarball.
- `--registry URL`  ---  `publish` / `search` / `info` registry
  override.
- `--action {compile|check|test}`  ---  `watch` per-save action.
- `--poll-ms N` / `--debounce N`  ---  `watch` timing knobs.
- `--include-erts` / `--overwrite`  ---  `release` layout knobs.
- `--lib | --app | --fsm`  ---  `new` template selector.
- `-v, --verbose`  ---  verbose output across commands.
- `-h, --help`  ---  local help.

## Wrap-up

`cure` in v0.27.0 is a single escript that covers compile, run,
check, LSP, docs, formatting, REPL, watch, scaffolding, deps,
tests, benchmarks, error explanations, health checks, safe fixes,
registry publish/search/info, publisher keys, OTP releases, a
runtime snapshot, a typed tracer, and typed-hole synthesis. The
uniform shape --- `cure <command> [options] [arguments]` --- makes
it comfortable to script; the fact that every command emits
structured text rather than a fancy TUI makes it friendly to CI,
`grep`, and pipes.

If you skipped to the end and want a one-line setup to try any of
this on your own machine:

```bash
git clone https://github.com/cure-lang/cure-lang.git
cd cure-lang
mix deps.get && mix escript.build
./cure help
```

Every transcript in this post was captured off exactly that
build, on Elixir 1.20.0-rc.4 / OTP 29, with `Z3` on `$PATH`. If a
command in this post behaves differently on your machine, I would
like to hear about it.
