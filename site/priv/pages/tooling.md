%{
  title: "Tooling",
  description: "CLI, Language Server, MCP server, optimizer, profiler, and pipeline events.",
  order: 9
}
---

Cure ships with a CLI, LSP and MCP servers, structured diagnostics, a
compilation profiler, and a PubSub event system that lets external tools
observe every compilation stage. All compiler-facing tools now use the same
dependent front end and canonical module loader.

## CLI

The `cure` escript is the primary interface. Build it with `mix escript.build`.

```bash
cure <command> [options] [arguments]
```

### Subcommands

**`cure compile <file|dir>`** -- Compile `.cure` files to BEAM bytecode.

```bash
cure compile hello.cure
cure compile src/               # compiles all .cure files recursively
cure compile hello.cure --output-dir _build/cure/project/ebin --verbose
```

Options:

- `--output-dir DIR` (`-o`) -- artifact-set root (default: `_build/cure/project/ebin`)
- `--verbose` (`-v`) -- show detailed compilation output

Compilation cannot bypass the dependent checker or trusted Core validation.

**`cure run <file>`** -- Compile and execute a `.cure` file. Calls `main/0` if
it exists. It uses the same checked dependent pipeline as `compile`.

```bash
cure run examples/hello.cure
cure run examples/recursion.cure
```

**`cure check <file>`** -- Type-check without compiling. Runs lexer, parser,
and type checker, then reports errors or prints `<file>: OK`.

```bash
cure check lib/std/core.cure
```

**`cure lsp`** -- Start the Language Server Protocol server over stdio.

```bash
cure lsp
```

**`cure stdlib`** -- Compile all `.cure` files in `lib/std/` to BEAM bytecode.

```bash
cure stdlib
cure stdlib --output-dir _build/cure/ebin
```

**`cure version`** -- Print the Cure version.

**`cure init <name>`** -- Create a new Cure project with `Cure.toml` and
`lib/main.cure`.

```bash
cure init my_project
```

**`cure deps`** -- Resolve dependencies from `Cure.toml`.

**`cure test`** -- Run test files from `test/`. Compiles each `.cure` file,
then calls all exported functions whose names start with `test`. Reports
pass/fail counts.

```bash
cure test
```

**`cure doc [path|dir]`** -- Generate HTML documentation from `.cure` files.

As of v0.29.0 the generator produces an ExDoc-like two-pane site. A
persistent left sidebar lists orphan pages (`[doc].extras`) and every
extracted module (optionally grouped via `[doc.groups_for_modules]`);
the right pane renders the selected page with anchored entries for
every public function, type, and protocol, a local table of contents,
a `prefers-color-scheme` theme toggle, and a keyboard-focusable (`/`)
filter over the sidebar. Module docstrings are parsed as Markdown
(via the NIF-free `:md` library, wrapped by `Cure.Doc.Markdown`) with
Makeup-powered syntax highlighting for `cure` / `elixir` / `erlang`
fenced code blocks.

```bash
cure doc                         # documents lib/**/*.cure and lib/std/*.cure
cure doc lib/std/ -o _build/cure/doc --title "Cure Stdlib"
cure doc --main MyLib.Core --extras README.md --extras CHANGELOG.md
```

Options:

- `--output-dir DIR` (`-o`) -- output directory (default: `_build/cure/doc`)
- `--title TITLE` -- title shown in the sidebar; overrides `[doc].title`
- `--main SLUG` -- landing-page slug (module name or extra slug)
- `--extras PATH` -- repeatable; prepended Markdown files turned into
  orphan pages

The `[doc]` table in `Cure.toml` drives the rest of the layout
(`main`, `title`, `extras`, `logo`, `source_url`, `source_ref`, plus
`[doc.groups_for_modules]`). Placeholders `{{cure_version}}` and
`{{cure_vversion}}` are substituted inside every docstring before
rendering.

The full reference lives at
[`docs/DOC.md`](https://github.com/cure-lang/cure-lang/blob/main/docs/DOC.md).

### `/stdlib` on the Cure website (v0.29.0)

The Cure website ships the same documentation layout for the
standard library. `CureSite.Stdlib` walks `cure/lib/std/*.cure` at
site-compile time; `CureSiteWeb.StdlibController` serves `/stdlib`
(the index) and `/stdlib/:module` (one page per module) with a
DaisyUI-styled two-pane layout and a GitHub "View source" link.
The old hand-written `/standard-library` 301-redirects to `/stdlib`.

### highlight.js language description (v0.29.0)

`highlightjs-cure/` in the repository ships a highlight.js
language description for Cure (`src/languages/cure.js`) plus a demo
page and a minified bundle (`dist/cure.min.js`). Drop it into any
highlight.js-backed site to syntax-highlight `.cure` snippets in
blog posts and READMEs without pulling in Makeup.

**`cure fmt [path|dir]`** -- Format `.cure` source files in place.

As of v0.21.0, the default formatter is the
**Wadler/`Inspect.Algebra`-style pretty printer** built on
`Cure.Compiler.Algebra` and `Cure.Compiler.AlgebraFormatter`. It
uses a best-fit line-wrapping algorithm, separates top-level
definitions with blank lines, and round-trips plain `#` comments
(lexed under `preserve_comments: true`) as real `# ...` lines in
source order. Every rewrite is round-trip-validated against the
original AST modulo comment placement; if verification fails, the
file is left untouched, so the formatter is non-destructive by
construction.

```bash
cure fmt                         # algebra formatter (default)
cure fmt lib/std/core.cure       # format a specific file
cure fmt --check                 # CI mode: exits 1 if any file would change
cure fmt --dry-run               # show colour diff without touching disk (v0.28.0)
cure fmt --safe                  # legacy byte-level safe formatter
cure fmt --aggressive            # legacy AST rewrite; strips comments
```

Options:

- `--check` -- report files that would be reformatted and exit
  non-zero; leaves files on disk untouched.
- `--dry-run` (v0.28.0) -- render a colour-annotated unified diff
  for every file that would change using `List.myers_difference/2`.
  Red lines (`-`) are removed; green lines (`+`) are added. Exits 1
  when any file has pending changes, making it a natural CI gate:
  `cure fmt --dry-run || exit 1`. ANSI colour is suppressed when
  `NO_COLOR` is set or stdout is not a tty.
- `--safe` -- v0.20.0 byte-level formatter. Kept as an escape hatch
  for sources that trip the algebra formatter's round-trip check.
- `--algebra` -- explicit opt-in to the algebra formatter;
  synonymous with the default since v0.21.0.
- `--aggressive` / `--ast` -- legacy AST pretty printer. Strips
  plain `#` comments. Prints a warning before touching files.

**`cure repl`** -- Start a readline-grade interactive Cure session.
Since v0.24.0, the REPL runs on top of a raw-mode line editor with
live `Makeup`-powered syntax highlighting, persistent history, `Ctrl+R`
incremental reverse search, Tab completion, a minimal vi mode, and a
`Marcli`-rendered `:help`. Each submitted expression is compiled via
`compile_and_load` and its result printed.

```bash
cure repl
```

See the dedicated [REPL reference page](/repl) for the complete
key-bindings table and meta-command list.

**`cure replay <path.journal>`** (v0.28.0) -- Replay a recorded FSM
trace from a `.journal` file produced by a `@record`-annotated FSM
container.

```bash
cure replay .cure-trace/abc123.journal               # print trace only
cure replay .cure-trace/abc123.journal --module MyFsm  # live replay
cure replay .cure-trace/abc123.journal --module MyFsm --step  # step mode
```

See [`docs/REPLAY.md`](https://github.com/cure-lang/cure-lang/blob/main/docs/REPLAY.md)
for `@record` annotation details and the full API.

**`cure explain <code>`** -- Look up a structured error explanation.

```bash
cure explain E001
cure explain E010
```

**`cure help`** -- Show usage information.

## v0.34.0 additions

### Migration and editions

`cure migrate` ports source between editions. It understands the current
keyword and module changes, including `proto` / `impl` to `interface` /
`implementation`, legacy conditionals to `pickup`, uppercase type variables,
module renames, and decorator placement.

```bash
cure migrate --check examples
cure migrate --print lib/old.cure
cure migrate --strict lib/
```

Migration runs rules to a fixpoint, reparses the result, supports atomic batch
updates, and refuses unsafe mutation of a dirty worktree. `@edition` and
`Cure.toml [project].edition` pin the grammar a project expects.

### Trust audit

```bash
cure audit trust My.Module
cure audit trust My.Module --format json --strict
```

The report follows canonical definition reachability and lists the
`postulate`, bodyless `@extern`, and `believe_me` roots on which the selected
module actually depends.

### Canonical multi-file builds

CLI, project, and incremental Mix compilation now share:

- dependency-graph ordering rather than filesystem order;
- duplicate-module, unresolved-import, and cycle diagnostics;
- immutable module interfaces and canonical owner-qualified definitions;
- deterministic implementation-provider loading;
- user `@prelude` discovery and transitive operator-fixity propagation;
- dependency-aware incremental invalidation.

### Structured diagnostics

Compiler failures are adapted at their owning subsystem into a common
diagnostic shape. Terminal, JSON, LSP, migration, and audit output share stable
codes, primary and related source ranges, canonical definition identities,
provenance, and machine-safe fixes.

Repository maintainers can audit registry coverage with:

```bash
mix cure.diagnostics --color=always --width=80 --coverage
mix cure.diagnostics.audit
```

### Authoritative example checks

`mix cure.check.examples` discovers every root `.cure` example, compiles it,
and runs every recorded `main/0` expectation. A manifest distinguishes
language, library, migration, and optimizer-only status, fails on silently
omitted files, and treats a passing skipped fixture as stale. The current
corpus has 40 passing examples, no skips, and no failures.

## v0.33.0 additions

### Formal specifications for `match` and `pickup`

v0.33.0 publishes two long-form normative specifications into HexDocs
alongside the rest of the language references. Both are stable at
version 1.0.0 and follow the same five-stratum layout (surface;
semantics; surface conventions; theory and machinery; closure) plus
eleven appendices (acceptance corpus, glossary, change log,
normative-requirement index, reference implementation sketch, worked
examples, style guide, anti-patterns, reserved future syntax,
soundness proof sketch, bibliography, open questions, colophon).

- [`docs/MATCH.md`](https://github.com/cure-lang/cure-lang/blob/main/docs/MATCH.md)
  -- *The `match` Construct, Language Specification, Version 1.0.0*.
  Implementer-facing sections cover the EBNF grammar, the full
  pattern sub-grammar, T-Match typing, Maranget-style exhaustiveness,
  reachability, refinement narrowing, big-step / small-step
  operational semantics, the soundness proof sketch, and the
  diagnostic catalogue (`E004`, `E021`-`E025`, `E031`-`E034`).
- [`docs/PICKUP.md`](https://github.com/cure-lang/cure-lang/blob/main/docs/PICKUP.md)
  -- *The `pickup` Construct, Language Specification, Version 1.0.0*.
  Mirrors `MATCH.md` for predicate dispatch: T-Pickup-Else /
  T-Pickup-Cons, totality enforced by the mandatory terminator,
  source-order short-circuit semantics, refinement-context
  strengthening, the migration story for legacy `if` / `elif`
  (`cure rewrite if-to-pickup`, `E-IF-REMOVED`), and the diagnostic
  catalogue (`E-PICKUP-NO-ELSE`, `E-PICKUP-ELSE-NOT-LAST`,
  `E-PICKUP-MULTIPLE-ELSE`, `E-PICKUP-GUARD-TYPE`,
  `E-PICKUP-BRANCH-MISMATCH`).

Tooling-relevant sections include twenty-five formatter-conformance
clauses per construct (alignment, comment fidelity, idempotence,
round-trip, performance bounds, plugin interface, editor-folding
integration, and a final formatter grammar), language-server
requirements (hover, code actions, smart-selection, foldable
regions), and macro / quote interaction rules. The `cure rewrite
if-to-pickup` migration tool, the `cure fmt` formatter, and the LSP
server are all expected to satisfy these clauses.

User-facing pages live at [`/match`](/match) and [`/pickup`](/pickup);
`docs/LANGUAGE_SPEC.md` cross-references both as the normative
sources of truth.

---

## v0.32.0 additions

### `cure verify` -- offline proof verification

`cure verify` replays the `.cureproof` artifacts embedded in
published package tarballs (v0.32.0) through the offline verifier
without re-running the full SMT solver or the type-checker:

```bash
mix cure.verify                          # verify current project's own proofs
mix cure.verify my_pkg-0.1.0.tar.gz     # verify a tarball
mix cure.verify _build/cure/deps/       # verify installed deps
mix cure.verify --strict ...            # E065 on missing .cureproof artifact
```

`cure publish` now embeds a `<name>.cureproof` file (gzip-compressed
binary certificates: equality witnesses, refinement bounds, SMT
models, totality SCCs) unless `[publish] include_proofs = false` is
set in `Cure.toml`. Three new error codes: **E065 Proof File
Missing**, **E066 Proof Verification Failed**, **E067 Proof Schema
Incompatible**. Full reference:
[`docs/PROOF_CARRYING.md`](https://github.com/cure-lang/cure-lang/blob/main/docs/PROOF_CARRYING.md).

### `cure export-types` -- cross-language ADT export

Translates Cure `rec`, `type`, and `enum` declarations to schema
files for external languages. The first target is proto3:

```bash
mix cure.export_types                                      # all lib/**/*.cure
mix cure.export_types --target protobuf --out proto/       # explicit dir
mix cure.export_types --dry-run                            # print, don't write
mix cure.export_types lib/events.cure lib/types.cure       # specific files
```

Type mapping highlights: `Int->int64`, `List(T)->repeated T`,
`Option(T)->optional T`, pure-enum ADTs to proto3 `enum`,
payload-bearing ADTs to wrapper `message` + `oneof value` blocks.
Field names are converted `camelCase->snake_case`; field numbers by
declaration order. Refinements and dependent types emit `bytes` with
a comment and raise **E068 Export Type Unmappable** (warning, not
hard error). Full reference:
[`docs/EXPORT_TYPES.md`](https://github.com/cure-lang/cure-lang/blob/main/docs/EXPORT_TYPES.md).

### `cure snap` -- REPL session snapshots

Save and restore the entire REPL environment as a compact binary
(`.cure-snap`) file. Available as REPL meta-commands and as a Mix
task:

```bash
# inside the REPL
:snap save my-session.cure-snap
:snap load my-session.cure-snap
:snap list sessions/

# from the shell (inspection without a running REPL)
mix cure.snap load my-session.cure-snap
mix cure.snap list .
```

A snap captures: all named declarations (`fn`, `type`, `rec`,
`interface`, `implementation`, `proof`), up to 500 history entries, `use` imports,
open typed holes, stdlib mode, theme, and editing mode. Loading
*merges* rather than replaces: last-writer-wins for defs, union for
uses, prepend for history. Two new error codes: **E069 Snap Schema
Incompatible**, **E070 Snap Module Missing**. Full reference:
[`docs/SNAP.md`](https://github.com/cure-lang/cure-lang/blob/main/docs/SNAP.md).

### `cure story` -- narrative architecture generator

Reads a project's source tree and writes `STORY.md` -- a
human-readable introduction to the system, top-down:

```bash
mix cure.story                           # write STORY.md at project root
mix cure.story --diagrams                # embed Mermaid FSM diagrams
mix cure.story --out docs/ARCH.md       # custom output path
mix cure.story --format html --out docs/story.html
mix cure.story --stdout                  # print without writing
```

The generator parses every `.cure` file under `lib/`, classifies AST
containers into a five-layer outline (app -> supervisor -> actor ->
fsm -> types), and emits structured prose for each. `--diagrams`
embeds Mermaid `stateDiagram-v2` blocks for each FSM, renderable in
GitHub Markdown and GitLab without extra tooling. Use as a CI gate:

```bash
mix cure.story --out /tmp/STORY.md && diff STORY.md /tmp/STORY.md
```

Full reference:
[`docs/STORY.md`](https://github.com/cure-lang/cure-lang/blob/main/docs/STORY.md).

---

## v0.30.0 additions

### `cure john` -- everything-at-once diagnostic

A single panoramic diagnostic that gathers everything worth knowing
about Cure, the BEAM VM, the project currently in `pwd`, and the last
few log entries, and prints it as Markdown-to-ANSI. Three surfaces
funnel into one implementation:

- `mix cure.john`
- `cure john`
- `:john` (REPL meta-command)

```bash
cure john                         # banner + every section, ANSI out
cure john --width 120             # wider separators
cure john --no-ansi --no-banner   # CI-friendly raw Markdown
```

Sections: Cure (version, app state, stdlib modules loaded, pipeline
event-bus size, protocol registry size); BEAM / OTP (scheduler
topology, memory breakdown, process / port / atom counts, reductions,
uptime); System (OS, architecture, hostname, `LANG` / `TERM` /
`SHELL`); Tooling (`z3` / `git` / `make` / `cc` presence plus loaded
dependency versions); Project (when `Cure.toml` is present: name,
version, source paths, lockfile status, dependency table); Runtime
(condensed `cure top` snapshot); Doctor (severity counters); Recent
logs (tails of `.cure/logs/` and `_build/cure/logs/`).

Renders through `Marcli.render/2` when its MDEx NIF can load, and
falls back to `Cure.REPL.Markdown.render/2` inside the escript.

Named in tribute to **John Carbajal**. See
[`docs/JOHN.md`](https://github.com/cure-lang/cure-lang/blob/main/docs/JOHN.md)
for the full reference.

---

## v0.24.0 additions

### Interactive REPL rewrite

**`cure repl`** -- The legacy `IO.gets` loop has been replaced by a
raw-mode line editor. The whole architecture is split across small,
single-responsibility modules:

- `Cure.REPL.Terminal` -- raw-mode stdin via `stty`, safe restore on
  every exit path, decodes arrows, `Home` / `End` / `Delete` /
  `PgUp` / `PgDn`, `Ctrl+Arrow` word-wise movement, `F1`-`F12`, and
  bracketed paste.
- `Cure.REPL.LineEditor` -- a pure-function line buffer. Cursor
  movement, kill ring + yank + rotate, transpose, case changes,
  undo / redo, and a minimal vi normal mode.
- `Cure.REPL.History` -- atomic write-and-rename `~/.cure_history`,
  consecutive-duplicate dedup, 10,000-entry cap, draft-preserving
  `Up` / `Down` navigation.
- `Cure.REPL.Search` -- `Ctrl+R` / `Ctrl+S` incremental reverse and
  forward search with inverse-video status line and accept-and-edit
  semantics.
- `Cure.REPL.Completer` -- Tab completion for meta-commands, file
  paths (inside `:load` / `:save` / `:edit`), loaded modules (inside
  `:use` / `:doc`), and Cure keywords.
- `Cure.REPL.Highlight` + `Cure.REPL.Theme` -- live ANSI syntax
  highlighting via `Makeup.Lexers.CureLexer` and `Marcli.Formatter`.
  `:dark` (default), `:light`, and `:mono` presets; `:mono` is forced
  automatically when `NO_COLOR` is set, when stdout is not a tty, or
  when `TERM=dumb`.

New meta-commands alongside the existing `:t`, `:type`, `:effects`,
`:load`, `:reload`, `:use`, `:holes`, `:env`, `:reset`, `:fmt`,
`:help`, `:quit`:

- `:history [n]`, `:search term`, `:clear`
- `:save path`, `:edit`
- `:time expr`, `:bench expr [n]`
- `:ast expr`
- `:theme dark|light|mono`, `:mode emacs|vi`, `:color on|off`

Non-tty stdin (CI, pipes) short-circuits to the legacy `IO.gets`
loop so test automation is unaffected.

The REPL page also documents the three new Hex deps that back it:
[`makeup`](https://hex.pm/packages/makeup) + [`makeup_cure`](https://hex.pm/packages/makeup_cure)
for lexing, [`marcli`](https://hex.pm/packages/marcli) for
Markdown-to-ANSI rendering.

---

## v0.23.0 additions

### Package registry

**`cure publish`** -- Build the package tarball, sign it with the
maintainer's Ed25519 key, upload via `POST /packages`. Reads the
maintainer handle and upload token from `--handle` / `--token`, or
from the `CURE_HANDLE` / `CURE_TOKEN` environment variables.

```bash
cure publish --handle alice --token $CURE_TOKEN
cure publish --dry-run          # build + verify locally, no upload
cure publish --hex              # emit a Hex-compatible tarball under
                                # _build/cure/publish/hex.tar
```

**`cure search <query>`** -- Substring search against the registry
index.

**`cure info <name>[:version]`** -- Print the version list for a
package, or the full manifest JSON when a version is given.

**`cure keys generate <handle>`** -- Generate an Ed25519 keypair under
`~/.cure/keys/` and add the public key to `trusted.toml`.

**`cure keys list`** -- List every handle currently on the trust list.

### Health and hygiene

**`cure doctor`** -- Structured environment + project + source health
report. Exits non-zero when any finding has severity `:warning` or
`:error`, so it is ready to drop into CI. Checks include Elixir / OTP
/ Z3 presence, `:telemetry` availability, registry URL, `Cure.toml`
sanity, lockfile freshness, open type holes, and undocumented public
functions.

**`cure fix [--dry-run]`** -- Project-wide safe rewrites over
`lib/**/*.cure` and `test/**/*.cure`. Five conservative transforms:
`normalize_line_endings`, `strip_trailing_whitespace`,
`strip_mixed_tabs` (leading tabs -> two spaces), `collapse_blank_lines`,
and `ensure_trailing_newline`. Silently no-ops on already-clean files.

### Coverage

**`cure test --cover`** -- Instrument every compiled module under
`_build/cure/project/ebin/` via OTP's `:cover`, run the self-hosted test suite,
and emit an HTML report under `_build/cure/cover/index.html` plus a
text summary.

### Telemetry bridge

Start `Cure.Telemetry.start/0` from your host application to subscribe
to every `Cure.Pipeline.Events` stage and re-emit events under
`[:cure, :pipeline, <stage>, <event_type>]`. The `:telemetry` dep is
optional in `mix.exs`; when it is not on the load path the bridge
silently becomes a no-op.

---

## LSP Server

The LSP server implements the Language Server Protocol over stdio. It provides
real-time feedback in any editor that supports LSP.

### Capabilities

- **Text document synchronization** -- full sync mode. The server re-analyzes
  the entire document on every change.
- **Diagnostics** -- compile errors and type errors reported on every keystroke.
  Each diagnostic includes file, line, and a description.
- **Hover** -- shows function signatures, type information, and inferred
  effects when hovering over identifiers.
- **Completion** -- triggered by `.` and `:`, provides keyword completions.
- **Go-to-definition** (v0.13) -- jump to the definition of functions and
  modules.
- **Document symbols** (v0.13) -- hierarchical outline of modules, functions,
  protocols, and FSM definitions.
- **Code actions** (v0.13) -- quick-fix suggestions:
  - Add wildcard pattern for non-exhaustive matches.
  - "Did you mean?" suggestions for unbound variables (Levenshtein distance).

### AST caching

The server caches parsed ASTs per document version. If a `didChange`
notification arrives with the same version number, the server skips
re-parsing and re-diagnosing. This reduces redundant work during rapid edits.

### Neovim configuration

```lua
vim.api.nvim_create_autocmd("FileType", {
  pattern = "cure",
  callback = function()
    vim.lsp.start({
      name = "cure-lsp",
      cmd = { "cure", "lsp" },
      root_dir = vim.fs.dirname(
        vim.fs.find({ "Cure.toml", "mix.exs" }, { upward = true })[1]
      ),
    })
  end,
})
```

### VS Code (generic LSP client)

Any VS Code extension that supports custom LSP servers can be pointed at
`cure lsp`. Set the command to the absolute path of the `cure` escript.

---

## MCP Server

The Model Context Protocol server provides AI tool integration via JSON-RPC
2.0 over newline-delimited stdio. Start it with `mix cure.mcp`.

### Tools

7 tools are exposed:

**`compile_cure`** -- Compile Cure source code. Returns the module name and
exports on success, or error details.

```json
{"name": "compile_cure", "arguments": {"source": "mod Hello\n  fn main() -> Int = 42"}}
```

**`parse_cure`** -- Parse source and return an AST summary.

**`type_check_cure`** -- Type-check source. Returns errors and warnings.

**`analyze_fsm`** -- Analyze an FSM definition. Returns states, transitions,
and verification results (reachability, deadlock freedom).

**`validate_syntax`** -- Quick syntax validation (lex + parse only, no type
checking).

**`get_syntax_help`** -- Get help on a Cure syntax topic. Topics: `functions`,
`types`, `fsm`, `protocols`, `pattern_matching`, `modules`, `records`.

**`get_stdlib_docs`** -- Get documentation for a stdlib module by name
(e.g., `Std.List`, `Std.Core`).

### Protocol

The server speaks MCP protocol version `2024-11-05`. On `initialize`, it
returns its capabilities. Tools are listed via `tools/list` and invoked via
`tools/call`.

---

## Optimizer

> **Deferred in 0.34:** the sections below document the v0.31 classic-AST
> optimizer. That input pipeline was removed with the classic compiler.
> A future optimizer must consume validated dependent Core; current
> compile/run commands do not advertise these passes.

The optimizer runs 5 transformation passes on the MetaAST between type
checking and code generation. Enable it with `--optimize` on the CLI or
`optimize: true` in compiler options.

```elixir
{:ok, optimized_ast, stats} = Cure.Optimizer.optimize(ast)
```

### Pass 1: Inline

Small, pure, non-recursive functions are inlined at their call sites. The
function body replaces the call expression with arguments substituted.

Before:
```cure
fn double(x: Int) -> Int = x * 2
fn main() -> Int = double(21)
```

After optimization: `main` compiles to `21 * 2`.

### Pass 2: Constant fold

Evaluates constant expressions at compile time. Covers arithmetic (`+`, `-`,
`*`, `/`, `%`), boolean operations (`and`, `or`, `not`), string concatenation
(`<>`), and comparisons (`==`, `!=`, `<`, `>`, `<=`, `>=`).

Before:
```text
fn answer() -> Int = 6 * 7
fn greeting() -> String = "hello" <> " " <> "world"
```

After optimization: `answer` returns the literal `42`, `greeting` returns
`"hello world"`.

### Pass 3: Dead code elimination

Removes unreachable code:

- `if true then A else B` -> `A`
- `if false then A else B` -> `B`
- Code after `return` or `throw` is dropped.

### Pass 4: Pipe inline

Simplifies pipe chains by converting `a |> f |> g` into direct calls `g(f(a))`.
Also eliminates identity functions in pipe chains: `x |> identity |> f` becomes
`f(x)`.

### Pass 5: Guard simplify

Applies algebraic boolean simplification rules to guard expressions:

- `P and P` -> `P`
- `P or P` -> `P`
- `true and P` -> `P`
- `false and P` -> `false`
- `true or P` -> `true`
- `false or P` -> `P`
- `not not P` -> `P`
- `not true` -> `false`
- `not false` -> `true`

### Statistics

The optimizer returns a stats map counting transformations per pass:

```elixir
%{inline: 3, constant_fold: 7, dead_code: 2, pipe_inline: 1, guard_simplify: 0}
```

Individual passes can be run in isolation:

```elixir
{:ok, ast, count} = Cure.Optimizer.run_pass(ast, :constant_fold)
```

---

## Error Catalog

Cure uses structured error codes. Each code has a detailed explanation
accessible via `cure explain <code>`.

**E093: Type Mismatch** -- A function's body type does not match its declared
return type, or an argument type does not match the parameter type.

```cure E093
fn add(a: Int, b: Int) -> String = a + b
# error E093: declared return type String but body has type Int
```

**E091: Unknown Value** -- A value is referenced that has not been defined.

```cure E091
fn foo() -> Int = x + 1
# error E091: unknown value 'x'
```

**E003: Arity Mismatch** -- A function is called with the wrong number of
arguments.

```cure E003
fn add(a: Int, b: Int) -> Int = a + b
fn main() -> Int = add(1)
# error E003: expects 2 arguments, got 1
```

**E004: Non-Exhaustive Match** -- A match expression does not cover all
possible patterns.

```text
match x
  true -> "yes"
# warning E004: missing pattern for 'false'
```

**E005: Constraint Violation** -- A function with a guard constraint is
called with arguments that may violate the constraint. The compiler uses Z3
to check this.

```cure
fn safe_div(a: Int, b: Int) -> Int when b != 0 = a / b
fn main() -> Int = safe_div(10, 0)
# warning E005: b != 0 may be violated (counterexample: b = 0)
```

**E006: Effect Violation** -- A function performs an effect not declared in
its `!` annotation.

**E007: Unused Variable** -- A `let` binding or parameter is defined but
never referenced. Prefix with `_` to suppress.

**E008: Undocumented Public Function** -- A public function has no `##` doc
comment. Emitted only in `cure doc --strict` mode.

**E009: Unreachable Clause** -- A pattern matching clause is shadowed by a
prior clause.

**E010: Missing Effect Annotation** -- A public function performs side effects
but has no `!` annotation. Emitted only in `--strict-effects` mode.

### Dependent-type and pattern codes (v0.17.0+)

**E011: Missing Implicit Argument** -- first-order unification could not
solve every implicit parameter at a call site. The unification trace names
the constraint that failed.

**E012: Sigma Destructuring Failure** -- pattern attempted to destructure a
sigma value against shapes that disagree with its declared components.

**E013: Totality Failure** -- an `@total true`-annotated function is not provably
total.

**E014: Unfilled Hole** -- a `?name` or `?_` placeholder remained unfilled.
Informational unless `cure check --strict` is active.

**E015: Refinement Counterexample** -- a value flowing into a refinement-typed
parameter might violate the predicate; the Z3 model gives a witness.

**E016: Dependent Type Mismatch** -- a dependent return type does not match
the expected type at the use site after substitution and reduction.

**E017: Equality Proof Mismatch** -- historical code for the retired
primitive `Eq` / `refl` surface. Current identity proofs use
`Equivalent(T, a, b)` and `reflexive`; conversion or constructor mismatch
diagnostics retain the authored proof span.

**E018: Path-sensitive Refinement Conflict** -- a path-sensitive refinement
extracted from a guard contradicts a previously declared refinement.

**E019: Implicit Argument Solved Inconsistently** -- the same implicit was
solved to two different types from different parts of the call site.

**E020: Doctest Mismatch** -- a `cure>` doctest produced a different value
from its `=>` expected line.

### Pattern engine codes (v0.18.0)

**E021: Unknown Record Field in Pattern** -- a record pattern references a
field that is not declared in the record's schema.

**E022: Record Pattern Field Type Mismatch** -- a sub-pattern inside a record
pattern is incompatible with the declared type of that field.

**E023: Non-Literal Map Pattern Key** -- map keys in pattern position must
be literal values (atoms, integers, strings, ...).

**E024: Unbound Pin Variable** -- the pin operator `^x` was used on a name
that is not in scope at the pattern's position.

**E025: Non-Exhaustive Nested Match** -- a `match` with nested patterns does
not cover every inhabitant of the scrutinee type; the compiler prints a
concrete missing witness.

### v0.28.0 codes

**E063: Parse Error (recovered)** -- a statement contained a syntax
error from which the parser recovered by skipping tokens until the
next statement boundary (`fn`, `mod`, `rec`, etc.). Subsequent
definitions in the same file are still reported. Fix the primary
parse error; E063 diagnostics disappear automatically.

### v0.19.0 codes

**E026: Proof Shape Mismatch**
does not elaborate to the declared proposition.

**E027: `assert_type` Assertion Failed** -- the expression in
`assert_type expr : T` does not match `T`.

**E028: Record Default Type Mismatch** -- a record field's default value
does not match the declared field type.

**E029: Mutual Recursion Not Structural** -- an `@total true` function takes
part in a cycle in which no argument shrinks on every path.

**E030: Package Version Conflict** -- the dependency resolver could not find
a set of versions satisfying every active constraint.

### v0.21.0 codes

**E031: Binary Pattern Not Exhaustive** -- a sequence of binary patterns
(in a `match`, function head, `let`, or comprehension generator) does not
cover every byte-length inhabitant of the scrutinee's Bitstring type. The
compiler prints a concrete missing witness such as `"<<>>"` or
`"<<_, _rest::binary>>"`.

**E032: Function Type Payload Invalid** -- an ADT constructor payload
carries a value whose type cannot be resolved. Function-type payloads
(e.g. `On(Int -> Int)` and `On((Int, Int) -> Int)`) are allowed and compile
to first-class functions at runtime.

**E033: Multi-line Type Layout Invalid** -- a `type` ADT declaration
spans multiple lines but the layout cannot be absorbed by the type-def
recogniser. Usually means the continuation lines are not indented
beyond the `type` keyword.

**E034: Let Pattern Not Exhaustive** -- a `let` binding destructures its
RHS with a pattern that does not cover every inhabitant of the RHS type.
The binding still compiles -- Erlang's `=` raises at runtime on a failed
match -- but the compiler surfaces the gap as a warning.

### Error formatting

Errors include source location with caret display:

```
error: type mismatch in function 'bad'
 --> hello.cure:3
  | declared return type Int but body has type String
```

The compiler suggests corrections for typos using Levenshtein distance.
As of v0.28.0 this covers every name-resolution failure site: unbound
variables, record field patterns, CLI subcommands, REPL `:use`, and
REPL unknown meta-commands ("Did you mean `:type`?").

---

## Pipeline Events

Every stage of the compilation pipeline emits structured events through a
Registry-backed PubSub system. External tools (LSPs, profilers, debuggers,
IDE plugins) can subscribe and observe compilation in real time.

### Event structure

Events are 4-tuples: `{stage, event_type, payload, metadata}`

- **stage** -- `:lexer`, `:parser`, `:type_checker`, `:codegen`, `:fsm_verifier`
- **event_type** -- stage-specific atom (e.g., `:token_produced`, `:node_parsed`,
  `:form_generated`, `:error`)
- **payload** -- the data (token, AST node, error, etc.)
- **metadata** -- `%{file: String.t(), line: pos_integer(), timestamp: integer()}`

### Subscribing

```elixir
# Subscribe to all events from the lexer
Cure.Pipeline.Events.subscribe(:lexer)

# Subscribe only to errors from the parser
Cure.Pipeline.Events.subscribe(:parser, :error)
```

### Receiving events

Events are delivered as standard Erlang messages:

```elixir
receive do
  {Cure.Pipeline.Events, :lexer, :token_produced, token, meta} ->
    IO.inspect(token)
end
```

### Emitting (internal)

Pipeline stages use `emit/4`:

```elixir
Cure.Pipeline.Events.emit(:codegen, :form_generated, form, Events.meta(file, line))
```

Emission can be disabled with `emit_events: false` in compiler options (which
the CLI uses by default for non-profiling runs).

---

## Profiler

The profiler measures per-stage event counts and total compilation time by
subscribing to pipeline events.

### Usage

```elixir
{:ok, report} = Cure.Profiler.profile_file("hello.cure")
IO.puts(Cure.Profiler.format_report(report))

{:ok, report} = Cure.Profiler.profile_string(source, check_types: true, optimize: true)
```

### Report structure

```elixir
%{
  file: "hello.cure",
  source_bytes: 142,
  total_us: 1523,
  stages: %{
    lexer: %{count: 24},
    parser: %{count: 12},
    codegen: %{count: 8}
  },
  event_count: 44,
  result: "success"
}
```

### Formatted output

```
Cure Compilation Profile
========================
File:         hello.cure
Source:       142 bytes
Total time:   1.52 ms
Events:       44
Result:       success

Pipeline Stages:
  lexer                24     events
  parser               12     events
  codegen              8      events
```

The profiler subscribes to all 5 pipeline stages (`:lexer`, `:parser`,
`:type_checker`, `:codegen`, `:fsm_verifier`), drains events after compilation
completes, and groups them by stage.
