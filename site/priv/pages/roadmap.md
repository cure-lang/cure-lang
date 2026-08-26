%{
  title: "Roadmap",
  description: "What's implemented, what's next, and what's planned for the future.",
  order: 10
}
---

## In development: v0.34.0 -- One dependent language

v0.34 removes the classic compiler path. Every program now flows through the
dependent elaborator, trusted Core kernel, quantitative erasure, and BEAM
emitter.

- **Dependent surface** -- indexed families with separate parameters and
  indices, dependent results, implicit erased parameters, Sigma pairs,
  impossible and forced patterns, `with` abstraction, unions, `typealias`, and
  visible primitive declarations.
- **Quantitative checking** -- `{0, 1, ω}` grades plus affine/linear binders;
  proof/index data cannot escape erasure and capabilities cannot be duplicated.
- **Identity** -- `Std.Equivalent` and `reflexive` replace primitive
  `Eq`/`refl`/`rewrite`. Runtime comparison remains the distinct
  `Std.Equatable` interface.
- **Interfaces** -- `interface`, `implementation`, and `requires` replace
  `proto`, `impl`, and implicit guard dispatch. `Std.Comparable` replaces
  `Std.Ord`.
- **Canonical modules** -- stable owner-qualified identities, lexical versus
  qualified visibility, deterministic implementation loading, user preludes,
  propagated operator fixity, and incremental dependency invalidation.
- **Patterns and functions** -- one typed structural-pattern path for
  `match`, function heads, and `let`; complete multi-expression lambda bodies
  with expected-type inference.
- **Generation** -- structural `@derive` implementations are published like
  authored declarations; staged syntax, hygienic holes, quotation, splicing,
  `computed by`, and `Std.Syntax` support user macros.
- **Standard library** -- canonical `Std.Option` / `Std.Result`,
  `Std.Equivalent`, `Std.Equatable`, `Std.Comparable`, indexed vectors,
  typed optics and OTP, proof/reflection modules, and the expanded lazy
  iterator surface.
- **Tooling** -- editions and `cure migrate`, trust-ledger auditing,
  structured diagnostics, canonical multi-file builds, and an authoritative
  example runner. The root corpus currently has 40 passing examples with no
  skips or failures.

Optimization over validated dependent Core is future work. See
[`ROADMAP-0.34.md`](https://github.com/cure-lang/cure-lang/blob/main/ROADMAP-0.34.md)
and the Unreleased changelog for the full engineering inventory.

## Implemented: v0.33.0 -- Formalisation

The two branching constructs in the language -- `match` and `pickup`
-- graduate from "described in a tutorial" to "specified, normatively,
at version 1.0.0". v0.33.0 ships the contract, not a behaviour change:
the implementation already honours every clause of both specifications.
See the [v0.33.0 release post](/blog/cure-v0.33.0) for the full
narrative.

- **`docs/MATCH.md` -- *The `match` Construct, Language
  Specification, Version 1.0.0*.** EBNF grammar, the full pattern
  sub-grammar (literals, wildcards, silent bindings, tuples / lists /
  maps / records / ADT constructors / pin operator / binary segments,
  repeated variables, refutability, arbitrary nesting), static
  semantics (T-Match typing rule, Maranget-style exhaustiveness,
  reachability, scoping, refinement-context strengthening), dynamic
  semantics, big-step / small-step operational semantics, twenty-five
  formatter-conformance clauses, tail-position behaviour, lowering,
  constant folding, macro hygiene, IDE / language-server requirements,
  the diagnostic catalogue (`E004`, `E021`-`E025`, `E031`-`E034`, plus
  warnings / hints), the soundness proof sketch, an acceptance test
  corpus, and reserved future syntax (or-patterns, view patterns, range
  patterns, dependent patterns, as-patterns).
- **`docs/PICKUP.md` -- *The `pickup` Construct, Language
  Specification, Version 1.0.0*.** Mirrors `MATCH.md` in shape with
  the typing rules T-Pickup-Else / T-Pickup-Cons, the totality
  guarantee enforced by the mandatory terminator, source-order
  short-circuit semantics, refinement narrowing, twenty-five formatter
  clauses, the migration story for legacy `if` / `elif`
  (`cure rewrite if-to-pickup`, the new `E-IF-REMOVED` diagnostic),
  the diagnostic catalogue (`E-PICKUP-NO-ELSE`, `E-PICKUP-ELSE-NOT-LAST`,
  `E-PICKUP-MULTIPLE-ELSE`, `E-PICKUP-GUARD-TYPE`,
  `E-PICKUP-BRANCH-MISMATCH`, plus warnings / hints), reserved future
  syntax (`pickup as`, `pickup with`, `pickup async`, trailing
  `where`), and the soundness proof sketch.
- **HexDocs integration.** Both specifications added to `mix.exs`
  `docs.extras`, alongside `docs/PATTERNS.md`, `docs/BINARIES.md`, and
  the rest of the language references.
- **Cross-references.** `docs/LANGUAGE_SPEC.md` § "Pattern Matching"
  now opens with a normative pointer to `docs/MATCH.md`; a new
  `## Conditional Dispatch (`pickup`)` section opens with a pointer to
  `docs/PICKUP.md` and recapitulates the mental model in one paragraph.
- **Website.** `/match` grew leading and trailing notes pointing at
  the new normative documents; `/pickup` is new and mirrors the `/match`
  shape (grammar, totality, evaluation order, scoping, refinement
  narrowing, tail position, migration from `if`, formatter conventions,
  diagnostic catalogue, idioms).
- **No language-surface behaviour changes.** Code that compiled and
  ran under v0.32.0 compiles and runs identically under v0.33.0.

## Implemented: v0.32.0 -- Trust, Export, Recall, Narrate

Four independent features completing the sprint. The theme is closing
gaps that have been queued since the registry landed in v0.23.0.
See the [v0.32.0 release post](/blog/cure-v0.32.0) for the full
narrative.

- **Proof-carrying packages** (`Cure.Project.Proof`,
  `Cure.Project.Proof.Verifier`) -- When `cure publish` assembles a
  tarball the compiler is re-invoked in `proof_collect` mode.
  Every proof obligation discharged by the type-checker (equality
  witnesses, refinement predicates, SMT constraints, totality
  arguments) is serialised as a certificate and written into
  `<name>.cureproof` alongside the source files. Binary format:
  `"CUREPROOF\0" <> <<0x01>> <> gzip(term_to_binary([cert, ...])))`.
  `cure verify [path] [--strict]` replays each certificate through
  the offline verifier -- no source, no Z3 for equality / refinement
  proofs. `[publish] include_proofs = false` in `Cure.toml` opts out.
  New error codes: **E065 Proof File Missing**, **E066 Proof
  Verification Failed**, **E067 Proof Schema Incompatible**.
  New Mix task `mix cure.verify`. New doc `docs/PROOF_CARRYING.md`.
- **Cross-language ADT export** (`Cure.ExportTypes`,
  `Cure.ExportTypes.Protobuf`) -- `cure export-types --target protobuf`
  translates Cure `rec`, `type`, and `enum` declarations to proto3
  `.proto` files. Complete type mapping: `Int->int64`,
  `List(T)->repeated T`, `Option(T)->optional T`, pure-enum ADTs to
  proto3 `enum`, payload-bearing ADTs to wrapper `message` +
  `oneof value` blocks + one synthetic payload message per variant.
  Refinements and dependent types emit a `bytes` field with a comment
  and raise **E068 Export Type Unmappable** (warning, not hard error).
  Field names converted from `camelCase` to `snake_case`; field
  numbers by declaration order. `--out`, `--dry-run`, `--verbose`
  flags. New Mix task `mix cure.export_types`. New doc
  `docs/EXPORT_TYPES.md`.
- **`cure snap`** (`Cure.REPL.Snap`) -- REPL session snapshots.
  `:snap save [path]`, `:snap load <path>`, `:snap list [dir]` as
  REPL meta-commands. Binary format:
  `"CURESNAP\0" <> <<0x01>> <> gzip(term_to_binary(snap_map))`.
  Captures: session entries (fn/type/rec/proto/impl/proof),
  up to 500 history lines, use imports, holes, stdlib mode, theme,
  editing mode, loaded-file paths. Load merges (last-writer-wins for
  defs, union for uses, prepend for history); E070 warning for each
  saved path no longer on disk. New Mix task `mix cure.snap save|
  load|list`. New doc `docs/SNAP.md`. New error codes: **E069 Snap
  Schema Incompatible**, **E070 Snap Module Missing**.
- **`cure story`** (`Cure.Story`, `Cure.Story.Outline`,
  `Cure.Story.Narrator`) -- narrative `STORY.md` generator. Parses
  every `.cure` file under `lib/`, classifies AST containers into a
  five-layer outline (app -> supervisor -> actor -> fsm -> types), and
  emits template-driven prose for each level. `--diagrams` embeds
  Mermaid `stateDiagram-v2` blocks for each FSM. `--format html`
  wraps the output in a minimal HTML shell. `--stdout` prints to
  stdout without writing a file. Project name read from `Cure.toml`.
  New Mix task `mix cure.story`. New doc `docs/STORY.md`.
- **Cross-cutting**: six new error codes E065--E070 added to
  `Cure.Compiler.Errors`; all four commands wired into `Cure.CLI`
  and `cure help`; `mix.exs` version 0.32.0; four new doc pages
  registered in Hex extras.

## Implemented: v0.31.0 -- Profile & Draw

This release added profile-data plumbing and terminal diagrams to the classic
compiler. That optimizer and its PGO stack were later deleted with the classic
pipeline; the profile format remains historical design material.
- **Profile-Guided Optimisation** (`Cure.PGO`, `Cure.PGO.Profile`,
  `Cure.PGO.Recorder`) -- runtime-profile capture + compile-time
  consumption. `Cure.PGO.Recorder` is a `GenServer`-backed ETS
  counter table with `tick/1`, `tick_with_us/2`, `tick_branch/2`,
  `tick_smt/3`, and `flush/1` operations. `Cure.PGO.Profile`
  serialises one record per module to `_build/cure/pgo/<mod>.profile`
  via compressed `term_to_binary`. `Cure.PGO.load/2` partitions
  entries into hot (top 80% of total cost) and cold sets, with
  stale-profile detection via `:erlang.phash2/1` of the live
  `function_def` meta. The inliner accepts `:pgo` + `:module` opts:
  hot fns get `ast_size <= 12`, cold get `<= 2`, default stays at
  `<= 5`. `Cure.SMT.Solver.check_sat/3` accepts a `:hot | :cold |
  :default` budget hint -- hot doubles the Z3 timeout and emits
  `(set-option :smt.arith.solver 6)`; cold halves the timeout and
  conservatively returns `:sat` on `:unknown`. PGO is **strictly
  opt-in**: never auto-discovered, must be requested via
  `cure compile --pgo`.
- **`cure profile` subcommand** -- `cure profile run`,
  `cure profile show [--top N]`, `cure profile clear`. Plus
  `cure run --record-profile [--profile-dir DIR]` flushes profiles
  on exit.
- **`cure draw <path.cure> [fsm|sup|app]`** -- new ASCII / Unicode
  box-drawing renderer (`Cure.Doc.Ascii`) that reuses the FSM /
  supervisor / application traversals from `Cure.Doc.Mermaid`.
  States render as `▢` / `▣`, transitions as `──[event]──>` with
  `!`/`?` event suffixes, supervisor children as a `├──`/`└──`
  vertical tree, applications as a panel summarising vsn, root,
  and declared `applications`.
- **New docs:** `docs/PGO.md`, retained as historical optimizer design.

Deferred to v0.33.0 and beyond:
- **Cure-native notebook** (v0.33.0 target) -- first-class `.cnb`
  format evaluated by a Livebook-style runner. Groundwork in place:
  `Cure.Doc.Mermaid`, `Cure.Doc.HtmlGenerator`, `Cure.REPL` pipeline.
- **Typed hot code upgrades** (`cure release --upgrade-from`,
  `@migration`, E057/E058) -- the appup/relup machinery is large and
  fragile; it continues to get its own cycle.
- **Automatic PGO instrumentation** -- inject
  `Cure.PGO.Recorder.tick/1` at every compiled function's entry.
  v0.31.0 ships the data layer; users who want PGO today drive ticks
  manually or via `Cure.Profiler`.
- **`cure export-types --target typescript` and `--target rust`** --
  the Protobuf backend (v0.32.0) proved the extractor API; additional
  emitters are additive.

## Implemented: v0.30.0 -- John

Every surface gets a new `john` button. Named in tribute to **John
Carbajal**, whose knack for spotting the one line on a dashboard
that actually mattered inspired the release. See the
[v0.30.0 release post](/blog/cure-v0.30.0) for the full narrative.

- **`mix cure.john`, `cure john`, `:john`** -- three surfaces,
  one implementation. Each prints a panoramic Markdown-to-ANSI
  diagnostic covering Cure application state, BEAM / OTP stats,
  system info, tooling, the current Cure project (if any),
  runtime snapshot, doctor severity counts, and tails of the most
  recent log files.
- **`Cure.John`** -- `collect/1` returns a plain Elixir map
  (serialisable, assertable); `render/2` emits CommonMark;
  `run/1` collect-renders-writes. All three are testable in
  isolation.
- **Marcli fallback** -- `run/1` renders through `Marcli.render/2`
  when its MDEx NIF can load, and falls back to the pure-Elixir
  `Cure.REPL.Markdown` renderer inside the escript (where the
  NIF path is not loadable).
- **CLI and REPL integration** -- `cure help`, `Cure.CLI`'s
  `known_commands` list, and the REPL's `known_commands` list
  all advertise `john` / `:john`, so a typo surfaces a
  Levenshtein "Did you mean?" suggestion.
- **Docs** -- new `docs/JOHN.md` on-disk reference (added to
  the Hex docs extras), `:john` added to `docs/REPL.md` and the
  site REPL reference, new v0.30.0 section in the Tooling page,
  and a release blog post.

## Implemented: v0.29.0 -- Make Documentation Great

The documentation release. `cure doc`, the REPL, the stdlib, the
website, and the editor plugins all pulled up to the same bar. See
the [v0.29.0 release post](/blog/cure-v0.29.0) for the full
narrative.

- **`cure doc` two-pane layout** -- ExDoc-like HTML site driven by a
  new `[doc]` table in `Cure.toml`
  (`main`, `title`, `extras`, `logo`, `source_url`, `source_ref`,
  plus `[doc.groups_for_modules]`). Anchored entries for every
  public function / type / protocol; `/`-focusable sidebar filter;
  `prefers-color-scheme` theme toggle. `--title`, `--main`,
  `--extras` CLI flags.
- **`Cure.Doc.Markdown`** -- NIF-free Markdown-to-HTML pipeline
  (`Md.generate/1` + Makeup highlighting for `cure` / `elixir` /
  `erlang` fences + `{{cure_version}}` / `{{cure_vversion}}`
  placeholder interpolation). Safe inside the escript (where the
  `marcli` / `MDEx` NIF path is not loadable).
- **Stdlib Examples blocks** -- every module under `lib/std/` now
  carries a module-level `## Examples` block; four high-traffic
  `Std.Core` functions (`compose`, `map_ok`, `and_then`,
  `map_option`) carry per-function examples. All round-trip through
  `mix cure.compile_stdlib`.
- **`/stdlib` site integration** -- `CureSite.Stdlib` bundles every
  `Std.*` module at site-compile time; `CureSiteWeb.StdlibController`
  serves `/stdlib` (index) and `/stdlib/:module` (single-module
  page) with a DaisyUI-styled two-pane layout and a GitHub
  "View source" link. `/standard-library` redirects to `/stdlib`.
- **REPL Markdown renderer upgrade** -- `Cure.REPL.Markdown`
  gains a block-aware parser (fenced code, lists, blockquotes,
  indented code, inline links, horizontal rules, paragraph breaks)
  while staying NIF-free.
- **Parser fix** -- consecutive `##` doc-comment blocks separated
  by blank lines are now merged into a single docstring with a
  paragraph break (`collect_all_doc_comments/1,2`).
- **Editor and highlighter alignment** -- `highlightjs-cure/`
  ships a highlight.js language description plus a minified
  bundle; `vicure/` and `vscode-cure/` are re-aligned with the
  Cure 0.28.2 grammar (syntax, indent, ftplugin, ftdetect, tests,
  README / CHANGELOG).
- **REPL session and signatures** -- `Cure.REPL.Session`
  accumulates top-level declarations (`fn`, `type`, `rec`, `proto`,
  `impl`, `proof`); `Cure.Types.Checker.infer_expr/2` gains an
  `:extra_bindings` option so session fns show their real type in
  `:t` and `:effects` (promoted from v0.28.1 / v0.28.2).
- **`docs/DOC.md`** -- authoritative on-disk reference for the
  whole doc pipeline; `docs/TUTORIAL.md` Chapter 13 "Documenting
  your modules" walks through docstrings, Examples, `[doc]`
  configuration, and running `cure doc`.

## Implemented: v0.28.0 -- Talk Back

Feedback loops closed at every level. See the [v0.28.0 release post](/blog/cure-v0.28.0)
for the full narrative.

- **Checker bug fix** -- `infer_and_unify_args` silently swallowed
  lambda body type errors, returning `List(U)` instead of a type
  error for ill-typed polymorphic lambdas. Fixed via error accumulator.
  `Type.numeric?` extended to handle named type aliases and type
  variables without false positives.
- **Parser error recovery (E063)** -- `synchronize_to_statement/1`
  after every error-producing expression; one pass, all errors.
- **"Did you mean?"** -- Levenshtein suggestions at every
  name-resolution failure: unbound variables, record fields, CLI
  subcommands, REPL `:use`, REPL meta-commands.
- **`cure fmt --dry-run`** -- colour-annotated unified diff without
  touching disk; exits 1 when files would change.
- **`cure bless`** -- Socratic type-error assistant with `[y/n/s]`
  interactive fix prompting. `Cure.Bless`, `Cure.Bless.Advisor`,
  `mix cure.bless`, REPL `:bless`.
- **`@record` + `cure replay`** -- `@record` decorator opts any FSM
  into `Cure.Observe.Journal`. `cure replay` loads `.journal` files
  and replays event sequences with optional `--step` mode.
- **Playground v2** -- live type-check panel + sandboxed evaluator
  (`CureSiteWeb.Eval`, 64 MB heap cap, 2 s kill timer).
- **1503 tests.** E063 added to the error catalog.

## Implemented: v0.27.0 -- See Your System Breathe

Observability and verification layered on top of the v0.26.0 OTP
application surface. See the [v0.27.0 release post](/blog/cure-v0.27.0)
for the full narrative.

- **`Cure.OTel`** -- OpenTelemetry-compatible span bridge. Every
  pipeline event becomes a span; `inject_ctx`/`extract_ctx` carry
  trace context across process boundaries; `MemoryExporter` for tests.
- **`cure top`** -- snapshot observer for supervisors, actors, and FSMs.
- **`cure trace`** -- typed `:dbg` wrapper with BEAM signature lookup.
- **`Cure.Temporal`** -- LTL formula DSL + bounded model checker over
  FSM transition graphs. `E059 Temporal Property Violated` with a
  minimal counterexample trace.
- **`Cure.Protocol`** -- session types between actor roles, structural
  verifier, projection to FSM traces. `E056 Protocol Violation`.
- **`cure synth`** -- typed-hole synthesis via depth-budgeted
  enumeration + stdlib catalogue. `E061 Synthesis Budget Exhausted`.
- **New stdlib** -- `Std.Time` (14 fns), `Std.Regex` (7 fns, `E060`),
  `Std.CRDT` (5 CRDTs × 4 ops).
- **`Cure.Doc.Mermaid`** -- FSM / sup / app diagrams in `cure doc`.
- **OSC 8 hyperlinks** -- `Cure.Term.Hyperlink` wraps error file paths
  so they are clickable in WezTerm, Kitty, iTerm2, VTE, and Warp.
- **LiveView Playground v1** -- syntax-highlighted two-pane editor.
- **`examples/cure_atelier/`** -- showcase project exercising every
  v0.27.0 surface.
- **1451 tests.** 5 new error codes (E056--E062).

## Implemented: v0.26.0 -- Applications and Releases
v0.26.0 promotes the v0.25.0 supervision surface into a full OTP
application lifecycle. A new `app` container declares the project's
OTP application directly in Cure source, cross-checked against
`Cure.toml`'s new `[application]` and `[release]` tables. The same
compiler cycle emits the `<name>.app` resource file and a
`:"Cure.App.<Name>"` `Application`-behaviour module; a new
`cure release` subcommand (also available as `mix cure.release`)
packages the whole thing as a bootable BEAM release. See the
dedicated [Applications reference](/applications) for the full tour.
### `app` container
- `app Name` containers declare an OTP application with `vsn`,
  `description`, `root`, `applications`, `included_applications`,
  `registered`, `env` assignments, plus `on_start` / `on_stop` /
  `on_phase :name` lifecycle clauses. The clause grammar is shared
  with `actor` and `sup` (pattern tuple + optional `when` guard +
  body).
- `app` is a *contextual* soft keyword, treated the same way as
  `sup`: the lexer keeps it as an identifier so programs that use
  `app` as a field or variable name keep compiling; the parser
  dispatches `app <Name>` to the application-container parser only
  at statement-prefix position.
- `Cure.App.Verifier` enforces exactly one `app` container per
  project, matches its name against `[application].name` in
  `Cure.toml` (both sides normalised through `Macro.underscore/1`),
  cross-checks start-phase names, and validates that `root = ...`
  resolves to a known module atom.
- `Cure.App.Compiler` emits a loaded `Application`-behaviour module
  via `Code.compile_string/2`; the codegen dispatcher returns
  `{:ok, {:app, module()}}`. When `--output-dir` is given the
  bytecode and an OTP `<name>.app` resource file are persisted
  alongside every other Cure module.
### Release builder
- `Cure.Release` assembles a bootable BEAM release under
  `_build/cure/rel/<name>/`:
  `lib/<app>-<vsn>/ebin/*.{beam,app}`, `releases/<vsn>/<name>.rel`,
  `releases/<vsn>/start.boot`, `releases/<vsn>/start.script`,
  `releases/<vsn>/sys.config`, `releases/<vsn>/vm.args`, and a
  POSIX `bin/<name>` runner script.
- `--include-erts` (or `[release].include_erts = true`) bundles the
  running ERTS into the release directory.
- `Mix.Tasks.Cure.Release` exposes the subcommand as
  `mix cure.release`.
### `Cure.toml` extensions
- `[application]` -- `name`, `vsn`, `description`, `applications`,
  `included_applications`, `registered`, `start_phases`, plus nested
  `[application.env]`. `name` is authoritative for the emitted
  `<name>.app`; `applications` is merged with the container's own
  list; `start_phases` must agree with the container's `on_phase`
  clauses.
- `[release]` -- `name`, `vsn`, `include_erts`, `applications`,
  `vm_args`, `sys_config`. `Cure.Release` threads these into the
  release assembly.
### Standard library additions
- **`Std.App`** (9 functions) -- `ensure_all_started/1`,
  `start/1`, `stop/1`, `get_env/2`, `get_env/3`, `put_env/3`,
  `which_applications/0`, `loaded_applications/0`,
  `start_phase/3`. Thin wrappers over `:application` with
  plain-atom return shapes.
### Error catalog
Five new codes `E051` -- `E055`:
- `E051 Duplicate Application` -- more than one `app` container in
  a project (or a name mismatch with `[application].name`).
- `E052 Missing Application` -- `cure release` invoked with no
  `app` declared.
- `E053 Start Phase Mismatch` -- TOML and container disagree on
  phase names.
- `E054 Unresolved Root Supervisor` -- `root = ...` does not
  resolve to a known module reference.
- `E055 Release Build Failed` -- wraps `:systools.make_script/2`
  or release-write I/O errors.
### Example
- `examples/cure_forge/` -- fully-fledged OTP application showcase.
  An `app CureForge` container with `vsn`, `description`, `env`,
  `applications`, `on_start`, `on_stop`, and a `:warm_cache` start
  phase; a `sup Forge.Root` supervision tree; and four actors
  (metrics, logger, queue, pool) cooperating through the Melquiades
  Operator `<-|`.
### Documentation
- `docs/APP.md` -- full on-disk reference for the `app` container,
  `Cure.toml` `[application]` / `[release]` sections, the
  `cure release` subcommand, `Std.App`, and error codes.
- `docs/TUTORIAL.md` -- new Chapter 13 "Applications".
- `docs/LANGUAGE_SPEC.md` -- new "Applications (v0.26.0)" section.
- `docs/STDLIB.md` -- new `Std.App` entry.
- `site/priv/pages/applications.md` -- user-facing reference on the
  Cure website.
## Implemented: v0.25.0 -- Typed Supervision Trees
v0.25.0 turns the language into a first-class environment for
writing OTP-style supervision trees on top of the BEAM. Four pieces
land together: the Melquiades Operator `<-|` for typed sends, an
`actor` container that compiles to a loaded `GenServer` module, a
`sup` container that compiles to a verified `Supervisor` behaviour
module, and a new stdlib surface exposing the runtime from Cure
source. See the dedicated [Actors reference](/actors) for the full
tour.
### Melquiades Operator
- `pid <-| message` (ASCII) and `pid ✉ message` (unicode U+2709)
  are interchangeable spellings of a typed send. Both lower to
  Erlang's `!` operator in abstract form, return the sent message,
  and never raise for a dead receiver.
- Non-associative; binds one notch below `|>` so pipelines feed into
  sends without extra parentheses.
- `send target, msg` remains as a synonymous statement form for
  backward compatibility with `Std.Fsm` clients.
- Printer preserves the author's spelling through a
  `:melquiades_form` meta key; round-trips `<-|`, `✉`, and the
  keyword form faithfully.
### Typed primitives
- **`Pid(Inbox)`** -- a typed pid. Bare `Pid` elaborates to
  `{:pid, :any}`, the top of the covariant family, so existing FFI
  code remains assignable from narrower typed pids without friction.
- **`Ref`** -- new primitive type for monitor references.
- `Cure.Types.Checker.do_infer/2` grows a dedicated clause for
  `{:send, ...}` that unifies the message type against the receiver's
  inbox and emits `E046 Inbox Mismatch` on conflict.
- `Cure.Types.Effects` attracts `:state` for every send.
### Actors (`actor` container)
- `actor Name with <init>` declares a typed process. Lifecycle hooks
  `on_start`, `on_message`, `on_stop` reuse the FSM callback-clause
  machinery (pattern tuple, optional `when` guard, body).
- `Cure.Actor.Compiler` emits a loaded `GenServer` module via
  `Code.compile_string/2`; the codegen dispatcher returns
  `{:ok, {:actor, module()}}`.
- `Cure.Actor.Runtime` tracks spawned actors in an ETS registry,
  monitors each pid, and cleans up on `DOWN`. Supervised by
  `Cure.Supervisor` alongside `Cure.FSM.Runtime`.
- `Cure.Actor.State` struct carries `caller`, `meta`, `payload`;
  `notify/1` inside any clause body resolves the registered caller
  via the process dictionary.
- `Cure.Actor.Builtins` bridges `Std.Actor` to the runtime.
### Supervisors (`sup` container)
- `sup Name` declares a supervisor module with inline
  `strategy`, `intensity`, `period` settings plus a `children` block
  whose entries are `Module as id (restart: ..., shutdown: ...)`.
- Child module resolution: dotted paths are used verbatim; bare names
  resolve to `Cure.Actor.<Name>` (worker default) or
  `Cure.Sup.<Name>` (when prefixed with `sup <Name> as id`).
- `Cure.Sup.Verifier` rejects invalid strategies, non-positive
  periods, duplicate child ids, unknown restart / shutdown values,
  and trivial self-reference cycles. Emits `:sup_verifier` pipeline
  events.
- `Cure.Sup.Compiler` emits a `Supervisor`-behaviour module via
  `Code.compile_string/2`; the codegen dispatcher returns
  `{:ok, {:supervisor, module()}}`.
- `Cure.Sup.Runtime` wraps the compiled module with a lazy ETS
  registry (`start/1,2`, `stop/1`, `lookup/1`, `which_children/1`,
  `count_children/1`, `list/0`).
- `sup` is a *contextual* keyword -- it stays an identifier at the
  lexer level so programs using `sup` as a field or local variable
  keep compiling; the parser only dispatches `sup <Name>` to
  `parse_supervisor/1` at statement-prefix position when followed by
  an identifier.
### Stdlib additions
- **`Std.Actor`** -- `spawn/1`, `spawn_with_payload/2`,
  `spawn_named/2`, `stop/1`, `send/2`, `get_state/1`, `is_alive/1`,
  `lookup/1`.
- **`Std.Process`** -- `link/1`, `unlink/1`, `monitor/1`,
  `demonitor/1`, `trap_exit/1`, `exit/2`, `self/0`, `is_alive/1`.
  Most entries are direct `:erlang` BIF calls; `monitor/1` and
  `trap_exit/1` go through thin wrappers in `Cure.Process.Builtins`
  so the Cure signatures read idiomatically.
- **`Std.Supervisor`** -- `start/1`, `start_with/2`, `stop/1`,
  `which_children/1`, `count_children/1`, `lookup/1`, `list/0`.
### Error catalog
Six new codes `E045` -- `E050`: Untyped Send, Inbox Mismatch,
Supervisor Unknown Child, Supervisor Cycle, Actor Handler
Non-Exhaustive, Invalid Supervisor Strategy. Run `cure explain <code>`
for the full text.
### Example
- `examples/cure_colony/` -- a worker actor, an echo actor, and a
  `sup Colony` supervisor wiring them under `:one_for_one`. Exercises
  `actor`, `sup`, and the Melquiades Operator end to end.
### Numbers
- 1310 tests pass (up from 1295; 3 doctests + 1307 tests);
  `mix credo --strict`: 0 issues across 200 source files;
  `mix cure.check.stdlib`: 30/30 (three new stdlib modules).
## Implemented: v0.24.0 -- The REPL You Deserve
v0.24.0 is deliberately single-purpose. The compiler surface is
untouched; every change lands on the interactive read-eval-print
side. The legacy `IO.gets` loop (shipped in v0.15.0, barely touched
since) is replaced wholesale by a raw-mode line editor with live
syntax highlighting, persistent history, incremental reverse search,
Tab completion, and a minimal vi mode. See the dedicated
[REPL reference](/repl) for the full key-bindings table and
meta-command list.
### Raw-mode terminal
- **`Cure.REPL.Terminal`** puts stdin into cbreak/no-echo mode via
  `stty`, restores it on every exit path (normal `:quit`, EOF on an
  empty buffer, `Ctrl+C` on a non-empty buffer, uncaught exception,
  SIGINT / SIGTERM), and decodes raw byte streams into high-level
  key events: arrows, `Home` / `End` / `Delete` / `PgUp` / `PgDn`,
  every `Ctrl+<letter>` and `Alt+<char>` shortcut, `Ctrl+Arrow` for
  word-wise movement, `F1`-`F12`, and bracketed paste.
- Non-tty stdin (CI, pipes, `|` into `cure repl`, `TERM=dumb`)
  short-circuits to the legacy `IO.gets` loop so test automation
  continues to work unchanged.
### Pure-function line editor
- **`Cure.REPL.LineEditor`** is a stateless buffer: every key event
  produces a new `%LineEditor{}` struct. Emacs-mode menu covers one-
  grapheme and one-word cursor movement, begin / end of line,
  backspace / delete, `Ctrl+K` / `Ctrl+U` / `Ctrl+W` / `Alt+D` kill
  variants, yank (`Ctrl+Y`) and kill-ring rotation (`Alt+Y`),
  transpose chars / words, upcase / downcase / capitalise word,
  undo / redo (`Ctrl+_` / `Alt+_`), and a minimal vi normal mode
  (`h` / `j` / `k` / `l`, `w` / `b` / `e`, `0` / `^` / `$`,
  `i` / `a` / `I` / `A`, `x`, `D`, `C`, `u`).
### History and reverse search
- **`Cure.REPL.History`** persists entries to `~/.cure_history` via
  atomic write-and-rename. Consecutive duplicates are deduplicated,
  the file is capped at 10,000 entries, and `Up` / `Down` step
  through history while preserving the current draft.
- **`Cure.REPL.Search`** implements `Ctrl+R` / `Ctrl+S` incremental
  reverse and forward search with an inverse-video status line and
  accept-and-edit semantics (`Tab` / arrow keys pull the match into
  the main buffer for further editing).
### Live syntax highlighting
- **`Cure.REPL.Highlight`** pipes every buffer state through
  `Makeup.Lexers.CureLexer` and `Marcli.Formatter` for ANSI syntax
  highlighting on every keystroke. Cached by buffer hash so repeated
  redraws do not re-tokenise.
- **`Cure.REPL.Theme`** ships `:dark` (default), `:light`, and
  `:mono` presets. `:mono` is forced automatically when `NO_COLOR`
  is set, when stdout is not a tty, or when `TERM=dumb`. Toggle at
  runtime with `:theme dark|light|mono` or `:color on|off`.
### Tab completion
- **`Cure.REPL.Completer`** handles four categories in one pass:
  meta-commands, file paths (inside `:load` / `:save` / `:edit`),
  loaded modules (inside `:use` / `:doc`), and theme / mode / colour
  argument literals plus Cure keywords everywhere else.
### Meta-commands
All existing meta-commands (`:t`, `:type`, `:effects`, `:load`,
`:reload`, `:use`, `:holes`, `:env`, `:reset`, `:fmt`, `:help`,
`:quit`) are preserved. v0.24.0 adds `:history [n]`, `:search term`,
`:clear`, `:save path`, `:edit`, `:time expr`, `:bench expr [n]`,
`:ast expr`, `:theme dark|light|mono`, `:mode emacs|vi`, and
`:color on|off`. `:help` output is rendered via `Marcli.render/2`
as ANSI-styled Markdown.
### Dependencies
- `{:marcli, "~> 0.3"}` -- Markdown-to-ANSI renderer and Makeup
  token-to-ANSI formatter.
- `{:makeup, "~> 1.2"}` -- explicit so `Makeup.Registry` is
  available at runtime.
- `{:makeup_cure, "~> 0.1"}` -- Cure language lexer for Makeup.
### Documentation
- New [`/repl`](/repl) user-facing reference page on the Cure
  website alongside the existing
  [docs/REPL.md](https://github.com/cure-lang/cure-lang/blob/main/docs/REPL.md)
  on-disk contract.
## Implemented: v0.23.0 -- Packaging, Proof, and Polish
v0.23.0 ships the remote package-registry story that was
rescheduled through three releases. It lands alongside a broad
ergonomics upgrade: property-based shrinking, two new stdlib
modules, a `cure doctor` diagnostic, a `cure fix` project-wide
rewriter, a `:telemetry` bridge, `cure test --cover` coverage
reporting, and the `cure_brainloop` showcase example.
### Remote package registry
- `Cure.Project.Registry` -- read-only HTTP client over OTP's
  `:httpc`. Content-addressed, disk-cached, hash-verified responses.
  New `:registry` pipeline stage (`:fetch_start`, `:fetch_ok`,
  `:fetch_failed`, `:cache_hit`, `:hash_mismatch`).
- `Cure.Project.Lock` -- `Cure.lock` reader / writer with
  `resolve_with_lock/2`. When every top-level constraint still
  accepts the locked version, `cure deps` skips the backtracker and
  the network entirely.
- `Cure.Project.resolve_deps/1` extended: dependencies without
  `path` or `git` are registry dependencies. Tarballs are fetched,
  hash-checked, signature-verified, unpacked under
  `_build/deps/<name>-<version>/`, and added to the code path.
- `Cure.Project.Signing` -- Ed25519 key management on top of OTP
  `:crypto`. Keys under `~/.cure/keys/` with tight file perms.
  Signs `name || NUL || version || NUL || sha256(tarball)`.
- `Cure.Project.Transparency` -- Rekor-style append-only log
  verifier. Canonicalises entries by key-sorted JSON, validates the
  Merkle-like hash chain, degrades gracefully to
  `{:ok, :unverified}` when `/log` is unreachable. Promotable to a
  hard failure with `config :cure, strict_transparency: true`.
- `Cure.Project.Publisher` -- assembles the package tarball,
  signs, uploads. `build_hex_tarball/1` emits a Hex-compatible
  tarball (`VERSION` / `CHECKSUM` / `metadata.config` /
  `contents.tar.gz`) for cross-publishing via
  `mix hex.publish package --replace`.
### CLI surface
- `cure publish`, `cure publish --dry-run`, `cure publish --hex`.
- `cure search <query>`, `cure info <name>[:version]`.
- `cure keys generate <handle>`, `cure keys list`.
- `cure doctor` -- environment / project / source health report,
  suitable as a CI gate.
- `cure fix [--dry-run]` -- project-wide safe rewrites
  (line endings, trailing whitespace, tabs -> two spaces,
  blank-line runs, trailing newline).
- `cure test --cover` -- runs the self-hosted test suite under
  `:cover`, emits an HTML index under `_build/cure/cover/`.
### Standard library (25 -> 27)
- **`Std.Json`** (`lib/std/json.cure`) -- JSON encoder + decoder
  backed by the `Value` ADT
  (`Null | Bool | Num | Str | Arr | Obj`). Companion to the
  v0.21.0 `@derive(JSON)` target.
- **`Std.Http`** (`lib/std/http.cure`) -- `get/1`, `get/2` (with
  headers), `post/3`, `head/1` returning
  `Result(Response, HttpError)`. The registry client dogfoods it.
- **`Std.Gen.shrink_int/1`**, **`shrink_list/1`**, **`shrink/1`** --
  shrinking primitives.
- **`Std.Test.forall_shrunk/3`** and
  **`forall_shrunk_default/2`** -- shrinking-aware property runner.
  Raises `{:property_failed_with_shrunk, minimal_value}` on the
  minimised counterexample instead of the first draw.
### Infrastructure
- **`Cure.Telemetry`** -- subscribes to every stage of
  `Cure.Pipeline.Events` and re-emits events under
  `[:cure, :pipeline, <stage>, <event_type>]`. Production
  deployments can feed compilation and Z3 latency into an existing
  observability stack. `:telemetry` is declared optional in
  `mix.exs`; missing the library silently turns the bridge into a
  no-op.
- **`Cure.Doctor`** -- structured diagnostic (Elixir / OTP / Z3 /
  registry URL / telemetry / project / source health). Non-zero
  exit on any warning or error finding.
- **`Cure.Fix`** -- project-wide safe rewrites.
- **`Cure.Cover`** -- `:cover` harness with HTML report generation.
### Showcase example
- `examples/cure_brainloop/` -- the top-pick showcase from the
  internal `ideas_for_cure_apps.md`. Toy expression-language
  interpreter with a REPL FSM. Exercises ADTs, records, refinement
  types, protocols, effects, FSM callback mode, OTP interop, FFI,
  and the new `Std.Json` module in one self-contained codebase.
  Ships with an ExUnit suite covering lexer, parser, evaluator,
  and environment semantics.
### Error catalog
Five new codes `E038` -- `E042`: Registry Fetch Failed, Registry
Hash Mismatch, Registry Package Not Found, Registry Signature
Invalid, Transparency Log Unreachable.
### Documentation
- `docs/PACKAGE_REGISTRY.md` rewritten from a v0.17.0-era design
  document into the authoritative shipped contract.
- `docs/PUBLISHING.md` -- end-to-end walkthrough for publishing a
  Cure package, including Hex cross-publishing and strict
  transparency-verification mode.
### Numbers
- 1144 tests pass (up from 1114; 3 doctests + 1141 tests);
  `mix credo --strict`: 0 issues across 167 source files;
  `mix cure.check.stdlib`: 27/27; `mix cure.check.examples`:
  44/44.

## Implemented: v0.22.0 -- Loose Ends
v0.22.0 closes the three language-surface gaps that v0.20.0 /
v0.21.0 deliberately left open: multi-statement lambda bodies,
binary comprehension generators, and full byte-size refinement
propagation through `rest::binary` tails. The v0.21.0 "Unreleased"
first-class FSM overhaul also graduates into a shipped release.
### Multi-statement lambda bodies
- `Cure.Compiler.Parser.parse_lambda_body/2` routes the body
  through a new `parse_lambda_block_body/2` dispatcher. Indented
  and single-expression bodies keep their v0.19.0 semantics; two
  new shapes land for argument positions where the lexer
  suppresses newlines:
```text
map(xs, fn(x) -> { let y = x + 1; y + 2 })
map(xs, fn(x) -> let y = x + 1; y + 2; end)
```
- Both shapes emit `{:block, [block_shape: :brace | :end, ...], exprs}`,
  reusing the existing codegen and checker paths. The Printer and
  algebra formatter round-trip the author's chosen shape.
- `end` is now a reserved keyword. Cure's stdlib and example
  programs do not use it as an identifier; third-party code that
  does must rename.
### Binary comprehension generators
- `parse_generator_or_filter/1` dispatches on `:binary_open` and
  delegates to `parse_binary_generator/1`. Segments inside the
  generator are parsed at binding power 42 so the trailing `<-`
  arrow is not mis-tokenised as a less-than comparison.
- `Cure.Compiler.Codegen.compile_comprehension/3` lowers the new
  `:binary_generator` qualifier to Erlang's `b_generate` form
  inside the existing `:lc` comprehension:
```text
[byte for <<byte <- "abc">>]       # [97, 98, 99]
[word for <<word::16 <- buf>>]     # 16-bit words
[ch   for <<ch::utf8 <- text>>]    # UTF-8 code points
```
- `Cure.Types.Checker.do_infer/2` on `:comprehension` now binds
  every qualifier's pattern variables into the body's environment
  via `bind_pattern_vars/3`.
### `byte_size` arithmetic refinements
- `Cure.SMT.Translator` speaks `byte_size/1` as an uninterpreted
  `(Int) -> Int` function. Queries that reference `byte_size`
  prepend `(declare-fun byte_size (Int) Int)` and switch to the
  `QF_UFLIA` logic automatically.
- `Cure.Types.PatternRefinement.narrow/2` rewrites its binary-
  segment branch. Trailing `rest::binary`/`rest::bytes`/
  `rest::bitstring` tails receive
  `{rest: Bitstring | byte_size(rest) == byte_size(scrutinee) - sum}`
  where the sum is the byte-aligned count of preceding segments.
  When a segment's size cannot be linearised the tail degrades to
  plain `Bitstring` and the pipeline emits a `:refinement_ignored`
  event under code `E037`.
### Error catalog
Three new codes `E035`-`E037` (Lambda Block Unterminated, Binary
Comprehension Source Not Bitstring, Binary Segment Size Non-Linear).
### First-class FSM handling
The v0.21.0 "Unreleased" block that described the `%Cure.FSM.State{}`
rewrite of callback-mode FSMs is promoted to a shipped surface.
`start_link/1` accepts three init shapes, `on_transition` clauses
receive the struct as their 4th argument, and `@notify_transitions`
/ `@initial` / `@auto_caller` annotations carry first-class payload
semantics. Simple-mode (`gen_statem`) FSMs are entirely unchanged.
### Numbers
- 1114 tests pass (up from 1078; 3 doctests + 1111 tests);
  `mix credo --strict`: 0 issues across 142 source files;
  `mix cure.check.stdlib`: 25/25; `mix cure.check.examples`:
  44/44 (up from 40/40).
- 3 new example files (`lambda_block.cure`,
  `binary_comprehension.cure`, `byte_size_refinement.cure`).
### Deferred to v0.23.0
Remote package-registry index service, publication signing, and
Hex.pm cross-publishing -- the `Cure.Project.Registry` HTTP
client against the read-only index protocol, Ed25519 archive
signing, and the `cure publish --hex` export path are all
rescheduled for v0.23.0.

## Implemented: v0.21.0 -- Through the Segments

The v0.21.0 release turns the v0.20.0 AST scaffolding into
user-visible features and clears three language gaps that surfaced
during the v0.20.0 cycle. The headline is full Erlang-style
destructuring of binaries in `match`, multi-clause function heads,
and `let` bindings, with a dedicated exhaustiveness pass that
surfaces under code `E031`.

### Binary destructuring

- `Cure.Types.Checker.bind_pattern_vars/3` grows a `:bin_segment`
  clause. Every `<<...>>` pattern in `match`, function heads, and
  `let` introduces its inner variables with the type implied by the
  segment specifier: `integer`/`size(n)` -> `Int`, `float` ->
  `Float`, `utf8`/`utf16`/`utf32` -> `Char`,
  `binary`/`bytes`/`bitstring`/`bits` -> `Bitstring`.
- `Cure.Types.PatternChecker.check_binary_exhaustiveness/2` --
  dedicated Maranget-lite coverage analysis over a sequence of
  binary-pattern arms. A top-level wildcard, or the combination of
  an empty-binary arm and an open-ended tail arm, covers the
  scrutinee; otherwise a concrete witness (`"<<>>"` or
  `"<<_, _rest::binary>>"`) is reported under code `E031`.
- `Cure.Types.PatternRefinement.narrow/2` gets a binary-literal
  branch that narrows the scrutinee through the segments.

### In-place `let` destructuring

- `let` bindings reuse the v0.18.0 deep-destructuring engine.
  `let Ok(x) = expr`, `let %[a, b] = pair`, `let [h | t] = xs`,
  `let Point{x, y} = p`, and `let <<tag, _::binary>> = buf` all
  bind the right variables with the right narrowed types.
- Non-exhaustive `let` patterns emit code `E034` as a warning;
  the binding still compiles, and Erlang's `=` raises at runtime
  on a failed match.

### Multi-line `type` ADT declarations

- `parse_type_def/1` absorbs an optional wrapping `:indent`/`:dedent`
  pair, accepts an optional leading `|` before the first variant,
  and `parse_more_variants/1` skips newlines before peeking for
  `|`. Both layouts parse identically to the single-line form:

```cure
type Shape =
  | Circle(Int)
  | Square(Int)
  | Triangle(Int, Int, Int)
```

- `E033` Multi-line Type Layout Invalid added to the error catalog.

### ADT function-type payloads

Constructor payloads accept arbitrary type expressions including
function arrows. `type Callback = On(Int -> Int) | Off` and
`type Transform = Morph((Int, Int) -> Int) | Id` compile end-to-end;
pattern matching binds the callable to a variable callable from
inside the arm.

### Algebra formatter as default

`cure fmt` now runs the Wadler/`Inspect.Algebra`-style pretty
printer by default. The legacy byte-level formatter remains
available via `cure fmt --safe`; `cure fmt --check` routes through
the algebra formatter so CI agrees with interactive use.

### `@derive(Functor, Monoid, JSON)`

`Cure.Types.Derive.derive/3` gains three new targets: `:functor`
emits `fmap(x, f)` that applies `f` to every field; `:monoid`
emits `combine(a, b)` that pairwise combines each field with `<>`;
`:json` emits `to_json(x)` that renders the record as a JSON
object whose keys are the field names. `can_derive?/1` is extended
accordingly.

### Multi-clause parameter destructuring

`check_multi_clause/7` routes every clause parameter through
`bind_pattern_vars/3` instead of only binding bare variables. ADT
constructors, tuples, cons patterns, record patterns, and binary
patterns in function heads now introduce their inner variables for
the clause body.

### Error catalog

Four new codes `E031`-`E034` (Binary Pattern Not Exhaustive,
Function Type Payload Invalid, Multi-line Type Layout Invalid, Let
Pattern Not Exhaustive) with examples and fix guidance.

### Numbers

- 1078 tests pass (up from 1050, 3 doctests + 1075 tests);
  `mix credo --strict`: 0 issues across 137 source files;
  `mix cure.check.stdlib`: 25/25; `mix cure.check.examples`: 40/40.
- 5 new examples (`binary_destructuring.cure`, `adt_fn_payload.cure`,
  `multi_line_adt.cure`, `let_destructuring.cure`,
  `json_derive.cure`); 1 new doc (`docs/BINARIES.md`); updates to
  `docs/LANGUAGE_SPEC.md` and `docs/TUTORIAL.md` (new Chapter 11
  "Binary parsing").

## Implemented: v0.20.0 -- The Shape of Things

AST polish across four coupled compiler features. Plain `#`
comments are first-class nodes in the tree, binary literals and
patterns gain the full Elixir-style segment grammar
(`<<x::utf8, rest::binary>>`), a Wadler/`Inspect.Algebra`-style
pretty-printer lands behind `cure fmt --algebra`, and pattern
narrowing can expose disjoint-tag and literal-equality witnesses
via `Cure.Types.PatternRefinement`. None of the four tracks are
new surface-language features on their own -- they are the
scaffolding the next generation of features (binary destructuring,
width-aware layout, path-sensitive dependent narrowing) will build
on.

### Plain comment AST nodes

- `Cure.Compiler.Lexer.tokenize/2` gains a
  `preserve_comments: true` option. Plain `#` comments are emitted
  as `:line_comment` tokens; doc comments (`##`, `###`) continue
  to be preserved regardless.
- `Cure.Compiler.Parser` threads those tokens into the AST as
  `{:comment, [line:, col:], text}` nodes in top-level programs,
  container bodies, and block bodies. Indented comment-only lines
  preceding a block's `:indent` are routed inside the block so the
  comment ends up a sibling of the definition it documents.
- `Cure.Compiler.Codegen` and `Cure.Types.Checker` skip comment
  nodes silently so comment preservation has no runtime or
  type-checking cost.

### Full bitstring segments

- `:colon_colon` lexer token for `::`, distinct from `:colon`
  (type annotations) and `:atom` (symbol literals).
- `Cure.Compiler.Parser.parse_binary_literal/1` now wraps every
  element of `<<...>>` in a `{:bin_segment, meta, [value]}` node.
  Meta keys: `:type` (`:integer`, `:float`, `:bits`, `:bitstring`,
  `:bytes`, `:binary`, `:utf8`, `:utf16`, `:utf32`),
  `:signedness`, `:endianness`, `:size` (an AST node), `:unit`
  (integer). Specifiers chain with `-`
  (`::binary-size(n)`); a bare integer is shorthand for
  `size(n)`. Defaults mirror Erlang:
  `integer-unsigned-big-size(8)-unit(1)`, with `utf8` / `utf16` /
  `utf32` providing their own implicit size.
- `Cure.Compiler.Codegen` and `Cure.Compiler.PatternCompiler`
  translate the segment AST into full Erlang `:bin_element` forms
  in both construction and pattern positions.
- `Cure.Compiler.Printer` round-trips segments back into surface
  syntax.

This is the groundwork for the v0.21.0 headline feature: full
Erlang-style destructuring of binaries in `match`, function heads,
`let`, and comprehension generators.

### Algebra-based formatter

- `Cure.Compiler.Algebra` -- a new `Inspect.Algebra`-style document
  module with `empty`, `concat`, `nest`, `break`, `line`, `group`,
  `string`, `space`, `fold`, and a best-fit `format/2`. A `group`
  fits flat when its content stays within the remaining width;
  otherwise every soft break inside renders as a newline at the
  current indent.
- `Cure.Compiler.AlgebraFormatter` -- AST-to-document renderer
  that walks top-level programs, containers, and blocks, and
  delegates per-node rendering to the existing `Printer`.
  Standalone `{:comment, ...}` nodes round-trip as `# <text>`
  lines; sequences are separated by blank lines.
- `Cure.Compiler.Formatter.format_algebra/2` runs the new
  formatter with comment-aware round-trip verification: the
  formatted buffer must re-parse to an AST structurally equal to
  the input (modulo comment placement and position metadata),
  otherwise the original source is returned unchanged.
- CLI: `cure fmt --algebra` opts in. The existing byte-level safe
  formatter stays the default for v0.20.0 and will be promoted to
  `--algebra` as the default in v0.21.0.

### Structural refinement narrowing

- `Cure.Types.PatternRefinement.narrow/2` returns
  `{bindings, narrowed_scrutinee}` for any pattern against any
  scrutinee type. Literal sub-patterns yield equality refinements
  (`{x: Int | x == 0}` for `0`); constructor patterns (`Ok(v)`,
  `Error(e)`) and map patterns with a literal `:kind` tag yield
  `{:variant, tag, args}` witnesses. Integrates with the existing
  `Cure.Types.Refinement` SMT representation, so every narrowed
  type is something the SMT translator already understands.
- `bind_pattern_vars/3` in `Cure.Types.Checker` keeps its existing
  precise element typing for tuples / lists / records / maps;
  `PatternRefinement` is exposed as a separate module for callers
  that want the narrowed scrutinee. v0.21.0 will route
  `do_infer({:pattern_match, ...})` through it so match-arm bodies
  take advantage of the narrowing, and the path-sensitive
  refinement pass can propagate disjoint-tag witnesses across
  subsequent expressions in the same branch.

### Numbers

- 3 new Elixir modules (`Cure.Compiler.Algebra`,
  `Cure.Compiler.AlgebraFormatter`,
  `Cure.Types.PatternRefinement`); major extensions to
  `Cure.Compiler.Lexer`, `Cure.Compiler.Parser`,
  `Cure.Compiler.Codegen`, `Cure.Compiler.PatternCompiler`,
  `Cure.Compiler.Printer`, `Cure.Compiler.Formatter`,
  `Cure.Types.Checker`, and the CLI.
- 1016 tests pass (up from 970); `mix credo --strict`: 0 issues
  across 136 files; `mix cure.check.stdlib`: 24/24;
  `mix cure.check.examples`: 30/30.

### Deferred to v0.21.0

Type-checker refinement narrowing *through* binary patterns
(propagating `size(n)` into refinements on `rest`). Exhaustiveness
analysis for binary patterns (`Cure.Types.PatternChecker`).
Promotion of `cure fmt --algebra` to the default formatter.
Type-directed `@derive` extensions (Functor, Monoid, JSON). Full
Erlang-style destructuring of binaries in `match` expressions,
function heads, `let` bindings, and comprehension generators --
the segment AST from v0.20.0 is the groundwork; v0.21.0 adds
type-checker narrowing across binary segments and the
exhaustiveness analysis that goes with it.

Three parser/type gaps surfaced during the v0.20.0 cycle also
roll into v0.21.0: ADT constructor payloads must accept arbitrary
type expressions (including function arrows, so
`type Callback = On((Int) -> Int) | Off` parses and type-checks);
multi-line `type` ADT declarations with leading `|` on
continuation lines must parse (the indented layout currently
defeats `parse_type_def`); and `let` must support in-place
destructuring with the same depth and exhaustiveness guarantees
as `match` arms (ADT constructors, tuples, lists, records, and
maps, with `E025` on non-exhaustive bindings).

### Deferred to v0.22.0

Multi-statement lambda bodies -- brace-delimited
(`fn (x) -> { stmt1; stmt2; final }`) and `end`-terminated
(`fn (x) ->\n  stmt1\n  stmt2\nend`) block forms for anonymous
functions embedded in argument lists where the existing
indented-block form is not usable.
### Deferred to v0.23.0

Remote package-registry index service, publication signing, and
Hex.pm cross-publishing -- a `Cure.Project.Registry` HTTP client
against a read-only index protocol, Ed25519 archive signing, and
a `cure publish --hex` export path.

## Implemented: v0.19.0 -- Bring the Furniture

Ergonomics, proofs, and the first half of a registry.

### Language additions

- **`proof` containers** -- new `proof Name.Path` keyword; every
  binding inside must return `Eq(T, a, b)` or a refinement witness.
  Enforced as `E026`.
- **`assert_type expr : T`** -- compile-time type assertion that is
  stripped at codegen. Mismatches surface as `E027`.
- **Record field defaults** -- `rec Person\n  name: String = ""` --
  construction merges declared defaults with user-supplied fields;
  default/declared mismatches emit `E028`.
- **`@derive(Show, Eq, Ord)`** wired end-to-end on `rec` through
  `Cure.Types.Derive` plus the codegen's expansion pass.
- **Multi-head cons patterns** `[a, b, c | rest]` desugar to
  right-associated cons cells.

### Standard library additions

- **`Std.Proof`** -- reflexivity laws (`plus_zero`, `zero_plus`,
  `plus_comm`, `append_nil`, `map_id`).
- **`Std.Gen`** -- tiny stateless generator API (`int_in`, `bool`,
  `one_of`, `list_int`, `list_of_int`) backed by `:rand`.
- **`Std.Iter`** -- lazy iterator protocol; constructors `empty`,
  `from_list`, `range`; consumers `fold`, `take`, `to_list`.
- **`Std.Test.forall/3`** -- property-based runner.

### Totality

- `Cure.Types.Totality.check_mutual/1` -- Tarjan SCC analysis; cycles
  without a structural-decrease proof raise `E029`.

### Packaging

- `Cure.Project.Version` -- SemVer + constraint parser (`~>`, `>=`,
  `<=`, `<`, `>`, `==`, compound `and`); MAJOR.MINOR is shorthand for
  MAJOR.MINOR.0.
- `Cure.Project.Resolver` -- deterministic backtracking resolver
  over a local workspace; conflicts surface as `E030`. Remote index
  service deferred to v0.20.0.

### Error catalog

Five new codes `E026`-`E030`.

### Numbers

- 2 new Elixir modules (`Cure.Project.Version`, `Cure.Project.Resolver`);
  major extensions to `Totality`, `Derive`, `Codegen`, `Parser`,
  `Checker`, and `Type`.
- 3 new stdlib modules (`Std.Proof`, `Std.Gen`, `Std.Iter`); 24
  total.
- 4 new examples, 1 new doc (`PROOFS.md`).
- ~970 tests (up from 923); `mix credo --strict`: 0 issues;
  `mix cure.check.stdlib`: 24/24; `mix cure.check.examples`: 30/30.

## Implemented: v0.18.0 -- Deep Destructuring

`match` and `let` grow up. Pattern matching now descends through
arbitrary nesting across tuples, lists (cons and fixed), maps,
records, and ADT constructors. The previous implementation quietly
miscompiled map patterns (wrong Erlang abstract form) and never
recursed into nested shapes; v0.18.0 replaces it wholesale.

### Pattern engine

- **`Cure.Compiler.PatternCompiler`** -- dedicated pattern-to-Erlang
  translator, separated from expression codegen. Every pattern node
  is dispatched through a single recursive entry point.
- Map patterns emit `map_field_exact` (`:=`), not `map_field_assoc`
  (`=>`). Matching against a map pattern actually matches now.
- Record patterns lower to map patterns with
  `__struct__ := :tag` and per-field exact entries; unspecified
  fields are open-matched.
- Field punning: `Point{x, y}` is shorthand for `Point{x: x, y: y}`.
- Pin operator `^x` compares against a previously-bound value; the
  compiler lowers it to a synthetic `andalso` equality guard.
- Repeated variable occurrences in the same pattern emit equality
  guards too: `%[x, x]` matches only when both slots are equal.
- ADT constructors, cons, and tuple patterns recurse correctly
  through nested sub-patterns.

### Type checker

- `bind_pattern_vars/3` rewritten with deep recursion. Tuple
  patterns narrow element-by-element; map and record patterns
  resolve per-field through the record schema or the map value
  type.
- Maranget-style nested-exhaustiveness pass in
  `Cure.Types.PatternChecker.check_nested/2` reports concrete
  missing witnesses (for example ``"%[Error(_)]"``) under code
  `E025`. The flat classifier from v0.11.0 remains as a fast path.
- New error codes `E021`-`E025` (unknown record field, record-field
  type mismatch, non-literal map-pattern key, unbound pin, nested
  non-exhaustive match).

### Parser

- `^` lexed as `:caret`; parser now produces
  `{:pin, meta, [inner]}` for the pin operator.
- Field-punning in record patterns and map pairs: a bare identifier
  followed by `,` or `}` desugars to `name: name`.

### Standard library and examples

- New **`Std.Match`** module -- eight destructuring helpers
  (`unpack_pair/1`, `fst/1`, `snd/1`, `head_tail/2`, `uncons/1`,
  `first_two/2`, `unwrap_ok/2`, `unwrap_some/2`).
- `Std.List.uncons/1`, `Std.List.split_first/2` added using cons
  destructuring.
- `examples/destructuring.cure`, `examples/json_tree.cure` --
  end-to-end showcases. `examples/pattern_guards.cure` extended
  with record patterns, field-punning, and nested ADT destructuring.

### Documentation

- `docs/PATTERNS.md` -- authoritative pattern matching reference
  (Cure surface syntax, Erlang abstract-form mapping, binding
  semantics, exhaustiveness behaviour).
- `docs/LANGUAGE_SPEC.md` pattern-matching section rewritten from a
  12-line stub to a full reference.
- `docs/TUTORIAL.md` -- new Chapter 4 "Destructuring in `match`";
  later chapters renumbered.

### Numbers

- 1 new Elixir module (`Cure.Compiler.PatternCompiler`, ~480 LOC);
  rewrites inside `Codegen`, `Checker`, and `PatternChecker`.
- 1 new stdlib module (`Std.Match`), 1 extended (`Std.List`);
  21 stdlib modules total.
- 2 new examples, 1 extended.
- 923 tests passing (3 doctests, 920 tests) -- 26 new, 0 regressions.
- `mix credo --strict`: 0 issues across 117 source files.
- `mix cure.check.stdlib`: 21/21 clean;
  `mix cure.check.examples`: 26/26 clean.

## Implemented: v0.17.0 -- Proofs & Polish

The dependent-typing core grows up; the everyday UX catches up. Three
themes land together: dependent-type maturation, friction-free UX, and
ecosystem groundwork.

### Dependent-type maturation

- **Sigma types** `Sigma(name: T1, T2)` -- dependent pairs with
  componentwise subtyping; round-trip to plain runtime tuples.
- **Pi types** -- dependent function types with `:explicit`, `:implicit`,
  and `:erased` parameter modes and AST-based return types.
- **`Cure.Types.Reduce`** -- terminating normaliser for type-level
  arithmetic, booleans, comparisons, and pair projection. Trivial
  arithmetic never touches the SMT solver.
- **Propositional equality** `Eq(T, a, b)` with constructor `refl` and
  eliminator `rewrite`; runtime-erased via `:cure_refl`.
- **`Cure.Types.Unify`** -- first-order unification with occurs check
  for implicit-argument inference; `:unification_trace` pipeline event
  rendered in LSP hover and CLI error output.
- **`Cure.Types.Holes`** -- `?name` and `?_` placeholders with goal-type
  and local-context reporting via `:hole_goal`.
- **`Cure.Types.Totality`** -- coverage + structural-recursion analysis;
  `:total | :partial | :unknown` classification; `@total true` decorator.
- **`Cure.Types.PathRefinement`** -- path-sensitive refinement flow along
  `if` / `match` guards.
- `Std.Equal` -- `refl`, `sym`, `trans`, `cong`.
- `Std.Refine` -- `NonZero`, `Positive`, `Negative`, `NonNegative`,
  `Percentage`, `Probability`, and predicate helpers.

### Friction-free UX

- **`Cure.REPL`** -- full rewrite. Multi-line input, meta-commands `:t`,
  `:doc`, `:effects`, `:load`, `:reload`, `:use`, `:holes`, `:env`,
  `:reset`, `:fmt`, `:help`, `:quit`. History persisted to
  `~/.cure_history`.
- **`Cure.Watch`** -- `cure watch` recompiles, type-checks, or runs tests
  on every save with a 200 ms debounce.
- **`Cure.LSP.Server`** -- inlay hints, signature help, formatting,
  `prepareRename` / rename, code lenses, semantic tokens, workspace
  symbols.
- Error catalog codes `E011`-`E020` covering implicit-argument failures,
  sigma destructuring, totality, unfilled holes, refinement
  counterexamples, dependent-type mismatches, equality-proof mismatches,
  and doctests.
- `cure new <name> [--lib | --app | --fsm]` with three templates.
- `Cure.lock` lockfile; `cure deps update`, `cure deps tree`; git-based
  dependency resolution in `Cure.Project.resolve_git_dep/2`.
- `cure bench` -- benchmark runner for `bench/**/*.cure`.
- `cure test --filter PATTERN --doctests`; `Cure.Doc.Doctests` harvests
  `cure>` / `=>` doctests from `##` blocks.

### Ecosystem groundwork

- MIT `LICENSE` at repo root.
- Complete `mix.exs` `package` block for Hex publication, including docs
  extras.
- `vscode-cure/` -- TypeScript / LSP VS Code extension scaffold with
  TextMate grammar and language configuration.
- `docs/PACKAGE_REGISTRY.md` -- design document for the v0.19.0+
  package registry.
- `docs/TUTORIAL.md` -- ten progressive chapters.
- `docs/DEPENDENT_TYPES.md` -- full guide for the new type-system
  features.

### Numbers

- ~11 new Elixir modules, ~12 new test files, ~155 new tests (830
  total, 0 failures). Zero credo issues in strict mode.
- 2 new stdlib `.cure` modules (`Std.Equal`, `Std.Refine`); 20 total.
- 7 new examples, one for each major feature.
- `mix check` runs 20 stdlib + 24 example regressions in CI.

## Implemented: v0.16.0

Finitomata-inspired FSM rewrite. FSM definition and transition logic now
coexist in the same `.cure` file via callback mode; simple mode stays
backward-compatible.

### Dual-mode compilation

- **Callback mode** -- FSMs with an `on_transition` block compile to
  `GenServer`-based modules with embedded transition tables, user-defined
  `on_transition/4` dispatch, and lifecycle callbacks.
- **Simple mode** (backward-compatible) -- `gen_statem` codegen now
  includes `transitions/0` and `allowed/2` introspection, hard-event
  auto-fire via `next_event` actions, and soft-event silent catch-all
  clauses.
- `Cure.Compiler` pipeline handles both modes transparently.

### Event suffixes and lifecycle callbacks

- **Hard events** `event!` auto-fire when the FSM enters a state where the
  event is the sole outgoing transition. The compiler verifies the
  constraint.
- **Soft events** `event?` silently swallow failed transitions without
  logging or calling `on_failure`.
- `on_enter`, `on_exit`, `on_failure`, and `on_timer` lifecycle callbacks.
- `@timer <ms>` annotation for periodic `on_timer` invocations.

### Introspection and tooling

- `transitions/0`, `allowed/2`, `allowed?/2`, `responds?/2` --
  runtime-introspectable FSM API; `Cure.FSM.Runtime.allowed?/3` and
  `responds?/3` delegation.
- LSP: FSM transitions as children in the symbol tree with event-suffix
  labels; lifecycle callbacks in hover; FSM callback completions inside
  FSM blocks.
- MCP: `analyze_fsm` reports compilation mode, timer, event kinds with
  suffixes, and callback blocks.
- Printer emits event suffixes and `@timer` annotations.
- `examples/cure_turnstile/` rewritten to use callback mode.

## Implemented: v0.15.0

Effect system, documentation generator, developer experience improvements,
and full record type support with functional update syntax.

### Phase 1: Effect system

Track side effects in the type system. Pure functions can be aggressively
optimized; effectful functions are clearly marked.

- **Effect-annotated function types** -- `{:effun, params, ret, effects}`
  type with `MapSet` of effect kinds: `:io`, `:state`, `:exception`,
  `:spawn`, `:extern`.
- **Syntax: `! Effect`** -- optional effect annotations after return types:
  `fn read(path: String) -> String ! Io`. Inferred by default.
- **Effect inference** -- `Cure.Types.Effects` module walks function bodies,
  classifies effects from `@extern` targets, keywords (`send`, `spawn`,
  `throw`, `receive`), and known stdlib functions. Transitive propagation.
- **Effect subtyping** -- pure functions are subtypes of effectful functions
  with the same signature. Effect sets follow subset ordering.
- **Optimizer integration** -- `Inline` pass uses effect-grounded purity
  check instead of ad-hoc function name lists.
- **LSP hover** -- shows inferred effects alongside function signatures.
- **Pipeline events** -- `{:type_checker, :effects_inferred, ...}` and
  `{:type_checker, :effect_error, ...}` events.

### Phase 2: Documentation generator

Extract function signatures, type annotations, and doc comments into
browsable HTML documentation.

- **`##` doc comments** -- lexer emits `:doc_comment` tokens for double-hash
  lines; parser attaches them as `:doc` metadata on definitions.
- **`Cure.Doc.Extractor`** -- extracts structured doc maps from module ASTs:
  module name, module doc, functions with signatures/docs/effects, protocols,
  types.
- **`Cure.Doc.HTMLGenerator`** -- renders standalone HTML pages with
  syntax-highlighted signatures, effect badges, dark/light mode CSS.
- **`cure doc`** -- CLI subcommand generates HTML docs for `.cure` files.
- **Stdlib documented** -- all 18 stdlib modules annotated with `##` doc
  comments.

### Phase 3: Developer experience

- **`cure repl`** -- minimal interactive session backed by `compile_and_load`.
- **`cure fmt`** -- source formatter using `Cure.Compiler.Printer`.
- **Unused variable tracking** -- `Env` tracks variable usage; foundation for
  E007 warnings.
- **Error catalog E006-E010** -- Effect Violation, Unused Variable,
  Undocumented Public Function, Unreachable Clause, Missing Effect Annotation.

### Phase 4: Records

Full record type support: definitions, typed field access, and functional
update syntax.

- **Named type representation** -- `Type.resolve/1` now returns
  `{:named, "TypeName"}` for user-defined record/ADT names instead of `:any`.
  This carries the name through the type checker so field schemas are
  accessible during inference.
- **Field schema registration** -- the checker's first pass registers each
  `rec` definition's field types in `Env.types`. Field access `p.x` on a
  `Point`-typed value infers the declared field type (`Int`) rather than `Any`.
- **Record construction typing** -- `Point{x: 1, y: 2}` infers type
  `{:named, "Point"}` and the codegen emits a BEAM map literal with a
  `__struct__` key.
- **Record update syntax** -- `TypeName{base | field: val, ...}` produces a
  modified copy. Only listed fields change; all others are preserved.
  Compiles to the BEAM map-update instruction (`Map#{key := val}`).
  The parser detects update vs. construction by probing for `|` after the
  first sub-expression, rewinding if not found.
- **Type checker integration** -- override field values are checked against
  the registered schema. Wrong field types produce a compile-time error.
- **678 tests.** Zero Credo issues. Zero compilation warnings. 54 Elixir
  source files.

## Implemented: v0.14.0

Package management, deeper type tracking, LSP type holes, incremental
parsing, cross-module protocol dispatch, and extended testing.

### Phase 1: Package management

Cure gets its own project file and dependency resolution.

- `Cure.toml` project file with `[project]`, `[dependencies]`, `[compiler]`
  sections. Parsed at `cure compile` / `cure run` time.
- `cure init <name>` scaffolds the project: `Cure.toml`, `lib/`, `test/`,
  and a hello-world `lib/main.cure`.
- `cure deps` resolves and compiles path-based dependencies, adding their
  `.beam` files to the code path.

### Phase 2: Deep dependent type tracking

Move beyond call-site literal substitution into full value tracking.

- **Type tracking through `let` bindings** -- bound variables carry their
  inferred types through the type environment for subsequent call-site
  checking.
- **Path-sensitive refinement** -- inside `if x > 0 then safe_div(10, x) else 0`,
  the checker applies the branch condition as a type assumption in the
  then-branch and its negation in the else-branch.
- **SMT context accumulation** -- guard conditions accumulate as type
  refinements in the environment as the checker descends into branches.

### Phase 3: LSP type holes

Interactive type inference via placeholder types.

- `_` in type annotation positions resolves to `{:type_hole, :infer}` and
  is compatible with any type (`subtype?(_, T)` and `subtype?(T, _)` are
  always true).
- The type checker infers the hole's type from the function body and emits
  a `:type_hole_inferred` pipeline event with the inferred type.

### Phase 4: LSP incremental compilation

Performance optimization for large projects.

- **Version-based AST cache** -- on `textDocument/didChange`, re-parse and
  re-diagnostics are skipped when the incoming document version matches
  the cached entry, avoiding redundant work during rapid edits.

### Phase 5: Cross-module protocol dispatch

Complete the protocol story.

- **Registry-aware call resolution** -- when the codegen encounters an
  unresolved function call, it queries the global protocol registry;
  matching methods emit remote calls to the providing module.
- **Runtime fallback** -- calls not found in the registry fall back to
  local call resolution, allowing graceful degradation when compilation
  order does not guarantee visibility.

### Phase 6: Testing infrastructure

First-class testing support.

- `cure test` discovers `.cure` test files in `test/`, compiles each file,
  runs all `test_*` functions, and reports per-test pass/fail counts.
- `Std.Test` with `assert`, `assert_eq`, `assert_ne`, `assert_gt`,
  `assert_lt` assertion primitives.
- **670 tests.** Zero Credo issues. Zero compilation warnings. 49 Elixir
  source files. 18 stdlib modules.

## Implemented: v0.13.0

Dependent types get teeth. The compiler now proves constraints at call sites.

- **Dependent type verification at call sites** -- functions with `when`
  guards register as constrained types. At call sites, the compiler
  substitutes literals into the guard and sends the predicate to Z3. If
  unsatisfiable, you get a warning with a counterexample.
- **Cross-module protocol registry** -- global ETS table backing
  `register_impl`, `lookup_impl`, `has_impl?`. Every `impl` block registers
  during compilation, enabling cross-module dispatch resolution.
- **LSP: go-to-definition** -- jump to function and module definitions.
- **LSP: document symbols** -- hierarchical outline of modules, functions,
  protocols, FSMs.
- **LSP: code actions** -- quick-fix for non-exhaustive matches (add wildcard
  pattern) and did-you-mean suggestions for unbound variables.
- **5 optimizer passes** -- added inline (small pure non-recursive functions)
  and guard simplify (algebraic boolean rules).
- **FSM transition guards and actions** -- transitions support `when` guards
  and `do` actions: `State --event when cond do action--> NextState`.
- **Structured error catalog** -- error codes E001-E005 with `cure explain`.
  Errors show source location with caret display.
- **4 new stdlib modules** -- Map (14 fns), Set (11 fns), Option (10 fns),
  Functor (1 fn). Total: 17 modules, ~200 functions.
- **Std.Test** -- assertion primitives (`assert`, `assert_eq`, `assert_ne`,
  `assert_gt`, `assert_lt`). Total: 18 modules.
- **`cure test`** -- run test files from `test/`, compile and execute
  `test_*` functions.
- **`cure init`** -- scaffold a new project with `Cure.toml`.
- **`cure explain`** -- look up error code explanations.
- **606 tests.** Zero Credo issues. Zero compilation warnings. 48 Elixir
  source files.

## Implemented: v0.12.0

The first complete release. Full compilation pipeline from source to `.beam`.

- **Compilation pipeline** -- lexer, parser, type checker, code generator.
  Each stage emits structured events via PubSub.
- **Bidirectional type system** -- local type inference with annotation
  checking. Refinement types with constraints (`{x: Int | x > 0}`).
- **SMT integration** -- Z3 solver verifies refinement type constraints at
  compile time.
- **First-class FSMs** -- `fsm` blocks compile to OTP `gen_statem` modules
  with automatic reachability, deadlock freedom, and terminal state
  verification.
- **Protocol system** -- `proto`/`impl` with guard-based dispatch. Clauses
  ordered by type specificity (Bool before Atom).
- **Self-hosted stdlib** -- 12 modules written in Cure: Core, List, Math,
  String, Pair, Io, Show, Eq, Ord, System, Fsm, Result.
- **LSP server** -- diagnostics, hover, keyword completions over stdio.
- **MCP server** -- 7 tools for AI integration via JSON-RPC 2.0.
- **CLI** -- `cure compile`, `cure run`, `cure check`, `cure lsp`,
  `cure stdlib`, `cure version`.
- **Optimizer** -- 3 passes: constant fold, dead code elimination, pipe
  inline.
- **569 tests.** Zero Credo issues in strict mode. Zero compilation warnings.

## Future
These are not scheduled but are on the long-term radar.
**Typed hot code upgrades.** `cure release --upgrade-from` to emit
a typed `.appup` file with SMT-verified state migrations
(`@migration`, E057/E058). Time-boxed in v0.31.0 and rescheduled
for v0.32.0; the appup/relup machinery is large enough that it
deserves its own release cycle.
**Automatic PGO instrumentation.** v0.31.0 ships the data layer,
recorder, and consumer; the codegen pass that injects
`Cure.PGO.Recorder.tick/1` at every function entry (so users get
profiles by default with `cure run --record-profile`) is the
natural next step.
**Pattern-trigger SMT encoding.** v0.31.0 ships the
`generate_query/3` `pgo_hint` parameter and the hot-path
`arith.solver=6` switch; richer `forall ... :pattern` emission for
refinement obligations is the natural follow-up.
**Broader IDE support.** First-class Helix and Zed configurations.
An upgraded VS Code extension that tracks the current LSP surface
(inlay hints, signature help, code lenses, semantic tokens,
workspace symbols).
**REPL-level hot reload.** Recompile-and-rebind on every file save
for long-running REPL sessions, closing the loop between editing
`.cure` files and the running REPL environment.
