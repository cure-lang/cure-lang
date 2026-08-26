# Changelog

All notable changes to Cure are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## [Unreleased]

### Fixed

- `Cure.Protocol.Verifier` hardcoded `E056` for protocol-violation
  diagnostics, colliding with the unrelated, fully-catalogued
  `E056 @extern Declaration Missing a Typed Head` compiler diagnostic
  in `Cure.Diagnostic.Registry`. The protocol DSL runs outside the
  `.cure` compiler pipeline and was never actually registered in the
  registry, so it now uses its own `PROTO001` code instead of
  borrowing from the `E`-catalog namespace.

### Changed -- one dependent compiler pipeline

- The classic checker and code generator have been removed. Parsing now feeds
  `Cure.Elab.Program`, dependent Core validation, quantitative erasure, and the
  BEAM emitter for every program.
- The kernel now validates cumulative universes, Pi and Sigma types, indexed
  inductive families, dependent case elimination, strict positivity,
  definitional equality by normalization, and size-change totality
  certificates, including mutual recursion.
- Every Core binder carries a `{0, 1, ω}` usage grade, with affine and linear
  surface modes. Erased values cannot escape into runtime computation.
- Primitive `Eq`/`refl`/`rewrite` tokens were retired. `Std.Equivalent`
  provides the kernel-recognised inductive identity type
  `Equivalent(a, x, y)` and its `reflexive` constructor.
- Refinement predicates no longer enter the trusted type theory. SMT/Z3 guard
  coverage and shadow analysis remain explicitly untrusted diagnostics.

### Added -- dependent language surface

- Indexed families use `indices` to separate uniform parameters from
  constructor-varying indices. Dependent results may mention arguments, and
  brace-implicit parameters are inferred and erased when grade `0`.
- Empty and single-constructor types, bare nullary constructor patterns,
  forced patterns, impossible arms, `with` abstraction, unions,
  `typealias`, and visible `primitive` declarations are supported.
- Structural pattern elaboration is shared by `match`, multi-clause heads, and
  pattern-valued `let`: literals, tuples, nested list/cons patterns, maps,
  records, ADT/Option/Result constructors, pins, repeated variables, and guards
  retain narrowed types and nested source spans.
- Anonymous functions support single-expression, indented, brace-delimited,
  and `end`-terminated multi-expression bodies with expected-type propagation.
- `Any` is a genuine top type in safe covariant positions. For example,
  `List(Int)` satisfies `List(Any)`; invariant and index-sensitive positions
  continue to reject unsafe widening.
- Integer literals default to `Int` but may be interpreted contextually through
  `ExpressibleByNaturalLiteral` / `ExpressibleByIntegerLiteral`. Total
  `LiteralResult` conversion lets finite domains reject invalid literals at
  compile time rather than wrap or trap.

### Changed -- interfaces, implementations, and modules

- `interface` / `implementation` replace `proto` / `impl`; generic functions
  state obligations with `requires`. `cure migrate` performs the keyword
  rewrite.
- `Std.Equatable` backs runtime `==`/`!=`; `Std.Comparable` replaces
  `Std.Ord` and backs ordering operators. `Std.Equivalent` is proof equality
  and is deliberately separate from both.
- Canonical module interfaces publish authored and generated declarations
  under stable owner-qualified identities. Lexical imports remain separate
  from qualified availability, repeated loading is idempotent, and transitive
  bare names do not leak.
- Module graphs determine declaration/loading order, including implementation
  providers and user `@prelude` modules, rather than relying on file order.
- User precedence groups and infix/prefix/postfix declarations propagate
  through `use` edges and ambient project preludes; conflicts and cycles are
  diagnosed before authoritative parsing.

### Added -- derivation and macros

- `@derive(Show, Equatable, Ord)` publishes structural record
  implementations; the `Ord` derive tag targets `Comparable`.
  `@derive(JSON)` publishes `to_json/1`. Generated declarations use the same
  canonical tables and provenance as authored functions.
- Staged `syntax ... becomes`, typed/repeated/hygienic holes, `quote` with
  splicing, `computed by`, and `Std.Syntax` reflection provide user-defined
  syntax. OTP actor/FSM/supervisor/application and reactive DSLs are authored
  through this macro surface.

### Changed -- standard library

- `Option`, `Some`, and `None` have the canonical home `Std.Option`; `Result`,
  `Ok`, and `Error` have the canonical home `Std.Result`. Import the module
  with `use` and write the bare type/constructors; no
  `Std.Result.Result` spelling is required.
- `String` is the transparent `List(Char)` alias. Primitive `Char`, `Atom`,
  `Binary`, `Int`, and `Float` have visible standard-library homes.
- Added or reshaped `Std.Optic`, length-indexed `Std.Vector`,
  `Std.NonEmpty`, `Std.Decision`, `Std.Sigma`, `Std.Tuple`, the typed
  `Std.Otp` algebra, proof/reflection modules, and the expanded `Std.Iter`.
- `Std.Regex` is indexed by its extraction result and compiles to a direct
  pattern machine with typed evidence decoding. The unindexed tree, recursive
  suffix matcher, and OTP regex shim are removed.
- `Std.Access`, `Std.Equal`, and `Std.Ord` are retired in favor of
  `Std.Optic`, `Std.Equivalent`, and `Std.Comparable`.
- `Std.Test` assertions and ordinary property runners return `Unit`.
  Shrinking runners return `Result(Unit, t)`, with a minimized
  counterexample in `Error`.

### Added -- diagnostics, migration, and build tooling

- Structured diagnostics now retain stable codes, authored/related ranges,
  canonical definition identities, and machine-safe fixes across terminal,
  JSON, and LSP consumers.
- Editions (`@edition` and `[project].edition`) pin grammar and keyword sets.
  `cure migrate` supports check/print/strict modes, atomic batches,
  fixpoint/reparse validation, import-order-independent rewrites, and refuses
  unsafe dirty-tree mutation.
- `cure audit trust <Module>` reports reachable `postulate`, bodyless
  `@extern`, and `believe_me` roots.
- Multi-file and incremental builds share dependency ordering, canonical
  module loading, user-prelude discovery, and sound cache invalidation.
- `mix cure.check.examples` compiles every root example and executes every
  recorded `main/0` expectation. The corpus currently reports 40 passing
  examples with no skips or failures.

### Added -- canonical `%[A, B]` tuple-type syntax

Tuple types use the same `%[...]` sigil as tuple values. `%[A, B]`, `%[A]`,
and `%[]` enter the dependent tuple pipeline directly; positions may also carry
dependent binders such as `%[x: A, B(x)]`. Legacy `(A, B)` remains accepted and
compiles to the same Core and BEAM representation, while parser tooling emits
the explainable `E086 / E-TYPE-TUPLE-PAREN` deprecation. Grouped `(A)` and
function domains `(A, B) -> C` are unchanged.

### Added -- `Std.Iter` becomes a peer of `Std.List`

The lazy half of the collections story is fleshed out. `Std.Iter`
previously shipped only `empty`, `from_list`, `range`, `fold`, `take`,
and `to_list` (v0.19.0). It is now a complete lazy-iterator API,
designed so a chain like

```cure
use Std.List

fn pipeline() -> List(Int) =
  map([1, 2, 3, 4, 5], fn(x) -> x * x)
```

reads left to right and only materialises at the terminal consumer.

- **`lazy/1`** -- documented entry point for the lazy-pipeline idiom.
  Identical to `from_list/1`; the alternate name signals at the call
  site that the rest of the chain should be read as lazy.
- **Producers** -- `iterate(x0, f)`, `unfold(seed, f)`, `repeat(x)`,
  `cycle(list)`. The first three are infinite and must be paired
  with a slicer. `cycle/1` collapses to `empty/0` for an empty input
  so consumers terminate.
- **Transformers (lazy in, lazy out)** -- `map(it, f)`,
  `filter(it, pred)`, `flat_map(it, f)`, `concat(a, b)`,
  `zip_with(a, b, f)` (curried), `intersperse(it, sep)`. None of
  these force the iterator; they wrap a thunk that defers work.
- **Slicers (lazy in, lazy out)** -- `take_while(it, pred)`,
  `drop(it, n)`, `drop_while(it, pred)`. `drop/2` with non-positive
  `n` is a no-op.
- **Consumers (terminal)** -- `each(it, f)`, `count(it, pred)`,
  `any(it, pred)`, `all(it, pred)`, `find(it, pred, default)`.
  `any` and `all` short-circuit; `find` returns at the first hit.
  Existing `fold`, `take`, and `to_list` continue to materialise.

### Added -- documentation

- **`docs/STDLIB.md`** -- `Std.Iter` section rewritten. Covers the
  `lazy/1` idiom, the four function categories (constructors,
  transformers, slicers, consumers), and per-function signatures.
- **`lib/std/iter.cure` moduledoc** -- expanded with the
  lazy-pipeline idiom, a Fibonacci `unfold` worked example, and
  the existing fold/take examples preserved verbatim.

### Added -- tests

- **`test/cure/stdlib/iter_test.exs`** -- 43 tests covering every
  new function, edge cases (empty inputs, predicates that never
  match, drop past the end, cycle of empty, single-element
  intersperse), and a laziness-verification test that drives a
  ten-million-element range through `map` + `take(5)` and asserts
  `map`'s callback ran exactly five times.

### Notes on backward compatibility

No language-surface or behaviour changes. `Std.Iter`'s pre-existing
functions keep their signatures and semantics; the additions are
purely additive. Code that compiled and ran against the v0.19.0
shape compiles and runs unchanged.

No new operator was introduced. The `|~>` "lazy pipe" was
considered and rejected: in Cure, `|>` is a syntactic transform
(`a |> f(b)` desugars to `f(a, b)`), and a sibling operator that
flipped module dispatch would either require a global eager-to-lazy
rewrite map (fragile) or polymorphic dispatch by argument shape (in
which case the operator stops earning its keep relative to a plain
`lazy/1` call). Explicit dispatch via `lazy/1` keeps the language
small and the call site honest about when laziness begins.

## [0.33.0] -- Formalisation

v0.33.0 is the formalisation release. The two branching constructs in
the language -- `match` and `pickup` -- graduate from "described in a
tutorial" to "specified, normatively, at version 1.0.0". Two long-form
documents land in HexDocs, the website grows a dedicated `pickup`
page, and the language reference cross-links the new sources of truth.

Nothing in the compiler moves. The specifications were written against
the behaviour the implementation already exhibits; v0.33.0 ships the
contract, not a behaviour change.

### Added -- Normative specifications

- **`docs/MATCH.md`** -- *The `match` Construct, Language
  Specification, Version 1.0.0*. Covers the lexical syntax, EBNF
  grammar, the full pattern sub-grammar (literals, wildcards, silent
  bindings, tuples, lists, maps, records, ADT constructors, the pin
  operator, binary segments, repeated variables, refutability, and
  arbitrary nesting), the static semantics (typing judgement T-Match,
  Maranget-style exhaustiveness, reachability, scoping, refinement
  interaction, polymorphism, decidability, erasure), the dynamic
  semantics (evaluation order, side-effect observability, exceptions,
  divergence), the formal operational semantics (big-step rules
  M-Hit / M-Skip-Pat / M-Skip-Guard / M-NoClause, small-step rules
  SM-Scrut / SM-Hit / SM-Skip-Pat / SM-Skip-Guard / SM-NoClause,
  evaluation contexts, determinism / progress / preservation /
  equivalence / confluence, cost and memory models), formatter
  conformance (twenty-five clauses), tail-position behaviour,
  compilation / lowering rules, constant folding obligations, macro
  hygiene, IDE / language-server requirements, the diagnostic
  catalogue, non-goals, the soundness proof sketch (Appendix J), an
  acceptance test corpus (Appendix A), worked pattern examples
  (Appendix F), the style guide (Appendix G), anti-patterns
  (Appendix H), reserved future syntax (Appendix I -- or-patterns,
  view patterns, range patterns, dependent patterns, as-patterns), a
  bibliography (Appendix K), open questions (Appendix L), and the
  colophon (Appendix M).
- **`docs/PICKUP.md`** -- *The `pickup` Construct, Language
  Specification, Version 1.0.0*. Mirrors the `match` document in
  shape: lexical syntax, grammar, static semantics (typing rules
  T-Pickup-Else and T-Pickup-Cons, exhaustiveness via the mandatory
  terminator, reachability lattice, scoping, refinement interaction,
  type-inference algorithm, polymorphism, decidability, erasure),
  dynamic semantics, operational semantics (big-step rules
  P-Else / P-Hit / P-Skip / P-Guard-Raise / P-Guard-Diverge,
  small-step rules SP-Guard / SP-Hit / SP-Skip / SP-Else /
  SP-Guard-Raise, properties, cost model, memory model), the
  formatter rules (alignment, default-clause normalisation, comment
  fidelity, idempotence, round-trip, performance bounds, plugin
  interface, editor-folding integration, the formatter conformance
  grammar), tail-position behaviour, lowering, constant folding, the
  algebraic-laws table, the migration story for legacy `if`/`elif`
  including `cure rewrite if-to-pickup` and the new `E-IF-REMOVED`
  diagnostic, IDE / language-server requirements, the diagnostic
  catalogue (errors `E-PICKUP-NO-ELSE`, `E-PICKUP-ELSE-NOT-LAST`,
  `E-PICKUP-MULTIPLE-ELSE`, `E-PICKUP-GUARD-TYPE`,
  `E-PICKUP-BRANCH-MISMATCH`, `E-IF-REMOVED`; warnings
  `W-PICKUP-UNREACHABLE`, `W-PICKUP-DEAD-ELSE`,
  `W-PICKUP-EFFECTFUL-GUARD`; hints `H-PICKUP-PREFER-ELSE`,
  `H-PICKUP-DEGENERATE`, `H-PICKUP-LINE-TOO-LONG`,
  `H-PICKUP-COMMENT-RELOCATED`), non-goals, an acceptance test
  corpus, worked migration examples, the style guide, anti-patterns,
  reserved future syntax (`pickup as`, `pickup with`, `pickup async`,
  trailing `where`), a bibliography, open questions, and the
  colophon.

### Added -- Surrounding documentation

- **`docs/MATCH.md` and `docs/PICKUP.md`** wired into the `mix.exs`
  documentation extras list, so HexDocs renders both specifications
  alongside `docs/PATTERNS.md`, `docs/BINARIES.md`, and the rest of
  the language references.
- **`docs/LANGUAGE_SPEC.md`** -- the existing `## Pattern Matching`
  section now opens with a normative pointer to `docs/MATCH.md`; a
  new `## Conditional Dispatch (`pickup`)` section opens with a
  pointer to `docs/PICKUP.md` and recapitulates the mental model in
  one paragraph for inline readers.
- **`site/priv/pages/match.md`** -- a leading note frames the page
  as the user-facing tutorial complement to `docs/MATCH.md`; a
  closing note links to the new `pickup` page and to
  `docs/PICKUP.md`.
- **`site/priv/pages/pickup.md`** (new) -- user-facing reference
  page for `pickup`. Covers the grammar, the totality requirement,
  guard evaluation order, strict-`Bool` typing, per-clause scoping,
  worked examples (sign classification, HTTP routing, nested
  `match`/`pickup`, `pickup` as an expression), the migration story
  from legacy `if`/`elif`, the error catalogue, and the formatter's
  alignment / `else` normalisation rules. Cross-links
  `docs/PICKUP.md` and `docs/MATCH.md`.
- **`site/priv/pages/roadmap.md`** -- new `## Implemented: v0.33.0
  -- Formalisation` section.
- **`site/priv/pages/tooling.md`** -- new v0.33.0 additions section
  pointing at the formal specifications and highlighting the
  tooling-relevant clauses (formatter conformance, language-server
  requirements, the per-construct diagnostic catalogue).
- **`site/priv/posts/2026/04-26-cure-v0.33.0.md`** -- release blog
  post.

### Changed

- `mix.exs` version bumped to `0.33.0`.
- `docs/MATCH.md` and `docs/PICKUP.md` each gain a `v0.33.0` entry
  under Appendix C -- Change Log, recording the publication into
  HexDocs and the surrounding documentation work. The 1.0.0 normative
  body of both documents is unchanged.
- `RELEASE.md` rewritten to lead with the formalisation theme.
- `stuff/TODO-IDEAS.md` updated: a new `## v0.33.0 -- accepted
  bundle` block describes the formalisation theme; the Cure-native
  notebook block is rescheduled to `## v0.34.0 -- planned next
  sprint`.

### Notes on backward compatibility

No language-surface behaviour changes. The implementation already
honours every clause of the published specifications; v0.33.0 turns
the contract into a published artefact. Code that compiled and ran
under v0.32.0 compiles and runs identically under v0.33.0.

## [0.32.0] -- Trust, Export, Recall, Narrate

Four independent features completing the v0.32.0 sprint.

### Added -- Proof-carrying packages

- **`Cure.Project.Proof`** -- certificate serialization core. Binary
  format: `"CUREPROOF\0" <> <<0x01>> <> gzip(term_to_binary([cert, ...])))`.
  `collect/1` re-invokes the compiler in `proof_collect` mode and drains
  the accumulated certificate ETS table. `serialize/1`, `deserialize/1`,
  and `verify/1` cover the full lifecycle. Four certificate kinds:
  `:equality`, `:refinement`, `:smt`, `:totality`.
- **`Cure.Project.Proof.Verifier`** -- offline replay engine. Equality
  certificates verified by structural term equality against `:cure_refl`.
  Refinement certificates via lightweight Z3-free bounds arithmetic.
  SMT certificates via local Z3 query replay (degrades to `:ok` when
  no solver is present). Totality certificates via SCC structural-decrease
  check.
- **`Cure.Compiler`** -- `proof_collect: true` compile flag; when the
  checker result carries a list of certificate maps, each cert is deposited
  into the named ETS table `cure_proof_certs` via `Cure.Project.Proof.deposit/1`.
- **`Cure.Project.Publisher.build_tarball/2`** -- gains `include_proofs:
  boolean()` option (default `true`). When enabled, calls
  `Cure.Project.Proof.collect/1` and appends `<name>.cureproof` to the
  tar entries. `project_include_proofs/1` reads the flag from the new
  `[publish]` TOML table.
- **`Cure.Project`** -- new `publish` struct field. TOML parser reads a
  new `[publish]` table; `normalize_publish/1` extracts
  `include_proofs :: boolean()`. Default: `true`.
- **`Mix.Tasks.Cure.Verify`** -- `mix cure.verify [path] [--strict]`.
  Dispatches to tarball extraction, directory glob, or current-project
  proof collection depending on the path argument.
- **`docs/PROOF_CARRYING.md`** -- file format spec, CLI reference, CI
  integration guide, `strict_proofs: true` config, certificate-kind table.
- **Error codes E065--E067**: Proof File Missing, Proof Verification
  Failed, Proof Schema Incompatible.

### Added -- Cross-language ADT export

- **`Cure.ExportTypes`** -- orchestrator. Walks `.cure` source files,
  parses with the compiler's lexer+parser, classifies `:enum`, `:struct`,
  and `:type_annotation` AST nodes, delegates to backend emitters.
- **`Cure.ExportTypes.Protobuf`** -- proto3 emitter. Complete type
  mapping: `Int->int64`, `Float->double`, `Bool->bool`, `String->string`,
  `Bytes->bytes`, `List(T)->repeated T`, `Option(T)->optional T`, pure-enum
  ADTs to proto3 `enum` with `_UNSPECIFIED = 0`, payload-bearing ADTs to
  wrapper `message` + `oneof value` blocks + one synthetic payload message
  per variant. Field names `camelCase->snake_case`; field numbers by
  declaration order. Refinements / dependent types emit `bytes` with a
  comment and call `IO.warn/2` with E068.
- **`Mix.Tasks.Cure.ExportTypes`** -- `mix cure.export_types
  [--target protobuf] [--out dir] [--dry-run] [--verbose] [files...]`.
  Default output: `_build/cure/export/<target>/`.
- **`docs/EXPORT_TYPES.md`** -- type mapping table, CLI flags, proto3
  field numbering rules, `@export_as` annotation hint, guidance on ADT
  shapes.
- **Error code E068**: Export Type Unmappable (warning, not hard error).

### Added -- `cure snap` (REPL session snapshots)

- **`Cure.REPL.Snap`** -- snapshot serialization. Binary format:
  `"CURESNAP\0" <> <<0x01>> <> gzip(term_to_binary(snap_map))`.
  `save/2`, `load/1`, `apply_snap/2`, `list/1`. Captures: session entries,
  up to 500 history lines, use imports, holes, stdlib mode, theme, editing
  mode, advisory loaded paths. Merge semantics on load: last-writer-wins
  per entry key for defs; union for uses; prepend for history.
- **`Cure.REPL`** -- six new `handle_meta` clauses:
  `:snap save [path]`, `:snap load <path>`, `:snap list [dir]`,
  bare `:snap` (shows sub-command help). Alias `Snap` added to the
  module alias list. `:help` text updated.
- **`Mix.Tasks.Cure.Snap`** -- `mix cure.snap save|load|list`.
  `save` creates an empty stub snap; `load` prints the snap manifest
  (definition count, history entries, imports); `list` prints paths.
- **`docs/SNAP.md`** -- file format spec, merge semantics table, CI
  workflow, E069/E070 guidance.
- **Error codes E069--E070**: Snap Schema Incompatible, Snap Module
  Missing.

### Added -- `cure story` (narrative architecture generator)

- **`Cure.Story.Outline`** -- AST walker. Parses every `.cure` file
  under `lib/` silently (parse errors skipped). Classifies `:app`,
  `:supervisor`, `:actor`, `:fsm`, `:enum`, `:struct`, and
  `:type_annotation` containers into a five-layer outline map.
- **`Cure.Story.Narrator`** -- template-driven prose generator. One
  section per outline level. `--diagrams` option embeds
  `stateDiagram-v2` Mermaid code blocks for each FSM (reuses
  `Cure.Doc.Mermaid` conventions).
- **`Cure.Story`** -- orchestrator. Reads `[project].name` from
  `Cure.toml`; supports `--format html` (minimal HTML shell),
  `--stdout` (return content without writing), `--out`.
- **`Mix.Tasks.Cure.Story`** -- `mix cure.story [--out path]
  [--stdout] [--diagrams] [--format md|html]`.
- **`docs/STORY.md`** -- CLI reference, container classification table,
  example output excerpt, CI gate pattern.

### Added -- Cross-cutting

- **`Cure.Compiler.Errors`** -- six new catalog entries E065--E070
  following the existing `"E0XX" => """..."""` pattern.
- **`Cure.CLI`** -- `verify`, `export-types`, `snap`, `story` dispatch
  clauses; all four wired into `known_commands` and `cure help`.
- **`mix.exs`** -- version `0.32.0`; four new extras:
  `docs/PROOF_CARRYING.md`, `docs/EXPORT_TYPES.md`, `docs/SNAP.md`,
  `docs/STORY.md`.
- **`site/priv/posts/2026/04-25-cure-v0.32.0.md`** -- release blog post.
- **`site/priv/pages/roadmap.md`** -- new v0.32.0 Implemented section.
- **`site/priv/pages/tooling.md`** -- new v0.32.0 additions section.
- **`site/priv/pages/repl.md`** -- `:snap save/load/list` added to the
  Session meta-commands section.

### Changed

- `Cure.Project.Publisher` alias list: `Proof` alias removed (module
  is called via full name `Cure.Project.Proof`).
- `Cure.REPL` `known_commands` list and `:help` markdown updated with
  `:snap`.
- `stuff/TODO-IDEAS.md` updated: v0.32.0 accepted bundle section
  added; v0.31.0 deferred block updated to point at v0.33.0 notebook;
  `cure snap` and proof-carrying packages removed from parked pool.

## [0.30.2] -- `john`, polished

Patch release that makes the three `john` surfaces render identically
and keeps the task pleasant to re-run a hundred times a session.

### Fixed

- **`mix cure.john` no longer mojibakes its bullet markers.**
  `Cure.John.run/1` now writes its rendered report through
  `IO.write/2` rather than `IO.binwrite/2`. Under the Mix-owned
  `:stdio` IO server, `binwrite` transcodes binaries byte-by-byte
  as Latin-1 into UTF-8, which double-encoded every multi-byte glyph
  Marcli emits -- most visibly its `U+25B8` bullet, which used to
  surface as the now-infamous `U+00E2 U+00B8` (`a-circumflex + cedilla`)
  pair in the terminal. `IO.write/2` goes through the Unicode-aware
  path and passes the original UTF-8 bytes untouched.

### Changed

- **Tighter, repeatable banner.** The multi-line italic tribute
  paragraph was dropped from every `john` surface so the report
  stays welcome when run repeatedly during a debugging session.
  The headline is now a single line:

  ```
  # Cure X.Y.Z  --  John  --  'What I need is visibility'
  ```

  The em dashes and curly quotes are literal Unicode (`U+2014`,
  `U+2018`, `U+2019`). Marcli renders them as text, and
  `Cure.REPL.Markdown.render/2` decodes them via its UTF-8 clause,
  so both pipelines preserve the codepoints.

## [0.30.1] -- `john` formatting follow-up

Post-release polish for the `john` diagnostic. No feature changes.

### Fixed

- Structured `erl_crash.dump` summary extraction replaces the old
  raw-tail view that flooded terminals with illegible process-state
  blobs. Only the first 64 KiB of the dump are scanned; standard
  header fields (`Slogan`, `System version`, `Atoms`, the `=memory`
  block) and section counts (`=proc:`, `=ets:`, `=mod:` ...) are
  rendered as Markdown bullets.
- Log tails and crash-dump bodies are run through a UTF-8 sanitiser
  that substitutes ill-formed bytes with `?`, so mid-line binary
  payloads no longer break the downstream Markdown renderer.
- Fallback renderer uses `*italic*` instead of `_italic_` because
  `Cure.REPL.Markdown.render/2` only understands the asterisk form.
- Removed the redundant catch-all clause in `Cure.REPL`'s
  `bare_use?/1` that caused a dialyzer pattern-match warning.
- Aligned REPL / CLI banners to ASCII-only punctuation for the
  renderers that did not yet handle every Unicode dash.

## [0.30.0] -- John

v0.30.0 is the `john` release. The headline feature is a single
panoramic diagnostic -- call it by any of three names, get the same
report -- that gathers everything worth knowing about Cure, the BEAM
VM it is running on, the project under the cursor, and the last few
log entries, and prints it as Markdown-to-ANSI. Everything else is
quiet: a handful of small bugfixes, documentation refreshes, and
alignment between the CLI, the Mix task registry, and the REPL
meta-command list.

The feature is named in tribute to **John Carbajal**, who taught the
author that the most useful button on any dashboard is the one that
shows everything.

### Added -- `john`: the everything-at-once diagnostic

A single Markdown-rendered report exposed through three surfaces that
all funnel into one implementation:

- **`mix cure.john`** -- `Mix.Tasks.Cure.John`. Supports `--width`,
  `--ansi` / `--no-ansi`, `--banner` / `--no-banner`, `--root PATH`.
- **`cure john`** -- `Cure.CLI` subcommand. Same flags. Listed in
  `cure help` alongside `cure top` and `cure doctor`.
- **`:john`** -- `Cure.REPL` meta-command. Inherits the current
  session's theme and colour state; listed in `:help` and in the
  Levenshtein suggestion set so a typo surfaces a "Did you mean?".

The collector (`Cure.John.collect/1`) produces a plain Elixir map --
no PIDs, references, or functions -- so the result can be inspected
in tests, serialised to JSON, or piped into a structured logger.
Sections:

- **Cure** -- version, escript entry point, application loaded /
  started state, count of loaded stdlib modules, pipeline event-bus
  size, protocol registry size, UTC snapshot timestamp.
- **BEAM / OTP** -- Elixir / OTP / ERTS versions, full system banner,
  scheduler topology (online / total / dirty CPU / dirty I/O),
  logical processor count, process / port / atom counts with their
  limits, ETS table count, memory breakdown (total / processes /
  atom / binary / code / ETS / system), reductions, runtime,
  wall-clock uptime, internal / external wordsize.
- **System** -- OS family and version, architecture, hostname,
  user, home, cwd, and selected environment variables (`LANG`,
  `TERM`, `SHELL`, `PATH` entry count).
- **Tooling** -- Elixir / OTP / Cure versions, plus the resolved
  paths of `z3`, `git`, `make`, `cc` and the loaded versions of every
  declared dependency.
- **Project** -- when `Cure.toml` is present in the current
  directory: name, version, root, source paths, lockfile status,
  and the full dependency table with per-entry
  `version` / `path` / `git` markers.
- **Runtime** -- a condensed `Cure.Observe.Top` snapshot: supervisor
  / actor / FSM counts plus the top five supervisors.
- **Doctor** -- severity counters from `Cure.Doctor.run/1`
  (info / warning / error) plus the overall `ok?` flag. The report
  itself still lives behind `cure doctor` for the detail.
- **Recent logs** -- tails of up to five log files under
  `.cure/logs/*.log`, `_build/cure/logs/*`, or an `erl_crash.dump`
  at the project root, sorted by mtime.

`Cure.John.render/2` turns the map into CommonMark. `Cure.John.run/1`
renders through `Marcli.render/2` when the MDEx NIF can load
(`mix cure.john`, `iex -S mix`), and transparently falls back to
`Cure.REPL.Markdown.render/2` when it cannot (most notably inside
the bundled `cure` escript), so the three call sites always produce
a human-readable report.

### Added -- Documentation

- **`docs/JOHN.md`** -- authoritative on-disk reference for the
  `john` subcommand, Mix task, and REPL meta-command, plus the
  `Cure.John.collect/1` / `Cure.John.render/2` / `Cure.John.run/1`
  API and the fallback Marcli-to-pure-Elixir rendering path. Added
  to `mix.exs` docs extras.
- **`docs/REPL.md`** -- `:john` added to the Quit section next to
  `:help` and `:quit`.
- **`site/priv/pages/tooling.md`** -- new v0.30.0 section pointing
  at `cure john` and at `docs/JOHN.md`.
- **`site/priv/pages/repl.md`** -- `:john` added to the
  meta-commands reference.
- **`site/priv/pages/roadmap.md`** -- new Implemented: v0.30.0
  entry above v0.29.0.
- **`site/priv/posts/2026/04-24-cure-v0.30.0.md`** -- release blog
  post.

### Changed

- `mix.exs` version bumped to `0.30.0`.
- `cure help`, `Cure.CLI`'s `known_commands` list, and the REPL's
  `known_commands` list now all advertise `john` / `:john`.

## [0.29.0] -- Make Documentation Great

v0.29.0 is the documentation release. Nothing else was the primary
target. Every compiler module, the REPL, the website, the editor
plugins, the Hex docs, and the escript's own `cure doc` output were
pulled up to the same bar: real explanations, real examples, real
cross-links. The compiler surface itself is quiet -- one parser fix
for doc-comment merging -- but the result is a codebase where every
public surface is now discoverable in the place a reader would expect
to find it.

### Added -- `cure doc`: ExDoc-like two-pane layout

`cure doc` now produces a full documentation site, not a per-module
HTML fragment. The new layout mirrors ExDoc's shape: a persistent
left sidebar lists orphan pages and every extracted module, the right
pane shows the selected page with anchored entries for every public
function, type, and protocol, and a small vanilla-JS bundle wires up
a `prefers-color-scheme` theme toggle and a keyboard-focusable
(`/`) filter over the sidebar.

- **`[doc]` section in `Cure.toml`** drives the layout. Supported
  keys: `main` (landing-page slug), `title`, `extras` (array of
  relative Markdown paths turned into orphan pages), `logo`,
  `source_url`, `source_ref`.
- **`[doc.groups_for_modules]`** lets the sidebar group the module
  list. Unassigned modules land in a trailing `"Other"` bucket so
  nothing is silently dropped.
- **`Cure.Doc.Markdown`** -- new module. Thin wrapper over the
  NIF-free `:md` library with two escript-safe extras: placeholder
  interpolation (`{{cure_version}}`, `{{cure_vversion}}`) and
  Makeup-powered syntax highlighting for `cure`, `elixir`, and
  `erlang` fenced code blocks.
- **`--title`, `--main`, `--extras`** CLI switches on `cure doc`
  override the matching `[doc]` keys per invocation. `--extras` is
  repeatable.
- **Project-root extras discovery.** Relative paths in `[doc].extras`
  resolve against the directory that contains `Cure.toml`, so the
  same configuration works from any sub-directory.
- **Anchored entries.** Every public function, type, and protocol
  inside a module page gets a stable `#fn-<name>`, `#type-<name>`,
  `#proto-<name>` anchor. Sources URLs link back to
  `github.com/cure-lang/cure-lang/blob/main/lib/std/<module>.cure`
  at the right symbol.

### Added -- Stdlib Examples blocks

Every module under `lib/std/` now carries a module-level
`## Examples` block in its `##` doc comments, showcasing idiomatic
usage. Four high-traffic `Std.Core` functions also carry per-function
examples: `compose`, `map_ok`, `and_then`, `map_option`.

All examples round-trip through `mix cure.compile_stdlib` without
modification -- the Examples blocks are valid Cure, not hand-waved
pseudo-code.

### Added -- `/stdlib` site integration

The Cure website now renders stdlib docs as first-class pages,
identical to what `cure doc` would produce from the same sources:

- **`CureSite.Stdlib`** -- compile-time bundle of every `Std.*`
  module, extracted from `cure/lib/std/*.cure` at
  `site/` compile time. Module doc maps are keyed by name and
  grouped via a curated `@groups_for_modules` list. Modules added
  in future releases that are not in the curated list fall into
  the trailing `"Other"` bucket.
- **`CureSiteWeb.StdlibController`** + `stdlib_html/` templates --
  `/stdlib` lists every module, `/stdlib/:module` renders a single
  module page with a DaisyUI-styled two-pane layout and a GitHub
  "View source" link. The old hand-written
  `site/priv/pages/standard-library.md` is removed;
  `/standard-library` now 301-redirects to `/stdlib` via the new
  `CureSiteWeb.RedirectController`.
- **Navigation** -- the "Standard Library" sidebar entry points at
  `/stdlib`.

### Added -- REPL Markdown renderer upgrade

`Cure.REPL.Markdown` was a flat line-renderer; it is now a small
block-aware parser that produces richer ANSI output in `:help` and
`:doc` commands:

- Fenced code blocks (` ```lang...``` `) and indented code blocks.
- Bullet lists (`-`, `*`) and numbered lists (`1.`).
- Blockquotes (`> `).
- Inline backtick code, `**bold**`, `*italic*`, and `[text](url)`
  links rendered as `text (url)`.
- Horizontal rules (`---`, `***`) and blank-line paragraph
  separation.

The renderer remains NIF-free so `:help` keeps working inside the
escript (unlike the richer Marcli/MDEx path).

### Fixed -- Parser: consecutive doc-comment blocks across blank lines

`collect_all_doc_comments/1,2` now merges consecutive `##` blocks
separated by blank-line gaps (or by plain `#` comments dropped by the
lexer) with a paragraph break, and then binds the merged text to the
following definition. Previously, the second block was left dangling
as a stray `:doc_comment` token that would trip `parse_expr/2` with
an `unexpected doc_comment` error.

### Added -- Editor and highlighter alignment

- **`highlightjs-cure/`** -- ship a highlight.js language
  description for Cure, a demo page, and a minified bundle
  (`dist/cure.min.js`). Suitable for any site that uses highlight.js
  to syntax-highlight `.cure` snippets in blog posts and READMEs.
- **`vicure/`** -- vim/neovim plugin updated to Cure 0.28.2 grammar:
  `syntax/cure.vim`, `indent/cure.vim`, `ftplugin/cure.vim`,
  `ftdetect/cure.vim`, matching tests, and refreshed README /
  CHANGELOG.
- **`vscode-cure/`** -- the VS Code extension's TextMate grammar
  (`syntaxes/cure.tmLanguage.json`), language configuration, and
  entry point are re-aligned with the same Cure 0.28.2 grammar so
  highlighting, auto-indent, and bracket matching keep parity with
  vicure.

### Added -- REPL top-level declarations and signatures

The REPL session surface introduced during v0.28.1 and v0.28.2 is
promoted into a documented release surface:

- **`Cure.REPL.Session`** -- accumulates top-level declarations
  (`fn`, `local fn`, `type` ADT and alias, `rec`, `proto`, `impl`,
  `proof`) between submissions, synthesises a stable
  `:"Cure.Repl.Session"` module on the fly, and auto-prepends
  `use Repl.Session` to every expression module the REPL compiles.
  Redefinitions replace the matching entry in place, keyed by kind
  + name + arity.
- **`:defs` meta-command** lists installed declarations. `:reset`
  now also clears the session and unloads the synthesised module.
- **`Cure.Types.Checker.infer_expr/2`** grows an `:extra_bindings`
  keyword option. `Cure.REPL.Session.signatures/1` projects public
  `fn` entries into the `{name, {:fun, param_types, ret_type}}`
  shape the checker expects, and `:t` / `:effects` in the REPL now
  show the declared type/effects for session fns rather than
  `Any`.

### Added -- Documentation (on disk)

- **`docs/DOC.md`** -- authoritative on-disk reference for the new
  `cure doc` pipeline: `[doc]` / `[doc.groups_for_modules]`
  tables, `--title` / `--main` / `--extras` flags, Cure.Doc.Markdown
  placeholder interpolation and Makeup highlighting, the generated
  HTML layout, and the REPL markdown renderer.
- **`docs/TUTORIAL.md`** -- new Chapter 13 "Documenting your
  modules" walks through `##` doc comments, `## Examples` blocks,
  `Cure.toml [doc]` configuration, and `cure doc`.
- **`docs/LANGUAGE_SPEC.md`** -- doc-comment grammar clarified:
  consecutive `##` blocks separated by blank lines merge with a
  paragraph break, `###` fences accept full Markdown with placeholder
  interpolation.
- **`docs/STDLIB.md`** -- introduction reworked to reference
  `/stdlib` on the website and the Examples blocks under each
  module.
- **`site/priv/pages/tooling.md`** -- `cure doc` section updated to
  the v0.29.0 surface.
- **`site/priv/pages/roadmap.md`** -- new Implemented: v0.29.0 entry.
- **`site/priv/posts/2026/04-23-cure-v0.29.0.md`** -- release blog
  post.

### Changed

- `mix.exs` version bumped to `0.29.0`; `docs/DOC.md` added to the
  docs extras list.
- `extra_applications` unchanged; the doc pipeline uses
  `:inets` / `:ssl` / `:crypto` already declared for the registry
  client.

## [0.28.0] -- Talk Back

v0.28.0 closes feedback loops. The compiler now emits all parse errors
per file (not just the first), every name-resolution failure carries a
"did you mean?" suggestion, the formatter gains a colour diff view,
type errors get an interactive fix assistant (`cure bless`), FSMs and
actors can opt into time-travel journaling (`@record` + `cure replay`),
and the Playground gains an in-browser type-check panel and sandboxed
evaluator. A lurking type-checker bug that returned `List(U)` for
ill-typed polymorphic lambdas is fixed at the source.

### Fixed

- **Checker: lambda body errors silenced in `infer_and_unify_args`.**
  `:t Std.List.map(["1","2","3"], fn (x) -> x + 1)` previously returned
  `List(U)` because `infer_and_unify_args` swallowed errors from
  `infer_arg_with_expected` and substituted `:any`, leaving `U` unbound.
  The fix threads an error accumulator through `infer_and_unify_args`;
  when any argument expression is internally ill-typed the first error
  is propagated instead of returning the garbage return type.
- **Type.numeric?: named types and type variables treated as potentially
  numeric.** User-defined numeric aliases (`type Rate = {r: Float | ...}`)
  and polymorphic type variables (`T` in `fn(x: T) -> x + 1`) no longer
  produce false-positive arithmetic type errors.

### Added -- Parser

- **Error recovery (E063).** `parse_block_body` and `parse_program` now
  synchronise to the next statement boundary after every error-producing
  expression so a broken statement cannot consume tokens belonging to the
  next well-formed definition. New error code `E063 Parse Error
  (recovered)` documents the behaviour.

### Added -- "Did you mean?" suggestions

- Unbound variable errors include the closest in-scope name.
- Record field pattern errors include the closest declared field name.
- `cure <unknown-subcommand>` suggests the closest known command.
- REPL `:use <unknown-module>` warns and suggests the closest stdlib
  module name.
- REPL `:unknown-command` suggests the closest known meta-command.

### Added -- `cure fmt --diff`

`cure fmt --dry-run` (alias: `--diff`) shows a colour-annotated unified
diff for every file that would be reformatted without touching disk.
Exits 1 when any file has pending changes (CI-friendly).

### Added -- `cure bless`

New Socratic type-error assistant. For each type or refinement error
in a `.cure` file, `cure bless` displays the error, explains what went
wrong, and offers a concrete fix with a `[y/n/s]` prompt. On `y`, the
fix is applied and the checker is re-run to confirm resolution.

- New modules: `Cure.Bless`, `Cure.Bless.Advisor`.
- New Mix task: `mix cure.bless`.
- REPL `:bless <path>` command.

### Added -- Time-travel: `@record` + `cure replay`

`@record` decorator on a `fsm` container opts every transition into
`Cure.Observe.Journal`, which writes ETS entries and flushes them to
`.cure-trace/<pid>.journal`. `cure replay <path>` loads a journal file,
prints the event trace, and optionally replays it against a live FSM
with `--step` single-step mode.

- New modules: `Cure.Observe.Journal`, `Cure.Observe.Replay`.
- New Mix task: `mix cure.replay`.
- `Cure.FSM.Compiler` extended to detect `@record` and inject journal
  calls into the generated `handle_cast`.

### Added -- Playground v2

- **In-browser type checker.** `CureSiteWeb.PlaygroundLive` now runs
  `Cure.Types.Checker` on every debounced keystroke and renders results
  in a live type-check panel.
- **Sandboxed evaluator.** `CureSiteWeb.Eval` spawns an isolated BEAM
  process with `max_heap_size` and a 2-second kill timer, captures
  stdout, and returns the `main/0` return value. A "Run" button in the
  playground triggers it on demand.

### Added -- Error catalog

- **E063 Parse Error (recovered)** -- emitted implicitly when the
  parser skips tokens to reach the next statement boundary after a
  syntax error.

### Changed

- `mix.exs` version bumped to `0.28.0`.

## [0.27.0] -- See Your System Breathe

v0.27.0 is the observability-and-verification release. It turns the
v0.26.0 OTP application surface into something users can *watch*
running (`cure top`, `cure trace`, `Cure.OTel` spans), *reason
about* (`Cure.Temporal` LTL properties over FSMs,
`Cure.Protocol` session types between actors), and *fill in by hand*
(`cure synth` typed-hole suggestions). Three new stdlib modules
(`Std.CRDT`, `Std.Time`, `Std.Regex`) round out the practical
toolbox, and compiler errors now carry OSC 8 terminal hyperlinks so
file paths are clickable in WezTerm, Kitty, iTerm2, VTE, and Warp.
A companion LiveView Playground ships at
[`cure-lang.org/playground`](https://cure-lang.org/playground).

### Added -- Observability

- `Cure.OTel` -- OpenTelemetry-compatible span bridge on top of
  `Cure.Pipeline.Events`. Manual span helper `span/3`, cross-process
  context injection via `inject_ctx/1` + `extract_ctx/1`, pluggable
  exporter, configurable service name and sample ratio.
- `Cure.OTel.MemoryExporter` -- bundled in-memory ETS exporter for
  tests and the showcase example; exposes `all/0`, `flush/0`,
  `count/0`, `reset/0`.
- `Cure.Observe.Top` -- snapshot-based supervisor/actor/FSM reader
  with a text renderer. `Mix.Tasks.Cure.Top` exposes the output as
  `mix cure.top` (also `cure top`).
- `Cure.Observe.Trace` -- typed tracer wrapper over `:dbg` with
  per-function signature lookup from the new
  `Cure.Observe.Trace.Registry` ETS table. CLI surface via
  `mix cure.trace Module.fun/arity --duration N`.

### Added -- Verification

- `Cure.Temporal.Formula` -- LTL formula ADT with smart
  constructors and a pretty-printer.
- `Cure.Temporal.Parser` -- hand-written recursive-descent parser
  for the temporal DSL (`always`, `eventually`, `never`, `next`,
  `and`, `or`, `->`, `until`, `!`; multi-property scripts separated
  by `;` or newlines; parentheses for grouping).
- `Cure.Temporal.Checker` -- bounded model checker with explicit
  safety, liveness, `next`, and `until` semantics; produces
  concrete counterexample traces on violations.
- `Cure.Protocol` -- session-typed binary protocols between actor
  roles. Parser (`Cure.Protocol.Parser`), ADT
  (`Cure.Protocol.Script`), structural verifier
  (`Cure.Protocol.Verifier`) surfacing `E056`, and
  `participant_trace/2` that plugs into `Cure.Temporal.Checker`.

### Added -- Typed holes synthesis

- `Cure.Types.Synth` -- depth-budgeted enumeration of well-typed
  candidates for a given goal type and local context. Seeded with a
  hand-maintained subset of `Std.Core`, `Std.Option`, `Std.Result`,
  `Std.List`, `Std.Math`, `Std.String`, and `Std.Io`. Candidates are
  ranked by cost, filtered by a declared effect budget, and emitted
  through the new `:synthesis` pipeline stage.
- `Mix.Tasks.Cure.Synth` -- `mix cure.synth --goal T --ctx var=T`
  CLI driver that prints the top-`N` candidates.

### Added -- Stdlib

- `Std.Time` (14 functions) -- `Instant`, `Duration`, ISO 8601
  parsing/formatting, arithmetic, Unix conversions, smart duration
  constructors. Runtime: `:cure_std_time`.
- `Std.Regex` (7 functions) -- `compile`, `compile_bang`,
  `is_match`, `run`, `scan`, `replace`, `split` on top of `:re`.
  Invalid patterns surface as `E060 Regex Invalid`. Runtime:
  `:cure_std_regex`.
- `Std.CRDT` (5 CRDTs × 4 ops + `pn_decrement`) -- `GCounter`,
  `PNCounter`, `ORSet`, `LWWRegister`, `MVRegister` with
  commutative / associative / idempotent `*_merge/2`. Runtime:
  `:cure_std_crdt`.
- `Cure.Stdlib.Preload` updated to load the three new modules.

### Added -- Developer UX

- `Cure.Term.Hyperlink` -- OSC 8 terminal-hyperlink helper with a
  `TERM`-based allowlist (`wezterm`, `xterm-kitty`, `iterm`,
  `iterm2`, `vte`, `warp`) plus `NO_COLOR` and `CURE_HYPERLINKS`
  environment overrides. Wired into
  `Cure.Compiler.Errors.format_diagnostic/5` so every error location
  emits clickable links when the terminal supports them.
- `Cure.Doc.Mermaid` -- emits Mermaid source for FSM / sup / app
  containers ready to embed in `cure doc` HTML output.

### Added -- Playground

- `CureSiteWeb.PlaygroundLive` on the Cure website serves a
  two-pane LiveView editor with live Makeup-driven syntax
  highlighting at `/playground`.
- `site/priv/pages/playground.md` documents the current surface and
  what lands in v0.28 (type-check + sandboxed evaluator +
  WASM target).

### Added -- Documentation and examples

- `docs/OBSERVABILITY.md`, `docs/PROTOCOL.md`, `docs/TEMPORAL.md`,
  `docs/PLAYGROUND.md`.
- `docs/STDLIB.md` extended with `Std.Time`, `Std.Regex`,
  `Std.CRDT`.
- `examples/cure_atelier/` -- showcase project that exercises
  every v0.27.0 surface in a single compact test suite:
  `Std.CRDT.ORSet`, `Std.Time.Instant`, `Std.Regex`,
  `Cure.Protocol`, `Cure.Temporal`, `Cure.OTel`, `Cure.Types.Synth`,
  `Cure.Term.Hyperlink`.

### Added -- Error catalog

- **E056 Protocol Violation** -- role / reachability / projection
  failures inside a `protocol` declaration.
- **E059 Temporal Property Violated** -- with a minimal
  counterexample trace.
- **E060 Regex Invalid** -- bad pattern surfaced at compile or call
  time.
- **E061 Synthesis Budget Exhausted** -- warning emitted when
  `Cure.Types.Synth` runs out of depth without finding a candidate.
- **E062 Temporal Target Unknown** -- temporal formula references a
  state absent from the model.

### Changed

- `mix.exs` version bumped to `0.27.0`.
- `extra_applications` grew `:runtime_tools` so `:dbg` is visible
  to `Cure.Observe.Trace` without a separate load step.

## [0.26.0] -- Applications and Releases

v0.26.0 promotes the supervision surface from v0.25.0 into a full OTP
application lifecycle. A new `app` container declares the project's
OTP application directly in Cure source, cross-checked against
`Cure.toml`'s new `[application]` and `[release]` tables. The same
compiler cycle emits the `<name>.app` OTP resource file and a
`:"Cure.App.<Name>"` `Application`-behaviour module; a new
`cure release` subcommand (also available as `mix cure.release`)
packages the whole thing as a bootable BEAM release.

### Added -- `app` container

- `app Name` containers declare an OTP application with
  `vsn`, `description`, `root`, `applications`,
  `included_applications`, `registered`, `env` assignments and
  `on_start`, `on_stop`, `on_phase :name` lifecycle clauses. The
  clause grammar is shared with `actor` / `sup` (pattern tuple +
  optional `when` guard + body).
- `app` is a *contextual* soft keyword, treated the same way as
  `sup`: the lexer keeps it as an identifier so existing Cure
  programs that use `app` as a field or variable name keep
  compiling; the parser dispatches `app <Name>` to the application
  container parser only at statement-prefix position.
- `Cure.App.Compiler` emits a loaded `Application`-behaviour
  module via `Code.compile_string/2`; the codegen dispatcher returns
  `{:ok, {:app, module()}}`. When `:output_dir` is provided, the
  bytecode and an OTP `<name>.app` resource file are persisted
  alongside every other Cure module.
- `Cure.App.Verifier` enforces exactly one `app` container per
  project, matches its name against `[application].name` in
  `Cure.toml` (both sides are normalised through
  `Macro.underscore/1`), cross-checks start-phase names, and
  validates that `root = ...` resolves to a known module atom.
- `Cure.App.Resource` emits the OTP `<name>.app` resource file from
  the container's metadata merged with `[application]`.
- `Cure.App.Builtins` bridges `Std.App` to `:application` with
  plain-atom returns.

### Added -- Release builder

- `Cure.Release` assembles a bootable BEAM release under
  `_build/cure/rel/<name>/`:
  `lib/<app>-<vsn>/ebin/*.{beam,app}`, `releases/<vsn>/<name>.rel`,
  `releases/<vsn>/start.boot`, `releases/<vsn>/start.script`,
  `releases/<vsn>/sys.config`, `releases/<vsn>/vm.args`, and a
  POSIX `bin/<name>` runner script.
- The boot script seeds its application closure with `:kernel`,
  `:stdlib`, `:compiler`, `:elixir`, the project's own application
  atom, and every entry in `[release].applications`; out-of-tree
  dependencies are loaded from the live code path.
- `--include-erts` (or `[release].include_erts = true`) bundles the
  running ERTS into the release directory.
- The runner script uses `${ERL:-erl}` so the release can be tested
  against any Erlang VM on `PATH`.
- `Mix.Tasks.Cure.Release` exposes the subcommand as
  `mix cure.release`.

### Added -- `Cure.toml` sections

- `[application]` -- `name`, `vsn`, `description`, `applications`,
  `included_applications`, `registered`, `start_phases`, plus nested
  `[application.env]`. `name` is the source of truth for the emitted
  `<name>.app`; `applications` is merged with the container's own
  list; `start_phases` is authoritative and every entry must have a
  matching `on_phase :name` clause.
- `[release]` -- `name`, `vsn`, `include_erts`, `applications`,
  `vm_args`, `sys_config`. `Cure.Release` threads these values into
  release assembly.
- The TOML parser accepts a minimal subset: scalar string / integer /
  bool / array-of-strings values, plus nested tables for
  `[application.env]`.

### Added -- Standard library

- `lib/std/app.cure` -- `Std.App`: `ensure_all_started/1`,
  `start/1`, `stop/1`, `get_env/2`, `get_env/3`, `put_env/3`,
  `which_applications/0`, `loaded_applications/0`,
  `start_phase/3`. Thin wrappers over `:application` that return
  plain atoms and values rather than OTP's tagged-tuple shapes.

### Added -- Documentation and examples

- `docs/APP.md` -- full reference for the `app` container,
  `Cure.toml` `[application]` / `[release]` sections, `cure release`
  subcommand, `Std.App`, and error codes.
- `docs/TUTORIAL.md` -- new Chapter 13 "Applications" covering the
  whole lifecycle end to end.
- `docs/LANGUAGE_SPEC.md` -- new "Applications (v0.26.0)" section and
  `app` soft-keyword note.
- `docs/STDLIB.md` -- new `Std.App` section.
- `docs/SUPERVISION.md` -- cross-references to `docs/APP.md` and
  `examples/cure_forge/`.
- `examples/cure_forge/` -- fully-fledged showcase: an
  `app CureForge` container with `vsn`, `description`, `env`,
  `applications`, `on_start`, `on_stop`, and a `:warm_cache` start
  phase; a `sup Forge.Root` supervision tree; a metrics actor, a
  logger actor, a queue actor, and a pool actor cooperating through
  the Melquiades Operator `<-|`.
- `site/priv/pages/applications.md` -- user-facing reference on the
  Cure website.
- `site/priv/posts/2026/04-21-cure-v0.26.0.md` -- release blog post.

### Added -- Error catalog

- **E051 Duplicate Application** -- more than one `app` container in
  a project, or a name mismatch against `[application].name`.
- **E052 Missing Application** -- `cure release` invoked with no
  `app` declared.
- **E053 Start Phase Mismatch** -- TOML and container disagree on
  phase names.
- **E054 Unresolved Root Supervisor** -- `root = ...` does not
  resolve to a known module reference.
- **E055 Release Build Failed** -- wraps `:systools.make_script/2`
  or release-write I/O errors.

### Changed

- `mix.exs` version bumped to `0.26.0`. `Cure.CLI` banner and
  `cure version` output updated accordingly.
- `cure new --app` scaffolds a project with a minimal `app`
  container, a `sup` root, and the matching `[application]` /
  `[release]` sections in `Cure.toml`.

## [0.25.0] -- Typed Supervision Trees

v0.25.0 turns Cure into a first-class language for writing OTP-style
supervision trees. The release introduces a typed send operator --
the Melquiades Operator `<-|` (unicode alias `✉`) -- a typed `actor`
container that compiles to a live `GenServer` module, and a `sup`
container that compiles to a verified `Supervisor` behaviour module.
A small stdlib surface (`Std.Actor`, `Std.Process`, `Std.Supervisor`)
exposes the runtime from Cure source.

### Added -- Melquiades Operator

- `pid <-| message` sends `message` to `pid`, returning the message.
  The unicode form `✉` is interchangeable with the ASCII form; the
  lexer preserves the author's choice via a `:melquiades_form` meta
  key so the printer round-trips it faithfully.
- Non-associative operator binding one notch below `|>` so pipelines
  feed naturally into sends.
- `send target, msg` keyword form desugars to the same `{:send, ...}`
  MetaAST node so one codegen path handles both forms.
- Codegen lowers to Erlang's `!` operator (`{:op, Line, :!, ...}`).
- Effect inference: `<-|` attracts the `:state` effect.

### Added -- Typed primitives

- `Pid(Inbox)` is a new compound type constructor. Bare `Pid` in
  source resolves to `{:pid, :any}`, the top of the covariant family.
- `Ref` is a new primitive for monitor references.
- The type checker has a dedicated clause for `{:send, ...}` that
  unifies the message type against the receiver's declared inbox and
  emits `E046 Inbox Mismatch` when the types disagree.

### Added -- Actors

- `actor Name with <init>` declares a typed process. Lifecycle hooks
  `on_start`, `on_message`, `on_stop` reuse the FSM callback-clause
  machinery (pattern tuple + optional `when` guard + body).
- `Cure.Actor.Compiler` emits a `GenServer` module loaded eagerly;
  the codegen dispatcher returns `{:ok, {:actor, module()}}` for
  actor containers.
- `Cure.Actor.Runtime` (GenServer) tracks spawned actors in an ETS
  registry, monitors each pid, and cleans up on `DOWN`. Started by
  `Cure.Application` alongside `Cure.FSM.Runtime`.
- `Cure.Actor.State` struct holds `caller`, `meta`, `payload`; exposes
  `notify/1` / `notify_self/1` for the sugar available inside hook
  bodies.
- `Cure.Actor.Builtins` bridges `Std.Actor` to the runtime.

### Added -- Supervisors

- `sup Name` declares a supervisor container. Inline settings
  (`strategy`, `intensity`, `period`) and a `children` block with
  per-line child specs (`Module as id (restart: ..., shutdown: ...)`).
- `Cure.Sup.Verifier` rejects invalid strategies / restarts /
  shutdowns, non-positive period, duplicate child ids, and trivial
  cycles. Emits `:sup_verifier` pipeline events.
- `Cure.Sup.Compiler` emits a `Supervisor`-behaviour module via
  `Code.compile_string/2`; the compiler returns
  `{:ok, {:supervisor, module()}}`.
- `Cure.Sup.Runtime` wraps the compiled module with a lazy ETS
  registry (`start/1,2`, `stop/1`, `lookup/1`, `which_children/1`,
  `list/0`).
- `Cure.Sup.Builtins` bridges `Std.Supervisor` to the runtime.
- `sup` is a *contextual* keyword: the lexer keeps it as an
  identifier so existing Cure programs that use `sup` as a field or
  variable name (for instance the superdiagonal row in a tridiagonal
  system) keep compiling; the parser dispatches on `sup <Name>` only
  at statement-prefix position.

### Added -- Standard library

- `lib/std/actor.cure` -- `spawn/1`, `spawn_with_payload/2`,
  `spawn_named/2`, `stop/1`, `send/2`, `get_state/1`, `is_alive/1`,
  `lookup/1`.
- `lib/std/process.cure` -- `link/1`, `unlink/1`, `monitor/1`,
  `demonitor/1`, `trap_exit/1`, `exit/2`, `self/0`, `is_alive/1`.
- `lib/std/supervisor.cure` -- `start/1`, `start_with/2`, `stop/1`,
  `which_children/1`, `count_children/1`, `lookup/1`, `list/0`.
- New Elixir bridges: `Cure.Process.Builtins` (`proc_monitor/1`,
  `proc_trap_exit/1`) and `Cure.Sup.Builtins`.

### Added -- Documentation & examples

- `docs/SUPERVISION.md` -- full reference for the new surface.
- `examples/cure_colony/` -- minimal typed supervision tree demo.
- Error catalog entries `E045` -- `E050` covering untyped sends,
  inbox mismatches, unknown children, cycles, non-exhaustive actor
  handlers, and invalid supervisor strategies.

### Added -- Tests

- `test/cure/compiler/melquiades_lexer_test.exs`,
  `melquiades_parser_test.exs` -- lexer, parser, printer, effect, and
  runtime coverage for the Melquiades Operator.
- `test/cure/types/typed_pid_test.exs` -- `Pid(Inbox)` covariance,
  inbox mismatch diagnostics.
- `test/cure/actor/actor_test.exs` -- actor parsing, codegen,
  spawn/send/stop, notify/1, runtime registry.
- `test/cure/sup/sup_test.exs` -- supervisor parsing, verifier,
  compiler, runtime, and actor-child composition.

## [0.24.0] -- The REPL You Deserve

v0.24.0 is the release where the interactive cycle catches up with
the rest of the language. The legacy `IO.gets`-backed REPL, present
since v0.15.0 and only lightly touched in v0.17.0, has been rewritten
whole-cloth on top of a raw-mode line editor with live syntax
highlighting, persistent history, incremental reverse search, Tab
completion, a minimal vi mode, and a Marcli-rendered `:help`. The
compiler itself is untouched; every change in this release is on the
read-eval-print side.

### Added -- REPL overhaul

The interactive REPL (`cure repl`) has been rewritten on top of a
raw-mode line editor with live syntax highlighting.

- `Cure.REPL.Terminal` puts stdin in cbreak/no-echo mode via `stty`,
  restores it on any exit path, and decodes raw byte streams into
  high-level key events (arrows, `Home`/`End`/`Delete`, `PgUp`/`PgDn`,
  `Ctrl+<letter>`, `Alt+<char>`, `Ctrl+Arrow`, F-keys, bracketed
  paste).
- `Cure.REPL.LineEditor` is a pure-function line buffer supporting
  cursor movement, word-wise movement, kill ring, yank, transpose,
  case changes, undo/redo and a minimal vi normal mode (`h/j/k/l`,
  `w/b/e`, `0`/`^`/`$`, `i/a/I/A`, `x`, `D`, `C`, `u`).
- `Cure.REPL.History` adds proper `Up`/`Down` navigation with draft
  preservation, consecutive-duplicate dedup, a 10,000 entry cap, and
  atomic write-and-rename persistence.
- `Cure.REPL.Search` implements `Ctrl+R` / `Ctrl+S` incremental
  reverse and forward search with an inverse-video status line and
  accept-and-edit semantics.
- `Cure.REPL.Completer` offers `Tab` completion for meta-commands,
  file paths (for `:load`/`:save`/`:edit`), loaded modules (for
  `:use`/`:doc`), theme / mode / colour argument literals, and Cure
  keywords.
- `Cure.REPL.Highlight` pipes input through `Makeup.Lexers.CureLexer`
  and `Marcli.Formatter` for live ANSI syntax highlighting, cached by
  buffer hash.
- `Cure.REPL.Theme` defines `:dark` (default), `:light`, and `:mono`
  presets; `NO_COLOR`, non-tty output, and `TERM=dumb` automatically
  drop to `:mono`.
- New meta-commands: `:history [n]`, `:search term`, `:clear`,
  `:save path`, `:edit`, `:time expr`, `:bench expr [n]`, `:ast expr`,
  `:theme dark|light|mono`, `:mode emacs|vi`, `:color on|off`. All
  existing meta-commands are preserved.
- `:help` output is rendered via `Marcli.render/2` so the key bindings
  table arrives as ANSI-styled Markdown.
- Non-tty stdin (CI, pipes) short-circuits to a legacy `IO.gets` loop
  so test automation continues to work.

### Added -- Dependencies

- `{:marcli, "~> 0.3"}` -- Markdown-to-ANSI renderer / Makeup ANSI
  formatter.
- `{:makeup, "~> 1.2"}` -- explicit dependency so `Makeup.Registry` is
  available at runtime.
- `{:makeup_cure, "~> 0.1"}` -- Cure language lexer for Makeup.

### Added -- Documentation

- `docs/REPL.md` -- full key-bindings table, meta-command reference,
  configuration, environment variables, vi-mode subset.
- `site/priv/pages/repl.md` -- user-facing REPL reference on
  [cure-lang.org](https://cure-lang.org) with the full key-bindings
  table and meta-command reference.

### Changed

- `mix.exs` version bumped to `0.24.0`. `Cure.CLI` banner and
  `cure version` output updated accordingly.
- `cure repl` defaults to raw-mode when stdin is a tty; the legacy
  line-mode loop is kept behind `Cure.REPL.start/1` `raw: false` and
  used automatically when the terminal cannot be put into cbreak mode.
- `Cure.Stdlib.Preload.preload/1` is invoked from `Cure.REPL.start/1`
  so expressions can reference `Std.List`, `Std.Math`, etc. without
  an explicit `:use`.

### Deferred to v0.25.0

- Profile-guided optimisation wiring between `Cure.Profiler` and the
  inliner / pattern-aware SMT encoder.
- First-class Helix / Zed configurations and a VS Code extension
  upgrade to track the current LSP surface.
- REPL-level hot reload that recompiles-and-rebinds on every file
  save for long-running REPL sessions.

## [0.23.0] -- Packaging, Proof, and Polish

v0.23.0 ships the remote package-registry story that has been
rescheduled three releases in a row. It lands alongside a broad
ergonomics upgrade -- property-based shrinking, two new stdlib
modules, a doctor diagnostic, a project-wide fixer, a telemetry
bridge, coverage reporting -- and the `cure_brainloop` showcase
example that exercises every Cure feature in a single project.

### Added -- Remote package registry

- `Cure.Project.Registry` -- read-only HTTP client over OTP's
  `:httpc`. Implements the full endpoint set from
  `docs/PACKAGE_REGISTRY.md`: `GET /packages/:name`,
  `/packages/:name/:version`, `/packages/:name/:version/tarball`,
  `GET /packages?q=<query>`, `GET /log`, `POST /packages`. Content-
  addressed caching under `~/.cure/registry_cache/`. Emits `:registry`
  pipeline events for every network call (`:fetch_start`, `:fetch_ok`,
  `:fetch_failed`, `:cache_hit`, `:hash_mismatch`).
- `Cure.Project.Lock` -- `Cure.lock` reader and writer. Grows a
  `resolve_with_lock/2` entry point so `cure deps` can reuse the
  lockfile when every constraint is still satisfied.
- `Cure.Project.resolve_deps/1` extended: dependencies without `path`
  or `git` are treated as registry dependencies -- fetched, hash-
  checked, unpacked under `_build/deps/<name>-<version>/`, and added
  to the code path.
- `Cure.Project.Signing` -- Ed25519 key management on top of OTP
  `:crypto`. Keys under `~/.cure/keys/` with tight file perms. Signs
  `name || NUL || version || NUL || sha256(tarball)`. Verifies every
  install against the trusted-key list.
- `Cure.Project.Transparency` -- client-side verifier for the
  Rekor-style publish log. Canonicalises entries by key-sorted JSON,
  validates the Merkle-like hash chain, degrades gracefully to
  `{:ok, :unverified}` when `/log` is unreachable. Promotable to a
  hard failure with `config :cure, strict_transparency: true`.
- `Cure.Project.Publisher` -- assembles the package tarball, signs,
  and uploads. `build_hex_tarball/1` emits a Hex-compatible tarball
  (`VERSION` / `CHECKSUM` / `metadata.config` / `contents.tar.gz`)
  for cross-publishing via `mix hex.publish package --replace`.
- `Cure.Project.Json` -- minimal internal JSON codec used by every
  packaging module so the compiler has no runtime JSON dependency.

### Added -- CLI

- `cure publish`, `cure publish --dry-run`, `cure publish --hex`.
- `cure search <query>`, `cure info <name>[:version]`.
- `cure keys generate <handle>`, `cure keys list`.
- `cure doctor` -- environment / project / source health report,
  suitable as a CI gate.
- `cure fix [--dry-run]` -- project-wide safe rewrites
  (`normalize_line_endings`, `strip_trailing_whitespace`,
  `strip_mixed_tabs`, `collapse_blank_lines`,
  `ensure_trailing_newline`).
- `cure test --cover` -- runs the self-hosted test suite under
  `:cover`, emits an HTML index under `_build/cure/cover/`.
- New switches: `--dry-run`, `--hex`, `--handle`, `--token`,
  `--cover`, `--strict`, `--registry`.

### Added -- Standard library (brings total to 27)

- **`Std.Json`** (`lib/std/json.cure`) -- JSON encoder + decoder via
  the `Value = Null | Bool(Bool) | Num(Float) | Str(String) |
  Arr(List(Value)) | Obj(List((String, Value)))` ADT. Runtime is
  `:cure_std_json`. Companion to the v0.21.0 `@derive(JSON)` target.
- **`Std.Http`** (`lib/std/http.cure`) -- thin wrapper over `:httpc`.
  `get/1`, `get/2`, `post/3`, `head/1` returning `Result(Response,
  HttpError)`. Runtime is `:cure_std_http`.
- **`Std.Gen.shrink_int/1`**, **`shrink_list/1`**, **`shrink/1`** --
  shrinking primitives backing the property-based tests. Runtime is
  `:cure_std_gen`.
- **`Std.Test.forall_shrunk/3`** and
  **`Std.Test.forall_shrunk_default/2`** -- shrinking-aware property
  runner. Raises `{:property_failed_with_shrunk, value}` on the
  minimised counterexample. Runtime is `:cure_std_test`.

### Added -- Infrastructure

- `Cure.Telemetry` -- subscribes to every stage of
  `Cure.Pipeline.Events` and re-emits `[:cure, :pipeline, <stage>,
  <event_type>]` events through OTP's optional `:telemetry` library.
  Silent no-op when `:telemetry` is not on the load path.
- `Cure.Doctor` -- structured diagnostic (Elixir / OTP / Z3 /
  registry URL / telemetry / project / source health). Non-zero exit
  on any warning or error finding.
- `Cure.Fix` -- project-wide safe rewrites via `Cure.Fix.run/2`.
- `Cure.Cover` -- instrumentation harness around OTP's `:cover`;
  HTML report under `_build/cure/cover/`.

### Added -- Example project

- `examples/cure_brainloop/` -- the top-pick showcase from
  `stuff/ideas_for_cure_apps.md`. A toy expression-language
  interpreter with a REPL driven by a Cure FSM. Exercises ADTs,
  records, refinement types, protocols, effects, FSM callback mode,
  OTP interop, FFI, and the new `Std.Json` module in one coherent
  codebase. Ships with an ExUnit suite covering lexer, parser,
  evaluator, and environment semantics.

### Added -- Error catalog

Five new codes `E038` -- `E042`:
- `E038 Registry Fetch Failed`
- `E039 Registry Hash Mismatch`
- `E040 Registry Package Not Found`
- `E041 Registry Signature Invalid`
- `E042 Transparency Log Unreachable`

### Added -- Documentation

- `docs/PACKAGE_REGISTRY.md` rewritten from a v0.17.0-era design
  document into the authoritative shipped contract.
- `docs/PUBLISHING.md` -- end-to-end walkthrough for publishing a
  Cure package, including Hex cross-publishing and strict
  transparency-verification mode.

### Changed

- `mix.exs` version bumped to `0.23.0`. `:telemetry, "~> 1.3"`
  declared as an optional dependency. `:inets`, `:ssl`, `:crypto`,
  `:public_key` listed as `extra_applications` so the registry and
  signing code work out of the box.
- `Cure.toml` dependency parser recognises three forms:
  `name = { path = "..." }`, `name = { git = "...", tag = "..." }`,
  and the new bare `name = "<constraint>"` for registry deps.
- `cure deps` prefers the lockfile path when every constraint is
  still satisfied by the locked versions; otherwise falls back to
  fresh resolution and rewrites `Cure.lock`.

### Tests

- New test modules under `test/cure/project/`: `json_test.exs`,
  `lock_test.exs`, `signing_test.exs`, `transparency_test.exs`,
  `registry_test.exs`.
- New `test/cure/doctor_test.exs`, `test/cure/fix_test.exs`,
  `test/cure/telemetry_test.exs`.
- New `test/cure/stdlib/cure_std_json_test.exs`,
  `cure_std_gen_test.exs`, `cure_std_test_test.exs`.
- `examples/cure_brainloop/test/cure_brainloop_test.exs` covers the
  interpreter end-to-end.

## [0.22.0] -- Loose Ends

v0.22.0 closes three language-surface gaps that the v0.20.0 / v0.21.0
work scaffolded but deliberately left open, and elevates the v0.21.0
"Unreleased" first-class FSM overhaul into a shipped release. Lambdas
gain explicit multi-statement body shapes that work inside argument
lists, binary comprehension generators land (`for <<b <- buf>>`), and
trailing `rest::binary` segments now carry a `byte_size`-based
refinement so subsequent binary patterns type-check without having to
re-assert every invariant.

### Added -- Multi-statement lambda bodies

- `Cure.Compiler.Parser.parse_lambda_body/2` routes the body through
  a new `parse_lambda_block_body/2` dispatcher with four shapes:
  indented block (unchanged from v0.19.0), single expression
  (unchanged), brace-delimited `fn (x) -> { s1; s2; final }`, and
  `end`-terminated `fn (x) -> s1; s2; final; end`. The brace and end
  forms work inside argument positions where the lexer suppresses
  newlines and `:indent`/`:dedent` are never emitted.
- Both new forms compile to the same `{:block, meta, exprs}` AST
  node the indented form produces; `:block_shape` meta keys
  (`:brace` or `:end`) let the Printer and algebra formatter
  round-trip the author's chosen shape.
- `end` is now a reserved keyword (previously unused in `.cure`
  source). The lexer's `@keywords` list grows by one.
- `E035 Lambda Block Unterminated` error-catalog entry for an
  unclosed `{` or missing `end` inside a lambda body.

### Added -- Binary comprehension generators

- `Cure.Compiler.Parser.parse_generator_or_filter/1` dispatches on
  `:binary_open` and delegates to a new `parse_binary_generator/1`
  path. The resulting AST is `{:binary_generator, meta, [pattern,
  source]}` where `pattern` is the v0.21.0 `{:literal, [subtype:
  :bytes], segments}` shape and the segments are parsed at BP 42 so
  the trailing `<-` of the generator is not mis-tokenised as a
  less-than comparison inside `<<...>>`.
- `Cure.Compiler.Codegen.compile_comprehension/3` lowers
  `:binary_generator` qualifiers to Erlang's `b_generate` form
  inside the existing `:lc` comprehension so mixed qualifier lists
  still compile uniformly.
- `Cure.Types.Checker.do_infer/2` on `:comprehension` now binds
  every qualifier's pattern variables via `bind_pattern_vars/3` so
  the comprehension body type-checks with the generator variables
  in scope.
- `E036 Binary Comprehension Source Not Bitstring` error-catalog
  entry.

### Added -- `byte_size` arithmetic refinements

- `Cure.SMT.Translator` speaks `byte_size/1` as an uninterpreted
  `(Int) -> Int` function. Queries that reference `byte_size`
  prepend `(declare-fun byte_size (Int) Int)` and switch to the
  `QF_UFLIA` logic automatically.
- `Cure.Types.PatternRefinement.narrow/2` rewrites its binary-
  segment branch. Trailing `rest::binary` (`::bytes`, `::bitstring`,
  `::bits`) tails receive a refinement whose predicate captures
  `byte_size(__value__) == byte_size(__scrutinee__) - sum_of_preceding`,
  where the sum is the byte-aligned count of preceding segments. When
  any preceding segment's size cannot be linearised, the tail stays
  bound to plain `:bitstring` and the pipeline emits a
  `:refinement_ignored` event under code `E037`.
- `E037 Binary Segment Size Non-Linear` error-catalog entry.

### Added -- First-class FSM handling
- `Cure.FSM.State` -- the canonical runtime state record carried by
  every callback-mode FSM. A single struct with three fields:
  `:caller` (pid notified by lifecycle hooks), `:meta` (FSM-private
  bookkeeping), and `:payload` (user-visible domain value). Exposes
  `from_init/1`, `merge/2`, `notify/2`, `notify_self/1`, and the
  process-dictionary helpers `register_self/1` and `current/0`.
- Callback-mode FSMs generated by `Cure.FSM.Compiler` now store a
  `%Cure.FSM.State{}` as their primary state. The `start_link/1` entry
  point accepts three init shapes: a pre-built struct, a keyword list
  or map with `:caller`/`:meta`/`:payload` keys, or any bare value
  (treated as the initial `:payload` for backward compatibility).
- `on_transition` clauses now receive the struct as their 4th argument
  (`(current_state, event, event_payload, %FsmState{}) -> ...`) and
  may return either a full struct, a partial map containing
  `:payload` / `:meta` keys (merged into the current struct), or any
  bare value (interpreted as the new payload). The `:__same__` return
  path is unchanged.
- `on_enter`, `on_exit`, `on_failure`, `on_timer` receive the struct
  too.
- Two new lifecycle blocks: `on_start` (invoked inside `init/1`; may
  return `:ok`, `{:ok, full_or_partial_state}`) and `on_stop` (invoked
  from `terminate/2`).
- Three new `fsm` annotations:
  - `@initial :state_name` -- override the initial state.
  - `@notify_transitions` -- after every successful transition, send
    `{:cure_fsm, pid, {:transition, from, event, to, payload}}` to the
    caller.
  - `@auto_caller` -- when `:caller` is not explicitly provided, fall
    back to the spawning process registered via
    `:cure_fsm_spawner` in the FSM's process dictionary.
- Event payloads are a first-class concept: generated callback-mode
  FSMs expose `send_event/3` that wraps the event + payload into the
  `{:event, event, payload}` tuple already expected by `handle_cast`.
  `Cure.FSM.Runtime.send_event/3` and `Cure.FSM.Builtins.fsm_send_with/3`
  surface the same.
- `Std.Fsm` (`lib/std/fsm.cure`) grows `spawn_with_payload/2`,
  `spawn_with/2`, `send_with/3`, `full_state/1`, `notify/1`, and
  `caller/1` for full caller/meta/payload control from Cure.
- Inside any lifecycle hook body, a bare `notify(msg)` call reaches
  the FSM's `:caller` (implemented as a private helper in the
  generated module, resolving to `Cure.FSM.State.notify_self/1`).
- `Cure.FSM.Runtime.spawn_fsm/2` accepts `:caller`, `:meta`,
  `:payload`, `:init`, and the legacy `:data`. By default the
  spawning process is installed as the FSM's caller, so notifications
  reach the expected pid without ceremony.
- `Cure.FSM.Runtime.get_fsm_state/1` and the generated FSM module's
  `get_fsm_state/1` expose the full struct (not just the payload).
- `Cure.FSM.Runtime.send_event/2,3` routes through the target FSM
  module's own `send_event/2,3` when available, so simple-mode
  (`gen_statem`) FSMs continue to receive bare event atoms, while
  callback-mode FSMs receive the `{:event, event, payload}` tuple.

### Changed -- cure_turnstile example
- `examples/cure_turnstile/cure_src/turnstile.cure` now owns every bit
  of state (coin count in `:payload`, passage count in `:meta`) and
  opts into `@notify_transitions`. The Elixir wrapper
  (`lib/cure_turnstile.ex`) no longer wraps a host GenServer: it just
  calls `Runtime.spawn_fsm`, forwards events, and exposes a `stats/1`
  helper that reads the `%FsmState{}` struct.

### Added -- Tests
- `test/cure/fsm/fsm_first_class_test.exs` -- 21 tests covering the
  struct helpers, the three `start_link/1` init shapes, `send_event/3`
  with payload, `@notify_transitions`, `on_start`, and
  `Cure.FSM.Runtime.spawn_fsm` option mapping.
- Turnstile test suite updated for the struct-backed state and
  extended with a `@notify_transitions` receive assertion.

### Notes on backward compatibility
Legacy callback-mode FSMs that accessed the 4th argument as a bare
data term continue to compile -- the return-value contract still
accepts bare values, which are interpreted as the new payload with
`:caller` and `:meta` left untouched. However, any code that reached
into the handler's 4th argument directly (e.g. `data + 1`) must now
destructure the struct (`%{payload: n}` -- map pattern against the
struct works because structs are maps) to read the underlying payload.
Simple-mode (`gen_statem`) FSMs are entirely unchanged.

`end` is a new reserved keyword. No `.cure` file in the stdlib or
examples uses `end` as an identifier, but third-party code that
does will need to rename the binding.

### Numbers

- 1114 tests pass (up from 1078; 3 doctests + 1111 tests);
  `mix credo --strict`: 0 issues across 142 source files;
  `mix cure.check.stdlib`: 25/25; `mix cure.check.examples`:
  44/44 (up from 40/40 -- 4 new example files:
  `lambda_block.cure`, `binary_comprehension.cure`,
  `byte_size_refinement.cure`, and the first-class FSM example).

### Deferred to v0.23.0

- Remote package-registry index service, publication signing, and
  Hex.pm cross-publishing -- the `Cure.Project.Registry` HTTP
  client, Ed25519 archive signing, and `cure publish --hex`
  export path remain rescheduled for v0.23.0.

---
## [0.21.0] -- Through the Segments

v0.21.0 turns the v0.20.0 AST scaffolding into user-visible features
and clears three language gaps that surfaced during the v0.20.0
cycle. The headline is full Erlang-style destructuring of binaries
in `match`, multi-clause function heads, and `let` bindings, with a
dedicated exhaustiveness pass and the corresponding `E031`
diagnostic. ADT constructor payloads now accept function arrows,
`type` ADT declarations parse multi-line, `let` bindings admit deep
destructuring, the algebra pretty-printer is promoted to be the
default formatter, and three new `@derive` targets (Functor,
Monoid, JSON) land on top of the existing Show/Eq/Ord trio.

### Added -- Binary destructuring

- `Cure.Types.Checker.bind_pattern_vars/3` grows a `:bin_segment`
  clause. Every `<<...>>` pattern in `match` arms, multi-clause
  function heads, and `let` bindings now introduces its inner
  variables with the type implied by the segment specifier:
  `integer`/`size(n)` -> `Int`, `float` -> `Float`,
  `utf8`/`utf16`/`utf32` -> `Char`,
  `binary`/`bytes`/`bitstring`/`bits` -> `Bitstring`.
- `Cure.Types.PatternChecker.check_binary_exhaustiveness/2` --
  dedicated Maranget-lite coverage analysis over a sequence of
  binary-pattern arms. A top-level wildcard, or the combination of
  an empty-binary arm and an open-ended tail arm, covers the
  scrutinee; otherwise a concrete witness (`"<<>>"` or
  `"<<_, _rest::binary>>"`) is reported under code `E031`.
- `Cure.Types.PatternRefinement.narrow/2` grows a binary-literal
  branch that narrows the scrutinee type through the segments and
  returns the variable bindings separately.
- `E031` Binary Pattern Not Exhaustive error-catalog entry with
  example and fix guidance.

### Added -- Let destructuring

- `let` bindings reuse the v0.18.0 deep-destructuring engine.
  `let Ok(x) = expr`, `let %[a, b] = pair`, `let [h | t] = xs`,
  `let Point{x, y} = p`, and `let <<tag, _::binary>> = buf` all
  bind the right variables with the right narrowed types.
- Non-exhaustive `let` patterns emit code `E034` as a warning; the
  binding still compiles, and Erlang's `=` raises at runtime on a
  failed match. Setting `partial: true` on the assignment metadata
  suppresses the warning.
- `E034` Let Pattern Not Exhaustive error-catalog entry.

### Added -- Multi-line `type` ADT declarations

- `parse_type_def/1`, `parse_type_variant/1`, and
  `parse_more_variants/1` accept the canonical multi-line ADT
  layout with leading `|` on every continuation line, or with the
  first variant on the same line as `=` and subsequent variants
  marked with `|`. An optional wrapping `:indent`/`:dedent` pair
  emitted by the lexer is absorbed by the type-def recogniser.
- `E033` Multi-line Type Layout Invalid error-catalog entry.

### Added -- ADT function-type payloads

- Validated: constructor payloads accept arbitrary type
  expressions including function arrows
  (`type Callback = On(Int -> Int) | Off` and
  `type Transform = Morph((Int, Int) -> Int) | Id`). Function-typed
  payloads compile to first-class functions and are callable from
  inside match arms.
- `E032` Function Type Payload Invalid error-catalog entry reserved
  for the case where a variant payload is not a resolvable type
  expression.

### Added -- `@derive(Functor, Monoid, JSON)`

- `Cure.Types.Derive.derive/3` gains three new targets:
  - `:functor` emits `fmap(x, f)` that applies `f` to every field.
    Intended for single-parameter records; works on any record.
  - `:monoid` emits `combine(a, b)` that pairwise combines every
    field with the `<>` operator. Users supply `empty/0`
    separately; the derivation does not guess a neutral element.
  - `:json` emits `to_json(x)` that renders a record as a JSON
    object string with field names as JSON keys. `from_json/1`
    is reserved for a future release.
- `can_derive?/1` extended accordingly.

### Added -- Algebra formatter is the default

- `cure fmt` now runs the Wadler/`Inspect.Algebra`-style pretty
  printer from v0.20.0 by default. The legacy byte-level formatter
  remains available via `cure fmt --safe`. `cure fmt --algebra`
  stays as a synonym for the default. `cure fmt --check` routes
  through the same algebra formatter so CI agrees with interactive
  use.

### Added -- Multi-clause parameter destructuring

- `Cure.Types.Checker.check_multi_clause/7` routes every clause
  parameter through `bind_pattern_vars/3` instead of only binding
  bare variables. ADT constructors, tuples, cons patterns, record
  patterns, and binary patterns in function heads now introduce
  their inner variables for the clause body.

### Added -- Std.Access (carried from 0.20.x)

- New `Std.Access` stdlib module implementing an Elixir-style
  `Access` behaviour for Cure. Self-hosted under
  `lib/std/access.cure` and dispatched through the existing
  `proto`/`impl` machinery.
- Core protocol `proto Access(C)` with callbacks `fetch/2`,
  `get_and_update/3`, and `pop/2`. Implementations are provided for
  `Map` (which also covers records, since records compile to maps
  with a `__struct__` discriminator) and for `List` interpreted as
  a keyword-style list of `%[key, value]` pairs. Popping from a
  map that carries a `:__struct__` key raises
  `:struct_pop_not_allowed`, matching Elixir's struct semantics.
- Direct helpers: `fetch/2`, `fetch_bang/2` (raises `:key_error`),
  `get/3` (with default), `get_and_update/3`, `pop/2`.
- Composable lens ADT `Accessor` with factories `key/1`,
  `key_default/2`, `key_bang/1`, `elem_at/1`, `at/1`, `all/0`,
  `filter/1`.
- Nested traversal helpers: `fetch_in/2`, `get_in/2`, `put_in/3`,
  `update_in/3`, `get_and_update_in/3`, `pop_in/2`, accepting a
  `List(Accessor)` path.
- `Cure.Stdlib.Preload` updated to load `Cure.Std.Access` alongside
  the rest of the stdlib beams.

### Added -- Examples

- `examples/binary_destructuring.cure`, `examples/adt_fn_payload.cure`,
  `examples/multi_line_adt.cure`, `examples/let_destructuring.cure`,
  `examples/json_derive.cure`.

### Added -- Docs

- `docs/BINARIES.md` -- authoritative binary pattern reference.
- `docs/LANGUAGE_SPEC.md` updates: multi-line ADT layout, ADT
  function-type payloads, `let` destructuring, binary patterns.
- `docs/TUTORIAL.md` -- new Chapter 11 "Binary parsing"; FSMs
  renumbered to Chapter 12.

### Numbers

- 1078 tests pass (up from 1050); `mix credo --strict`: 0 issues
  across 137 source files; `mix cure.check.stdlib`: 25/25;
  `mix cure.check.examples`: 40/40.

### Deferred to v0.22.0

- Multi-statement lambda bodies -- brace-delimited
  (`fn (x) -> { stmt1; stmt2; final }`) and `end`-terminated block
  forms for anonymous functions embedded in argument lists where
  the existing indented-block form is not usable.
- Binary comprehension generators (`for <<b <- buf>>`) -- the
  parser currently mis-tokenises `<-` inside `<<...>>` as a
  less-than comparison; a dedicated binary-generator path in
  `parse_generator_or_filter/1` will unlock this shape.
- Full byte-size refinement propagation through `rest::binary`
  tail segments -- v0.21.0 binds `rest` to plain `Bitstring`;
  v0.22.0 will emit
  `byte_size(rest) == byte_size(scrutinee) - sum_of_preceding_sizes`
  once the SMT translator grows the arithmetic support.

### Deferred to v0.23.0

- Remote package-registry index service, publication signing, and
  Hex.pm cross-publishing -- the `Cure.Project.Registry` HTTP
  client, Ed25519 archive signing, and `cure publish --hex`
  export path are rescheduled to v0.23.0 so that v0.22.0 can
  focus on closing out the lambda / binary language-surface work.

---

## [0.20.0] -- The Shape of Things

v0.20.0 is the AST-polish release. Plain `#` comments are now
first-class nodes in the tree, binary literals and patterns gain the
full Elixir-style segment grammar (`<<x::utf8, rest::binary>>`), a
Wadler/Inspect.Algebra-style pretty-printer replaces the historical
byte-level formatter in `--algebra` mode, and pattern narrowing can
expose disjoint-tag and literal-equality witnesses through
`Cure.Types.PatternRefinement`.

### Added -- Plain comment nodes

- `Cure.Compiler.Lexer.tokenize/2` gains a `preserve_comments: true`
  option. When set, plain `#` comments emit `:line_comment` tokens
  instead of being discarded; doc comments (`##`, `###`) continue to
  be preserved regardless.
- `Cure.Compiler.Parser` threads `:line_comment` tokens into the AST
  as `{:comment, [line:, col:], text}` nodes in top-level programs,
  container bodies, and block bodies. Indented comment-only lines
  that precede a block's `:indent` token are rerouted inside the
  block body so they attach to the surrounding scope.
- `Cure.Compiler.Codegen` and `Cure.Types.Checker` silently skip
  comment nodes so preserving them has no effect on compilation or
  type checking.

### Added -- Full bitstring segments

- `:colon_colon` lexer token for `::`, distinct from `:colon` (type
  ascription) and `:atom` (symbol literals).
- `Cure.Compiler.Parser.parse_binary_literal/1` now wraps every
  element of `<<...>>` in a `{:bin_segment, meta, [value]}` node.
  The meta carries normalised specifier keys: `:type` (`:integer`,
  `:float`, `:bits`, `:bitstring`, `:bytes`, `:binary`, `:utf8`,
  `:utf16`, `:utf32`), `:signedness` (`:signed`/`:unsigned`),
  `:endianness` (`:big`/`:little`/`:native`), `:size` (an AST node),
  and `:unit` (integer). Specifiers chain with `-`
  (`::binary-size(n)`); bare integers are shorthand for `size(n)`.
- `Cure.Compiler.Codegen` and `Cure.Compiler.PatternCompiler` emit
  full Erlang `:bin_element` forms with the correct size/type/unit/
  sign/endian tuples from the segment AST.
- `Cure.Compiler.Printer` round-trips segment AST back into surface
  syntax.

### Added -- Algebra formatter

- `Cure.Compiler.Algebra` -- an `Inspect.Algebra`-style pretty-printing
  document module with `empty`, `concat`, `nest`, `break`, `line`,
  `group`, `string`, `space`, and a `format/2` best-fit layout.
- `Cure.Compiler.AlgebraFormatter` -- AST-to-document renderer that
  walks top-level programs, containers, and blocks, and delegates
  per-node rendering to `Cure.Compiler.Printer`. Standalone
  `{:comment, ...}` nodes round-trip as `# <text>` lines; sequences
  are separated by blank lines.
- `Cure.Compiler.Formatter.format_algebra/2` runs the algebra
  formatter with round-trip verification: the result must re-parse
  to an AST structurally equal to the input (modulo comment
  placement and position metadata); otherwise the original source is
  returned unchanged.
- `cure fmt --algebra` opt-in CLI flag. The existing byte-level safe
  formatter remains the default for v0.20.0 and will be promoted to
  `--algebra` as the default in v0.21.0.

### Added -- Structural refinement narrowing

- `Cure.Types.PatternRefinement` -- `narrow/2` returns
  `{bindings, narrowed_scrutinee}` for any pattern against any
  scrutinee type. Literal sub-patterns produce refinement types
  (`{x: Int | x == 0}` for `0`); constructor patterns (`Ok(v)`,
  `Error(e)`) and map patterns with `kind: :tag` narrow the
  scrutinee to `{:variant, tag, args}`. Integrates with the existing
  `Cure.Types.Refinement` SMT representation.

### Changed

- `Cure.Compiler.Formatter` ships `format_algebra/2` alongside the
  existing safe `format/2`; neither replaces the other in v0.20.0.
- `Cure.Compiler.Printer.bytes_to_string/2` handles both segment AST
  and legacy flat-list bytes representations.
- `Cure.Types.Checker.do_infer` skips `{:comment, ...}` nodes and
  reports `:unit` for them.

---

## [0.19.0] -- Bring the Furniture

The v0.18.0 release deliberately stayed laser-focused on deep
destructuring. v0.19.0 brings the previously-deferred "furniture"
home: proof containers, `assert_type`, record field defaults,
`@derive(Show, Eq, Ord)` wiring, property-based testing, a lazy
iterator protocol, the first half of the package registry, mutual
recursion totality, and multi-head cons patterns.

### Added -- Language
- `proof` containers (new keyword) -- `proof Name.Path` compiles to a
  regular BEAM module but the type checker requires every binding to
  return `Eq(T, a, b)` or a refinement witness. Error code `E026`.
- `assert_type expr : T` -- compile-time type assertion that vanishes
  at runtime; errors surface as `E027`.
- Record field defaults: `rec Person\n  name: String = ""\n  age: Int = 0`.
  Construction merges declared defaults with user-supplied fields.
  Default type mismatches emit `E028`.
- `@derive(Show, Eq, Ord)` on `rec` -- wires `Cure.Types.Derive` end
  to end; synthesised functions are plain exports usable from any
  caller.
- Multi-head cons patterns: `[a, b | rest]` and deeper now parse,
  desugaring to right-associated cons cells.

### Added -- Standard library
- **`Std.Proof`** -- reflexivity-based laws (`plus_zero`, `zero_plus`,
  `plus_comm`, `append_nil`, `map_id`).
- **`Std.Gen`** -- tiny stateless generator API (`int_in/2`, `bool/0`,
  `one_of/2`, `list_of_int/3`, `list_int/3`).
- **`Std.Iter`** -- lazy iterator protocol; constructors `empty/0`,
  `from_list/1`, `range/2`; consumers `fold/3`, `take/2`, `to_list/1`.
- **`Std.Test.forall/3`** and **`Std.Test.forall_default/2`** --
  property-based runner backed by `Std.Gen`.

### Added -- Totality
- `Cure.Types.Totality.check_mutual/1` -- Tarjan SCC over a module's
  call graph. Non-trivial cycles are reported as `:ok` (structural
  decrease proved) or `:suspect` (`E029` for `@total true` callers).

### Added -- Packaging
- `Cure.Project.Version` -- SemVer + constraint parser (`~>`, `>=`,
  `<=`, `<`, `>`, `==`), compound constraints joined by `and`.
  MAJOR.MINOR is accepted as shorthand for MAJOR.MINOR.0.
- `Cure.Project.Resolver` -- deterministic backtracking resolver over
  a local registry. Conflicts surface as `E030`.

### Added -- Error catalog
- `E026` Proof Shape Mismatch.
- `E027` `assert_type` Failed.
- `E028` Record Default Type Mismatch.
- `E029` Mutual Recursion Not Structural.
- `E030` Package Version Conflict.

### Added -- Examples and docs
- `examples/defaults.cure`, `examples/derived_show.cure`,
  `examples/proof_laws.cure`, `examples/lazy_iter.cure`.
- `docs/PROOFS.md` -- proof containers + `assert_type` reference.

### Changed
- `Cure.Types.Type.subtype?` accepts `:atom` as an inhabitant of any
  `Eq(...)` type (proof atoms are erased at runtime as `:cure_refl`).
- `Cure.Compiler.Codegen` gains a per-module `records` registry plus
  a `@derive` expansion pass that runs before signature collection.
- Parser: `proof` added to the keyword list; `@derive(...)` decorators
  now attach to record containers; multi-head cons desugars in
  `parse_list_or_comprehension/1`.
- `Cure.Stdlib.Preload` preloads `Std.Match`, `Std.Proof`, `Std.Gen`,
  `Std.Iter`.

---

## [0.18.0] -- Deep Destructuring

`match` and `let` grow up. Patterns can now destructure arbitrary
nesting across tuples, lists (cons and fixed), maps, records, and ADT
constructors -- any combination, any depth. Along the way the pattern
engine gained a pin operator (`^x`), repeated-variable equality
guards, record field-punning shorthand, and a nested-exhaustiveness
analyser.

### Added -- Pattern engine

- `Cure.Compiler.PatternCompiler` -- a dedicated pattern-to-Erlang
  translator extracted from the old in-place `compile_pattern` in
  `Cure.Compiler.Codegen`. Every pattern shape recurses through this
  module rather than bottoming out at expression codegen.
- Map patterns now use `map_field_exact` (`K := V`) instead of the
  (wrong) `map_field_assoc` (`K => V`); matching a map pattern now
  actually matches the subject instead of silently succeeding.
- Record patterns: `Point{x: a, y: b}` in pattern position compiles to
  a map pattern with an exact `__struct__ := :point` tag and per-field
  exact matches. Unmentioned fields are open-matched.
- Record field punning: `Point{x, y}` is shorthand for
  `Point{x: x, y: y}`, both in patterns and in constructions.
- ADT constructor patterns and cons patterns recurse correctly through
  the new engine; `[Ok(x) | rest]` now binds `x`.
- Pin operator `^x` in pattern position compares against a
  previously-bound value by emitting a synthetic equality guard.
- Repeated variable occurrences in the same pattern emit synthetic
  equality guards too (`%[x, x]` matches only when both slots agree).

### Added -- Type checker

- `Cure.Types.Checker.bind_pattern_vars/3` rewritten for deep
  recursion. Tuple patterns narrow element-by-element from the
  scrutinee tuple type; map patterns narrow via the record schema
  (when the scrutinee is a record) or the map value type; record
  patterns resolve per-field via `Cure.Types.Env.lookup_type/2`.
- Nested exhaustiveness pass in `Cure.Types.PatternChecker.check_nested/2`
  -- a Maranget-style column walker that emits concrete missing
  witnesses (`%[Error(_)]`, etc.) for tuple-of-ADT scrutinees. The
  old flat classifier remains as a fast-path.
- New error codes `E021` -- `E025`: unknown record field in pattern,
  record pattern field type mismatch, non-literal map pattern key,
  unbound pin variable, non-exhaustive nested match.

### Added -- Parser

- `^` lexed as `:caret` and parsed as the pin prefix operator,
  producing `{:pin, meta, [inner]}`.
- Field-punning in record patterns and map literals: a bare
  identifier at a key position followed by `,` or `}` now desugars
  to `name: name`.

### Added -- Standard library

- `Std.Match` -- new module with destructuring helpers
  (`unpack_pair/1`, `fst/1`, `snd/1`, `head_tail/2`, `uncons/1`,
  `first_two/2`, `unwrap_ok/2`, `unwrap_some/2`); every function
  exercises the new pattern engine.
- `Std.List.uncons/1` and `Std.List.split_first/2` added using cons
  destructuring.

### Added -- Examples

- `examples/destructuring.cure` -- end-to-end showcase of nested
  tuples, maps, records, cons, ADT constructors, and the pin operator.
- `examples/json_tree.cure` -- small JSON-like interpreter driven
  entirely by nested destructuring.
- `examples/pattern_guards.cure` extended with record patterns,
  field-punning, and nested ADT destructuring.

### Added -- Documentation

- `docs/PATTERNS.md` -- authoritative pattern matching reference with
  Cure surface syntax, Erlang abstract-form mapping, and binding
  semantics.
- `docs/LANGUAGE_SPEC.md` pattern-matching section rewritten from a
  12-line stub to a full reference.
- `docs/TUTORIAL.md` -- new Chapter 4 "Destructuring in `match`" and
  renumbering of later chapters.

### Changed

- `Cure.Compiler.Codegen` structure gains `:pattern_guards` and
  `:pattern_dup_counter` fields used by `PatternCompiler` to
  accumulate synthetic guards.
- `Cure.Compiler.Formatter` (v0.17.0) -- a source-preserving
  formatter that normalises line endings, strips trailing whitespace,
  expands leading tabs into two spaces, collapses runs of blank lines
  to a single blank line, and canonicalises operator spacing.
  Operates directly on the source buffer rather than re-printing from
  the AST, so plain `#` comments, string/regex/char literals, and doc
  comments are preserved byte-for-byte. Every rewrite is
  round-trip-validated against the original AST before being returned,
  and the formatter degrades to the unchanged buffer on any mismatch
  or on unparseable input.
- `cure fmt --check` -- exits non-zero if any file would be
  reformatted, suitable for CI.
- `cure fmt --aggressive` / `--ast` -- opt-in access to the
  destructive AST pretty printer.
- `Cure.LSP.Server` advertises `documentFormattingProvider: true`
  again; the handler delegates to `Cure.Compiler.Formatter`.

### Deferred to v0.19.0

The original v0.18.0 "Bring the Furniture" items (`proof` containers,
`assert_type`, record defaults, `@derive`, property-based testing,
`Std.Iter`, package registry first half, mutual-recursion totality)
are moved to v0.19.0. The pin operator remains gated behind
`--experimental-pin` in v0.18.0 and is promoted to default in v0.19.0
once real-world feedback is in.

---

## [0.17.0] -- Proofs & Polish: Toward Idris

The dependent-typing core grows up and the everyday UX catches up.
Three themes land together: dependent-type maturation, friction-free
UX, and ecosystem groundwork.

### Added -- Dependent-type maturation (Theme A)
- `Cure.Types.Sigma` -- dependent pairs; `Sigma(name: T1, T2)` surface
  syntax, subtyping rules, `Type.resolve/1` integration.
- `Cure.Types.Pi` -- dependent function types with `:explicit`,
  `:implicit`, `:erased` parameter modes and an AST-based return type.
- `Cure.Types.Reduce` -- terminating normaliser for type-level
  arithmetic, booleans, comparisons, and pair projection.
- `Cure.Types.Equality` -- propositional equality (`Eq(T, a, b)`),
  `refl` constructor, `rewrite` eliminator; runtime-erased via
  `:cure_refl`.
- `Cure.Types.Unify` -- first-order unification with occurs check for
  implicit-argument inference; `:unification_trace` pipeline event.
- `Cure.Types.Holes` -- `?name` and `??` placeholders with goal-type
  and local-context reporting via the `:hole_goal` event.
- `Cure.Types.Totality` -- coverage + structural-recursion analysis;
  `:total | :partial | :unknown` classification; `@total true` decorator.
- `Cure.Types.PathRefinement` -- path-sensitive refinement flow along
  `if`/`match` guards.
- `Std.Equal` -- equality combinators (`refl`, `sym`, `trans`, `cong`).
- `Std.Refine` -- `NonZero`, `Positive`, `Negative`, `NonNegative`,
  `Percentage`, `Probability`, and predicate helpers.

### Added -- Friction-free UX (Theme B)
- `Cure.REPL` -- multi-line input, `:t`, `:doc`, `:effects`, `:load`,
  `:reload`, `:use`, `:holes`, `:env`, `:reset`, `:fmt`, `:help`,
  `:quit`. History persisted to `~/.cure_history`.
- `Cure.Watch` -- `cure watch` recompiles, checks, or tests on every
  change with a 200 ms debounce.
- `Cure.LSP.Server` -- inlay hints, signature help, formatting,
  prepareRename / rename, code lenses, semantic tokens, workspace
  symbols.
- Error catalog codes `E011`-`E020` in `Cure.Compiler.Errors` covering
  implicit-argument failures, sigma destructuring, totality,
  unfilled holes, refinement counterexamples, dependent-type
  mismatches, equality proof mismatches, and doctests.
- `cure new <name> [--lib | --app | --fsm]` with three templates.
- `Cure.lock` lockfile; `cure deps update`, `cure deps tree`;
  git-based dependency resolution in `Cure.Project.resolve_git_dep/2`.
- `cure bench` -- benchmark runner for `bench/**/*.cure`.
- `cure test --filter PATTERN --doctests`.
- `Cure.Doc.Doctests` -- harvests `cure>` / `=>` doctests from `##`
  blocks and runs them.
- `docs/TUTORIAL.md` -- ten progressive chapters.
- `docs/DEPENDENT_TYPES.md` -- full guide for the new type-system
  features.

### Added -- Ecosystem groundwork (Theme C)
- MIT `LICENSE` file.
- Complete `mix.exs` `package` block for Hex publication, including
  docs extras.
- `vscode-cure/` -- TypeScript/LSP VS Code extension scaffold with
  TextMate grammar and language configuration.
- `docs/PACKAGE_REGISTRY.md` -- design document for the v0.18.0+
  package registry.

### Changed
- `Cure.CLI`: adds `watch`, `new`, `bench`, `deps update`, `deps tree`,
  `why`; extended OptionParser switches.
- `Cure.Project`: `scaffold/2` supersedes `init/1`; lockfile and
  git-dep support.
- `Cure.Types.Type`: recognises `Sigma`, `DPair`, `Eq`, `Pi` names in
  `resolve/1`; subtyping for sigma/eq/pi; `display/1` covers new
  shapes.

### Numbers
- ~9 new Elixir modules, ~9 new test files, ~150 new tests.
- 2 new `.cure` stdlib modules (total now 20).
- 6 new examples; 3 new docs.

---

## [0.16.0] -- Finitomata-Inspired FSM Rewrite

Complete rethinking of FSM handling. The FSM definition and transition logic
now coexist in the same `.cure` file via callback mode, inspired by
[Finitomata](https://hexdocs.pm/finitomata). Simple mode remains
backward-compatible.

### Added -- Dual-Mode FSM Compilation
- **Callback mode**: FSMs with an `on_transition` block compile to
  `GenServer`-based modules with embedded transition tables, user-defined
  `on_transition/4` dispatch, and lifecycle callbacks
- **Simple mode** (backward-compatible): `gen_statem` codegen now includes
  `transitions/0` and `allowed/2` introspection, hard event auto-fire via
  `next_event` actions, and soft event silent catch-all clauses
- `Cure.Compiler` pipeline handles both modes transparently

### Added -- Event Suffixes
- **Hard events** (`event!`): auto-fire when the FSM enters a state where
  the event is the sole outgoing transition. Compiler verifies this constraint.
- **Soft events** (`event?`): failed transitions are silently swallowed
  without logging or calling `on_failure`

### Added -- Lifecycle Callbacks
- `on_enter` -- called after entering a state
- `on_exit` -- called before leaving a state
- `on_failure` -- called when a normal (non-soft) transition fails
- `on_timer` -- called periodically when `@timer <ms>` is set

### Added -- FSM Callback Clause Syntax
- Parser: `(pat1, pat2, ...) -> body` clause syntax for FSM callbacks
- Lexer: `fsm_transition_depth` tracking for `!`/`?` identifier suffixes
- Parser: `@timer <ms>` annotation support
- Parser: `event_kind` classification (`:hard`, `:soft`, `:normal`)

### Added -- Verifier Enhancements
- Hard event validation: `!` events must be the sole outgoing event
- `on_transition` coverage warnings for ambiguous transitions
- Informational pipeline events for coverage analysis

### Added -- Introspection API
- `transitions/0` -- compiled transition table (both modes)
- `allowed/2` / `allowed?/2` -- check transition validity
- `responds?/2` -- check event availability from a state (callback mode)
- `Cure.FSM.Runtime.allowed?/3` and `responds?/3` delegation

### Changed -- LSP
- Symbols: FSM transitions as children with event suffix and kind labels;
  callback blocks and `@timer` as FSM children; detail shows compilation mode
- Hover: `on_transition` and lifecycle callbacks show signature documentation;
  hard/soft event patterns show explanatory hover text
- Completions: FSM callback names offered inside FSM blocks

### Changed -- MCP
- `analyze_fsm`: reports compilation mode, timer, event kinds with suffixes,
  and callback blocks with clause counts
- `syntax_help("fsm")`: documents both modes, event suffixes, lifecycle callbacks

### Changed -- Printer
- Event suffix output (`!`/`?`) in transition rendering
- Callback block rendering in FSM output
- `@timer` annotation rendering

### Changed -- Examples
- `cure_turnstile/` rewritten to use callback mode with `on_transition`

---

## [0.15.0] -- Developer Experience

Public API for parsing and printing Cure source, an effect system for tracking
side effects through the type system, HTML documentation generation, a code
formatter, and an interactive REPL.

### Added -- Public API
- `Cure.quote/2` -- parse Cure source into MetaAST 3-tuples
- `Cure.quoted_to_string/2` -- convert MetaAST back to Cure source (round-trip capable)
- Clean entry point for tooling, macros, and metaprogramming

### Added -- Effect System
- `Cure.Types.Effects` -- infer side effects from function bodies
- Effect kinds: `:io`, `:state`, `:exception`, `:spawn`, `:extern`
- Effect checking: declared effects validated against inferred effects
- `@extern` classification by target module (`:io` -> IO, `:ets` -> state, etc.)
- Pipeline event emission (`:effects_inferred`) for effect inference results
- Pure functions identified for aggressive optimization

### Added -- Source Printer
- `Cure.Compiler.Printer` -- full AST-to-source printer covering all Cure constructs
- Handles literals, operators, bindings, conditionals, pattern matching, collections,
  comprehensions, lambdas, function definitions, containers (mod/rec/enum/proto/impl/fsm),
  type annotations, decorators, imports, exception handling
- Round-trip verified: `quote -> print -> re-quote` produces equivalent AST

### Added -- Documentation Generator
- `Cure.Doc.Extractor` -- extract structured documentation from module ASTs
  (functions, protocols, types, effects, visibility, guards, clauses)
- `Cure.Doc.HTMLGenerator` -- static HTML docs with dark/light theme (system preference),
  per-module pages, function signature rendering, effect badges
- `cure doc [path|dir]` CLI command

### Added -- Code Formatter
- `cure fmt [path|dir]` -- format `.cure` source files via parse-then-print
- Consistent indentation and style across projects

### Added -- Interactive REPL
- `cure repl` -- evaluate Cure expressions interactively
- Wraps input in temporary modules, compiles and executes on the fly

### Added -- Compiler Refactoring
- `Cure.Compiler.Token` -- extracted Token struct with type, value, line, col
- `Cure.Compiler.Parser.Precedence` -- extracted Pratt parser binding power table
  with operator category and symbol lookup

### Added -- Stdlib
- `Std.Test` (5 fns) -- assert, assert_eq, assert_ne, assert_gt, assert_lt
- Total: 18 stdlib modules

### Added -- Examples
- `dependent_types.cure` -- refinement types and guarded functions (12 examples total)

---

## [0.14.0] -- Real-World Readiness

A language is real-world ready when programs can have dependencies, protocols
work across module boundaries, and tests can be written in the language itself.

### Added -- Package Management (Phase 1)
- `Cure.Project` -- Cure.toml project file parsing (minimal TOML subset)
- `Cure.Project.resolve_deps/1` -- compile path-based dependencies, add to code path
- `Cure.Project.init/1` -- scaffold new projects with Cure.toml, lib/, test/
- `Cure.Project.compiler_opts/1` -- read compiler options from project config
- `cure init <name>` CLI command
- `cure deps` CLI command

### Added -- Cross-Module Protocol Dispatch (Phase 5)
- `Cure.Types.ProtocolRegistry` -- ETS-backed global protocol implementation registry
- `register_impl/4`, `lookup_impl/3`, `has_impl?/2`, `list_impls/1` APIs
- `list_impls_by_method/1` -- cross-protocol method lookup
- Started automatically in `Cure.Application`
- Used by codegen for cross-module protocol dispatch

### Added -- Testing Infrastructure (Phase 6)
- `cure test` CLI command -- compile and run `.cure` test files from test/
- Discovers functions starting with `test`, reports pass/fail counts
- `Std.Test` stdlib module -- assert, assert_eq, assert_ne, assert_gt, assert_lt

---

## [0.13.0] -- Depth Over Breadth

Deepened every subsystem from "working foundation" to "production ready."
Closed remaining gaps with the legacy Erlang implementation (~17,000 lines
ported, primarily the type optimizer and 5 LSP modules).

### Added -- Dependent Type Verification (Phase 1)
- Constrained function signatures stored in type env
- Call-site verification via SMT (`Cure.SMT.Solver.prove_implication/4`)
- Counterexample extraction from Z3 models via `Cure.SMT.Parser.parse_model/1`
- Type-level arithmetic in return types (`Vector(T, m + n)`)
- Value parameter parsing: `fn f(v: Vector(T, n: Nat))`
- `Std.Vector` stdlib module -- length-indexed vectors using dependent types

### Added -- Cross-Module Protocol Registry (Phase 2)
- ETS-backed global protocol registry started in `Cure.Application`
- Implementations registered during codegen, discovered at compile time
- `has_impl?` / `lookup_impl` APIs for protocol resolution
- `where Show(T)` constraint validation at call sites
- Cross-module `@derive(Show)` wired into codegen pipeline

### Added -- LSP Production Features (Phase 3)
- `textDocument/definition` with source location tracking
- Type holes: `_` in type annotations inferred and reported as LSP hint diagnostics
- Code actions: add missing match arms, add missing imports, typo correction
- Incremental compilation: AST caching per document URI + version
- Debounced diagnostic publication
- SMT feedback: refinement type info on hover, inline counterexamples

### Added -- Experimental Optimizer (Phase 4)
- Function inlining (small pure functions, recursion-safe)
- Guard simplification (algebraic rules, clause merging, redundancy elimination)
- Pattern-aware SMT encoding for precise exhaustiveness checking
- Deep pipe chain optimizer (Result propagation, Ok wrap/unwrap elimination)
- 5 optimizer passes: inline, constant_fold, dead_code, pipe_inline, guard_simplify

### Added -- FSM Actions & Monitoring (Phase 5)
- Transition actions: `Red --timer--> Green do count = count + 1`
- Guard codegen on transitions: `Red --timer when count > 0--> Green`
- Supervisor-compatible FSM processes with health check API
- Automatic restart tracking (last event time, transition count, error count)

### Added -- Error Reporting (Phase 6)
- CLI uses `format_with_source` for source-annotated errors with caret pointing
- Error catalog with codes E001-E005
- `cure explain E001` command with detailed explanations and examples
- "Did you mean?" suggestions wired into LSP code action quick fixes
- ANSI color output with TTY detection

### Added -- Stdlib Completion (Phase 7)
- `Std.Map` (14 fns) -- put, get, delete, merge, keys, values
- `Std.Set` (11 fns) -- add, remove, member, union, intersection
- `Std.Option` (10 fns) -- separate Option module from Std.Core
- `Std.Functor` (1 fn) -- functor protocol (map over any container)
- Total: 17 stdlib modules, ~200 functions

---

## [0.12.0] -- The Complete Rewrite

Completed the full rewrite from Erlang to Elixir, reimplementing all 12
phases of the original roadmap plus 8 additional phases of advanced features.

### Added -- Import Resolution (Phase A)
- `collect_imports/2` extracts module atoms from `use` declarations
- `resolve_import/3` checks imported modules for matching exports at compile time
- `collect_local_fn_names/1` ensures local functions take priority over imports
- Supports `use Std.List`, `use Std.{List, Core}`

### Added -- Dependent Types (Phase B)
- `Cure.Types.Dependent` -- dependent type representation with value parameters
- Type-level expression substitution
- Verification condition generation for SMT
- Compatibility checking

### Added -- Typeclass Derive (Phase C)
- `Cure.Types.Derive` -- auto-derive Show, Eq, Ord from type structure
- Generates protocol method AST from type name + field list

### Added -- LSP Enhancements (Phase D)
- `Cure.LSP.Symbols` -- symbol extraction from parsed AST
- Hierarchical DocumentSymbol format for `textDocument/documentSymbol`

### Added -- SMT Depth (Phase E)
- `Cure.SMT.Parser` -- Z3 S-expression output parser
- `parse_model/1` extracts variable -> value maps from `(get-model)` output
- General `parse_sexp/1` for nested S-expressions

### Added -- FSM Depth (Phase F)
- `Cure.FSM.TypeSafety` -- FSM transition consistency analysis
- Duplicate transition detection, wildcard shadow detection, self-loop detection

### Added -- Error Reporting Enhancements (Phase G)
- `Cure.Compiler.Errors.suggest/2` -- Levenshtein-based "did you mean?" suggestions
- `format_with_source/3` -- source-annotated errors with caret pointing

### Added -- Remaining Stdlib (Phase H)
- `Std.Eq` (2 fns) -- equality protocol with impls for all primitives
- `Std.Ord` (5 fns) -- ordering protocol with compare, lt, le, gt, ge
- `Std.Result` (11 fns) -- dedicated Result module with flatten

### Stats
- 569 tests, all passing
- 0 credo issues (strict mode)
- 0 compilation warnings
- 44 Elixir source files (~11,500 lines)
- 12 stdlib `.cure` modules (~160 functions)
- 10 example programs
- 4 documentation guides

---

## [0.11.0] -- First Roadmap Complete (Phases 1-12)

### Added -- Standard Library (Phase 1)
- 9 self-hosted stdlib modules (~140 functions) written in Cure itself
- `Std.Core` (36 fns) -- identity, compose, pipe, booleans, comparisons, Result, Option
- `Std.List` (25 fns) -- map, filter, foldl/foldr, flat_map, zip_with, take, drop
- `Std.Math` (18 fns) -- abs, sqrt, pow, log, ceil, floor, pi, max, min, clamp
- `Std.String` (17 fns) -- concat, split, trim, reverse, type conversions
- `Std.Pair` (9 fns) -- first, second, swap, map_first, map_second
- `Std.Io` (8 fns) -- println, print, type-to-string conversions
- `Std.System` (10 fns) -- timestamps, process info, system info
- `Std.Show` (protocol) -- Show with impls for Int, Float, String, Bool, Atom
- `Std.Fsm` (12 fns) -- spawn, send, state, history, lookup
- `mix cure.compile_stdlib` task

### Fixed -- Compiler Bugfixes (Phase 1)
- Lexer: blank/comment-only lines no longer break indentation
- Codegen: variable-as-function calls, lambda closure scoping, chained calls `f(x)(y)`
- Parser: qualified calls via dotted path reconstruction, guard binding power fix

### Added -- Protocol / Typeclass System (Phase 2)
- `Cure.Types.Protocol` -- protocol/impl tracking, type-to-guard mapping
- Codegen: 3-phase module body compilation (collect protos/impls, generate dispatch, compile)
- Type checker: protocol method signature registration, impl body validation
- Dispatch clause ordering by type specificity (Bool before Atom)

### Added -- SMT Solver + Refinement Types (Phase 3)
- `Cure.SMT.Process` -- Z3 GenServer via Erlang port, sentinel-based response parsing
- `Cure.SMT.Translator` -- MetaAST to SMT-LIB2, logic inference (QF_LIA/QF_LRA/QF_NIA)
- `Cure.SMT.Solver` -- check_sat, prove_implication, check_refinement_subtype
- `Cure.Types.Refinement` -- refinement type representation, SMT-backed subtype checking
- `Type.subtype?` extended for refinement-to-base and refinement-to-refinement

### Added -- Guard System Enhancements (Phase 4)
- `Cure.Types.GuardRefinement` -- guard constraint extraction, flow-sensitive refinement
- SMT-backed guard coverage analysis, unreachable clause detection
- Codegen fix: single-body functions with guards compile correctly
- Parser fix: guard expressions parse at BP 6 to stop before `=`

### Added -- Type-Directed Optimizations (Phase 5)
- `Cure.Optimizer` -- pass manager wired into compiler pipeline (`optimize: true`)
- `Cure.Optimizer.ConstantFold` -- arithmetic, boolean, comparison, string, unary folding
- `Cure.Optimizer.DeadCode` -- constant-condition branches, code after return/throw
- `Cure.Optimizer.PipeInline` -- identity elimination in pipe chains

### Added -- Pattern Exhaustiveness Checker (Phase 6)
- `Cure.Types.PatternChecker` -- classify patterns, compute coverage against scrutinee type
- Supports Bool, Result/Option ADTs, List, infinite types (require wildcard)
- Integrated into type checker as `:type_warning` pipeline events

### Added -- FSM Runtime (Phase 7)
- `Cure.FSM.Runtime` -- GenServer with ETS registry, event history, batch operations
- `Cure.FSM.Builtins` -- FFI bridge (fsm_spawn, fsm_send, fsm_state, etc.)
- Started automatically via Application supervisor

### Added -- Language Server Protocol (Phase 8)
- `Cure.LSP.Transport` -- Content-Length framing, JSON-RPC 2.0 over stdio
- `Cure.LSP.Server` -- initialize, textDocument lifecycle, diagnostics, hover, completions
- `cure-lsp` executable for editor integration
- `mix cure.lsp` task

### Added -- Standalone CLI (Phase 9)
- `Cure.CLI` -- escript entry point with 6 subcommands
- `cure compile|run|check|lsp|stdlib|version`
- Options: `--output-dir`, `--type-check`, `--optimize`, `--verbose`

### Added -- MCP Server (Phase 10)
- `Cure.MCP.Server` -- newline-delimited JSON-RPC with 7 tools
- Tools: compile_cure, parse_cure, type_check_cure, analyze_fsm, validate_syntax,
  get_syntax_help, get_stdlib_docs
- `mix cure.mcp` task

### Added -- Extended Examples & Documentation (Phase 11)
- 10 example programs: hello, math, traffic_light, list_basics, result_handling,
  pattern_guards, recursion, protocols, ffi, adt
- 4 doc guides: LANGUAGE_SPEC.md, TYPE_SYSTEM.md, FSM_GUIDE.md, STDLIB.md

### Added -- Profiler & Developer Tools (Phase 12)
- `Cure.Profiler` -- per-stage event counting, total time measurement
- `mix cure.profile` task

---

## [0.10.0] -- Project Bootstrap

Complete rewrite of Cure from Erlang to Elixir using Metastatic's MetaAST
format. Milestones 1-7 of the initial roadmap.

### Added -- Project Bootstrap & Lexer (Milestone 1)
- Elixir project with full tooling (credo, oeditus_credo, ex_doc, dialyxir, excoveralls)
- `Cure.Pipeline.Events` -- Registry-backed PubSub for pipeline stage events
- `Cure.Compiler.Lexer` -- tokenizes all Cure syntax keywords, operators, literals
- Indentation tracking (`:indent`, `:dedent`, `:newline` tokens)
- String interpolation tokenization
- Position tracking (line, column) on every token

### Added -- Parser: Expressions & Bindings (Milestone 2)
- Pratt (precedence-climbing) parser with indentation awareness
- All literal types, variables, binary/unary operators, function calls
- Let bindings, augmented assignment, conditionals, pattern matching
- Blocks, collections (list, tuple, map, range), pipe desugaring
- String interpolation, comprehensions, early return, throw, yield

### Added -- Parser: Definitions, Modules & FSMs (Milestone 3)
- Named function definitions (single-line, multi-line, multi-clause, guards, constraints)
- Modules, records, ADT/sum types, type aliases, refinement types
- Protocols, implementations, imports
- FSM definitions with transitions, wildcards, @terminal, @invariant, @verify
- Metastatic Cure adapter (ToMeta + FromMeta)

### Added -- BEAM Code Generation (Milestone 4)
- `Cure.Compiler.Codegen` -- MetaAST -> Erlang abstract forms
- Module assembly with exports, @extern wrappers, multi-clause functions
- ADT constructors as tagged tuples, records as maps
- `Cure.Compiler.BeamWriter` -- `:compile.forms/2` wrapper + `.beam` file writing
- `Cure.Compiler` -- orchestrator (lex -> parse -> codegen -> beam_write)
- `Mix.Tasks.Cure.Compile` -- `mix cure.compile` task

### Added -- Type System Foundation (Milestone 5)
- `Cure.Types.Type` -- canonical type representations, subtyping, join, AST resolution
- `Cure.Types.Env` -- scoped typing environment with builtins
- `Cure.Types.Checker` -- bidirectional type checker (infer + check modes)
- Two-pass module checking (signatures then bodies), @extern trusted

### Added -- FSM Compilation & Verification (Milestone 6)
- `Cure.FSM.Verifier` -- reachability (BFS), deadlock freedom, terminal state validation
- `Cure.FSM.Compiler` -- FSM MetaAST -> gen_statem Erlang abstract forms
- start_link, send_event, get_state, callback_mode, init, handle_event

### Added -- CLI, Error Reporting, CI, Examples (Milestone 7)
- `Cure.Compiler.Errors` -- structured error formatter for all pipeline stages
- GitHub Actions CI (`.github/workflows/ci.yml`)
- Example programs (hello.cure, math.cure, traffic_light.cure)
- Comprehensive README

### Stats
- 28 source files
- 290 tests, all passing
- 0 credo issues (strict mode)
- Clean dialyzer
