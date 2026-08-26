# Elm Diagnostic Parity: Remaining Work

**Status:** implementation specification

**Date:** 2026-07-20

**Depends on:**

- `2026-07-20-structured-compiler-diagnostics-design.md`
- `2026-07-20-elm-quality-compiler-diagnostics-design.md`

## 1. Purpose

This specification defines the work remaining after the initial diagnostic
foundation landed on the `elaborator-gaps` branch. It is a closure plan, not a
replacement for the two authoritative designs above.

The target is repository-wide Elm-quality diagnostic behavior. Attractive
rendering for a few errors is not parity. Parity means every reachable
rejection path preserves useful semantic context, blames honest authored
source, converts exhaustively, and reaches terminal, JSON, LSP, Elixir, Mix,
and CLI consumers through one diagnostic model.

## 2. Current baseline

The following capabilities are implemented:

- `Cure.Diagnostic.Doc` with plain and ANSI encoders, wrapping, indentation,
  semantic emphasis, lists, notes, hints, code, and Unicode display width;
- the diagnostic body is authoritative and host messages are derived from it;
- TTY-aware colour policies and structured banners;
- Elm-style single, paired, overlapping, separated, cross-file, zero-width,
  clipped, elided, and multiline snippets;
- lexer tokens with byte and line/column endpoint spans;
- source-order token publication after span completion;
- an initial typed registry and loud `UnhandledError` fallback;
- structured syntax, name, type, operational, and macro-lift adapters for a
  limited set of paths;
- JSON, LSP, Code, and Mix projection of the shared diagnostic;
- parser AST span attachment for nodes that already carry positional metadata;
- semantic walkers that ignore diagnostic metadata;
- annotation-specific E093 production at one declared-return checking boundary;
- deterministic usability-first name candidate ranking.

Audit at this baseline:

| Measure | Current |
| --- | ---: |
| Registered codes | 86 |
| Marked reachable | 84 |
| Explicitly retired | 2 (`E015`, `E018`) |
| Registry catalog cases | 15 |
| Codes currently owned by `Cure.Diagnostic.Adapter` | 18 |
| Legacy `format_error` clauses | 49 |
| Legacy `structured_error?` clauses | 21 |
| Raw/legacy formatting references in compiler and host paths | approximately 159 |

The registry currently derives entries from `Cure.Compiler.Errors.list_all/0`.
That makes the prose catalog, rather than the typed registry, authoritative.
Most entries are optimistically marked reachable without a verified producer
or real catalog fixture.

Known verification debt:

- the full suite is not green: the grammar-strictness `sup` family example is
  currently rejected after the family parser recognizes it;
- no final verdict-preservation or performance comparison has been run;
- catalog coverage is far below the required 100% of reachable codes.

## 3. Definition of Elm parity

Cure is at Elm parity only when all of these statements are true:

1. Every deliberate reachable error producer maps to exactly one registered
   public code through an explicit family converter.
2. Every reachable code has a real public-compilation fixture, except an
   explicitly justified operational case that is unsafe to induce.
3. Default output never contains raw domain tuples, Core constructors,
   generated implementation blame, generic `codegen error`, or an uncontrolled
   stacktrace.
4. Every available authored range is exact. Missing ranges remain absent; no
   line-zero, column-zero, or file-start location is fabricated.
5. Syntax reports explain the grammatical construct and a plausible repair,
   not merely `expected X, got Y`.
6. Type reports identify the expression role and expectation origin and show
   stable surface types with the smallest useful difference.
7. Macro reports use the public vocabulary of the invoked macro and blame the
   smallest editable authored input.
8. Terminal, plain, JSON, LSP, Code, and Mix projections agree on semantic
   content.
9. Every CLI and host path uses one sink and one colour policy.
10. Removing diagnostic metadata does not change acceptance, normalization,
    checking, erasure, or emitted code.

This definition is stricter than visual resemblance to Elm.

## 4. Required architecture at completion

### 4.1 Registry is authoritative

`Cure.Diagnostic.Registry` owns all stable metadata directly. An entry contains:

- code, internal key, severity, title;
- `reachable` or `retired` status and retirement reason;
- owning subsystem and producer variant identifiers;
- payload schema version;
- converter module and function;
- real catalog fixture identifier;
- documentation text or a documentation reference.

`Cure.Compiler.Errors.explain/1` and `list_all/0` become compatibility views of
the registry. They must not own a separate code list.

The registry validates at compile or test time that codes and keys are unique,
reachable entries name a converter and catalog case, retired entries include a
reason, and converter modules export the declared boundary.

### 4.2 Family conversion boundary

`Cure.Diagnostic.Adapter.from_error/2` remains the only public conversion
entry. It unwraps boundary envelopes and delegates to exhaustive family
converters:

- `Adapter.Syntax`
- `Adapter.Name`
- `Adapter.Type`
- `Adapter.Macro`
- `Adapter.StaticAnalysis`
- `Adapter.Kernel`
- `Adapter.Codegen`
- `Adapter.Operational`

No family converter has a generic ordinary-error fallback. The root fallback
raises `Cure.Diagnostic.UnhandledError`. E101 accepts only caught exceptions or
contractually impossible return shapes with stacktraces/fingerprints.

### 4.3 One source context and one sink

A compilation establishes a `SourceRegistry` before lexing. Unsaved buffers,
generated buffers, and authored files receive distinct source identities.

A single `Cure.Diagnostic.Sink` accepts diagnostics and renderer options and is
used by compile, check, run, test compilation, docs, package, release,
migration, formatter validation, REPL, watch mode, and Mix tasks. Progress
messages do not pass through the sink.

## 5. Workstream A — registry and producer inventory

### Deliverables

1. Generate a checked inventory of:
   - every registry code;
   - every `{:error, ...}` constructor and deliberate raising boundary;
   - every formatter/renderer consumer;
   - every direct stderr/Mix error site;
   - every existing catalog fixture.
2. Assign every producer variant an owner, stable code, payload schema, and
   converter.
3. Correct reachability classifications using public-path evidence. A code is
   not reachable merely because it appears in the prose catalog.
4. Move registry metadata out of `Errors` and make legacy catalog APIs derived.
5. Add a CI check that fails on an unowned producer or duplicate/unregistered
   code.

### Gate

The inventory reports zero unowned deliberate producers. Every reachable
entry has at least one producer identifier and planned fixture. Retired entries
state why they remain and what permits deletion.

## 6. Workstream B — complete source ownership

### Deliverables

1. Replace the post-parse span inference bridge with parser-owned spans for:
   declarations, annotations, parameters, patterns, guards, branches, record
   fields/updates, type applications, containers, and macro sections.
2. Retain whole-call, callee, and per-argument spans; whole-operator and
   per-operand spans; annotation and body spans; pattern and guard spans.
3. Give synthetic indent, dedent, newline, and EOF tokens honest zero-width or
   consumed ranges.
4. Preserve authored spans when copying/capturing syntax. Generated syntax
   records invocation, definition/template, generated declaration, and parent
   provenance frames.
5. Remove remaining width guesses and line/column reconstruction from normal
   diagnostic paths.
6. Audit all generic AST walkers and equality helpers so diagnostic metadata is
   ignored or treated atomically.

### Tests

- token lexeme round-trips for every token family, interpolation, multiline
  strings, comments, Unicode, tabs, and invalid UTF-8;
- AST range tests for every construct listed above;
- macro capture/copy/generation provenance tests;
- verdict, normalization, hygiene, formatter, erasure, and emitted-form
  equivalence with metadata stripped.

### Gate

No reachable diagnostic reconstructs a token width or invents a source
location when an authored span could have been retained.

## 7. Workstream C — contextual syntax diagnostics

### Deliverables

Define explicit `SyntaxProblem` variants for modules, imports, declarations,
types, expressions, calls, operators, blocks, indentation, delimiters,
patterns, literals, interpolation, macros, and containers. Each variant owns:

- `at`, `within`, opener, and previous-token spans where applicable;
- observed kind and source spelling;
- useful expected alternatives;
- construct-specific facts and a unique safe edit when one exists.

Migrate lexer/parser producers by grammar family. Preserve established codes
such as E035, E063, and E072; use E094 only when no specific registered syntax
code applies. Delete each corresponding legacy formatter clause when its
family migrates.

### Gate

No reachable lexer/parser failure uses `expected X, got Y` as its complete
explanation. Every syntax producer has fixed-width plain and ANSI snapshots and
a real parser-path fixture.

## 8. Workstream D — names, declarations, and canonicalization

### Deliverables

Migrate unknown value/type/constructor/module/member/interface,
wrong-namespace, inaccessible/private, ambiguous, import/export, duplicate,
shadowing, arity, and fixity failures.

Producers retain spelling, namespace, visibility, owner, qualification, arity,
imports, candidate metadata, and both declaration spans for conflicts.
Suggestion ranking must prefer immediately usable candidates, then namespace,
arity, visibility, qualification/import cost, and edit distance. The message
states when a candidate needs qualification or an import.

Elm reference behavior is part of this deliverable. The equivalent of
`Reporting.Suggest` must be a deterministic, pure ranking helper that applies
restricted Damerau-Levenshtein distance after semantic filtering and compares
names case-insensitively for ranking. It must not search arbitrary source text
or let edit distance override namespace, visibility, arity, qualification, or
import usability.

The producer-specific candidate sets are also required:

- unknown values, types, constructors, modules, members, and exports rank only
  candidates visible in the relevant namespace; qualified alternatives retain
  their owner and state whether an import or qualification is required;
- record-field typos rank fields from the actual record shape and may show the
  nearest replacement plus nearby fields; a missing-field or incompatible-root
  error must not invent a rename candidate;
- arity failures may suggest only declarations whose callable shape can satisfy
  the observed application, and must preserve the argument/application range;
- duplicate, ambiguous, inaccessible, and wrong-namespace errors may list
  candidates for explanation but must not mark them as directly applicable
  edits;
- machine data retains the candidate identity, namespace, owner, qualification
  or import requirement, and source origin. Human output may cap the displayed
  list (Elm commonly shows the nearest few), but renderers must not recompute
  eligibility or ranking independently.

This workstream does not implement typed-hole completion, case generation, or
hole-specific code actions. Those are a separate future feature; ordinary
diagnostic metadata here must remain sufficient for source ranges and
provenance without storing candidate sets in the MetaAST.

### Gate

Every unknown-name class identifies the offender and its namespace/import
status without tracing. Conflict diagnostics show both authored regions.

## 9. Workstream E — contextual and dependent type reports

### Deliverables

1. Expand `TypeProblem` and `ExpectationOrigin` to cover call argument/result,
   operator side, condition, branch, collection element, record field/update,
   pattern/guard, annotation, constructor argument/index, implicit,
   typeclass/overload, FFI, effect, actor, FSM, supervisor, and application
   contexts.
2. Enrich errors at the checking site, not later in the renderer.
3. Retain surface expected/observed types, relevant telescope entries,
   dependent indices, normalized forms, stuck computations, unresolved
   constraints, relevance, and implicitness.
4. Implement alias-aware surface localization and smallest-difference
   emphasis. Raw Core and full constraints remain debug-only.
5. Use paired evidence for annotation/body and sibling-branch disagreement.

The existing declared-return annotation boundary is the reference vertical
slice, not completion of this workstream.

### Gate

No reachable elaboration mismatch relies on generic E093 prose. The same Core
disagreement renders accurately different explanations in different checking
contexts.

## 10. Workstream F — trusted and static rejection families

### Deliverables

Migrate coverage, unreachable branches, exhaustiveness witnesses, totality,
positivity, relevance, erasure, holes, proofs, kernel, code generation, BEAM
lint, effects, serialization, and Antigen-facing failures.

Core remains span-free. Kernel errors retain complete semantic facts, while
the elaboration/program boundary attaches the nearest honest surface context.
Locationless independently supplied Core remains locationless.

### Gate

Trusted-core and complete Antigen verdicts match the frozen corpus. Default
reports contain no raw Core vocabulary or inspected tuples.

## 11. Workstream G — macro abstraction and provenance

### Deliverables

Provide exhaustive public diagnostic boundaries for user-defined macros and
actor, FSM, supervisor, and application macros.

- Captured authored-code failures blame the capture using macro vocabulary.
- Invocation contract failures blame the relevant section or field.
- Generated-only failures use E092 at the invocation and identify a
  macro/compiler defect.
- Machine data retains the underlying diagnostic, invocation, definition,
  generated declaration, nested expansion chain, and cause.
- Duplicate sections, transitions, children, cycles, policies, phases, and
  dependencies use paired or cross-file evidence.

### Gate

No default macro report asks the user to edit generated code or exposes an
expanded helper/Core term as primary blame.

## 12. Workstream H — host, CLI, and editor convergence

### Deliverables

1. Introduce and adopt `Cure.Diagnostic.Sink` everywhere.
2. Convert file, configuration, dependency, artifact, command, and usage errors
   without fabricated snippets.
3. Capture BEAM diagnostics structurally and retain native details.
4. Implement `color: auto | always | never`, explicit width, project root, and
   output device consistently in every command.
5. Complete JSON encoding for document roles, all labels, edits, schemas, and
   provenance.
6. Negotiate LSP UTF-8 first, then UTF-16/UTF-32, map secondary labels to
   related information, and expose machine-applicable edits as code actions.
7. Test unsaved buffers and cross-file edits against the source registry.

### Gate

Repository searches find no compiler error output assembled with `inspect`,
direct file-error prose, or a legacy formatter. All projections agree on code,
severity, ranges, labels, suggestions, edits, and provenance.

## 13. Workstream I — exhaustive catalog and legacy deletion

### Deliverables

1. Replace the single exerciser with one fixture per reachable registry code
   and producer branch.
2. Compile each fixture through the public compiler path and assert code,
   schema, critical payload facts, authored blame, and canonical output.
3. Permit constructor-only cases only for unsafe operational failures and mark
   them explicitly.
4. Add `mix cure.diagnostics --color=auto|always|never --width=N --coverage`
   with a hard missing-code failure.
5. Add raw-leak scanning for tuples, maps, Core constructors, generic
   categories, stacktraces, and generated primary blame.
6. Delete `format_diagnostic/5`, `format_legacy_with_source/3`,
   `structured_error?/1`, legacy width guesses, string-message adapters, and
   tuple-inspection fallbacks.
7. Keep compatibility entry points only when they immediately perform
   structured conversion.

### Gate

Reachable code coverage and registered producer-branch coverage are both 100%.
No legacy output path is reachable.

## 14. Required sequencing

Implement in these mergeable phases:

1. Registry authority and checked producer inventory.
2. Parser-owned spans and complete provenance.
3. Lexer/parser conversion by grammar family.
4. Names/declarations/canonicalization.
5. Contextual type infrastructure and elaboration slices.
6. Trusted/static rejection families.
7. Macro families.
8. Unified sink and host/editor convergence.
9. Exhaustive catalog, raw-leak gate, and legacy deletion.
10. Full verification, performance comparison, and documentation closure.

Each phase begins with a failing producer/range/catalog test, removes the
superseded legacy clause in the same slice, and commits only after focused and
affected-subsystem suites pass. A temporary adapter may bridge an unmigrated
family, but it may not emit generic public prose or be counted as catalog
coverage.

## 15. Final verification matrix

Before parity is declared, run and record:

```text
mix format --check-formatted
MIX_ENV=test mix compile --warnings-as-errors
mix test test/cure/diagnostic_test.exs test/cure/diagnostic
mix test test/cure/compiler/*parser* test/cure/compiler/*lexer*
mix test test/cure/elab test/cure/core
mix test test/cure/compiler/*macro* test/cure/compiler/*actor* test/cure/compiler/*fsm*
mix test test/cure/lsp* test/cure/cli*
mix antigen complete
mix test
mix cure.diagnostics --color=always --width=80 --coverage
NO_COLOR=1 mix cure.diagnostics --color=auto --width=80
```

The exact globs may be replaced with explicit repository-supported suite
commands, but no relevant suite may be silently omitted.

Compare the final verdict corpus with the frozen baseline. Measure stdlib and
generated-macro compilation over enough warm repetitions to report a median.
Median wall-time regression must be at most 5%; peak memory regression must be
at most 10%.

## 16. Exit criteria

The work is complete only when:

- all gates in sections 5–13 pass;
- the known `sup` grammar regression is fixed or its fixture is corrected with
  documented grammar evidence;
- the full verification matrix is green;
- the worktree is clean;
- both parent specifications are updated with commands, coverage totals,
  verdict comparison, and performance evidence;
- this document is marked **complete** with links to the closing commits.

Until then, the accurate project status is **Elm-quality foundation present;
repository-wide Elm parity not yet achieved**.
