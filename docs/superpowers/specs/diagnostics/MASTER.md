# Cure Compiler Diagnostics — Condensed Master Spec

**Date:** 2026-07-21

**Scope.** This document condenses the diagnostics specification family into
one reference — the typed structured-diagnostic data model, provenance and
source ownership, the Elm-quality presentation grammar, renderer architecture
(terminal/plain/JSON/LSP/Elixir/Mix), stable-code compatibility, macro
diagnostic abstraction, and the remaining-work ledger toward repository-wide
Elm parity — and can replace reading the individual specs. Cure-native parser
self-hosting and the public `Std.Parse` platform remain 0.35 work governed by
`2026-07-17-cure-native-parser-diagnostics-self-hosting-design.md` (outside
this folder).

## 1. Status ladder and supersession

The two 2026-07-20 designs are **authoritative**: the structured spec owns the
data model, provenance, source ownership, and conversion boundary; the
Elm-quality spec is its normative presentation subsidiary. The 2026-07-20
remaining-work ledger is the completion gate. The 2026-07-10 expansion spec
and the 2026-07-12 PARKED Elm-rendering spec are both **superseded for
implementation** (the former kept as historical audit; the latter's
forward-compatibility contract survives, §9). Accurate current status:
**Elm-quality foundation present (on `elaborator-gaps`); repository-wide Elm
parity not yet achieved.**

**Core decision (locked):** 0.34 ships a shared structured diagnostic
foundation *before* the remaining `actor`/`fsm`/`sup`/`app` macro work
completes. Diagnostics were reclassified from presentation polish to
implementation infrastructure because bare failures like `:unknown_global`
discard information the compiler already has, forcing instrument-run-revert
cycles (motivating evidence: five stdlib modules failed with the identical
`{:error, :unknown_global}` for five different root causes). A second
diagnostic framework is forbidden — 0.35 parser work must reuse this model.
Precedents combined: **Elixir** (`Code.diagnostic/1` envelope, capture,
Mix/editor integration), **Gleam** (one diagnostic value for terminal + LSP),
**Racket** (source identity separate from expansion origin, origin chains,
precise subform blame), plus Cure's additions: stable codes, typed payloads,
machine-applicable edits, macro provenance, dependent-type context.

## 2. Product requirement

A diagnostic must answer, without compiler tracing: (1) what failed; (2) which
authored source to change; (3) what other locations explain it; (4) what
expansion/desugaring path produced the checked term; (5) expected vs observed;
(6) a safe next action; (7) the stable code identifying the condition — and a
programmer unfamiliar with compiler internals must be able to tell where each
side of a disagreement came from and the smallest next action. Default
presentation speaks surface Cure vocabulary — never `vdata`, metavariable
ids, Core tuples, generated Erlang, or internal exception names (verbose/
debug mode only).

## 3. Non-negotiable invariants

1. **Rejection-path only.** Diagnostic metadata (spans, notes, suggestions,
   provenance) never participates in conversion, normalization, unification,
   coverage, totality, erasure, or emitted runtime behavior. Stripping all of
   it must leave every accept/reject verdict unchanged.
2. **Information retained at the point of knowledge.** A producer that knows
   the missing name, expected type, conflicting declaration, or span records
   it immediately; renderers never reconstruct discarded semantic facts.
3. **Construction and rendering are separate.** Phases produce structured
   diagnostics, never hand-formatted strings; all renderers consume the same
   value.
4. **Honest locations.** Absent locations stay absent — never fabricate line
   0, column 0, file start, or a generated path as authored source.
5. **Authored blame first.** The primary label is the smallest authored
   syntax the user can change; generated syntax and outer invocations are
   secondary; internal Core is never the default presentation.
6. **Macro abstraction preserved.** A macro user gets a diagnostic in that
   macro's vocabulary, not a raw parser/elaborator/kernel/codegen failure
   from its expansion. Three blame cases: (a) invocation violates the macro's
   declared grammar/verifier → the macro's declared diagnostic is primary;
   (b) captured authored syntax is semantically invalid → the semantic error
   at the captured syntax, macro role stated; (c) only generated syntax is
   invalid → a macro/compiler-defect diagnostic at the invocation; never
   instruct users to edit generated code. Full underlying diagnostics and
   provenance remain available to machine/verbose consumers.
7. **Compatibility by code, not shape or prose.** Tests, Antigen, CLI, and
   editors match stable codes and structured fields — never internal tuple
   arity or prose (except dedicated rendering snapshots).

## 4. Canonical data model

`Cure.Diagnostic` is the canonical semantic value; it projects losslessly into
Elixir's `Code.diagnostic/1` / `Mix.Task.Compiler.Diagnostic` envelope with
the complete Cure value stored in `:details` (Cure does not invent a second
BEAM-facing protocol). Aligned fields: severity, primary path→`:file`,
authored root→`:source`, primary start/end→`:position`/`:span`, rendered
message.

- **Span:** `source_id, path?, start_byte/end_byte` (zero-based, exclusive
  end; authoritative for slicing) plus one-based line/column presentation
  coordinates matching Elixir conventions. Zero-width spans allowed for
  insertions. Source buffers live once in a compilation `SourceRegistry`,
  referenced by id — never copied per label. LSP prefers UTF-8; UTF-16 is
  the protocol fallback.
- **Label:** span + optional message + `primary | secondary`. Zero or one
  primary; any number of secondaries, possibly in other files.
- **ProvenanceFrame:** `kind (source | desugaring | macro_expansion |
  generated_declaration), name, invocation?, definition?, generated? (span
  or stable template label), parent?` — ordered nearest-generated → authored
  root; frames are shared immutable identities.
- **Suggestion/TextEdit:** message + applicability (`machine_applicable |
  maybe_incorrect | manual`) + edits. Machine-applicable only when applying
  all edits atomically is known to preserve parse structure and directly fix
  the condition; name-distance guesses and multi-owner imports are not.
- **Diagnostic:** `code (E123/W045), key (internal atom), severity, title,
  message/body (Doc), primary?, secondary[], notes[], suggestions[],
  provenance[], payload` — code-specific serializable data (e.g. unknown-name
  namespace/candidates; conversion expected/actual surface + debug-only Core
  forms; duplicate first/duplicate spans). Debug-only fields are hidden from
  ordinary rendering.

## 5. Error production architecture

- **Domain errors stay typed** in each phase (parser, resolver, elaborator,
  unifier, coverage, totality, kernel, macro verifier, release builder),
  converting to `Diagnostic` at the phase boundary.
- **No bare error atoms in new code.** Bare atoms survive only behind a
  migration adapter recording that detail is unavailable.
- **Exhaustive conversion, no catch-all.** Every deliberate error variant has
  an explicit conversion clause, registered code, payload schema, and test;
  a missing converter fails loudly via `Cure.Diagnostic.UnhandledError` —
  never silent `inspect(reason)` fallthrough. Real host exceptions cross a
  separate crash boundary (exceptions + stacktraces only) into a stable
  Internal Compiler Error diagnostic (E101/ICE), which therefore cannot
  conceal an incomplete converter.
- **Unknown names are classified before rendering** (local/value, type,
  constructor, module, member, interface, inaccessible, ambiguous,
  wrong-namespace, unimported), recording spelling, namespace, arity, visible
  candidates, owners, span. The elaborator diagnoses unresolved surface names
  *before* emitting a Core global when possible; the kernel stays defensive
  (unregistered `{:global, name}` returns the name, no fabricated location) —
  keeping presentation metadata out of trusted Core.
- **Type/conversion errors** retain semantic values until re-presented as
  surface syntax; Core forms in debug payload only.
- **Multiple diagnostics:** 0.34 needs no global recovery; a phase may stop
  at its first fatal error. Verifiers over closed collections may return
  multiple diagnostics in deterministic source order. No recovery heuristic
  may change acceptance or run later phases on an invalid trusted term.

## 6. Source and provenance propagation

- Every blame-capable authored AST node carries a canonical span; legacy
  line/column metadata is normalized at the parser boundary.
- Generated syntax preserves captured authored span, invocation span, macro
  definition/template span, stable template label, and parent chain. Copying
  preserves authored identity; constructing marks generated; splicing keeps
  the authored primary span while extending expansion context (Cure's
  analogue of Racket `syntax-original?`/`syntax-track-origin`). Nested
  expansion **appends** frames; renderers may collapse unhelpful frames but
  machine output retains the full chain.
- `LiftModule` preserves provenance **per declaration**: generated module
  name/behavior, failing declaration, authored origin, underlying diagnostic
  unchanged. `{:lift_module_error, module, reason}` with a detail-free
  reason is not an acceptable final diagnostic.
- **Kernel boundary:** Core terms stay free of renderer metadata. Kernel
  errors retain all semantic facts; the elaboration boundary attaches the
  nearest honest surface context. Independently supplied Core with no surface
  origin stays honestly locationless. (The 2026-07-10 spec's option of
  carrying `meta` on Core `{:global,...}` nodes was rejected in the final
  design in favor of this boundary attachment.)
- Exact-range ownership: lexer tokens record exclusive end byte + end
  coordinate (operator ranges cover the whole operator; literal ranges
  include/exclude delimiters per what the diagnostic concerns). Parser nodes
  cover complete constructs *and* retain the narrow `at` token/insertion
  point, the `within` construct, and opener/previous token. Calls keep
  callee/argument/whole-application spans; branches pattern/guard/body;
  annotations annotation + body. The legacy fixed token-width lookup is a
  migration bridge whose deletion is a completion requirement.

## 7. Rendering

### 7.1 Document algebra

Human content is a document tree, not an interpolated string.
`Cure.Diagnostic.Doc` provides `empty/text/concat/line/blank_line/paragraph/
stack/indent/code/emphasis/note/hint/bullet_list` with semantic emphasis
roles (`name, type, keyword, expected, observed, addition, removal`) — roles,
not colours; each renderer decides representation. The algebra owns wrapping
and layout; domain converters never compute padding or ANSI. No parallel
store of terminal-only meaning: any fact in terminal prose must exist as a
structured field for machine consumers.

### 7.2 Elm-style presentation grammar (normative)

- **Banner:** `-- TYPE MISMATCH [E093] ------------------ src/main.cure` —
  concise human uppercase title (never an internal atom), stable code always
  visible, project-relative path right-aligned, **cyan for every severity**
  (severity is expressed by code and marker colour, keeping the banner a
  stable separator). Locationless diagnostics omit the path honestly.
- **Block order:** intro prose → primary snippet → connecting prose →
  secondary snippets → focused semantic comparison → Note/Hint →
  suggestions/edits → collapsed expansion trace. Blank-line separated; prose
  reflows to 80 columns; source/code/tables never reflow.
- **Colour semantics:** error markers red, warning yellow, info/hint +
  secondary cyan, edit additions green; emphasis restrained, never
  whole-paragraph; colour never the only carrier of meaning. Colour policy
  `auto | always | never`, TTY-aware.
- **Markers:** the underline covers the complete displayed range (a two-char
  `->` gets two carets; an expression, one caret per displayed column), min
  width one column, measured by the canonical display-width policy (tabs,
  combining marks, wide chars, emoji) — never bytes or UTF-16 units.
  Multiline ranges use Elm's gutter `>` marking, optionally a focused
  first/last-line underline; elision is deterministic and never removes a
  labelled boundary.
- **Layouts:** single, same-line pair, separated pair, cross-file (path
  banner per extra source). Duplicates, incompatible branches, annotation vs
  body, and macro definition/invocation failures use paired evidence — never
  flattened to prose coordinates. Overlapping labels get separate marker
  rows, primary-then-source order. `--> path:line:column` is optional
  chrome, not a snippet substitute. Unsaved buffers render from the source
  registry (never reread changed files); unavailable source keeps prose +
  honest location without fabricating lines.
- This is a **semantic** requirement: an uppercase banner around a raw tuple,
  Core term, generic category, or unexplained expected/got pair fails it.

### 7.3 Renderers

All consume the same Diagnostic + Doc tree: **terminal** (styled, width-aware,
default 80 cols, deterministic after path/colour normalization); **plain**
(colour-free, snapshots/logs); **JSON/machine** (all fields, stable keys and
offsets — never parsed back out of prose); **LSP** (primary → main range,
secondaries → related info, machine-applicable suggestions → code actions;
UTF-8 negotiated first); **Elixir/Mix** adapter (host envelope, full Cure
value in `:details`; BEAM diagnostics captured structurally via
`Code.with_diagnostics/2`/`Kernel.ParallelCompiler`, never scraped from
formatted text; `Code.print_diagnostic/2` is a fallback, not the canonical
renderer). Terminal and LSP must not construct different semantic diagnostics.

### 7.4 Suggestions

Scope- and namespace-aware ranking: immediately-usable first, then namespace,
arity, visibility, qualification/import cost, edit distance. Reports state
whether a candidate is directly usable, needs qualification, or needs an
import. Private/inaccessible names are never suggested as directly usable.

## 8. Per-family requirements

- **Syntax:** a structured `SyntaxProblem` family describing the grammar
  operation (modules/imports, declarations, types, expressions, calls,
  operators, blocks, indentation, delimiters, patterns, literals,
  interpolation, macro sections). Each variant retains
  `at`/`within`/opener/previous-token spans, observed kind + spelling, and
  only the useful expected alternatives. No public generic `expected X, got
  Y` fallback; uniquely determined delimiter repairs are machine-applicable.
  Read-only lexical inspection of registered source at the cursor may
  improve rejection reporting but must not influence the accepting lexer.
- **Types:** `TypeProblem` records category, checking context, subject span,
  expected, observed, **expectation origin** (why the type was expected —
  annotation, function domain, operator, branch sibling, pattern, interface,
  macro contract; origin becomes a secondary label), related spans, local
  environment summary, unresolved constraints. Contexts cover every checked
  role: call argument/result, operator side, condition, branch, collection
  element, record field/update, pattern/guard, annotation/body, constructor
  param/index, implicit/constraint, FFI boundary, actor/FSM/sup/app —
  enabling "The second argument to `map` has the wrong type" instead of
  "expected Text, got Integer". Surface presentation: localize to stable
  surface syntax, normalize only as needed, isolate the smallest differing
  substructure, suppress identical surroundings, humanize metavariables;
  expected and observed are separate styled fragments. Dependent mismatches
  also retain relevant indices (pre/post normalization), referenced
  telescope entries, stuck computations + blocking constraints, the
  establishing declaration, and implicit/erased/relevant status.
- **Names/declarations:** unknown, ambiguous, inaccessible, duplicate,
  shadowed, arity, import/export, fixity, and namespace errors each own a
  specific report; conflicts show both locations; arity reports show declared
  vs observed plus the application range; operator-mixing offers parentheses
  only where grouping is unambiguous.
- **Macros:** actor/FSM/sup/app errors use public vocabulary (message
  variant, state, event, transition, child, strategy, phase, dependency).
  `Std.Syntax` exposes safe constructors for macro-authored diagnostics
  (stable macro-local key, captured-syntax labels, safe syntax-replacement
  suggestions, inherited provenance); macro authors cannot forge paths or
  offsets — they select captured syntax or template labels. The existing
  `Failure(name, args)` is a migration floor that must lower into a
  structured diagnostic. Every public macro must define/derive a diagnostic
  boundary covering its whole public contract.
- **ICE:** the stable internal-compiler-error report carries apology + repro
  request, phase + current declaration, incident fingerprint, verbose-only
  stacktrace; tests prove ordinary domain terms cannot reach it.
- **CLI:** every diagnostic-emitting command (compile, check, run, test,
  docs, package, release, migration, formatter validation, REPL, watch, Mix
  tasks) uses the canonical renderer via one `Cure.Diagnostic.Sink`.
  Operational errors (files, config, dependencies, usage) use the same model
  without fabricated snippets. Progress text bypasses the sink.

## 9. Stable codes, registry, compatibility

- **Registry is authoritative** (`Cure.Diagnostic.Registry`): per-code stable
  key + numeric spelling, severity, title, `reachable`/`retired` status with
  reason, owning subsystem + producer variants, payload schema version,
  converter module/function, real catalog fixture id, `cure explain` docs.
  `Cure.Compiler.Errors.explain/1`/`list_all/0` become derived views
  (currently inverted — a known defect: the prose catalog still drives the
  registry). Prose renames don't change codes; splitting a condition into
  different user actions may allocate new codes with documented migration.
- **Category extraction:** one helper extracts the stable key/code from a
  Diagnostic, `{:error, diagnostic}`, or legacy atoms/tuples; Antigen and
  behavioral tests migrate to it *before* error shapes expand. Behavioral
  tests assert code + payload facts; dedicated snapshots pin
  rendering/spans/labels; ordinary tests never pin prose.
- **Conversion boundary:** `Cure.Diagnostic.Adapter.from_error/2` is the sole
  public conversion entry, delegating to exhaustive family converters
  (Syntax, Name, Type, Macro, StaticAnalysis, Kernel, Codegen, Operational);
  no family converter has a generic fallback.
- **Forward-compat contract** (from the parked spec, still binding on interim
  diagnostics such as the macro error floor): route through the central
  renderer, keep message content in the conversion clause, carry maximal
  region info — so structural upgrades apply everywhere at once.

## 10. Testing and verification

Each migrated family needs: a producer test (code + payload), source-range
test (byte + coordinates), fixed-width plain snapshot, focused ANSI
assertions, JSON/LSP parity, and ≥1 real-compilation catalog case. The
**semantic catalog** (`mix cure.diagnostics --color=... --width=N
--coverage`) compiles real failing programs through the public compiler
boundary for every reachable code; registry coverage is a hard CI gate;
constructor-only cases are allowed only for unsafely-inducible operational
failures and are labelled supplemental. A **raw-leak scanner** fails default
output containing raw tuples/maps, unclassified atoms (`unknown_global`),
Core vocabulary, exception dumps outside ICE, generated-location primary
blame, or generic `codegen error`/`syntax error` where a specific code
exists. The snippet matrix covers tokens/expressions/zero-width/pairs/
cross-file/multiline/clipping/elision/tabs/Unicode/no-final-newline/unsaved/
colour modes. Also required: verdict preservation (frozen before/after
corpus), full Antigen, the TCB gate on kernel rejection-path changes, and
performance budgets (≤5% median wall-time, ≤10% peak memory regression).

## 11. Implementation status and remaining work

**Landed** (on `elaborator-gaps`): Doc with plain/ANSI encoders and Unicode
display width; authoritative Doc body with derived host messages; TTY colour
policies and banners; all Elm snippet layouts; lexer endpoint spans; typed
registry seed + loud `UnhandledError`; partial
syntax/name/type/operational/macro-lift adapters; JSON/LSP/Code/Mix
projections; parser span attachment where metadata existed; metadata-ignoring
semantic walkers; one E093 declared-return vertical slice; deterministic
name-candidate ranking. Baseline audit: 86 registered codes (84 marked
reachable, 2 retired: E015, E018), 15 catalog cases, 18 codes on the adapter,
49 legacy `format_error` clauses, ~159 raw/legacy formatting references.
**Known debt:** full suite not green (a `sup` grammar-strictness family
example is rejected after the family parser recognizes it); registry derived
from the prose catalog instead of owning it; no verdict-preservation or
performance run yet; catalog coverage far below 100%.

**Remaining workstreams** (A–I, each gated; ledger spec has detail):
A registry authority + checked producer inventory (zero unowned producers);
B parser-owned spans + provenance, delete width guesses; C contextual syntax
family per grammar family (preserve established codes E035/E063/E072; E094
only when nothing specific applies); D names/declarations/canonicalization;
E contextual + dependent type reports (no reachable mismatch on generic E093
prose); F trusted/static families (coverage, totality, kernel, codegen —
Core stays span-free); G macro abstraction (E092 for generated-only
failures); H one sink + host/CLI/editor convergence; I exhaustive catalog,
raw-leak gate, deletion of `format_diagnostic/5`,
`format_legacy_with_source/3`, `structured_error?/1`, and tuple-inspection
fallbacks — in that sequence, each phase starting with a failing test and
deleting its superseded legacy clause in the same slice.

**Explicit non-goals:** no parser replacement (0.35), no broad parser
recovery, no type-system changes to improve messages, no spans in
definitional equality or runtime terms, no verbatim Elm wording, no
guaranteed machine edit when several repairs are plausible.

## Source specs

- `README.md` — one-paragraph map of which document owns what.
- `2026-07-10-compiler-error-expansion-design.md` — historical audit/motivation
  (five-way `:unknown_global` incident), first struct sketch,
  category-extraction helper, matcher-migration rule; superseded.
- `2026-07-12-elm-style-error-rendering-PARKED.md` — parked predecessor: the
  single-renderer chokepoint, gaps vs Elm, and the still-binding
  forward-compatibility contract; superseded/unparked into the 0.34 designs.
- `2026-07-20-structured-compiler-diagnostics-design.md` — authoritative 0.34
  design: invariants, data model, Elixir envelope, production architecture,
  provenance, renderer contracts, code registry, phases, verification gates.
- `2026-07-20-elm-quality-compiler-diagnostics-design.md` — authoritative
  presentation subsidiary: Doc algebra, banner/colour/marker/layout grammar,
  exact range ownership, contextual syntax/type reports, ICE/CLI behavior,
  testing matrix, completion gates.
- `2026-07-20-elm-diagnostic-parity-remaining-work.md` — implementation
  ledger: landed baseline audit, strict parity definition, registry/sink
  architecture, workstreams A–I, verification matrix, exit criteria.
