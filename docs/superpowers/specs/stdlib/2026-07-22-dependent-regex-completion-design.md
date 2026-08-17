# Dependently Typed Regex Completion from the Current Implementation

**Status:** authoritative for all remaining dependent-regex work

**Date:** 2026-07-22

**Amended:**

- 2026-08-10 — runtime module decomposition is measurement-triggered, not a
  prerequisite for the proof phases. The post-CharacterLiteral baseline and
  decision are recorded in `docs/COMPILER_PERFORMANCE_BASELINES.md` and
  `2026-08-10-regex-actor-module-split-design.md`.
- 2026-08-13 — Phases C–F are discharged. Phase G soundness is generic and
  complete; completeness has generic base cases, Alternate composition, and
  Concat composition. Group, Repeat, and the final structural completeness
  induction are the current proof frontier. The Concat convoy and elaborator
  decision are recorded below and in
  `../tooling/2026-08-13-regex-proof-elaboration-assessment.md`.
- 2026-08-14 — generic Group completeness composition is discharged. The
  compiler now accepts graded implicit constructor domains
  (`{@erased index: T}`), preserving their quantity in constructor metadata;
  `ThompsonEvidenceProof` uses that syntax for proof-only shape indices. Group
  completion transports the child acceptance and its capture theorem together
  across `PatternMachine` η before lifting it into the capture-wrapping machine.
  Repeat composition and the final structural completeness induction are the
  current proof frontier.
- 2026-08-14 — the generic Repeat continuation base is discharged:
  `complete_repeat_mode_empty_from` constructs the empty repeated acceptance
  from arbitrary incoming evidence and captures, preserving the capture stack
  and emitting exactly one list-open/list-close pair. Non-empty Repeat
  continuation composition remains the active frontier.
- 2026-08-14 — the first constructive non-empty Repeat transition is
  discharged. `lift_repeat_closing_transition_member` embeds any accepted child
  edge into the Repeat machine's greedy or lazy closing alternative and then
  through canonical boundary filtering. This is the forward counterpart of
  the existing projection relation.
- 2026-08-14 — Repeat's remaining one-step forward algebra is discharged.
  `lift_repeat_active_transition_member` preserves an active child destination
  through Repeat transformation and filtering;
  `lift_repeat_reentry_transition_member` combines an accepted child edge with
  an exact active start edge, including routine/constraint prefixing and
  greedy/lazy ordering. Recursive non-empty Repeat path composition is now the
  active frontier.
- 2026-08-14 — the consuming initial edge is discharged:
  `lift_repeat_initial_active_member` embeds an exact active child start through
  Repeat's greedy/lazy start ordering and boundary filter while prefixing
  `BeginList` exactly once. Together with the transition embeddings, the
  remaining work is path/execution composition rather than machine membership.
- 2026-08-14 — post-filter child edges now have canonical Repeat adapters for
  active, closing, and re-entry transitions. Each adapter recovers the raw
  boundary constraints and their proofs before invoking the transformation
  lemmas, so path construction does not duplicate filter internals. The
  adapters are the direct inputs to recursive path/execution composition.
- 2026-08-14 — final-item path composition is discharged.
  `lift_repeat_closing_active_path` recursively preserves every active child
  transition, turns the child's unique accepted transition into Repeat's close
  alternative, executes `EndList`, and returns the exact closed evidence list.
  An indexed active-path view supplies the full sibling refinements required by
  the kernel; no fixed-pattern or predicate-only path is used.
- 2026-08-14 — the final-item lift is also totality-certified. Its recursion is
  structurally anchored on the matched input tail (rather than a refined view
  binder), and `filtered_starts_from_advanced_initial_edge` supplies the inverse
  boundary conversion needed by the forthcoming non-final handoff.
- 2026-08-14 — the one-step non-final handoff is discharged.
  `splice_repeat_reentry_step` combines the accepting routine of the completed
  child with the next child's active start routine, composes their certified
  executions, takes the canonical filtered re-entry edge, and attaches an
  arbitrary already-built Repeat suffix. It consumes no extra character and
  emits no second `BeginList`.
- 2026-08-14 — generic non-final child path composition is discharged.
  `RepeatContinuationFrom` packages an ordinary child start with a path already
  running in the Repeat machine, and `lift_repeat_reentry_active_path` lifts an
  arbitrary preceding child path into it. The proof transports capture-stack,
  position, suffix-association, and boundary identities explicitly and is
  totality-certified by structural recursion on the child input.
- 2026-08-14 — complete arbitrary child acceptances now enter that path algebra
  through `repeat_closing_continuation_from_acceptance` and
  `repeat_reentry_continuation_from_acceptance`. These bridges retain the exact
  indexed acceptance while normalizing its start, transport the child start
  boundary to the whole repeated input, and align certificate-level final
  captures with the active child path before closing or splicing. Remaining
  Repeat work is at the language-induction layer: recursively complete each
  child denotation, choose closing or re-entry from the remaining denotation,
  and add the single outer `BeginList`.
- 2026-08-14 — generic recursive non-empty Repeat continuation is discharged.
  `complete_repeat_mode_continuation_from` recursively completes every
  non-empty child denotation, closes on the final item, and otherwise re-enters
  through the next child while preserving the entire residual partition
  (`next child ++ later input`). `ExactRepeatModeMoreView` keeps the non-empty
  child shape and exact denotation in one index, and the totality regression
  certifies the public recursive theorem. The remaining Repeat step is to wrap
  this continuation in the single outer `BeginList`; after that, only the final
  structural completeness induction remains.
- 2026-08-14 — Phase G is discharged. `complete_repeat_continuation` adds the
  single outer `BeginList` to an arbitrary non-empty recursive Repeat
  continuation, and `complete_repeat_mode_more_from` transports that acceptance
  back to the exact compiled machine while retaining the capture certificate.
  `pattern_completeness` is the final structural induction over every `Pattern`
  constructor. Its proof packages declare phantom shape, syntax, input, and
  starting-state parameters as erased indices; only final evidence and
  executable routines survive at runtime. Phase H is the earliest incomplete
  phase.
- 2026-08-14 — Phase H bounded quantifiers are implemented. `{m}`, `{m,}`, and
  `{m,n}` (plus lazy suffixes) parse into dedicated literal nodes and lower
  through typed recursive combinators that return `Regex(List(a))` directly;
  repeated `Unit` therefore simplifies to `Nat` without exposing nested tuple
  shapes. Missing bounds, reversed ranges, unclosed/malformed delimiters,
  atomless quantifiers, and the documented 64-repetition expansion limit have
  dedicated macro diagnostics. Scalar/property escapes and the remaining
  diagnostic-span matrix are the active Phase H frontier.
- 2026-08-14 — Phase H hexadecimal scalar escapes are implemented in ordinary
  atoms and character classes. Fixed `\xHH` and braced `\x{H...}` forms share
  one checked scalar parser, accept astral code points, and reject incomplete or
  invalid hex, empty/unclosed braces, values above `0x10FFFF`, and UTF-16
  surrogates with dedicated macro diagnostics. Unicode property classes remain
  the active syntax frontier.
- 2026-08-14 — Phase H Unicode general-category properties are implemented in
  ordinary atoms and bracket classes. `\p{...}` and `\P{...}` support the
  Unicode two-letter general-category vocabulary, its one-letter aggregates,
  and documented long aliases. Matching is driven by the principled
  `Std.Char.unicode_category` primitive rather than a host regex engine;
  malformed, empty, unknown, and unclosed properties have distinct structured
  diagnostics. Exact diagnostic subspans, unsupported-construct diagnostics,
  the modifier interaction matrix, and raw character-integer cleanup remain.
- 2026-08-14 — Phase H unsupported constructs now reject at their first
  distinguishing token with dedicated structured reasons. Numeric and named
  backreferences, recursion/subroutines, conditionals, lookahead, lookbehind,
  atomic groups, named captures, inline option groups, and possessive
  quantifiers can no longer silently degrade into literals or unrelated parser
  failures. Exact diagnostic subspans and user-facing reason content remain the
  diagnostic frontier.
- 2026-08-14 — the Phase H modifier matrix is complete for each supported flag
  and the load-bearing interactions: flag order and duplication are
  idempotent; `i` composes with Unicode literal/range folding; `m` composes
  with first-line search; `x` distinguishes whitespace, comments, escaped
  spaces, and class contents; `U` inverts both default and explicit lazy
  quantifiers; and `E` composes with behavioral flags. Unknown modifiers retain
  the lexer's exact character location. Unicode scalar ceilings and surrogate
  bounds have also moved out of regex syntax into named `Std.Char` predicates.
  Structured macro-authored subspans and user-facing reason content are now the
  only remaining Phase H implementation frontier.
- 2026-08-14 — Phase H is discharged. Every parser failure now crosses the
  macro boundary with authored message/hint content, and malformed groups,
  classes, ranges, quantifiers, scalar/property escapes, unsupported features,
  and POSIX classes carry exact source subspans. Extended-mode preprocessing
  retains a Unicode-scalar source map, so skipped whitespace and comments do
  not corrupt diagnostics. All fourteen POSIX class names accepted by the
  installed Elixir/PCRE version are implemented with ASCII semantics by default
  and Unicode-property semantics under `u`, including inner/outer negation.
  Numeric escapes are rejected explicitly because PCRE assigns octal versus
  backreference meaning contextually; users are directed to `\\xHH` or
  `\\x{...}`. Per-literal newline/BSR control verbs are rejected explicitly:
  Cure's verified engine uses one Unicode newline relation across execution and
  boundary proofs. The complete dependent-regex suite passes 72 tests, and the
  documentation fence gate passes 329 snippets. Phase I is now the earliest
  incomplete phase.
- 2026-08-14 — Phase I is discharged. `Match(a)` carries Unicode-scalar
  `start` and `length` positions alongside the exact subject partition. Typed
  `scan` is non-overlapping, preserves the original boundary state, and advances
  one scalar after an empty match while emitting the terminal empty match once.
  `split` exposes separator inclusion, empty-field trimming, and subject-part
  limits as Cure data. Callback replacement receives the complete typed match;
  literal replacement is its specialization. All three APIs consume `scan`, so
  they share the certified VM and its one progress rule. The complete
  dependent-regex suite passes 78 tests, including 300 generated Unicode
  subjects checking scan partitions/offsets, comma splitting, and literal
  replacement. Phase J is now the earliest incomplete phase.
- 2026-08-18 — Phase J1 now stages a direct indexed `TransitionRows` artifact
  for every certified Thompson constructor. `staged_machine_from_compilation`
  performs one row-backed construction, and the runtime proof layer transports
  each row lookup pointwise to the canonical Thompson machine for predicate,
  empty, boundary, group, concat, alternate, and repeat. The focused source,
  differential, and bounded-quantifier suites pass; J4 (removing the remaining
  compile-time Thompson traversal) and the final J/K verification matrix remain
  open.
- 2026-08-18 — Phase J4 is implemented at the canonical Runtime construction
  site. `staged_machine_seed_from_compilation` let-binds each child machine
  before consuming its starts and transition closure, and
  `direct_staged_rows_values_from_compilation` compiles rows from that one
  machine without calling `thompson_machine`. The proof layer transports the
  direct rows and starts to the canonical machine through checked equivalence
  theorems; the old `reference_thompson_machine` remains test-only. The source,
  transition-row, language-correctness, and full canonical-pipeline gates pass.
  One serialized 79-source profile measured 102.519 s cold and 8.148 s warm;
  `Std.Regex.Proof` remained the dominant cold component at 62.392 s. Phase J5
  differential reference coverage is retained, so Phase K is now the earliest
  incomplete phase.

**Supersedes for unfinished work:**
`2026-07-21-dependently-typed-regex-design.md`

**Primary reference:** Katarzyna Marek, *Dependently-typed regex matchers in
Idris*, MSc thesis, University of Edinburgh, 2021
(`docs/research/idris-tyre-2305.04480.pdf`; owner copy:
`/Users/ch/Downloads/msc_proj.pdf`).

**Implementation baseline:** committed through `50340c0d` ("optimize staged
regex machine construction"). The ordered ledger is
authoritative for later work; no uncommitted work is credited as complete.

## 1. Purpose

The previous design correctly chose a pure Cure, dependently typed regex engine,
but it is a clean-slate architecture document rather than an exact ledger from
the implementation that now exists. It also attributes a stronger theorem to the
thesis than the thesis proves.

This document answers, precisely:

1. what the thesis actually implements and proves;
2. what Cure currently implements;
3. which current pieces are scaffolding rather than discharged proofs;
4. what Elixir-compatible behavior Cure adds beyond the thesis;
5. the only permitted order for reaching a complete implementation;
6. the test, trust, erasure, performance, Unix, and AtomVM gates for each step.

Completion means satisfying every mandatory item below. A working `/.../flags`
literal or green examples are not, by themselves, completion.

## 2. Thesis claim boundary

The thesis contributes a shape-safe parser for the regular core:

```text
Pred | Empty | Concat | Group | Alt | Star
```

It has three representations:

- `RE`, surface sugar whose result shape is simplified;
- `TyRE a`, typed combinators and one-way conversions;
- `CoreRE`, the minimal algebra consumed by Thompson construction.

It has two parsing modes: whole-string and stream-prefix parsing. Matching runs
an epsilon-free NFA and an evidence VM. Its verification certificate consists of
exactly three links:

1. successful execution yields an accepting path carrying the same evidence;
2. an accepting path through `thompson(re)` yields evidence encoding
   `ShapeCode(re)`;
3. evidence accompanied by that `Encodes` proof is totally extractable as
   `Sem(ShapeCode(re))`.

The thesis does **not** prove that Thompson construction recognizes exactly the
denotational language of the regex. Section 7.1 explicitly leaves matching
soundness and completeness as future certified-regex work. Cure requires those
theorems eventually, but they are a Cure strengthening and must be identified as
such in code, tests, and documentation.

The thesis also leaves these as future work or known limitations:

- bounded quantifiers such as `a{4,7}`;
- generic escapes such as `\d`;
- tailored literal diagnostics;
- efficient state-indexed thread storage;
- staged or memoized Thompson construction;
- language soundness and completeness;
- practical performance engineering.

Therefore “paper parity” and “complete Cure regex” are separate milestones.

## 3. Non-negotiable Cure constraints

1. `Regex(a)`, its parser, NFA, VM, evidence, and proof code live in Cure.
2. No OTP `:re`, PCRE handle, runtime syntax interpreter, runtime macro
   dispatcher, opaque container, or Elixir matching helper may implement regex
   semantics.
3. `/pattern/flags` is a compile-time macro. Generated runtime code contains
   direct checked Cure behavior and never reparses `pattern`.
4. The compiler knows only generic macro/syntax/elaboration mechanisms. It does
   not know regex grammar, modifiers, constructors, or APIs.
5. No `believe_me`, proof postulate, proof-carrying `@extern`, cast, or impossible
   fallback is permitted.
6. `Bounded(n)` remains the ordinary indexed inductive in `Std.Bounded`. Finite
   NFA states use it; regex work must not replace it with a primitive or weaken
   the TCB.
7. Character classification and code-point manipulation are encapsulated by
   `Std.Char`; regex modules do not perform raw integer/code-point arithmetic.
8. Proof and index arguments are erased and verified absent from emitted BEAM.
9. Every accepted syntax form and modifier has direct behavioral tests. Parsing
   and retaining an option without implementing its meaning is forbidden.
10. Property tests use `Antigen.Backend.StreamData`, not StreamData directly.
11. A MetaM-like reflective API is not a prerequisite. Regex proofs and runtime
    construction use ordinary checked Cure definitions; the existing checked
    macro/syntax pipeline is sufficient for `/pattern/flags` to emit qualified
    `Std.Regex.*` calls. Reflective declaration lookup or publication must not be
    introduced into the trusted Regex path.

## 4. Honest baseline audit

### 4.1 Implemented and retained

The following are real foundations and should be evolved, not deleted:

- closed `ShapeCode`, `Sem`, `Simplify`, and `simplify_value`;
- indexed `Pattern(shape)` corresponding to the thesis core, plus boundary and
  priority extensions;
- indexed public `Regex(result)` and typed conversion algebra;
- pure Cure epsilon-free Thompson-style machine construction;
- ordered evidence-producing execution;
- typed full parsing, prefix parsing, search, and `Match(result)`;
- capture extents producing `String`;
- deterministic left/right and greedy/lazy priority;
- compile-time slash-literal parser and checked macro expansion;
- staged compile-time syntax modules;
- options `u`, `i`, `s`, `m`, `x`, `f`, `U`, and `E`;
- anchors `^`, `$`, `\A`, `\z`, `\Z` and word boundaries `\b`, `\B`;
- classes, ranges, negation, and `\d/D`, `\w/W`, `\s/S`, `\h/H`, `\v/V`;
- focused shape, NFA, evidence, parsing, modifier, anchor, boundary, and source
  tests;
- some generated and exhaustive-small-word comparison tests;
- proof-erasure inspection for total evidence extraction;
- source scans rejecting OTP `:re` in regex sources;
- dependency-ordered stdlib bundling and direct execution of fresh checked
  stdlib macro BEAMs.

### 4.2 Thesis evidence/extraction parity now implemented

Successful full, prefix, positioned-prefix, and search execution now returns an
erased `MachineAcceptance` certificate. The constructor-complete Thompson
theorem turns that certificate into `Encodes(shape, evidence, Nil())`, and the
runtime evidence is consumed by total `extract_encoding`; no `Option` or error
branch exists between accepted execution and the public result wrapper.

The former `decode_pattern_encoding` oracle was compared against certified
extraction over 500 generated cases spanning every Pattern constructor and then
deleted. Language correctness in Phase G is complete for the whole `Pattern`
algebra in both directions. `pattern_acceptance_path_is_sound` is the generic
soundness induction; `pattern_completeness` is the generic constructive
completeness induction, including recursive Repeat and explicit greedy/lazy
modes.

### 4.3 Structural and performance gaps

- `PatternMachine(n)` now uses `Bounded(n)` for every active state and
  transition source/target. The remaining machine gap is not range safety but
  eliminating function-composed transition reconstruction.
- ordered thread deduplication uses a structurally indexed
  `ThreadWinnerTable`. Each active `Bounded(n)` state has exactly one slot,
  accepted has its own slot, and the first (highest-priority) thread wins
  without rescanning an ever-growing winner list.
- Thompson transition functions are closure-composed and re-traverse
  construction structure during execution.
- executed evidence is already an append-efficient reverse-list builder:
  every evidence instruction prepends in constant time, capture characters are
  accumulated in reverse, and reversal occurs only at the materialization
  boundary. The remaining linear appends construct `EvidenceInstruction` and
  proof-only `ExtendedInstruction` programs while rebuilding transition
  destinations; they belong to the compiled-transition-row work above rather
  than the runtime evidence builder.
- literal expansion emits typed combinator construction, not a completely
  staged finite machine.
- the runtime module remains monolithic, but the post-CharacterLiteral baseline
  measures it at 0.471 seconds (3.8% of the 12.351-second cold pipeline), so
  decomposition is not presently a performance blocker.

### 4.4 Test gaps

The suite does not yet provide all of:

- generated surface-AST print/parse round trips;
- exhaustive regex enumeration rather than a representative fixed menu;
- exhaustive mutation/property coverage for the complete accepting-path and
  evidence theorem (focused constructor and totality tests exist);
- broader generated proof-directed extraction coverage (the accepted path is
  already total and failure is unrepresentable);
- all ambiguity examples required below;
- benchmark thresholds and complexity ratchets;
- final Unix and AtomVM runs.

### 4.5 Current proof checkpoint (2026-08-13)

Phases C–F are implemented and retained:

- active states are intrinsically `Bounded(n)` throughout `PatternMachine(n)`;
- successful execution carries `MachineAcceptance`, including a checked
  `AcceptingFrom` path and certified extended-routine replay;
- `ThompsonEvidenceProof` covers Predicate, Empty, Boundary, Concat, Group,
  Alternate, and Repeat and yields `Encodes` for any certified acceptance;
- successful public parsing uses total `extract_encoding`; the old fallible
  decoder has been differentially checked and removed.

Phase G is complete in both directions:

- `pattern_acceptance_path_is_sound` dispatches over the complete certified
  compilation proof and produces `PatternDenotation`;
- `pattern_completeness` recursively converts any `PatternDenotation` into a
  certified acceptance from arbitrary incoming evidence and capture state.

The Concat milestone is not a fixed-pattern special case. Given arbitrary left
and right `AcceptancePathFrom` certificates whose inputs partition the combined
input and whose evidence/capture states line up, `lift_concat_acceptances`
constructs an acceptance for `concat_pattern_machine` with `PairEvidence`. It
covers:

- paths that remain in the left machine before entering the right;
- paths already executing in the right machine;
- nullable-left starts into active or immediately accepted right starts;
- boundary-constraint filtering and routine concatenation; and
- explicit canonical `Bounded(left + right)` injections.

The load-bearing convoy is `ExactAcceptanceStartView`, indexed by the original
machine, input, and acceptance certificate. Its constructors return the exact
`active_acceptance_certificate(...)` or `accepted_now_certificate(...)`, so
matching the view preserves the relational identity needed by dependent
projections such as `machine_state_thread`. An ordinary payload-only view or a
direct nested-`Sigma` match loses that identity and is insufficient.

Repeated boundary normalization is factored into the total checked
`normalize_initial_active` and `normalize_initial_accepted` combinators. Each
recovers the raw routine and constraints, reconstructs a `Nil()`-constraint
initial edge after boundary filtering, and transports the corresponding
`RoutineExecution` in one indexed result. Group and Repeat should reuse these
combinators and their existing projection-specific transports instead of
open-coding the witness/filter/transport sequence.

Group now does so through `lift_group_acceptance`. The child acceptance is
initially indexed by `thompson_machine(compilation)`; destructuring a
`PatternMachine` alone does not transport the dependent capture certificate.
`transport_certified_acceptance_machine` therefore eliminates
`pattern_machine_eta(machine)` once and carries the acceptance and its exact
final-capture equality together to the canonical
`MkPatternMachine(pattern_machine_starts(machine), pattern_machine_next(machine))`
index. This is a local propositional transport, not stronger global reduction.

Repeat completeness cannot recursively splice a fresh
`PatternAcceptanceFrom(PatternRepeat...)` for the remaining input: that package
would emit another `BeginList`. Its recursive proof must instead maintain a
repeat continuation inside the one already-open evidence list. The checked
base of that continuation is `complete_repeat_mode_empty_from`, parameterized
by arbitrary incoming evidence and captures; the non-empty composer must
thread child acceptances into this continuation without reopening the list.

Do not add stronger global reducible-index simplification before Group and
Repeat. The Concat failure was loss of propositional identity, not a stuck
definitionally equal index. The elaborator already provides homogeneous
Eq-arrow motives for non-indexed `with ... proof` and kernel-checked indexed
LHS-rematch convoys. A whole-value equation for an indexed scrutinee crosses the
heterogeneous-equality boundary and is not a modest elaborator-only change.
Revisit compiler work only with a minimal Group/Repeat red case meeting the gate
in `2026-08-13-regex-proof-elaboration-assessment.md`.

Checkpoint evidence:

- `08dab797` committed the generic Concat theorem and its exact convoy;
- `f17e747c` committed the checked normalization combinators, their totality
  assertions, and the elaborator assessment;
- the focused language-correctness and accepting-path command completed with 12
  tests and 0 failures after the checkpoint:

  ```sh
  MIX_ENV=test mix test \
    test/cure/stdlib/dependent_regex_language_correctness_test.exs \
    test/cure/stdlib/dependent_regex_accepting_path_test.exs
  ```

- the worktree was clean at that commit boundary.

## 5. Final architecture

The final flow is:

```text
/source/flags
  -> compile-time SurfacePattern(shape)
  -> checked Regex(Sem(shape)) expression
  -> Pattern(raw_shape) + Conversion(Sem(raw_shape), Sem(shape))
  -> sigma package (state_count ** Machine state_count raw_shape)
  -> ordered VM execution
  -> Failed | AcceptedRun(input, evidence, erased accepting_path,
                           erased evidence_certificate)
  -> total proof-directed extraction
  -> typed conversion
  -> Option(result)
```

The runtime cannot construct `AcceptedRun` unless all certificate fields check.
The public `Option` describes match failure only; it does not also hide malformed
evidence or conversion failure.

### 5.1 Finite machine

Use an existential state count with intrinsically bounded states:

```text
Machine(shape) = Sigma(n : Nat, MachineOf(n, shape))

MachineOf(n, shape) contains:
  starts      : ordered collection of Bounded(n) or Accept
  accepting   : Bounded(n) -> Bool
  next        : Bounded(n) -> Char -> ordered destinations in Bounded(n) + Accept
  routines    : routine aligned with every start/destination
  invariants  : erased construction proofs
```

`Accept` may remain an explicit terminal destination rather than consuming a
bounded state. State shifting must return bounded values with proofs derived
structurally from addition. There is no unchecked Nat-to-Bounded coercion.

### 5.2 Ordered winning semantics

Ordering is product semantics, not a proof artifact:

1. search chooses the earliest starting position;
2. alternatives choose the left branch by default;
3. greedy quantifiers prefer consuming;
4. lazy quantifiers prefer exiting;
5. `U` inverts each quantifier's default, while an explicit `?` inverts that
   quantifier again;
6. deduplication by `{position,state}` keeps the first/highest-priority thread
   and its complete history/evidence;
7. full parsing chooses the highest-priority accepting path after consuming all
   input;
8. Cure's string `parse_prefix` chooses the highest-priority accepted prefix,
   while a separately named streaming primitive may expose the thesis's
   stop-on-first-accept behavior.

Test at minimum `a|a`, `a?|a?`, `(a*)a`, `(a|aa)*`, `(a?)*`, empty alternatives,
and nested greedy/lazy bounded quantifiers.

### 5.3 Evidence and proof chain

Adopt the thesis proof decomposition explicitly:

```text
AcceptingFrom(machine, state, word)
Accepting(machine, word)

run_certificate:
  run(machine, word) = Accepted(evidence)
  -> Sigma(path : Accepting(machine, word),
           extracted_path_evidence(path) = evidence)

thompson_evidence:
  (pattern : Pattern(shape))
  -> (path : Accepting(compile(pattern), word))
  -> Encodes(extracted_path_evidence(path), [shape])

extract:
  (evidence : Evidence)
  -> {0 certificate : Encodes(evidence, context ++ [shape])}
  -> Extraction(shape, context)
```

As in the thesis, use an extended routine containing ordinary VM instructions
and `Observe(char)`. This separates proof reasoning from transition chunking and
allows the theorem to generalize over pre-existing VM evidence/capture state.

Every `Pattern` constructor—including Cure's boundary and priority extensions—
requires its own proof clause. Boundary patterns append `Unit` evidence without
consuming input. Priority modes change ordering only and reuse the same language
and evidence theorem.

Extraction returns the typed value, remaining evidence, and an erased proof that
the remainder encodes the remaining context. No branch returns `None` when given
an `Encodes` certificate.

### 5.4 Additional language correctness

After thesis parity, define a small structural denotation and prove Cure's stronger
claims:

- Thompson soundness: accepting path implies denotation membership;
- Thompson completeness: denotation membership constructs an accepting path;
- full-run correctness;
- prefix-run correctness;
- search leftmost correctness independent of winning ambiguity policy.

Do not entangle these proofs with evidence extraction. Language correctness and
shape safety are separate theorem families.

### 5.5 Dependent elaboration diagnostics required by this work

Proof development must not depend on reading unstructured dumps of fully
normalized dependent types. In particular, `E093` (call result has the wrong
type) must report the first structurally differing subterm between the expected
and inferred result types. The diagnostic must:

- preserve and display meaningful binder names instead of exposing only
  anonymous metavariables such as `?39`;
- identify the enclosing index or result-type position containing the mismatch;
- render the differing subterms compactly, with unchanged surrounding terms
  elided;
- say when the mismatch crosses a pattern-match branch refinement and name the
  scrutinee whose constructor was substituted;
- distinguish a missing explicit equality transport from an unsolved
  metavariable or a failure to apply a valid branch refinement; and
- retain declaration, call-site, source-span, and macro-expansion provenance.

The motivating regression is a proof whose result is indexed by
`accepting_final_captures(..., path)`: after matching `path` as
`AcceptingNextAccepted(...)`, `E093` currently prints two enormous normalized
types whose only material difference is the original abstract `path` versus the
branch constructor. The improved diagnostic must isolate that pair and indicate
whether the programmer must transport across their equality or the elaborator
failed to refine the dependent motive. Add a focused compiler diagnostic test
before relying on the improved behavior for further Phase G proof work. This
diagnostic requirement is independent of the decision not to broaden global
reducible-index simplification.

## 6. Literal and Elixir-compatibility contract

Slash literals—not `~r`—are Cure syntax. `/[A-Z]*/im` and `/[A-Z]*/mi` are valid,
equivalent macro invocations. The modifier set is the current Elixir set:

| Flag | Required Cure behavior |
| --- | --- |
| `i` | Unicode-aware under `u`; otherwise documented ASCII/simple folding |
| `m` | `^`/`$` become line boundaries |
| `s` | dot includes newline; newline convention is documented |
| `x` | ignore unescaped whitespace/comments outside classes using a stateful scanner |
| `u` | Unicode properties/classes and valid Unicode input semantics |
| `f` | unanchored start must occur before/at first newline |
| `U` | invert quantifier greediness |
| `E` | accepted for Elixir source parity; semantically direct/staged in Cure because no exportable PCRE object exists |

Flags are order-independent. Duplicate-flag policy must be selected and tested;
until changed, accepting duplicates is permitted only if documented as Elixir
behavior. Unknown flags are compile-time errors.

### 6.1 Mandatory regular syntax

The final regular subset includes:

- literals, escaped metacharacters, dot;
- concatenation and alternation;
- capturing and non-capturing groups;
- classes, negated classes, ranges, and escaped classes within classes;
- `?`, `*`, `+`, `{m}`, `{m,}`, `{m,n}` and lazy forms;
- anchors and word boundaries already listed;
- `\a`, `\e`, `\f`, `\n`, `\r`, `\t`;
- `\xHH` and `\x{H...}` Unicode scalar escapes;
- documented octal escape disposition (support with tests or reject with a
  precise diagnostic; never misparse as literal digits);
- Unicode property classes `\p{...}` and `\P{...}` required by `u` parity;
- POSIX classes if the final Elixir behavior audit finds they are accepted by
  the supported Elixir version;
- leading newline-convention controls only if they can be represented without
  compromising the pure finite model.

Unsupported non-regular constructs—backreferences, recursion, conditionals, and
general lookbehind—produce dedicated compile-time diagnostics. Lookahead,
atomic groups, possessive quantifiers, named captures, and inline option groups
remain out of scope until separately specified; they must not silently degrade.

### 6.2 Bounded quantifiers

Bounded repetition is a Cure extension beyond the thesis and returns
`Regex(List(a))`, simplified to `Nat` for repeated `Unit`.

- `{m}` means exactly `m` repetitions;
- `{m,}` means at least `m`;
- `{m,n}` means between `m` and `n`, inclusive;
- `n < m`, missing counts, overflow/resource excess, and malformed delimiters
  are compile-time errors with quantifier subspans;
- exact repetition accepts a lazy suffix syntactically but it has no behavioral
  effect;
- expansion must preserve list shape directly, not expose nested tuple shapes;
- compile-time limits prevent generated-machine explosions.

The current draft's typed-combinator recursion is acceptable as the first green
implementation. Final staging must compile the resulting finite machine once.

## 7. Public API completion

Mandatory typed primitives:

```text
parse_full   : Regex(a) -> String -> Option(a)
parse_prefix : Regex(a) -> String -> Option(Tuple(a, String))
search       : Regex(a) -> String -> Option(Match(a))
matches      : Regex(a) -> String -> Bool
```

`Match(a)` must ultimately contain typed value, matched text, prefix, suffix, and
character or byte positions with the unit explicitly documented.

After the proof core is complete, add typed APIs corresponding where sensible to
Elixir operations:

- `scan : Regex(a) -> String -> List(Match(a))` with non-overlap and empty-match
  progress rules;
- `split` with explicit inclusion/trimming/parts options represented as Cure data;
- `replace` driven by typed callbacks or literal replacement, never numbered
  capture indexing into an untyped list;
- capture access designed around typed groups or a named-capture extension,
  rather than weakening `Regex(a)`.

These APIs reuse one verified engine. They do not introduce alternate matchers.

## 8. Ordered implementation ledger

Every phase is red-test first, focused-green, full relevant gate, documentation
update, and descriptive commit. Do not credit partially edited work.

### Phase A — stabilize the current baseline

1. Finish or revert the bounded-quantifier draft coherently.
2. Run dependency-ordered clean stdlib compilation.
3. Run all current regex tests and the full suite.
4. Record the syntax/behavior matrix generated from tests.
5. Confirm no E101 in the real `MIX_ENV=test mix test` pre-task path.

Gate: clean baseline, no uncommitted regex changes, no current regression.

### Phase B — measured module-boundary decision

Retain the existing compile-time split across `Std.Regex.Syntax.Model`,
`.Class`, `.Flags`, `.Parser`, and `.Emitter`. Do not split the dependent runtime
before the proof phases merely because the source file is large. The 2026-08-10
post-CharacterLiteral baseline measures `Std.Regex` at 0.471 seconds, while
`Std.Actor` alone takes 4.821 seconds; publishing the runtime's indexed
shape/machine/evidence chain through additional interfaces has no demonstrated
payoff and may add conversion and interface-loading work.

Reopen runtime decomposition only if a representative post-proof baseline puts
`Std.Regex` above 15% of cold module-check time, or an isolated Regex edit forces
unrelated layers to rebuild at a cost above one second. Then split along
shape/core/NFA/Thompson/evidence/VM/proof/API dependency direction, with parity
tests before every move. Do not introduce cycles, duplicate definitions,
compatibility wrappers, or alias-dependent recovery.

Gate: a current cold/warm baseline and an explicit keep/split decision are
recorded. This gate is discharged by the 2026-08-10 baseline and split-decision
document; Phase C may proceed without runtime decomposition.

### Phase C — intrinsic finite states

**Status: discharged.** `PatternMachine(n)`, `MachineState(n)`, threads, paths,
and transition functions use `Bounded(n)` for active states. Structural
left/right injections are checked and tested; no unchecked Nat-to-Bounded path
is part of the machine.

Replace raw state `Nat` with `Bounded(n)` inside an existential machine package.
Implement structural shift/injection helpers with erased proofs. Property-test
that every generated start and transition target is in range.

Gate: no unchecked state conversion; `Bounded` remains inductive; TCB, totality,
compact-Bounded, and Antigen regression suites pass.

### Phase D — accepting paths from execution

**Status: discharged.** Successful full, prefix, positioned-prefix, and search
execution carries an erased `MachineAcceptance` with a checked path and routine
replay certificate.

Define `AcceptingFrom`/`Accepting`, retain predecessor/history data in winning
threads, and construct a path plus evidence equality from every successful full
or prefix execution.

Gate: successful execution cannot be returned without a kernel-checked erased
path certificate; fixed and generated replay equality tests pass.

### Phase E — Thompson evidence theorem

**Status: discharged.** The constructor-complete `ThompsonEvidenceProof`
dispatch covers every current Pattern constructor, including boundary and
priority variants, and converts arbitrary certified acceptances to `Encodes`.

Introduce extended routines and prove the generalized evidence theorem for
`Predicate`, `Empty`, `Concat`, `Group`, `Alternate`, `Repeat`, boundary, and
priority variants. Handle nullable starts and nullable star explicitly.

Gate: the theorem kernel-checks over the complete totality closure; no
postulates; constructor mutation tests fail for the expected proof reason.

### Phase F — total extraction and seam removal

**Status: discharged.** Accepted execution flows through total
`extract_encoding`; the fallible decoder was used as a differential oracle and
then deleted.

Implement proof-directed extraction and contextual remainder validity. Route
successful parsing through it. Delete the fallible post-hoc decoder from the
accepted path; retain it only as a test oracle if useful, then remove it after
differential tests.

Gate: after an accepted run there is no `Option`/error branch until the public
match result is wrapped; proof erasure inspection passes.

**This gate is faithful thesis parity.**

### Phase G — language soundness and completeness

**Status: discharged.** Generic soundness and constructive completeness cover
the entire `Pattern` algebra. Non-empty Repeat uses one recursively composed
continuation and exactly one outer `BeginList`; the final theorem is not
restricted to fixed patterns.

Define denotation and prove the stronger Cure theorem family in §5.4. Use
exhaustive small models while developing the proofs.

Gate: all proof modules kernel-check and all small models agree among denotation,
NFA paths, VM acceptance, and public parsing.

### Phase H — finish literal parity and diagnostics

**Status: discharged.**

Bounded quantifiers, hexadecimal scalar escapes, Unicode general-category and
POSIX classes, malformed/unsupported construct rejection, exact source
subspans, extended-mode source mapping, and the modifier matrix are complete.
Regex character semantics use character literals and named `Std.Char`
predicates/constants rather than hidden integer-code arithmetic.

Gate: every accepted grammar row has positive, negative, interaction, Unicode,
and inferred-shape tests; every rejected row has a structured diagnostic test.
The recorded gate is 72 tests with zero failures plus 329 documentation
snippets with zero failures.

### Phase I — complete typed APIs

**Status: discharged.** `Match(a)` records Unicode-scalar positions; `scan`,
typed-option `split`, callback `replace`, and literal replacement share the
certified search engine. Empty matches advance one scalar and the terminal empty
match is emitted once. Fixed examples and 300 generated collection-law cases
pass; the complete dependent-regex suite is 78 tests with zero failures.

Finalize positions in `Match`, then implement `scan`, `split`, and typed
replacement where specified. Lock empty-match progress and leftmost behavior.

Gate: fixed and generated API laws pass; all APIs call the same verified VM.

### Phase J — stage and optimize

1. **Implemented.** Literal machines now stage a direct indexed transition-row
   artifact; the checked semantic transport preserves canonical machine
   behavior, and generated literal tests contain no runtime parser/Thompson
   dispatcher reference.
2. **Discharged.** Replace list `distinct` with a state-indexed winner
   table/set preserving priority and evidence.
3. **Discharged for executed evidence and captures.** Evidence and captured
   characters use reverse-list builders. Eliminate the remaining instruction-
   program appends as part of item 4 instead of adding a second runtime evidence
   representation.
4. **Discharged.** `staged_machine_seed_from_compilation` visits each
   constructor child once, and the active row compiler consumes that direct
   machine without reconstructing `thompson_machine` closures. The proof
   transport covers starts and pointwise transitions for every Thompson
   constructor. The 79-source cold/warm profile is recorded in
   `docs/COMPILER_PERFORMANCE_BASELINES.md`.
5. **Discharged.** `reference_thompson_machine` remains an unstaged reference
   used by the transition-row and exhaustive staged-vs-unstaged tests only;
   generated runtime artifacts do not reference it.

Gate: generated literal BEAM contains neither parser nor Thompson builder calls;
proofs remain erased; semantics are unchanged.

### Phase K — final verification

Run the complete matrix in §9, scan trust boundaries, update public docs and the
older spec's status, and commit final evidence/benchmark reports.

Gate: every acceptance criterion in §10 has an attached command/result artifact.

## 9. Required verification matrix

### 9.1 Fixed tests

Cover every Pattern and Regex constructor, conversion, simplification, syntax
form, flag, parser mode, boundary position, ambiguity policy, capture nesting,
empty input, empty regex, nullable repetition, malformed literal, and public API.

### 9.2 Property tests

Through `Antigen.Backend.StreamData`:

1. generated surface AST print/parse round trip;
2. `matches(r,s) == Option.is_some(search(r,s))`;
3. full acceptance agrees with structural denotation;
4. successful prefix result recombines consumed text and suffix to input;
5. successful run path replays to identical evidence;
6. proof-directed extraction returns a value of computed shape;
7. simplification agrees with structural conversion;
8. smart constructors agree with primitive forms;
9. deduplication keeps the specified ambiguity winner;
10. all generated nullable stars terminate;
11. staged and unstaged machines agree;
12. bounded repetition agrees with a small count reference.

Generators shrink to a surface regex AST and input pair.

### 9.3 Exhaustive models

Enumerate all core regex trees to a documented depth over `{'a','b'}` and all
words to a documented length. Compare denotation, accepting-path existence, NFA,
VM, evidence extraction, and public parse outcome. Report counts so accidental
generator shrinkage is visible.

### 9.4 Trust and erasure

- kernel-check proof modules and complete closure;
- totality and termination checks;
- relevant Antigen TCB/normalization/erasure assays;
- inspect BEAM abstract code and references for proof constructors;
- scan all implementation and emitted references for `:re`, legacy shims,
  runtime parsers, casts, and postulates;
- inspect representative literal artifacts for direct compiled behavior.

### 9.5 Performance

Benchmark the thesis families:

- `a*` over increasing input;
- `((a*c)|a)*b` over increasing input;
- growing `a|a|...|a`;
- growing concatenation.

Add ambiguous-nullable, capture-heavy, Unicode-class, bounded-repeat, search,
and compile-time literal families. Record warm runtime, cold compilation, state
count, peak thread count, and allocation. Ratchet complexity trends rather than
machine-specific microsecond constants.

### 9.6 Platform gates

- focused regex suite;
- complete `MIX_ENV=test mix test` from a clean dependency-ordered stdlib build;
- Unix CLI/escript smoke tests;
- AtomVM-compatible compile and runtime fixtures for the supported subset;
- no warning and no E101 diagnostic.

## 10. Final acceptance criteria

Work is complete only when:

- the paper's three-certificate chain exists end to end;
- accepted execution cannot be followed by evidence/extraction failure;
- finite states are intrinsically bounded without changing `Bounded`'s trusted
  status;
- Cure's additional language soundness/completeness proofs pass;
- `/[A-Z]*/im` and the complete supported syntax matrix compile and behave as
  documented;
- every modifier has interaction tests and no modifier is text-only;
- bounded quantifiers and required scalar/property escapes are complete;
- typed full, prefix, search, scan, split, and approved replacement APIs share
  one engine;
- nullable and empty matches always make specified progress;
- ambiguity winners are deterministic and tested;
- generated literals contain no runtime parser/dispatcher/Thompson construction;
- state deduplication and evidence construction meet performance requirements;
- proofs and indices are absent from runtime artifacts;
- no OTP regex dependency, compatibility engine, cast, postulate, or impossible
  fallback remains;
- fixed, property, exhaustive, proof, trust, performance, full-suite, Unix, and
  AtomVM gates are green;
- repository documentation reports thesis parity and Cure extensions accurately.

Until all of these are true, status must name the earliest incomplete phase and
must not say the thesis or regex implementation is finished.
