# Dependently Typed Regular Expressions

**Status:** superseded for unfinished work by
`2026-07-22-dependent-regex-completion-design.md`

**Date:** 2026-07-21

**Applies to:** `Std.Regex`, regex literals, typed regex parsing, pure Cure
automata, evidence extraction, and the removal of the current recursive matcher

**Primary reference:** Katarzyna Marek, *Dependently-typed regex matchers in
Idris*, MSc thesis, University of Edinburgh, 2021 (`msc_proj.pdf` supplied by
the project owner).

**Macro constraint:** regex literals follow the compile-time-only macro rules in
`../2026-07-14-compile-time-reflective-beam-macros-design.md`. Generated
runtime code must not contain a syntax parser, macro dispatcher, opaque regex
handle, or OTP `:re` call.

## 1. Decision

The existing `Std.Regex.Regex` implementation is not the foundation of the
finished system. It must be removed and replaced from scratch by a
dependently-typed regex parser based on the TyRE architecture described in the
reference thesis.

The thesis names its two indexed representations `CoreRE` and `TyRE`. Cure uses
the user-facing names `Pattern(shape)` and `Regex(result)` respectively. The
paper names are used only when discussing the reference; they are not public
Cure type names.

In particular, the finished implementation must not retain:

- the current unindexed `Regex` syntax tree;
- the recursive suffix-list matcher (`run_with`, `repeat_all`, and related
  helpers);
- `Capture` as a no-op wrapper;
- `run : Regex -> String -> List(String)` as the primary execution model;
- `literal(pattern, flags)` parsing pattern text at runtime;
- a compatibility wrapper around the old implementation;
- an OTP `:re` fallback, compiled handle, NIF object, or Elixir helper that
  performs matching;
- two parallel public regex systems, one typed and one untyped.

This is an intentional breaking replacement. Existing tests are useful as
behavioral requirements and migration evidence, but they do not define the new
representation or API.

## 2. Goals

The implementation must provide all of the following:

1. A regex carries, in its type, the type of value produced by a successful
   parse.
2. Literal shape is computed while compiling, not recovered dynamically.
3. Matching, evidence production, and parse-tree extraction remain type-safe at
   every layer.
4. Proofs and indices are erased and add no runtime allocation or dispatch.
5. Regex literals expand to ordinary Cure definitions and direct compiled
   behavior.
6. The compiler remains regex-agnostic beyond generic macro, elaboration,
   dependent-type, and emission facilities.
7. The runtime implementation is pure Cure, except for already-principled
   character/collection primitives.
8. Full-input parsing and prefix parsing return typed values.
9. Search semantics are deterministic, with a specified leftmost and
   greediness policy.
10. Nullable repetition terminates and cannot produce an infinite epsilon loop.

## 3. Non-goals

The first complete version does not include constructs that are not regular:

- backreferences;
- recursive subpatterns;
- arbitrary semantic predicates over prior captures;
- general lookbehind;
- conditional PCRE subpatterns.

Lookahead, atomic groups, possessive quantifiers, and named-capture syntax may
be added only after the typed regular core is complete and each construct has a
clear automata and shape semantics. They are not permitted as opaque foreign
escapes.

Exact source compatibility with Elixir/PCRE is secondary to typed semantics.
Modifier letters may be retained where their behavior is meaningful, but
accepting a modifier without implementing its behavior is forbidden.

## 4. Layered architecture

The implementation has seven source-level layers:

```text
literal source
    ↓ compile-time syntax parser
surface RE + normalized shape
    ↓ checked compilation
indexed Regex(result)
    ↓ erase conversions / retain typed conversion program
indexed Pattern(shape)
    ↓ Thompson construction
ordered NFA + evidence program
    ↓ execute
accepting path + evidence
    ↓ proof-erased extraction
typed result
```

All seven layers live in Cure source. Elixir code must not contain regex
vocabulary or matching logic.

### 4.1 Module layout

The intended source layout is:

```text
lib/std_deps/regex/regex.cure                 public Regex API and literal-facing exports
lib/std_deps/regex/regex_core.cure            ShapeCode, indexed Pattern, and simplification
lib/std_deps/regex/regex_syntax.cure          compile-time literal grammar and diagnostics
lib/std_deps/regex/regex_runtime.cure         Regex, finite machine, and ordered thread VM
lib/std_deps/regex/regex_proof.cure           soundness/completeness obligations
lib/std_deps/regex/regex_language.cure        constructive language semantics
```

The exact split may change to avoid import cycles, but these boundaries are
normative.

## 5. Shape universe

### 5.1 Codes

Regex result types are represented by a closed code universe:

```cure
type ShapeCode =
  | UnitC
  | CharC
  | StringC
  | BoolC
  | NatC
  | PairC(ShapeCode, ShapeCode)
  | EitherC(ShapeCode, ShapeCode)
  | MaybeC(ShapeCode)
  | ListC(ShapeCode)
```

`Sem : ShapeCode -> Type` interprets each code:

```text
Sem(UnitC)       = Unit
Sem(CharC)       = Char
Sem(StringC)     = String
Sem(BoolC)       = Bool
Sem(NatC)        = Nat
Sem(PairC a b)   = Tuple(Sem(a), Sem(b))
Sem(EitherC a b) = Either(Sem(a), Sem(b))
Sem(MaybeC a)    = Option(Sem(a))
Sem(ListC a)     = List(Sem(a))
```

This is a genuine large elimination from a value-level code to a type. Phase 1
must prove that Cure can elaborate, normalize, and kernel-check it. If support is
incomplete, the missing generic dependent-type mechanism must be implemented
and verified independently; the regex library must not simulate `Sem` with
runtime tags, `Dynamic`, casts, or `believe_me`.

### 5.2 Raw and simplified shapes

Core construction uses structural shapes. Literal syntax additionally computes
a user-facing simplified shape. Simplification removes information that can be
reconstructed without inspecting input:

```text
PairC(UnitC, b)             ⇒ b
PairC(a, UnitC)             ⇒ a
PairC(UnitC, UnitC)         ⇒ UnitC
EitherC(UnitC, UnitC)       ⇒ BoolC
MaybeC(UnitC)               ⇒ BoolC
ListC(UnitC)                ⇒ NatC
```

All other pairs, alternatives, options, and lists retain their structure.

Simplification requires two total functions:

- `Simplify : ShapeCode -> ShapeCode`;
- `simplify_value : Sem(raw) -> Sem(Simplify(raw))`.

If restoration is exposed, it must also provide a total
`restore_value : Sem(Simplify(raw)) -> Sem(raw)`. The library never relies on an
unproved cast between raw and simplified interpretations.

## 6. Indexed regex representations

### 6.1 Pattern

`Pattern(shape)` is the minimal regular-language algebra consumed by Thompson
construction. Its constructors determine the index definitionally:

```text
PatternPredicate : (Char -> Bool) -> Pattern(CharC)
PatternEmpty     : Pattern(UnitC)
PatternConcat    : Pattern(a) -> Pattern(b) -> Pattern(PairC(a,b))
PatternGroup     : Pattern(a) -> Pattern(StringC)
PatternAlternate : Pattern(a) -> Pattern(b) -> Pattern(EitherC(a,b))
PatternRepeat    : Pattern(a) -> Pattern(ListC(a))
```

The final Cure declaration syntax may differ, but these indices and result
types are mandatory.

`Group` records the consumed substring. It is not a precedence-only node and
must not silently delegate to its child. A non-capturing grouping construct in
the surface grammar changes precedence without introducing `Group`.

Derived constructors are compiled into the core:

```text
Plus(r)      = Concat(r, Star(r))
Optional(r)  = Alt(r, Empty)
Exactly(c)   = predicate equal to c, converted to Unit at the Regex layer
Any          = Pred(always true)
OneOf        = Pred(character membership)
Range        = Pred(character range membership)
```

Anchors are input-position constraints, not character predicates. They require
an explicit boundary-aware extension to the NFA transition model and must not
be encoded as fake characters.

### 6.2 Regex

`Regex(result_type)` is the public indexed combinator type:

```text
FromPattern  : Pattern(code) -> Regex(Sem(code))
Concatenated : Regex(a) -> Regex(b) -> Regex(Tuple(a,b))
Mapped       : (a -> b) -> Regex(a) -> Regex(b)
Alternated   : Regex(a) -> Regex(b) -> Regex(Either(a,b))
Repeated     : Regex(a) -> Regex(List(a))
```

`Conv` is one-way. Unparsing is not part of this design.

Required smart constructors include:

- `discard_left`, equivalent to `<*`;
- `discard_right`, equivalent to `*>`;
- `or_same : Regex(a) -> Regex(a) -> Regex(a)`;
- `optional : Regex(a) -> Regex(Option(a))`;
- `one_or_more : Regex(a) -> Regex(NonEmpty(a))` or another explicitly non-empty
  result type;
- `exactly : Char -> Regex(Unit)`;
- `char`, `one_of`, `range`, and `any_char`;
- `digit : Regex(Int)` using `Std.Char` numeric APIs rather than leaked code-point
  arithmetic;
- `captured : Regex(a) -> Regex(String)`;
- `as_string : Regex(a) -> Regex(String)` when the matched extent is required.

Combinator names and operators must follow Cure naming conventions. The semantic
types above are normative.

## 7. Literal syntax and macro expansion

### 7.1 Supported grammar

The first complete literal grammar must cover at least:

| Syntax | Meaning | Simplified result |
| --- | --- | --- |
| `a` | exact character | `Unit` |
| `[abc]` | one of | `Char` |
| `[a-c]` | scalar range | `Char` |
| `.` | any permitted character | `Char` |
| `AB` | concatenation | simplified pair |
| `A\|B` | alternation | simplified either/bool |
| `A?` | optional | simplified option/bool |
| `A*` | zero or more | simplified list/count |
| `A+` | one or more | non-empty/list result |
| `(A)` | captured group | `String` |
| `(?:A)` | precedence-only group | shape of `A` |

Character escapes and classes (`\d`, `\w`, `\s`, and negations) must have
documented ASCII/Unicode behavior implemented through `Std.Char`.

Current useful syntax tests should be migrated, including ranges, alternation,
repetition, extended mode, multiline boundaries, dotall, first-line behavior,
caseless matching, and Unicode classes. A syntax feature is retained only if its
typed meaning and NFA behavior are implemented.

### 7.2 Compile-time expansion

`/.../flags` is a compile-time macro. Expansion must:

1. parse the literal text during compilation;
2. validate flags and reject duplicates or incompatible settings as specified;
3. build the surface RE;
4. compute and normalize its shape;
5. produce an indexed Regex expression;
6. compile its Pattern into an ordinary Cure machine representation where
   staging is possible;
7. attach source spans and expansion provenance to every diagnostic;
8. emit no runtime call that reparses the pattern text.

The inferred type of a literal is `Regex(Sem(simplified_shape))`. Users must be
able to inspect this type in holes and diagnostics.

Dynamic pattern strings are not literals. If supported later, they must return
an existential package such as `Sigma(code : ShapeCode, Regex(Sem(code)))`, never
pretend to have a statically known result type.

## 8. NFA and Thompson construction

### 8.1 Finite ordered NFA

The NFA representation contains:

- a finite state carrier or a `Bounded(n)` state index;
- an ordered collection of start states;
- an accepting-state decision;
- boundary-aware transitions;
- transition routines for evidence production;
- no epsilon transitions in the runtime machine, following the thesis design;
- a proof or construction invariant that every referenced state is in range.

The state count must be statically known after construction. Dynamic unbounded
state identifiers are forbidden.

### 8.2 Construction

Implement Thompson construction structurally for every `Pattern` constructor.
The construction returns the NFA and its evidence program together so state
renaming and routine attachment cannot drift.

The following cases require explicit proofs and tests:

- accepting start states for nullable expressions;
- concatenation where either side is nullable;
- alternatives with overlapping languages;
- `Star` when the child is nullable;
- capture/group boundaries;
- start/end and multiline boundaries;
- greedy versus ungreedy transition priority.

## 9. VM, evidence, and deterministic ambiguity

### 9.1 Evidence

Evidence markers mirror the typed Pattern structure:

```text
CharMark(Char)
StringMark(String)
UnitMark
PairMark
LeftMark
RightMark
BeginList
EndList
```

The exact representation may use snoc lists, vectors, or a builder, but it must
support linear extraction without repeated list concatenation.

### 9.2 VM instructions

The evidence VM requires instructions equivalent to:

```text
Record
EmitString
EmitChar
EmitUnit
EmitPair
EmitLeft
EmitRight
BeginList
EndList
```

Each active thread stores its NFA state, evidence state, capture buffer state,
and priority. Runtime proof fields are erased.

### 9.3 Ambiguity policy

The thesis notes that dropping duplicate states can lose differing evidence.
Cure must not leave this unspecified.

The required policy is ordered Thompson execution:

1. search chooses the earliest input start;
2. alternatives prefer the left branch unless priority is explicitly inverted;
3. greedy repetition prefers consuming transitions;
4. ungreedy repetition prefers exiting transitions;
5. when two threads reach the same state, retain the higher-priority thread and
   its evidence;
6. thread deduplication must preserve this ordering.

This policy must be tested against ambiguous expressions such as `a|a`,
`(a*)a`, `(a|aa)*`, and nullable alternatives.

## 10. Parsing APIs

The public API is typed and value-producing:

```text
parse_full   : Regex(a) -> String -> Option(a)
parse_prefix : Regex(a) -> String -> Option(Tuple(a, String))
search       : Regex(a) -> String -> Option(Match(a))
matches      : Regex(a) -> String -> Bool
```

`Match(a)` contains at least:

- the typed value;
- the consumed substring or start/end positions;
- the unmatched prefix and suffix when returned by search.

`matches` is derived from typed parsing/search and does not use a second matcher.

Streaming prefix parsing is a later subphase of the same architecture, not a
separate engine. It must reduce to the verified string parser by producing the
consumed finite word and remaining stream.

There is no public suffix-list execution API.

## 11. Verification obligations

The proof layer must establish the following.

### 11.1 Language correctness

- Thompson soundness: every accepting path denotes a word in the Pattern
  language.
- Thompson completeness: every word in the Pattern language has an accepting
  path.
- Full parsing accepts exactly when the entire input is recognized.
- Prefix parsing returns exactly an accepted prefix.

### 11.2 Evidence correctness

Define an indexed proposition equivalent to:

```text
Encodes : Evidence -> List(ShapeCode) -> Type
```

Then prove:

- executing the routine extracted from an accepting path appends evidence
  encoding the Pattern shape;
- evidence accumulated before a submachine remains valid;
- concatenation composes evidence contexts correctly;
- alternatives mark the selected branch;
- repetition evidence has balanced list boundaries;
- group evidence is exactly the consumed extent.

### 11.3 Extraction

Implement a total extractor whose type guarantees the result:

```text
extract : (evidence : Evidence)
       -> {0 proof : Encodes(evidence, [shape])}
       -> Sem(shape)
```

If extraction also consumes a suffix of a larger evidence context, return the
remaining evidence and its proof, as in the thesis. No impossible marker/shape
combination may reach runtime failure.

### 11.4 Erasure and trust

All acceptance-path certificates, `Encodes` proofs, state-range proofs, and
shape equalities are quantity-zero where possible. Emitted BEAM must be
inspected to verify that proof terms are absent.

No theorem may be postulated with `@extern`, `believe_me`, an opaque axiom, or a
host-language assertion.

## 12. Termination and nullable repetition

`Star(r)` is problematic when `r` accepts the empty word. The current matcher
avoids some loops by requiring suffix length to decrease; that implementation is
being deleted and is not a proof.

The new construction must choose and document one principled strategy:

- normalize nullable repetition so epsilon-only cycles are removed; or
- include visited-state/position information proving each epsilon closure is
  finite; or
- reject a repetition whose body is nullable with a compile-time diagnostic.

The preferred implementation is normalization plus finite closure. Rejection is
acceptable only as an explicit temporary phase gate. Silent divergence or
dropping arbitrary evidence is forbidden.

## 13. Performance requirements

Correctness lands before optimization, but the architecture must avoid known
pathologies:

- active threads use a state-indexed set/map, not quadratic list `distinct`;
- deduplication retains the priority-winning evidence thread;
- Thompson construction is staged once per literal, not traversed for every
  character;
- evidence uses an append-efficient representation;
- extraction is linear in evidence size;
- no runtime pattern parsing occurs;
- no exponential reconstruction of identical submachines occurs.

Required benchmark families:

- `a*` over increasing input;
- `((a*c)|a)*b` over increasing input;
- increasing alternation `a|a|...|a`;
- increasing concatenation;
- ambiguous nullable expressions;
- capture-heavy patterns.

Benchmarks are regression signals, not substitutes for semantic tests.

## 14. Diagnostics

Compile-time literal errors require structured diagnostics for:

- malformed syntax and unclosed groups/classes;
- invalid or unsupported modifiers;
- reversed/invalid ranges;
- unsupported non-regular constructs;
- nullable repetition when temporarily rejected;
- shape-computation or simplification failure;
- conversion-function type mismatch;
- automata state-size or compile-time resource limits.

Diagnostics must identify the literal subspan, retain macro expansion
provenance, and explain the expected typed shape when relevant. Returning
`Empty` for malformed syntax is forbidden.

## 15. Testing strategy

### 15.1 Fixed behavior tests

Every constructor, syntax form, modifier, smart constructor, parser mode,
ambiguity rule, and diagnostic receives focused tests. Include Unicode edges,
case expansions, empty input, empty regex, nested captures, and nullable
expressions.

### 15.2 Property tests

Use StreamData only through `Antigen.Backend.StreamData`. Required generated
properties include:

- literal parser round-trips for generated surface REs;
- `matches(r,s)` agrees with `Option.is_some(parse_full(r,s))`;
- NFA acceptance agrees with a small structural reference semantics;
- full parse consumes all input;
- prefix parse returns a prefix whose re-concatenation restores the input;
- extracted values satisfy the computed shape;
- simplification and restoration commute where restoration is provided;
- equivalent smart-constructor and primitive forms behave identically;
- thread deduplication preserves the specified ambiguity winner;
- generated nullable stars always terminate.

Counterexamples must shrink to a regex and input pair.

### 15.3 Exhaustive small models

Enumerate all regexes up to a small depth over a two- or three-character
alphabet and all words up to a small length. Compare Pattern denotation, NFA
acceptance, VM acceptance, and typed parse success.

### 15.4 Proof and trust gates

- kernel-check every proof module;
- run totality checking over the complete closure;
- run relevant Antigen TCB/normalization assays if any generic dependent
  mechanism changes;
- inspect emitted BEAM for proof erasure;
- scan `lib/**/*.ex` and emitted references for `:re` and deleted shim names;
- inspect literal-generated artifacts to prove no runtime syntax parser remains.

## 16. Ordered implementation phases

Each phase ends with focused tests, the relevant full gate, documentation, and
a descriptive commit. Do not begin a later phase while an earlier gate is red.

### Phase 0 — freeze requirements and delete the old design

1. Record current accepted syntax and behavior as migration requirements.
2. Mark tests that assert the obsolete AST/suffix API for replacement.
3. Delete the current `Regex` algebra and recursive matcher in one explicit
   breaking commit.
4. Keep the project compiling with `Std.Regex` temporarily absent or with only
   scaffold declarations; do not retain a compatibility engine.

Gate: no `:re`, no old matcher, no old regex runtime helper, and no stale public
API documentation.

### Phase 1 — dependent-shape feasibility

1. Implement `ShapeCode` and `Sem` in a probe module.
2. Prove normalization and kernel checking for every code.
3. Verify proof/index erasure on BEAM.
4. If large elimination is missing, implement the generic language feature with
   its own TCB, termination, and Antigen gates.

Gate: `Sem(PairC(CharC,ListC(UnitC)))` computes definitionally to the expected
type and can be used in function signatures and pattern matches.

### Phase 2 — indexed Pattern and shape simplification

1. Implement indexed Pattern constructors.
2. Implement raw shape, `Simplify`, and value conversion.
3. Add constructor and simplification laws.
4. Add exhaustive small shape tests.

Gate: no cast or runtime shape dispatch; all constructor indices kernel-check.

### Phase 3 — Regex combinators

1. Implement `Regex(a)`, `FromPattern`, `Mapped`, concatenation, alternation, and
   repetition.
2. Implement required smart constructors.
3. Build room-number and time-parser examples from the thesis.
4. Use holes/diagnostics to demonstrate inferred parse-result types.

Gate: conversion functions are accepted or rejected solely by their inferred
types; no parsing engine is needed yet.

### Phase 4 — literal parser and compile-time macro

1. Implement the literal grammar as compile-time Cure code.
2. Compute simplified shape and produce a Regex expression.
3. Implement structured literal diagnostics.
4. Prove expansion leaves no runtime parser.

Gate: literals infer their Regex result type and malformed literals fail during
compilation with precise spans.

### Phase 5 — finite ordered NFA and Thompson construction

1. Implement finite states, ordered transitions, and acceptance.
2. Implement Thompson construction for all Pattern constructors.
3. Implement nullable analysis and epsilon-cycle handling.
4. Verify against exhaustive structural denotation.

Gate: acceptance soundness/completeness tests and small-model exhaustive checks
pass.

### Phase 6 — evidence VM

1. Implement instructions, routines, VM state, and prioritized thread pool.
2. Add captures/groups and repetition evidence.
3. Implement deterministic ambiguity and deduplication.
4. Add prefix and full execution modes.

Gate: evidence traces match fixed examples and ambiguity properties.

### Phase 7 — proofs and typed extraction

1. Define `Accepting`, routine/path correspondence, and `Encodes`.
2. Prove Thompson evidence correctness constructor by constructor.
3. Implement total typed extraction.
4. Verify proof erasure and totality closure.

Gate: `parse_full` and `parse_prefix` return `Option(a)` for `Regex(a)` with no
runtime type test or impossible extraction branch.

### Phase 8 — public API and search

1. Expose typed parse, prefix, search, and boolean convenience APIs.
2. Implement source-position/capture metadata without weakening result typing.
3. Complete modifier semantics through ordered transitions and boundaries.
4. Port all retained behavioral tests.

Gate: every accepted modifier and syntax form has behavioral tests; no option is
merely retained as text.

### Phase 9 — performance and final removal audit

1. Stage literal machines at compile time.
2. Use state-indexed thread deduplication.
3. Optimize evidence representation and extraction.
4. Run benchmark families and establish regression thresholds.
5. Run full Unix and AtomVM-compatible gates where applicable.

Gate: full suite green; old Regex symbols absent; no OTP regex dependency;
proofs erased; literal artifact contains direct compiled behavior.

## 17. Acceptance criteria

The work is complete only when all of the following are true:

- the old unindexed Regex and recursive matcher are deleted;
- `/.../flags` infers a typed `Regex(result)`;
- parsing returns that result type;
- groups produce real typed evidence;
- literal parsing is compile-time-only;
- Thompson construction and the VM are pure Cure;
- acceptance and evidence correctness are proved and kernel-checked;
- extraction is total and proof-directed;
- proofs and indices erase from BEAM;
- nullable repetition terminates;
- ambiguity is deterministic and tested;
- full, prefix, and search APIs are typed;
- fixed, property-based, exhaustive, proof, trust, and performance gates pass;
- no `:re`, old shim, runtime regex parser, compatibility engine, cast, or
  `believe_me` remains.

## 18. Open implementation questions

These questions are resolved during the named phase, not by weakening the
design:

1. Whether `Sem` requires a generic large-elimination extension (Phase 1).
2. The most convenient Cure syntax for indexed Pattern constructors (Phase 2).
3. Whether `one_or_more` returns `NonEmpty(a)` or a proof-indexed list (Phase 3).
4. The finite-state representation best suited to both BEAM and AtomVM
   (Phase 5).
5. The proof-friendly epsilon-elimination representation (Phase 5).
6. Whether evidence uses snoc lists, vectors, or a dedicated builder (Phase 6).
7. The exact typed representation of source spans in `Match(a)` (Phase 8).

None of these questions permits retaining the current matcher as a fallback.
