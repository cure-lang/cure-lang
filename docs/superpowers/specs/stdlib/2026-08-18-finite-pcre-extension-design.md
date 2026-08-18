# Finite PCRE-Compatible Extensions for `Std.Regex`

**Status:** proposed extension; non-blocking for the discharged dependent-regex
completion ledger

**Date:** 2026-08-18

**Parent specification:**
`2026-07-22-dependent-regex-completion-design.md`

**Reference implementation:** Erlang/OTP `re` (PCRE2), used only as a behavior
oracle in tests. Production Cure code must not call `:re`, embed a PCRE handle,
or parse regex text at runtime.

## 1. Purpose and compatibility boundary

The completed Cure engine proves a typed regular language over Unicode scalar
strings. This specification adds the useful PCRE-family features that remain
finite-state or finite-control features without replacing the proof architecture
with a backtracking interpreter.

The governing rule is:

> A feature may be added when its accepted language and its capture/control
> behavior can be represented by a finite staged machine plus finite metadata.

Every feature must therefore have:

1. a compile-time parser representation;
2. a direct lowering to checked Cure syntax, `Pattern`, or a new finite machine
   node;
3. a staged runtime artifact with no source-string parser or PCRE dispatcher;
4. a denotational semantics and machine correspondence theorem;
5. evidence/extraction behavior that remains total;
6. fixed, property, exhaustive-small-model, trust, erasure, and performance
   tests.

This is an extension of the proved regular subset, not a promise of complete
Erlang `re` or PCRE2 compatibility. The following remain permanently outside
this model unless a separate foundational design is approved:

- general backreferences and subroutine recursion;
- callouts, runtime callbacks, and opaque compiled-pattern handles;
- raw-byte matching (`\\C`) through Cure's Unicode-scalar `String` type;
- runtime regex parsing;
- any construct whose semantics requires unbounded subject equality or an
  unbounded call stack.

## 2. Existing invariants that must not change

The implementation continues to use the boundaries established by the parent
specification:

- `Std.Regex.Syntax.*` parses and emits literals at compile time;
- `Std.Regex.Core` owns `ShapeCode`, `Sem`, `Simplify`, `Pattern`, evidence, and
  extraction;
- `Std.Regex.Runtime` owns finite machines, transition rows, boundaries, and
  the VM;
- `Std.Regex.Proof` owns constructor-complete Thompson correspondence,
  acceptance, and extraction certificates;
- `Std.Regex.Language` owns denotation, soundness, and completeness;
- `Std.Regex` owns the typed public API;
- `Bounded(n)` remains the state index;
- proof and index arguments remain erased and absent from emitted BEAM;
- all character classification and scalar conversion remains in `Std.Char`;
- the staged literal path remains direct machine construction, not a runtime
  reconstruction of `Pattern`.

No extension may add a compatibility wrapper, a late bare-name lookup, an OTP
regex dependency, an unchecked cast, a proof postulate, or an impossible
fallback.

## 3. Semantic layers and shared data structures

### 3.1 Syntax layer

Extend `Std.Regex.Syntax.Parser` with explicit nodes for the features below.
Do not represent them as untyped atoms or leave them for the runtime. Every
node carries source offsets so malformed and unsupported forms can produce the
same structured diagnostic shape as existing literals.

The parser must produce a normalized syntax model before emission:

```text
RegexSyntax
  : CoreSyntax
  | LineBreakSyntax(LineBreakPolicy)
  | UnicodeNameSyntax(UnicodeScalar)
  | NamedGroupSyntax(CaptureName, RegexSyntax)
  | BranchResetSyntax(List(RegexSyntax))
  | LookaheadSyntax(AssertionPolarity, RegexSyntax)
  | LookbehindSyntax(AssertionPolarity, Width, RegexSyntax)
  | AtomicSyntax(RegexSyntax)
  | ConditionalCaptureSyntax(CaptureRef, RegexSyntax, Option(RegexSyntax))
```

The concrete syntax forms are checked before lowering. In particular, a parser
must never reinterpret a malformed `(?<...` as a literal or silently turn an
unsupported construct into an ordinary group.

### 3.2 Width and purity analysis

Add a compile-time structural analysis used by lookbehind, capture conditionals,
and resource checks:

```text
Width = Exact(Nat) | Bounded(Nat) | Unbounded
CaptureEffect = NoCaptures | Captures(CaptureLayout)
```

The analysis is conservative. `Unbounded` is not accepted where an exact or
bounded width is required. Assertion operands in the first implementation must
be `NoCaptures`; supporting captures inside assertions is a later, separately
proved extension because PCRE makes those captures visible to the surrounding
match.

### 3.3 Capture layout

Capture numbering must become explicit compile-time metadata rather than an
implicit traversal convention. Introduce a `CaptureLayout` containing:

- stable slot IDs;
- source span and display name, if any;
- the typed shape path for ordinary typed extraction;
- participation policy;
- branch-reset scope, if any.

The layout is metadata, not part of `ShapeCode`, unless a feature changes the
typed result itself. Existing unnamed groups retain their current behavior and
existing BEAM tuple shapes. New APIs use a separate wrapper type instead of
changing the existing `Match(a)` tuple representation.

### 3.4 Finite execution context

Extend the VM context, not the unbounded machine state index, with:

- a bounded subject-history window for fixed-length lookbehind;
- a finite capture-participation mask;
- an atomic-commit scope stack bounded by the compiled syntax depth;
- newline policy and current boundary facts.

The context is runtime data. Its maximum size is checked at compile time and is
included in the performance report. Deduplication keys must include every
context field that can affect future acceptance or evidence; two threads may not
be merged merely because their `Bounded(n)` state is equal.

## 4. Feature tiers and implementation order

Implement the features in this order. Each phase is red-test first, focused
green, proof gate, full relevant suite, documentation update, and commit.

1. `\\R`, `\\N`, and explicit newline policy;
2. named captures and the capture layout;
3. branch-reset groups;
4. capture-participation conditionals;
5. atomic groups and possessive quantifiers;
6. fixed/bounded lookahead and lookbehind;
7. combined differential and exhaustive gates.

The order is intentional: later features depend on explicit capture slots and
finite execution context, and lookaround depends on the boundary/history model.

## 5. Phase A — newline and Unicode-name extensions

### 5.1 `\\R` semantics

Add a `LineBreak` pattern whose result is a `String`, not a `Char`, because
`CRLF` is one logical line-break token but two Unicode scalars. The accepted
forms are:

- LF (`U+000A`);
- CR (`U+000D`);
- CRLF as one sequence;
- Unicode line separators `U+0085`, `U+2028`, and `U+2029` under the Unicode
  policy.

The default policy is `Unicode`, with CRLF preferred over the individual CR and
LF alternatives. Matching consumes both scalars for CRLF; `Match.start` and
`Match.length` remain Unicode-scalar offsets, so a CRLF match has length two.
The captured `String` contains the exact subject scalars.

Do not implement this as a single `Char -> Bool` predicate. The staged artifact
must contain the finite sequence alternatives and its evidence must account for
both characters.

### 5.2 Newline policies

Add a closed compile-time option:

```text
NewlinePolicy = LF | CRLF | AnyCRLF | AnyUnicode
```

It controls `\\R`, dot/newline behavior, `^`, `$`, `\\A`, `\\z`, and `\\Z` only
where the selected policy is semantically relevant. The implementation must
define the interaction matrix before accepting syntax:

| Policy | line terminator set | CRLF treatment |
|---|---|---|
| `LF` | LF | CR is ordinary |
| `CRLF` | CRLF | pair is one line break |
| `AnyCRLF` | CR, LF, CRLF | CRLF is preferred pair |
| `AnyUnicode` | AnyCRLF plus NEL/LS/PS | CRLF is preferred pair |

Leading PCRE-style controls `(*LF)`, `(*CRLF)`, `(*ANYCRLF)`, and `(*ANY)` are
accepted only at the beginning of a literal, are lowered into this option, and
are rejected when repeated or conflicting. The spelling `(*BSR_...)` is handled
by the same policy parser; it must not become a runtime control instruction.

The line-start and line-end facts used by boundary constraints must be computed
from the same policy as `\\R`. Add a focused matrix for every policy crossed with
LF, CR, CRLF, NEL, LS, and PS subjects, including search and scan progress.

### 5.3 `\\N` and Unicode character names

Support:

- `\\N{NAME}` for a Unicode character name;
- `\\N{U+10FFFF}` for an explicitly named scalar form;
- bare `\\N` as the documented non-newline class if retained for the selected
  PCRE compatibility target.

Name lookup is compile-time only. `Std.Char` owns the Unicode-versioned table
and scalar validation; regex syntax asks it for a `Char` and never performs raw
code-point arithmetic. The table version is recorded in the generated artifact
and the performance baseline.

Normalization rules must be explicit: accepted spelling, case-folding, spaces,
hyphens, aliases, and control-character names are fixed by a checked table
generator. Unknown names, empty names, malformed `U+` forms, surrogate values,
and values above `10FFFF` receive dedicated diagnostics with the exact source
subspan.

### 5.4 Phase A proof and tests

Add:

- denotational line-break and policy definitions;
- lowering lemmas from `LineBreak` to the finite sequence machine;
- boundary-policy equivalence lemmas;
- Unicode-name lookup soundness (`name -> scalar` agrees with the pinned table);
- fixed tests for every policy and escape form;
- property tests over all line-break scalars and generated names;
- source tests proving no runtime name lookup and no OTP regex call;
- BEAM tests proving the table and proof metadata do not introduce erased
  indices or parser/runtime dispatch.

## 6. Phase B — named captures

### 6.1 Syntax and validation

Accept the PCRE spellings `(?<name>r)`, `(?'name'r)`, and `(?P<name>r)`.
Names must be non-empty, start with the documented identifier class, and use
only the documented identifier characters. The three spellings normalize to one
`NamedGroupSyntax` node.

Reject duplicate names in Phase B. Duplicate-name and `dupnames` behavior are
not inferred from PCRE; they require a later layout design.

### 6.2 Semantics

A named group has the same language and typed result as an ordinary group. The
name is metadata identifying the capture slot; it does not change `ShapeCode`,
`Sem`, or the existing positional extraction path. A named group still captures
the exact Unicode-scalar subject partition, including empty captures.

Add an additive result type rather than changing the existing `Match(a)` tuple:

```text
type NamedMatch(a)
  NamedMatch : Match(a) -> List(NamedCapture) -> NamedMatch(a)

type NamedCapture
  NamedCapture : String -> Option(String) -> NamedCapture
```

The public API adds `search_named`, `parse_full_named`, and a total lookup helper
for `NamedMatch`. Existing `search`, `parse_full`, and `Match(a)` remain binary
compatible. The initial named API exposes capture text; typed positional values
remain available through the wrapped `Match(a)`. A generated typed-name view is
optional future work and is not needed for PCRE syntax parity.

### 6.3 Runtime and proof changes

Add explicit capture-slot IDs to capture instructions and the capture ledger.
Names are not carried in proof indices. The evidence certificate proves the
same capture partition as before; a separate erased/effect-free theorem proves
that the layout maps each slot to its declared name. Unmatched slots return
`None`; empty participating captures return `Some("")`.

Test nested, empty, alternate, repeated, and Unicode named captures. Add
diagnostics for malformed names, duplicate names, and name syntax that conflicts
with lookbehind (`(?<=`) or other reserved prefixes.

## 7. Phase C — branch-reset groups

### 7.1 Syntax and capture allocation

Accept `(?|r1|r2|...)`. The group is an ordered alternation whose capture
numbers restart at the same base for every arm. Ordinary typed alternation still
returns `Choice`; branch reset changes only capture-slot allocation and names.

The capture-layout pass assigns each arm a local slot region and joins those
regions at the branch-reset boundary. Each corresponding slot must have a
compatible capture policy. In Phase C:

- the number of captures in every arm must be equal;
- corresponding named slots must have the same name or be unnamed in every arm;
- nested branch-reset scopes must be balanced;
- typed result shapes may differ because the ordinary regex result is still a
  `Choice`.

Reject incompatible layouts with a structured diagnostic rather than silently
renumbering captures.

### 7.2 Machine behavior and proof

Branch reset does not add a new language operator. Lower it to the existing
ordered alternation machine plus the joined `CaptureLayout`. Capture evidence
must carry slot IDs so that the winning arm populates the shared slots and the
losing arm cannot leak stale values.

Prove layout preservation separately from language preservation. Add tests for
ordinary groups around branch reset, nested branch reset, named slots, empty
arms, greedy/lazy repetition, and failure after one arm has partially captured.

## 8. Phase D — capture-participation conditionals

### 8.1 Supported forms

Support only conditions asking whether an earlier capture participated:

- `(?(1)yes|no)`;
- `(?(<name>)yes|no)`;
- `(?(name)yes|no)` where the name resolves unambiguously.

The assertion condition forms `(?(?=r)yes|no)`, recursion conditions, and
subroutine conditions remain rejected. The referenced slot must be defined
earlier in the enclosing scope and may not be the conditional's own descendant.
The `no` arm is optional and lowers to an empty branch.

### 8.2 Typed semantics

`PatternConditional` has the same shape rule as ordered alternation: the result
is a `Choice` of the yes/no arm shapes. A chosen arm emits the corresponding
choice evidence. Participation is a finite Boolean fact, not a backreference
comparison and not a string equality test.

The capture-participation mask is part of the VM deduplication key. Threads at
the same machine state with different masks must not be collapsed. On a
successful group close, set the slot bit; on a failed or non-entered group,
leave it clear. The mask is reset according to the ordinary capture scope and
branch-reset layout rules.

### 8.3 Proof and tests

Define participation in the denotational semantics and prove that the runtime
mask agrees with it at every conditional boundary. Test optional captures,
nested conditionals, alternatives that fail after participation, named and
numeric references, empty captures, and interactions with branch reset. Add a
property that changing only a non-referenced capture cannot change the result.

## 9. Phase E — atomic groups and possessive quantifiers

### 9.1 Syntax lowering

Accept `(?>r)` and possessive forms:

- `r?+`, `r*+`, `r++`;
- `r{m,n}+`, `r{m,}+`, and `r{m}+`.

Lower each possessive quantifier to an atomic scope around its greedy form.
Atomic groups may be nested, but the scope depth is checked against a fixed
compile-time limit.

### 9.2 Ordered commitment semantics

Atomicity is a control policy, not a new denotational language constructor. At
the first successful exit from an atomic scope, discard lower-priority sibling
threads created inside that scope and prevent later re-entry into them. The
scope records its commit identity in the finite execution context.

Do not implement atomicity by invoking a host backtracking engine. The staged
artifact must contain explicit commit markers or a directly compiled equivalent
in the Cure VM.

### 9.3 Proof obligations

Extend the ordered-choice theorem with a commitment invariant:

1. before commit, all live threads represent the ordered prefixes allowed by the
   scope;
2. at commit, the selected exit is the highest-priority successful exit;
3. after commit, discarded alternatives are unreachable by definition;
4. evidence from the selected thread remains total and extraction-safe.

The language theorem must distinguish ordinary greedy semantics from atomic
semantics where the accepted language differs because later outer alternatives
are deliberately unavailable. Add a reference interpreter in Elixir tests only
for finite patterns; it is never part of production or proof code.

### 9.4 Tests

Cover the classic cases where `(?>a|ab)c` and `a++a` differ from ordinary
backtracking, nested scopes, empty nullable operands, captures inside atomic
groups, and all bounded-quantifier variants. Verify no infinite loop for
nullable possessive repetition and no proof/index data in emitted BEAM.

## 10. Phase F — fixed and bounded lookaround

### 10.1 Supported subset

Accept positive and negative lookahead `(?=r)` and `(?!r)` with regular,
capture-free operands. Accept positive and negative lookbehind `(?<=r)` and
`(?<!r)` only when width analysis proves an exact scalar width or a bounded
width below the configured limit. The initial implementation may require every
lookbehind alternative to have the same exact width; variable-width support is
not inferred from a maximum bound.

Nested assertions, captures inside assertions, and assertion conditionals are
rejected in Phase F with dedicated diagnostics. They can be proposed later
after this phase has independent evidence and performance data.

### 10.2 Zero-width semantics

An assertion consumes no subject scalars and contributes `Unit` to the typed
result. A positive assertion succeeds when its operand accepts at the current
cursor; a negative assertion succeeds when it does not. The assertion's own
capture/evidence stream is discarded because operands are capture-free.

Lookahead runs a separately staged finite assertion machine against the suffix.
Lookbehind runs a reversed or bounded-window assertion machine against the
history immediately preceding the cursor. The history window is updated after
every consumed scalar and is never allowed to grow with the subject.

### 10.3 Search and boundary behavior

Assertions see the same newline policy, Unicode classification, and absolute
subject boundaries as the enclosing match. `search`, `scan`, empty-match
progress, and `Match` offsets must remain defined in Unicode scalars. A
zero-width successful assertion alone must not advance the cursor; the existing
one-scalar progress rule applies to scan/search loops.

### 10.4 Proof obligations

Generalize the language relation from `pattern` over a suffix to
`pattern_at(subject, cursor, history)`. Prove:

- positive and negative assertion correspondence;
- fixed-width reversal/window equivalence for lookbehind;
- assertion non-consumption;
- preservation of existing evidence and capture extraction;
- termination under nested VM calls and the compile-time assertion-size limit.

The staged assertion machine must be included in the closure and transition-row
proofs. It must not call `thompson_machine` at runtime or rebuild a child machine
per attempt.

### 10.5 Tests

Add fixed and generated tests for positive/negative lookahead, one- and
multi-scalar lookbehind, failure at subject start, CRLF and Unicode boundaries,
search at every cursor, nullable assertions, and interactions with atomicity,
conditionals, and named captures where those combinations are permitted.

## 11. Diagnostics and limits

Replace the current unsupported diagnostics only when the corresponding phase
is implemented. Add full structured diagnostics for:

- `InvalidUnicodeName`;
- `UnicodeNameOutOfRange` and `UnicodeNameSurrogate`;
- `DuplicateCaptureName`;
- `InvalidCaptureName`;
- `BranchResetCaptureLayoutMismatch`;
- `UndefinedCaptureCondition`;
- `RecursiveCaptureCondition`;
- `InvalidNewlinePolicy` and `ConflictingNewlinePolicy`;
- `VariableLengthLookbehind`;
- `LookbehindTooWide`;
- `AssertionCapturesUnsupported`;
- `NestedAssertionUnsupported`;
- `AtomicScopeTooDeep`;
- `AssertionStateLimit`;
- `CaptureLayoutLimit`.

Each error must name the declaration/literal, exact source span, failing syntax
node, expected restriction, and an actionable replacement. Do not collapse these
into a generic “unsupported regex” error.

Resource limits are compile-time, deterministic, and visible in diagnostics:

- maximum Unicode-name table version and generated table size;
- maximum capture slots and participation-mask width;
- maximum atomic-scope depth;
- maximum lookbehind width;
- maximum assertion machine states and nested assertion depth;
- maximum staged artifact size.

The limits must be tested at the boundary and must not be bypassed by macros.

## 12. Verification matrix

Every phase must add all of the following before being marked discharged:

1. focused red tests for accepted and rejected syntax;
2. fixed semantic tests against an independent finite reference;
3. `Antigen.Backend.StreamData` properties over small patterns and subjects;
4. exhaustive small-model coverage over a documented depth and alphabet;
5. proof-module kernel, totality, and termination checks;
6. capture-layout and machine-closure checks;
7. BEAM erasure/source scans proving no OTP `:re`, parser, PCRE handle, or
   proof/index artifact is emitted;
8. differential tests against Erlang `:re` only for the explicitly supported
   subset, with each intentional semantic difference recorded;
9. cold/warm compile and runtime benchmarks, including assertion and capture
   context sizes;
10. canonical pipeline, docs-fence, Unix/escript, AtomVM, and full-suite gates.

The differential oracle must compare normalized observations, not raw tuple
shapes: Cure uses Unicode-scalar offsets and typed values, while `re` uses
PCRE/Erlang capture conventions. Unsupported PCRE constructs must be tested as
diagnostic cases, never as silent divergence.

## 13. Acceptance criteria

The extension is complete only when:

- all seven feature families have explicit parser, lowering, runtime, proof,
  and diagnostic implementations;
- ordinary existing regex programs have unchanged semantics and BEAM shapes;
- named captures and branch-reset allocation are deterministic and total;
- conditional masks and atomic scopes participate in thread deduplication;
- lookaround is finite, bounded, capture-free in the initial release, and
  zero-width by construction;
- newline policy is shared by `\\R`, boundaries, dot, search, and scan;
- Unicode-name lookup is compile-time and pinned to a documented Unicode table;
- the three-certificate chain and Cure soundness/completeness theorems still
  pass for the extended algebra;
- proof/index arguments remain absent from runtime artifacts;
- no runtime parser, OTP regex call, PCRE handle, cast, or fallback exists;
- all fixed/property/exhaustive/trust/erasure/differential/performance/platform
  gates are green;
- the parent completion ledger remains discharged for its original scope and
  this document records the new extension's own status.

## 14. Explicit non-goals

This specification does not add:

- backreferences (`\\1`, `\\k<name>`, `\\g{name}`);
- recursion or subroutine calls (`(?R)`, `(?1)`, `(?&name)`);
- conditional assertions or recursion conditions;
- duplicate-name/`dupnames` semantics until a separate capture-layout design;
- captures inside lookaround;
- unbounded or unequal-alternative lookbehind;
- PCRE callouts, verbs with host callbacks, or runtime replacement programs;
- a compatibility wrapper around Erlang `re`.

Those features either require a different semantic model or need a separate
proposal demonstrating that the finite, typed, proof-directed invariants can be
preserved.
