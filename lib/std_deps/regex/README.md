# Cure Regex

`cure_regex` is Cure's native, finite, dependently typed regular-expression
engine.  It is intended to replace the OTP `:re`/PCRE dependency for Cure and
to provide the same portable erased engine to BEAM and AtomVM.  The package is
currently embedded in the compiler tree at
[`lib/std_deps/regex`](../../lib/std_deps/regex); this README is the package
capability and roadmap document.

The public compile-time façade is `Std.Regex`.  The package manifest currently
exports only `Std.Regex`; the parser, machine, proof, and implementation modules
are package-internal.

## Status vocabulary

This document deliberately separates four claims:

- **Implemented** — the parser, lowering, and executable behavior exist and
  have focused regression coverage.
- **Proof gate open** — the behavior exists, but its generic soundness,
  completeness, extraction, or erasure obligation is still being discharged.
- **Planned** — specified for a later phase; it is not accepted by the current
  parser/runtime.
- **Rejected/divergent** — intentionally outside the finite Cure model, with a
  structured diagnostic or an explicitly documented semantic difference.

The current engine is not yet a claim of complete PCRE2, OTP `re`, or Elixir
`Regex` parity.  Compatibility claims must always name the pinned oracle and
the exact checked subset.

## What is implemented now

### Compile-time interface

Regex literals are parsed at compile time and lowered to typed Cure values:

```cure
mod Example
  use Std.Regex

  fn exact(input: String) -> Option(Unit) = parse_full(/abc/, input)
  fn word(input: String) -> Option(String) = parse_full(/(\w+)/u, input)
  fn all(input: String) -> List(Match(Nat)) = scan(/ab+/, input)
end
```

The literal macro preserves source locations through normalization.  Malformed
or unsupported input is rejected at the literal site with a diagnostic code,
highlighted span, explanation, and repair hint.  The parser is fuel-bounded so
hostile syntax cannot make compilation recurse without a finite limit.

The typed combinator API is also available without a literal.  It provides
predicates, exact characters, concatenation, alternation, optional/repeated
forms, captures, mapping, left/right retention, and result-shape simplification.

### Pattern grammar

The current parser admits the following forms.

| Family | Forms | Status |
| --- | --- | --- |
| Atoms | literal scalar, empty pattern, `.`, escaped scalar | Implemented |
| Composition | concatenation and ordered `A\|B` alternation | Implemented |
| Groups | capturing `(...)`, non-capturing `(?:...)` | Implemented |
| Captures | numbered positional captures; `(?<name>...)`, `(?'name'...)`, `(?P<name>...)` | Implemented; named data is an additive side channel |
| Branch reset | `(?\|a\|(b))` and nested branch-reset layouts | Implemented |
| Repetition | `*`, `+`, `?`, `{m}`, `{m,}`, `{m,n}` | Implemented; bounded counts are limited to 64 |
| Ordering | lazy `*?`, `+?`, `??`, `{m,n}?`; possessive `*+`, `++`, `?+`, `{m,n}+` | Implemented |
| Atomicity | `(?>...)` and nested atomic scopes | Implemented |
| Assertions | `(?=...)`, `(?!...)`, `(?<=...)`, `(?<!...)` | Implemented for finite admitted operands; generalized proof gate remains open |
| Conditionals | `(?(1)yes\|no)`, `(?(name)yes\|no)`, `(?(<name>)yes\|no)` | Implemented for capture participation; assertion-conditionals are being generalized |
| Anchors | `^`, `$`, `\A`, `\z`, `\Z`, word boundaries `\b`/`\B` | Implemented |
| Line breaks | `\R`; leading `(*LF)`, `(*CR)`, `(*CRLF)`, `(*ANYCRLF)`, `(*ANY)`, `(*BSR_ANYCRLF)`, `(*BSR_UNICODE)` | Implemented |
| Classes | ranges, negation, unions, escaped members, POSIX classes | Implemented |
| Generic classes | `\d`, `\D`, `\w`, `\W`, `\s`, `\S`, `\h`, `\H`, `\v`, `\V` | Implemented with ASCII/Unicode option semantics |
| Unicode | `\xHH`, `\x{...}`, `\N{name}`, `\p{...}`, `\P{...}` and pinned general-category aliases | Implemented |
| Controls | `\a`, `\e`, `\f`, `\n`, `\r`, `\t` and ordinary escaped characters | Implemented |
| Scoped options | `(?i:...)`, `(?m:...)`, `(?s:...)`, `(?u:...)`, `(?U:...)`, with `-` removals | Implemented |

The parser recognizes the literal modifier string `i m s x u f U E` (in any
order, with repeated modifiers idempotent):

- `i` caseless matching;
- `m` multiline line anchors;
- `s` dot-all;
- `x` extended source mode (unescaped whitespace and `#` comments are removed
  while escaped/class content is preserved);
- `u` Unicode generic classes and case folding;
- `f` first-line-only search;
- `U` ungreedy defaults, while explicit lazy/greedy markers retain their
  explicit intent;
- `E` is accepted and carried by the Cure-facing option surface.

Scoped `x`, `f`, and `E` are intentionally not admitted yet: `x` needs a
canonical source-map contract inside scopes, while `f` and `E` are execution
or export-level controls rather than lexical pattern semantics.

### Typed result and execution APIs

`Std.Regex` exposes full parsing, prefix parsing, search, scanning, splitting,
replacement, named-capture lookup, and boolean matching:

```text
parse_full(/(a)(b)/, input)              # Option(Tuple(String, String))
parse_prefix(/a+/, input)                # Option(Tuple(List(Char), String))
search(/ab/, input)                      # Option(Match(Unit))
search_named(/(?<word>ab)/, input)       # Option(NamedMatch(Unit))
scan(/,+/, input)                        # List(Match(Unit))
split_default(/,+/, input)               # List(String)
replace_literal(/\d+/u, input, "X")      # String
matches(/^abc$/m, input)                 # Bool
```

`Match` records the typed value, prefix, matched text, suffix, scalar start
offset, and scalar length.  The typed value is constructed from the indexed
`ShapeCode` semantics, not from an untyped runtime tuple.  Named capture
metadata is additive: it reports participation as `Some(text)` or `None()` and
does not change existing typed result shapes.

Search order is deterministic: alternation, repetition, greediness/laziness,
possessive commitment, atomic scopes, captures, and empty-match scan progress
all follow the machine's ordered-thread semantics.  The default subject model
is a complete Cure `String` of Unicode scalar values; offsets count scalars,
not host binary bytes.

### Machine and proof foundation

The implementation lowers patterns to an indexed Thompson-style finite machine:

- `ShapeCode` indexes the typed semantic result;
- `Bounded(n)` indexes machine states, so state references cannot be out of
  range;
- transition rows and start lists are staged and checked against the canonical
  machine;
- captures and assertion observations are represented by finite evidence and
  replay routines;
- ordered search returns accepting paths, typed extraction evidence, or finite
  refutation trees;
- lookaround machines carry their own existential state-count index;
- proof/index metadata is erased from generated BEAM code.

Positive and negative lookaround decisions are checked values rather than free
booleans.  Nested assertions consume a finite depth budget.  Lookbehind uses a
finite retained history window and exact scalar width.  Atomic and possessive
paths use an explicit commitment relation, including inside assertions and
around assertion boundaries.  Capture participation created by a successful
assertion can be observed by a later conditional and is replayed for named
captures.

The executable behavior and many local correspondence lemmas are present.
The generalized assertion refutation soundness/completeness audit, exhaustive
comparison of every admitted machine shape, and the final Phase 2 exit gate are
still open.  This is why the implementation is useful today but must not yet
be described as fully proved.

## Explicit current limits

The following are rejected by the current finite parser or remain deliberately
outside the admitted execution subset:

- numeric/octal ambiguity (`\1`, `\123`) and general numeric or named
  backreferences (`\1`, `\k<name>`);
- recursive and subroutine calls (`(?R)`, `(?1)`, `(?&name)`), `DEFINE`, and
  recursive conditionals;
- unbounded or variable-length lookbehind and lookbehind wider than the finite
  history limit;
- unsupported inline scoped `x`, `f`, and `E` controls;
- arbitrary PCRE control verbs, callouts, embedded code, host callbacks, raw
  byte `\C`, runtime pattern hooks, and host JIT/NIF escape hatches;
- any syntax or expansion that exceeds parser, repetition, capture, assertion,
  Unicode-table, or machine resource limits.

These are structured compile/runtime failures, never silent fallback to OTP
`:re`, PCRE, a process-global cache, or an incomplete “fuel means no match”
answer.  A valid finite search may return `NoMatch`; exhaustion, malformed
input, unsupported syntax, and resource refusal remain distinguishable.

## Planned capability sequence

The roadmap is intentionally ordered.  Later compatibility work cannot paper
over a missing proof or portability obligation in the erased engine.

### Phase 2 — generalized assertions and proof closure

Complete the current assertion foundation with generic recursive inside-out
expansion, complete finite refutation certificates, exact/bounded nested
lookbehind, and proofs for:

1. machine-denotation agreement for every admitted transition;
2. positive witness soundness and negative refutation completeness;
3. ordered capture/backtracking and atomic commitment;
4. boundary, newline, history, and depth-limit correctness;
5. typed extraction and proof/index erasure;
6. exhaustive bounded-subject oracle agreement.

### Phase 3 — finite PCRE-family syntax and controls

Add each feature as a complete vertical slice: parser, normalized syntax,
typed lowering, finite control metadata, execution, evidence, theorem or
preservation certificate, extraction, diagnostics, erasure, properties, oracle
comparison, and AtomVM vectors.

The planned families are:

- richer newline/BSR policies and Unicode names/properties;
- Unicode binary properties, scripts, script extensions, bidi properties, and
  a generated finite grapheme-break (`\\X`) machine;
- quoted literals (`\\Q...\\E`) and additional explicitly finite escapes;
- duplicate-name policy and any remaining capture-layout compatibility;
- assertion conditionals and the admitted assertion/atomic combinations;
- finite controls such as `(*MARK)`, `(*FAIL)`, and `(*ACCEPT)`;
- only after their algebra is proved, candidates such as `(*THEN)`, `(*PRUNE)`,
  `(*SKIP)`, and `(*COMMIT)`.

The engine will continue to reject controls whose meaning depends on an opaque
host backtracking optimizer.

### Phase 4 — proof-carrying normalization

Unsupported-looking source syntax may be translated only on the parsed syntax
tree, never by ad-hoc source rewriting.  Each translation must produce a
checked certificate preserving all observable behavior: acceptance, selected
ordered match, captures and participation, spans, atomic/control effects, and
diagnostics.

The planned finite translations are:

- bounded variable-lookbehind to exact-width alternatives;
- finite-domain backreferences to enumeration, tries, or a finite register
  machine;
- nested assertions to the shared finite assertion program;
- acyclic subroutine calls to compile-time inlining;
- statically bounded recursion to finite unrolling;
- finite `(*FAIL)`/`(*ACCEPT)` control transitions.

If finiteness, termination, capture-layout compatibility, ordered observability,
or resource bounds cannot be proved, the source remains rejected.  There is no
fuel-bounded semantic fallback that pretends an uncompleted search proves
`NoMatch`.

### Phase 5 — exact compatibility ledger

Audit every syntax, option, Unicode property, capture, replacement, split,
return-shape, and error family against pinned versions of OTP `re`, Elixir
`Regex`, PCRE2, and Unicode data.  Every row must be classified as:

1. directly supported and proved;
2. translated with a checked preservation certificate;
3. deliberately divergent, with executable documentation; or
4. unsupported, with a stable diagnostic and rationale.

The published claim will name the exact profile and will not imply total PCRE
compatibility.

### Phase 6 — full erased-engine stabilization

Before runtime parsing is activated, the package must pass clean dependency-
ordered builds, the complete test/doc-fence suite, TCB and totality gates,
proof/index erasure, Antigen, the canonical module pipeline, Unix/escript
smoke tests, BEAM/AtomVM behavior vectors, forbidden-dependency closure audits,
and recorded cold/warm performance budgets.  There must be no E101/E093,
compiler warnings, bare unresolved closure keys, or host regex dependency.

### Phases 7–11 — runtime patterns and AtomVM ABI

Only after Phase 6 is green, share the parser/model/normalizer with a runtime
pattern path.  The runtime path will:

1. parse pattern data with total structured diagnostics;
2. resolve captures and references and check resource limits;
3. use the same proof-carrying normalization and finite machine compiler;
4. package the hidden typed shape existentially;
5. project generic captures, scalar spans, and match results;
6. expose reusable `compile`, `run`, `run_prefix`, `scan`, `split`, and literal
   replacement operations;
7. publish a neutral, versioned Erlang ABI and an Elixir adapter;
8. package only the reachable `cure_regex` closure for AtomVM.

This is a compatibility layer, not a second matcher.  Cure's typed literal API
remains primary and never manufactures typed values from generic runtime
matches.  Ordinary calls return a final success, no-match, or diagnostic; they
do not expose a public `Continue`.  AtomVM fairness comes from normal BEAM
reductions and loop backedges, with a separate future streaming API if
incomplete-input semantics are eventually specified.

The runtime ABI will distinguish invalid/unsupported/too-large patterns from a
valid pattern that simply does not match.  Forged compiled terms, unknown
options, scalar-versus-byte offset requests, capture selection, replacement
expansion, cancellation, memory ownership, and resource limits all receive
explicit versioned contracts.

### Final package integration

The standalone erased engine is a package named `cure_regex`, with private
modules hidden behind its export surface and a thin `Std.Regex` façade.  The
eventual OTP migration is intentionally last: move `cure-otp` into
`lib/std_deps/otp` (package identity `cure_otp`) and make the stdlib depend on
it directly, without copying OTP implementations into `lib/std` and without
adding any dependency from `cure_regex` back to OTP.

## Source map

The implementation is split as follows:

| File | Role |
| --- | --- |
| [`regex.cure`](../../lib/std_deps/regex/regex.cure) | Public `Std.Regex` façade and collection/search APIs |
| [`regex_syntax.cure`](../../lib/std_deps/regex/regex_syntax.cure) | Regex literal macro entry point: expansion, failure diagnostics, and hints |
| [`regex_syntax_model.cure`](../../lib/std_deps/regex/regex_syntax_model.cure) | Compile-time syntax tree, options, capture layout, limits, diagnostics |
| [`regex_syntax_parser.cure`](../../lib/std_deps/regex/regex_syntax_parser.cure) | Fuel-bounded literal grammar |
| [`regex_syntax_class.cure`](../../lib/std_deps/regex/regex_syntax_class.cure) | Classes, ranges, POSIX forms, Unicode property syntax |
| [`regex_syntax_flags.cure`](../../lib/std_deps/regex/regex_syntax_flags.cure) | Literal modifiers, extended-mode source mapping, newline options |
| [`regex_syntax_emitter.cure`](../../lib/std_deps/regex/regex_syntax_emitter.cure) | Typed/staged machine emission |
| [`regex_core.cure`](../../lib/std_deps/regex/regex_core.cure) | `ShapeCode`, indexed `Pattern`, evidence, boundaries, language core |
| [`regex_runtime.cure`](../../lib/std_deps/regex/regex_runtime.cure) | Thompson machine, ordered search, captures, assertions, public runtime values |
| [`regex_proof.cure`](../../lib/std_deps/regex/regex_proof.cure) | Compilation, acceptance, extraction, soundness/completeness adapters |
| [`regex_language.cure`](../../lib/std_deps/regex/regex_language.cure) | Constructive pattern denotation and language semantics |

The governing sequence and gates are in the
[Regex master implementation roadmap](../../docs/superpowers/specs/stdlib/2026-08-20-regex-master-implementation-roadmap.md).
The semantic foundation is specified in the
[pure portable engine design](../../docs/superpowers/specs/stdlib/2026-08-19-pure-portable-regex-engine-design.md),
and the deferred runtime ABI is specified in the
[runtime compatibility-layer design](../../docs/superpowers/specs/stdlib/2026-08-20-runtime-regex-compatibility-layer-design.md).
