# Pure, Portable, Proof-Backed Regex Engine

**Status:** proposed follow-on design

**Date:** 2026-08-19

**Parent specifications:**

- `2026-07-22-dependent-regex-completion-design.md`
- `2026-08-18-finite-pcre-extension-design.md`

**Decision:** Cure's regex implementation is the production semantic
implementation. Erlang `:re`/PCRE2 are test oracles only. The production
closure must run without `:re`, NIFs, ports, opaque PCRE handles, or a runtime
regex parser on both BEAM and AtomVM. The erased production engine is a
separately identified Cure package, provisionally named `cure_regex`, embedded
and bundled by the stdlib release rather than merged into its public module
namespace.

This specification deliberately extends the finite-PCRE design rather than
replacing it. The finite-PCRE specification remains authoritative for the
already discharged core and for the initial bounded lookaround release. This
document changes the current restriction that lookaround operands must be
non-nested: nested assertions become a staged, depth-bounded, proof-carrying
feature instead of a permanent semantic limitation.

## 1. Motivation and scope

Cure is intended to provide a regex engine that can be embedded in firmware
and run on AtomVM, where Erlang's `:re` service is not available. A wrapper
around PCRE would therefore fail the portability goal, and a runtime
backtracking interpreter would reintroduce the proof and resource problems that
the current finite engine was built to avoid.

The implementation target is a useful, explicitly documented subset of the
PCRE family with:

- compile-time parsing and lowering;
- finite staged machines and finite control metadata;
- typed, total matching and extraction;
- deterministic resource bounds;
- identical generated behavior on BEAM and AtomVM;
- a proof boundary that can be checked by Cure's kernel and gates.

The target is not source compatibility with every PCRE2 construct. A construct
is admitted only when its language and observable match behavior can be
represented by finite data plus a bounded execution context. Unsupported
constructs must fail at compile time with a structured diagnostic.

## 2. Compatibility policy

### 2.1 Production boundary

Production Cure modules must not:

- invoke `:re`, `:re.run`, `:re.compile`, or any PCRE/PCRE2 API;
- store or pass a PCRE compiled-pattern handle;
- call a NIF, port, process, ETS table, or process-global regex cache;
- parse regex source at runtime;
- rely on Erlang binary code-unit offsets for Unicode matching;
- use host backtracking to decide acceptance.

The generated artifact contains only Cure data and functions plus the already
approved character/string primitives. Proof arguments, `Bounded(n)` indices,
and compile-time tables that are not needed by execution must be erased from
the BEAM/AtomVM artifact.

### 2.2 Oracle boundary

The test suite may use OTP `:re` (PCRE2) as an independent behavior oracle for
the documented overlap. Oracle tests must normalize differences in:

- capture tuple shape and unmatched-capture representation;
- Unicode-scalar versus byte offsets;
- named-capture ordering;
- empty-match scan advancement;
- error wording and option spelling.

The oracle is never used to manufacture a Cure result, to fill a missing proof,
or to decide whether production code is correct. Every intentional difference
must be recorded beside the differential test.

### 2.3 Versioning

The supported Unicode data version and the oracle OTP/PCRE2 version are pinned
in the test metadata. A Unicode-table change is a semantic change: it requires
regenerating tables, rerunning differential and property suites, and updating
the compatibility ledger. A PCRE2 update changes only the oracle unless it
exposes a previously undocumented behavior that Cure elects to support.

## 3. Goals and explicit non-goals

### 3.1 Goals

The staged roadmap shall support, in order of proof and implementation risk:

1. nested positive and negative lookahead;
2. nested fixed/bounded lookbehind;
3. atomic groups and possessive choices inside assertions, and assertions
   inside atomic groups;
4. assertion conditionals and scoped inline options;
5. quoted literals (`\\Q...\\E`), Unicode script/script-extension/Bidi and
   binary properties, and grapheme clusters (`\\X`);
6. search-context anchors (`\\G`) and match-start reset (`\\K`);
7. finite backtracking-control verbs such as `(*MARK)`, `(*FAIL)`, and
   `(*ACCEPT)`, followed only by explicitly modelled forms of `(*THEN)`,
   `(*PRUNE)`, `(*SKIP)`, and `(*COMMIT)`.

The order is a dependency order, not a promise that every PCRE spelling will
be accepted. Each feature is independently specified, tested, and discharged
before the next feature relies on it.

### 3.2 Permanent non-goals

The following remain outside this design unless a new foundational
specification proves a different finite model:

- general backreferences (`\\1`, `\\k<name>`) whose equality obligation is
  unbounded in the subject;
- recursive and subroutine calls (`(?R)`, `(?1)`, `(?&name)`) with an
  unbounded call stack;
- callouts, embedded code, host callbacks, and runtime pattern hooks;
- raw-byte `\\C` semantics through Cure's Unicode-scalar `String` API;
- unbounded or runtime-computed variable-length lookbehind;
- arbitrary PCRE verbs whose semantics depend on a host backtracking engine;
- a runtime parser, JIT, or opaque compiled-pattern representation.

Rejecting these is intentional. Cure's engine is a finite, portable, typed
engine, not a reimplementation of every non-regular PCRE extension.

## 4. Package boundary, architecture, and invariants

The portable erased engine belongs to the embedded `cure_regex` package under
`lib/std_deps/regex`. The
stdlib bootstrap compiles foundational modules, then this package, then any
public `Std.Regex` façade. Package-owned source, tests, manifests, and AtomVM
artifacts live in a dedicated package subtree rather than being discovered as
ordinary `lib/std` modules or copied into generated `priv/std` sources. The
package has its own identity, dependency/source hashes, artifact manifest, and
explicit exported-module list; its private modules are available to package
code and bundled for runtime calls but are not available to arbitrary consumers.

No feature in this document may weaken the following boundaries:

- package-owned syntax/model modules provide the shared neutral representation
  and runtime-safe parsing;
- `Std.Regex.Syntax.*` is the stdlib macro façade that emits literals;
- package-owned core/runtime/proof modules own the erased semantic engine;
- `Std.Regex.Core`/`Std.Regex` compatibility adapters own the typed
  `ShapeCode`, `Sem`, `Simplify`, `Pattern`, evidence, and extraction API;
- `Bounded(n)` remains the state index;
- proof and index arguments remain erased in generated code;
- all scalar classification and conversion remains in `Std.Char`;
- the staged literal path constructs machines directly and never reconstructs a
  `Pattern` or reparses source at runtime.

The package pipeline may be embedded in the stdlib build, but it must not create
a dependency cycle from the foundational stdlib back into package internals.
The implementation may add modules, but it must not create a compatibility
wrapper around a second compiler or a second runtime. There is one canonical
syntax-to-machine path, one canonical definition identity for generated
helpers, and one canonical closure check for emitted machines.

## 5. Portable runtime contract

### 5.1 Allowed runtime representation

The runtime may use pure Cure functions and the existing inductive/tuple/list
values. It may use finite arrays represented by the established Cure data
structures and the approved `Std.Char`/`Std.String` primitives. It may carry:

- a Unicode-scalar cursor;
- a bounded lookbehind history window;
- a finite capture frame and participation mask;
- an assertion depth counter;
- finite control markers for atomicity and verbs;
- an optional scan/search context for `\\G`.

The representation must be inspectable by the compiler and have a finite size
bound derived from the literal and the configured resource limits.

### 5.2 AtomVM gate

Every feature must pass all of these checks before being called portable:

1. compile the Cure source and staged modules for the AtomVM target;
2. inspect the reachable closure for `:re`, NIF, port, ETS, process, binary
   parser, and host-regex references;
3. run the same fixed vectors under BEAM and AtomVM;
4. compare typed matches, captures, scalar offsets, marks, and scan progress;
5. inspect generated code to confirm proof/index metadata is absent;
6. run a clean build, not only a warm incremental build.

The source scan is necessary but insufficient: dynamic dispatch and generated
helpers must be checked through the canonical reachability closure as well.

## 6. Generalized assertion model

### 6.1 Current limitation

The finite-PCRE implementation currently represents an assertion as a boundary
condition containing a `Sigma(n, PatternMachine(n))`. Its child evaluator is
depth-bounded, but the syntax validator rejects an assertion operand that
contains another assertion. This makes the first proof small and keeps the
child evaluator's constraints ordinary-only.

That rejection is an implementation boundary, not a property of the regular
language. This specification replaces it with a depth-indexed assertion
program and a complete finite decision procedure.

### 6.2 Assertion program

Introduce a compile-time representation conceptually equivalent to:

```text
AssertionProgram(depth)
  = OrdinaryMachine
  | And(AssertionProgram(depth - 1), AssertionProgram(depth - 1))
  | Or(AssertionProgram(depth - 1), AssertionProgram(depth - 1))
  | Lookahead(Polarity, AssertionProgram(depth - 1))
  | Lookbehind(Polarity, Width, AssertionProgram(depth - 1))
  | Atomic(AssertionProgram(depth - 1))
  | Conditional(Condition, AssertionProgram(depth - 1), Option(...))
```

The concrete Cure types may use different constructors, but they must encode
the same invariant: every recursive child has a strictly smaller compile-time
depth. A runtime `Nat` check is not a substitute for a structurally bounded
type or a compiler-checked recursive function.

The assertion program carries the same newline, Unicode, and option context as
its parent. Option changes are lexical and are restored when the child returns;
they must not mutate sibling branches.

### 6.3 Checked decisions, not free booleans

An assertion result must not be represented solely by a `Bool` that a proof
later trusts. Positive and negative assertions need a complete finite decision
certificate:

```text
AssertionDecision
  = Satisfied(AssertionPath)
  | Refuted(AssertionFailureCertificate)
```

`AssertionPath` records the accepted child transitions, boundary context,
history window, nested decisions, and remaining input. A refutation certificate
records that the finite child search explored every possible accepting path and
found none. It may be represented compactly by a checked finite-state failure
summary, but it must not be implemented as `not child_accepts(...)` without a
completeness proof.

The parent proof consumes the appropriate constructor:

- positive assertion consumes `Satisfied(path)`;
- negative assertion consumes `Refuted(certificate)`;
- a failed positive or successful negative assertion is an ordinary total
  branch failure, not an unchecked exception or an impossible value.

This is especially important for nested negative assertions: a child can
contain another negative assertion, so the child decision itself must already
be certified before the parent can establish refutation.

### 6.4 Boundary and history semantics

Assertions are zero-width. Lookahead observes the suffix beginning at the
parent cursor. Lookbehind observes only the bounded scalar history immediately
before that cursor. A nested lookbehind uses the same history model, with its
own exact or bounded width checked before lowering.

The initial nested release remains capture-free. Captures inside assertions are
not rejected forever, but they require a separate capture-frame specification:
PCRE makes assertion captures visible to the surrounding match, and silently
discarding them would be unsound. Until that specification is discharged,
`AssertionCapturesUnsupported` remains a valid diagnostic even when nested
assertions are accepted.

### 6.5 Resource limits

The compiler calculates, records, and checks:

- maximum nested assertion depth;
- maximum child machine states and transition rows;
- maximum exact/bounded lookbehind width;
- maximum capture/participation metadata;
- maximum combined staged artifact size;
- maximum control-context width.

Exceeding a limit produces a compile-time diagnostic. It must never silently
turn a match into `false`, truncate a child machine, or use an unbounded
runtime recursion. The configured limits are part of the generated literal's
fingerprint so an incremental build cannot reuse an artifact under different
semantics.

## 7. Feature phases

### Phase 0 — portability guardrails

Before changing syntax or proofs:

1. add a production-closure test that fails if `:re`, NIF, port, ETS, process,
   or runtime parser symbols are reachable;
2. add a BEAM/AtomVM smoke fixture with ordinary literals, captures, lookahead,
   lookbehind, search, scan, and empty-match progress;
3. record clean and warm compile baselines;
4. document the supported Unicode data version and resource-limit defaults.

### Phase 1 — recursive assertion witnesses

Implement the assertion program and decision certificates without changing the
public match shape:

1. preserve a red test for nested capture-free positive lookahead;
2. implement depth-indexed lowering and structurally decreasing evaluation;
3. implement complete finite refutation certificates for negative assertions;
4. generalize `LookaroundPath`/`LookaroundSearchPath` to contain nested child
   decisions;
5. prove soundness, completeness, termination, and non-consumption;
6. add exact-width nested lookbehind and boundary-start failures;
7. replace `NestedAssertionUnsupported` only for forms now covered by proofs.

Required examples include:

```text
(?=(?=a)a)a
(?!(?=b)b)a
(?<=a(?=b))b
(?<!a(?!b))c
```

The exact surface forms accepted depend on the parser's grouping rules; the
tests must state the intended scalar-language meaning rather than rely on a
PCRE error string.

### Phase 2 — assertion interactions

Add, in separate commits:

- atomic groups and possessive quantifiers inside assertions;
- assertions inside atomic groups;
- assertion conditionals;
- scoped inline options inside assertion operands.

The evaluator must preserve ordered-choice and commitment semantics across a
child boundary. A child commit cannot mutate its parent or a sibling branch.
Conditionals inspect only the finite capture/participation state that the
capture specification permits; they may not introduce an implicit host stack.

### Phase 3 — syntax and Unicode semantics

Add compile-time nodes and direct lowering for:

- `\\Q...\\E` quoted literals (with explicit handling of a literal `\\E`);
- scoped modifiers such as `(?im-sx:...)`;
- Unicode script, script-extension, Bidi, and binary properties;
- `\\X` extended grapheme clusters.

Unicode properties lower to generated finite predicates over `Std.Char`. The
property table version is part of the artifact fingerprint. `\\X` lowers to a
finite UAX #29 grapheme-break machine and returns a scalar-string atom; it is
not implemented by splitting host binaries or by calling a Unicode library at
runtime. Grapheme clusters are variable scalar width but have a finite
property-state machine and explicit maximum artifact/resource checks.

### Phase 4 — finite search controls

Add only controls with explicit Cure semantics:

- `\\K`: reset the reported match start without rewinding consumed input;
- `\\G`: match at the caller-provided scan/search cursor;
- `(*MARK:name)`: carry a finite mark in the match result;
- `(*FAIL)` and `(*ACCEPT)`: explicit finite branch outcomes.

`\\G` requires an explicit search-context field in the public or internal API;
it must not read process state. `\\K` requires an additive match-span policy so
existing `Match` values remain source-compatible. `MARK` likewise requires an
additive optional mark result, not a hidden side channel.

Only after those controls are proved may the project consider `(*THEN)`,
`(*PRUNE)`, `(*SKIP)`, or `(*COMMIT)`. Each must lower to an explicit finite
control algebra and have tests showing how it changes ordered search; copying
PCRE backtracking behavior is not a specification.

### Phase 5 — stabilization

Run the full verification matrix, portability gates, performance benchmarks,
and documentation-fence suite. Update the finite-PCRE specification's Phase F
and non-goal wording only after the corresponding phases are discharged.

## 8. Feature semantics that require explicit decisions

### 8.1 Atomic and non-atomic assertions

The first recursive assertion release permits only the existing atomic policy:
the child machine's ordered successful exit is committed according to the
compiled scope. General PCRE2 non-atomic lookaround requires retaining and
re-entering child alternatives after the parent has progressed. It must not be
quietly approximated by the current atomic evaluator. Treat non-atomic
lookaround as a later feature with its own path-order and resource theorem.

### 8.2 Assertion captures

Captures in lookaround are a separate API decision. The implementation must
choose and prove one of:

1. expose assertion captures in the surrounding capture frame exactly;
2. expose them in a separate assertion-result field;
3. reject them with a structured diagnostic.

The current release chooses (3), including for nested assertions.

### 8.3 Lookbehind

Lookbehind accepts only exact scalar width in the first recursive release.
Bounded finite width may follow if the path and history theorem proves all
alternatives are enumerated. Runtime scanning backwards through host bytes is
never allowed. If width analysis returns `Unbounded` or cannot prove a common
width, emit `LookbehindWidthUnknown` or `VariableLengthLookbehind` with the
offending syntax node and the required rewrite.

### 8.4 Search controls

`\\G`, `\\K`, and marks affect observations, not the accepted scalar language.
Their state must be threaded through the typed result and included in proof
correspondence. A scan loop must define empty-match progress and cursor reset
in scalar units. There is no hidden mutable cursor.

## 9. Proof and kernel obligations

Each phase must discharge all of the following before its feature is enabled by
default:

1. **Syntax-lowering soundness:** every accepted syntax node lowers to exactly
   the intended finite machine/control program.
2. **Machine denotation:** every transition row has a finite, canonical meaning
   and no missing closure key.
3. **Assertion decision soundness:** `Satisfied` implies an accepting child
   path; `Refuted` implies complete exploration with no accepting child path.
4. **Assertion decision completeness:** every finite child acceptance or
   refutation produces the matching certificate.
5. **Depth termination:** recursive assertion evaluation decreases the indexed
   depth and cannot loop through a nullable assertion forever.
6. **Boundary correctness:** lookahead, lookbehind, absolute start/end, CRLF,
   and Unicode scalar boundaries agree between syntax, machine, and language.
7. **Ordered-control correctness:** atomic scopes and control verbs preserve
   their documented priority/commit behavior.
8. **Typed extraction:** accepted evidence is sufficient for total conversion;
   no result is obtained from a free Boolean or an unchecked cast.
9. **Capture correctness:** any enabled capture form has a deterministic layout,
   participation mask, and extraction theorem.
10. **Unicode correctness:** generated property and grapheme tables match the
    pinned data version and are erased/embedded as intended.
11. **Portability:** the proof/runtime closure contains no host regex bridge.
12. **Erasure:** indices, proof paths, refutation certificates, and compile-time
    source metadata do not leak into emitted runtime values unless explicitly
    part of the public result (for example a mark).

Negative assertions deserve special review. The proof must establish finite
search completeness, not merely show that one attempted path failed. A test
that passes because a search was cut off at the depth limit is a bug.

## 10. Diagnostics

All new errors use the existing structured diagnostic pipeline and include the
declaration/literal name, exact source span, syntax node, expected restriction,
actual analysis, and an actionable hint. At minimum add:

- `NestedAssertionDepthExceeded`;
- `AssertionStateLimit`;
- `AssertionWitnessIncomplete`;
- `AssertionRefutationIncomplete`;
- `LookbehindWidthUnknown`;
- `LookbehindTooWide`;
- `AssertionCapturesUnsupported`;
- `AssertionAtomicityUnsupported`;
- `GAnchorRequiresSearchContext`;
- `GraphemeTableVersionMismatch`;
- `UnicodePropertyUnavailable`;
- `RegexHostDependencyDetected`;
- `AtomVMUnsupportedRegexFeature`;
- `ControlVerbRequiresFiniteModel`;
- `CaptureLayoutLimit`.

An emission failure must identify the originating Core reference and closure
path. It must never surface only “no such definition”, `ArgumentError`, or a
bare “unsupported regex” string.

## 11. Testing and verification matrix

Every phase follows the red-test-first rule and adds all of these gates:

1. focused accepted and rejected syntax tests;
2. fixed semantic tests against an independent finite reference;
3. `Antigen.Backend.StreamData` properties over small patterns and subjects;
4. exhaustive small-model enumeration over a documented alphabet and depth;
5. Cure kernel, totality, termination, TCB, and erasure checks;
6. closure checks proving every reachable key is a body or legitimate extern;
7. BEAM/AtomVM output equality for matches, captures, scalar spans, marks, and
   scan progress;
8. source and reachable-closure scans for host-regex dependencies;
9. differential tests against `:re` for the explicitly supported overlap;
10. negative tests for permanently unsupported non-regular constructs;
11. cold/warm compilation and runtime benchmarks;
12. canonical pipeline, docs-fence, Unix/escript, and full-suite gates.

The fixed vector set must include nested positive and negative assertions,
lookbehind at the start boundary, nullable children, CRLF, Unicode scalar and
grapheme boundaries, atomic/nested combinations, option scoping, `\\G`, `\\K`,
marks, empty matches, and every resource-limit boundary. Include deliberately
adversarial patterns that force all child paths to be explored so incomplete
negative certificates cannot pass accidentally.

## 12. Performance and artifact requirements

The compiler must report, behind the existing trace/timing machinery:

- parser and normalization time;
- width/purity/property analysis time;
- assertion-machine construction time per literal;
- proof/certificate construction time;
- staged artifact size and transition-row count;
- warm-cache hit/miss and source/dependency fingerprint;
- runtime steps and peak finite context sizes.

No implementation may rebuild a child `PatternMachine` per match attempt or per
assertion boundary. Interfaces, Unicode tables, and assertion programs are
cached by source/dependency/options/data-version fingerprints. Cache entries are
immutable and are never allowed to change canonical identities or leak between
concurrent builds.

The performance gate records separate cold and warm baselines. A warm-cache
improvement does not justify a cold-build regression that exceeds the project's
stabilization budget. Any new cache must be measured on a clean build before it
is retained.

## 13. Migration and commit boundaries

Implement in reviewable, independently green commits:

1. portability closure/AtomVM guardrails and baseline fixtures;
2. depth-indexed assertion syntax and machine data types;
3. positive nested lookahead witnesses;
4. complete negative/refutation certificates;
5. exact-width nested lookbehind;
6. atomic/conditional/scoped-option interactions;
7. Unicode properties, quoting, and grapheme clusters;
8. `\\G`, `\\K`, marks, and finite control verbs;
9. proof, erasure, performance, and documentation stabilization.

Each commit must keep the previous supported subset working. Do not land a
syntax parser branch before its lowering, diagnostic, and red regression test
exist. Do not broaden the accepted subset by weakening a validator or replacing
an indexed witness with `Bool`.

The public `Std.Regex` API remains source-compatible. New observations such as
marks or reset spans are additive fields or explicit opt-in result types. The
ordinary match result and existing scalar-offset convention do not change.

## 14. Acceptance criteria

This specification is complete only when:

- the documented feature subset has one canonical pure Cure implementation;
- production closure has no `:re`/PCRE/NIF/host parser dependency;
- the same generated behavior runs on BEAM and AtomVM;
- nested supported assertions use indexed, compositional witnesses;
- negative assertions use complete finite refutation certificates;
- all resource limits are deterministic, diagnosed, and tested at their
  boundaries;
- enabled captures, controls, Unicode properties, and grapheme semantics have
  explicit typed results and correspondence proofs;
- every emitted closure key resolves to a body or legitimate extern;
- kernel, totality, TCB, erasure, Antigen, canonical-pipeline, docs-fence,
  Unix/escript, AtomVM, and full-suite gates are green;
- cold and warm performance baselines are recorded and within the stabilization
  budget;
- unsupported backreferences, recursion, callouts, raw-byte matching, and
  unbounded lookbehind fail with full diagnostics rather than silently using a
  host engine.

Only after these criteria are met may the compatibility ledger claim that Cure
replaces PCRE for the supported subset on both BEAM and AtomVM.

## 15. Compatibility ledger: `:re`, Elixir, and Cure

This ledger is the implementation target for the pure portable engine. The
`:re` column refers to Erlang/OTP 28's PCRE2-backed `re` module. The Elixir
column refers to `Regex` on that runtime; Elixir forwards its compilation
options to `:re`, but its public result and convenience APIs are different.
The authoritative references are the [OTP `re` documentation](https://www.erlang.org/docs/28/apps/stdlib/re.html),
[Elixir `Regex` documentation](https://hexdocs.pm/elixir/Regex.html), and the
[PCRE2 syntax reference](https://www.pcre.org/current/doc/html/pcre2syntax.html).

The Cure status columns distinguish implementation from design:

- **now** means current source and regression tests accept the form;
- **planned** means it is a committed phase of this specification;
- **finite** means it is accepted only after an exact finite translation is
  proved for that particular literal;
- **candidate** means a possible later extension, not a promise of parity;
- **no** means it remains outside the portable scalar finite model.

### 15.1 Core syntax and character semantics

| Capability | Example | `:re` | Elixir | Cure now | Cure route |
|---|---|---:|---:|---:|---|
| Literal characters | `abc` | yes | yes | yes | Existing finite machine |
| Concatenation | `abc` | yes | yes | yes | Existing finite machine |
| Empty pattern | `//` | yes | yes | yes | Existing finite machine |
| Alternation | `cat|dog` | yes | yes | yes | Existing ordered machine |
| Capturing group | `(abc)` | yes | yes | yes | Typed capture evidence |
| Non-capturing group | `(?:abc)` | yes | yes | yes | Erased grouping |
| Nested groups | `((a)b)` | yes | yes | yes | Typed nested shape |
| Control escapes | `\n`, `\r`, `\t`, `\f`, `\a`, `\e` | yes | yes | yes | `Std.Char` scalar literals |
| Two-digit hex | `\x7F` | yes | yes | yes | Compile-time scalar validation |
| Braced scalar hex | `\x{1F600}` | yes | yes | yes | Compile-time scalar validation |
| Unicode character name | `\N{LATIN CAPITAL LETTER A}` | yes | yes | yes | Pinned compile-time table |
| Octal escapes | `\123` | yes | yes | no | Possible explicit finite rewrite; not canonical now |
| Numeric ambiguity | `\1`, `\123` | yes | yes | no | Rejected as ambiguous backreference/octal syntax |
| `\u`/`\U` escapes | `\u0041` | variant-dependent | docs say no | no | Use `\x{...}` |
| Quoted literal region | `\Q[a-z]+\E` | yes | yes | no | Planned literal-sequence normalization |
| Dot | `.` | yes | yes | yes | Existing scalar predicate |
| Dotall | `/./s` | yes | yes | yes | Current `s` modifier |
| Character ranges | `[a-z]` | yes | yes | yes | Finite scalar predicate |
| Negated classes | `[^0-9]` | yes | yes | yes | Finite complement predicate |
| Class union | `[a-z0-9_]` | yes | yes | yes | Finite predicate composition |
| Escapes in classes | `[\d_]` | yes | yes | yes | Current class parser |
| POSIX classes | `[[:alpha:]]` | yes | yes | yes | Finite POSIX predicates |
| Negated POSIX classes | `[[:^digit:]]` | yes | yes | yes | Finite complement |
| Extended class algebra | `(?[[a-z]&&[^aeiou]])` | yes | yes | no | Finite predicate conjunction/difference |
| Generic digit class | `\d`, `\D` | yes | yes | yes | ASCII/Unicode mode tracked |
| Generic word class | `\w`, `\W` | yes | yes | yes | ASCII/Unicode mode tracked |
| Generic whitespace | `\s`, `\S` | yes | yes | yes | ASCII/Unicode mode tracked |
| Horizontal whitespace | `\h`, `\H` | yes | yes | yes | `Std.Char` predicates |
| Vertical whitespace | `\v`, `\V` | yes | yes | yes | `Std.Char` predicates |
| Unicode newline | `\R` | yes | yes | yes | Finite newline policy |
| Non-newline class | `\N` | yes | yes | no | Candidate complement of newline |
| General Unicode categories | `\p{L}`, `\p{Nd}` | yes | yes | yes | Pinned finite property table |
| Negated categories | `\P{L}` | yes | yes | yes | Pinned complement table |
| Unicode binary properties | `\p{Emoji}` | yes | yes | no | Planned generated predicates |
| Unicode scripts | `\p{Greek}` | yes | yes | no | Planned generated predicates |
| Script extensions | `\p{scx=Hira}` | yes | yes | no | Planned generated predicates |
| Bidi properties | `\p{Bidi_Class=AL}` | yes | yes | no | Planned generated predicates |
| Grapheme clusters | `\X` | yes | yes | no | Planned finite UAX #29 machine |
| Raw byte matching | `\C` | yes | yes | no | No scalar equivalent; separate byte API only |
| Script-run matching | `(*script_run:\p{Greek}+)` | yes | yes | no | Candidate finite property-state machine |

### 15.2 Repetition, ordering, captures, and conditionals

| Capability | Example | `:re` | Elixir | Cure now | Cure route |
|---|---|---:|---:|---:|---|
| Greedy repetition | `a*`, `a+`, `a?` | yes | yes | yes | Ordered machine |
| Exact bound | `a{3}` | yes | yes | yes | Compile-time expansion |
| Lower-bounded repeat | `a{3,}` | yes | yes | yes | Staged finite representation |
| Bounded range | `a{2,5}` | yes | yes | yes | Current compile-time limit |
| Lazy quantifiers | `a*?`, `a{2,4}?` | yes | yes | yes | Ordered lazy path |
| Possessive quantifiers | `a*+`, `a{2,4}+` | yes | yes | yes | Atomic commitment machine |
| Atomic group | `(?>a|ab)` | yes | yes | yes | Commitment proof |
| Nested atomic groups | `(?>a(?>b|bc))` | yes | yes | yes | Bounded atomic scopes |
| Automatic possessification | `A+B` optimized as `A++B` | yes | yes | no | Optimization only after proof |
| Named capture | `(?<word>abc)` | yes | yes | yes | Additive capture metadata |
| Python named capture | `(?P<word>abc)` | yes | yes | yes | Same normalized capture slot |
| Quoted named capture | `(?'word'abc)` | yes | yes | yes | Same normalized capture slot |
| Branch reset | `(?|(a)|(b))` | yes | yes | yes | Shared capture layout |
| Duplicate names | `(?J)(?<x>a)|(?<x>b)` | yes | yes | no | Candidate separate layout design |
| Capture participation | `(?(1)yes|no)` | yes | yes | yes | Finite participation mask |
| Named participation | `(?(<x>)yes|no)` | yes | yes | yes | Finite participation mask |
| Assertion conditional | `(?(?=a)b|c)` | yes | yes | no | Planned certified assertion branches |
| Recursion conditional | `(?(R)yes|no)` | yes | yes | no | Separate recursive model required |
| Subroutine conditional | `(?(R&name)yes|no)` | yes | yes | no | Separate recursive model required |
| Version conditional | `(?(VERSION>=10.4)yes|no)` | yes | yes | no | One pinned Cure semantic version |
| No-auto-capture mode | `(?n)(abc)` | yes | via `:re` | no | Possible group-normalization pass |
| Numeric backreference | `(a)\1` | yes | yes | no | Finite specialization only |
| Named backreference | `(?<x>a)\k<x>` | yes | yes | no | Finite capture-domain trie |
| Relative backreference | `\g{-1}` | yes | yes | no | Same finite restriction |
| Forward backreference | `\g{+1}` | yes | yes | no | Not in initial finite model |
| Bounded backreference | `(?<x>[ab]{2})\k<x>` | yes | yes | no | Exact enumeration/trie if size is acceptable |
| Unbounded backreference | `(?<x>.+)\k<x>` | yes | yes | no | Separate subject-indexed evaluator, not finite staging |
| Acyclic subroutine | `(?&byte)` | yes | yes | no | Compile-time inlining when call graph is acyclic |
| Statically bounded recursion | finite recursive depth | yes | yes | no | Finite unrolling |
| General recursion | `(?R)` | yes | yes | no | Outside current finite model |
| `DEFINE` block | `(?(DEFINE)(?<byte>...))` | yes | yes | no | Inline only for finite call graph |

### 15.3 Anchors and assertions

| Capability | Example | `:re` | Elixir | Cure now | Cure route |
|---|---|---:|---:|---:|---|
| Subject start | `\A` | yes | yes | yes | Absolute-start boundary |
| Strict subject end | `\z` | yes | yes | yes | Strict-end boundary |
| End before final newline | `\Z` | yes | yes | yes | Final-end boundary |
| Line anchors | `^`, `$` | yes | yes | yes | Subject/newline policy |
| Multiline anchors | `/^a$/m` | yes | yes | yes | Current `m` modifier |
| Word boundaries | `\b`, `\B` | yes | yes | yes | Boundary state |
| Unicode word boundaries | `\b` with UCP/Unicode | yes | yes | yes | Pinned Unicode predicate |
| Positive lookahead | `a(?=b)` | yes | yes | yes | Capture-free finite child machine |
| Negative lookahead | `a(?!c)` | yes | yes | yes | Complete finite child decision |
| Fixed lookbehind | `(?<=a)b` | yes | yes | yes | Bounded scalar history |
| Multi-scalar lookbehind | `(?<=ab)c` | yes | yes | yes | Exact-width history |
| Variable lookbehind | `(?<=a*)b` | limited | limited | no | Finite width expansion only |
| Unequal bounded lookbehind | `(?<=a|bc)x` | yes | yes | no | Exact-width branch expansion |
| Unbounded lookbehind | `(?<=.*foo)x` | no/limited | no/limited | no | No unbounded history |
| Nested assertions | `(?=(?=a)a)` | yes | yes | no | Product machine and indexed witnesses |
| Nested negative assertions | `(?! (?!a)b )` | yes | yes | no | Complete nested refutation certificates |
| Atomic inside assertion | `(?=(?>a|ab))` | yes | yes | no | Planned assertion/control composition |
| Assertion inside atomic | `(?>a(?=b))` | yes | yes | no | Planned assertion/control composition |
| Captures inside assertion | `(?=(?<x>a))` | yes | yes | no | Candidate separate capture-frame semantics |
| Non-atomic lookaround | `(?*...)` | yes | yes | no | Candidate path-reentry model |
| Scan-substring assertion | `(*scan_substring:(x))` | yes | yes | no | Candidate captured-subject machine |
| Search anchor | `\G` | yes | yes | no | Explicit scan/search cursor |
| Match-start reset | `foo\Kbar` | yes | yes | no | Additive reported-span semantics |

### 15.4 Options and control verbs

| Capability | Example | `:re` | Elixir | Cure now | Cure route |
|---|---|---:|---:|---:|---|
| Caseless | `/foo/i` | yes | yes | yes | Current `i` |
| Multiline | `/^foo$/m` | yes | yes | yes | Current `m` |
| Dotall | `/foo.bar/s` | yes | yes | yes | Current `s` |
| Extended/comments | `/foo # c/x` | yes | yes | yes | Compile-time source stripping |
| Unicode | `/\\w/u` | yes | yes | yes | Pinned scalar semantics |
| First-line | `/foo/f` | yes | yes | yes | Current first-line search bound |
| Ungreedy | `/foo/U` | yes | yes | yes | Current lazy-default behavior |
| Export flag | `/foo/E` | yes | yes | accepted marker | Not OTP cross-node export |
| Scoped inline options | `(?im-sx:foo)` | yes | yes | no | Planned lexical option environment |
| Newline control | `(*CRLF)`, `(*ANY)` | yes | yes | yes | Current finite newline policy |
| `\R` policy | `(*BSR_ANYCRLF)` | yes | yes | yes | Current finite newline policy |
| Anchored execution | `anchored` | yes | yes | equivalent APIs | `parse_full`/`parse_prefix_at` |
| Execution offset | `{offset, N}` | yes | yes | internal only | Planned public scalar-offset API |
| `notbol`/`noteol` | execution options | yes | via `:re` | internal only | Candidate explicit context API |
| `notempty` | execution option | yes | via `:re` | no | Candidate explicit scan policy |
| Match limit | `{match_limit, N}` | yes | via `:re` | no | Compile-time admissibility, not false |
| Recursion limit | `{match_limit_recursion, N}` | yes | via `:re` | no | No fuel-based semantic fallback |
| `(*MARK:name)` | `a(*MARK:A)b` | engine yes | engine yes | no | Planned typed mark result |
| `(*FAIL)` | `a(*FAIL)` | yes | yes | no | Planned finite failure transition |
| `(*ACCEPT)` | `a(*ACCEPT)` | yes | yes | no | Planned finite success transition |
| `(*THEN)` | `A(*THEN)B|C` | yes | yes | no | Candidate alternative-control algebra |
| `(*PRUNE)` | `A(*PRUNE)B` | yes | yes | no | Candidate finite search control |
| `(*SKIP)` | `A(*SKIP)B` | yes | yes | no | Candidate search-cursor control |
| `(*COMMIT)` | `A(*COMMIT)B` | yes | yes | no | Candidate strong commitment model |
| Callouts | `(?C)` | yes via PCRE API | syntax via engine | no | No arbitrary host effects |
| Embedded host code | Perl code blocks | no in PCRE2 | no | no | Permanently excluded |

### 15.5 API and result semantics

| Capability | `:re` | Elixir | Cure today | Cure route |
|---|---:|---:|---:|---|
| Runtime source compilation | `re:compile/2` | `Regex.compile/2` | no | Compile-time literal model |
| Compile-time literal | no ordinary equivalent | `~r/.../` | yes `/.../flags` | Canonical staged machine |
| Opaque compiled pattern | `mp()` | `%Regex{re_pattern: ...}` | no | No opaque runtime regex |
| Pattern export/import | OTP 28 | `E` / `Regex.import/1` | no | Canonical compiler interfaces instead |
| First unanchored match | `re:run/3` | `Regex.run/3` | `search/2` | Preserve |
| Boolean test | pattern result | `Regex.match?/2` | `matches/2` | Preserve |
| Full-string parse | `anchored` | anchors/options | `parse_full/2` | Preserve |
| Typed prefix parse | no direct equivalent | no direct equivalent | `parse_prefix/2` | Preserve |
| Global non-overlapping scan | `global` | `Regex.scan/3` | `scan/2` | Preserve |
| Empty-match progress | defined by `global` | inherited | one-scalar progress | Preserve and prove |
| Overlapping scan | not ordinary `global` | not ordinary `scan` | no | Possible separate API |
| Split | `re:split/3` | `Regex.split/3` | typed `split/3` | Preserve |
| Split limits | options | `parts:` | typed `SplitLimit` | Preserve |
| Trim empty pieces | options | `trim:` | typed option | Preserve |
| Include separators | capture/options | `include_captures:` | typed option | Preserve |
| Literal replacement | `re:replace/4` | `Regex.replace/4` | `replace_literal/3` | Preserve |
| Callback replacement | Erlang fun | Elixir function | typed `(Match) -> String` | Preserve |
| Replacement templates | `\\1`, `\\g{1}` | supported | no | Candidate typed replacement template |
| Named capture lookup | names/options | `named_captures/3` map | `NamedCapture` list/lookup | Map convenience later |
| Capture subset selection | `capture` option | `capture:` | no | Candidate typed projection |
| Binary results | yes | yes | no under scalar `String` | Separate byte API only |
| Charlist results | yes | not normal | no | Cure `String` is canonical |
| Byte indexes | default index mode | `return: :index` | no | Scalar offsets remain canonical |
| Scalar indexes | no default | no default | yes | Core semantic distinction |
| Typed semantic result | no | no | yes `Regex(result)` | Core differentiator |
| Structured compile diagnostics | `compile/2` tuples | `Regex.compile/2` tuples | source spans/codes | Preserve and expand |
| Match-limit errors | optionally reported | underlying engine behavior | no unknown result | Reject unprovable forms before execution |
| AtomVM execution | depends on OTP `:re` | depends on OTP `:re` | yes for Cure subset | Primary portability gate |

## 16. Translation policy for unsupported forms

The ledger's **finite** entries are not permissive fallbacks. They require a
normalization result of the form:

```text
{:ok, canonical_pattern, equivalence_certificate}
{:error, structured_diagnostic}
```

The certificate must preserve the observables relevant to the selected Cure
API: acceptance, ordered/leftmost matching, captures, participation, scalar
spans, scan progress, marks, and control effects. If those observables cannot
be preserved, the compiler may accept the rewrite only for an API mode where
the differing metadata is provably unobservable; otherwise it must reject the
literal.

The first translation targets are:

1. nested capture-free assertions → product/Boolean assertion machines;
2. negative assertions → complete finite refutation certificates;
3. bounded variable lookbehind → exact-width branch expansion;
4. assertion conditionals → certified positive/negative branches;
5. acyclic subroutine calls → compile-time inlining;
6. statically bounded recursion → finite unrolling;
7. bounded backreferences → finite enumeration, trie, or register machine;
8. class intersection/difference → scalar-predicate conjunction/complement;
9. dead assertion captures → erasure only after an observability proof;
10. `(*FAIL)`/`(*ACCEPT)` → explicit finite control transitions.

Failure to prove finiteness, layout compatibility, termination, or ordered
search equivalence is a compile-time error. It must never become a runtime
`NoMatch`, a fuel exhaustion result, a host-engine call, or a silently weakened
pattern.

## 17. Proof-carrying normalization architecture

### 17.1 Normalize syntax trees, not source text

Unsupported-but-potentially-reducible forms must be translated from a lossless
compile-time syntax tree or semantic IR. The compiler must not rewrite regex
source text and then reparse the result. Textual rewriting can change escapes,
source positions, capture numbering, branch ordering, option scope, and the
meaning of context-sensitive numeric syntax.

Every syntax node retains its original source span and an origin identifier.
Normalized nodes retain a link to the source nodes from which they were
derived. Diagnostics and debug traces therefore name the authored construct,
even when the emitted machine was built from a substantially different shape.

The canonical pipeline is:

```text
regex literal
  -> lossless PCRE-shaped AST with source spans
  -> width/capture/finiteness/control analysis
  -> normalization into canonical Cure IR
  -> generated equivalence certificate
  -> kernel/proof checking
  -> finite machine compilation
  -> runtime artifact
```

The normalizer returns a checked decision, not a nullable target:

```text
Normalized(target_ir, equivalence_certificate)
Rejected(structured_diagnostic)
```

`target_ir` may be an ordinary `Pattern`, a product/intersection assertion
machine, a bounded lookbehind machine, a finite capture/register machine, or a
directly staged `PatternMachine`. The normalizer may run in the host compiler
or in Cure's compile-time machinery for performance and convenience, but its
output is untrusted until the certificate is checked by the trusted proof
boundary.

### 17.2 Observable equivalence, not language equivalence alone

The certificate must state which observations it preserves. Accepted patterns
in the ordinary Cure API require the strongest applicable profile:

```text
ObservableProfile
  = LanguageOnly
  | FullMatch
  | Search
  | Control
```

The profiles include, as appropriate:

- accepted versus rejected subjects;
- leftmost and ordered-choice behavior;
- greedy/lazy/possessive selection;
- capture values and participation;
- scalar match spans and `\\K`-adjusted reported spans;
- search and empty-match scan progress;
- marks, atomic commitment, and control-verb effects;
- assertion boundary and history behavior.

Language equivalence is not sufficient when the source pattern exposes
captures, ordered matching, spans, or control state. A rewrite may use a
weaker profile only when the public API mode proves that the omitted metadata
is unobservable. The default typed Cure APIs do not silently downgrade to a
language-only proof.

### 17.3 Certificate shape and trust boundary

The certificate is a checked Cure value indexed by the source and target
representations. Its concrete constructors may evolve, but it must cover the
normalization rules actually used, for example:

```text
TranslationCertificate
  = SequenceCongruence(...)
  | AlternateCongruence(...)
  | GroupCongruence(...)
  | BoundedLookbehindExpansion(...)
  | AssertionProduct(...)
  | AssertionConditionalExpansion(...)
  | AcyclicSubroutineInlining(...)
  | BoundedRecursionUnrolling(...)
  | FiniteBackreferenceEnumeration(...)
  | DeadCaptureErasure(...)
  | ClassPredicateAlgebra(...)
```

The proof relation is conceptually:

```text
Equivalent(source_ast, target_ir, observable_profile)
```

The host/compiler normalizer may propose a target and construct a certificate,
but it may not assert equivalence through a cast, opaque token, postulate, or
unchecked Boolean. The Cure kernel checks the certificate; the regex proof
layer then proves that the target IR corresponds to its staged machine and
typed extraction routines. The emitter runs only after both obligations hold.

The runtime artifact contains the target machine and its necessary public
metadata only. Source ASTs, spans, normalization certificates, proof paths,
and dependent indices are erased unless a feature explicitly makes a value
observable, such as a user-requested mark.

### 17.4 Examples of certified translations

#### Bounded lookbehind

```text
(?<=a|bc)x
```

may normalize to an alternation of exact-width lookbehind branches when the
operands are capture-free and their boundary behavior is compatible. The
certificate must establish:

1. every branch has a finite statically known width;
2. each branch is zero-width at the same parent cursor;
3. branch ordering is preserved for the selected profile;
4. captures, spans, and failure behavior are unchanged.

#### Finite backreference domain

```text
(?<x>[ab]{2})\\k<x>
```

has a finite capture domain. The compiler may enumerate that domain or build a
finite trie/register machine. If the capture is observable, generated paths
must preserve the `x` slot and its exact value. Proving only that the same
subjects are accepted is insufficient for a named-capture API.

#### Nested assertions

```text
(?=(?=a)a)
```

may lower to a product/Boolean assertion machine or to a depth-indexed
assertion program. The certificate proves non-consumption, nested boundary
semantics, and complete positive/negative decisions. It need not produce a
textual flattened regex.

#### Acyclic subroutines

```text
(?(DEFINE)(?<digit>\\d))(?&digit)+
```

may be inlined when the subroutine call graph is acyclic and capture/control
metadata can be mapped without ambiguity. Recursive cycles require a separate
complete recursive model or are rejected; they are never silently truncated.

### 17.5 Rejection and diagnostics

“Unprovable” means “not proven under the selected Cure model,” not “the
compiler did not try hard enough.” The normalizer must reject when it cannot
prove finiteness, layout compatibility, termination, or ordered-observable
equivalence. Rejection is compile-time and structured; it must not become:

- a runtime `NoMatch`;
- fuel exhaustion presented as a match failure;
- a host `:re` call;
- an unchecked cast or proof postulate;
- a silently weakened pattern.

The diagnostic names the original syntax node and span, the attempted target
model, the failed side condition, the relevant resource estimate, and an
actionable rewrite when one exists. Debug traces may additionally print the
normalized IR and certificate constructor chain, but those traces never become
part of production semantics.

### 17.6 Required verification for every rewrite

Every normalization rule requires:

1. a smallest red regression using the original surface syntax;
2. a source-to-target semantic theorem at the strongest applicable profile;
3. a target-IR-to-machine correspondence theorem;
4. capture/layout and scalar-span tests where relevant;
5. differential tests against `:re` for the supported overlap;
6. exhaustive small-model and property tests over the rule's side conditions;
7. erasure and closure checks proving no source/proof artifact leaks into the
   runtime;
8. a boundary test showing that the rule rejects when its proof assumptions
   fail.

The normalization phase is therefore a proof-producing compiler pass, not a
collection of parser conveniences. Its purpose is to enlarge the supported
surface while preserving Cure's single canonical machine, diagnostic, and
proof authorities.

## 18. PCRE2/OTP parity-completeness audit

The compatibility ledger must be maintained as an inventory, not as a list of
the most familiar regex operators. Before claiming maximum practical parity,
the implementation must audit every relevant PCRE2/OTP `re` family against the
following checklist.

### 18.1 Syntax-family inventory

The parser/classifier must have an explicit row for each family below, even if
the final decision is `no`:

- literal characters, escaped controls, hexadecimal scalars, octal forms,
  `\\N{name}`, bare `\\N`, `\\Q...\\E`, and context-sensitive numeric escapes;
- dot, all generic character classes, POSIX classes, ranges, negation, class
  algebra, Unicode general categories, binary properties, scripts,
  script-extensions, Bidi classes, and grapheme clusters;
- sequence, alternation, empty alternatives, ordinary/non-capturing/named
  groups, branch reset, duplicate names, no-auto-capture, and capture layout;
- greedy, lazy, bounded, possessive, atomic, and automatically possessified
  repetition;
- `^`, `$`, `\\A`, `\\Z`, `\\z`, `\\G`, `\\b`, `\\B`, `\\K`, lookahead,
  lookbehind, nested assertions, non-atomic assertions, and scan-substring
  assertions;
- capture, assertion, recursion, subroutine, `DEFINE`, version, and
  participation conditionals;
- numeric, named, relative, forward, and subroutine references;
- script-run and atomic-script-run groups;
- `(*MARK)`, `(*FAIL)`, `(*ACCEPT)`, `(*THEN)`, `(*PRUNE)`, `(*SKIP)`,
  `(*COMMIT)`, and all named-verb forms;
- callouts, embedded-code forms, and other host-effect constructs;
- replacement references and replacement callback behavior.

No syntax family may disappear merely because it is uncommon or absent from
Elixir's convenience documentation. The row must record whether the form is:

1. directly lowered to a Cure finite machine;
2. normalized with a checked equivalence certificate;
3. handled by a complete finite-subject evaluator;
4. exposed only in a non-portable host profile; or
5. rejected with a structured diagnostic.

### 18.2 Start-of-pattern and option inventory

PCRE2 has controls that are not ordinary regex atoms. The audit must explicitly
cover:

- `(*UTF)` and `(*UCP)`;
- `(*CR)`, `(*LF)`, `(*CRLF)`, `(*ANYCRLF)`, `(*ANY)`, and `(*NUL)`;
- `(*BSR_ANYCRLF)` and `(*BSR_UNICODE)`;
- `(*NO_START_OPT)` and `(*NO_AUTO_POSSESS)`;
- `(*LIMIT_MATCH=...)`, `(*LIMIT_DEPTH=...)`, and other limit pragmas;
- inline `i`, `m`, `n`, `s`, `x`, `xx`, `J`, `U`, and option unsetting;
- Unicode/ASCII restriction options and casing restrictions;
- Erlang compile options such as `anchored`, `caseless`, `dollar_endonly`,
  `dotall`, `extended`, `firstline`, `multiline`, `no_auto_capture`,
  `dupnames`, `ungreedy`, `newline`, `bsr_anycrlf`, `bsr_unicode`, `ucp`, and
  `never_utf`;
- execution options such as `global`, `offset`, `notbol`, `noteol`,
  `notempty`, `notempty_atstart`, `report_errors`, `match_limit`, and
  `match_limit_recursion`.

Cure should normalize controls that merely select its pinned Unicode or
newline semantics. Controls that alter host optimizer behavior must not be
pretended to be semantic regex features: either they become a checked compile
policy or they receive a clear “optimizer control is not portable” diagnostic.
Runtime limits must never turn incomplete execution into `NoMatch`.

### 18.3 API-family inventory

Parity work includes behavior and API observations, not only pattern syntax.
The audit must track equivalents for:

- source compilation and compile diagnostics;
- compile-time literals and source/provenance inspection;
- first match, anchored match, global scan, offset search, empty-match
  progress, and capture selection;
- binary, list, and index result modes;
- scalar offsets and Cure's typed semantic result;
- named-capture lookup, duplicate-name behavior, and unmatched/empty capture
  representation;
- split options (`parts`, trimming, inclusion, capture selection);
- replacement literals, capture references, callbacks, and global/first-only
  behavior;
- compiled-pattern introspection, source retrieval, options retrieval,
  version reporting, and export/import;
- `:re` error results, `Regex.compile/2` errors, and Cure structured
  diagnostics;
- host-only compiled-pattern behavior versus portable staged artifacts.

Where Cure deliberately differs, the difference must be an explicit API design:

- Cure uses Unicode-scalar offsets rather than Erlang/Elixir byte offsets;
- Cure returns typed values and additive metadata rather than a PCRE tuple;
- Cure's default regex is a compile-time literal, not a runtime source parser;
- byte-oriented matching and `\\C` require a separate byte profile;
- opaque `re_pattern`/`mp()` values are not part of the portable API.

### 18.4 Version-drift gate

OTP's `:re` implementation and PCRE2 syntax evolve. The compatibility ledger
must therefore record:

1. OTP version and underlying PCRE2 version;
2. Unicode data version used by the oracle and Cure tables;
3. syntax/features added, removed, or behaviorally changed since the previous
   baseline;
4. normalized result differences and intentional incompatibilities;
5. a regenerated differential corpus for every version update.

An OTP upgrade may change the oracle without changing Cure production code, but
it cannot silently change the claimed parity surface. The full stabilization
gate must be rerun before the new version becomes authoritative.

### 18.5 Final parity claim

The project may claim “maximum practical PCRE parity” only when every inventory
row has a disposition, every supported disposition has a parser/lowering/
proof/runtime test, and every rejected disposition has a structured diagnostic
and documented reason. The claim must state the exact OTP/PCRE2/Unicode profile
and must distinguish:

- pure portable Cure support;
- exact finite normalization;
- complete finite-subject extended evaluation;
- non-portable host-only compatibility; and
- deliberate non-parity.
