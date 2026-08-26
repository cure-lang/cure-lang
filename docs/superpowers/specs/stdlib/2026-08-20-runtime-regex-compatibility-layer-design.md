# Runtime Regex Compatibility Layer for BEAM and AtomVM

**Status:** deferred design; implementation is explicitly blocked until the
erased Cure-native regex engine is complete.

**Date:** 2026-08-20

**Parent specifications:**

- `2026-07-22-dependent-regex-completion-design.md`
- `2026-08-18-finite-pcre-extension-design.md`
- `2026-08-19-pure-portable-regex-engine-design.md`

**Package boundary:** the runtime-compatible erased engine and its neutral ABI
are owned by the separately identified `cure_regex` Cure package under
`lib/std_deps/regex`. That package
is embedded and bundled by the stdlib release, but has its own dependency graph,
artifact identity, and explicit exported-module list. The stdlib bootstrap
builds foundational modules, then `cure_regex`, then any public `Std.Regex`
façade. Private package modules are bundled for internal calls but are not
available for arbitrary consumer lookup.

## 0. Decision and deferral

Cure will eventually provide two deliberately different entry paths into one
finite regex implementation:

```text
compile-time Cure source       runtime pattern string
        |                              |
        v                              v
typed, erased Cure engine      compatibility parser/compiler
        |                              |
        +---------- shared finite machine ----------+
                               |
                               v
                    BEAM and AtomVM execution
```

The compile-time path remains Cure's primary semantic API. It provides typed
captures, typed composition, compile-time diagnostics, and proof-carrying
lowering. The compatibility path accepts pattern source after the containing
program has already been compiled and returns ordinary BEAM data such as
matched text and capture lists.

This document does **not** authorize implementation yet. Work on this design
may begin only after the parent erased Cure-native engine has satisfied its
full stabilization gate:

- the erased engine is complete for the feature set claimed by the parent
  specification;
- its ordinary, assertion, capture, Unicode, scan, replacement, and AtomVM
  gates are green;
- no unresolved E101/E093 errors or kernel work remain on that pathway;
- the generated closure contains no host regex dependency;
- the typed and erased Cure APIs have stable semantics and result conventions;
- the full test suite, TCB, totality, erasure, Antigen, Unix/escript, and
  AtomVM smoke gates pass.

Until those conditions hold, this file is a design record only. In particular,
no runtime parser, compatibility module, ABI wrapper, or parser-related
refactor should be mixed into the erased-engine implementation commits.

## 1. Motivation

AtomVM applications are compiled before deployment, but their users and
protocols may provide regex patterns at runtime. A purely compile-time regex
macro cannot handle that use case. AtomVM also does not provide OTP's `:re`
service, so a wrapper around PCRE2 or a `:re` compiled handle is not a portable
solution.

The compatibility layer must therefore ship a parser and finite compiler as
ordinary precompiled BEAM/AtomVM code. The deployed program does not compile
Cure source or generate BEAM code at runtime. It merely turns a runtime string
into a pure, immutable finite-machine value and executes that value.

The layer is intended for:

- Erlang applications running on AtomVM;
- Elixir applications compiled for AtomVM;
- other BEAM languages that can call an Erlang-compatible module;
- Cure applications that intentionally need dynamic, untyped patterns.

It is not intended to weaken the guarantees of a Cure regex literal or to
pretend that every PCRE2 construct has a finite, total implementation.

## 2. Product boundaries

### 2.1 Compile-time typed path

The existing `Std.Regex` path remains the typed path. Its source pattern is
parsed by the Cure macro machinery, lowered into `Pattern(shape)` and staged
machine values, and checked by the existing proof layer. The generated module
does not contain the regex parser unless the module explicitly imports the
compatibility tier.

The typed path may expose constructors such as:

- `Regex(result)`;
- `Pattern(shape)`;
- `NamedRegex(result, shape)`;
- `parse_full`, `search`, `scan`, `replace`, and typed combinators.

No compatibility API may change the result type or proof obligations of this
path.

### 2.2 Runtime compatibility path

The compatibility path is explicit and opt-in. A pattern must be supplied to a
compatibility function such as `compile/2`; it must never be inferred by the
typed macro path.

The compatibility path exposes a generic result contract:

- matched text as `String`/binary-compatible data;
- unmatched captures as an explicit `None`/`undefined` representation;
- named captures as an ordered list of name/value pairs;
- scalar and, when separately requested, byte offsets;
- structured compile and execution errors.

It does not expose `Sem(shape)` as a runtime type. The shape is existentially
packaged internally and erased at the language boundary.

### 2.3 One semantic implementation

There must be one canonical syntax grammar, one normalization policy, one
finite-machine semantics, and one ordered execution model. The compatibility
tier must not grow a second backtracking interpreter whose behavior is merely
tested against the Cure engine.

If a currently indexed helper cannot be called from an existential package,
add an erased adapter or factor the helper into a shared first-order machine
kernel. Do not copy its transition algorithm into a compatibility-only module.

### 2.4 No default replacement for `:re`

The primary module name must not be `:re` on ordinary BEAM systems. OTP users
may already have `:re`, and Cure cannot claim complete PCRE compatibility.

The neutral module is provisionally named `cure_regex`. An AtomVM distribution
may additionally ship an opt-in `re`-shaped adapter when its supported subset
and result differences are documented. The adapter must delegate to
`cure_regex`; it must not become a second engine.

## 3. Required source refactor after deferral lifts

The current syntax model is described as compile-time-only. Once this design is
activated, split the responsibilities without changing the AST constructors:

```text
cure_regex.Syntax.Model       shared syntax/data/error definitions
cure_regex.Syntax.Parser      runtime-safe parser over pattern data
cure_regex.Syntax.Flags       shared option parsing and normalization
cure_regex.Syntax.Class       shared class/property parsing
cure_regex.Core                erased finite-machine semantic core
cure_regex.Proof               erased/proof-backed correspondence adapters
cure_regex.Compat.Compiler     runtime AST-to-machine compiler
cure_regex.Compat.Runtime      generic runtime API and projections
cure_regex.Compat              public Cure compatibility façade

Std.Regex.Syntax               public compile-time macro façade
Std.Regex.Syntax.Emitter       public typed/staged emitter
Std.Regex                       public typed API façade
```

The package parser/model modules must not import `Std.Syntax`, macro expansion state,
source quotation, or compile-time environment state. The macro façade may
continue to import them and may attach source diagnostics to the shared parser
errors.

The stdlib build must invoke the ordinary package pipeline for this embedded
package rather than silently treating every package source as a stdlib module.
Package export metadata is the only authority for consumer visibility; ordinary
module public declarations do not by themselves publish a private package
module.

The existing `LiteralPattern` tree may be retained as the shared AST while the
parent engine is stable. If its name or comments imply that it can never exist
at runtime, rename it to a neutral name such as `RegexSyntaxPattern` and keep a
compatibility alias only if the Cure compiler can preserve interface hashes.

## 4. Compatibility compilation pipeline

`compile(pattern, options)` must perform the following total sequence.

### 4.1 Input normalization

1. Validate the incoming BEAM term as a supported string/binary or Cure
   `String`.
2. Decode UTF-8 into Cure scalar input for Unicode mode.
3. Reject malformed UTF-8 with an explicit diagnostic; do not reinterpret it as
   a different valid pattern.
4. Parse flags/options using the shared option parser.
5. Reject unknown, contradictory, or unsupported options before matching.

The parser must retain a scalar offset and, where useful, a byte offset for
each source error. It must never report a parser/resource failure as a valid
empty pattern.

### 4.2 Shared syntax parsing

The parser consumes the same supported syntax as the compile-time path,
including the same treatment of:

- literals and escaped literals;
- character classes, ranges, POSIX classes, and Unicode properties;
- alternation, concatenation, grouping, and branch reset;
- greedy, lazy, possessive, and bounded repetition where admitted;
- anchors and word boundaries;
- newline policies;
- named and numbered captures;
- conditionals and assertions admitted by the parent engine.

The runtime parser may accept a smaller set than the current compile-time
parser during the first release, but the difference must be explicit in the
capability ledger and represented by a structured `UnsupportedFeature`
diagnostic.

### 4.3 Capture allocation and reference resolution

Capture slots are allocated once, in source order, using the same rules as the
literal path. The compiler must preserve:

- slot numbers;
- names and duplicate-name policy;
- branch-reset numbering;
- conditional reference resolution;
- participation versus empty-string distinction;
- source spans for diagnostics.

Capture metadata must remain separate from `ShapeCode`; it must not alter the
typed result of compile-time Cure regexes.

### 4.4 Normalization

Normalization must run before machine construction. It may:

- desugar syntax into canonical AST constructors;
- resolve scoped options;
- normalize newline policies;
- normalize Unicode/property aliases;
- expand finite bounded forms;
- translate an admitted finite form into an equivalent finite form.

Every translation must obey the proof-carrying normalization rules in the
parent finite-PCRE specification. A runtime-only rewrite with no corresponding
compile-time proof or differential property is not permitted.

### 4.5 Runtime lowering

The normalized AST must lower to the same finite runtime plan used by the
erased Cure engine. Conceptually, the plan is an existential package:

```text
RuntimePlan = Sigma(shape: ShapeCode, Plan(shape))

Plan(shape) =
    Thompson(ThompsonCompilation(shape))
  | Atomic(AtomicRuntimePattern(shape))
  | Lookaround(Pattern(shape), ThompsonCompilation(shape), NewlinePolicy)
```

The concrete representation may use the existing `StagedMachine`,
`NamedThompsonCompilation`, or a factored successor, provided that it preserves
the same transition order and boundary semantics.

Named capture IDs may be carried by a parallel named compilation or capture
ledger. Erasing those IDs must recover the ordinary language machine exactly.

### 4.6 Resource admission

Before returning a compiled value, calculate and check at least:

- maximum AST nodes;
- maximum nesting depth;
- maximum capture slots;
- maximum machine states;
- maximum assertion depth;
- maximum bounded expansion size;
- maximum Unicode/property table expansion;
- maximum serialized compiled-pattern size, if serialization is supported.

If any limit is exceeded, return `PatternTooLarge` or `PatternResourceLimit`.
The compiler must not return a partial machine.

## 5. Runtime representation

### 5.1 Public Cure type

The public Cure type is intentionally generic:

```text
type RuntimeRegex = RuntimeRegex(
  version: Nat,
  options: RuntimeOptions,
  program: RuntimePlan,
  captures: RuntimeCaptureLayout
)
```

The exact constructor may remain private. Callers obtain values only from
`compile`; functions receiving a forged or wrong-version term must return an
explicit `InvalidCompiledRegex` error rather than crash.

### 5.2 Capture layout

```text
type RuntimeCaptureLayout = RuntimeCaptureLayout(List(RuntimeCaptureSlot))

type RuntimeCaptureSlot = RuntimeCaptureSlot(
  index: Nat,
  name: Option(String)
)
```

The runtime result must preserve capture participation:

```text
type RuntimeCapture = RuntimeCapture(
  index: Nat,
  name: Option(String),
  value: Option(String)
)
```

`None` means the group did not participate. `Some("")` means it participated
and captured an empty string.

### 5.3 Match result

```text
type RuntimeMatch = RuntimeMatch(
  matched: String,
  captures: List(RuntimeCapture),
  scalar_start: Int,
  scalar_length: Int,
  byte_start: Option(Int),
  byte_length: Option(Int)
)
```

The neutral API returns an ordered list. Elixir adapters may additionally
construct maps or keyword lists; those are adapter conveniences and are not
part of the AtomVM core ABI.

### 5.4 Diagnostics

```text
type RuntimeRegexDiagnostic =
    InvalidPattern(Atom, Int, Int, String)
  | InvalidOption(Atom, String)
  | UnsupportedFeature(Atom, Int, Int, String)
  | PatternResourceLimit(Atom, Nat, Nat)
  | InvalidUtf8(Int, String)
  | InvalidCompiledRegex(Atom)
  | RuntimeResourceLimit(Atom, Nat, Nat)
```

Diagnostics must contain a stable code, source offset/span where applicable,
and a human-readable explanation. They must not be reduced to `error: blah` or
an `ArgumentError`.

## 6. Runtime execution API

The initial neutral API is:

```text
compile(pattern: String, options: RuntimeCompileOptions)
  -> Result(RuntimeRegex, RuntimeRegexDiagnostic)

run(regex: RuntimeRegex, subject: String, options: RuntimeRunOptions)
  -> Result(Option(RuntimeMatch), RuntimeRegexDiagnostic)

run_prefix(regex: RuntimeRegex, subject: String, options: RuntimeRunOptions)
  -> Result(Option(RuntimeMatch), RuntimeRegexDiagnostic)

scan(regex: RuntimeRegex, subject: String, options: RuntimeRunOptions)
  -> Result(List(RuntimeMatch), RuntimeRegexDiagnostic)

split(regex: RuntimeRegex, subject: String, options: RuntimeSplitOptions)
  -> Result(List(String), RuntimeRegexDiagnostic)

replace(regex: RuntimeRegex, subject: String, replacement: String,
        options: RuntimeReplaceOptions)
  -> Result(String, RuntimeRegexDiagnostic)

supports(feature: Atom) -> Bool
capabilities() -> List(Atom)
```

The BEAM facade translates these into ordinary terms such as:

```erlang
{ok, Regex} = cure_regex:compile(Pattern, Options),
{ok, none} = cure_regex:run(Regex, Subject, Options),
{ok, {some, Match}} = cure_regex:run(Regex, Subject, Options),
{error, Diagnostic} = cure_regex:compile(Pattern, Options).
```

An OTP-shaped adapter may instead expose `nomatch` and `{match, Captures}`,
but it must document every deviation from `:re` and delegate to the neutral
facade.

### 6.1 Search and prefix semantics

`run` performs the same leftmost/ordered search as `Std.Regex.search`. Prefix
matching and greedy/lazy selection must be delegated to the same machine
search routines, not reconstructed by repeatedly compiling a suffix pattern.

The runtime API must expose an explicit search context for features such as
`\\G`, previous-word state, line-start state, and scan continuation. A context
must be an ordinary immutable value supplied by the caller or by `scan`.

### 6.2 Empty-match progress

`scan` must implement the parent engine's empty-match progress law: after an
empty match, advance by one Unicode scalar when input remains. This rule must
be identical on BEAM and AtomVM and must not depend on byte length.

### 6.3 Replacement

The neutral replacement API initially accepts a literal replacement string. A
callback API may be added only after the BEAM ABI and AtomVM closure behavior
are tested. Replacement expansion must have explicit capture-reference
semantics; it must not silently interpret arbitrary host-language code.

### 6.4 Scheduler fairness: rely on AtomVM reductions

The AtomVM source audit was performed against commit `89918dc1`. AtomVM gives a
scheduled process `DEFAULT_REDUCTIONS_AMOUNT` reductions, currently 1024, and
reschedules when the budget reaches zero. The interpreter charges reductions at
ordinary local, tail, external, closure, and apply calls and at jumps, including
loop backedges. The JIT emits corresponding reduction checks for those same
operations.

Consequently, the initial compatibility engine does **not** need an
application-level `Continue` result merely to achieve scheduler fairness. The
runtime parser, compiler, matcher, scanner, splitter, and replacer must remain
ordinary recursive Cure code lowered to normal BEAM calls and jumps. AtomVM can
then preempt them without changing the regex API or its semantics.

This conclusion has an important boundary: charging one reduction before a
native operation does not interrupt a long native operation. The reachable
closure must therefore be audited for primitives that can perform input-sized
work in one call, including bulk string-to-character conversion, Unicode
operations, binary copying, and host collection conversion. Such a primitive
must be shown to have an acceptable bound, trap/yield on AtomVM, or be replaced
by chunked Cure code. A monolithic native regex parser, compiler, or matching
loop is forbidden.

The scheduler contract is therefore:

- ordinary regex execution never exposes a public or private `Continue`
  protocol;
- no hard wall-clock latency promise inferred from the number 1024, because a
  reduction is not a constant-time instruction;
- a large compile and match must allow an independent heartbeat process to make
  progress;
- the fairness regression must run against the AtomVM interpreter and JIT when
  both are supported by the release;
- the release manifest must pin the AtomVM revision used for the scheduler and
  native-primitive audit.

This is a permanent API boundary, not merely a first-release shortcut. The
ordinary `compile`, `run`, `run_prefix`, `scan`, `split`, and `replace` result
types remain final-result APIs: success, no match where applicable, or a
structured error. Scheduler preemption is an implementation concern and must
not become an observable regex result.

Explicit cancellation uses normal process supervision or termination. It does
not require a resumable regex result. If application-controlled pacing is ever
needed, it belongs in a distinct controlled-runner API layered over the same
machine semantics. Streaming likewise gets a distinct API because it represents
temporarily incomplete input, not an incomplete scheduling turn. Neither may
change the ordinary API or reinterpret temporary exhaustion as `NoMatch`.

An internal execution-state representation may be introduced to share code
with a future controlled runner or streaming executor. That representation is
not part of the public ABI. Any stepped implementation must be a refinement of
uninterrupted execution and satisfy partition invariance: dividing execution at
arbitrary positive work boundaries produces the same final observable result.
This permits a future implementation optimization without requiring callers to
migrate or changing regex semantics.

### 6.5 Streaming is a separate feature

Resumable execution over an already available subject is not streaming input.
The first compatibility release does not accept partial subjects and does not
claim streaming semantics. A later streaming API must separately define:

- `feed(chunk)` and end-of-input/finalization behavior;
- how `$`, `\\z`, lookahead, and negative assertions wait for more input;
- the maximum retained lookbehind and capture history;
- behavior for a UTF-8 scalar split across chunks;
- whether a provisional match may later be invalidated;
- how `\\G`, scan progress, and empty matches cross chunk boundaries.

Until those rules and their proofs exist, every matching call receives one
complete subject.

### 6.6 Initial ABI option registry

Before the BEAM facade is implemented, freeze a normative table containing the
exact public atom/tuple spelling, default, phase, conflicts, and error behavior
for every option. At minimum it must cover:

- Unicode/scalar and future byte profiles;
- caseless, multiline, dotall, extended, firstline, and ungreedy modes;
- newline and `\\R` policy;
- anchored, global, offset, not-empty, beginning-of-line, and end-of-line run
  behavior where supported;
- capture selection by index/name and unmatched-capture representation;
- text, index, scalar-offset, and byte-offset return modes;
- split limits/trimming;
- replacement capture expansion and escaping;
- duplicate option handling and contradictory options.

Unknown options and unsupported `:re` options return structured errors. An
adapter must not silently ignore them.

## 7. Character, Unicode, and byte policy

### 7.1 Unicode-scalar mode

Unicode-scalar mode is the default and matches Cure's native `String` model.
The matcher operates on `Char` values. Returned scalar offsets count Unicode
scalars, not UTF-8 code units.

### 7.2 Byte-compatible mode

Byte offsets may be requested by a compatibility adapter only when the input is
valid UTF-8 and the scalar-to-byte map is retained for the match. Byte mode
must not change character classification or turn a scalar pattern into a
raw-byte engine.

Raw-byte `\\C`, arbitrary invalid binaries, and PCRE byte-profile behavior are
separate work. They must not be smuggled into Unicode mode.

### 7.3 Unicode data

The compatibility bundle uses the same pinned Unicode data version as the
erased Cure engine. A Unicode-table update is a semantic change and requires:

- regenerated tables;
- compile-time and runtime differential tests;
- BEAM/AtomVM comparison;
- compatibility-ledger review;
- a version increment if observable results change.

### 7.4 Subject and result ownership

The neutral ABI must specify whether each returned text value is copied, is a
view/sub-binary into the subject, or is represented only by indices. Retaining a
small capture must not accidentally retain an arbitrarily large subject without
the API making that tradeoff explicit.

The initial API must provide an index-only result mode suitable for constrained
AtomVM applications. The default text-returning mode should copy matched and
captured text unless AtomVM inspection establishes a safe, documented
sub-binary ownership model. Peak-memory benchmarks must include a small capture
from a large subject.

## 8. Failure and resource semantics

### 8.1 Compile failure versus no match

These states are disjoint:

```text
invalid/unsupported/too-large pattern -> {error, Diagnostic}
valid pattern, subject rejected        -> {ok, none} / nomatch
valid pattern, subject accepted         -> {ok, some(Match)} / {match, ...}
```

No parser fuel cutoff, machine-size cutoff, or execution guard may be reported
as `nomatch`.

### 8.2 Termination

The parser is structurally recursive over finite input. Matching is over a
finite subject and finite machine/control state. Any future feature that needs
an unbounded stack, unbounded subject memory, or an incomplete decision
procedure remains rejected in the compatibility tier.

### 8.3 Execution limits

If a future feature requires a runtime execution limit, exhaustion must produce
`RuntimeResourceLimit`, never a false negative. The initial finite engine
should instead derive bounds from pattern state count, assertion depth, and
subject length so ordinary matching has no ambiguous timeout outcome.

### 8.4 No host escape hatch

The compatibility tier must not fall back to `:re`, PCRE2, NIFs, ports, host
callbacks, processes, ETS, `persistent_term`, or a runtime JIT when it sees an
unsupported form. It must return `UnsupportedFeature`.

### 8.5 Complexity and regex-denial-of-service contract

Every admitted feature must publish a conservative asymptotic cost bound for
compilation, execution, and peak live memory. The bound must be expressed using
at least pattern AST size, finite machine state count, subject scalar length,
capture count, assertion depth, and maximum lookbehind width where relevant.

The initial finite subset must not contain catastrophic backtracking. For each
new assertion, control verb, finite translation, or capture feature, tests and
analysis must show whether it changes the execution bound. A feature whose only
available implementation has uncontrolled exponential exploration remains
unsupported even if typical fixtures are fast.

Resource limits are admission and safety checks, not substitutes for the cost
model. Benchmarks must include adversarial patterns and subjects near each
configured limit.

## 9. Proof and trust obligations

### 9.1 Shared machine correctness

The erased Cure engine's existing machine proofs remain authoritative. The
compatibility compiler must construct the same machine constructors and use
the same boundary, transition, ordered-search, evidence, and capture routines.

Where a runtime compiler produces an existential package, add an adapter theorem
that is polymorphic in the packaged `shape`. The theorem must show that
unpacking the runtime package yields the same plan accepted by the erased
engine.

### 9.2 Parser soundness

Once implementation begins, add a parser soundness theorem or an equivalent
checked relation:

```text
parse(source) = Parsed(ast)
  implies
denote(source) = denote(ast)
```

For syntax rejected by the compatibility subset, the parser must produce a
stable rejection code and span. The host parser may propose ASTs, but the
runtime Cure path must not trust an unchecked host-side cast.

### 9.3 Lowering equivalence

For every admitted AST constructor, prove or property-check:

```text
language(ast) = language(lower(ast))
```

For ordered captures and scan behavior, language equality is insufficient. The
test/proof relation must also cover:

- leftmost match selection;
- greedy/lazy choice;
- capture participation and text;
- branch-reset numbering;
- assertion polarity;
- empty-match advancement;
- scalar offsets and byte-map projection;
- marks/control metadata when supported.

### 9.4 Named compilation erasure

Named capture metadata must erase to the ordinary compilation exactly. The
existing named-compilation erasure certificate is the model for this boundary.
Adding a capture name must not change language acceptance, transition order, or
machine state count except for explicitly documented capture bookkeeping.

### 9.5 Translation certificates

If a runtime pattern is normalized from a construct that is not directly in the
finite AST, the translation must carry the same checked certificate required by
the parent proof-carrying normalization architecture. A source rewrite without
a certificate is not a compatibility feature.

## 10. BEAM and AtomVM packaging

### 10.1 Precompiled parser bundle

The AtomVM artifact must contain the compiled compatibility modules and all
reachable Cure standard-library dependencies. The application never invokes
the Cure compiler at runtime and never loads a dynamically generated module.

### 10.2 Allowed runtime features

The compatibility closure may use:

- ordinary tuples, lists, atoms, binaries, and closures supported by AtomVM;
- Cure scalar/string primitives already admitted by the erased-engine gate;
- pure recursive functions and immutable values;
- the finite machine and capture routines.

It may not use:

- NIFs or ports;
- host regex modules;
- process-global state;
- ETS or `persistent_term`;
- dynamic module loading;
- opaque PCRE handles;
- a host-language parser or callback interpreter.

### 10.3 Closure audit

The compatibility closure must be checked separately from the ordinary typed
closure. The audit must verify that `:re`, NIF, port, ETS, process, JIT, and
dynamic-code references are absent, including through generated helpers and
qualified calls.

### 10.4 Versioned ABI

The compiled value must contain a small format/version tag. The public facade
must reject an unknown version with `InvalidCompiledRegex` rather than trying
to interpret the term as a different machine representation.

No caller may depend on the internal tuple layout. If serialization is added,
it gets a separate versioned wire format and a size limit.

### 10.5 Foreign-term validation and serialization boundary

An Erlang or Elixir caller can forge any ordinary tuple. The public BEAM facade
must therefore treat every received compiled-pattern term as untrusted and
perform bounded structural validation before execution. Validation includes:

- outer tag and ABI/representation version;
- option and capability fields;
- machine constructor and state-count consistency;
- capture-layout indices and names;
- bounded nesting and collection sizes;
- absence of foreign closures or malformed transition data where the selected
  representation permits them.

Validation itself must have an explicit work and depth bound. Invalid terms
return `InvalidCompiledRegex`; they must not cause a pattern-match crash or
unbounded traversal.

Serialized compiled patterns are a first-release non-goal. The initial contract
supports values returned by `compile` within the running VM. A future wire
format requires independent decoding validation, size limits, semantic-version
rules, and adversarial corpus tests.

### 10.6 Release and capability manifest

Every vendored artifact must publish an inspectable manifest containing:

- engine semantic version;
- public BEAM ABI version;
- internal compiled-pattern representation version;
- pinned Unicode data version;
- supported feature/capability set;
- minimum and tested AtomVM versions;
- artifact/build identifier;
- compressed and uncompressed module sizes.

The AtomVM bundle must be reproducible from a clean checkout. Capability
negotiation uses the manifest or `capabilities()`; it must not probe support by
attempting a pattern and interpreting an arbitrary parse failure.

## 11. Testing and verification matrix

### 11.1 Shared-parser tests

For every existing literal fixture:

1. parse the source through the compile-time path;
2. parse the same source through the runtime parser;
3. compare normalized ASTs or a canonical serialization;
4. compare error codes and source spans for malformed inputs.

The parser must cover escaped delimiters, Unicode names, classes, ranges,
newline controls, captures, conditionals, assertions, and all admitted flags.

### 11.2 Compile-time/runtime differential tests

For patterns admitted by both paths, compare:

- full-match acceptance;
- leftmost search;
- prefix matching;
- greedy/lazy behavior;
- captures and names;
- empty captures versus unmatched captures;
- scan progress;
- split and replacement output;
- scalar spans and byte projections.

The compile-time result is normalized into the generic compatibility result for
comparison. The compatibility result must never be used to manufacture the
typed result.

### 11.3 PCRE/OTP oracle tests

OTP `:re` remains an independent oracle only for the documented overlap. Tests
must normalize intentional differences in offsets, capture representation,
Unicode mode, errors, and empty-match scanning. An oracle pass cannot discharge
a Cure proof obligation.

### 11.4 Resource and malformed-input tests

Add tests proving that:

- malformed patterns return structured diagnostics;
- unsupported constructs return `UnsupportedFeature`;
- pathological nesting returns a resource error;
- state expansion limits are enforced before a machine is returned;
- parser exhaustion never returns `nomatch`;
- forged/wrong-version compiled terms return errors rather than crashing.

### 11.5 BEAM/AtomVM tests

Run identical vectors against:

- Cure on BEAM;
- Erlang facade on BEAM;
- Elixir adapter on BEAM;
- the packed AtomVM artifact.

Compare ordinary BEAM terms after normalization. Include Unicode, malformed
input, empty matches, captures, assertions, newline policies, and errors.

Add a scheduler-fairness regression in which one process compiles or matches a
large adversarial-but-admitted input while an independent heartbeat process
must continue to run. Exercise both the AtomVM interpreter and JIT when they are
release targets. This is a progress test, not a fragile microsecond deadline.

### 11.6 Property and fuzz tests

Add properties for:

- parser prefix/suffix decomposition;
- parse/print/parse metadata invariance;
- compile-time/runtime AST equivalence;
- named-compilation erasure;
- every reachable machine state being valid;
- bounded lowering preserving state-count limits;
- scan termination and empty-match progress;
- compatibility results agreeing with the erased engine.

Fuzzing may find counterexamples, but a fuzz pass is not a substitute for a
checked finite model or executable regression.

## 12. Performance and memory requirements

### 12.1 Compile once, execute many

`compile` must produce a reusable pure value. `run`, `scan`, and `replace` must
not reparse or rebuild the machine. A convenience `run_source` may compile on
each call, but it must be explicitly named and documented as slower.

### 12.2 No global cache

The core compatibility module must not maintain a process-global cache. A
caller may cache `RuntimeRegex` values in an application-owned process or data
structure, but that policy is outside the AtomVM core and must not be required
for correctness.

### 12.3 Cold-start budget

Record separate budgets for:

- module load/startup;
- first runtime parse/compile;
- repeated matching using one compiled value;
- scan and replacement;
- peak memory for parser and machine construction.

The benchmark must include realistic firmware patterns and deliberately large
patterns near each configured limit.

### 12.4 First-order representation preference

Where closures materially increase AtomVM memory or serialization cost, use the
existing transition-row representation or another first-order table. This is a
representation optimization only; it must preserve the canonical machine and
its proof relation.

### 12.5 Concurrency and reentrancy

A compiled regex is immutable and may be shared safely by multiple BEAM
processes. All cursor, frontier, capture, assertion, continuation, scan, and
replacement state belongs to one invocation and must not be stored in the
compiled value or process-global state.

Tests must execute the same compiled value concurrently against different
subjects and compare each result with isolated execution. Reentrancy must also
hold when a future replacement callback invokes the same compiled regex.

## 13. Feature and compatibility policy

The compatibility tier begins with the erased engine's completed finite subset.
It does not automatically inherit every future PCRE extension. A feature enters
the runtime tier only when all of these exist:

1. shared parser support;
2. shared normalized AST/IR support;
3. finite lowering;
4. ordered-result semantics;
5. proof or checked equivalence relation;
6. structured runtime diagnostics;
7. BEAM/AtomVM differential tests;
8. compatibility-ledger entry.

Unsupported features must be listed explicitly. Examples that remain rejected
until separately proven include:

- unbounded backreferences;
- unbounded recursion/subroutine calls;
- callouts and embedded code;
- arbitrary host callbacks;
- raw-byte semantics in Unicode mode;
- runtime-computed unbounded lookbehind;
- host-dependent backtracking verbs.

Finite translations may be admitted when their bounds are visible and checked.
They must use the source-AST-to-canonical-IR certificate architecture, never
string rewriting.

## 14. Implementation phases after the prerequisite gate

### Phase 0 — Activation review

- Verify the erased-engine completion evidence.
- Freeze the initial compatibility subset and ABI.
- Update the parent portability specification so “no runtime parser” applies
  only to the ordinary typed production closure.
- Create a compatibility ledger with explicit unsupported forms.

### Phase 1 — Shared syntax extraction

- Remove compile-time-only wording from shared AST/model modules.
- Ensure parser/model modules have no macro or compiler-environment imports.
- Add parser entry points returning structured errors and source spans.
- Add compile-time/runtime parser equivalence fixtures.
- Do not alter typed lowering semantics.

### Phase 2 — Existential runtime plan

- Define the private `RuntimePlan` and `RuntimeRegex` representations.
- Add existential adapters around the existing staged machine forms.
- Reuse named capture compilation and erasure certificates where applicable.
- Add tests that unpack a runtime plan and execute the same machine routines as
  a compile-time staged plan.

### Phase 3 — Runtime compiler

- Parse pattern and flags.
- Normalize options, captures, references, and finite translations.
- Lower AST to the shared runtime plan.
- Enforce all compile-time resource limits at runtime.
- Return structured diagnostics for every rejection.

### Phase 4 — Generic Cure API

- Implement `compile`, `run`, `run_prefix`, `scan`, `split`, and literal
  replacement.
- Project typed machine traces into generic matches and capture lists.
- Implement scalar spans and optional byte-map projections.
- Ensure compiled values are reusable and do not reparse.

### Phase 5 — BEAM facade

- Add the neutral `cure_regex` Erlang ABI.
- Add an idiomatic Elixir adapter without changing the neutral terms.
- Add version checks and forged-term diagnostics.
- Document the subset and all intentional `:re` differences.

### Phase 6 — AtomVM packaging

- Compile the closure for the AtomVM target.
- Remove or reject unsupported host dependencies.
- Pack the modules into a minimal artifact.
- Run identical BEAM/AtomVM vectors and memory/startup benchmarks.
- Audit every reachable native primitive for input-sized uninterruptible work.
- Run the scheduler-fairness heartbeat regression on the interpreter and JIT.

### Phase 7 — Compatibility expansion

- Add only features already accepted by the erased Cure engine.
- Add one vertical slice per feature: red regression, parser, normalizer,
  lowering, execution, proof/equivalence, ABI, and AtomVM test.
- Never add a compatibility-only semantic feature as a shortcut around a
  missing erased-engine feature.

### Phase 8 — Stabilization

- Run the full Cure suite and all compatibility tests serially.
- Run TCB, totality, erasure, Antigen, canonical pipeline, Unix/escript, and
  AtomVM gates.
- Audit the reachable closure for `:re`, NIF, port, process, ETS, and dynamic
  code references.
- Publish the supported-version/capability ledger.

## 15. Commit boundaries

Implementation, when unblocked, must be split into reviewable commits:

1. shared AST/parser extraction with no behavior change;
2. existential runtime-plan adapters;
3. runtime parser and diagnostics;
4. runtime AST lowering and resource admission;
5. generic Cure API and capture projection;
6. Erlang/Elixir facades;
7. AtomVM packaging and closure gates;
8. individually proven compatibility feature expansions;
9. documentation and compatibility-ledger updates.

The erased-engine completion commit must remain separate from all of these.

## 16. Acceptance criteria

The compatibility layer may be advertised only when:

- runtime patterns can be compiled without the Cure compiler, PCRE, `:re`,
  NIFs, ports, processes, ETS, or dynamic code loading;
- the parser and normalizer are shared with the compile-time path;
- runtime lowering feeds the same finite machine semantics;
- generic capture and offset behavior is documented and tested;
- invalid, unsupported, and resource-exhausted patterns produce structured
  errors distinct from no-match;
- compiled values are reusable and pure;
- BEAM and AtomVM produce identical normalized results;
- the AtomVM closure is independently audited;
- large pure-Cure regex work permits another AtomVM process to make progress,
  and no reachable native primitive hides an unbounded parser or matcher loop;
- compile-time/runtime differential tests pass for the entire claimed subset;
- the compatibility ledger names every intentional divergence from `:re`,
  Elixir `Regex`, and PCRE2;
- no typed Cure proof or erased-engine invariant was weakened to support the
  runtime path.

The final claim is therefore precise: Cure supplies a portable runtime regex
compatibility subset for BEAM and AtomVM, while Cure proper retains its richer
compile-time, typed, proof-backed regex interface.
