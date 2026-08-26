# Certificate-Generating Solver Integration — execution specification

**Date:** 2026-07-22
**Status:** implementation-ready follow-on to verified LIA reflection
**Layers:** stdlib metatheory (checked), elaborator/tooling (untrusted), kernel unchanged

This specification turns the verified-LIA design into the concrete boundary at
which Cure can accept certificates from an external generator. It is
authoritative for the work remaining after the proof-language, lemma-search,
indexed-constructor, and rich-diagnostic repairs landed on `otp-metatheory`.

The general LIA mathematics remains
`2026-07-18-verified-lia-reflection-design.md`; §4.5 adds the OTP-specific
semilinear mathematics that design did not cover. This document fixes the
current implementation inventory, module/API boundaries, protocol, failure
semantics, diagnostics, editor behavior, phases, and acceptance gates. Where
the older design describes P1/P2/P3 abstractly, this document is the execution
plan.

## 1. Outcome

Given a supported mailbox-pattern inclusion or linear-integer-arithmetic
obligation, Cure can:

1. quote it into a canonical semilinear-inclusion or LIA problem;
2. send that problem to an untrusted in-process or external producer;
3. receive either a Farkas or Presburger certificate, a countermodel, or an
   honest unknown result;
4. translate a witness into ordinary Cure evidence using the verified checker;
5. submit that evidence to the existing kernel; and
6. accept the program only when the existing kernel checks the resulting term.

The external program is a **certificate generator**, never a proof oracle. Its
native `sat`/`unsat` answer and native proof format have no authority. The only
successful result is a canonical certificate accepted by Cure's checked
metatheory and then by the unchanged kernel.

Execution is OTP-first. The first complete pipeline decides a sound, useful
fragment of semantic inclusion between commutative-regex mailbox patterns by
checking affine embeddings between their semilinear components. This is the
actual B3 counting/multiplicity blocker. General rational LIA uses compact
Farkas witnesses; broader quantifier-free integer contradictions later add
divisibility, cut, split, bounded-enumeration, and normalization nodes. A
producer may return `Unknown(:incomplete_procedure)` whenever the obligation is
outside the currently checked certificate language or configured budget.

## 2. Locked trust boundary

The following are non-negotiable:

- `Cure.Core.*` receives no new term, value, evaluator, conversion, or checking
  rule for LIA.
- No solver executable, producer module, parser, IPC adapter, certificate cache,
  or elaborator recognizer joins the TCB.
- A producer cannot return a Core proof term. It returns data only.
- A producer's `unsat` result without an accepted certificate is `Unknown`, not
  `Proven`.
- A producer's model is diagnostic evidence only after Cure independently
  evaluates every normalized hypothesis and the negated goal against it.
- Timeout, crash, malformed output, unsupported syntax, version mismatch,
  resource exhaustion, and incomplete search never mean success.
- Every generated proof term is checked with `Cure.Core.Kernel.check/3` against
  the original residual goal before it is returned from proof search.
- The checker is an ordinary total Cure program. The kernel discharges it by
  existing delta/iota computation. If implementation appears to require a new
  kernel rule, stop: that is a design violation, not an implementation task.

The trusted statements are therefore:

```text
kernel checks(checked_pattern_inclusion(source, target, certificate), original_goal)
kernel checks(check_lia_sound(problem, certificate), original_goal)
```

not:

```text
external solver said unsat
```

## 3. Current implementation inventory

At the start of this work the following is already present and must be reused:

- `Std.Int.Int = FromNat(Nat) | NegativeSuccessor(Nat)` is the sole integer
  representation.
- `Std.Proof.IntOrder` and `Std.Proof.IntDiscrete` provide the canonical ordered
  additive substrate.
- `Std.Proof.LinearArithmetic` already defines `Relation`, `LinearAtom`,
  `Hypotheses`, `FarkasWitness`, `Valuation`, dimension checks, affine
  combination, goal negation, and `check_lia_candidate/3`.
- The accepted/forged/short/dimension/boundary computation probes exist in
  `https://github.com/cure-lang/cure-otp/tree/main/metatheory/oracle/otp/linear_arithmetic_compute.{cure,idr}` and
  `test/cure/stdlib/linear_arithmetic_compute_test.exs`.
- The affine semantic lemmas needed by the soundness proof have begun landing in
  `Std.Proof.IntOrder` and the proof-language ergonomics now exist.
- `Cure.Elab.ProofSearch` has a deterministic ordered solver seam and already
  kernel-checks synthesized candidates.
- Rich structured diagnostics, source spans, completion, and hover
  infrastructure are available.

The following is **not** complete merely because `check_lia_candidate/3`
computes:

- proof-relevant certificate validity;
- Boolean-to-validity inversion;
- the LIA soundness theorem;
- quotation of Core goals and hypotheses into canonical atoms;
- any certificate producer;
- the producer registry/protocol;
- construction of checked evidence from a returned certificate;
- end-to-end solver dispatch;
- external-process hardening and user-facing diagnostics.

### 3.1 Immediate OTP consumer

The critical OTP gap is B3 in
`https://github.com/cure-lang/cure-otp/tree/main/docs/research/process-types/2026-07-17-otp-formalisation-ledger.md`: semantic
inclusion of commutative-regex mailbox patterns over Parikh vectors. It is not
merely a conjunction of quantifier-free affine atoms.

The existing checked `Otp.Meta.MailboxPattern` substrate already provides:

- `Pat = PZero | POne | PAtom | PPlus | PTimes | PStar`;
- three-coordinate natural-number multisets;
- `Accepts(pat, multiset)`;
- the sound but incomplete syntactic `Incl` relation; and
- derivative/nullability soundness and completeness.

The external `mbcheck` reference normalizes patterns into finite unions of
linear sets and states inclusion as quantified Presburger arithmetic. Its full
formula language contains conjunction, disjunction, negation, equality/order,
and existential/universal quantifiers. Therefore the generic Farkas and
cut/split tree alone is not a complete checker for B3. The first slice uses a
smaller domain certificate that directly proves a meaningful subset of
semilinear inclusions.

`Cure.SMT.Process` is not this interface. It remains the Z3 transport for the
separate, untrusted guard lint. The permissive historical
`Cure.Project.Proof.Verifier` SMT path is also not a certificate checker and must
not be reused as one.

## 4. P1 — finish the verified checker

No producer result may discharge a goal until the corresponding checked
validity and soundness layer is complete. Sections 4.1–4.4 describe general
LIA; §4.5 is the earlier OTP execution slice.

### 4.1 Checked data and evidence

Extend `Std.Proof.LinearArithmetic` with descriptive, proof-relevant types for:

- a common coefficient dimension for all atoms;
- exact witness length `length(hypotheses) + 1`;
- successful dimension-preserving affine combination;
- every final coefficient being zero;
- the combined normalized bound being strictly negative; and
- the goal relation being supported (`LessOrEqual` or `LessThan`).

The public validity proposition is:

```cure
ValidFarkasCertificate(hypotheses, goal, witness)
```

Its constructors must make malformed shape, truncation, and unsupported goal
relations unrepresentable. It may internally contain smaller evidence records,
but callers must not be able to construct validity from a bare Boolean or an
unchecked `LinearAtom`.

Add a second proof-relevant family for integer reasoning:

```cure
PresburgerCertificate(problem)
ValidPresburgerCertificate(problem, certificate)
```

Its closed v1 node set is:

- `FarkasLeaf` — delegates a rationally valid branch to the Farkas checker;
- `DivisibilityContradiction` — proves that the gcd of an integer affine
  equality's coefficients cannot divide its constant;
- `Cut` — derives a rounded integer inequality and continues with a child;
- `Split` — proves both exhaustive integer branches around a bound;
- `Enumerate` — checks every value in a finite, explicitly bounded interval;
- `Normalize` — records checked affine normalization/substitution; and
- `Contradiction` — closes a branch from an already checked false atom.

Every recursive child carries a strictly smaller fuel/measure witness. The
checker is total, rejects malformed references and non-decreasing recursion,
and cannot construct validity from a producer's native rule name.

### 4.2 Public checker API

The checked module exports:

```cure
fn check_lia(
  hypotheses: Hypotheses,
  goal: LinearAtom,
  witness: FarkasWitness
) -> Bool

fn decide_farkas_certificate(
  hypotheses: Hypotheses,
  goal: LinearAtom,
  witness: FarkasWitness
) -> Decision(ValidFarkasCertificate(hypotheses, goal, witness))

fn check_lia_true_implies_valid(
  hypotheses: Hypotheses,
  goal: LinearAtom,
  witness: FarkasWitness,
  checked: IsTrue(check_lia(hypotheses, goal, witness))
) -> ValidFarkasCertificate(hypotheses, goal, witness)

fn check_presburger(
  problem: PresburgerProblem,
  certificate: PresburgerCertificate(problem)
) -> Bool

fn check_presburger_true_implies_valid(
  problem: PresburgerProblem,
  certificate: PresburgerCertificate(problem),
  checked: IsTrue(check_presburger(problem, certificate))
) -> ValidPresburgerCertificate(problem, certificate)

fn check_presburger_sound(
  problem: PresburgerProblem,
  certificate: PresburgerCertificate(problem),
  valid: ValidPresburgerCertificate(problem, certificate),
  valuation: Valuation,
  holds: ProblemHypothesesHold(problem, valuation)
) -> IsTrue(evaluate_problem_goal(problem, valuation))
```

`check_lia_candidate/3` is either renamed to `check_lia/3` once the inversion
theorem is proven or retained as a private implementation helper. There must not
be two public checkers with subtly different meanings.

### 4.3 Soundness theorem

The checked payoff remains:

```cure
fn check_lia_sound(
  hypotheses: Hypotheses,
  goal: LinearAtom,
  witness: FarkasWitness,
  valid: ValidFarkasCertificate(hypotheses, goal, witness),
  valuation: Valuation,
  holds: AllHold(hypotheses, valuation)
) -> IsTrue(evaluate_atom(goal, valuation))
```

P1 must complete and use, rather than assume, the following proof layers:

1. canonical signed-integer additive/scaling laws;
2. coefficient-vector evaluation homomorphisms;
3. witness-fold preservation;
4. exact shape preservation;
5. `AllHold` list elimination/extension;
6. correctness of `<=`/`<` negation and strict normalization;
7. contradiction elimination for the zero-coefficient negative-bound form; and
8. Boolean-checker inversion into `ValidFarkasCertificate`.

No postulate, axiom, trusted declaration, unchecked extern, or opaque runtime
primitive may close these obligations.

The Presburger soundness proof additionally covers gcd/divisibility,
floor/ceiling rounding, branch exhaustiveness, bounded enumeration, checked
substitution, and well-founded recursive checking. It may reuse Farkas
soundness at `FarkasLeaf` nodes.

### 4.4 P1 acceptance

P1 is done only when:

- the positive multi-hypothesis witness is accepted;
- `2n = 1` is accepted through a valid divisibility certificate;
- forged, short, long, zero-multiplier, and dimension-mismatched witnesses are
  rejected deterministically;
- forged gcd, cut, split, enumeration, normalization, and recursion evidence is
  rejected deterministically;
- the soundness theorem type-checks in Cure;
- the Idris mirror reports `rel=same`;
- the theorem and all definitions it relies upon are certified total;
- axiom-closure/release checks remain clean; and
- mutating the checker to accept any malformed antibody causes a test failure.

### 4.5 OTP-first semilinear inclusion checker

This slice has execution priority over the general Presburger tree above. Its
canonical checked values are:

```cure
type NatVector = ...
type LinearSet = MkLinearSet(NatVector, List(NatVector))
type SemiLinearSet = List(LinearSet)

type LinearEmbedding = MkLinearEmbedding(
  target_component: Nat,
  base_offset: List(Nat),
  period_images: List(List(Nat))
)

type SemiLinearInclusionCertificate =
  MkSemiLinearInclusionCertificate(List(LinearEmbedding))
```

A linear set denotes:

```text
L(base, periods) = { base + sum(k[i] * periods[i]) | every k[i] in Nat }
```

For each source component `L(b, P)`, its `LinearEmbedding` selects one target
component `L(c, Q)` and supplies a nonnegative offset vector `o` plus one
nonnegative image vector `M[i]` for every source period. The checker recomputes
and requires:

```text
b    = c + Q * o
P[i] = Q * M[i]       for every source period P[i]
```

Here `Q * coefficients` means the checked natural linear combination of the
target period vectors. These equations induce the target coefficients
`o + sum(k[i] * M[i])` for every source point, proving component inclusion.
One embedding is required for every source component. Indexes, vector
dimensions, period counts, coefficient lengths, and every equality are checked;
lists may not truncate silently.

The checked API is:

```cure
fn normalize_pattern(pat: Pat) -> SemiLinearSet

fn check_semilinear_inclusion(
  source: SemiLinearSet,
  target: SemiLinearSet,
  certificate: SemiLinearInclusionCertificate
) -> Bool

fn check_semilinear_inclusion_sound(
  source: SemiLinearSet,
  target: SemiLinearSet,
  certificate: SemiLinearInclusionCertificate,
  checked: IsTrue(check_semilinear_inclusion(source, target, certificate)),
  multiset: MS,
  accepted: SemiAccepts(source, multiset)
) -> SemiAccepts(target, multiset)

fn checked_pattern_inclusion(
  source: Pat,
  target: Pat,
  certificate: SemiLinearInclusionCertificate,
  multiset: MS,
  accepted: Accepts(source, multiset)
) -> Accepts(target, multiset)
```

`checked_pattern_inclusion` composes the checker theorem with both directions
of the normalization bridge:

```text
Accepts(pat, m) <-> SemiAccepts(normalize_pattern(pat), m)
```

Normalization follows the already inspected `mbcheck` construction:

- `POne` is the singleton linear set with zero base and no periods;
- `PZero` is the empty union;
- `PAtom(t)` is the singleton vector for `t`;
- `PPlus` is union;
- `PTimes` is pairwise Minkowski sum of components; and
- `PStar` promotes component bases to periods and takes the finite product of
  the resulting component stars.

The raw `mbcheck` construction represents the star of a period-free singleton
`L(b,{})` as `L(0,{}) union L(b,{b})`. Cure's checked canonical simplifier may
coalesce exactly this pair to `L(0,{b})`; the equivalence must be proved in both
directions. This is why the locked positive probe has the compact normalized
core shown below. No unproved semilinear rewrite is permitted merely to improve
producer input.

The locked first positive probe is:

```text
PStar(PTimes(PAtom(TA), PAtom(TA))) <= PStar(PAtom(TA))
```

Its normalized core is `L(0,{[2,0,0]}) <= L(0,{[1,0,0]})`; the period image is
the coefficient vector `[2]`. The locked negative control reverses the
inclusion and returns the independently validated counterexample `[1,0,0]`.
This is genuinely multiplicity/star reasoning and is not derivable using the
current syntactic `Incl` constructors.

This certificate is intentionally sufficient but incomplete: some true
inclusions require partitioning one source component across multiple target
components. Such cases return `Unknown(:incomplete_procedure)` until the later
semilinear-cover or quantified-Presburger layer lands.

The checked implementation lives in
`lib/std/otp_mailbox_semilinear.cure` as
`Std.Otp.MailboxSemilinear`, importing and reusing
`Otp.Meta.MailboxPattern`; do not duplicate `Tag`, `MS`, `Pat`, or `Accepts`.
The differential mirror is
`https://github.com/cure-lang/cure-otp/tree/main/metatheory/oracle/otp/mailbox_semilinear.{cure,idr}`, and focused host tests live in
`test/cure/stdlib/otp_mailbox_semilinear_test.exs`. Producer/recognizer code
lives under `Cure.Elab.Solver.Semilinear*`, separate from the checked stdlib.

## 5. Canonical producer-neutral problem format

The producer boundary uses values, not Core terms or surface AST.

The OTP-first request is already normalized semilinear data:

```elixir
%Cure.Elab.Solver.SemilinearInclusionProblem{
  version: 1,
  dimension: non_neg_integer(),
  source: [linear_set()],
  target: [linear_set()],
  diagnostic_source: diagnostic_source()
}

%Cure.Elab.Solver.LinearSet{
  base: [non_neg_integer()],
  periods: [[non_neg_integer()]]
}
```

Every vector has exactly `dimension` entries. Components and periods use the
deterministic order produced by `normalize_pattern`; producer output refers to
that order and cannot reorder the problem.

The generic LIA request remains:

```elixir
%Cure.Elab.Solver.LiaProblem{
  version: 1,
  variables: [binary()],
  hypotheses: [atom()],
  goal: atom(),
  source: diagnostic_source()
}

%Cure.Elab.Solver.LinearAtom{
  coefficients: [integer()],
  constant: integer(),
  relation: :less_or_equal | :less_than | :equal
}
```

The semantic convention is fixed:

```text
sum(coefficients[i] * variables[i]) relation constant
```

Rules:

- `variables` order is first semantic occurrence after normalization, with a
  stable de-Bruijn/source-name tie-break; it is never map iteration order.
- Every atom has exactly `length(variables)` coefficients.
- Coefficients, constants, and model values are arbitrary-precision signed
  decimal integers in serialized form.
- `>=` and `>` are normalized by negating both sides into `<=` and `<`.
- Strict inequalities stay explicit at this boundary; the checked Cure layer
  performs its specified discrete normalization.
- Equalities remain explicit in the Presburger problem so divisibility facts
  are not erased. The Farkas projection deterministically expands an equality
  into its two inequalities. Equality goals are handled by proving both ordered
  directions, or produce an explicit unsupported result if the selected
  producer cannot construct both certificates.
- Nonlinear multiplication, division/modulo by variables, bitwise operations,
  floats, opaque calls, effects, holes, and unsupported coercions cause
  `Unknown(:unsupported_theory)` before producer invocation.
- The source field is never serialized to the producer and has no semantic
  effect. It exists only for diagnostics.

Normalization must be deterministic and independently unit-tested. Two
alpha-equivalent supported obligations must produce identical semantic problems
apart from diagnostic names/spans.

## 6. Producer result and behavior

Every producer implements one behavior:

```elixir
@callback produce(SolverProblem.t(), options()) ::
  {:certificate, FarkasCertificate.t(), ProducerMeta.t()}
  | {:certificate, PresburgerCertificate.t(), ProducerMeta.t()}
  | {:certificate, SemiLinearInclusionCertificate.t(), ProducerMeta.t()}
  | {:model, LiaModel.t(), ProducerMeta.t()}
  | {:unknown, unknown_reason(), ProducerMeta.t()}
```

The closed v1 unknown reasons are:

```text
:unsupported_theory
:incomplete_procedure
:budget_exhausted
:timeout
:unavailable
:protocol_error
:malformed_output
:solver_failure
:certificate_rejected
:model_rejected
```

Certificates carry an explicit kind and theory version; dispatch never guesses
from shape. `FarkasCertificate` contains only the ordered nonnegative
multiplier vector.
Negative multipliers, rationals not converted to an equivalent integer vector,
wrong lengths, and over-limit integers are malformed output.

`LiaModel` contains exactly one integer for each declared variable. A partial,
duplicate, non-integer, or extra assignment is rejected. Cure evaluates the
canonical problem under the model before it may be shown as a counterexample.

Producer metadata may contain producer name/version, elapsed time, and a stable
diagnostic trace. It never affects checking, cache keys, or generated evidence.

## 7. Producer registry and selection

Introduce a producer-neutral registry under `Cure.Elab.Solver`, not inside the
kernel and not coupled to `Cure.SMT.Process`.

The registry entry contains:

```elixir
%{
  id: :semilinear_inclusion,
  recognizer: &SemilinearRecognizer.recognize/3,
  producer: configured_producer,
  evidence_builder: &SemilinearEvidence.build/5
}
```

The first registry entry is `:semilinear_inclusion`; `:lia` joins through the
same seam after the OTP vertical slice is green. Producer selection is
configuration of a theory, not competing proof candidates:

1. explicit project configuration;
2. the bundled deterministic producer;
3. otherwise `Unknown(:unavailable)`.

There is no silent fallback from a configured external producer to a different
external producer. A separately enabled bundled fallback may run after an
external `Unknown`, but the diagnostic trace records both attempts and only a
checked certificate can succeed.

The existing lemma and positivity solvers retain precedence. LIA runs only after
those cheap syntactic strategies return `:none`; ambiguity and real errors are
never hidden by LIA.

## 8. P2 — reference certificate producer

Ship a deterministic in-process producer before relying on an external binary.
It serves as an executable reference for the protocol and a CI-independent
baseline.

The first producer is the OTP affine-embedding search specified in §4.5. For
each normalized source component it deterministically searches target
components in canonical order, solves the natural-vector base/period equations,
and returns the lexicographically least valid embedding. If no embedding is
found it searches a bounded Parikh-vector space for a real counterexample;
otherwise it returns `Unknown(:incomplete_procedure)`. It never reports a true
inclusion false merely because the sufficient embedding fragment failed.

After that slice, the general LIA producer uses bounded deterministic
Fourier–Motzkin/simplex-style search followed by a Presburger pass:

- fixed variable order from the canonical problem;
- fixed hypothesis and pivot order;
- exact rational/integer arithmetic, never floats;
- a committed operation/bit-size budget;
- primitive integer normalization of a rational multiplier vector;
- bounded gcd/divisibility contradictions, cuts, splits, and finite
  enumeration; and
- `Unknown(:budget_exhausted)` rather than heuristic acceptance.

Required properties:

- every emitted certificate is accepted by the checked checker;
- every emitted model independently satisfies all hypotheses and falsifies the
  goal;
- repeated runs produce byte-identical semantic results;
- permutation tests either preserve the canonicalized result or document the
  stable ordering rule; and
- deliberate producer mutations cannot infect kernel acceptance.

The producer is useful but not trusted. A bug may cause `Unknown`, a rejected
certificate, or a bad diagnostic model; it may not make an invalid program pass.

## 9. P3 — elaborator reflection seam

### 9.1 Recognition

When existing local/lemma/positivity search returns `:none`, the LIA recognizer:

1. weak-head-normalizes the residual goal;
2. recognizes supported `IsTrue` integer comparisons;
3. enumerates relevant local hypotheses in context order;
4. quotes only supported comparison evidence into atoms;
5. normalizes variables and affine expressions; and
6. returns either a canonical `LiaProblem` or `:not_applicable` /
   `{:unsupported, reason, source}`.

`not_applicable` allows ordinary proof search to continue. `unsupported` means
the goal is recognizably arithmetic but outside v1; explicit solver invocation
reports it, while opportunistic automatic search may preserve the existing
unsolved-goal error with an attached note.

The recognizer must never invent facts from runtime control flow, erased values,
untrusted refinements, or types merely convertible to a comparison by an
uncontrolled reduction. Only evidence present in the kernel context is usable.

### 9.2 Evidence construction

For an OTP semilinear certificate, the evidence builder constructs
`checked_pattern_inclusion(source, target, certificate, ...)` and kernel-checks
the resulting function against the original semantic-inclusion obligation.
Pattern normalization is rerun inside checked Cure code; the elaborator does
not assert that its Elixir normalization matched.

For `{:certificate, witness, meta}`:

1. revalidate shape and numeric limits in Elixir;
2. construct the canonical Cure `LinearAtom`/list/witness values;
3. build the ordinary application of the checked decision/inversion/soundness
   functions;
4. instantiate the valuation and `AllHold` bridge needed to match the original
   proposition;
5. kernel-check the final Core term against the exact original goal; and
6. return `{:ok, term}` only after that check succeeds.

A failure at steps 2–5 becomes `Unknown(:certificate_rejected)` with structured
diagnostic context. It must never fall through as if the producer did not apply.

For a validated model, return a structured disproven result to an explicit proof
command or a diagnostic note to opportunistic search. A model does not itself
construct evidence of negation unless a separately checked reflection path is
implemented.

### 9.3 Invocation surface

The integration must support both:

- automatic fallback for unresolved supported proof/refinement obligations; and
- an explicit proof command spelling, `because linear arithmetic`, so authors
  can request the procedure and receive its full diagnostics.

The parser may also accept the ceremonial equivalent already allowed for other
proof commands, but formatter output and documentation use the plain spelling.
This phase must not add a generic `smt` keyword: the checked theory is LIA, while
the producer implementation is replaceable.

## 10. External certificate-generator protocol

P4 makes the producer replaceable by a process such as a Z3/cvc5/veriT adapter.
The native solver output is translated outside Cure into the protocol below;
Cure does not replay or trust the solver's native proof.

### 10.1 Transport

- Executable and arguments are explicit project configuration; no shell string
  is evaluated.
- Communication is newline-delimited canonical JSON over stdin/stdout.
- One request produces exactly one response with the same request id.
- Stderr is bounded diagnostic text and never parsed semantically.
- Each process has wall-clock, output-byte, integer-bit-size, atom-count,
  variable-count, and certificate-length limits.
- Cancellation closes the request and kills a dedicated process after a bounded
  grace period. No orphan solver process may survive compilation.
- Environment inheritance is allowlisted. Network access and working-directory
  dependence are outside the protocol.

### 10.2 Request v1

```json
{"protocol":"cure-certificate-generator","version":1,"id":"<opaque>","theory":"semilinear-inclusion-v1","dimension":3,"source":[{"base":["0","0","0"],"periods":[["2","0","0"]]}],"target":[{"base":["0","0","0"],"periods":[["1","0","0"]]}],"limits":{"operations":100000,"integer_bits":4096,"certificate_nodes":10000}}
{"protocol":"cure-certificate-generator","version":1,"id":"<opaque>","theory":"presburger-v1","variables":["x0","x1"],"hypotheses":[{"coefficients":["-1","0"],"constant":"0","relation":"less_or_equal"},{"coefficients":["0","-1"],"constant":"0","relation":"less_or_equal"}],"goal":{"coefficients":["-2","-3"],"constant":"0","relation":"less_or_equal"},"limits":{"operations":100000,"integer_bits":4096,"certificate_nodes":10000,"branch_depth":64}}
```

### 10.3 Response v1

Exactly one of:

```json
{"protocol":"cure-certificate-generator","version":1,"id":"<opaque>","result":"certificate","kind":"semilinear_inclusion","embeddings":[{"target_component":0,"base_offset":["0"],"period_images":[["2"]]}]}
{"protocol":"cure-certificate-generator","version":1,"id":"<opaque>","result":"certificate","kind":"farkas","multipliers":["2","3","1"]}
{"protocol":"cure-certificate-generator","version":1,"id":"<opaque>","result":"certificate","kind":"presburger","root":{"node":"divisibility_contradiction","atom":0,"gcd":"2"}}
{"protocol":"cure-certificate-generator","version":1,"id":"<opaque>","result":"model","values":["0","-1"]}
{"protocol":"cure-certificate-generator","version":1,"id":"<opaque>","result":"unknown","reason":"incomplete_procedure"}
```

Unknown keys are rejected in v1. Missing keys, duplicate JSON keys, noncanonical
integer strings, negative multipliers, trailing output, mismatched ids/versions,
and a second response are protocol errors. Parser acceptance must not exceed the
documented grammar.

Presburger nodes use zero-based indexes into the canonical atom table; they do
not repeat or replace problem statements. `cut`, `split`, `enumerate`, and
`normalize` contain their checked derived atom plus child node(s).
`divisibility_contradiction` contains an equality atom index, the claimed
positive gcd, and Bézout coefficients sufficient for the checker to recompute
the gcd claim. Every node carries a natural-number `fuel` strictly greater than
each child's fuel. Node count, depth, branch width, indexes, integers, and
embedded vectors are validated before Cure values are allocated. The complete
JSON schema lands with Phase D and is frozen by accept/reject fixtures before a
real adapter is merged.

### 10.4 Caching

Cache only canonical producer results keyed by:

```text
protocol version
theory version
canonical semantic problem
producer identity/version
semantic limits
```

Source spans and variable display names are excluded. A cached certificate is
always rechecked; a cache hit never bypasses evidence construction or the
kernel. Unknown results may be cached only for deterministic semantic reasons
(`unsupported_theory`, `incomplete_procedure`), never for timeout, unavailable,
or solver failure.

## 11. Diagnostics

All new failures use structured problem types and the existing rich diagnostic
adapter/registry. No producer or elaborator code assembles final prose.

Required diagnostic categories:

1. **Unsupported arithmetic goal** — highlights the first unsupported
   subexpression and names the supported LIA fragment.
2. **Unsupported mailbox inclusion** — highlights the source and target
   patterns and explains whether normalization failed or the inclusion needs a
   semilinear-cover/quantifier-elimination certificate unavailable in v1.
3. **Certificate generator unavailable** — names the configured producer and
   actionable setup/configuration advice.
4. **Certificate generation timed out / exhausted budget** — shows the goal,
   active limits, and that no proof was accepted.
5. **Certificate generator protocol error** — reports bounded producer/version
   context without dumping uncontrolled output.
6. **Certificate rejected** — distinguishes malformed affine embeddings,
   invalid component/vector equations, invalid Farkas combinations, invalid
   gcd/cut/split/enumeration nodes, numeric limits, and final kernel rejection.
   This is loud because it indicates a producer bug or incompatible adapter.
7. **Counterexample found** — displays a validated Parikh vector or variable
   assignment and the source acceptance/target rejection that it witnesses.
8. **Procedure incomplete** — explains which supported Presburger certificate
   nodes the selected producer could not construct within the active limits and
   suggests explicit evidence or a different configured producer.

Every category needs:

- stable code allocated from the current registry at implementation time;
- exact primary/secondary spans from source metadata;
- color and no-color snapshots at width 80;
- one CLI test, one elaborator-level structured-payload test, and one LSP
  publication test where applicable;
- bounded/redacted external output; and
- no collapse of `Unknown` into the generic internal compiler error.

## 12. Completion and hover

The explicit `because linear arithmetic` surface participates in the same
language-service tables as the rest of the proof language.

The OTP slice is normally invoked by mailbox inference/subtyping rather than a
new proof keyword. Hover on an inferred mailbox constraint shows the normalized
source/target patterns, certificate theory `semilinear-inclusion-v1`, and
whether the result was checked, disproven, or incomplete. Completion for
mailbox-pattern constructors and inferred pattern variables remains available
in those type positions; no producer-specific name appears in source.

- Completion offers `linear arithmetic` only in a proof-justification position.
- Hover explains that it invokes an untrusted generator and that Cure rechecks
  the returned certificate.
- Hover on a successful generated step shows the theory (`lia-farkas-v1` or
  `presburger-v1`; mailbox constraints show `semilinear-inclusion-v1`), not a
  claim that Z3/cvc5 itself proved the theorem.
- Hover/diagnostics for `Unknown` name the stable reason.
- Go-to-definition for the phrase, if supported for proof commands, targets the
  checked `Std.Proof.LinearArithmetic` documentation rather than an external
  executable.
- Formatter round-trips the plain spelling and never injects producer-specific
  syntax.

## 13. Security and resource discipline

- All length/count/bit-size limits are checked before allocation proportional to
  producer-controlled values.
- JSON integer strings are parsed with explicit digit and bit limits.
- Certificate checking is total and separately bounded by compiler policy; a
  certificate bomb is rejection, not compiler failure.
- Producer processes are never shared across mutually untrusted projects unless
  the implementation proves reset/isolation semantics.
- Project configuration cannot interpolate shell syntax.
- Logs and diagnostics cap stdout/stderr and escape control characters.
- A producer cannot select a module, global name, Core term, or theorem to apply.
- Reproducible/release mode pins producer identity, protocol version, and limits;
  otherwise external production is disabled or explicitly marked
  non-reproducible. Kernel checking remains mandatory in every mode.

## 14. Test matrix

### Checked metatheory

- pattern-normalization soundness and completeness for every `Pat` constructor;
- affine embedding of `L(0,{[2,0,0]})` into `L(0,{[1,0,0]})`;
- forged/missing/extra component embeddings, invalid target indexes, vector
  dimension mismatches, bad base offsets, bad period images, and silent
  truncation antibodies;
- `check_semilinear_inclusion_sound` and `checked_pattern_inclusion` type-check;
- valid single- and multi-hypothesis certificates;
- forged multiplier vectors;
- too-short and too-long witnesses;
- atom/valuation dimension mismatches;
- strict and non-strict relation negation;
- negative coefficients/constants;
- zero multipliers;
- accepted integer-only `2n = 1` divisibility certificate;
- invalid gcd claims, unsound cuts, missing split branches, out-of-range
  enumeration, and non-decreasing recursive measures;
- `check_lia_sound` and inversion theorem type-checking;
- Idris `rel=same` oracle replay.

### Normalizer/recognizer

- `PZero`/`POne`/`PAtom`/`PPlus`/`PTimes`/`PStar` normalize deterministically;
- normalization agrees with `Accepts` for generated small patterns/multisets;
- source/target component and period order is stable;
- alpha-equivalent goals normalize identically;
- stable variable order;
- equality hypotheses expand correctly;
- equality goals and nonlinear terms reject honestly;
- irrelevant or erased context entries are not smuggled into hypotheses;
- source decoration does not change the semantic problem hash.

### Producer

- affine-embedding search accepts the positive star-multiplicity probe;
- the reversed probe yields validated Parikh counterexample `[1,0,0]`;
- true inclusions outside the embedding fragment return
  `Unknown(:incomplete_procedure)` rather than false rejection or acceptance;
- certificate/checker agreement properties;
- model validation properties;
- deterministic replay;
- budget exhaustion and incomplete results;
- very large signed coefficients;
- deliberate bad producer antibodies.

### Protocol

- fragmented reads and multiple requests;
- timeout, crash, unavailable executable, and cancellation;
- wrong id/version/theory;
- duplicate/missing/unknown keys;
- trailing bytes and multiple responses;
- partial/extra/non-integer models;
- negative/oversized/wrong-length certificates;
- stdout/stderr/output-size limits;
- no orphan process after cancellation or compiler exit.

### End to end

- a real `Otp.Meta.MailboxPattern` semantic inclusion closes through
  normalization, producer, checked evidence, and the unchanged kernel;
- its reverse fails with the rich Parikh-counterexample diagnostic;
- a symbolic LIA goal outside lemma/positivity search closes;
- the same goal closes through the reference and mock external producers;
- a forged external certificate is rejected and the program fails;
- a valid countermodel produces the rich diagnostic;
- `Unknown`, timeout, and unavailable producer fail honestly;
- existing lemma/positivity results retain precedence;
- final Core is identical in meaning regardless of producer identity;
- cold stdlib compilation, full `mix test`, diagnostics coverage, Antigen
  completion, and oracle replay remain green.

### 14.1 Pinned external feasibility probes

The pinned sources, exact revisions, build commands, and fixtures live in
`docs/research/solver-checkers/README.md`. On 2026-07-22 all six selected
projects built locally. The two canonical smoke fixtures established:

- cvc5 CPC checked as `correct` in Ethos for rational and integer-only
  contradictions using ordinary `Cpc.eo`, without `CpcExpert.eo`;
- cvc5's integer CPC proof exposes `arith-int-eq-conflict`, polynomial
  normalization, evaluation, equality resolution, and transitivity;
- cvc5 Alethe checks in Carcara for rational LIA, while its integer proof needs
  an external RARE definition for `arith-int-eq-conflict`;
- veriT Alethe checks in Carcara for both fixtures when integer/real subtyping
  is enabled, with the integer `la_generic` step exposing rational
  coefficients; and
- Princess decides both fixtures, but its displayed proof preprocesses the tiny
  divisibility example directly to `false`, so it is an algorithm reference
  until a lower-level proof extraction seam is identified.

These observations select CPC/Ethos and veriT/Alethe as adapter probes; they do
not add either checker or native calculus to Cure's trust boundary.

## 15. Implementation phases and commits

Each phase lands independently green. Later phases must not weaken earlier
antibodies.

### Phase A — lock the OTP probes and semilinear representation

- Add paired positive/reversed star-multiplicity probes for
  `PStar(PTimes(TA,TA)) <= PStar(TA)`.
- Add `NatVector`, `LinearSet`, `SemiLinearSet`, `SemiAccepts`, deterministic
  pattern normalization, and both normalization-correctness directions.
- Gate: Cure/Idris `rel=same`, normalization snapshots, totality, axiom closure.

### Phase B — checked affine-embedding certificate

- Add `LinearEmbedding`, `SemiLinearInclusionCertificate`, exact shape checks,
  Boolean inversion, and `check_semilinear_inclusion_sound`.
- Compose the normalization bridge into `checked_pattern_inclusion` over the
  existing `Otp.Meta.MailboxPattern.Accepts` relation.
- Add forged target-index, dimension, offset, period-image, missing-component,
  truncation, and reversed-inclusion antibodies.
- Gate: the positive OTP probe checks in the unchanged kernel and the reverse
  probe is rejected with counterexample `[1,0,0]`.

### Phase C — OTP reference producer and vertical seam

- Add the deterministic affine-embedding search over normalized components.
- Register `:semilinear_inclusion`, build ordinary Cure evidence, and
  kernel-check it against the original pattern-inclusion goal.
- Add explicit invocation, rich diagnostics, completion, hover, deterministic
  replay, and validated counterexample reporting.
- Gate: one real `Otp.Meta.MailboxPattern` inclusion closes end to end from
  source obligation through producer, checked certificate, and kernel.

### Phase D — strict external protocol for the OTP slice

- Freeze JSON for semilinear problems, embeddings, models, and unknown results.
- Add supervised transport, limits, cancellation, cache rechecking, and a
  deterministic fixture adapter.
- Add a thin external producer probe; external output is translated to affine
  embeddings and discarded.

### Phase E — finish the general Farkas substrate

- Preserve the existing computation probes and add red validity/soundness
  probes.
- Finish integer algebra, vector semantics, shape, list, and negation lemmas.
- Add `ValidFarkasCertificate`, `check_lia`, inversion, and `check_lia_sound`.
- Add producer-neutral LIA quotation and deterministic bounded Farkas search.

### Phase F — broader quantifier-free Presburger certificates

- Add divisibility, normalization, cut, split, and bounded-enumeration nodes,
  their well-founded checker, inversion, and soundness proof.
- Require direct `2n = 1` acceptance.
- Implement cvc5 CPC and veriT Alethe probe adapters using the pinned research
  fixtures; translate native steps into canonical nodes and discard the native
  proof.

### Phase G — semilinear completeness extensions and full gates

- Add semilinear-cover certificates or checked quantified-Presburger
  elimination only when an OTP inclusion falls outside affine embedding.

### Phase H — final documentation and release gate

- Full tests, oracle, diagnostics coverage, Antigen, formatter/diff checks.
- Update language/proof/reference docs and configuration schema.
- Record supported theory, incompleteness boundary, limits, and threat model.

## 16. Definition of done

This effort is complete only when all of the following are simultaneously true:

1. The checked Cure metatheory proves affine semilinear inclusion, Farkas, and
   supported Presburger certificate checking sound without axioms or kernel
   changes.
2. The real OTP star-multiplicity inclusion closes end to end, while its
   reversed negative control produces the validated `[1,0,0]` counterexample.
3. Supported residual symbolic LIA obligations, including an integer-only
   divisibility contradiction, can be discharged end to end by generated
   certificates.
4. The same elaborator seam accepts certificates from both the reference
   producer and a strict external-process fixture.
5. A real external solver adapter can be selected without changing the checker,
   evidence builder, or kernel.
6. Forged, malformed, oversized, stale, and wrong-version certificates are
   rejected.
7. Models are independently validated before display.
8. Every timeout/failure/unsupported/incomplete path is `Unknown(reason)` or a
   structured error, never acceptance.
9. Diagnostics, completion, and hover meet the existing rich-language-service
   standard.
10. The full repository gates are green and the worktree contains no hidden
   generated artifacts or orphan processes.
11. Documentation says precisely: the producer is untrusted; Cure proves only
    what its checked certificate checker and unchanged kernel validate.

## 17. Deferred extensions

These require separate specs and do not block v1:

- proof-size optimizations and shared DAG encoding for large Presburger trees;
- complete quantified Presburger elimination beyond the semilinear-cover needs
  encountered by OTP;
- nonlinear arithmetic certificates;
- Alethe/native-proof replay as a separately registered checked theory;
- proof-producing countermodel/refutation evidence;
- runtime path narrowing into arithmetic hypotheses; and
- distributed/remote certificate generators.

None may broaden v1 by silently interpreting unsupported input as a valid
certificate.
