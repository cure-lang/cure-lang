# Dependent Effects and Stackless Flow for Cure

**Status:** Normative companion specification  
**Date:** 2026-07-21  
**Related design:** `docs/superpowers/2026-07-20-algebraic-effects.md`

## 1. Purpose

This document records the consequences for Cure of studying:

- Kura, Gaboardi, Sekiyama, and Unno, *A Category-Theoretic Framework for
  Dependent Effect Systems*, arXiv:2601.14846v1 (2026); and
- the requirement that Cure execute on both BEAM and a resource-constrained
  ESP32 flow/event-loop architecture.

The paper is a semantic framework for indexed graded monads and refinement
types. It is not an algebraic-handler implementation and does not prescribe
Cure's BEAM or ESP32 runtime. Its value is that it gives a precise vocabulary
for separating dependent values, computations, qualitative effects, and
quantitative guarantees.

No source keyword spelling is frozen by this document.

## 2. Executive decision

Cure should support direct-style algebraic effects and explicit monadic/flow
composition through one computation architecture.

The compiler should distinguish:

1. **values**, which belong to Cure's dependent theory and may appear in types,
   proofs, refinements, indices, and definitional equality;
2. **computations**, which produce values and carry effect information; and
3. **flow frames**, which are explicit continuation state used when a
   computation suspends across the ESP32 outer loop.

An asynchronous boundary does not require a native stack unwind. It does still
require a continuation representation. On ESP32 that continuation is a
defunctionalized, one-shot flow frame rather than a captured machine stack.

The initial implementation should therefore support stackless, one-shot,
compiler-generated flow continuations. Unrestricted multi-shot resumptions and
arbitrary dynamic handler capture are deferred.

## 3. What the paper contributes

The paper defines graded refinement value/computation types conceptually of the
form:

```text
value type        A
computation type  T_E A
```

where `E` is an indexed grade that may depend on value terms. It also keeps
dependent types and refinements dependent on values, not computations.

Its important rules for Cure are:

- computation results are not ordinary values merely because they have a
  result type;
- a computation's effect/grade may depend on already-available values;
- refinement predicates may establish relationships needed to compare or
  simplify dependent grades;
- effectful computations must not be executed while checking definitional
  equality or normalizing proofs;
- sequencing of dependent effects is difficult: the paper's initial `let`
  rule deliberately restricts the continuation grade from depending directly
  on the result of the preceding computation, recovering useful examples via
  refinement and subtyping.

These are directly relevant to Cure's dependently typed kernel. The paper does
not justify adding a runtime monad, allowing effectful terms in Core, or
executing handlers during kernel normalization.

## 4. Cure's three layers

### 4.1 Value layer

The value layer remains the trusted dependent theory:

```text
Γ ⊢v value : A
```

Values may be used in:

- dependent function and pair types;
- constructor indices;
- equality and refinement propositions;
- proofs and erased terms;
- kernel normalization and conversion, subject to existing termination and
  soundness rules.

Runtime effects cannot enter this layer by being wrapped in a constructor.

### 4.2 Computation layer

Computations use a separate judgment:

```text
Γ ⊢c computation : A ! ρ
```

`A` is the produced value type. `ρ` is a qualitative effect row. The source
language keeps direct-style sequencing and does not expose `Effect(A)` or
`Computation(A, ρ)` as ordinary values.

The compiler may use a monad-like composition internally or expose a library
monadic API, but that does not make the computation representation a trusted
Core value.

### 4.3 Flow layer

A computation containing a suspending operation lowers to an explicit flow
state:

```text
FlowFrame(
  handler_state,
  continuation_state,
  captured_values,
  resume_policy
)
```

The frame is a runtime/compiler artifact. It is not a proof term, dependent
index, or value-normalization object.

## 5. Effect rows and indexed guarantees

The qualitative row and quantitative/indexed information must remain distinct.

Examples of qualitative rows:

```text
{}
{Clock}
{Device.Sensor, Suspend}
{Send(typed_subject), Monitor}
```

Examples of later indexed/refinement information:

```text
cost(length(input))
events ≤ k
trace satisfies ProtocolState
latency ≤ deadline
```

The paper shows how a grade can depend on value terms. Cure may eventually
support a similar indexed layer, but it must not place arbitrary dependent
grades directly into the qualitative runtime row namespace.

A future computation type may therefore be conceptually understood as:

```text
Computation(result_type, effect_row, optional_index/refinement)
```

Only the first two components are required for the initial implementation. The
indexed component must be checked through value-level terms and constraints;
it must not require executing an effectful computation.

## 6. Suspension is a semantic property, not initially a keyword

Surface spelling is deliberately deferred. Internally, the initial design
requires a sealed primitive row marker, provisionally named `Suspend`.

For example:

```text
read_sensor : Unit -> Sample ! {Device.Sensor, Suspend}
```

Suspension propagates through calls and latent higher-order function types. A
caller of `read_sensor` is suspending even if the caller has no explicit
surface annotation.

`Suspend` means that execution may return to the outer scheduler/event loop
before producing the result. It does not mean that every operation is an
algebraic operation that user code may handle.

The scheduler/runtime owns the actual suspension boundary. User-defined
handlers may interpret abstract effects, but may not silently erase or fake a
sealed runtime suspension effect.

## 7. Monadic and algebraic styles

These styles should be two interfaces to one computation IR.

### Direct/algebraic style

Users write ordinary sequencing and handlers. The compiler tracks rows and
lowers local operations directly where possible.

### Explicit monadic/flow style

Users may explicitly construct and compose computations when they need to:

- store a pending operation;
- pass a computation as data at runtime;
- compose cancellation or timeout behavior;
- model an explicit device protocol;
- make the flow state visible;
- integrate with foreign code or a scheduler.

The explicit API must compile to the same computation IR. It must not create a
second incompatible effect system or require the trusted kernel to normalize
runtime computation values.

On BEAM, a computation can often lower to ordinary direct calls, processes,
messages, or compiler-supported continuation paths. On ESP32, a suspending
computation lowers to a flow frame and returns control to the outer loop.

## 8. Why stackless flow does not make handlers free

Returning to the outer loop removes the need to unwind a native stack, but a
handler that resumes later still needs to preserve:

- the continuation after the operation;
- captured local values;
- active handler state and nesting;
- success, failure, timeout, and cancellation paths;
- ownership of resources held across the suspension.

The ESP32 representation is therefore an explicit continuation, usually a
defunctionalized state machine. It avoids stack copying and native stack
unwinding, but it still consumes memory and requires a resumption protocol.

The initial ESP32 policy is:

- one-shot resumptions only;
- linear/affine treatment where resource ownership requires it;
- no unrestricted multi-shot continuation duplication;
- no handler capture whose lifetime cannot be represented in a flow frame;
- explicit bounds or diagnostics for frame size and suspension depth where the
  target can enforce them.

If an operation does not suspend, it should lower as an ordinary direct call.
If a handler never crosses a suspension boundary, it may be compiled locally
without a persistent flow frame.

## 9. Dependent sequencing restriction

The paper's conservative sequencing rule is a useful starting point for Cure.
Initially, the effect row/index of a continuation should not depend arbitrarily
on the result of a computation that may suspend.

Permitted early cases include:

- effect indices depending on input values already in the context;
- result refinements that allow a dependent index to be rewritten or bounded;
- pure computations whose values are safe for ordinary dependent substitution.

Deferred cases include:

- arbitrary runtime-result-dependent effect rows;
- executing a suspended computation to discover a type/index;
- effectful terms inside refinement predicates;
- dependent equality whose proof requires running a handler.

This restriction is not a permanent rejection of dependent effects. It is a
soundness and implementation boundary while Cure's computation IR, row solver,
and refinement reasoning mature.

## 10. Handler boundary

The first handler implementation should distinguish:

1. **abstract effects**, which user-defined handlers may interpret; and
2. **sealed runtime effects**, such as suspension, foreign calls, and selected
   OTP/device primitives, whose lowering is controlled by the compiler/runtime.

Handling an abstract effect can remove that label from the residual row only
when the handler's typing rules establish the removal. Handling must not erase
the fact that the handler itself suspends, allocates, calls foreign code, or
performs another sealed effect.

The handler IR must preserve the latent effects of callbacks, spawned
processes, and resumptions. A child process's effects are not automatically
charged to the spawning computation, but the child computation type must retain
them for deployment and supervision checks.

## 11. Kernel and normalization boundary

The following remain forbidden:

- effectful computations in dependent indices;
- effectful computations in proof bodies;
- foreign execution during normalization;
- handler execution during conversion;
- treating `Effect(A)` as a safe escape hatch into the value universe;
- using qualitative rows as proofs of exact operation counts;
- using an indexed grade as evidence without a checked refinement/certificate.

The paper's categorical semantics can justify soundness of an indexed layer,
but the Cure kernel still needs a concrete trusted boundary, termination story,
erasure story, and solver/certificate policy.

## 12. Proposed implementation sequence

1. Freeze the value/computation judgment split and remove assumptions that an
   opaque effect container is a value.
2. Represent qualitative rows and row variables independently of indexed
   quantitative grades.
3. Add latent effect propagation for higher-order functions and callbacks.
4. Add the computation IR shared by direct-style and explicit flow/monadic APIs.
5. Add a sealed internal `Suspend` effect and propagate it through inference.
6. Lower a single suspending primitive to an ESP32-style one-shot flow frame.
7. Lower the same computation to direct BEAM behavior and compare semantics.
8. Add abstract handlers with one-shot linear resumptions.
9. Add refinement/index constraints for bounded cost, trace, and protocol facts.
10. Add deployment checks for child-process and callback effect closure.

Every step requires the existing kernel, Antigen, compiler, BEAM, and AtomVM
verification gates. ESP32 flow verification additionally requires a real
device-observed suspension/resumption test.

## 13. Open questions for the language comparison phase

- Which reference languages make suspension/async effects explicit versus
  inferring them from operation signatures?
- Which handler implementations retain continuations across event-loop turns,
  and how are those continuations represented?
- What optimizations eliminate frames for non-suspending handlers?
- How do higher-order effect systems track callbacks that may suspend?
- Which systems enforce one-shot or linear resumption use?
- What evidence exists for bounded memory behavior on embedded targets?
- How should Cure expose explicit flow construction without requiring users to
  understand compiler-generated continuation frames?

These questions are intentionally left for the next phase: studying the
acquired Koka, Eff, Effekt, Frank, Unison, Links, OCaml, Idris2, Granule, and
Racket implementations.

## 14. Paper review log

### 14.1 Kura et al., *A Category-Theoretic Framework for Dependent Effect Systems*

**Reviewed:** 2026-07-21  
**Local source:** `algebraic-effects/papers/dependent-effect-systems.pdf`

The paper's concrete calculus is fine-grain call-by-value. Its value types may
depend on values, while computation types have the form `T_E A`; computation
terms are never used as arguments to refinement predicates. The dependent grade
`E` is built from a value-indexed basic-effect map and a monoidal composition,
and subeffecting is discharged semantically in the refinement context.

The most important implementation constraint is its initial sequencing rule:
the continuation grade in `let x <- M in N` may not depend directly on the
fresh computation result `x`. The paper demonstrates useful dependent costs by
using result refinements and subtyping to rewrite the later grade instead. Cure
should adopt this as an initial restriction for suspending computations rather
than attempting arbitrary result-dependent effect inference immediately.

The paper proves soundness by interpreting the indexed system as a lifting of
graded monadic semantics over a refinement fibration. This supports Cure's
three-layer architecture, but does not require a runtime monad or permit
effectful normalization. It also distinguishes the qualitative composition of
grades from the value predicates used to establish bounds, reinforcing Cure's
separation of effect rows from later cost, trace, and protocol indices.

### 14.2 Kura, *On Complete Categorical Semantics for Effect Handlers*

**Reviewed:** 2026-07-21  
**Local source:** `algebraic-effects/papers/complete-categorical-semantics-effect-handlers.pdf`

This paper studies a simply typed deep-handler calculus with computation types
`A!Σ` and handler types `Σ ⇒ C`. Its central result is that sound and complete
models are more general than free monads: the same handler calculus admits both
free-model interpretations and CPS/continuation-style interpretations. With
equational operation theories, only handlers respecting those equations are
valid.

For Cure, this strengthens the one-IR decision. A monad-like composition API,
a direct handler semantics, and a CPS/defunctionalized ESP32 lowering need not
be competing source features. They can be distinct models or compiler
lowerings of one typed computation calculus. It also warns against identifying
the semantic computation type with a particular runtime representation.

The calculus is deliberately simply typed and omits Cure's dependent and
higher-order concerns, so it does not solve the kernel integration problem. It
does, however, give Cure a useful semantic test: any proposed handler lowering
must preserve the handler equations, and any sealed primitive with equations
must restrict handlers to those that respect them. This applies directly to
the boundary between user handlers and sealed scheduler/device operations.

### 14.3 Kawamata et al., *Answer Refinement Modification*

**Reviewed:** 2026-07-21  
**Local source:** `algebraic-effects/papers/answer-refinement-modification.pdf`

This paper makes the continuation cost of handlers concrete. An operation
captures the remaining computation as a delimited continuation, and the
refinement type of that continuation must describe both the value it accepts
and the answer/refinement state it produces. Answer refinement modification
(ARM) tracks how operation handling changes refinements and the order of effects;
answer type modification (ATM) handles the corresponding type-level change.

The paper's implementation discussion is especially relevant to ESP32: a
scheduler may keep suspended continuations in an imperative queue, and some
computational effects are better treated as primitive operations for efficiency
even when they could theoretically be encoded as handlers. This supports Cure's
sealed runtime effects and explicit flow-frame storage rather than requiring
every device operation to be represented as a user-level algebraic handler.

It also presents a bidirectionally type-preserving CPS translation to a pure
target. The translation is useful as a verification and fallback lowering
strategy, but requires additional source annotations, can produce harder error
messages, and may require higher-order predicate polymorphism. Cure should
therefore retain direct source-level checking and use CPS/defunctionalization as
an internal target or proof cross-check, not as the only user-visible type
checking path.

Finally, the paper identifies recursive computation types, effect polymorphism,
type-polymorphic operations, and deep versus shallow handlers as real extension
points. Cure's initial one-shot flow design should avoid claiming full support
for these until their recursive continuation and resource behavior are typed.

### 14.4 van den Berg and Schrijvers, *A Framework for Higher-Order Effects & Handlers*

**Reviewed:** 2026-07-21  
**Local source:** `algebraic-effects/papers/higher-order-effects-handlers-framework.pdf`

This paper draws the boundary that ordinary algebraic effects cannot cross:
algebraic operations commute with sequencing and expose an operation result plus
a continuation, but higher-order effects inspect or manipulate an internal
computation. Scoped effects distinguish in-scope from out-of-scope computation;
parallel effects execute an internal computation in parallel; latent effects
defer one; bracketing effects manage resource lifetimes.

The generic higher-order signature places those internal computations in the
effect syntax and gives them an interpreter. This is directly relevant to Cure
because callbacks, actor children, supervisor bodies, deferred device work,
and resource brackets are not adequately described by a flat row of operation
names. They require latent computation types in the computation IR.

The paper also gives a precise reason not to force all effects through a single
ordinary algebraic-handler encoding: non-algebraic operations can lose
modularity when encoded naively as handlers. Cure should therefore classify
effects as first-order algebraic, higher-order/scoped, or sealed runtime
primitives while keeping them in one typed IR. `Suspend` belongs to the latter
two categories depending on whether it owns a latent continuation.

The paper's generic free-monad implementation is useful as a semantic model,
but not as a requirement for runtime allocation. On ESP32, higher-order
signatures should lower to explicit flow-frame fields and scheduler actions;
the internal computation must not become an opaque dynamically interpreted tree.

### 14.5 van der Rest et al., *Handling Higher-Order Effects*

**Reviewed:** 2026-07-21  
**Local source:** `algebraic-effects/papers/handling-higher-order-effects.pdf`

This paper introduces a calculus in which computations can be passed as
suspended values to higher-order handlers. Its key semantic choice is that
subcomputations are delayed until the handler explicitly forces them, rather
than being eagerly pre-handled by every surrounding handler. That distinction
is a useful model for Cure flows: a pending device/action computation should
carry its latent effect context until the scheduler or owning handler runs it.

The paper also formalizes separation of concerns between handlers. Its central
practical observation is that handlers using their continuation affinely—at
most once—tend to preserve separation, while handlers that resume a continuation
multiple times, such as nondeterminism, introduce interaction and duplication.
This gives independent semantic support for Cure's initial one-shot/linear
resumption policy on ESP32, beyond merely treating it as an optimization.

The design must still permit explicit interaction when required: state plus
exception handling, cancellation, timeout, and supervision can intentionally
observe one another. Cure should encode this interaction in handler/flow
types, not assume that handler order is always interchangeable. A future
implementation should test a separation-of-concerns law for handlers that are
declared independent and reject or require an explicit interaction witness for
handlers that are not.

### 14.6 Lindley, McBride, and McLaughlin, *Do Be Do Be Do*

**Reviewed:** 2026-07-21  
**Local source:** `algebraic-effects/papers/do-be-do-be-do-frank.pdf`

Frank is the closest source-language comparison in this reading set. It
separates values from computations using suspended computation types, tracks
available abilities through a bidirectional type system, and treats ordinary
function/operator application as the mechanism for passing and handling
computations. Its effect polymorphism is ambient: operators receive an ability
and offer it to their computation arguments, rather than every source term
explicitly accumulating effect variables.

Frank elaborates its direct language into a simpler Core language of ordinary
functions, case expressions, and unary handlers. This is a strong precedent for
Cure's computation IR and for keeping direct-style syntax independent from the
runtime representation. It also makes the deep/shallow handler choice explicit:
Frank uses shallow continuations and explicit recursion, while deep handlers
implicitly reinstall the handler on resumption.

Frank's suspended computations are syntactically value-like, but Cure must not
copy that choice into the trusted dependent value universe. Cure may offer a
runtime/flow computation object for explicit monadic composition, storage, or
scheduling, but it must be marked as a computation-layer object and remain
unavailable to proofs, indices, conversion, and kernel normalization.

The paper's implementation notes reinforce several Cure priorities: avoid
allocating a continuation when a handler invokes it exactly once; use linear,
affine, or relevant typing for continuation and protocol honesty; index
interfaces over session state when communication protocols matter; and treat
dynamic resource allocation as a separate hard problem. These map directly to
one-shot ESP32 frames, typed actor protocols, and future ownership/resource
effects.

## 15. BEAM backend target

### 15.1 Recommendation

For the BEAM backend, Cure should lower to Core Erlang rather than directly to
Erlang abstract forms. The recommended path is:

```text
Cure AST
  → Cure value/computation IR
  → Cure Flow/control IR where required
  → Core Erlang
  → OTP compiler/backend
  → BEAM code
```

Core Erlang is a better semantic boundary than Erlang abstract forms because it
makes evaluation order, closures, pattern matching, recursion, process
operations, and control flow more explicit. The machine-checked formalisation
of concurrent Core Erlang provides a plausible future target for a verified
Cure-to-Core-Erlang translation, including a frame-stack semantics and
properties such as determinism and bisimulation for its supported subset.
The reference clone is `algebraic-effects/core-erlang-formalization/` at
`4a59339cdc5c9cff3a144732397d56dfa7378631`; it is a Rocq 9.1 development with
explicit `FrameStack/Frames.v`, concurrent process/node semantics, equivalence
proofs, and an extracted interpreter.

This does not mean that Core Erlang replaces Cure's computation or Flow IR.
Core Erlang has no representation of Cure's dependent proofs, effect rows,
latent callback effects, one-shot resumption guarantees, or ESP32 frame bounds.
Those facts must be discharged before the Core Erlang boundary and erased or
compiled into explicit runtime state as appropriate.

### 15.2 Core Erlang versus the OTP `cerl` API

The target should be specified as a versioned Core Erlang subset/encoder, not as
an assumption that the OTP `cerl` internal data structures are stable. The
official `cerl` documentation describes the module as an internal compiler API,
with representations subject to change and type-correctness largely assumed of
callers. Cure should isolate any OTP-specific constructor adapter behind a
backend module and test the emitted Core Erlang through the installed OTP
compiler.

The verified subset should initially cover the constructs Cure actually emits:
modules, functions, calls, `let`/`letrec`, `case`, `receive`, literals, tuples,
maps/binaries as needed, process primitives, and explicit flow-state dispatch.
Unsupported OTP features must fail closed rather than being fabricated through
opaque escape nodes.

### 15.3 Why not emit BEAM bytecode first

Direct BEAM bytecode emission would couple Cure to a lower-level, versioned
object format, instruction set, loader/validator contract, literal table,
exception representation, and register/stack conventions before Cure has a
verified semantic backend. It would also make a future C backend share less
infrastructure with the BEAM path.

The OTP compiler documentation explicitly treats Core input as a compiler
boundary while describing lower-level assembly/object representations as
internal or undocumented. Therefore direct bytecode generation should be a
later, separately justified backend—not the first way to avoid abstract forms.

### 15.4 Proof boundary

A future metatheory should aim first to prove:

```text
Cure computation/Flow IR semantics
  ≈
Core Erlang semantics of the generated program
```

That proof establishes Cure's translation correctness relative to Core Erlang.
It does not by itself prove the OTP Core-Erlang-to-BEAM compiler correct, nor
does it prove AtomVM compatibility. Those require separate compiler/runtime
validation or a verified backend boundary.

For restricted C/ESP32 targets, the same Cure computation/Flow IR should lower
directly to C state machines and scheduler calls. Core Erlang remains the BEAM
backend target, not the universal target IR.

## 16. Prior art for Cure Flow IR

### 16.1 Terminology and conclusion

The exact phrase “flow IR” is not a standard name for one established compiler
representation. The design is, however, a direct combination of several
well-established techniques:

```text
CPS conversion
  → defunctionalized continuations
  → explicit frames/abstract machine
  → target-specific state-machine lowering
```

Reynolds-style CPS conversion followed by defunctionalization explains how a
recursive interpreter or direct-style program can become an abstract machine
whose continuations are represented by a finite family of data constructors.
This is the theoretical foundation for Cure's explicit flow frames, rather
than an invention of a new control-flow principle. See [Continuation-Passing
Style, Defunctionalization, Accumulations, and Associativity](https://arxiv.org/abs/2111.10413).

The Cure-specific contribution is to make those continuation constructors
typed with computation effects, dependent-kernel boundaries, ownership or
one-shot guarantees, and deployment constraints. “Flow IR” is therefore a
useful Cure name, but the implementation documentation should also call it a
**typed defunctionalized computation/flow IR** so its relationship to prior
work is unambiguous.

### 16.2 Closest implementation and semantics precedents

The strongest directly relevant precedents are:

- The sequential Core Erlang frame-stack semantics models evaluation with
  explicit frames and proves equivalence properties over that machine. See [A
  Frame Stack Semantics for Sequential Core Erlang](https://arxiv.org/abs/2308.12403).
- The concurrent Core Erlang formalisation extends the frame-stack approach to
  actors, processes, and mailboxes, with determinism/confluence results and
  bisimulation reasoning. See [A Formalisation of Core Erlang, a Concurrent
  Actor Language](https://arxiv.org/abs/2311.10482).
- Effect-handler verification work uses defunctionalization to represent the
  continuations exposed by handlers, demonstrating that handler control can be
  made explicit for automated reasoning. See [A Framework for the Automated
  Verification of Algebraic Effects and Handlers](https://arxiv.org/abs/2302.01265).
- WasmFX treats typed continuation creation, suspension, and resumption as a
  low-level target interface for async/await, generators, lightweight threads,
  and effect handlers. See [Continuing WebAssembly with Effect
  Handlers](https://arxiv.org/abs/2308.08347).
- Frank elaborates a direct-style effect language into a smaller core language
  containing functions, cases, and handlers. See [Do Be Do Be
  Do](https://arxiv.org/abs/1611.09259).

These precedents support the architecture but do not provide a ready-made
Flow IR for Cure. Core Erlang's frames are an execution semantics, WasmFX is a
runtime target extension, and Frank's Core language does not carry Cure's
dependent or ownership information. Cure must retain its own typed IR until
those properties have been checked and only then erase or compile them into
runtime state.

### 16.3 Definition of the Cure Flow IR

The first Flow IR should be an explicit control representation, not an opaque
runtime `Effect(A)` container and not a general-purpose syntax tree. Its
minimum conceptual entities are:

```text
FlowProgram
  - entry state
  - state definitions
  - effect/operation transitions
  - terminal return and failure transitions

FlowState
  - state identifier
  - captured value fields
  - current computation step
  - handler/environment fields where permitted
  - next-state transitions

FlowFrame
  - continuation state identifier
  - captured values
  - expected result type
  - remaining effect obligations
  - one-shot ownership status
```

The exact data structures remain an implementation task, but the invariants
are fixed now:

1. Every suspended continuation has an explicit frame or an equivalent
   statically known state transition.
2. A frame's captured fields are typed independently of the dependent value
   kernel; effectful computations cannot enter definitional equality or proof
   normalization.
3. A first implementation consumes each resumption at most once. Multi-shot
   cloning is rejected until continuation duplication, resource ownership, and
   dependent answer-state changes have a formal account.
4. The same Computation IR can lower either to direct BEAM calls, explicit
   Core Erlang flow dispatch, or a C/ESP32 scheduler loop.
5. The Flow IR is introduced only where a computation can suspend, cross a
   handler/process boundary, or require a restricted-runtime scheduler. Pure
   straight-line code should not be converted into frames unnecessarily.

### 16.4 Consequence for the implementation order

The research changes the order slightly: Flow IR is the first major compiler
IR, but it must follow the typing representation that gives it meaning.
Implementation should proceed as follows:

1. Define value types versus computation types and effect rows.
2. Define the Computation IR and its typing judgments.
3. Add CPS/continuation conversion and defunctionalization into Flow IR.
4. Verify one pure/effectful example pair and one suspension/resumption pair.
5. Add actor/process/mailbox transitions and preserve latent effects.
6. Lower Flow IR to Core Erlang for BEAM and to an explicit scheduler loop for
   C/ESP32.
7. Add abstract handlers and one-shot resumptions after primitive flow
   execution is stable.

This makes the Flow IR the shared semantic/control boundary for BEAM and
restricted targets, while leaving the dependent kernel responsible only for
values, types, proofs, and certified static effect/flow facts.
