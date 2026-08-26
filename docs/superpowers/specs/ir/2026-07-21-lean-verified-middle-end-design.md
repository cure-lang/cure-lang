# Lean-Verified Cure Middle-End

**Status:** Design specification  
**Date:** 2026-07-21  
**Related specifications:**

- `2026-07-21-dependent-effects-and-stackless-flow-design.md`
- `2026-07-21-multiple-irs-architecture-design.md`

## 1. Decision

Cure will place a Lean-implemented and Lean-checked middle-end between the
existing front end and the target backends. The first version will accept a
versioned canonical Cure Core representation over JSON, validate it inside
Lean, lower it through the typed Cure IRs, and emit a verified Core Erlang AST.

```text
existing Cure parser/elaborator
  → canonical Cure Core JSON
  → Lean validation
  → Typed Value/Computation IR
  → Handler/Continuation IR
  → Flow IR
  → Concurrency/Capability IR
       ├→ verified Core Erlang AST → Core Erlang text → OTP compiler/backend
       └→ C/ESP32 machine IR
```

This is a verified middle-end, not initially a fully verified compiler. The
first phase proves the transformations after canonical Core has been accepted.
The correctness of parsing, macro expansion, name resolution, and elaboration
remains outside the Lean proof boundary until those components are moved into
Cure or Lean, or emit checkable certificates.

Lean is selected over Idris or Agda for this role because it combines dependent
types, an efficient native compiler, a mature theorem-proving ecosystem,
automation, and practical JSON/process integration. Idris remains useful as a
language-design comparison; Agda remains useful for literate metatheory. They
are not required for the production middle-end.

## 2. Goals

The Lean middle-end must:

- provide executable implementations of Cure's semantic IRs;
- make value/computation separation explicit;
- check qualitative effect rows before target lowering;
- preserve dependent value information until the relevant checks complete;
- represent handlers and continuations with explicit ownership policy;
- defunctionalize escaping continuations into typed Flow states;
- preserve latent effects through actors, callbacks, supervisors, and foreign
  operations;
- construct only well-formed Core Erlang target terms;
- prove semantic preservation for the supported fragment;
- expose a stable process boundary usable by the existing compiler;
- leave a path for eventual Cure self-hosting.

## 3. Non-goals

The first version will not:

- parse all Cure source syntax inside Lean;
- prove the existing Cure parser, macro system, or elaborator correct;
- formalize all of Erlang/OTP;
- prove the OTP Core-Erlang-to-BEAM compiler correct;
- support unrestricted multi-shot continuations;
- support arbitrary effectful terms inside dependent indices;
- make JSON the permanent internal representation between every pass;
- replace the existing compiler front end or all backends immediately;
- emit direct BEAM bytecode.

JSON is a boundary and debugging format. Lean datatypes are the internal IR
representation.

## 4. Trust boundary

### 4.1 Initial trust model

The initial pipeline has the following trust profile:

```text
source parser/macro expander/elaborator       trusted but not yet verified
        ↓
canonical Core JSON validator                  checked by Lean
        ↓
Lean IR transformations and proofs            checked by Lean kernel
        ↓
Core Erlang AST and well-formedness proof      checked by Lean kernel
        ↓
OTP Core Erlang compiler                       trusted external component
```

For `cure-core-0.1`, the Lean proof begins at a structurally and simply-typed
validated canonical Core term. It proves that the
Lean middle-end preserves the semantics of that term through the supported IRs
and constructs a target term in the formalized Core Erlang subset.

The existing Cure dependent kernel remains a separate trust assumption in this
initial slice. Full independent checking of Cure dependent conversion is a
later trust-reduction stage, not an implicit consequence of encoding terms in
Lean.

This must be stated explicitly in diagnostics and release documentation. A
successful Lean proof must not be advertised as proof that the original Cure
source was elaborated correctly until the front-end boundary is also checked.

### 4.2 Future trust reduction

Trust can be reduced in stages:

1. Lean validates canonical Core independently of the host compiler's claims.
2. The host elaborator emits a typed Core certificate checked by Lean.
3. Canonical Core elaboration is implemented in Cure or Lean.
4. Macro expansion and name resolution are moved into the checked pipeline.
5. A Cure compiler is bootstrapped and its generated canonical Core is checked
   by the same Lean boundary.

The Lean kernel, the Lean compiler used to execute the checker, and the OTP
backend remain separate trust assumptions unless independently formalized.

## 5. Canonical Cure Core JSON

### 5.1 Purpose

Canonical Core JSON is a stable interchange format between the current Cure
front end and Lean. It is not the source AST and must not contain unresolved
syntax, macros, implicit elaboration choices, or arbitrary backend escape
nodes.

The format must be versioned:

```json
{
  "schema": "cure-core-0.1",
  "module": "Example",
  "data": [],
  "effects": [],
  "definitions": [],
  "concurrency": [],
  "capabilities": [],
  "metadata": {}
}
```

Unknown schema versions and unknown constructors are rejected. Decoding must
be total: malformed input produces a structured error, never a partial term.

### 5.2 Binding representation

Local binders should use de Bruijn indices or an equivalent explicitly scoped
representation. Global names use validated module-qualified identifiers.
Source names may be retained only as metadata.

This prevents JSON names from changing binding semantics and makes substitution,
weakening, and alpha-equivalence explicit in Lean.

### 5.3 Required canonical nodes

The first schema supports:

```text
Values:
  variable, literal, constructor, pair, lambda, recursive function,
  pure primitive, proof/reference metadata

Computations:
  return, let, apply, pure operation, case, primitive effect,
  exception/failure, suspension, handler, concurrency operation

Types:
  universe/base, data type, dependent pair, dependent function,
  computation type, result type, effect row, refinement summary

Effects:
  primitive, abstract, higher-order, suspend, concurrency, foreign

Actors/deployment:
  process declaration, mailbox schema, spawn target, callback,
  supervision relation, required capability
```

The JSON schema must distinguish values from computations structurally. A
computation cannot appear where a value is expected without an explicit
computation-layer wrapper whose type is checked by Lean.

### 5.4 Proof and metadata fields

JSON may contain:

- source spans and generated-origin IDs;
- declared result types and effect rows;
- refinement summaries;
- elaborator fingerprints;
- optional proof/certificate payloads in a future schema.

Lean must not trust declared types or rows merely because they are present in
JSON. It reconstructs or validates them. Metadata is never allowed to alter
kernel reduction or runtime behavior.

## 6. Lean package structure

The implementation should be a standalone Lean project, for example:

```text
cure-verified/
  lakefile.lean
  CureVerified/
    Json.lean
    Syntax.lean
    Types.lean
    Effects.lean
    ValueIR.lean
    ComputationIR.lean
    HandlerIR.lean
    FlowIR.lean
    ConcurrencyIR.lean
    LowCure.lean
    CoreErlang.lean
    Semantics/
      Value.lean
      Computation.lean
      Flow.lean
      Actor.lean
      CoreErlang.lean
    Lowering/
      CoreToComputation.lean
      ComputationToHandler.lean
      HandlerToFlow.lean
      FlowToActor.lean
      ActorToCoreErlang.lean
    Proofs/
      TypePreservation.lean
      EffectPreservation.lean
      FlowCorrectness.lean
      LowCureCorrectness.lean
      CoreErlangCorrectness.lean
    Main.lean
```

The package must expose two interfaces:

```text
validate : JSON → Result ValidatedCore Diagnostic
compile  : ValidatedCore → Result (CoreErlang × Certificate) Diagnostic
```

The executable command-line wrapper reads JSON from a file or stdin and writes
Core Erlang plus diagnostics. Internal passes operate on Lean values, not JSON.

## 7. Lean representations and proof indices

The exact Lean syntax is implementation-specific, but the types must encode
the critical invariants rather than relying solely on predicates checked by
convention.

### 7.1 Values and computations

Conceptually:

```lean
inductive Value where
  | var       : BVar → Value
  | literal   : Literal → Value
  | ctor      : CtorId → Array Value → Value
  | lambda    : ValueType → Computation → Value
  | pair      : Value → Value → Value

inductive Computation where
  | ret       : Value → Computation
  | let1      : Computation → Computation → Computation
  | apply     : Value → Array Value → Computation
  | pureOp    : PureOp → Array Value → Computation
  | perform   : Operation → Array Value → Computation
  | case      : Value → Array Branch → Computation
  | suspend   : SuspendOp → Array Value → Continuation → Computation
  | handle    : Computation → Handler → Computation
```

Typing is indexed or accompanied by an explicit derivation:

```lean
HasValue      Γ v A
HasComputation Γ c A ρ ι
```

The representation strategy is fixed for the first implementation:

```text
raw decoded syntax
  → extrinsic validator producing a checked derivation
  → validated Core paired with its derivation
  → intrinsically constrained Flow transitions where ownership matters
```

Large mutually recursive terms are therefore easy to decode, while the
lowering APIs cannot consume raw syntax. Flow states and continuation ownership
must be represented by proof-carrying or intrinsically constrained structures;
ordinary value/computation nodes may use explicit derivations.

### 7.2 Effect rows

Rows must distinguish known labels, an optional open variable, and sealed
runtime labels:

```text
Row := { labels : Finset EffectLabel, tail : Option EffectVar }
```

Row operations must provide checked results for union, inclusion, subtraction
by a handler, and closure. Sealed effects cannot be removed by ordinary row
subtraction.

Indexed/refinement summaries are separate from qualitative rows:

```text
ComputationType := result : ValueType
                × row    : EffectRow
                × index  : Optional EffectIndex
```

This preserves the dependent-effects paper's distinction between qualitative
effects and value-indexed quantitative/refinement information.

### 7.3 Continuation ownership

Continuation ownership is explicit:

```text
Ownership := oneShot | affine | unrestricted
```

The first compiler accepts only `oneShot` or statically safe affine uses.
Continuation-consuming operations should return a state that no longer owns
the consumed continuation. This makes double resume unrepresentable in the
checked Flow IR where possible and dynamically diagnosable otherwise.

## 8. The Lean IR sequence

### 8.1 Typed Value/Computation IR

This is the first semantic IR after validation. It makes evaluation order,
result types, effect rows, and indexed summaries explicit.

Required operations:

```text
return
let
apply
pure operation
case
perform primitive/abstract effect
raise/fail
suspend
handle
concurrency operation
```

Optimisations allowed here:

- pure constant folding;
- pure beta reduction where it does not cross an effect boundary;
- redundant `let` elimination;
- pure operation fusion;
- dead pure computation removal;
- row normalization and duplicate-label removal.

No optimization may remove a sealed effect, change evaluation order, or
normalize an effectful computation in the dependent kernel.

### 8.2 Handler/Continuation IR

This IR makes handler scopes, operation clauses, return clauses, answer types,
captures, and ownership explicit. It is the last IR that may represent a
continuation as a higher-order Lean function.

Required checks:

- operation clause completeness and type compatibility;
- handled versus unhandled row calculation;
- deep/shallow/scoped behavior;
- answer-type modification;
- continuation capture typing;
- state/resource protocol preconditions and postconditions;
- one-shot/affine use.

The handler verification paper's client/server protocol distinction motivates
retaining operation preconditions, postconditions, and modified-resource sets
in this IR. See [A Framework for the Automated Verification of Algebraic
Effects and Handlers](https://arxiv.org/abs/2302.01265).

### 8.3 Defunctionalized Flow IR

Flow IR is a first-order state machine generated from typed continuation sites.
It uses explicit state IDs and capture layouts rather than opaque continuation
closures.

Conceptual Lean representation:

```lean
structure FlowState where
  id          : StateId
  captures    : Array CaptureField
  step        : FlowStep
  resultType  : ValueType
  effectRow   : EffectRow

inductive FlowStep where
  | return    : ValueRef → FlowStep
  | call      : FunctionId → Array ValueRef → StateId → Optional StateId → FlowStep
  | perform   : Operation → Array ValueRef → StateId → Optional StateId → ControlMode → FlowStep
  | branch    : ValueRef → Array (Pattern × StateId) → FlowStep
  | concurrency : ConcurrencyAction → StateId → FlowStep
  | abort     : Failure → FlowStep
```

Each generated state must have a proven capture layout and a transition proof:

```text
FlowTransitionCorrect : source continuation invocation
                      ≈ generated state transition
```

The CPS/defunctionalization paper supports this construction, while the
WasmFX paper supports the explicit single-shot continuation policy. See
[CPS, Defunctionalization, Accumulations, and
Associativity](https://arxiv.org/abs/2111.10413) and [Continuing WebAssembly
with Effect Handlers](https://arxiv.org/abs/2308.08347).

Flow optimisations include continuation-site specialization, frame-field
liveness, state merging, tail-transition elimination, and direct-call lowering
when no continuation escapes. These are valid only after the corresponding
semantic and ownership proofs are available.

### 8.4 Concurrency/Capability IR

Concurrency/Capability IR makes process topology, mailboxes, scheduler ownership,
links, monitors, supervision, callbacks, foreign capabilities, and deployment
effect closure explicit.

It must preserve the latent effect row of every callback, child process, and
supervisor body. Spawning cannot turn a computation into an untracked opaque
value.

The concurrent Core Erlang formalisation provides the semantic reference for
separating process-local frames from node-level actions and mailbox state. See
[A Formalisation of Core Erlang, a Concurrent Actor
Language](https://arxiv.org/abs/2311.10482).

### 8.5 Core Erlang AST

Lean constructs a typed subset of Core Erlang directly, rather than relying on
Erlang abstract-form constructors as the semantic representation.

The first target subset contains:

```text
modules
functions
calls
let/letrec
case
receive
literals
tuples
maps/binaries as required
process primitives
explicit Flow-state dispatch
```

The target datatype must distinguish well-formed terms from raw terms:

```lean
CoreTerm
WellFormedCore : CoreTerm → Prop
```

The compiler returns a target accompanied by a proof or certificate of target
well-formedness. Core Erlang's formalisation in the `harp-project` repository
is the primary external reference, but its supported subset and semantic
assumptions must be recorded explicitly rather than silently generalized.

## 9. Semantic layers and proof obligations

Each IR has both an executable evaluator and a semantic relation, at least for
the initial fragment.

```text
Core semantics
  → Computation semantics
  → Handler/Continuation semantics
  → Flow machine semantics
  → Actor/network semantics
  → Core Erlang semantics
```

The minimum theorem set is:

### 9.1 Validation soundness

If JSON validation succeeds, the resulting canonical Core term has:

- valid bindings;
- well-formed types;
- well-formed effect rows;
- no runtime macro constructs;
- no unclassified foreign operations.

### 9.2 Type preservation

Each lowering preserves result types and the required effect/index summaries:

```text
Γ ⊢ c : A ! ρ [ι]
⇒
Γ' ⊢ lower(c) : A' ! ρ' [ι']
```

with explicit relations for representation changes and permitted erasure.

### 9.3 Effect preservation

The lowered term cannot perform an effect absent from the source row, and a
source effect cannot disappear unless a checked handler or target capability
discharges it.

### 9.4 Defunctionalization correctness

For every continuation site, executing the source continuation is related to
executing the generated Flow state with its captured fields.

### 9.5 Ownership preservation

One-shot continuations are consumed at most once. Resource-bearing frames have
an explicit completion, abort, or cleanup path.

### 9.6 Concurrency preservation

The Concurrency/Capability lowering preserves observable sends, receives, spawn,
exit, link, monitor, and supervision actions under the chosen scheduler and
mailbox model.

### 9.7 Core Erlang correctness

For the supported target fragment:

```text
⟦source canonical Core⟧
  ≈ ⟦Lean-generated Core Erlang⟧
```

The relation may initially be contextual equivalence, trace equivalence, or a
simulation relation appropriate to the sequential subset. Concurrent process
code should use an explicitly stated bisimulation or weak-bisimulation
relation. The semantics must represent divergence and blocking: a terminating
big-step result is insufficient for recursive Flow machines, blocked receives,
and long-running processes. The initial model uses finite traces for completed
or failed runs and coinductive/infinite traces for divergence and scheduler
behavior. This does not prove OTP's backend correct.

## 10. JSON and diagnostics contract

The command-line tool must produce machine-readable diagnostics:

```json
{
  "ok": false,
  "phase": "flow-lowering",
  "code": "CURE_CONTINUATION_DOUBLE_USE",
  "message": "one-shot continuation is resumed twice",
  "spans": [ ... ],
  "related": [ ... ]
}
```

Diagnostics must identify the IR phase, source-origin IDs, effect labels,
continuation/state IDs, and the failing invariant. Lean proof failures must be
converted into stable compiler diagnostics rather than exposed as raw tactic
traces.

The JSON protocol must support:

- schema version negotiation;
- deterministic output for reproducible builds;
- a `--check-only` mode;
- a `--dump-ir <phase>` mode;
- a `--emit-core-erlang` mode;
- a `--emit-certificate` mode;
- bounded resource/depth limits for hostile or malformed input.

## 11. Host compiler integration

Initially, the existing Cure compiler invokes the Lean executable as a separate
process. It must not reimplement Lean's transformations in parallel.

```text
host compiler:
  parse → elaborate → emit canonical Core JSON

Lean process:
  validate → lower → prove/check → emit Core Erlang
```

The host compiler retains source diagnostics and project orchestration. Lean
owns semantic IR dumps and transformation diagnostics. Every phase boundary
must have golden fixtures so the two processes can be tested independently.

The first integration should use files or stdin/stdout for simplicity. An
in-process FFI or library embedding can be considered after the IR schema and
diagnostics stabilize.

## 12. Core Erlang formalisation strategy

The existing Core Erlang formalisation is in Rocq and provides a valuable
reference for syntax, sequential frame-stack semantics, concurrent process
semantics, and equivalence proofs. Cure should not attempt to port the entire
project before implementing the first Lean slice.

Port in this order:

1. Core Erlang values, expressions, functions, and environments;
2. sequential evaluation for the exact emitted subset;
3. frame-stack semantics relevant to Flow dispatch;
4. process/mailbox semantics for the first actor subset;
5. bisimulation or trace equivalence;
6. compiler-correctness relation from Flow IR to Core Erlang.

The Lean port should retain references to the Rocq definitions and theorem
correspondence. Similar theorem names are useful, but semantic correspondence
matters more than textual translation.

The formalization is not allowed to assume that all OTP behavior is represented
by the Core Erlang subset. Unsupported primitives and version-sensitive `cerl`
constructors must fail closed.

## 13. Staged implementation plan

### Stage 0: Freeze the boundary

- define the `cure-core-0.1` schema;
- choose de Bruijn/local-binding representation;
- define stable source-origin IDs;
- define supported types, effects, and primitive operations;
- add a JSON fixture suite.

Gate: malformed, ambiguous, or unsupported JSON is rejected deterministically.

### Stage 1: Lean validation and pure target slice

- implement JSON decoding;
- implement canonical Core datatypes;
- validate bindings and pure types;
- implement Typed Value/Computation IR;
- emit pure Core Erlang;
- prove pure type and semantic preservation for literals, lets, functions,
  calls, cases, tuples, and recursion.

Gate: Lean-generated Core Erlang agrees with the reference evaluator and is
accepted by the installed OTP compiler.

### Stage 2: Primitive effects and computation typing

- add effect rows and sealed/abstract labels;
- add primitive operations and foreign capability declarations;
- implement conservative dependent sequencing;
- prove effect preservation;
- add direct lowering for non-suspending primitive calls.

Gate: no primitive effect can be removed by an untyped transformation.

### Stage 3: Handler/Continuation IR

- add handler clauses and return clauses;
- add answer-type transitions;
- add continuation captures and one-shot ownership;
- add handler protocol summaries;
- prove handler typing and continuation-use invariants.

Gate: a continuation cannot be resumed twice or dropped without a required
cleanup path.

### Stage 4: Flow IR

- implement CPS conversion where suspension escapes;
- defunctionalize continuation sites;
- generate typed state IDs and capture layouts;
- implement frame liveness and direct-call fast paths;
- prove simulation between continuation execution and Flow execution.

Gate: a direct-style suspension example produces an executable Flow machine and
has a checked transition-preservation result.

### Stage 5: Actors and deployment

- add actor/process/mailbox operations;
- preserve latent callback and child effects;
- add links, monitors, supervision, and failure transitions;
- compute deployment effect closure;
- lower the first actor subset to Core Erlang.

Gate: generated actor programs preserve the selected observable message and
failure traces.

### Stage 6: C/ESP32 target

- define a C scheduler ABI for Flow states;
- lower explicit suspension to loop transitions;
- check stack, allocation, and capability bounds;
- differential-test C execution against Lean Flow semantics.

Gate: no suspension path requires unbounded native stack growth.

### Stage 7: Bootstrap and trust reduction

- implement the canonical Core producer in Cure or Lean;
- have Lean validate the bootstrapped compiler's output;
- migrate selected elaboration and lowering passes;
- compare bootstrapped output with the reference Lean middle-end;
- only then consider self-hosting more of the compiler.

Gate: the bootstrapped compiler is observationally equivalent to the checked
reference pipeline on the supported corpus.

## 14. Optimization policy

The Lean implementation may optimize only through transformations with a
corresponding preservation theorem or checked invariant.

The first implementation uses theorem-producing transformations for semantic
lowerings and translation validation for optional optimizations. An optimizer
may propose a candidate IR; a small Lean checker either proves the required
equivalence/invariant or the compiler retains the unoptimized term. This keeps
frame shrinking, state merging, and target peepholes from becoming part of the
trusted compiler path merely because they are fast.

Allowed examples:

- pure constant folding;
- dead pure binding elimination;
- effect-row normalization;
- handler clause pruning when reachability is proved;
- continuation-site specialization;
- frame-field liveness and shrinking;
- state merging when types, rows, ownership, and observable transitions agree;
- tail-transition elimination;
- direct-call lowering when no continuation escapes;
- actor capability and unreachable-state pruning.

Forbidden initially:

- effectful normalization in the dependent kernel;
- removal of sealed effects because a backend call looks primitive;
- continuation duplication;
- state merging across different ownership or effect obligations;
- opaque runtime `Effect(A)` containers;
- runtime macro interpretation;
- whole-program CPS as the only lowering path.

## 15. Relationship to Cure bootstrapping

The Lean middle-end is a bootstrap aid, not a permanent rejection of Cure
self-hosting.

The intended long-term arrangement is:

```text
bootstrapped Cure front end
  → canonical Cure Core
  → Lean-verified middle-end
  → Core Erlang / C / AtomVM
```

Later, selected verified transformations may be reimplemented in Cure, with
Lean remaining the reference proof environment or checking generated
certificates. Cure must not become the only implementation of the semantic
passes until its own dependent kernel can express and verify the relevant
metatheory.

The first milestone is therefore not “bootstrap the compiler.” It is a small,
executable, proof-producing Lean pipeline whose output can be compared against
the current compiler and tested on BEAM.

## 16. Normative companion specifications

This document is the architectural overview. The following documents are the
normative contracts for implementation:

- [`2026-07-21-cure-core-json-schema.md`](2026-07-21-cure-core-json-schema.md)
  defines the `cure-core-0.1` process boundary and validation rules.
- [`2026-07-21-cure-computation-effect-typing.md`](2026-07-21-cure-computation-effect-typing.md)
  defines value/computation judgments, rows, handlers, latent effects, and
  initial restrictions.
- [`2026-07-21-cure-flow-machine-semantics.md`](2026-07-21-cure-flow-machine-semantics.md)
  defines Flow states, frames, scheduler transitions, ownership, and actor
  extensions.
- [`2026-07-21-lean-core-erlang-proof-boundary.md`](2026-07-21-lean-core-erlang-proof-boundary.md)
  defines Lean's target AST, source-to-target relation, proof obligations, and
  external trust assumptions.
- [`2026-07-21-lowcure-restricted-ir-design.md`](2026-07-21-lowcure-restricted-ir-design.md)
  defines the ownership-aware restricted profile and C/Rust/Wasm/ESP32 target
  contracts.

When this overview conflicts with one of those documents, the more specific
normative companion specification governs the relevant implementation detail.
