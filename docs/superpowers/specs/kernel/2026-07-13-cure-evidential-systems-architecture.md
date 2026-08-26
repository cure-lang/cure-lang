CURE EVIDENTIAL SYSTEMS
RED-TEAM-HARDENED DEFINITIVE FUTURE ARCHITECTURE
=================================================

STATUS
======

This document synthesizes and supersedes the previous Cure Evidential Systems
architecture, the subsequent research expansions, and all red-team reviews.

It is a future architectural specification.

It is not a claim about the capabilities of the current Cure implementation.

The purpose of this document is to define:

- what Cure should eventually guarantee;
- what the trusted computing base may contain;
- how proofs, effects, resources, protocols, clocks, and external assumptions
  interact;
- which mechanisms are foundational;
- which mechanisms are domain theories or certificate plugins;
- which claims are admissible for each deployment profile;
- and which implementation gates must be passed before a feature is described
  as sound, verified, deterministic, bounded, or real-time.

The architecture is deliberately conservative at its trusted core and ambitious
outside that core.

The governing principle is:

    Cure must be more suspicious of its own proof infrastructure than it is of
    user programs.


NORMATIVE LANGUAGE
==================

MUST
    Required for architectural conformance.

MUST NOT
    Architecturally prohibited.

SHOULD
    Expected unless a documented and justified alternative exists.

SHOULD NOT
    Strongly discouraged.

MAY
    Optional.

EXPERIMENTAL
    Not admissible in high-assurance profiles unless accompanied by the
    required evidence package.


EXECUTIVE CONCLUSION
====================

The correct architecture is not:

    one enormous dependent kernel
    plus every interesting research feature

and it is not:

    a collection of unrelated verification DSLs
    glued together by compiler convention.

The correct architecture is:

    1. A small intensional quantitative dependent value kernel.

    2. A separate dependent computation core with explicit effects,
       continuation multiplicity, destruction, cancellation, and runners.

    3. Identity-only implicit subsumption.

    4. Explicit adapters, validation, and approximation for every conversion
       that performs work, changes representation, may fail, or loses
       information.

    5. Opaque modules and representation-independent interfaces.

    6. Stratified contract theories rather than one purportedly decidable
       universal contract logic.

    7. Domain calculi for Flow, actors, protocols, hardware, formats,
       persistence, distribution, numerics, physical systems, and security.

    8. Relationally specified compiler stages whose forward compilers,
       validators, lifters, and migration engines are claimed separately.

    9. A claim-and-evidence graph that distinguishes mathematical proof from
       certificates, assumptions, finite observations, measurements, tests, and
       trusted declarations.

    10. Deployment profiles defined as sets of required claims and acceptable
        evidence classes.

The stable public description should be:

    Cure has a small quantitative dependent kernel and an explicitly effectful
    computation core.

    Domain-specific languages elaborate into that shared foundation.

    Every strong system claim names its model, assumptions, observer, evidence
    class, and deployment scope.

    Every conversion, compilation, upgrade, and runtime enforcement boundary
    is explicit and auditable.


WHAT THE FINAL ARXIV PASS CHANGED
================================

The previous red-team synthesis was still missing seven foundational areas.

1. MODULE AND REPRESENTATION ABSTRACTION

   Dependent clients can accidentally prove facts about private
   representations unless opacity and abstraction are enforced semantically,
   not merely by source-file visibility.

   Research on abstraction functions as types and phase-separated modules shows
   that modular verification requires a noninterference boundary between private
   implementation structure and public behavioral meaning.  [arXiv:2502.20496]

2. UNIVERSE AND EQUALITY CONSTITUTION

   A future kernel cannot merely say "dependent types." It must fix:

   - the universe hierarchy;
   - cumulativity;
   - level polymorphism;
   - definitional equality;
   - propositional equality;
   - proof relevance;
   - and which extensional principles are axioms rather than computation.

   Explicit universe-level terms and constraints have a developed formal basis
   and are preferable to hidden, ad hoc universe inference inside the kernel.
   [arXiv:2212.03284]

3. DEPENDENT PATTERN-MATCHING SEMANTICS

   Pattern coverage, absurd patterns, equality refinements, dot patterns, and
   nested patterns are not merely parser conveniences. Their soundness requires
   a precise coverage or eliminator elaboration discipline.  [arXiv:2501.18087]

4. PARTIALITY AND INCOMPLETE DEVELOPMENT

   General recursion, executable holes, nontermination, and incomplete proofs
   must never leak into definitional equality or logical evidence.

   Gradual dependent systems can run incomplete terms, but their imprecise
   fragments are not consistent proof logics; certified Cure builds must
   preserve a hard boundary between executable incompleteness and proof
   acceptance.  [arXiv:1906.06469]

5. IMPLICIT INSTANCE AND PROTOCOL COHERENCE

   Cure protocols, overloads, implicit arguments, and derived instances can
   change runtime behavior if resolution has more than one valid result.

   Coherence is therefore a semantic requirement, not merely a quality-of-error
   requirement.  [arXiv:1907.00844]

6. INCREMENTAL-CACHE SOUNDNESS

   Proof and compilation caches are part of the effective proof pipeline.

   Cache reuse must be content-addressed over canonical checked artifacts and
   complete semantic dependencies. Incrementalization itself must preserve the
   from-scratch semantics.  [arXiv:2602.20866]

7. COST/BEHAVIOR NONINTERFERENCE

   Resource accounting must not alter the functional behavior being analyzed.

   Cost-aware dependent theories use phase distinctions to ensure that program
   outputs cannot depend on ghost cost instrumentation while still supporting
   compositional cost proofs.  [arXiv:2107.04663]


PART I — ASSURANCE DOCTRINE
===========================


1. ONE LANGUAGE, MULTIPLE CLAIM PROFILES
----------------------------------------

Cure MUST remain one language.

Profiles MAY restrict:

- permitted recursion;
- permitted allocation;
- permitted effects;
- runtime topology;
- evidence classes;
- fault models;
- schedulers;
- target backends;
- trusted boundaries.

Profiles MUST NOT create incompatible logical languages.

Required eventual profiles include:

    profile development

    profile beam.dynamic

    profile beam.deterministic

    profile embedded.atomvm

    profile embedded.native

    profile embedded.intermittent

    profile distributed.resilient

    profile security.hardened


2. CLAIMS ARE NOT BOOLEAN BADGES
--------------------------------

A build MUST NOT expose only:

    Verified

A build MUST expose individual claims.

Example:

    MemorySafety:
      ProofChecked

    ProtocolConformance:
      ProofChecked

    MailboxBound:
      CheckedCertificate under BEAMMailboxModel(version)

    Deadline:
      CheckedCertificate under ESP32C3DeploymentModel(hash)

    PhysicalSafety:
      ProofChecked under PlantModel(hash)
      and SensorAccuracyAssumption

    SensorAccuracyAssumption:
      RuntimeMonitored

    CoreErlangToBEAM:
      TrustedToolchain

    FirmwareIdentity:
      Attested

    WiFiTiming:
      BestEffortUnproved


3. EVIDENCE CLASSES ARE DISTINCT
--------------------------------

Cure MUST distinguish:

    Proof(P)

    CheckedCertificate(P, Checker)

    Assumption(P, Scope)

    Observation(O, Time, ObservationModel)

    Measurement(Value, ErrorModel, Calibration)

    MonitorKnowledge(P, TracePrefix, ObservationModel)

    StatisticalEvidence(P, ConfidenceModel)

    TestEvidence(P, CoverageModel)

    TrustedClaim(P, Authority, Reason)

These classes MUST NOT be implicitly convertible.

In particular:

    MonitorKnowledge(P) MUST NOT imply Proof(P).

    TestEvidence(P) MUST NOT imply CheckedCertificate(P).

    Assumption(P) MUST NOT imply Proof(P).

    TrustedClaim(P) MUST remain visible as trust.


4. PROPERTY-DIRECTED ASSURANCE CASES
------------------------------------

Every exported system claim MUST produce an assurance-case graph.

Each graph node MUST identify:

- proposition;
- evidence class;
- model;
- assumptions;
- target;
- observer;
- fault model;
- evidence producer;
- checker;
- semantic version;
- expiry or freshness;
- runtime degradation policy.

Example:

    claim MotorTemperatureSafe

    depends on:
      ControllerInvariant
      PlantModelCorrespondence
      SensorErrorBound
      SchedulingJitterBound
      FloatErrorBound
      ShieldCorrectness
      NativeLoweringCorrectness
      FirmwareIdentity

When an assumption fails, Cure MUST identify exactly which claims are invalidated
or weakened.


5. CLOSED-WORLD VERSUS OPEN-WORLD CLAIMS
----------------------------------------

Closed-world claims include:

- typing;
- value invariants;
- state transitions;
- protocol conformance;
- Flow causality;
- resource use under a model;
- schedule properties;
- compilation;
- serialization;
- migration.

These SHOULD be statically established.

Open-world claims include:

- sensor accuracy;
- physical dynamics;
- power stability;
- hardware timing;
- radio behavior;
- remote services;
- external operators;
- unverified FFI.

These MUST be:

- explicit assumptions;
- monitored where observable;
- validated at startup;
- isolated behind enforcement;
- or represented as fallible runtime results.


6. UNKNOWN IS NOT FALSE AND NOT TRUE
------------------------------------

Every solver and checker interface MUST support:

    Proven

    Disproven

    Unknown(reason)

Possible reasons include:

    BudgetExhausted

    UnsupportedTheory

    IncompleteProcedure

    ModelMismatch

    MissingEvidence

    SolverFailure

    CertificateRejected

No tool timeout may be interpreted as acceptance.

Failure of a sufficient analysis MUST NOT be reported as a proof of
impossibility.


PART II — STABLE CORE CONSTITUTION
=================================


7. PURE INTENSIONAL QUANTITATIVE DEPENDENT KERNEL
-------------------------------------------------

The stable kernel SHOULD contain only:

- variables and contexts;
- predicative universes;
- dependent functions;
- dependent pairs;
- identity types;
- strictly positive inductive families;
- eliminators;
- quantitative usage;
- definitional reduction;
- explicit proof terms;
- explicit universe terms;
- explicit coercion terms;
- termination/productivity evidence checking where admitted.

The kernel MUST NOT directly contain:

- Flow scheduling;
- actor scheduling;
- mailbox execution;
- SMT;
- model checking;
- hybrid-system solvers;
- contract negotiation;
- FFI execution;
- network effects;
- runtime monitors;
- code generation;
- migration engines;
- optimization search.


8. VALUE AND COMPUTATION STRATA
-------------------------------

The kernel architecture MUST distinguish:

    ValueType

    ComputationType

Only total pure values may participate directly in:

- types;
- indices;
- definitional equality;
- universe expressions;
- quantity expressions used by the kernel.

Effectful computations MUST NOT execute during conversion.

This should use a dependent call-by-push-value-style architecture.

Dependent CBPV provides a principled separation between values and computations
and exposes the difficulties introduced when dependent types are allowed to
become more specific as effects execute.  [arXiv:1512.08009]

Initial Cure SHOULD follow the conservative form:

    types may depend on values;

    types may not depend on arbitrary pending computations.

Runtime values may become indexed only after explicit validation or packaging.


9. UNIVERSE HIERARCHY
---------------------

The initial kernel MUST use a predicative hierarchy:

    Type(0)
    Type(1)
    Type(2)
    ...

Core universe levels SHOULD include:

    zero

    successor(level)

    maximum(level_a, level_b)

    level variables

    explicit constraints

Surface syntax MAY infer universe levels.

Canonical core MUST contain explicit levels and solved constraints.

The kernel MUST independently check universe constraints.

The kernel MUST NOT support:

    Type : Type

The initial kernel SHOULD avoid:

- impredicative data universes;
- first-class unrestricted universe reflection;
- universe equations whose decision procedure is unclear.

Surface cumulativity MAY be supported, but canonical core MUST record explicit
lifting or checked level inclusion.


10. PROPOSITIONS AND PROOF RELEVANCE
------------------------------------

The initial stable kernel SHOULD NOT assume universal proof irrelevance.

Instead:

- propositions are types;
- proof terms may be marked quantity 0;
- erasability is established through the quantitative and phase discipline;
- proposition-specific proof irrelevance may be proved or declared through a
  checked interface.

This avoids conflating:

- truth;
- proof equality;
- totality;
- purity;
- runtime irrelevance;
- and erasability.

A later proof-irrelevant `Prop` universe MAY be admitted only with:

- explicit elimination restrictions;
- a metatheory package;
- erasure correctness;
- interaction proofs for quantities and effects.


11. EQUALITY
------------

The kernel MUST use intensional definitional equality.

Required distinction:

    DefinitionalEquality(a, b)
      decided by kernel conversion.

    PropositionalEquality(a, b)
      represented by an identity type and proof.

The stable kernel MUST NOT include general equality reflection:

    Proof(a = b) => a definitionally equals b

because unrestricted equality reflection makes type checking depend on theorem
proving and can destroy decidability.

Function extensionality, quotient principles, univalence, classical axioms, and
similar principles MAY exist as:

- explicit axioms;
- imported trusted theorems;
- or theory plugins.

They MUST NOT silently extend kernel reduction.

Every such dependency MUST appear in the theorem's axiom closure.


12. CONVERSION CHECKING
-----------------------

Conversion correctness requires more than normalization.

The kernel constitution MUST state and eventually mechanize:

- weakening;
- substitution;
- context conversion;
- subject reduction;
- type constructor injectivity;
- universe constructor injectivity;
- dependent function injectivity;
- dependent pair injectivity;
- inductive-family injectivity;
- soundness of algorithmic conversion;
- completeness of algorithmic conversion;
- termination under the declared transparency policy.

Recent work emphasizes that injectivity properties are central to certifying
conversion procedures, not merely auxiliary lemmas.  [arXiv:2502.15500]

Cure SHOULD eventually maintain:

    ReferenceChecker

    ProductionChecker

High-assurance builds MAY require acceptance by both.


13. CONTROLLED UNFOLDING
------------------------

Definitions MUST be opaque across module boundaries by default.

The language MUST support explicit local transparency:

    unfold Foo within proof

    transparent Foo in module InternalProofs

Unfolding MUST NOT be a global accidental property of declaration order.

Controlled unfolding improves proof robustness and prevents private
implementation changes from invalidating unrelated client proofs.
[arXiv:2210.05420]

Transparency settings MUST be included in semantic hashes.


14. ERASURE
-----------

Erasure MUST distinguish:

    Logical

    RuntimeRelevant

    Erasable

    ProofIrrelevant

    Total

    Pure

A term is erasable only if the compiler establishes:

    Total(term)

    Pure(term)

    NoRuntimePatternDependency(term)

    RepresentationIndependent(term)

    NoEffectDependency(term)

Proof irrelevance alone MUST NOT imply erasability.

Cure MUST distinguish:

    RuntimeSigma
      witness retained at runtime.

    ErasedSigma
      witness erased and operational representation independent of it.

    PackedSigma
      witness hidden from public behavior but retained in runtime metadata.

Structural phase-based erasure has a formal model and can support correct code
extraction, but open-term and erased-pattern interactions remain areas requiring
care.  [arXiv:2605.00655]


15. INDUCTIVE FAMILIES
----------------------

The initial kernel SHOULD support only regular strictly positive inductive
families.

Every declaration MUST pass:

- universe consistency;
- strict positivity;
- constructor typing;
- parameter/index discipline;
- elimination-level checking;
- generated eliminator checking.

The following SHOULD remain experimental initially:

- nested inductives;
- inductive-recursive definitions;
- quotient inductives;
- higher inductives;
- arbitrary user rewrite rules;
- coinductives in the proof kernel.

Guarded reactive coinduction SHOULD initially live in the Flow theory rather
than the general kernel.


16. DEPENDENT PATTERN MATCHING
------------------------------

Surface pattern matching MUST elaborate to one of:

    checked eliminator terms

    typed decision trees with a coverage certificate

The kernel MUST NOT trust a surface coverage checker.

The elaboration MUST account for:

- nested patterns;
- equality refinements;
- dot patterns;
- absurd patterns;
- inaccessible patterns;
- indexed constructors;
- branch-local equations;
- branch coverage;
- redundant branches.

An absurd branch MUST carry evidence that its pattern context is empty.

Recent coverage semantics work demonstrates that admissible dependent pattern
sets require a semantic coverage criterion rather than ordinary syntactic
exhaustiveness alone.  [arXiv:2501.18087]


17. TOTALITY, PARTIALITY, AND GENERAL RECURSION
----------------------------------------------

Functions used by:

- definitional equality;
- types;
- indices;
- proofs;
- compile-time normalization

MUST be total.

Accepted totality evidence MAY include:

- structural recursion;
- well-founded recursion;
- sized recursion;
- guarded recursion;
- certificate-checked termination;
- explicit fuel where the result type reflects exhaustion.

General recursion MUST live in the computation stratum.

Possible forms:

    Partial(A)

    Computation(A, effects {divergence})

    Process(A)

    StreamProcess(A)

Partial computation MUST NOT reduce during kernel conversion.

A theorem MUST NOT depend on executing a partial computation unless a separate
termination proof has first reclassified that computation as total.


18. DEVELOPMENT HOLES
---------------------

Development profiles MAY permit:

    term holes

    proof holes

    unknown implementations

    runtime stubs

Every hole MUST be represented explicitly in the artifact.

A build containing holes MUST NOT receive:

    ProofChecked

    ProductionCertified

    HardRealtime

    SemanticCompatibility

unless the relevant claim is independent of those holes and that independence
is proved.

There MUST be no hidden equivalent of:

    sorry

inside certified artifacts.

Release profiles SHOULD reject all unapproved axioms and holes.


PART III — MODULES, ABSTRACTION, AND IMPLICITS
=============================================


19. MODULE ABSTRACTION
----------------------

A module interface MUST separate:

    public behavioral specification

    private representation

    private algorithm

    public resource envelope where relevant

Clients MUST NOT be able to derive public facts from private representation
details.

A module implementation MUST provide an abstraction relation:

    Represents(Concrete, Abstract)

or an abstraction function:

    abstract : Concrete -> Abstract

Operations MUST preserve that relation.

Research on phase-separated abstraction demonstrates a route to representation
independence and modular cost reasoning in dependent type theory.
[arXiv:2502.20496]


20. OPAQUE INTERFACES
---------------------

Example conceptual form:

    module Queue
      opaque type Queue(A)

      behavior
        abstract Queue(A) as List(A)

      fn empty() -> Queue(A)

      fn push(
        queue: Queue(A),
        item: A
      ) -> Queue(A)

      fn pop(
        queue: Queue(A)
      ) -> Option({head: A, tail: Queue(A)})

      laws
        abstract(empty()) == []

        abstract(push(q, x)) == abstract(q) ++ [x]

The client sees:

- abstract behavior;
- operation types;
- laws;
- exported resource contracts.

The client does not see:

- pair-of-list representation;
- balancing strategy;
- private proof objects;
- private cost instrumentation.


21. BEHAVIOR AND COST PHASES
----------------------------

Cure SHOULD distinguish behavioral meaning from cost observation.

Cost accounting MUST NOT affect ordinary outputs.

Conceptually:

    Behavior(program)

    Cost(program, CostModel)

Required noninterference property:

    changing ghost cost instrumentation does not change Behavior(program)

Cost models MUST be explicit and versioned.

Possible cost models include:

    BEAMReductions

    BEAMAllocatedWords

    AtomVMHeapWords

    NativeInstructions

    PlatformCycles

    EnergyEstimate

    NetworkBytes

A cost theorem under one model MUST NOT be reused under another.


22. GENERATIVE MODULES
----------------------

Generative modules create fresh abstract identities.

If supported, freshness MUST be explicit in core.

Two separately instantiated generative modules MUST NOT have definitionally
equal private types merely because their implementation source is identical.

Generativity MAY initially be omitted in favor of simpler sealed modules.


23. PROTOCOL AND TYPECLASS COHERENCE
------------------------------------

Cure protocols and overload resolution MUST have one predictable meaning.

Stable Cure SHOULD initially require:

    one canonical implicit implementation
    for each protocol/type head within an instance scope

Alternative implementations SHOULD be passed explicitly.

Overlapping or locally shadowed instances MAY exist only when:

- selection is explicit;
- or a formally coherent resolution calculus is used.

Canonical core MUST contain explicit dictionaries or implementation references.

The kernel MUST check the elaborated call, not rerun instance search.

Resolution ambiguity MUST be a compile error.

Resolution order MUST NOT depend on:

- import order;
- filesystem order;
- hash-map iteration;
- parallel compilation timing.


24. PROTOCOL LAWS
-----------------

Method signature conformance and algebraic law conformance MUST be separate.

Example:

    proto Ord(T)
      fn compare(a: T, b: T) -> Ordering

      laws
        antisymmetric
        transitive
        total

An implementation may satisfy the method type but not the laws.

Cure MUST report separately:

    InterfaceConformant

    LawChecked

    LawAssumed

    LawUntested


25. OVERLOAD AND CALL-SITE LABEL ELABORATION
--------------------------------------------

Overloaded functions and Swift-style call-site labels MUST elaborate to explicit
core references.

Labels affect:

- name resolution;
- API clarity.

Labels MUST NOT alter the logical meaning of an already resolved function.

All overload selection MUST be stable before proof checking.


26. MACROS
----------

Macros MUST be hygienic.

Macro output MUST be fully elaborated and kernel checked.

A macro that claims a semantic derivation MUST provide evidence for that claim.

Examples:

    derive Codec(T)
      MUST prove codec laws or mark them unproved.

    derive protocol role
      MUST provide projection/conformance evidence.

    derive Flow schedule
      MUST provide schedule validity evidence.

Generated code merely typechecking is not sufficient evidence that a semantic
derivation is correct.


PART IV — CONVERSION AND SUBTYPING
=================================


27. FIVE DISTINCT RELATIONS
---------------------------

Cure MUST distinguish:

    RuntimeIdentityInclusion(A, B)

    ProofForgettingRefinement(A, B)

    Adapter(A, B)

    Approximation(A, B, ErrorModel)

    DynamicValidation(A, B, Failure)

Only the first two may drive implicit subsumption.


28. RUNTIME IDENTITY INCLUSION
------------------------------

An implicit inclusion is legal only if:

- runtime representation is identical;
- no code executes;
- no allocation occurs;
- no traversal occurs;
- no failure is possible;
- no effect occurs;
- no information is lost;
- no capability or ownership state changes.

Example:

    PositiveInt -> Int

may be an identity-preserving proof-forgetting refinement if the runtime
representations are identical.


29. INT IS NOT A SUBTYPE OF FLOAT
---------------------------------

Cure MUST remove:

    Int <: Float

for arbitrary integers and finite IEEE floating-point values.

Required explicit operations:

    fn Int.to_float_exact(
      value: Int
    ) -> Result(Float, NotExactlyRepresentable)

    fn Int.to_float_approx(
      value: Int
    ) -> Approximation(
      Float,
      AbsoluteError
    )

No implicit conversion may introduce numerical approximation into:

- refinements;
- proofs;
- physical models;
- resource calculations;
- schedule calculations.


30. CONTAINER VARIANCE
----------------------

An inclusion:

    Container(A) -> Container(B)

is implicit only if the `A -> B` inclusion is runtime identity and the container
representation is unchanged.

Otherwise it is an explicit mapping adapter.

Example:

    List(Int) -> List(Float)

is:

- O(n);
- potentially allocating;
- numerically approximate;
- not subtyping.


31. FUNCTION VARIANCE
---------------------

Function adaptation MUST be explicit in canonical core.

Conceptually:

    adapt_function(
      input_adapter,
      output_adapter,
      function
    )

The wrapper's:

- effects;
- allocation;
- captures;
- timing;
- failure;
- representation

must be included in its type and summaries.

The surface MAY hide only a proven runtime-identity wrapper.


32. COERCION COHERENCE
----------------------

For every two implicit paths:

    p: A -> B
    q: A -> B

Cure MUST prove that they have the same runtime and logical meaning, or reject
the ambiguity.

The implicit inclusion graph MUST be:

- acyclic after equality collapsing;
- deterministic;
- validated at module-link time.

Explicit adapters may have multiple alternatives because their selection is
visible.


PART V — EFFECTFUL COMPUTATION CORE
==================================


33. COMPUTATION TYPE
--------------------

Conceptual core:

    Computation(
      Result,
      Effects,
      Requirements,
      Captures,
      ControlQuantity
    )

Surface syntax SHOULD remain direct style.

Users SHOULD NOT be forced to write monadic notation.


34. EFFECTS VERSUS MODALITIES
-----------------------------

An operation such as:

    send
    spawn
    read GPIO
    allocate
    suspend

is an effect.

A property such as:

    use exactly once
    available later
    captured by closure
    located on node
    classified secret

is contextual or modal information.

Cure MUST NOT place every property into one universal effect row.

The initial kernel SHOULD directly support only quantitative use.

Other theories SHOULD elaborate into:

- indexed types;
- computation effects;
- context requirements;
- domain IR;
- or admitted modal extensions.


35. THEORY ADMISSION
--------------------

A new effect algebra or mode theory MUST provide:

    syntax

    equality procedure

    composition

    identity

    ordering

    coherence laws

    substitution interaction

    quantity interaction

    effect interaction

    erasure behavior

    operational semantics

    checker or proof translation

    Antigen test families

Normal source programs MUST NOT freely invent kernel modes.


36. CONTROL-FLOW LINEARITY
--------------------------

Effect handlers can duplicate or discard continuations.

A continuation may capture a linear resource.

Therefore Cure MUST track:

    value quantity

    continuation quantity

Required continuation quantities:

    NeverResume

    AtMostOnce

    ExactlyOnce

    Bounded(n)

    Many

Research has demonstrated that ordinary value linearity is insufficient when
handlers may invoke captured continuations multiple times.  [arXiv:2307.09383]


37. HANDLER DEFAULT
-------------------

Stable Cure SHOULD default handlers to one-shot continuations.

A `Many` continuation is accepted only if all captured resources are duplicable.

It MUST NOT capture:

- linear buffers;
- active session roles;
- DMA ownership;
- unique borrows;
- destructible resources requiring exactly-once finalization;
- revocable exclusive capabilities.


38. RUNNERS
-----------

External resources SHOULD be interpreted by typed runners.

A runner:

- owns implementation state;
- interprets an effect interface;
- states its invariant;
- states its cost model;
- states its failure behavior;
- provides finalization;
- identifies trusted boundaries.

Runners provide a natural model for top-level resources and finalization.
[arXiv:1910.11629]

Example:

    runner ESPGPIO4
      implements GPIOEffect(4)

      owns @linear GPIO(4, Configured)

      invariant
        hardware_mode == Output

      finalizes
        set_low
        disable


39. DESTRUCTION
---------------

Cure MUST distinguish:

    Linear

    AffineForgettable

    AffineDestructible

    Unrestricted

Dropping `AffineDestructible` MUST execute an approved destructor.

Examples:

    proof token:
      AffineForgettable

    open socket:
      AffineDestructible

    in-flight DMA:
      Linear


40. CANCELLATION
----------------

Cancellation MUST be an effectful protocol transition.

It MUST NOT mean silently discarding computation state.

Example:

    cancel:
      DMA(channel, Active(buffer))
      -> Computation(
           {
             dma: DMA(channel, Idle),
             buffer: Buffer(Ready)
           },
           DMAEffects
         )

Cancellation semantics MUST cover:

- exception;
- timeout;
- actor death;
- supervisor restart;
- Flow shutdown;
- hot upgrade;
- deployment teardown.


41. FINALIZATION
----------------

Runners MUST define finalization on:

- success;
- ordinary failure;
- cancellation;
- handler abort;
- process termination;
- upgrade;
- shutdown.

Finalization failure MUST remain observable.

Cure MUST define ordering when both the main computation and finalizer fail.


42. CAPABILITY REVOCATION
-------------------------

Capabilities MAY become invalid asynchronously.

Capabilities that can be revoked SHOULD be indexed by authority epoch:

    Capability(Resource, Epoch)

A received serialized capability is not live authority.

It SHOULD first be:

    PresentedCapability(Resource, Epoch)

and validated into:

    ValidCapability(Resource, CurrentEpoch)

Revocation MUST invalidate reachable aliases according to the capability model.


43. EFFECT SPECIFICATIONS
-------------------------

Every standard effect interpretation SHOULD provide:

    operational semantics

    weakest-precondition semantics

    relational semantics where required

    resource semantics

This avoids manually inventing unrelated proof rules for each effect.

Contracts over effectful code SHOULD be derived from the effect interpretation.


PART VI — CONTRACT AND SPECIFICATION ARCHITECTURE
================================================


44. STRATIFIED CONTRACT THEORIES
--------------------------------

Cure MUST NOT pretend that one general contract logic has a complete decision
procedure for all domains.

Required initial classes:

    Contract.Local
      preconditions and postconditions.

    Contract.FiniteState
      finite automata and bounded temporal properties.

    Contract.Stream
      clocked stream relations.

    Contract.Resource
      memory, work, latency, energy, queue bounds.

    Contract.Protocol
      communication behavior.

    Contract.Hyper
      named cross-execution relations.

    Contract.Hybrid
      controller and physical-plant relations.

A general semantic `Hypercontract` MAY serve as the umbrella denotation.

Algorithms MUST remain theory-specific.


45. CONTRACT OPERATIONS
-----------------------

Where defined, contract theories SHOULD provide:

    compose

    refines

    compatible

    conjoin

    quotient

    hide

    project

    strengthen

    weaken

Results MUST state precision:

    Exact

    SoundOverApproximation

    SoundUnderApproximation

    Unsupported

    Unknown


46. CIRCULAR CONTRACT REASONING
-------------------------------

A contract dependency cycle is rejected unless justified by:

    induction

    guarded recursion

    temporal delay

    monotone least fixed point

    monotone greatest fixed point

    explicit invariant

    well-founded measure

Unguarded assume-guarantee cycles MUST NOT discharge themselves.


47. QUOTIENT IMPLEMENTABILITY
-----------------------------

After computing:

    residual = quotient(system, known_component)

Cure MUST check:

    causality

    interface locality

    realizability

    resource feasibility

    profile implementability

The result type SHOULD be:

    ImplementableResidual

rather than an unrestricted contract.


48. REALIZABILITY
-----------------

Supported finite-state and bounded specifications SHOULD be checked for
realizability before implementation proof.

On failure Cure SHOULD produce:

- counterstrategy;
- conflicting guarantees;
- insufficient assumptions;
- candidate repair.

The compiler MUST NOT silently add assumptions.


49. NON-VACUITY
---------------

Every hard guarantee SHOULD be analyzed for:

    assumption satisfiability

    trigger reachability

    consequent relevance

    output constraint coverage

    redundancy

Required results:

    NonVacuous

    VacuousBecauseTriggerUnreachable

    VacuousBecauseAssumptionsImpossible

    VacuousBecauseConsequentIrrelevant

    Redundant

    Unknown

A proof under impossible assumptions MUST NOT receive an ordinary green
assurance presentation.


50. SPECIFICATION COVERAGE
--------------------------

Cure SHOULD emit:

    specification_coverage {
      reachable_triggers
      unreachable_triggers
      constrained_outputs
      unconstrained_outputs
      assumptions_used
      assumptions_unused
      covered_states
      unspecified_states
      vacuous_guarantees
    }


51. REQUIREMENT TRACEABILITY
----------------------------

Human requirements SHOULD map to:

- formal propositions;
- implementation components;
- monitors;
- shields;
- tests;
- assumptions;
- target profiles.

Example:

    requirement REQ-MOTOR-017
      text:
        "The motor shall stop within 10 ms of overtemperature."

      formal:
        EventuallyWithin(
          10.ms,
          motor == Stopped
        )

      depends_on:
        sensor pace
        scheduler bound
        shield latency
        actuator model

Changing the formal requirement is a semantic change.


52. CONTRACT WEAKENING
-----------------------

Weakening a public guarantee MUST:

- be reported as a breaking semantic change;
- identify invalidated downstream claims;
- require explicit approval in protected profiles;
- never be silently introduced by synthesis.


PART VII — FLOW CALCULUS
=======================


53. FLOW IS A DOMAIN THEORY
---------------------------

Flow remains a first-class user-facing DSL.

Flow MUST elaborate into:

- total transition relations;
- clock and pace constraints;
- guarded state;
- indexed effects;
- contract summaries;
- resource obligations.

Flow SHOULD NOT require users to write raw modal or monadic syntax.


54. TWO PRIMARY SEMANTICS
-------------------------

Flow MUST have:

    stream semantics

    transition-system semantics

Neither is merely documentation.

Cure MUST establish:

    StreamTransitionEquivalent(flow)

Stream semantics supports:

- user meaning;
- temporal reasoning;
- compositional equations.

Transition semantics supports:

- scheduling;
- state layout;
- model checking;
- code generation.


55. SIGNAL MODEL
----------------

Conceptually:

    Signal(
      Value,
      Pace,
      Dependencies,
      Availability,
      InformationQuality
    )

Most parameters SHOULD be inferred.


56. CLOCKS AND PACES
-------------------

Cure MUST distinguish:

- trigger dependency;
- pace;
- logical clock;
- physical schedule;
- resampling;
- latency;
- staleness.

Clock crossing requires explicit policy:

    current

    hold_latest

    sample_at

    interpolate_at

    await_next

    optional

    all_since_previous


57. GUARDED FEEDBACK
--------------------

Reactive cycles require:

- temporal delay;
- or a constructive causality proof.

Initial stable Flow SHOULD require explicit delay for every cycle.

Constructive zero-delay feedback MAY be introduced later with a dedicated
certificate.


58. INITIALIZATION
------------------

Availability MUST be typed.

Conceptually:

    AvailableFrom(tick)

No output may depend on an unavailable value.

Startup state MUST be total for deterministic and embedded profiles.


59. REACTION CLASSES
--------------------

Every Flow-callable function SHOULD be classified:

    ConstantBound

    ValueBound(expression)

    TerminatingUnbounded

    Suspending

    PotentiallyDivergent

    ExternalUnknown

Hard deterministic reactions may call only accepted bounded classes.


60. DETERMINISTIC REGIONS
-------------------------

Within a deterministic region:

- events have logical tags;
- same-tag ordering is deterministic;
- independent reactions may execute concurrently;
- observable behavior is schedule-independent;
- asynchronous ingress is explicitly tagged;
- asynchronous egress is explicit.

Required relational claim:

    ScheduleIndependent(region)


61. PARTIAL INFORMATION
-----------------------

Physical and distributed observations SHOULD use:

    Observation(A)
      | Known(A)
      | Bounded(lower, upper)
      | Missing(interval)
      | Late(A, timestamp)
      | Invalid(reason)

Partial information MUST propagate soundly.


62. QUEUE BOUNDEDNESS
---------------------

Cure MUST distinguish:

    UniversallyBounded(n)

    SchedulerBounded(n, schedule)

    ExistentiallyBounded(n)

    EmpiricallyBounded(n)

    Unbounded

Only universal and scheduler-specific bounds are sufficient for static embedded
allocation.


63. FLOW RESOURCE SEMANTICS
---------------------------

Resource analysis MUST include:

- node state;
- history;
- queues;
- monitor state;
- shield state;
- work;
- latency;
- allocation;
- stack;
- message copies.

Cost instrumentation MUST be behaviorally noninterfering.


PART VIII — ACTORS, MAILBOXES, AND PROTOCOLS
===========================================


64. GLOBAL VERSUS LOCAL PROTOCOL MODELS
---------------------------------------

Global interactions SHOULD use choreographies or global protocols.

Local BEAM implementations SHOULD use:

    mailbox types

    actor-reference capabilities

    handler-context transitions

Multiparty session types SHOULD NOT be the sole local actor model.


65. NETWORK-PARAMETRIC IMPLEMENTABILITY
---------------------------------------

Every global protocol MUST name its communication architecture.

Examples:

    PeerToPeerFIFO

    Mailbox

    SelectiveMailbox

    Senderbox

    Bag

    LossyBroadcast

Global-protocol implementability depends on the network architecture, and recent
work provides architecture-parametric coherence criteria for several common
models.  [arXiv:2602.10320]


66. PROTOCOL PIPELINE
---------------------

Required pipeline:

    global protocol
        ->
    network-specific implementability
        ->
    local automata
        ->
    mailbox types
        ->
    actor-reference capabilities
        ->
    handler checking
        ->
    backend conformance


67. MAILBOX TYPES
-----------------

Mailbox types describe possible mailbox contents and obligations.

Practical mailbox-typing research models mailbox contents with commutative
regular expressions and detects protocol violations, unexpected messages,
forgotten replies, and self-deadlock.  [arXiv:2306.12935]

Cure's formalism MUST additionally model actual BEAM semantics:

- arrival order;
- selective scan;
- first matching clause;
- retained unmatched messages;
- clause order;
- guards;
- timeouts;
- starvation;
- scan cost.


68. ACTOR REFERENCE CAPABILITIES
-------------------------------

An actor reference SHOULD specify:

- messages the holder may send;
- ordering constraints;
- protocol role;
- authority scope;
- capability epoch.

Delegating or splitting references MUST preserve aggregate authority.


69. LOCAL ACTOR PROPERTIES
--------------------------

Required properties include:

    MailboxConformance

    MailboxJunkFreedom

    MailboxBound

    SelectiveReceiveProgress

    ScanCostBound

    SessionInterferenceFreedom

    HandlerProgress

    SharedStateInvariant


70. RESOURCE-AWARE PROTOCOLS
----------------------------

Messages MAY carry resource potential used to pay for:

- parsing;
- mailbox scanning;
- computation;
- allocation;
- reply generation;
- cryptography.

This SHOULD be integrated early for bounded AtomVM and denial-of-service
analysis.


71. CORE ERLANG REFERENCE BACKEND
---------------------------------

The reference BEAM lowering SHOULD target a defined Core Erlang subset.

Concurrent Core Erlang has a machine-checked semantics and bisimulation-based
program-equivalence work that provides a concrete foundation for a Cure backend
relation.  [arXiv:2311.10482]

Pipeline:

    Cure computation core
        ->
    Cure actor/mailbox IR
        ->
    supported Core Erlang
        ->
    Erlang compiler
        ->
    BEAM


72. BEAM TRUST SPLIT
--------------------

Claims MUST distinguish:

    CureToCoreErlang:
      ProofChecked or TranslationValidated

    CoreErlangToBEAM:
      TrustedToolchain or separately validated

    BEAMRuntime:
      TrustedRuntimeModel

A proof of Cure-to-Core-Erlang correctness MUST NOT imply that ERTS is verified.


73. SUPERVISION
---------------

Supervision claims MUST include:

- application state;
- protocol state;
- capability ownership;
- timer epochs;
- mailbox frontier;
- output commit frontier;
- monitor history;
- replayed nondeterminism.

Restarting only the application struct is insufficient.


74. FAIRNESS AND SYNCHRONY
--------------------------

Every liveness theorem MUST name:

- network synchrony;
- process fairness;
- message fairness;
- timer fairness;
- receive fairness;
- failure detector;
- fault model.

Required distinctions include:

    NoFairness

    WeakProcessFairness

    StrongProcessFairness

    WeakMessageFairness

    StrongMessageFairness

    FairMailboxDispatch

    FairSessionDispatch


75. FAULT MODELS
----------------

Required fault classes:

    Correct

    CrashStop

    CrashRecovery

    Omission

    Duplication

    Reordering

    Corruption

    TimingFault

    Byzantine

    CompromisedKey

    ArbitraryStateCorruption

Protocol claims MUST be indexed by the precise model.


76. SELF-STABILIZATION
----------------------

Distributed resilient profiles MAY support:

    Legitimate(State)

    ClosedUnderTransitions(Legitimate)

    ConvergesTo(Legitimate, FaultEnvelope)

    StabilizesWithin(bound)

Self-stabilization MUST remain distinct from:

- checkpoint recovery;
- failure transparency;
- Byzantine containment.


PART IX — DISTRIBUTED COORDINATION
=================================


77. COORDINATION REQUIREMENTS
-----------------------------

Cure SHOULD infer whether a distributed computation requires:

    None

    PerKey

    Causal

    Quorum

    TotalOrder

    Consensus


78. STABLE VERSUS PROVISIONAL RESULTS
-------------------------------------

Distributed queries SHOULD produce:

    Stable(A)

    Provisional(A)

    FinalAfter(Watermark, A)

A conclusion based on absence of information MUST identify:

- closure evidence;
- watermark;
- timeout;
- or coordination.


79. REPLICATED STATE
--------------------

Replicated types MAY require:

    JoinSemilattice(State)

    AssociativeMerge

    CommutativeMerge

    IdempotentMerge

    MonotoneUpdate

Convergence claims MUST name network-delivery assumptions.

A convergent state type does not imply every query is stable.


80. DYNAMIC RECONFIGURATION
----------------------------

Cure MUST distinguish:

- code upgrade;
- state-schema migration;
- protocol migration;
- actor placement migration;
- replica-set reconfiguration;
- trust-root rotation.

Each requires its own preservation relation.


PART X — DURABILITY AND FAILURE TRANSPARENCY
===========================================


81. EFFECT COMMIT LIFECYCLE
---------------------------

External effects SHOULD use states:

    Proposed

    Prepared

    Committed

    ExternallyVisible

    DetectablyCommitted

    Compensated

    Aborted


82. COMMIT STATUS
-----------------

After recovery:

    CommitStatus(effect_id)
      | DefinitelyCommitted
      | DefinitelyNotCommitted
      | UnknownCommitStatus

Unknown commit status MUST NOT be automatically retried for non-idempotent
operations.


83. EFFECT IDENTITIES
---------------------

Recoverable effects SHOULD have stable:

    EffectId

Deduplication requires evidence that the receiving system recognizes the same
identity across retries.


84. COMMIT FRONTIERS
--------------------

Persistent processes SHOULD track:

    input_frontier

    state_frontier

    output_frontier

    acknowledgment_frontier

Failure transparency depends on their relationship.


85. DURABILITY CLAIMS
---------------------

Cure MUST distinguish:

    PersistedBeforeReturn

    DurableLinearizable

    BufferedDurableLinearizable

    DurableOpaque

    Detectable

    ExactlyOnceVisible

    RecoverableToPrefix


86. DURABLE ACTOR RUNNER
------------------------

A durable actor runner MAY atomically persist:

- consumed message identity;
- next state;
- outgoing message intents;
- protocol transition;
- timer changes.

Publishing and acknowledgment MUST use explicit deduplication and commit
semantics.


87. FAILURE TRANSPARENCY
------------------------

Required proposition:

    FailureTransparent(
      implementation,
      failure_free_model,
      observer
    )

This is stronger than local restart correctness.

It requires failed executions to correspond to an allowed failure-free
observation.


88. INTERMITTENT EXECUTION
--------------------------

Optional embedded profiles MAY distinguish:

    Volatile(A)

    Persistent(A)

    Checkpointed(A, Epoch)

    ExternalState(A)

Required claims MAY include:

    PowerFailureAtomic

    IntermittenceEquivalent

    FreshAfterResume

    ExactlyOnceAcrossPowerFailure


PART XI — RUNTIME ASSURANCE
===========================


89. MONITORS COMPUTE KNOWLEDGE
------------------------------

A monitor SHOULD be typed as:

    Monitor(
      Property,
      ObservationModel,
      KnowledgeDomain
    )

It computes what can be known from observations.

It does not automatically prove the infinite-trace property.


90. OBSERVATION MODELS
----------------------

Required models include:

    CompleteSequentialTrace

    FinitePrefix

    OutOfOrder(maximum_lateness)

    Lossy(loss_bound)

    PartiallySynchronous(clock_skew)

    MultipleExecutions(count)


91. MONITOR VERDICTS
--------------------

Required statuses:

    DefinitivelySatisfied

    DefinitivelyViolated

    SatisfiedOnObservedPrefix

    ViolatedOnObservedPrefix

    Pending

    Inconclusive

    ProvisionalUntil(watermark)

    Retracted(previous)

Finite-observation temporal semantics must be formally related to infinite-trace
meaning; formula progression can be sound and complete for the chosen finite
semantics without turning every prefix into a final liveness verdict.
[arXiv:2411.14581]


92. MONITOR APPROXIMATION
-------------------------

Monitor certificates MUST state:

    SoundAndComplete

    SoundOverApproximation

    CompleteUnderApproximation

    BoundedApproximation

An overapproximating monitor MUST NOT emit unjustified definitive satisfaction.


93. DISTRIBUTED MONITORS
------------------------

Distributed monitors MUST state:

- event-time model;
- clock-skew assumption;
- reordering window;
- message-loss model;
- watermark;
- correction policy.

Arrival order MUST NOT be assumed to equal event order.


94. HYPERMONITORS
-----------------

Cross-execution properties require multiple executions.

Examples:

    Noninterference

    ScheduleIndependence

    DifferentialPrivacy

A finite sampled trace set normally yields test or statistical evidence, not a
general proof.


95. SAFETY SHIELDS
------------------

A hard shield MUST own the actuator capability.

Pipeline:

    Controller
      -> Proposed(Command)

    Shield
      consumes Proposed(Command)
      owns @linear Actuator
      -> Committed(Command)

Required shield claims:

    ShieldSafety

    ShieldTransparencyWhenSafe

    ShieldDeviationBound

    ShieldRecovery

    ShieldResourceBound

A shield MUST execute before the physical output is committed.


PART XII — NUMERICAL AND HYBRID ASSURANCE
========================================


96. IDEAL VERSUS EXECUTABLE NUMERICS
------------------------------------

Every verified numerical implementation SHOULD relate:

    ideal mathematical semantics

to:

    finite executable semantics

Required relation:

    ImplementsApproximately(
      implementation,
      ideal_function,
      input_domain,
      error_model
    )


97. ERROR MODELS
----------------

Supported error models SHOULD include:

    AbsoluteError

    RelativeError

    ULPError

    BackwardError

    IntervalEnclosure

    FixedPointQuantizationError

    SaturatingError


98. NUMERIC CERTIFICATES
------------------------

Required certificate types:

    RangeCertificate

    OverflowCertificate

    FloatingPointErrorCertificate

    FixedPointErrorCertificate

    StabilityCertificate

    MixedPrecisionCertificate


99. FLOATING-POINT REWRITES
---------------------------

Real-number equalities MUST NOT be applied automatically to finite floating
point.

Reassociation, distributivity, and similar rewrites require:

- exactness conditions;
- or an approximation certificate.


100. ROBUSTNESS MARGINS
-----------------------

Cure SHOULD compute margins:

    safety margin

    timing margin

    buffer margin

    numerical margin

    energy margin

System composition SHOULD establish:

    available margin
    - sensor uncertainty
    - numerical error
    - timing jitter
    - plant uncertainty
    > 0


101. HYBRID SYSTEMS
-------------------

Physical-safety profiles MAY define:

    plant state

    continuous dynamics

    uncertainty ranges

    sampling semantics

    actuator hold behavior

    sensor quantization

Required relation:

    ControlsSafely(
      controller,
      plant,
      sampler,
      invariant,
      assumptions
    )

Hybrid verification MUST be optional for ordinary embedded programs.


PART XIII — SECURITY ASSURANCE
==============================


102. NAMED OBSERVATION MODELS
-----------------------------

No unqualified:

    Noninterfering(program)

Required form:

    Noninterfering(
      program,
      secrets,
      observer,
      attacker_model
    )

Observers may include:

- outputs;
- branches;
- memory addresses;
- message sizes;
- timing;
- allocation;
- cache lines;
- peripheral activity;
- power model.


103. DECLASSIFICATION
---------------------

Declassification is a governed effect, not a cast.

It MUST identify:

- information released;
- recipient;
- authority;
- purpose;
- scope;
- expiry;
- audit event.

Example:

    declassify customer_record
      reveal {name, delivery_status}
      authority PrivacyPolicy
      purpose CustomerSupport
      until ticket.closed
      to SupportAgent


104. ENDORSEMENT
----------------

Endorsement converts untrusted data into trusted authority only after validation.

Validation MAY include:

- signature;
- signer authorization;
- freshness;
- replay protection;
- semantic range;
- current mode;
- key revocation status.


105. ROBUST INFORMATION FLOW
----------------------------

Optional hardened profiles SHOULD support named claims:

    RobustDeclassification

    TransparentEndorsement

    NonmalleableInformationFlow

    ProgressSensitiveNoninterference


106. ROBUST COMPILATION
-----------------------

Ordinary source-target trace equivalence is not sufficient when target code links
against unverified contexts.

Compiler security claims MUST name:

- target context class;
- FFI policy;
- memory authority;
- compartment boundary;
- undefined-behavior model.

Secure compilation for verified stateful code linked with unverified mutable
contexts requires explicit protection of which references may be shared.
[arXiv:2503.00404]


107. COMPARTMENTS
-----------------

Logical compartments SHOULD specify:

- owned capabilities;
- exported calls;
- permitted shared memory;
- denied capabilities;
- ingress validation.

Enforcement levels:

    StaticOnly

    LanguageRuntimeChecked

    ProcessIsolated

    MMUOrMPUProtected

    HardwareCapabilityProtected

    PhysicallySeparated


108. SIDE CHANNELS
------------------

Constant-time claims MUST name their leakage model.

A branch-and-address constant-time proof MUST NOT imply:

- cache independence;
- power independence;
- radio independence;
- message-size independence.


109. ATTESTATION
----------------

Attestation SHOULD yield scoped authority:

    AttestedPeer(
      identity,
      measurement,
      freshness,
      policy,
      expiry
    )

It MUST NOT merely yield `Bool`.

Attestation may authorize:

- protocol participation;
- firmware update;
- key release;
- declassification.

Attestation authority MUST be revocable.


PART XIV — CURE LOW AND BACKEND ARCHITECTURE
===========================================


110. CURE LOW
-------------

Cure Low SHOULD be a small imperative systems calculus.

It MUST NOT simply be unrestricted dependent C.

Required classes:

    ImmutableValue

    UniqueValue

    Destination(region, A)

    LocalMutable(region, A)

    ArenaOwned(arena, A)

    SharedAtomic(ordering, A)

    Volatile(A)

    MMIO(device, register, A)

    DMAOwned(channel, A)


111. PREFER THE WEAKEST MEMORY CLASS
------------------------------------

Examples:

    fixed packet construction:
      Destination

    Flow state:
      LocalMutable

    ADC register:
      MMIO

    DMA buffer:
      DMAOwned

Full shared-state separation logic should be needed only for genuinely shared
mutable computation.


112. DRIVER SUPPORT
-------------------

Cure Low SHOULD be designed so realistic drivers can be verified and compiled
without sacrificing predictable low-level semantics.

Pancake demonstrates a practical imperative verification-friendly language
compiled through a verified backend and used for a performant Ethernet driver.
[arXiv:2501.08249]


113. MMIO AND VOLATILE
----------------------

MMIO operations MUST:

- be explicit effects;
- preserve access width;
- preserve access order where required;
- forbid invalid reordering;
- name the device model;
- state read/write side effects.

Volatile does not by itself imply atomicity or synchronization.


114. DMA
-------

DMA buffers require linear ownership.

A buffer in flight MUST NOT be:

- mutated by CPU code;
- freed;
- moved to another DMA channel;
- reused.

DMA completion and cancellation must return ownership explicitly.


115. INTERRUPTS
---------------

Interrupt checking MUST be whole-call-graph.

Required closure report:

    transitive effects

    maximum stack

    maximum work

    touched MMIO

    shared memory

    blocking possibility

    allocation possibility

    unresolved externals

Interrupt rely/guarantee conditions MUST describe interference with normal code.


116. WEAK MEMORY
----------------

Shared-memory native targets MUST name their memory model.

Required primitives:

    Atomic(A, ordering)

    Fence(ordering)

    Volatile(A)

    MMIO(A)

The initial ESP32-C3 deterministic Flow profile SHOULD avoid general shared
memory through single ownership and static scheduling.


117. VERIFIED STATIC FLOW PIPELINE
----------------------------------

Normative aspiration:

    Surface Flow
      ->
    Elaborated Clocked Flow
      ->
    Normalized Flow
      ->
    Scheduled Transition System
      ->
    State-Allocated Transition System
      ->
    Cure Low
      ->
    Native Artifact

Each arrow MUST be:

- verified;
- proof-producing;
- translation validated;
- or explicitly trusted.

The core embedded path SHOULD progressively move toward proof rather than
permanent trust.


118. RELATIONAL COMPILATION
---------------------------

Compiler stages SHOULD be specified as relations:

    Elaborates(Surface, Core)

    Lowers(Flow, CureLow)

    Compiles(CureLow, Machine)

    Represents(Abstract, Concrete)

    Migrates(Old, New)

    Lifts(Target, SourceModel)

For each relation Cure MUST distinguish:

    specification

    forward compiler

    backward lifter

    validator

    synthesizer

The existence of one does not imply the others.


119. CUSTOM REPRESENTATIONS
---------------------------

Representation evidence MUST cover:

- abstraction relation;
- operation preservation;
- size;
- alignment;
- offsets;
- discriminants;
- endianness;
- calling convention;
- padding;
- ownership;
- serialization;
- mutation closure.

Encode/decode round trips alone are insufficient.


120. FFI
--------

FFI declarations MUST state:

- layout;
- ownership;
- aliasing;
- effects;
- blocking;
- allocation;
- callbacks;
- interrupt safety;
- timing;
- failure;
- trust level.

Evidence levels:

    VerifiedImplementation

    TranslationValidated

    AnalyzedBinary

    RuntimeEnforced

    AuditedDeclaration

    UncheckedDeclaration

High-assurance profiles MUST reject `UncheckedDeclaration`.


121. CONTRACT-ENFORCING BOUNDARIES
----------------------------------

For unverified components Cure SHOULD generate:

- input validation;
- output validation;
- copy-in/copy-out;
- capability wrappers;
- memory isolation;
- timeouts;
- watchdogs;
- shields;
- compartments.


PART XV — EMBEDDED EXECUTION
============================


122. NATIVE LOWERING
--------------------

Static Flow MUST NOT lower to one task or process per node by default.

Preferred lowering:

    graph analysis
      ->
    fusion
      ->
    static schedule
      ->
    compact transition machine
      ->
    one or a few fixed tasks


123. MEMORY CERTIFICATE
-----------------------

Every strict embedded build MUST emit:

    memory_certificate {
      static_data
      read_only_data
      Flow_state
      protocol_state
      monitor_state
      shield_state
      queues
      stacks
      arenas
      runtime_reserve
      FFI_buffers
      maximum_dynamic_heap
      total_accounted_RAM
      flash
    }


124. STACK CERTIFICATE
----------------------

Every call path MUST have:

- static bound;
- iterative lowering;
- bounded explicit work stack;
- or deployment rejection.


125. TIMING CERTIFICATE TAXONOMY
-------------------------------

Cure MUST distinguish:

    LogicalWorkCertificate

    InstructionCountCertificate

    CalibratedExecutionCertificate

    TaskResponseTimeCertificate

    InterruptInterferenceCertificate

    ResourceBlockingCertificate

    SystemSchedulabilityCertificate

    EndToEndLatencyCertificate

No implicit promotion is permitted.


126. SCHEDULER MODEL
--------------------

Every real-time certificate MUST bind:

- kernel version;
- scheduler configuration;
- target architecture;
- interrupt controller;
- priority model;
- critical-section model;
- flash/cache model;
- radio interference assumptions;
- clock frequency.

A model for one FreeRTOS port MUST NOT be reused for another without validation.


127. SCHEDULABILITY RESULTS
---------------------------

Required result:

    ProvenSchedulable(model, certificate)

    ProvenUnschedulable(model, counterexample)

    TestInconclusive(test)

    ModelMismatch(details)

    Unknown


128. PERIPHERAL TYPESTATES
--------------------------

Required capability families include:

    GPIO

    UART

    SPI

    I2C

    ADC

    PWM

    Timer

    Watchdog

    DMA

    Interrupt

    FlashPartition

    NVS

    WiFi

    BLE

Each MUST model:

- ownership;
- configuration;
- enabled state;
- conflicts;
- power state where relevant;
- interrupt legality;
- DMA compatibility.


129. ASSURANCE DOMAINS
----------------------

Embedded programs SHOULD separate:

    HardDeterministicDomain

    BestEffortDomain

Networking and telemetry MUST NOT directly own hard-domain actuators.

Communication MUST cross typed bounded channels.


130. ATOMVM
-----------

AtomVM claims require an AtomVM-specific runtime and memory model.

AtomVM MUST NOT inherit BEAM/ERTS resource certificates by analogy.

AtomVM acceptance MAY establish:

- protocol safety;
- process count bounds;
- mailbox policy;
- memory envelope;
- initialization;
- Flow causality.

It MUST NOT automatically imply hard real-time execution.


131. NATIVE
-----------

The strict native profile SHOULD require:

- static Flow topology;
- finite state;
- bounded queues;
- bounded stack;
- total initialization;
- no hidden allocation;
- typed peripherals;
- schedule certificate;
- memory certificate;
- lowering evidence.

Default:

    allocation_after_init == 0


PART XVI — EVIDENCE AND TRUST INFRASTRUCTURE
===========================================


132. CANONICAL CHECKED CORE
---------------------------

The authoritative proof input MUST be a canonical binary representation of
elaborated core.

It MUST include:

- explicit universes;
- explicit coercions;
- explicit dictionaries;
- explicit effects;
- explicit quantities;
- explicit theorem references;
- explicit transparency settings.

Text source is not the authoritative checked identity.


133. STANDALONE CHECKER
-----------------------

Required eventual tool:

    cure-check artifact.cureproof

The checker SHOULD:

- parse only canonical core and certificate formats;
- load no project plugins;
- have no network access;
- use deterministic execution;
- enforce memory limits;
- enforce stack limits;
- emit structured results.


134. CERTIFICATE DISCIPLINE
---------------------------

Certificate producers are untrusted.

Checkers SHOULD recompute every affordable authoritative fact.

Certificates may provide:

- witnesses;
- paths;
- proof DAGs;
- assignments;
- rewrite locations.

Checkers MUST recompute:

- hashes;
- typing;
- theorem applicability;
- side conditions;
- model identity;
- semantics version.


135. CHECKER CLASSIFICATION
---------------------------

Every checker MUST be classified:

    KernelPrimitive

    ProofReconstructing

    VerifiedChecker

    AuditedChecker

    TrustedChecker

A system with many trusted checkers does not have a small effective TCB.


136. EVIDENCE MANIFEST
----------------------

Every bundle MUST include:

    source_hash

    canonical_core_hash

    target_hash

    proposition_hash

    language_semantics_hash

    kernel_rule_set_hash

    universe_theory_hash

    mode_theory_hash

    theorem_registry_hash

    target_semantics_hash

    ABI_hash

    deployment_model_hash

    producer_binary_hash

    checker_binary_hash

    proof_format_version

    assumptions

    transitive_dependencies


137. AXIOM CLOSURE
------------------

Every theorem MUST expose its transitive axiom closure.

Possible entries:

    ClassicalChoice

    FunctionExtensionality

    TrustedFFI

    HardwareAssumption

    ExternalTheorem

    UserAxiom

High-assurance profiles MUST define an axiom allowlist.


138. NO HIDDEN ADMISSION
------------------------

Certified release builds MUST reject:

- unresolved holes;
- `sorry`-equivalent constants;
- unchecked proof stubs;
- missing theorem bodies;
- untracked trusted plugins.

Approved axioms remain possible only as explicit trusted claims.


139. INCREMENTAL CACHE
----------------------

Cache keys MUST cover:

- canonical input artifact;
- all imported interface hashes;
- theorem dependencies;
- transparency policy;
- semantics version;
- compiler version where relevant;
- theory plugins;
- target model.

Caches MUST NOT reuse results based on approximate semantic similarity.

Every high-assurance artifact MUST remain replayable from scratch.


140. CACHE POISONING DEFENCE
----------------------------

Cached proof objects MUST be:

- hash authenticated;
- rechecked on trust-boundary crossing;
- invalidated on dependency change;
- isolated by project/profile where required.

A cache hit is not evidence by itself.


141. FRONT-END VALIDATION
-------------------------

Every front-end stage MUST use:

    verified implementation;

or:

    translation validation;

or:

    redundant independent translation.

Stages include:

- parsing;
- macro expansion;
- name resolution;
- overload resolution;
- implicit resolution;
- coercion insertion;
- pattern elaboration;
- Flow elaboration;
- protocol projection;
- contract elaboration.


PART XVII — PROFILES
====================


142. DEVELOPMENT PROFILE
------------------------

May permit:

- holes;
- partial proofs;
- dynamic checks;
- unknown resource bounds;
- unchecked FFI;
- gradual terms.

It MUST visibly taint all dependent claims.


143. BEAM.DYNAMIC
-----------------

Requires:

- kernel typing;
- explicit effects;
- protocol and mailbox checks where declared;
- explicit FFI trust;
- no hidden proof holes.

May permit:

- dynamic processes;
- garbage collection;
- unbounded mailboxes unless contractually restricted;
- best-effort timing.


144. BEAM.DETERMINISTIC
-----------------------

Adds:

- deterministic logical-time regions;
- schedule-independent observations inside those regions;
- explicit asynchronous boundaries;
- replay identity;
- declared mailbox and queue policies.


145. EMBEDDED.ATOMVM
--------------------

Adds:

- finite process count in bounded domains;
- explicit mailbox capacities;
- finite application state;
- total startup;
- causality and productivity;
- AtomVM-specific memory envelope.


146. EMBEDDED.NATIVE
--------------------

Adds:

- static lowering;
- bounded stack;
- bounded memory;
- static queues;
- explicit overflow;
- typed hardware;
- no post-init allocation by default;
- target-bound schedule and lowering evidence.


147. EMBEDDED.INTERMITTENT
-------------------------

Adds:

- persistent/volatile distinction;
- power-loss atomicity;
- commit detection;
- fresh input after restart;
- intermittent equivalence.


148. DISTRIBUTED.RESILIENT
-------------------------

Adds:

- explicit fault model;
- synchrony model;
- fairness model;
- failure-detector contract;
- detectable commits;
- reconfiguration safety;
- optional self-stabilization.


149. SECURITY.HARDENED
----------------------

Adds:

- named attacker;
- named leakage model;
- declassification/endorsement policy;
- compartment enforcement;
- robust compilation claim;
- artifact provenance;
- attested deployment where supported.


150. PROFILE REQUIREMENTS
-------------------------

Every profile requirement MUST specify:

    proposition

    accepted evidence classes

    model

    permitted assumptions

    target scope

    freshness

    failure policy

Example:

    requirement UniversalMemoryBound {
      accepts:
        Proof
        VerifiedCertificate

      rejects:
        Measurement
        TestEvidence
        StatisticalEvidence
    }


PART XVIII — SEMANTIC CONTINUITY
===============================


151. OBSERVER-INDEXED COMPATIBILITY
-----------------------------------

Compatibility MUST name its observer.

Examples:

    ValueCompatible

    PublicAPICompatible

    TraceCompatible

    ProtocolCompatible

    TimingCompatible

    ResourceCompatible

    SecurityCompatible

    WireCompatible

No unqualified:

    SemanticallyCompatible


152. EQUIVALENCE CLASSES
------------------------

Required relations:

    ValueEquivalent

    TraceEquivalent

    ResourceEquivalent

    TimingEquivalent

    SecurityEquivalent

    WireEquivalent

    FailureEquivalent

Proofs transport only if their propositions are invariant under the supplied
equivalence.


153. PROOF REPAIR
-----------------

Cure MAY transport proofs across:

- declared equivalences;
- refinements;
- ornaments;
- representation relations.

It MUST NOT claim general automatic proof repair.

Every repaired proof MUST be kernel rechecked.


154. HOT UPGRADES
-----------------

Upgrade evidence MUST cover:

- application state;
- session state;
- mailbox contents;
- timers;
- capabilities;
- pending effects;
- commit frontiers;
- monitor state;
- runner state;
- mixed code versions.

Upgrade classes:

    ImmediatelySafe

    SafeAt(state)

    RequiresDrain

    RequiresCheckpoint

    RequiresRestart

    Impossible


155. SEMANTIC REGRESSION
------------------------

CI SHOULD compare:

- types;
- effects;
- captures;
- assumptions;
- guarantees;
- resource bounds;
- timing bounds;
- wire formats;
- fault tolerance;
- evidence classes;
- robustness margins.

A public type remaining identical does not imply semantic compatibility.


PART XIX — RED-TEAM INFRASTRUCTURE
=================================


156. METATHEORY INTERACTION MATRIX
----------------------------------

Maintain a matrix over:

    universes
    equality
    inductives
    refinements
    quantities
    erasure
    subtyping
    protocols
    effects
    handlers
    partiality
    pattern matching
    modules
    captures
    clocks
    custom representations
    FFI
    staging
    reflection

For each relevant pair and triple record:

    typing rules

    substitution status

    preservation status

    conversion status

    erasure status

    operational semantics

    implementation status

    Antigen coverage

    known counterexamples


157. ANTIGEN ASSAY FAMILIES
---------------------------

Antigen MUST attack:

- universe inconsistencies;
- positivity bypass;
- constructor injectivity;
- termination bypass;
- erased divergence;
- erased effects;
- erased pattern dependence;
- linear aliasing;
- continuation duplication;
- destructor skipping;
- capability revocation;
- implicit coercion diamonds;
- typeclass ambiguity;
- pattern coverage;
- stale proof caches;
- stale certificates;
- FFI ownership lies;
- mailbox starvation;
- protocol interference;
- schedule model mismatch;
- numerical rewrite unsoundness;
- ABI padding;
- upgrade effect duplication.


158. DIFFERENTIAL SEMANTICS
---------------------------

Where possible compare:

    reference kernel

    production kernel

    pure evaluator

    Flow stream interpreter

    Flow transition interpreter

    actor interpreter

    Core Erlang execution

    Cure Low interpreter

    generated C

    target hardware trace


159. PROOF MUTATION
-------------------

Mutate:

- proof nodes;
- theorem identifiers;
- universe levels;
- source hashes;
- target hashes;
- side conditions;
- certificates;
- artifacts;
- mode theories;
- schedule assumptions.

Every meaningful mutation MUST be rejected.


160. ADVERSARIAL COMPILER RESOURCES
-----------------------------------

The compiler MUST defend against:

- exponential normalization;
- proof-term explosion;
- metavariable cycles;
- unification blowups;
- certificate bombs;
- diagnostic rendering bombs;
- cache invalidation storms.

Budget exhaustion returns `Unknown`, never acceptance.


PART XX — IMPLEMENTATION GATES
==============================


GATE 0 — CORE CONSTITUTION
--------------------------

Produce a normative formal document defining:

- universes;
- equality;
- quantities;
- erasure;
- inductives;
- eliminators;
- recursion;
- opacity;
- canonical core.


GATE 1 — REFERENCE KERNEL
-------------------------

Implement:

- bidirectional checker;
- explicit core;
- bounded conversion;
- canonical serialization;
- theorem dependency tracking.


GATE 2 — CORE METATHEORY
------------------------

Establish or mechanize:

- weakening;
- substitution;
- subject reduction;
- injectivity;
- normalization;
- conversion correctness;
- erasure correctness.


GATE 3 — INDUCTIVES AND PATTERNS
--------------------------------

Implement:

- strict positivity;
- universe checking;
- eliminators;
- certified pattern elaboration;
- coverage evidence.


GATE 4 — TOTALITY AND PARTIALITY
--------------------------------

Implement:

- total recursion;
- separate partial computation;
- hole tainting;
- certified-build rejection of holes.


GATE 5 — IDENTITY-ONLY SUBSUMPTION
----------------------------------

Before further subtyping work:

- remove `Int <: Float`;
- classify all subtype rules;
- make adapters explicit;
- check coercion coherence;
- restrict covariance to identity inclusions.


GATE 6 — MODULE ABSTRACTION
---------------------------

Implement:

- opaque interfaces;
- abstraction relations;
- controlled unfolding;
- representation independence;
- instance coherence.


GATE 7 — DEPENDENT COMPUTATION CORE
-----------------------------------

Implement:

- value/computation separation;
- effects;
- indexed operations;
- direct-style elaboration;
- weakest-precondition interpretation.


GATE 8 — CONTROL-FLOW LINEARITY
-------------------------------

Implement:

- continuation quantities;
- one-shot default;
- multi-shot restrictions;
- handler resource accounting.


GATE 9 — RUNNERS AND CLEANUP
----------------------------

Implement:

- runners;
- destructors;
- cancellation;
- finalization;
- revocation;
- external-resource ownership.


GATE 10 — CLAIM AND EVIDENCE SYSTEM
-----------------------------------

Implement:

- evidence classes;
- claim dependencies;
- axiom closure;
- standalone checker;
- evidence manifests.


GATE 11 — CONTRACT QUALITY
--------------------------

Implement:

- assumptions/guarantees;
- composition;
- satisfiability;
- realizability;
- vacuity;
- requirement traceability.


GATE 12 — STATIC FLOW
---------------------

Implement:

- stream semantics;
- transition semantics;
- graph IR;
- clocks;
- pacing;
- initialization;
- guarded cycles;
- deterministic scheduling.


GATE 13 — CURE LOW
------------------

Implement:

- destination memory;
- local mutation;
- arenas;
- stack objects;
- MMIO;
- DMA;
- interrupts.


GATE 14 — ESP32-C3 NATIVE
-------------------------

Implement:

- static schedule;
- static memory;
- stack certificate;
- peripheral runners;
- C or RISC-V lowering;
- linker validation.


GATE 15 — MAILBOX-NATIVE ACTORS
-------------------------------

Implement:

- exact BEAM selective receive;
- mailbox types;
- actor references;
- resource potential;
- cross-session analysis.


GATE 16 — CORE ERLANG BACKEND
-----------------------------

Implement:

- supported subset;
- actor-to-Core-Erlang relation;
- bytecode validation;
- trust split.


GATE 17 — DURABLE EFFECTS
-------------------------

Implement:

- effect IDs;
- commit lifecycle;
- frontiers;
- durable actor runner;
- unknown commit status.


GATE 18 — RUNTIME ASSURANCE
---------------------------

Implement:

- knowledge semantics;
- finite observations;
- distributed ordering;
- shield placement;
- monitor lowering validation.


GATE 19 — NUMERICAL ASSURANCE
-----------------------------

Implement:

- ideal/executable relations;
- range/error certificates;
- fixed point;
- restricted float rewrites.


GATE 20 — ADVANCED PROFILES
---------------------------

Only after preceding gates:

- hybrid plants;
- probabilistic verification;
- self-stabilization;
- Byzantine protocols;
- intermittent execution;
- robust secure compilation;
- hardware capability targets.


PART XXI — NON-GOALS AND PROHIBITIONS
====================================


161. NO TYPE-IN-TYPE
--------------------

The kernel MUST NOT support `Type : Type`.


162. NO GENERAL EQUALITY REFLECTION
----------------------------------

Proved equality MUST NOT silently become definitional equality.


163. NO EFFECTFUL CONVERSION
----------------------------

Conversion MUST NOT execute effects or partial computations.


164. NO HIDDEN APPROXIMATION
----------------------------

Numerical or representation loss MUST be explicit.


165. NO GENERAL IMPLICIT CONVERSIONS
------------------------------------

Only identity-preserving inclusions may be implicit.


166. NO UNCHECKED PATTERN COVERAGE
---------------------------------

Surface exhaustiveness is not kernel evidence.


167. NO SILENT HOLES
-------------------

Incomplete proof terms MUST remain visible and profile-rejected.


168. NO MONITOR-AS-PROOF CONFUSION
---------------------------------

Finite observations do not generally establish infinite behavior.


169. NO ONE-PROCESS-PER-FLOW-NODE EMBEDDED LOWERING
----------------------------------------------------

Static Flow should fuse.


170. NO HARD-REALTIME CLAIM WITHOUT A DEPLOYMENT MODEL
------------------------------------------------------

Timing is model-relative.


171. NO SESSION-TYPE MARKETING WITHOUT BEAM SEMANTICS
-----------------------------------------------------

Selective receive, mailbox scanning, and inter-session interference must be
modeled.


172. NO EXACTLY-ONCE CLAIM WITHOUT COMMIT DETECTABILITY
-------------------------------------------------------

Recovery ambiguity must be typed.


173. NO SECURITY PROPERTY WITHOUT AN ATTACKER AND OBSERVER
---------------------------------------------------------

Security is model-relative.


174. NO "SMALL TCB" CLAIM THAT IGNORES CHECKERS
----------------------------------------------

Trusted plugins count.


175. NO SEMANTIC-COMPATIBILITY CLAIM WITHOUT AN OBSERVER
-------------------------------------------------------

Compatibility is relational and scoped.


176. NO PROOF-REPAIR CLAIM WITHOUT A DECLARED RELATION
------------------------------------------------------

Transport is not arbitrary repair.


177. NO PAPER-NAME-DRIVEN ASSURANCE
-----------------------------------

Research adoption MUST record:

    adopted theorem

    assumptions

    Cure correspondence

    differences

    lost guarantees

    new obligations

A feature is not verified because it resembles a paper.


PART XXII — DEFINITIVE ARCHITECTURE
==================================


Cure Evidential Systems
|
+-- Pure Intensional Quantitative Dependent Kernel
|   |
|   +-- explicit predicative universes
|   +-- intensional equality
|   +-- strict inductive families
|   +-- total reduction
|   +-- quantitative use
|   +-- explicit erasure
|   +-- certified conversion
|
+-- Surface Elaboration Boundary
|   |
|   +-- bidirectional elaboration
|   +-- explicit coercions
|   +-- pattern coverage certificates
|   +-- coherent protocol resolution
|   +-- macro correspondence
|
+-- Module and Abstraction System
|   |
|   +-- opaque interfaces
|   +-- abstraction relations
|   +-- controlled unfolding
|   +-- representation independence
|   +-- behavior/cost separation
|
+-- Dependent Computation Core
|   |
|   +-- value/computation separation
|   +-- algebraic effects
|   +-- indexed effects
|   +-- control-flow linearity
|   +-- handlers
|   +-- runners
|   +-- destruction
|   +-- cancellation
|   +-- revocation
|
+-- Explicit Conversion System
|   |
|   +-- identity inclusion
|   +-- proof forgetting
|   +-- adapters
|   +-- approximation
|   +-- validation
|
+-- Contract and Specification System
|   |
|   +-- stratified contract theories
|   +-- composition
|   +-- quotient
|   +-- realizability
|   +-- non-vacuity
|   +-- requirement traceability
|
+-- Domain Calculi
|   |
|   +-- deterministic multiclock Flow
|   +-- mailbox-native actors
|   +-- global protocols
|   +-- verified formats
|   +-- hardware typestate
|   +-- persistence
|   +-- distributed coordination
|   +-- numerical approximation
|   +-- hybrid plants
|   +-- security
|
+-- Cure Low
|   |
|   +-- destination memory
|   +-- local mutation
|   +-- arenas
|   +-- MMIO
|   +-- DMA
|   +-- interrupts
|   +-- atomics
|
+-- Relational Compiler
|   |
|   +-- Flow lowering
|   +-- Core Erlang lowering
|   +-- BEAM validation
|   +-- native lowering
|   +-- representation relations
|   +-- migration
|   +-- semantic regression
|
+-- Runtime Assurance
|   |
|   +-- knowledge-based monitors
|   +-- partial observations
|   +-- safety shields
|   +-- degradation policies
|
+-- Evidence Infrastructure
    |
    +-- proof terms
    +-- certificate plugins
    +-- standalone checker
    +-- canonical artifacts
    +-- axiom closure
    +-- evidence provenance
    +-- content-addressed caches
    +-- assurance-case graph


FINAL PUBLIC VISION
===================

Cure should eventually make the following promise:

    Cure separates mathematical truth from effectful execution.

    It distinguishes identity-preserving inclusion from conversion,
    approximation, and validation.

    It protects clients from private representations.

    It checks that specifications are satisfiable, realizable, and non-vacuous.

    It models actor mailboxes and target runtimes as they actually behave.

    It tracks cleanup, cancellation, revocation, crashes, and uncertain commits.

    It proves or explicitly bounds every compiler, scheduling, numerical,
    protocol, and deployment assumption required by a claimed profile.

    A Cure build is not "verified" in the abstract.

    It is accepted only for a named profile when every required claim is
    supported by an admissible proof, checked certificate, monitored
    assumption, or explicit trusted boundary.


CORE RESEARCH BIBLIOGRAPHY
==========================

Kernel and conversion:

    What Does It Take to Certify a Conversion Checker?
    arXiv:2502.15500
    https://arxiv.org/abs/2502.15500

    Martin-Löf à la Coq
    arXiv:2310.06376
    https://arxiv.org/abs/2310.06376

    An Extensible Equality Checking Algorithm for Dependent Type Theories
    arXiv:2103.07397
    https://arxiv.org/abs/2103.07397

    Type Theory with Explicit Universe Polymorphism
    arXiv:2212.03284
    https://arxiv.org/abs/2212.03284

Erasure and stratification:

    Type Theory With Erasure
    arXiv:2605.00655
    https://arxiv.org/abs/2605.00655

    A Two-Level Linear Dependent Type Theory
    arXiv:2309.08673
    https://arxiv.org/abs/2309.08673

    A Graded Modal Dependent Type Theory with Erasure
    arXiv:2603.29716
    https://arxiv.org/abs/2603.29716

Patterns and definitions:

    Coverage Semantics for Dependent Pattern Matching
    arXiv:2501.18087
    https://arxiv.org/abs/2501.18087

    Controlling Unfolding in Type Theory
    arXiv:2210.05420
    https://arxiv.org/abs/2210.05420

Abstraction and cost:

    Abstraction Functions as Types
    arXiv:2502.20496
    https://arxiv.org/abs/2502.20496

    Logical Relations as Types
    arXiv:2010.08599
    https://arxiv.org/abs/2010.08599

    A Cost-Aware Logical Framework
    arXiv:2107.04663
    https://arxiv.org/abs/2107.04663

    Decalf
    arXiv:2307.05938
    https://arxiv.org/abs/2307.05938

Effects and linearity:

    A Framework for Dependent Types and Effects
    arXiv:1512.08009
    https://arxiv.org/abs/1512.08009

    Soundly Handling Linearity
    arXiv:2307.09383
    https://arxiv.org/abs/2307.09383

    Runners in Action
    arXiv:1910.11629
    https://arxiv.org/abs/1910.11629

Actors and protocols:

    Special Delivery: Programming with Mailbox Types
    arXiv:2306.12935
    https://arxiv.org/abs/2306.12935

    Implementability of Global Distributed Protocols modulo Network
    Architectures
    arXiv:2602.10320
    https://arxiv.org/abs/2602.10320

    A Formalisation of Core Erlang
    arXiv:2311.10482
    https://arxiv.org/abs/2311.10482

Runtime assurance:

    Semantics for Linear-Time Temporal Logic with Finite Observations
    arXiv:2411.14581
    https://arxiv.org/abs/2411.14581

Low-level verification:

    Verifying Device Drivers with Pancake
    arXiv:2501.08249
    https://arxiv.org/abs/2501.08249

Implicit coherence:

    Coherence of Type Class Resolution
    arXiv:1907.00844
    https://arxiv.org/abs/1907.00844

    On the State of Coherence in the Land of Type Classes
    arXiv:2502.20546
    https://arxiv.org/abs/2502.20546

Incrementality:

    DeCo: A Core Calculus for Incremental Functional Programming
    arXiv:2602.20866
    https://arxiv.org/abs/2602.20866
