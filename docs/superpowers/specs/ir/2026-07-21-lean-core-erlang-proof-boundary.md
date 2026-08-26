# Lean/Core Erlang Proof Boundary

**Status:** Normative design specification  
**Parent:** `2026-07-21-lean-verified-middle-end-design.md`

## 1. Purpose

This document defines what Lean proves about the Core Erlang backend and what
remains trusted outside Lean. The target is a versioned Core Erlang subset, not
the unstable OTP `cerl` constructor API and not BEAM bytecode.

## 2. Lean target datatype

Lean defines a Cure-owned Core Erlang AST with explicit constructors for the
supported subset:

```text
module, function, variable, literal, tuple,
let, letrec, call, apply, case, receive,
send, spawn, exit, primitive call
```

The datatype is independent of OTP's internal Erlang term representation.
An adapter later maps the checked AST to OTP constructors or textual Core
Erlang.

The target grammar is pinned to an explicitly recorded OTP/Core Erlang version
for each release. A target constructor is not supported merely because an OTP
`cerl` helper happens to accept it.

## 3. Well-formedness

The target API exposes only checked terms:

```text
WellFormedCore : CoreTerm → Prop
```

Checks include:

- unique and correctly scoped variables;
- function arity and call compatibility;
- valid recursion bindings;
- valid case/receive branches;
- legal literals and constructor shapes;
- explicit process primitive signatures;
- absence of macro/runtime interpreter nodes;
- absence of opaque unlowered Cure computation containers.

## 4. Source-to-target relation

The first relation is defined between validated canonical Cure Core and Lean's
Core Erlang AST:

```text
Lowered : CureCore → CoreErlang → Prop
```

The compiler returns a target plus evidence:

```text
compile : (source : ValidatedCore) → Result {
  target : CoreErlang,
  wellFormed : WellFormedCore target,
  certificate : Lowered source target
} Diagnostic
```

Proof terms may be erased from the emitted file, but compilation succeeds only
after Lean has checked them.

## 5. Semantic reference

The relevant Core Erlang semantics are ported from the existing Rocq
formalisation in stages:

1. values, expressions, environments, functions;
2. sequential evaluation for the emitted subset;
3. frame-stack semantics;
4. process and mailbox semantics;
5. trace/bisimulation relation.

The port must record correspondence notes to the Rocq definitions. It must not
claim equivalence for constructs outside the ported subset.

## 6. Preservation theorems

### 6.1 Pure terms

For pure canonical terms:

```text
evalCure c = v
→ evalCoreErlang (compile c) = v
```

The first proof target is an evaluation correspondence for literals, lets,
functions, calls, cases, tuples, and recursion.

### 6.2 Computations and effects

For computations, use a result-and-trace semantics:

```text
evalCure c = trace τ, result r
→ evalCoreErlang (compile c) = trace τ', result r'
```

The theorem states the chosen trace equivalence between `τ` and `τ'`, including
primitive operations, suspension, failure, and actor actions.

### 6.3 Flow lowering

The Flow proof is composed with target lowering:

```text
Cure computation
  ≈ Flow machine
  ≈ Core Erlang dispatch
```

The middle theorem must account for frame ownership and cleanup, not merely
returned values.

### 6.4 Actors

For concurrent programs, use a stated weak-bisimulation or observable-trace
relation. Sequential determinism does not imply actor equivalence because
scheduling and mailbox arrival are observable.

## 7. Backend adapter

The OTP adapter is outside the semantic Lean AST. It must:

- serialize only `WellFormedCore` terms;
- target an explicitly recorded OTP/Core Erlang version;
- reject unsupported constructors;
- run OTP acceptance tests;
- preserve source-origin metadata in debug builds where possible.

The adapter must not add Cure semantics, perform macro expansion, interpret IR,
or introduce opaque OTP container classes. It is a representation adapter only.
The initial printer is trusted but must be checked by deterministic parse-back
and structural comparison against the Lean AST. A future Lean printer may
prove a `parse(print t) = t` theorem for the supported grammar.

The initial release gate is:

```text
Lean Core AST
  → deterministic printer
  → OTP Core Erlang parser
  → normalized structural comparison
```

The printer, parser version, and normalization rules are recorded with every
generated artifact. Parse success alone is not a proof that the printer
preserved the Lean AST.

## 8. Trust claims

### Proven by Lean

- canonical Core validation;
- IR typing and effect preservation;
- handler/continuation checks in the supported fragment;
- Flow transition correctness;
- target AST well-formedness;
- source-to-target semantic correspondence for formalized constructs.

### Trusted initially

- existing Cure parser and elaborator;
- Lean kernel and Lean executable runtime;
- JSON transport and process launcher;
- OTP Core Erlang parser/compiler;
- BEAM runtime and AtomVM runtime;
- target foreign primitives.

The compiler documentation must report these categories separately.

## 9. Differential and regression gates

Every supported construct has:

- a canonical Core JSON fixture;
- a Lean evaluator result or trace;
- a generated Core Erlang fixture;
- OTP compilation/execution output;
- a proof or explicitly documented unproved test relation.

The initial gate runs pure examples, one primitive effect, one suspension,
one one-shot resumption, and one actor mailbox trace. Unsupported constructs
must fail closed with stable diagnostics.

## 10. Future trust reduction

The proof boundary expands by:

1. having the host elaborator emit Lean-checkable certificates;
2. moving canonical Core elaboration into Lean or bootstrapped Cure;
3. formalizing macros as compile-time transformations;
4. formalizing more Core Erlang concurrency and OTP primitives;
5. independently verifying or replacing the Core Erlang-to-BEAM backend.

Direct BEAM bytecode emission is a separate target and must not weaken this
boundary.
