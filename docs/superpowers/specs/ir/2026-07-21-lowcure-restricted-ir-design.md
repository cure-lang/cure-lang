# LowCure Restricted IR

**Status:** Design specification  
**Date:** 2026-07-21  
**Related:**

- `2026-07-21-multiple-irs-architecture-design.md`
- `2026-07-21-lean-verified-middle-end-design.md`
- `2026-07-21-cure-flow-machine-semantics.md`
- `../ownership/2026-07-20-ownership-and-unique-types-design.md`

## 1. Decision

LowCure is a restricted, ownership-aware target profile of Cure. It is not a
second surface language and it is not a replacement for the general Cure
Computation or Flow IRs.

The pipeline for C, Rust, Wasm, and ESP32 targets is:

```text
Typed Cure Computation IR
  → Handler/Continuation IR
  → Defunctionalized Flow IR
  → Concurrency/Capability IR
  → LowCure IR
       ├→ C11/C89
       ├→ Rust
       ├→ CFlat/Wasm
       └→ C/ESP32 scheduler ABI
```

The MCU-oriented profile narrows this pipeline further. General handlers and
first-class resumptions may exist in preceding Cure IRs, but they must be
eliminated before entering LowCure:

```text
Typed Computation IR
  → defunctionalized Flow IR
  → pure Flow/Request IR
  → LowCure
  → C/Rust/ESP32 runtime
```

The state in this pipeline is an explicit, named state-machine continuation,
not an algebraic resumption or a native stack that must be unwound.

The BEAM path branches before LowCure:

```text
Flow/Concurrency IR → Core Erlang → OTP/BEAM
```

LowCure exists to make a program's memory, control, ownership, and foreign
effects sufficiently explicit that a C or Rust backend can be straightforward,
fast, and amenable to stack allocation. It is also a static capability profile:
programs that cannot meet its restrictions remain valid Cure programs but are
not LowCure programs.

## 2. Karamel/Low* precedent

KaRaMeL is the primary implementation comparison for this design. The local
clone is `/Users/ch/Develop/algebraic-effects/karamel` at
`0a39f5a21cb79993c5780b5da24a2f28afbef634`.

Its `DESIGN.md` describes a staged process that:

1. loads an input AST and creates a typed internal AST;
2. inlines type abbreviations and monomorphizes data types/functions;
3. removes tuples and high-level pattern matching;
4. simplifies data representations into enums, structs, switches, and bindings;
5. converts expressions into a statement-oriented form;
6. performs conservative stack-oriented inlining and usage analysis;
7. establishes an informal Low* invariant;
8. lowers to C*, abstract C, and C text, or branches to CFlat/Wasm.

KaRaMeL demonstrates that a restricted target profile is most useful after
high-level type/data/control transformations, not as a second source language.
It also demonstrates the value of separate C*, C, and CFlat/Wasm target layers.

KaRaMeL's Low* invariant is not itself Cure's ownership system. Its current
compiler performs usage analysis and storage/layout transformations, while
Low* and F* specifications provide the deeper memory guarantees. LowCure must
make Cure's ownership and continuation obligations explicit and checked before
the target backend.

## 3. LowCure legality profile

A `LowCureProgram` is a typed Flow/Concurrency program together with a proof or
checked certificate of the following properties.

### 3.1 First-order control

- no higher-order continuation remains;
- every required cross-step continuation is already a named Flow state with a
  fixed capture layout;
- no dynamic handler interpreter remains;
- no source macro, syntax object, or runtime macro dispatcher remains;
- recursion is represented by named calls or explicit loops;
- suspension is an explicit transition to an outer scheduler/runtime ABI.

Function pointers are permitted only when their signature, capture policy, and
ownership behavior are explicit. An arbitrary closure environment is not a
LowCure value.

### 3.2 Monomorphic target data

Before LowCure:

- type abbreviations are expanded;
- generic functions and data types are specialized or have a closed target
  representation;
- tuple and anonymous product layouts are made explicit;
- pattern matching is compiled to constructors, tags, switches, and branches;
- recursive data types require explicit indirection and a declared storage
  policy;
- every runtime layout has a known size/alignment formula or an explicit
  dynamically sized representation.

LowCure may retain type names for diagnostics, but target layout cannot depend
on unresolved type variables or dependent proof terms.

### 3.3 Explicit storage classes

Every allocated or addressable value has one storage class:

```text
Stack(frame)          owned by the current Flow/function frame
Region(region)        owned by a lexical or scheduler region
OwnedHeap             explicitly owned dynamic allocation
SharedRuntime         runtime-managed shared object
Foreign(capability)   storage owned by a declared foreign capability
Static                 immutable program/data segment
```

Storage class is not a runtime tag. It is a checked static property that may
determine target representation.

### 3.4 Explicit effects

LowCure has a closed residual effect set. Abstract handlers and open effect-row
variables must be resolved before entry unless a target runtime explicitly
supports the operation.

Residual effects may include only declared target capabilities such as:

```text
Foreign(capability)
Scheduler(yield/resume)
Concurrency(send/receive/spawn/exit)
Failure(exception/abort)
```

These residual effects belong to the surrounding program, scheduler, and
capability layers. They are not effects of a pure Flow transition. In
particular, ordinary `send`/`receive` and device operations are represented at
the graph/runtime boundary; `Signal.Remote` is the checked typed message edge
available to Flow.

`Suspend` is lowered to an explicit transition record or scheduler call. It is
not implemented by requiring native stack unwinding.

### 3.5 Flow purity and the MCU effect boundary

Flow is pure for every target profile. This is a semantic property of the Flow
model, not an ESP32-specific restriction. A Flow is a signal-graph
computation: each state consumes typed signal/input data and produces typed
signal/output data and an explicit next state. It may calculate results and
update its owned state, but it does not directly perform foreign, device,
scheduler, mailbox, filesystem, clock, or other ambient effects.

The only Flow-level bridge is `Signal.Remote`. `Signal.Remote` is a typed
transport operation between VM domains. It does not execute an arbitrary
effect in the Flow and is not an escape hatch for foreign calls; it constructs
or emits a message whose schema, destination capability, ownership, and
failure behavior are checked. The remote VM receives that message as typed
input and performs its own pure Flow computation or handles it at its own
explicit program/capability boundary.

Conceptually:

```text
FlowState × Signal<Input>
  → Pure(Signal<Output>* × NextState)
```

with `Signal.Remote` represented as a typed graph edge/message action whose
transport is supplied by the surrounding VM runtime.

LowCure-ESP32 and similarly restricted MCU profiles impose a further target
requirement on this already-pure model: device and runtime effects must be
requested through the outer `program` layer or an explicitly declared
capability owner. A Flow state may construct a typed request, but it may not
interpret or perform that request itself.

The pure transition has the conceptual form:

```text
FlowState × Input → Pure(State × Request*)
```

Requests are ordinary typed data, for example:

```text
Request =
    ReadSensor(SensorId)
  | WriteGPIO(Pin, Value)
  | StartTimer(Duration)
  | SendMessage(Process, Message)
```

The outer `program` layer, or an explicitly declared capability owner, handles
these requests and feeds typed responses or failure events back into the Flow.
This is an effect boundary, not a hidden global `World` token. Capabilities
remain explicit and independently typed: GPIO, timers, storage, messaging, and
other device services must be declared and owned by the code that interprets
them.

Remote signalling is separate from capability interpretation. A remote signal
may cross a VM boundary, but it remains a typed message transition; it does not
grant the receiving Flow implicit authority to perform the sender's effects.

The general Cure `Effect` monad remains valid at this boundary. It provides
sequencing, failure, resource cleanup, and capability interpretation for the
program layer. It does not require runtime monad objects: `bind` may lower to
direct control flow or an explicit outer scheduler state machine.

An effect request that needs a result is represented as an explicit protocol:

```text
Flow state
  → pure request
  → program performs capability effect
  → response or failure event
  → named Flow state
```

The final arrow is an ordinary state transition with a fixed frame layout. It
is not a general algebraic continuation, continuation clone, or stack unwind.

The `program` macro is compile-time syntax for generating this direct request
dispatcher and capability plumbing. It must not introduce a runtime syntax
interpreter, opaque effect container, or dynamic macro dispatcher.

## 4. Ownership and usage

LowCure adopts the separate axes from Cure's ownership design:

```text
usage:     unrestricted | affine | linear
ownership: shared | unique | borrowed
```

They must not be collapsed into one “linear” flag.

### 4.1 Ownership forms

Conceptually:

```text
Own<T>          unique movable owner
Borrow<'r, T>   shared read-only view bounded by region 'r
BorrowMut<'r,T> exclusive mutable view bounded by region 'r
Shared<T>       freely aliased runtime value
```

These are static capabilities. They need not become runtime wrappers.

### 4.2 LowCure ownership rules

The checker rejects:

- use after move or transfer;
- more than one live unique owner;
- storing a borrow beyond its region;
- sending a borrow across a process boundary;
- returning a stack-owned reference to an outer scope;
- placing a non-`Send` owned value into a message;
- dropping a linear cleanup/resource obligation;
- duplicating a one-shot Flow frame.

An operation must declare its ownership behavior:

```text
borrow        preserves owner
consume       destroys owner
return-own    consumes and returns a new/state-refined owner
transfer      consumes sender owner and creates receiver owner
share         requires a shared value or explicit runtime conversion
```

Failure behavior is part of the operation contract. A failed transfer either
preserves the source owner or produces an explicit recovery/poisoned state; it
must not silently lose ownership.

### 4.3 Continuation ownership

General LowCure resumptions are initially one-shot or affine. A frame is either
consumed, aborted with cleanup, or transferred to one scheduler owner.
Multi-shot continuation cloning is outside the first LowCure profile because it
conflicts with unique resources and stack allocation unless an explicit
persistent/clone policy is provided.

The MCU profile is stricter: no general continuation value enters LowCure at
all. A Flow state is a defunctionalized, named control state with a statically
known capture layout. It may be retained by the scheduler or represented in a
message protocol, but it cannot be duplicated, inspected as a function, or
resumed through a dynamically chosen handler. The ownership proof applies to
the state record and its captures.

This distinction is intentional:

```text
general Cure: algebraic handlers and resumptions are expressible
LowCure:     only explicit first-order state transitions remain
MCU profile: effects are requested by pure Flow and interpreted outside it
```

## 5. LowCure IR syntax

LowCure is statement/control oriented and resembles a typed, ownership-aware
machine IR rather than a source expression language.

```text
LowProgram = {
  types : LayoutDecl*,
  regions : RegionDecl*,
  functions : LowFunction*,
  capabilities : CapabilityDecl*
}

LowFunction = {
  name,
  parameters : Place*,
  locals : LocalDecl*,
  entry : BlockId,
  blocks : Block*,
  result : LowType,
  effects : ClosedEffectSet
}

Block = {
  id,
  statements : Statement*,
  terminator : Terminator
}
```

```text
Statement ::= let(place, RValue)
            | move(place, place)
            | copy(place, place)
            | borrow(place, place, BorrowKind, Region)
            | load(place, place)
            | store(place, RValue)
            | construct(place, Constructor, Place*)
            | drop(place)
            | call(place*, Function, Place*)
            | primitive(place*, Capability, Place*)

Terminator ::= return(Place*)
             | jump(BlockId, Place*)
             | branch(Place, BlockId, BlockId)
             | switch(Place, Case*)
             | suspend(Operation, Place*, ResumeState)
             | send(Place, Message, BlockId)
             | receive(Pattern*, BlockId)
             | spawn(Function, Place*, BlockId)
             | fail(Failure)
```

`Place` identifies a checked local, field, region location, or explicit foreign
memory location. RValues do not hide allocation or effectful computation.

## 6. Lowering into LowCure

### 6.1 Flow normalization

Defunctionalized Flow states become LowCure blocks/functions. Captured fields
become explicit frame layouts. A scheduler suspension becomes a `suspend`
terminator carrying a typed `ResumeState`.

### 6.2 Data representation lowering

Data lowering follows the Karamel pattern:

```text
polymorphic data
  → specialized data
  → explicit enum/struct/union layout
  → tag/switch/field operations
```

The LowCure checker proves that every constructor and field access agrees with
the selected layout. Recursive data must use an explicit pointer/region/heap
representation; infinitely sized by-value types are rejected.

### 6.3 Expression-to-statement lowering

Nested expressions are converted to ordered statements and explicit blocks.
This fixes evaluation order before C/Rust lowering and makes ownership uses
visible to the checker.

### 6.4 Storage resolution

For each value, the lowering chooses a storage class using ownership and escape
analysis:

```text
non-escaping, fixed-size, owner-local value  → Stack
lexically bounded shared temporary          → Region
escaping dynamic value                      → OwnedHeap
shared runtime/actor value                  → SharedRuntime
foreign buffer/capability                   → Foreign
```

Stack allocation is legal only when size is known or statically bounded, no
borrow/owner escapes the frame, no callback/process receives the address, and
all cleanup occurs before frame exit.

The checker must reject a stack choice if later Flow transitions can retain the
value.

### 6.5 Control lowering

Handlers must be resolved before LowCure. A local handler may become ordinary
blocks. An outer-loop suspension becomes a state transition. No abstract
handler row or continuation closure survives into LowCure.

### 6.6 Request/response lowering for MCU targets

For `LowCure-ESP32`, direct effect operations inside a Flow are rejected.
Lowering instead performs the following transformation:

```text
effectful Flow computation
  → pure request construction
  → explicit pending-request state
  → outer program/capability dispatch
  → typed response or failure event
  → explicit named Flow state
```

The pending request and its response state have fixed layouts and explicit
ownership. A request may transfer an owned, `Send` value to its capability
owner, but it may not contain a borrow, a stack address, or an unresolved
effectful computation. If the capability operation fails, its failure contract
must specify whether ownership is returned, consumed during cleanup, or moved
to an explicitly recorded recovery state.

The generated program dispatcher is ordinary compiled control flow. The
`Effect` monad is a source and outer-orchestration abstraction; it is lowered
away before the MCU ABI. A conforming backend may implement its sequencing as
direct calls, a bounded event loop, or an explicit scheduler state machine, but
may not require a general continuation runtime.

This gives the MCU backend a closed effect boundary while preserving the more
expressive general Cure and BEAM paths.

## 7. Target profiles

LowCure has target profiles rather than one universal layout:

```text
LowCure-C       C11/C89-compatible structs, pointers, and calls
LowCure-Rust    Rust ownership/borrow-compatible representation
LowCure-Wasm    fixed locals, explicit linear memory, CFlat-like layout
LowCure-ESP32   bounded scheduler transitions and platform capabilities
```

`LowCure-ESP32` additionally requires:

- pure Flow transition functions;
- a closed, declared request and response vocabulary;
- effect interpretation only in the generated program/capability layer;
- bounded pending-request and scheduler state;
- no general handlers, first-class resumptions, or continuation cloning;
- explicit failure and cleanup transitions for every request;
- no implicit allocation introduced by request dispatch.

Other MCU profiles may use the same boundary with a different scheduler ABI,
while a general LowCure-C or LowCure-Rust target may retain explicit one-shot
state-machine suspension where its runtime provides that support.

The semantic LowCure legality checks are shared. Layout, ABI, integer widths,
alignment, and foreign calls are target-profile parameters.

Rust output is a valuable validation backend, but passing the Rust borrow
checker is not the Cure ownership proof. Cure's ownership derivation remains
authoritative.

## 8. LowCure preservation obligations

The Lean implementation must establish or check:

1. LowCure typing and closed residual effects;
2. usage and ownership preservation;
3. borrow-region non-escape;
4. one-shot frame preservation;
5. layout/size/alignment correctness;
6. no hidden allocation or stack escape;
7. evaluation-order preservation;
8. failure/cleanup preservation;
9. target-profile capability closure;
10. purity of Flow transition functions for every target profile;
11. request/response protocol preservation at the MCU effect boundary;
12. semantic correspondence with C/Rust/Wasm execution on the supported
    profile.

The LowCure checker is a natural Lean component:

```text
Flow/Concurrency IR
  → LowCure legality derivation
  → target-specific lowering certificate
```

Optional layout and register optimizations should use translation validation.

## 9. What LowCure rejects

The first profile rejects:

- unrestricted higher-order closures;
- open effect rows at a target boundary;
- abstract handlers not statically resolved;
- multi-shot resumptions;
- unbounded recursive by-value data;
- unknown-size stack values;
- stack references escaping through messages/callbacks;
- unannotated foreign allocation or ownership behavior;
- implicit garbage collection;
- hidden runtime interpretation of Cure IR;
- runtime macro expansion.

The MCU profile additionally rejects:

- direct effectful operations in Flow states;
- effect rows that remain open at the Flow/Request boundary;
- request payloads containing borrows, stack references, or unresolved
  computations;
- unbounded pending requests or response frames;
- a runtime algebraic-handler or general-continuation implementation.

These MCU restrictions do not define Flow purity; they define how an already
pure Flow connects to device and runtime capabilities. `Signal.Remote` remains
permitted only as a checked typed VM-to-VM message boundary.

Programs containing these features may still compile to BEAM through the
general Flow/Concurrency path or use an explicit runtime/heap representation.

## 10. Implementation stages

1. Define ownership/usage/borrow derivations in Lean.
2. Add closed layouts and explicit storage classes.
3. Define pure Flow/Request IR and the capability request contracts.
4. Lower a pure, monomorphic Flow program into LowCure statements.
5. Prove stack non-escape and layout preservation.
6. Prove that MCU Flow transitions contain no residual effects.
7. Add explicit request/response dispatch and failure transitions.
8. Add one-shot `suspend`/resume transitions only for profiles that support
   explicit scheduler suspension.
9. Emit C and run differential tests against the Lean LowCure evaluator.
10. Emit Rust as a second layout/ownership comparison target.
11. Add bounded ESP32 scheduler, request, and allocation gates.
12. Extend to regions, owned heap, and selected concurrency operations.

LowCure should be implemented after the general Computation and Flow typing
boundaries exist, but its legality checker and storage model should be designed
before target-specific C/Rust lowering begins.
