# Cure Flow Machine Semantics

**Status:** Normative design specification  
**Parent:** `2026-07-21-lean-verified-middle-end-design.md`

## 1. Purpose

Flow IR is Cure's first-order representation of suspended control. It is
generated from typed continuation sites by CPS conversion and
defunctionalization. It is used for BEAM paths that cross suspension or actor
boundaries and for stackless C/ESP32 execution.

It is not an opaque `Effect(A)` value, a syntax interpreter, or a requirement
that every pure computation allocate a frame.

## 2. Syntax

```text
FlowProgram = { functions : Function* }

Function = {
  name, parameters, entry : StateId,
  states : State*
}

State = {
  id, captures : Capture*, result : ValueType,
  effects : EffectRow, step : Step
}
```

```text
ControlMode ::= LocalHandler | ExternalScheduler

Step ::= Return(ValueRef)
       | Call(FunctionId, ValueRef*, StateId, Optional StateId)
       | Perform(Operation, ValueRef*, StateId, Optional StateId, ControlMode)
       | Branch(ValueRef, (Pattern × StateId)*)
       | ConcurrencyAction(Action, StateId)
       | Abort(Failure)
```

The target state receives the result of `Call`, `Perform`, or
`ConcurrencyAction` in
the statically identified result slot. Captures have a fixed type and layout.

## 3. Runtime configurations

```text
Config ::= Running(StateId, Frame)
         | Suspended(Operation, Payload, Resumption, Owner)
         | Returned(Value)
         | Failed(Failure)
```

```text
Frame = {
  state : StateId,
  fields : Field*,
  ownership : OwnershipToken,
  handler : Optional HandlerEnv
}

Resumption = {
  success : StateId,
  failure : Optional StateId,
  frame : Frame
}
```

Scheduler state is separate:

```text
Scheduler = {
  ready : Queue<Frame>,
  blocked : Map<Owner, Resumption>,
  capabilities : CapabilitySet
}
```

## 4. Transition relation

The local transition relation is written:

```text
⟨config, scheduler⟩ → ⟨config', scheduler'⟩
```

Core rules:

```text
Running(s, f), state(s) = Return(v)
────────────────────────────────
Running(s, f) → Returned(resolve(v, f))
```

```text
Running(s, f), state(s) = Perform(op, args, success, failure, mode),
mode = ExternalScheduler
────────────────────────────────────────────────────────────────────
Running(s, f) → Suspended(op, resolve(args, f),
  {success, failure, f}, owner(f))
```

For `ExternalScheduler`, the corresponding resumption is also inserted into
`scheduler.blocked[owner(f)]`; the suspended configuration is not runnable
until the owner supplies a result. For `LocalHandler`, the Handler/Continuation
IR semantics handles the operation inside the current configuration and no
`Suspended` state is exposed.

For an externally handled operation, the runtime supplies a result through the
owner and creates exactly one continuation transition:

```text
Suspended(op, payload, {success, failure, frame}, owner) + result(v)
──────────────────────────────────────────────────────────────
Running(success, extend(frame, v))
```

An operation failure uses `failure` when present and otherwise produces
`Failed`. `ControlMode` distinguishes an ordinary operation handled locally
from an externally resumed suspension. Handler resolution occurs before the
external `Suspended` configuration is created.

For `LocalHandler`, handler execution is part of the local Flow transition and
does not expose a scheduler suspension. For `ExternalScheduler`, the
resumption is inserted into `blocked` and control returns to the scheduler.
Call failures use the optional failure state and otherwise produce `Failed`.

The exact scheduler protocol is target-specific, but it must implement this
abstract relation.

## 5. Ownership

Each one-shot frame has one of:

```text
Available → Consumed
Available → Aborted
Available → Transferred(owner)
```

No transition is legal from `Consumed` or `Aborted`. A transferred frame is
consumed only by its new owner. Resource-bearing frames require an explicit
cleanup transition on abort or completion.

Lean should encode ownership in state transitions where practical and retain a
dynamic check in debug/runtime builds until the representation is fully
intrinsic.

## 6. Defunctionalization contract

For every source continuation `k`, the lowering produces a state `s` and
capture environment `f` such that:

```text
sourceResume(k, v)  ≈  flowRun(s, extend(f, v))
```

The relation must preserve returned values, failures, performed effects, and
ownership outcomes. A continuation site may be compiled directly only when it
does not escape, cannot suspend across the local boundary, and has no resource
cleanup obligation requiring a frame.

## 7. Pure fast paths

The following may avoid Flow allocation:

- pure returns;
- pure calls whose continuations do not escape;
- local handlers with no suspension-capable operation;
- tail calls with compatible result/effect/ownership signatures.

The following must use explicit Flow state:

- scheduler suspension;
- callbacks stored or passed to higher-order operations;
- actor/process boundary crossings;
- resource-bearing continuations;
- continuations that survive the current host call;
- operations whose implementation may suspend even if one backend currently
  implements them synchronously.

## 8. Concurrency extension

A runtime process contains a local Flow configuration and a mailbox:

```text
Process = {
  id, flow : Config, mailbox : List<Message>,
  links, monitors, trapExit
}
```

The concurrency relation handles local transitions, message arrival, sends,
spawns, exits, links, and monitors. Local Flow semantics must not assume a
particular process scheduling order. Observable equivalence is stated using
traces or weak bisimulation.

## 9. Target interpretations

### BEAM

Non-escaping states may lower to direct Core Erlang calls. Escaping states
lower to explicit dispatch functions and frame records. The generated program
must contain direct compiled behavior, not a runtime IR interpreter.

### C/ESP32

Each scheduler step returns a bounded transition record:

```text
Done(value)
Next(stateId, fields)
Perform(operation, payload, owner)
Fail(error)
```

Suspension returns to the outer loop. No suspended path relies on native stack
unwinding or unbounded recursive calls.

## 10. Theorem obligations

The Lean implementation must establish, for the first fragment:

1. capture layouts match state requirements;
2. every Flow transition is type-correct;
3. defunctionalization simulates continuation invocation;
4. one-shot ownership is preserved;
5. pure fast paths agree with the corresponding Flow path;
6. scheduler execution preserves operation/result/failure traces;
7. concurrency extension preserves selected observable message traces.
