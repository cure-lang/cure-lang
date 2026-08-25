%{
  title: "Finite State Machines",
  description: "The `fsm` macro: transition tables with typed states, events, guards and updates, verified at compile time and lowered onto OTP gen_statem.",
  order: 4
}
---

`fsm` is a transparent macro from `Std.Fsm`; it is not ambient, so a unit
that declares one must `use Std.Fsm`. It expands to an ordinary lifted
module whose behaviour and callbacks use the checked BEAM algebra — there is
no privileged FSM object class in the compiler, and the dependent pipeline
checks the expanded declarations like any other code. The generated module
is a `gen_statem`.

There are two surfaces, and they are different macros:

- **Transition tables** — `fsm <Name> with <DataType>`, a body of `From --Event--> To`
  rows. States and events are *derived from the rows*: you never declare them.
- **Structured FSMs** — `fsm <Name>`, with `state`, `events` and friends, when the
  handler logic matters more than the graph.

Both require `use Std.Fsm`. A lifted name belongs to its enclosing module, just
like every other declaration. At top level that owner is the implicit `Main`,
while `fsm Turnstile` inside `mod Gate` emits `Cure.Gate.Turnstile`. In either
case code in the same owner writes the local name, `Turnstile`.

For long-lived processes whose behaviour is a flat message handler rather than a
state-transition graph, reach for [typed actors and supervision
trees](/actors) instead. FSMs remain the right tool when the state machine
itself is the primary abstraction.

## Transition tables

Each row is `SourceState --Event--> TargetState`. States and events are
capitalised constructors, not atoms — the macro collects them and emits two
nominal enum types, `State` and `Event`, in the generated module.

```cure
use Std.Fsm

fsm TrafficLight with Int
  Red    --Timer--> Green
  Green  --Timer--> Yellow
  Yellow --Timer--> Red
```

`with Int` names the FSM's data type. Every instance carries one value of that
type, threaded through transitions; it is what `init/1` is given and what
`update` rewrites.

### Wildcard rows

`*` as the source matches any state:

```cure
use Std.Fsm

fsm TrafficLightWithOverride with Int
  Red    --Timer-->     Green
  Green  --Timer-->     Yellow
  Yellow --Timer-->     Red
  *      --Emergency--> Red
```

Explicit rows are tried first; wildcard rows are the fallback. From `Green`,
`Emergency` goes to `Red`; `Timer` still goes to `Yellow`.

### Initial and terminal states

The initial state defaults to the first *explicit* (non-wildcard) source in the
table. State an initial explicitly with `initial`, and mark states that are
allowed to have no outgoing transitions with `terminal` — which may be repeated.

```cure
use Std.Fsm

fsm DoorLock with Int
  initial Locked
  terminal Blocked
  Locked   --Unlock--> Unlocked
  Unlocked --Lock-->   Locked
  Locked   --Block-->  Blocked
```

### Guards and updates

A row can carry an indented `when` guard and an `update` expression. The guard
decides whether the row fires; the update computes the new data. Inside both,
the FSM's data is bound as `data`.

```cure
use Std.Fsm

fsm Counter with Int
  initial Counting
  terminal Done
  Counting --Tick--> Counting
    when data > 0
    update data - 1
  Counting --Finish--> Done
```

A row whose guard is false falls through to the next candidate row, and then to
the wildcard rows. If nothing matches, the FSM keeps its state and data
unchanged — an unhandled event is not an error.

### Events with payloads

An event may carry parameters. The parameter names are bound in that row's
`when` and `update`:

```cure
use Std.Fsm

fsm Meter with Int
  terminal Unlocked
  Locked --Insert(amount: Int)--> Unlocked
    when amount > 0
    update data + amount
```

An event's payload must be declared consistently everywhere it appears;
disagreeing rows are rejected with `fsm_inconsistent_event_payload`.

## Compile-time verification

The macro verifies the graph while expanding, and a violation is a compile
error, not a warning:

| Check | Error |
| --- | --- |
| The table has at least one row | `fsm_requires_transition` |
| An initial state can be determined | `fsm_requires_initial_state` |
| The initial state appears in the graph | `fsm_unknown_initial_state` |
| Every declared terminal state appears in the graph | `fsm_unknown_terminal_state` |
| No two unguarded rows share a source and event | `fsm_duplicate_transition` |
| Every state is reachable from the initial state | `fsm_unreachable_state` |
| Every non-terminal state has an outgoing row | `fsm_deadlocked_state` |

So this is rejected — `C` and `D` are unreachable from `A`:

```text
fsm Broken with Int
  terminal B
  terminal D
  A --Go--> B
  C --Go--> D
```

and so is this, because `B` has no way out and was not declared terminal:

```text
fsm Deadlocked with Int
  A --Go--> B
```

Guards make otherwise-duplicate rows distinct, because they can no longer both
fire:

```cure
use Std.Fsm

fsm Router with Int
  terminal Fast
  terminal Slow
  Start --Dispatch--> Fast
    when data > 0
  Start --Dispatch--> Slow
    when data <= 0
```

## The generated module

`fsm Turnstile with Int` emits a child module of its lexical owner which local
code refers to as `Turnstile`, containing:

- `type State` — an enum of every state constructor in the table.
- `type Event` — an enum of every event constructor, carrying its payload types.
- `typealias Data` — whatever followed `with`.
- `typealias Handle = Std.Otp.FsmPid(Event, State, Data)`.
- `callback_mode() -> Atom` and `init(Data)` — the `gen_statem` callbacks.
- `decide(Event, State, Data) -> FsmAction(State, Data)` — the pure transition
  function the table compiles to. It is worth reading in isolation: it is the
  whole graph as one total function.
- `handle_event(Atom, Event, State, Data)` — `decide` lowered to the tuple
  vocabulary `gen_statem` expects.
- `start_link(Data) -> Effect(Tuple)` — the supervisor-facing entry point.
- `start(Data) -> Effect(Std.Otp.StartResult(Handle))` — the typed entry point.
- `send(Handle, Event) -> Effect(Unit)`.

## Driving an FSM

`start/1` returns a `Std.Otp.StartResult`, so the handle arrives already
narrowed. Event constructors belong to the generated module:

```cure
mod Turnstile
  use Std.Fsm
  use Std.Otp

  fsm Machine with Int
    Locked   --Coin--> Unlocked
    Unlocked --Push--> Locked
      update data + 1

  fn start() -> Effect(StartResult(Machine.Handle)) = Machine.start(0)
```

Under a supervisor, use `start_link/1` instead:

```cure
mod Gate
  use Std.Fsm
  use Std.Otp

  fsm Machine with Int
    terminal Closed
    Open --Shut--> Closed

  fn boot() -> Effect(Tuple) = Machine.start_link(0)
```

## Structured FSMs

When the transition graph is less interesting than what each event *does*, use
the other `fsm` macro: declare the data type with `state` and map event
constructors to actions under `events`.

```cure
use Std.Fsm

fsm Ticker
  state Int
  events
    Tick -> :keep_state_and_data
```

Event constructors that are not declared elsewhere are collected into an `Event`
enum belonging to the generated machine — `Ticker.Event` here. It is a companion
of the machine, not a name bound beside it, so two modules can each declare a
`Ticker` without colliding, and the constructors are not in scope for the code
around the `fsm`. Use `event_type` (below) when the surrounding module needs to
name the events itself.

An action is a `FsmAction(state, data)`:

- `Keep(data)` — stay in the current state with this data.
- `Next(State(), data)` — move to `State()` with this data.
- `Stop(reason, data)` — terminate; `reason` is a `Std.ExitReason`.

### Naming the states

Add `states`, `initial` and `event_type` to work with your own types rather than
generated ones. `states` requires `initial` — without it the macro fails with
`typed_fsm_requires_initial_state`.

```cure
use Std.Fsm

type DoorState = Locked | Unlocked
type DoorEvent = Coin | Push

fsm Door
  state Int
  states DoorState
  initial Locked
  event_type DoorEvent
  events
    Coin -> Next(Unlocked(), data + 1)
    Push -> Next(Locked(), data)
```

Stopping works the same way. `Std.ExitReason` is `Normal | Kill | Shutdown |
Because(Atom)`; qualify the constructor, since these names are common:

```cure
use Std.Fsm

type JobState = Working | Paused
type JobEvent = Pause | Resume | Finish

fsm Job
  state Int
  states JobState
  initial Working
  event_type JobEvent
  events
    Pause  -> Next(Paused(), data)
    Resume -> Next(Working(), data)
    Finish -> Stop(Std.ExitReason.Normal(), data)
```

The structured form emits `Data`, `StateName` and `Event` aliases plus
`callback_mode/0`, `init/1`, `decide/3`, `handle_event/4` and `start_link/1`. It
does *not* emit `start/1` or `send/2` — reach for the transition-table surface,
or `Std.Otp` directly, when you want the typed handle.
