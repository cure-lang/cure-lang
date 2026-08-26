# FSM Programming Guide

`fsm` is an auto-preluded standard-library macro. It expands to an ordinary
`lift module` with a checked `gen_statem` callback surface; the compiler does
not contain a separate FSM parser or object class.

## Defining An FSM

The preferred surface is the transition graph itself:

```cure
use Std.Fsm

fsm Turnstile with Int
  Locked --Coin--> Unlocked
    update data + 1
  Unlocked --Push--> Locked
  Unlocked --Coin--> Unlocked
    update data + 1
  Locked --Push--> Locked
```

`with Int` declares the machine's data type. The macro catalogs every endpoint
into a nominal `State` type (`Locked | Unlocked`) and every label into a nominal
`Event` type (`Coin | Push`). The first source state is the initial state.

An edge preserves `data` unless it has an indented `update` expression. The
expression is checked as the declared data type and may refer to `data`; the
target state is already fixed by the edge and is not repeated in callback
tuples.

Record data uses Cure's ordinary typed record-update syntax. Fields not named
after the bar are preserved:

```cure
use Std.Fsm

rec TurnstileData
  coins: Int
  pushes: Int
  enabled: Bool

fsm Turnstile with TurnstileData
  Locked --Coin--> Unlocked
    update TurnstileData{
      data
      | coins: data.coins + 1,
      enabled: true
    }
  Unlocked --Push--> Locked
    update TurnstileData{data | pushes: data.pushes + 1}
  Unlocked --Coin--> Unlocked
    update TurnstileData{data | coins: data.coins + 1}
  Locked --Push--> Locked
```

The `|` may instead occupy its own line before the first field; both layouts
parse as the same typed record update.

## Transition Tables

Transition rows are parsed by a grammar production declared in `Std.Fsm`, not
by a compiler-owned FSM parser:

```cure
use Std.Fsm

fsm Light with Int
  Red --Timer--> Green
  Green --Timer--> Yellow
  Yellow --Timer--> Red
```

The generated callback is direct nested pattern matching over the derived
constructors. It returns checked `FsmAction` values and lowers them to the
native `gen_statem` protocol; no transition table or syntax interpreter remains
at runtime.

## Runtime

The generated module is an ordinary BEAM module. It exports both entry points a
`gen_statem` needs: `start_link/1` for a supervisor, and `start/1` for a typed
handle. Events go through `send/2`, and the event constructors are the ones
derived from the table.

```cure
mod TrafficLight
  use Std.Fsm
  use Std.Otp

  fsm Machine with Int
    Red    --Timer--> Green
    Green  --Timer--> Yellow
    Yellow --Timer--> Red

  fn boot() -> Effect(Tuple) = Machine.start_link(0)

  fn start() -> Effect(StartResult(Machine.Handle)) = Machine.start(0)
```

`start/1` returns a `Std.Otp.StartResult(Handle)`, so the failure cases are in
the type rather than in a tuple you have to remember to check. There is no FSM
registry or process-inspection layer: a running machine is reached through its
handle, like any other OTP process.

## Transparency

The expansion is ordinary Cure syntax. It contains no `__otp_container`
marker, raw-source compilation, or direct code-server load. Generated modules
are collected and emitted by the same generic lifted-module path as any
user-defined macro.

The transition grammar and event/state derivation are language-level macro
work. Another package can define the same kind of declarative algebra without
changing the compiler.
