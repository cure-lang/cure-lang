# Typed Supervision Trees

`actor` and `sup` are standard-library macros living in `Std.Actor` and
`Std.Supervisor`. Neither is ambient: a unit that declares one must `use` the
module it comes from. Each expands to an ordinary lifted module and is checked
and emitted through the common Cure pipeline. OTP behavior knowledge belongs in
these Cure definitions and the checked `Std.Otp` algebra, not in a bespoke
compiler object class.

Both macros name a lifted module, and they name it the way `mod` does: you write
`sup Root`, and the emitter is the one that decides what the loaded BEAM module
is called. Other Cure code refers to it by the name you wrote.

## Supervisors

A supervisor is a name and at least one child. `children` is not optional:

```cure
use Std.Supervisor

sup Root
  children
    worker Counter as counter
```

Each child names its kind (`worker` or `supervisor`), the module that
implements it, and the identity it is known by inside the tree. `restart` and
`shutdown` are optional per child, and the tree's own policy is three optional
clauses:

```cure
use Std.Supervisor

sup Tree
  strategy OneForOne()
  intensity 5
  period more(9)
  children
    worker Counter as counter
      restart Permanent()
      shutdown Timeout(5000)
    supervisor Subtree as subtree
      restart Transient()
```

`period` takes a `Positive`, which is `One | More(Nat)` -- `more(9)` is 10, and
`one()` is 1. There is no way to write a zero or negative period, which is the
point: OTP rejects both at run time, and here they are unrepresentable.
`intensity` is an ordinary `Nat` literal.

Two children may not share an identity. `sup` rejects that at expansion time
with `duplicate_supervisor_child_identity` rather than deferring it to the
supervisor's own start-up.

### Child specs by hand

The macro's `children` clause is the ordinary way to build a tree, but the
underlying vocabulary is public. `Restart`, `Shutdown`, `ChildType`, and
`Strategy` are closed Cure values rather than arbitrary atoms:

```cure
mod Specs
  use Std.Supervisor

  fn defaults() -> ChildSpec = child(:counter_mod, :counter)

  fn explicit() -> ChildSpec =
    child_with(:counter_mod, :counter, permanent(), shutdown_after(5000), worker())

  fn subtree() -> ChildSpec =
    child_with_raw_args(
      :subtree_mod,
      :subtree,
      empty_raw_args(),
      transient(),
      brutal_shutdown(),
      supervisor()
    )
```

`child/2` is `child_with` at OTP's own defaults: permanent, a 5000ms shutdown,
and worker. The module and identity are plain atoms here, not module paths --
Cure has no quoted-atom literal, so a generated module is named by the atom the
emitter gave it.

The generated `init/1` callback returns the standard supervisor strategy and
child-spec structure, built from exactly these values.

## Actors

An actor creates a lifted `gen_server` module. `state` is the only required
clause; the rest of the family -- `initial`, `messages`, `init`, `on_start`,
`on_message`, `on_cast`, `on_info`, `handle_cast`, `handle_info`, `terminate`,
`on_stop`, `code_change`, `body`, and `on_call` queries -- is optional, and the
shape of what you supply chooses how the module is derived.

The raw form splices full GenServer callback results verbatim, which is what
lets value-equality dispatch and `pickup`/`else` appear where the structured
surface cannot express them:

```
actor Clock state Int initial 0 messages Atom handle_cast
  pickup
    message == :tick -> %[:noreply, state + 1]
    message == :reset -> %[:noreply, 0]
    else -> %[:noreply, state]
```

Synchronous calls are declared as typed queries, each naming its request, its
parameters, and the type of its reply:

```cure
use Std.Actor

actor Counter
  state Int
  initial 0
  on_call Value() returns Int
    reply state
  on_call Bump(step: Int) returns Int
    reply state + step
    update state + step
```

`reply` is what the caller receives; the optional `update` is the state the
actor keeps. The generated module exports the normal `gen_server` callbacks
plus a checked `start_link`, a typed `start`, `send`, `request`, and `stop`.

A request name is a constructor of the generated `Request` family, so it is
capitalised, and the adapter the caller uses is its downcased form -- `Value()`
gives `value/1`, `Bump(step: Int)` gives `bump/2`. Spelling the request itself
in lower case makes the constructor and its own adapter the same name, and the
lifted module is rejected with `constructor_function_collision`.

> **Known gap.** The raw fence above is shown unchecked because the one-line
> positional form does not parse from a unit that only says `use Std.Actor`;
> `actor Clock state ...` is rejected with a macro-syntax mismatch on the name.
> The example packages that use this form compile it through their own preload.
> The query fence beside it is checked and does describe emitted code.

Callback results are checked as erased `Effect(...)` values. Pure values are
lifted automatically, while `beam_ops` expressions must satisfy the ordinary
process algebra.

## The BEAM Algebra

Process operations are expressed with `beam_ops` and checked `Std.Otp`
functions:

```cure
mod ProcessUser
  use Std.Otp

  fn me() -> Effect(Pid(Atom)) = beam_ops self
  fn tell(pid: Pid(Atom)) -> Effect(Unit) = beam_ops tell pid :ping
```

The message and reply indices are static only and erase to ordinary BEAM pids
and terms. The raw extern boundary is isolated in `Std.Otp.Raw`.

## Runtime Helpers

Starting and stopping a tree is done through the module the macro generated,
not through `Std.Supervisor` -- that module holds the vocabulary, while the
generated one holds the running tree:

```cure
mod Driver
  use Std.Supervisor
  use Std.Otp
  use Std.ExitReason

  sup Tree
    strategy OneForOne()
    children
      worker Counter as counter

  fn boot() -> Effect(Tuple) = Tree.start_link()

  fn typed() -> Effect(StartResult(Tree.Handle)) = Tree.start()

  fn halt(tree: Tree.Handle) -> Effect(Unit) =
    Tree.stop(tree, Normal())
```

`start_link/0` is the raw OTP startup tuple; `start/0` narrows it to
`StartResult(Handle)`, where `Handle` is the tree's own alias for a supervisor
handle. Both route to `Std.Otp.start_supervisor` / `start_typed_supervisor`,
the same checked effect path the generated `app` module's `start/2` uses.

## Transparency

The macro expansion contains no `__otp_container`, raw-source compilation, or
direct code-server load. Nested macros and callback bodies are recursively
parsed and elaborated before the generic lifted-module emitter writes BEAM
forms. New user-defined actor-like abstractions can use the same `lift module`,
`callback`, and algebra vocabulary without compiler changes.
