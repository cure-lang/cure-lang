# `reducer` — State-Dependent Payloads on the Flow Runtime

**Date:** 2026-07-08
**Status:** design (operator-designed surface, consolidated from parent §5.5).
Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
(§5.5, which remains the macro-facility worked example; this document is the
reducer's own home going forward); built as a `macro` (§5), top power tier
(tier 4 — `elab` with reflection, alongside `flow`).

The parent's four hiding principles (§3) are LAW here: indices flow from
declarations, never from annotations; ill-formed reducers are inexpressible,
not expressible-but-rejected; obligations discharge by computation or not at
all; `unsafe` is the pressure valve. The operator designed this surface — it
is fixed. This spec organizes and formalizes; genuine forks are ledgered (§10).

---

## 1. Purpose — and the SwiftUI-body analogy

`reducer` is `fsm` where the **payload type depends on the current state**
(per-state schemas via `State over {…}`), with typed `emits`/`rejects` streams
and a SwiftUI-style `body` that lowers onto the Flow runtime as a
`Signal.scan`. It exercises every power tier at once: derived index types, a
GADT model, refinement-carrying guards, and FRP lowering.

The SwiftUI analogy is load-bearing: like a `View`'s `body` producing `some
View`, a reducer's `body` is a **pure description** consumed by a runtime
that owns the state loop. The user declares a graph, per-state schemas, and
guarded clauses; they never write the loop, touch a process, or see a
`Signal.scan`. This is also Elm's update function (parent §7.1): `reducer` is
the shared core that `view`, `workflow`, and `bot` build on.

## 2. Surface (operator's design, verbatim)

```cure
type DoorEmit =
  OpeningStarted
  | Opened
  | Faulted

type DoorReject =
  InvalidTransition(source: Door.State, msg: Door.Msg)

type FaultReason =
  CannotOpenWhileLocked
  | MotorTimeout

type LockState =
  Locked
  | Unlocked

type MotorState =
  Stopped
  | MovingOpening

reducer Door fsm
  clock: Std.Clock
  emits: DoorEmit
  rejects: DoorReject

  Closed  --OpenPressed-->      Opening
  Closed  --OpenPressed-->      Fault
  Opening --MotorTimeout-->     Opening
  Opening --MotorTimeout-->     Fault
  Opening --MotorReachedOpen--> Open

  Closed over {
    lock: LockState
    motor: Stopped
  }

  Opening over {
    lock: Unlocked
    motor: MovingOpening
    started_at: Instant
    retries: Bounded(3)
  }

  Open over {
    lock: Unlocked
    motor: Stopped
    opened_at: Instant
  }

  Fault over {
    reason: FaultReason
  }

  init: Closed {
    lock: Unlocked,
    motor: Stopped
  }

  fn body =
    on OpenPressed from Closed with (payload, clock)
      when payload.lock == Unlocked ->
        emit <| Opening {
          lock: Unlocked,
          motor: MovingOpening,
          started_at: clock.now,
          retries: 0
        } <| OpeningStarted

    on OpenPressed from Closed with (payload, _clock)
      when payload.lock == Locked ->
        emit <| Fault {
          reason: CannotOpenWhileLocked
        } <| Faulted

    on MotorTimeout from Opening with (payload, clock)
      when elapsed(clock.now, payload.started_at) >= millis(500) && payload.retries < 2 ->
        update <| Opening {
          lock: Unlocked,
          motor: MovingOpening,
          started_at: clock.now,
          retries: payload.retries + 1
        }

    on MotorTimeout from Opening with (payload, _clock)
      when payload.retries == 2 ->
        emit <| Fault {
          reason: MotorTimeout
        } <| Faulted

    on MotorReachedOpen from Opening with (_payload, clock) ->
      emit <| Open {
        lock: Unlocked,
        motor: Stopped,
        opened_at: clock.now
      } <| Opened

    on _ with (model, msg) ->
      reject InvalidTransition(model.state, msg)
```

Design notes captured from the surface (parent §5.5, carried over): the graph
deliberately allows **multiple edges per (state, message) pair**
(nondeterministic in the graph, resolved by `when` guards in the body);
header lines declare **capabilities** (`clock`) that clauses receive as
binders; the user's own `type` declarations reference the macro-**derived**
names `Door.State`/`Door.Msg` — a staging / name-resolution consequence,
ledgered at the facility level (parent §9 item 6: two-pass resolution or
forward-declaration semantics); the mandatory final catch-all binds the whole
model with `model.state` projecting the dependent pair's index (§10 item 4).

## 3. Derived types — what elaboration manufactures

The user writes values and declarations; the macro writes every type
(hiding principle 1). From the Door block, elaboration derives:

- **`Door.State`** — one constructor per `over` schema:
  `Closed | Opening | Open | Fault`.
- **`Door.Msg`** — the deduplicated edge labels:
  `OpenPressed | MotorTimeout | MotorReachedOpen`.
- **Per-state payload records** `Door.Payload.<State>`, via the **singleton
  rule**: a bare constructor in type position becomes a refinement —
  `motor: Stopped` ~> `motor: {m: MotorState | m == Stopped()}` — zero bytes
  after erasure.
- **The state-indexed model GADT** — THE dependent part, one constructor per
  state:
  `type Door.Model(s: Door.State) = | Closed(p: Door.Payload.Closed) : Door.Model(Closed) | …`.
  Matching a constructor **refines the index** (landed K5 machinery): inside
  a `from Opening` clause, `payload : Door.Payload.Opening`, so
  `payload.retries` exists there and is a compile error in a `from Closed`
  clause.
- **The `Step` record** — one scan output, model as a **dependent pair**:

  ```cure
  rec Door.Step
    model:     %[s: Door.State, Door.Model(s)]
    emission:  Option(DoorEmit)
    rejection: Option(DoorReject)
  ```

  A step carries at most one emission and one rejection alongside the new
  model, atomically — the unit the runtime scans over and the unit `check`'s
  temporal properties observe.

## 4. The lowering — `Signal.scan` on Flow

The target shape, shown for a time-driven Debounce reducer (operator's
intended lowering, verbatim):

```cure
fn body(
  clock : Signal(Std.Clock.Tick),
  input : Event(DebounceMsg(T)),
  initial : DebounceState(T)
) -> {
  model : Signal(DebounceState(T)),
  emission : Event(T),
  rejection : Event(Never)
} =
  let messages =
    merge(
      input.map(UserMsg),
      clock.tick.map(_ -> InternalTick)
    )

  let steps =
    Signal.scan(
      initial,
      messages,
      (state, message) ->
        match message
          UserMsg(Input(value)) ->
            {
              model: {
                pending: Some(value),
                last_seen: clock.now
              },
              emission: None,
              rejection: None
            }

          InternalTick
            when state.pending != None && elapsed(clock.now, state.last_seen) >= duration ->
              {
                model: {
                  pending: None,
                  last_seen: clock.now
                },
                emission: Some(unwrap(state.pending)),
                rejection: None
              }

          InternalTick ->
            {
              model: state,
              emission: None,
              rejection: None
            }
    )

  {
    model: steps.map(step -> step.model),
    emission: steps.filter_map(step -> step.emission),
    rejection: steps.filter_map(step -> step.rejection)
  }
```

Note `rejection : Event(Never)` — a reducer that declares no rejects gets a
statically-empty rejection stream.

**Clock nuance — sample vs. merge.** Door only *samples* the clock (the
generated scan uses `input.with_latest(clock)`); a time-driven reducer like
Debounce instead **merges** `clock.tick` as an internal message — visible in
the expansion above. The macro emits the merge exactly when some clause
consumes a tick message — same grammar, one conditional in the elab. Whether
that trigger is inferred or opted into explicitly is the first open decision
(§10 item 1).

## 5. Static discipline

Everything below is plain compile-time code in the `elab` — checks over lists
of quoted declarations, correct-by-construction, no proofs from anyone
(hiding principle 2).

- **Graph conformance.** Every edge endpoint is a declared state; every
  non-catch-all clause corresponds to a declared edge (`{:undeclared_edge}`
  otherwise); every edge is covered by some clause (`{:unhandled_edge}`); the
  `init` payload conforms to its state's schema.
- **Mandatory catch-all.** The last clause must be
  `on _ with (model, msg) -> …`. Catch-all plus edge coverage make the scan
  function **total** — and size-change termination then gives "this reducer
  provably cannot hang."
- **Guard-refinement double duty.** In the Door retry clause,
  `payload.retries + 1 : Bounded(3)` type-checks **because the `when
  payload.retries < 2` guard flows into the refinement context** — the guard
  does double duty: runtime dispatch *and* static bound discharge. Where the
  checker falls short, the answer is the `{:refinement_failed, …}` explainer
  ("add a `when` guard that bounds it"), never a surfaced proof goal (hiding
  principle 3). The checker's reach here is ledgered in the parent (§9 item
  16).
- **Forced-tag erasure — zero-byte state tags.** The dependent pair's state
  tag is a **forced pattern** (fully determined by the `Model` constructor),
  matched as `_` and erased at runtime; singleton fields (`motor: Stopped`)
  erase to nothing. The runtime model is just the live payload fields — the
  ESP32 zero-footprint story.

## 6. The macro definition (verbatim)

```cure
macro Reducer
  ## `reducer Name fsm` — a state machine whose payload TYPE depends on its
  ## state; typed emissions/rejections; `body` lowers onto Flow (Signal.scan).
  ## (`fsm` names the lowering family — room for `reducer Name flow` later.)

  # ---- grammar (each category auto-derives a quoted-AST record type) -------
  category Edge
  syntax Edge ::= $src:UpperIdent --$msg:UpperIdent--> $tgt:UpperIdent

  category Schema
  syntax Schema ::= $state:UpperIdent over $fields:RecordTypeBlock

  category Action
  syntax Action ::=
    | emit <| $model:Expr <| $emission:Expr
    | update <| $model:Expr
    | reject $err:Expr

  category Clause
  syntax Clause ::=
    | on $msg:Pattern from $state:UpperIdent with $args:ParamTuple
        (when $guard:Expr)? -> $act:Action
    | on _ with $args:ParamTuple -> $act:Action          # total catch-all

  syntax reducer $name:UpperIdent fsm
    clock:   $clock:TypeExpr
    emits:   $emits:TypeExpr
    rejects: $rejects:TypeExpr
    $edges:Many(Edge)
    $schemas:Many(Schema)
    init: $s0:UpperIdent $p0:RecordLit
    fn body = $clauses:Many(Clause)

  # ---- elaboration: total compile-time Cure, quoted syntax in and out ------
  elab reducer(name, clock, emits, rejects, edges, schemas, s0, p0, clauses) =
    # 1. Derive the index + message types from the declarations themselves.
    let states = schemas.map(fn(s) -> s.state)
    let msgs   = edges.map(fn(e) -> e.msg) |> dedup()
    let state_ty = quote type $(name).State = $(states.join(" | "))
    let msg_ty   = quote type $(name).Msg   = $(msgs.join(" | "))

    # 2. Per-state payload records. Singleton rule: a bare constructor in
    #    type position becomes a refinement — zero bytes after erasure.
    #      motor: Stopped   ~>   motor: {m: MotorState | m == Stopped()}
    let payload_recs = schemas.map(fn(s) ->
      quote rec $(name).Payload.$(s.state)
              $(s.fields.map(singleton_rule)))

    # 3. THE DEPENDENT PART — the state-indexed model, one GADT ctor per
    #    state. Matching a ctor refines the index (landed K5 machinery).
    let model_ty = quote
      type $(name).Model(s: $(name).State) =
        $(states.map(fn(st) ->
          quote | $(st)(p: $(name).Payload.$(st)) : $(name).Model($(st))))

    # 4. Graph discipline — correct-by-construction, plain code, no proofs.
    check edges.all(fn(e) -> e.src in states and e.tgt in states)
      else fail {:unknown_state, edges}
    check clauses.drop_last().all(fn(c) ->
        %[c.state, msg_head(c.msg), target_state(c.act)] in edges)
      else fail {:undeclared_edge, clauses}
    check edges.all(fn(e) -> clauses.any(fn(c) -> covers(c, e)))
      else fail {:unhandled_edge, edges}
    check clauses.last().is_catchall  else fail {:missing_catchall, name}
    check conforms(p0, schema_of(schemas, s0)) else fail {:bad_init, s0}

    # 5. One match arm per clause. The pair's state tag is a FORCED pattern
    #    (determined by the Model ctor) — matched as _, erased at runtime.
    #      on MotorTimeout from Opening with (payload, clk) when g
    #        -> emit <| Open {fs} <| Opened
    #      ~>
    #      %[%[_, $(name).Model.Opening(payload)], MotorTimeout()] when g ->
    #        $(name).Step{ model:     %[Open, Model.Open(Payload.Open{fs})],
    #                      emission:  Some(Opened()),
    #                      rejection: None() }
    let arms = clauses.map(fn(c) -> clause_to_arm(name, c))

    # 6. Emit everything, `body` last — the operator's Signal.scan shape.
    quote
      $(state_ty); $(msg_ty); $(payload_recs); $(model_ty)

      rec $(name).Step
        model:     %[s: $(name).State, $(name).Model(s)]    # dependent pair
        emission:  Option($(emits))
        rejection: Option($(rejects))

      fn $(name).body(clock: Signal($(clock)), input: Event($(name).Msg))
          -> { model:     Signal(%[s: $(name).State, $(name).Model(s)]),
               emission:  Event($(emits)),
               rejection: Event($(rejects)) } =
        let init = %[$(s0), $(name).Model.$(s0)($(name).Payload.$(s0) $(p0))]
        let steps = Signal.scan(
          $(name).Step{model: init, emission: None(), rejection: None()},
          input.with_latest(clock),
          fn(step, %[msg, clk]) -> match %[step.model, msg] $(arms))
        { model:     steps.map(fn(s) -> s.model),
          emission:  steps.filter_map(fn(s) -> s.emission),
          rejection: steps.filter_map(fn(s) -> s.rejection) }

  # ---- explainers -----------------------------------------------------------
  explain
    {:undeclared_edge, c} ->
      "on " <> c.msg <> " from " <> c.state <> " goes to " <>
      target_state(c.act) <> ", but the graph has no edge " <>
      c.state <> " --" <> c.msg <> "--> " <> target_state(c.act) <>
      ". Add the edge or fix the target."
    {:no_field, state, f} ->
      "state " <> state <> " has no field `" <> f <>
      "` — check its `over { … }` block."
    {:refinement_failed, bound, expr} ->
      expr <> " can exceed " <> show(bound) <>
      " — add a `when` guard that bounds it (e.g. retries < 2)."
    {:missing_catchall, n} ->
      "reducer " <> n <> " must end with `on _ with (model, msg) -> …` " <>
      "so every (state, message) pair is handled."
```

Honest gap (carried from the parent): `clause_to_arm` must *construct* GADT
match arms and record literals against macro-derived types —
`elab`-with-reflection territory (parent §5.2 tier 4, same as `flow`).
**`reducer` therefore joins `fsm` in the dogfood test (parent §5.4):** the
facility is done when this file compiles as a library.

## 7. Explainers

The `explain` block above is the contract, per the parent's error-explainer
architecture (§4): every failure a user can trigger maps to **reducer
vocabulary** — states, edges, guards, `over` blocks — in the fixed template
*what you wrote → why the domain forbids it → what to write instead*.
Generated terms carry provenance, so a kernel failure deep inside a generated
match arm is attributed to the user's `on … from …` line. A raw
`cannot_unify` reaching a reducer user is a defect by definition; the
fallback shows the raw error plus a "bug in the macro layer, please
report" note.

## 8. Flow citizenship & consumers

Because `body`'s inputs and outputs are `Signal`/`Event`, **reducers are Flow
citizens**: they compose inside `flow` blocks directly —
`sink motor <- Door.body(clock, presses).model |> …`. Consumers:

- **`workflow`** is `reducer` at business timescale (Order → Paid → Shipped),
  persistent, with event sourcing by construction — the `Step`'s emissions
  *are* the audit log, and replay is literally `Signal.scan` over history.
  **`bot`** is `reducer` per conversation (sessions are per-user actors;
  typestate makes "ask for payment before a cart exists" inexpressible).
  Both specialize this macro; see
  [`2026-07-08-workflow-bot-macro-design.md`](2026-07-08-workflow-bot-macro-design.md)
  (written in parallel).
- **`fleet` hub reducers** — a reducer inside `hub` logic is a stateful
  combinator under the fleet spec's ownership rule 4 (single owner, inferred
  from the downstream sink), emissions possibly fanning out to several nodes;
  [`2026-07-08-fleet-macro-design.md`](2026-07-08-fleet-macro-design.md)
  §11.7 tracks confirming no extra projection cases arise.
- **`view`** (parent §7.1) renders reducer models: because the model is the
  state-indexed GADT, **impossible UI states are unrepresentable** — the
  loading spinner literally cannot render alongside the error banner.

## 9. `check` integration

Per parent §7.5, `reducer` **ships property templates** — suites the user
never wrote: graph conformance (only declared edges are ever taken; the
catch-all rejects everything else) and init-schema validity. A `reducer`'s
`Msg` type derives a message-sequence generator, enabling temporal
properties — bounded model checking without ever saying those words:

```cure
check Door
  prop faults_are_announced(msgs: List(Door.Msg)) =
    run(Door, msgs)
    |> always(fn(step) ->
         step.state == Fault implies step.emissions.contains(Faulted))
```

And the static-discharge pass pays the dependent types off as deleted work:
`retries_bounded` reports `proved by construction — Opening.retries :
Bounded(3); 0 runs`. Generator strategy for solver-narrowed refinements and
the template-attachment interface remain ledgered in the parent (§9 item 17).

## 10. Open decisions (ledger)

Items 1–5 consolidate parent §9 items 9–13; 6–7 are new. Facility-level
dependencies stay ledgered in the parent, not duplicated here: tier-4
reflection API for `clause_to_arm` (item 5), staging for forward references
to `Door.State`/`Door.Msg` (item 6), guard→refinement-context reach (item
16), `check` interfaces (item 17).

1. **Clock sample-vs-merge trigger** — Door samples (`with_latest`); Debounce
   merges `clock.tick` as an internal message. Is the merge inferred from
   "some clause consumes a tick message," or opted into explicitly?
2. **Family tag semantics** — `reducer Name fsm`: what other families does
   the tag admit (`reducer Name flow`?), and is a **GenServer-lowering
   adapter** offered for non-Flow contexts (an OTP process wrapping the same
   pure step function)?
3. **Guard-coverage strategy** — multiple graph edges per (state, message)
   pair are resolved by `when` guards; completeness across guarded
   alternatives is **undecidable in general** ⇒ the mandatory catch-all is
   the current answer. Decide whether the refinement checker should
   additionally *prove* per-pair guard exhaustiveness when it can (e.g.
   `retries < 2` / `retries == 2` is exhaustive over `Bounded(3)` precisely
   because the bound caps `retries` at 2).
4. **Catch-all binder shape** — `on _ with (model, msg)` binds the dependent
   pair, with `model.state` as index-projection sugar; confirm the sugar.
5. **Singleton-rule scope** — bare constructor in type position ⇒ singleton
   refinement (`motor: Stopped`): a general language rule or per-macro
   elaboration?
6. **Emission ordering guarantees** *(new)* — a step that both changes the
   model and emits produces one atomic `Step`, but downstream `model` and
   `emission` are separate streams. Specify what a consumer observing both
   may assume within a tick (does `emission` see the pre- or post-step
   `model` via `with_latest`?) — the Flow glitch-freedom contract applied to
   the split streams; it must be stated, not discovered.
7. **Reducer composition/nesting** *(new)* — Elm-scale programs compose
   update functions (child reducer embedded in a parent's payload, message
   wrapping/routing). First-class composition (a child's `Step` lifted into
   the parent's) vs. composition at the `flow` level (wire two `body`
   outputs together) is undecided; Flow citizenship means the latter works
   today by construction.

## 11. Non-goals

- **No kernel/TCB delta.** The macro lives entirely in the untrusted
  frontend; its output is re-elaborated and kernel-checked like hand-written
  code (parent §5.3). A buggy `Reducer` macro can reject or confuse, never
  produce an unsound program.
- **No proof-authoring surface.** An obligation that does not discharge by
  computation gets an explainer or a narrower surface — never a goal shown
  to the user.
- **Not a replacement for `fsm`/`actor`** — `reducer` is the typed-payload,
  Flow-lowered family member; raw `fsm` remains for payload-uniform machines.
- **Not a GenServer framework in v1** — the lowering target is Flow
  (`Signal.scan`); an OTP adapter is ledgered (§10 item 2), not assumed.
- **No dynamic state schemas** — states, edges, and per-state fields are
  static declarations; that is what makes the model GADT, the coverage
  checks, and the zero-byte erasure possible.
