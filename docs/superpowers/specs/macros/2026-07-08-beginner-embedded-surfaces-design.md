# Beginner-Facing Embedded Surfaces — DSL Catalog & Ergonomics

**Date:** 2026-07-08
**Status:** product-direction design (operator-requested). Not scheduled; no wave
assignment. This is the *surface* counterpart to the dependent-kernel cleanup —
it defines what all that machinery is ultimately *for*.
**Goal:** make Cure a total no-brainer for custom ESP32 / Pico / embedded-Linux
projects, for users who will never learn what a Pi type is — while delivering
100% of the dependent-type benefits through domain DSLs.
**Scope note (2026-07-08):** with the `macro` facility (§5), embedded is the
*first vertical*, not the identity — §7 catalogs beginner macros across every
domain (web, data, services, distributed, play).

Companion documents:
- Kernel foundation this rides on: [`2026-07-07-final-core-grammar-design.md`](../kernel/2026-07-07-final-core-grammar-design.md)
  (grades §B power ownership/IFC; delta-globals §G power literal-index discharge).
- Effects: [`2026-07-07-sound-effect-discipline-design.md`](../effects/2026-07-07-sound-effect-discipline-design.md)
  (capability manifests, §6.10).
- FRP/Flow: the reactive-runtime design bible (v12) — the flagship DSL; this doc
  does not respecify it, only positions it.

## Child-spec index (2026-07-08 — every surface below is fully specced)

Infrastructure: [macro facility](2026-07-08-macro-facility-design.md) (§5's
home; the ONE compiler feature) ·
[error explainers](2026-07-08-error-explainer-design.md) (§4's home; provenance,
registry, code allocation E100–E199) ·
[toolchain & ergonomics](2026-07-08-toolchain-ergonomics-design.md) (§2's home;
`cure` CLI, images, host sim, REPL, LSP).

Macros: [board](2026-07-08-board-macro-design.md) ·
[driver](2026-07-08-driver-macro-design.md) ·
[packet/codec](2026-07-08-packet-codec-macro-design.md) ·
[tasks (`every`/`on`)](2026-07-08-tasks-macro-design.md) ·
[units](2026-07-08-units-macro-design.md) ·
[config/secret](2026-07-08-config-secret-macro-design.md) ·
[reducer](2026-07-08-reducer-macro-design.md) (consolidates §5.5) ·
[check](2026-07-08-check-macro-design.md) ·
[web trio (api/view/form)](2026-07-08-web-trio-macro-design.md) ·
[schema](2026-07-08-schema-macro-design.md) (absorbs §6.11 OTA migration) ·
[parse](2026-07-08-parse-macro-design.md) ·
[cli/job](2026-07-08-cli-job-macro-design.md) ·
[workflow/bot](2026-07-08-workflow-bot-macro-design.md) ·
[protocol](2026-07-08-protocol-macro-design.md) ·
[fleet](2026-07-08-fleet-macro-design.md) ·
[sim/pattern](2026-07-08-sim-pattern-macro-design.md) (games scoped to
tutorials there) ·
[cad](2026-07-08-cad-macro-design.md) (beyond-MCU §7: host-side solid
modeling; the "no result builders" worked case) ·
[crochet](2026-07-08-crochet-macro-design.md) (knit's sibling; position-
vector state, the form-aware flat-circle law).

Error-code blocks are authoritative in the error-explainer spec §5
(E100–E199, per-macro); where an older informal code in THIS document
disagrees with a child spec, the child spec wins.

---

## 1. Thesis

Cure's moat is real: BEAM concurrency semantics + provable totality + invisible
dependent types on a $3 microcontroller. Nothing in the Arduino / MicroPython /
embedded-Rust space has that combination.

Embedded is the *ideal* domain for hidden dependent types for one structural
reason: **the indices are almost always concrete literals.** Pin 5, address
0x76, 9600 baud, 32-byte buffer, 12-bit ADC. With the delta-reducing kernel and
whnf-before-unify, virtually every proof obligation discharges by pure
computation — no solver interaction, no proof term, no hole ever surfaced to the
user. Dynamic-size data (where dependent types get hard) is rare on a
microcontroller, and where it appears (packets) the length is carried in a
header field that is parsed first.

The through-line for every surface below:

> **Users declare facts; the compiler manufactures types; errors speak the
> user's vocabulary; every guarantee is marketed as the crash it prevents.**

### Target hardware honesty

"Arduino" is a *demographic*, not a target. AtomVM needs ESP32-class silicon.
Supported targets: ESP32 family, RP2040/Pico, STM32, and Linux SBCs (RPi) via
generic-unix. Classic AVR boards are out of scope — say so on page one of the
docs; nothing burns trust like a Nano user discovering this at step 4.

---

## 2. Gating ergonomics (not type-system work — but they decide adoption)

"No-brainer" is decided in the first fifteen minutes. Today those minutes are:
install Erlang, Elixir, rebar3, esptool, ESP-IDF 5.4.1, clone and build AtomVM,
restore patches, run a shell script with a flash map in your head. All of it
must disappear:

1. **One binary, one command.** `cure new blink --board esp32c3`, `cure run`
   (host simulation), `cure flash --port auto`, `cure monitor`, `cure repl`.
   Prebuilt versioned VM images per board (formalize the existing `phase1/*.img`
   practice); board manifests carry the flash map so `0x250000` is never typed
   by a human again. The escript + phase scripts become one distributable CLI.
2. **Host-first simulation as a product feature.** The unix-AtomVM loop is
   already the right architecture; expose it as `cure run --sim` with virtual
   GPIO/UART whose pin states render in the terminal. Hobbyists don't have CI;
   give them "ran on my laptop ⇒ runs on the board" for the pure + concurrency
   layer.
3. **LSP + formatter + VS Code extension.** Hover types, inline diagnostics,
   jump-to-def. A dependently-typed language *without* hover types is worse
   than C++ with IntelliSense, because the types carry more meaning.
4. **Error-explainer architecture as a first-class subsystem** (§4). The types
   are invisible until something fails; then the error IS the UX.
5. **REPL / hot code push.** BEAM's birthright and the demo that ends
   arguments: change the blink rate, push over serial/WiFi, no reflash. Even a
   constrained version (swap one module) beats compile-flash-pray so hard it
   becomes the headline feature.

Additional zero-boilerplate rule: a module with a `board` declaration and task
containers **auto-generates `start/0`** — including the AtomVM runtime-boot
calls (`Cure.FSM.Runtime.start_link` etc.) that today every driver program
must hand-write. The "start the runtime manually" gotcha must not exist for
DSL users.

---

## 3. The four hiding principles

Stated design rules for every DSL in the catalog:

1. **Indices flow from declarations, never from user annotations.** The user
   states concrete facts about hardware and data (a board file, a register
   map, a packet layout, an FSM). The elaborator manufactures the indexed
   types. Users write values; the DSL writes types.
2. **Correct-by-construction beats proved-correct.** Restrict each DSL so
   ill-formed things are *inexpressible*, not expressible-but-rejected. An fsm
   surface that can only build well-formed transition tables needs no coverage
   proof from anyone.
3. **Obligations discharge by computation or not at all.** If an obligation
   does not reduce away, the answer is a domain-language error or a narrower
   DSL — never a surfaced goal. (The Z3 lint layer may *suggest* — "duty cycle
   can exceed 100 when x > 3" — but per the locked SMT trust boundary it stays
   advisory, outside the TCB.)
4. **`unsafe` is the pressure valve.** The locked holes/unsafe taxonomy gives
   escapees a marked, greppable exit. A visible escape hatch converts "this
   language fights me" into "I'll clean that up later."

---

## 4. Error-explainer architecture

The single most important hiding mechanism. `cannot_unify plus(Z, ?0) S(Z)`
must never reach a user. Mechanism:

- Each DSL layer **registers explainers**: pattern-matched translators from
  kernel/elaborator failure shapes (+ the DSL-attached metadata on the term's
  provenance) back into the DSL's own vocabulary.
- Every DSL-elaborated term carries provenance (which surface declaration
  produced it), so a failed conversion deep in the kernel can be attributed to
  "pin 34 in `gpio.out(...)` at blink.cure:5".
- Errors follow a fixed template: *what you wrote → why the hardware/domain
  forbids it → what to write instead*. A datasheet/section reference where one
  exists.
- Fallback: if no explainer matches, the raw error is shown **plus** a note
  that this is a bug in the DSL layer ("please report") — raw kernel errors
  reaching users is a defect by definition.

Build this as infrastructure now, while the DSL count is small; retrofitting
per-DSL error reflection later is misery.

Representative target quality:

```
error[E102]: pin gpio34 cannot be used as an output
  --> blink.cure:5
   |
 5 |   let led = gpio.out(pin.gpio34)
   |                      ^^^^^^^^^^
  ESP32 pins 34–39 are input-only (no output driver hardware).
  Free output-capable pins on your board right now: gpio4, gpio5, gpio16, gpio17.
```

---

## 5. The `macro` facility — DSLs are defined in Cure

**Decision (operator, 2026-07-08): the DSLs themselves are written in the
language.** The compiler grows exactly ONE new frontend feature — a facility
for *defining* DSLs — and every surface in the catalog (§6) is library code
built on it. No per-DSL special treatment in the compiler; `board`, `driver`,
`packet`, `every` ship as ordinary Cure packages that happen to export syntax.

Reference model: Lean 4's `syntax`/`macro_rules`/`elab_rules` tower (hygienic,
in-language, layered by power), with Idris-style elaborator reflection as the
top tier. Racket proves the ecosystem effect: when extending the language is
library work, the ecosystem writes the languages.

### 5.1 Surface

A `macro` is a container (same family as `fsm`/`actor`/`sup`) with three
parts — grammar, expansion, and explainers:

```cure
macro Every
  ## `every <duration>: <block>` — run a block periodically, supervised.

  syntax every $period:Duration $body:Block

  expand
    every $period $body ~>
      fsm $fresh(Tick) with Unit
        Idle --tick--> Idle
        @timer $period
        on_timer
          (:idle, s) -> { $body; %[:ok, s] }

  explain
    {:no_instance, Duration, t} ->
      "every expects a duration — write every 500ms or every 2s (got " <> show(t) <> ")"
```

- **`syntax`** declares a grammar rule with *typed* non-terminals (`Duration`,
  `Block`, `UpperIdent`, `Indented(FieldDecl)`, …). Because rules are
  declarative data, the LSP gets highlighting/completion for every macro
  with zero per-DSL work — a structural consequence, not a feature request.
- **`expand`** is hygienic template rewriting (`~>`), for DSLs that are pure
  sugar over existing surface (most of them). `$fresh(..)` names are
  auto-hygienic; user identifiers cannot be captured.
- **`elab`** (not shown above) is the next tier: a **compile-time total Cure
  function** from quoted syntax to quoted syntax, for DSLs that compute
  (packet layouts, register maps). Staged: runs on the host at compile time,
  so no AtomVM constraints apply to it. Macro functions pass the same
  size-change termination checker as everything else — **Cure compilation
  provably terminates even with user-defined syntax**, which Lean does not
  give you.
- **`explain`** registers error explainers (§4). Expanded terms automatically
  carry provenance (macro name + source span), so a kernel failure deep
  inside generated code is attributed to the user's surface line.

Macro syntax is **scoped by import** (`use Hardware.Every` brings the
`every` keyword into the module), so macros compose without a global
grammar war.

### 5.2 Power tiers (and where each catalog entry sits)

| Tier | Mechanism | Catalog users |
|---|---|---|
| 1. Declarative data | `syntax` + `elab` over quoted decls | `boarddef`, `driver`/`regmap`, `packet`, `config` |
| 2. Template sugar | `syntax` + `expand` | `every`, `on`, `secret`, module-level `let` |
| 3. Literal rules | `literal $n ms ~> Duration.ms($n)` | units of measure (§6.6) |
| 4. Type-directed | `elab` with elaboration-API access (reflection-lite) | `flow` (index inference) |

Tier 4 is the only hard one; `flow` may stay semi-built-in initially and
migrate once the reflection API stabilizes.

### 5.3 Soundness story (why this is safe to hand to users)

Macro output is **re-elaborated and kernel-checked like hand-written
code** — the facility lives entirely in the untrusted frontend, upstream of
the elaborator, with the Final-Core validator and kernel unchanged behind it.
A buggy macro can produce a confusing error or a rejected program, **never
an unsound one**. This is the same layering argument as the elaborator itself:
UX bugs are possible, soundness bugs are not. (TCB delta: zero.)

### 5.4 Dogfood test

The facility is done when `fsm` itself could be re-expressed as a macro
(whether or not we actually move it). If the meta-layer can't express our own
flagship container, it isn't powerful enough for third-party driver authors.

### 5.5 Worked example — `reducer` (operator-designed, 2026-07-08)

`reducer` is `fsm` where the **payload type depends on the current state**
(per-state schemas via `State over {…}`), with typed `emits`/`rejects` streams
and a SwiftUI-style `body` that lowers onto the Flow runtime as a
`Signal.scan`. It exercises every tier at once: derived index types, GADT
model, refinement-carrying guards, and FRP lowering.

#### The surface (operator's design, verbatim)

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

Design notes captured from the surface: the graph deliberately allows
**multiple edges per (state, message) pair** (nondeterministic in the graph,
resolved by `when` guards in the body); header lines declare **capabilities**
(`clock`) that clauses receive as binders; the user's own `type` declarations
reference the macro-**derived** names `Door.State`/`Door.Msg` (a staging /
name-resolution consequence — see Open decisions §9); the mandatory final
catch-all binds the whole model with `model.state` projecting the dependent
pair's index.

#### The intended lowering (operator's `Signal.scan` shape, Debounce instance)

The SwiftUI analogy is load-bearing: like a `View`'s `body` producing `some
View`, a reducer's `body` is a pure description consumed by a runtime that
owns the state loop. The target shape, shown for a time-driven Debounce
reducer:

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
statically-empty rejection stream. And because `body`'s inputs and outputs are
`Signal`/`Event`, **reducers are Flow citizens**: they compose inside `flow`
blocks directly (`sink motor <- Door.body(clock, presses).model |> …`).

#### The macro definition

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

What the invisible machinery does in the operator's Door example:

- `on … from Opening with (payload, …)` gives `payload :
  Door.Payload.Opening` by **index refinement** — `payload.retries` exists
  here and is a compile error in a `from Closed` clause.
- `payload.retries + 1 : Bounded(3)` type-checks **because the `when
  payload.retries < 2` guard flows into the refinement context** — the guard
  does double duty: runtime dispatch + static bound discharge.
- Singleton fields (`motor: Stopped`) and the pair's state tag are erased —
  the runtime model is just the payload fields (ESP32 zero-footprint story).
- The catch-all + edge-coverage checks make the scan function total —
  size-change gives "this reducer provably cannot hang."
- Clock nuance: Door only *samples* the clock (`with_latest`); a time-driven
  reducer (Debounce) instead **merges** `clock.tick` as an internal message —
  visible in the operator's expansion above. The macro emits the merge
  exactly when some clause consumes a tick message — same grammar, one
  conditional in the elab (trigger rule is an open decision, §9).

Honest gap: this macro sits at the top power tier — `clause_to_arm` must
*construct* GADT match arms and record literals against macro-derived types,
which is `elab`-with-reflection territory (§5.2 tier 4), same as `flow`.
**`reducer` therefore joins `fsm` in the dogfood test (§5.4):** the facility
is done when this file compiles as a library.

---

## 6. The DSL catalog

Ordered by leverage. Each entry: surface sketch (in real Cure idiom — container
keyword + indented block, matching `fsm`/`actor`/`sup` style), what the user
gets, the invisible machinery, and a representative error.

### 6.0 The composed experience — a complete first program

What the catalog adds up to. A greenhouse controller with no `start/0`, no
runtime boot, no flash offsets, no visible types:

```cure
mod Greenhouse
  board :esp32c3

  config
    ssid: String        = env("WIFI_SSID")
    pass: secret String = env("WIFI_PASS")

  let fan    = gpio.out(pin.gpio5)
  let sensor = Bme280.on(i2c0)          # board-default SDA/SCL wiring

  flow Climate
    source temp = sensor.celsius every 2s
    let smooth  = temp |> median(5)
    sink fan <- smooth |> above(30.0)

  on rising(pin.gpio9) debounce 20ms
    fan.toggle()
```

Everything here is silently dependent: `pin.gpio5` is a board-indexed
`Bounded` with an `output`-capability refinement, `median(5)` is a
length-indexed window, the `flow` block carries causality indices proving no
feedback loops or space leaks, `secret` rides the IFC grade axis, and the
handlers are size-change-total (the board cannot hang). The user sees none of
it until an error — which arrives in hardware vocabulary (§4).

### 6.1 `board` — the foundation

Boards ship with Cure (or a package); users *select*, driver/board authors
*declare*. Selecting a board brings a typed `pin` namespace, bus handles with
board-default wiring, and the flash map for `cure flash`.

User surface (the whole point is this one line):

```cure
mod Blink
  board :esp32c3

  let led = gpio.out(pin.gpio4)

  every 500ms
    gpio.toggle(led)
```

(Module-level `let` for hardware bindings is new surface: it elaborates to
setup code in the generated `start/0`. Note: no `start/0`, no runtime boot,
no flash offsets — all generated.)

Author surface (shipped board definition):

```cure
boarddef Esp32c3
  chip   :esp32c3
  flash  4mb, app_offset 0x250000, libs_offset 0x1d0000
  pins   gpio0..gpio21
  caps   gpio0..gpio5:   [input, output, adc]
  caps   gpio2:          [input, output, strapping]   # boot-mode warning
  caps   gpio18..gpio19: [input, output, usb]
  bus    i2c0 (sda: gpio8, scl: gpio9)
  bus    uart0 (tx: gpio21, rx: gpio20)
```

Invisible machinery: `pin.gpioN : Pin(Esp32c3, n)` is the landed
`Bounded`/Fin builtin indexed by the board; capabilities are refinements on
that index; `gpio.out` demands the `output` capability. Everything discharges
by literal computation. Strapping pins produce *warnings* with boot-mode
explanations, not errors.

Kills: the single most common category of beginner hardware bug (wrong/
incapable/nonexistent pin), at zero user-visible type cost.

### 6.2 `driver` / `regmap` — the ecosystem play

Declare a peripheral from its datasheet; get a typed driver. Contributing a
driver becomes a declarative afternoon, which is how a package ecosystem
actually happens (the thing that makes Arduino sticky).

```cure
driver Bme280 over I2c(0x76)
  ## Bosch BME280 temperature / humidity / pressure sensor.

  reg chip_id   at 0xD0, read              # Byte by default
  reg reset     at 0xE0, write
  reg ctrl_meas at 0xF4, read_write
    field osrs_t: bits(7..5)               # temperature oversampling
    field osrs_p: bits(4..2)
    field mode:   bits(1..0)
  reg raw_temp  at 0xFA, read, bytes(3)

  init                                     # the attach protocol (typestate!)
    expect read(chip_id) == 0x60 else :wrong_chip_id
    write(ctrl_meas, %{osrs_t: 1, osrs_p: 1, mode: 3})

  fn celsius(d: Bme280) -> Celsius =
    raw_temp |> read() |> compensate(d.calibration)
```

User side:

```cure
let sensor = Bme280.on(i2c0)          # runs init; Result(Bme280, DriverError)
let t = sensor.celsius()
```

Invisible machinery: register writes are range-refined (a reserved bit is
unwritable — refinement on the field's `bits(..)` window); the `init` protocol
is **typestate** — the device handle's state is an index (the landed GADT-ctor
machinery), so `read` before `Bme280.on(...)` is a compile error. Field packing
math (`bits(7..5)`) is checked non-overlapping at compile time.

Representative error:

```
error[E110]: BME280 is not configured yet
  --> greenhouse.cure:14
  `celsius()` requires an attached sensor. Call `Bme280.on(i2c0)` first —
  the BME280 needs its ctrl_meas register set before sampling (datasheet §5.4).
```

### 6.3 `packet` — wire formats without overruns

Erlang bit-syntax power with length-dependence, behind a layout declaration:

```cure
packet Frame
  magic:   const 0xA7
  version: Byte
  length:  Byte
  payload: bytes(length)                 # indexed by the field above
  crc:     crc8 over [version, length, payload]
```

Generated: `Frame.parse : Bytes -> Result(Frame, ParseError)` and
`Frame.encode : Frame -> Bytes`, with `f.payload : Bytes(f.length)`.

```cure
match Frame.parse(chunk)
  Ok(f)    -> handle(f.payload)
  Error(e) -> log.warn(e)               # e says which field, at which offset
```

Invisible machinery: `payload` is a length-indexed vector (the Vector/Nat→Int
erasure work — zero runtime cost); parse cannot overrun by construction; CRC
coverage is declared, not hand-offset. The round-trip property
`parse(encode(f)) == Ok(f)` is proved/Antigen-checked **once, centrally, at
the library level** — every user-declared packet inherits it for free.

Covers: UART protocols, I2C payloads, LoRa frames, MQTT payloads, NMEA, etc.

### 6.4 `flow` — the FRP flagship (positioning only; see the design bible)

```cure
flow Climate
  source temp  = sensor.celsius every 2s
  let smooth   = temp |> median(5)
  let too_hot  = smooth |> above(30.0)
  sink fan <- too_hot
```

Invisible machinery: the Safe-FRP decoupledness/causality indices prove no
instantaneous feedback loops and no space leaks. Marketing rule: sell the
symptom prevented ("cannot deadlock, cannot leak, doesn't wedge after two
days"), never the theory.

### 6.5 `every` / `on` — tasks and interrupts

```cure
every 500ms
  gpio.toggle(led)

on rising(pin.gpio9) debounce 20ms
  fan.toggle()
```

Sugar over `fsm` + `@timer` / GPIO-interrupt NIFs; auto-supervised. Because
handlers are ordinary total Cure, **size-change termination already gives the
headline guarantee today**: callbacks provably terminate — user-visible as
"your board cannot hang; the watchdog never fires because of your logic."

Future (reserved cost-grade axis): `on rising(pin.gpio9) within 5ms` — real
deadline checking, an additive grade axis per the Final-Core grammar §B.1.

### 6.6 Units of measure

Literal suffixes for the quantities embedded code actually uses:

```cure
sleep(500ms)        # not sleep(500)  — of what?
pwm.set(fan, 80pct) # duty is {n: Int | 0 <= n and n <= 100}
uart.open(pin.tx, 115200baud)
adc.read(pin.gpio3) # -> Raw12  (0..4095), convert with .millivolts()
```

Invisible machinery: refinement types over native ints (Nat→Int erasure ⇒
zero runtime cost). Kills the ms/µs and percent/fraction bug class.

```
error[E115]: sleep expects a duration, got a bare number
  --> main.cure:9
  Write the unit: sleep(500ms), sleep(2s), sleep(10us).
```

### 6.7 `config` — validated deployment config

```cure
config
  ssid:   String        = env("WIFI_SSID")
  pass:   secret String = env("WIFI_PASS")
  broker: Host          = "mqtt.local"
  topic:  Topic         = "home/greenhouse/temp"
```

Checked at build: SSID length limits, topic grammar, host syntax, pin
non-conflict with the board file. Boring, high-value, pure refinements.

### 6.8 `secret` — the IFC lattice in one word

The grade record's security axis (Final-Core §B.3), surfaced as a single
keyword. A `secret` value cannot flow to serial, MQTT publish, HTTP, or logs
without an explicit, audited `declassify`:

```
error[E120]: `cfg.pass` is secret and cannot be written to serial output
  --> main.cure:22
  pass was declared secret in config (main.cure:6).
  If you really mean it: puts(declassify(cfg.pass, reason: "debugging"))
```

"The compiler proves your API key can't leak over the wire" is a no-brainer
sentence for the IoT crowd; the machinery is already designed (default-off
trivial lattice ⇒ zero cost when unused).

### 6.9 Pin/bus ownership — linearity's payoff

Once usage `1`/`≤1` enforcement lands (grade wave), claimed pins and buses are
linear resources:

```
error[E118]: pin gpio21 is already in use
  --> main.cure:11
  gpio21 was claimed as uart0.tx (board default) at main.cure:7.
  A pin can only do one job. Free it with uart.close(u), or pick another pin.
```

Deep-sleep enforcement: entering `sleep.deep(...)` without releasing claimed
peripherals is a compile error. Rust users recognize this as the borrow
checker's embedded pitch — Cure gets it from grades with no lifetime syntax.

### 6.10 Effects as capability manifests

The `!` effect discipline (companion spec) doubles as a hardware capability
report: `fn poll() ! Gpio, Wifi` tells the reader (and LSP hover) exactly what
hardware a function touches. An `:isr` context effect rejects blocking/
allocating calls inside interrupt handlers — the second-most-common Arduino
footgun, gone.

### 6.11 OTA state migration (long horizon)

Firmware v2 declares how to migrate v1's persisted FSM state; the migration is
checked total and type-correct against both schemas (dependent records).
"Update a deployed fleet without bricking state" — no one in this space has it.

---

## 7. Beyond the MCU — the macro facility de-specializes Cure

**Operator direction (2026-07-08): since macros are library code, Cure is
not "an MCU language" — it is a BEAM language where libraries are languages.
Embedded is the first vertical, not the identity. Consider every domain.**

One cross-cutting superpower before the catalog: **one declaration, both ends
of the wire.** A `packet`, `protocol`, or `schema` declared once compiles to
the ESP32 firmware *and* the host/server side, because Cure targets BEAM
everywhere. A sensor's frame layout, a fleet's telemetry topic, a device↔cloud
session — each is a single source of truth with both endpoints generated.
No other language in the hobbyist space can say this.

### 7.1 The web trio — `api`, `view`, `form` (the Elm architecture, completed)

`reducer` (§5.5) already *is* Elm's update function. Three macros complete
the architecture:

- **`api`** — declare routes with typed, refinement-validated params; total
  handlers; generated typed client + OpenAPI export; per-request supervision
  (a crashed handler is a 500, never a crashed server — BEAM's pitch, free).

  ```cure
  api Todos
    get    /todos/$id:{i: Int | i > 0}  -> Todo
    post   /todos  body: NewTodo        -> Todo
    delete /todos/$id                   -> Unit

    on get(id) -> store.find(id) else reject NotFound(id)
  ```

  Invisible machinery: path/query/body schemas are indexed parsers (the
  `packet` machinery pointed at HTTP); the route table is
  correct-by-construction (no unreachable routes, no unparsed params).

- **`view`** — `Signal(Model) -> Html(Msg)` on the Flow runtime:
  LiveView-grade server-rendered UI. Because the model is the reducer's
  state-indexed GADT, **impossible UI states are unrepresentable** — the
  loading spinner literally cannot render alongside the error banner.

- **`form`** — multi-step forms/wizards as typestate: step 3's type does not
  exist without step 2's data; field refinements generate client-side hints
  *and* server-side validation from one source.

### 7.2 Data — `schema`, `codec`, `parse`

- **`schema`** — typed storage (ETS/DETS/SQLite): columns as refinements,
  foreign keys as indices, and **migrations checked total and
  schema-compatible** — the OTA state-migration machinery (§6.11)
  generalized to every persistent store.
- **`codec`** — `packet` (§6.3) generalized to JSON/CBOR/MessagePack;
  round-trip (`decode(encode(x)) == Ok(x)`) proved once, centrally, inherited
  by every user schema.
- **`parse`** — PEG-style grammar blocks compiling to total, typed parsers:

  ```cure
  parse Semver
    version <- major "." minor ("." patch)?   -> Version
    major   <- digits                          -> Int
  ```

  Strategic bonus: this **retires the `Std.Regex` dead-end on device** — a
  grammar compiles to pure Cure and runs anywhere AtomVM does (no `:re`
  needed), and a total parser cannot catastrophically backtrack.

### 7.3 Services — `cli`, `job`, `workflow`, `bot`

- **`cli`** — declare commands/flags/args; get parser, `--help`, and shell
  completion; args are refinement-validated (`port: {p: Int | p >= 1 and
  p <= 65535}`, `file: ExistingPath`). The first program most new users
  actually write.
- **`job`** — scheduled/retrying background work (cron expressions, backoff
  policies) compiled onto `sup` — "your job cannot silently die" is the BEAM
  guarantee surfaced as one keyword.
- **`workflow`** — `reducer` at business timescale (Order → Paid → Shipped),
  persistent, with **event sourcing by construction**: the `Step`'s emissions
  *are* the audit log, and replay is literally `Signal.scan` over history.
  Typestate means a refund handler for an unpaid order is a compile error.
- **`bot`** — chat/messaging bots (Telegram/Discord/Slack/MQTT):
  conversations are FSMs, per-user sessions are actors (BEAM's exact sweet
  spot), and conversation typestate makes "ask for payment before a cart
  exists" inexpressible.

  ```cure
  bot Support
    session over Idle    { user: UserId }
    session over Ordering{ user: UserId, cart: Cart }

    on "/start" from Idle     -> say("Hi! What do you need?") then Menu
    on "/pay"   from Ordering with (s) -> checkout(s.cart)    then Paid
  ```

### 7.4 Distributed — `protocol`, `fleet`

- **`protocol`** — session-typed messaging between nodes, devices, or
  services: one declaration generates *both* endpoints; sending the wrong
  message at the wrong protocol step is a compile error at either end.
  Dependent session types, surfaced as "conversation steps." **Fully
  specced** (two-party v1, `choose`-at-role grammar making bad projections
  inexpressible, typestate handles + `serve` container, tag elision on the
  wire, affine handles, IFC×transport check): see
  [`2026-07-08-protocol-macro-design.md`](2026-07-08-protocol-macro-design.md).
- **`fleet`** — declare a device fleet + telemetry topics once; generate the
  firmware config, the broker topology, and the host-side dashboard glue.
  This is the MCU↔host **bridge product** — the `packet`/`protocol`/`flow`
  declarations shared across the wire (§7 preamble) made into a first-class
  experience, including a `dashboard` surface that renders device `Signal`s
  as live charts. **Now fully specced, including the distributed hub
  illusion (write centralized `hub` logic, compiler projects it onto the
  nodes as peer-to-peer messaging):** see
  [`2026-07-08-fleet-macro-design.md`](2026-07-08-fleet-macro-design.md).

### 7.5 `check` — property testing derived from types

Promoted to its own section (operator, 2026-07-08). This is Antigen's
generator technology — the machinery that soundness-tests Cure's own kernel —
productized for end users. Pitch: *"your types write your tests."* Likely the
single best trust-builder for skeptical newcomers, because it pays off the
type system in a currency every developer already values.

#### Surface

A `check` block holds `prop` declarations. A prop's **arguments are ordinary
typed parameters — the types ARE the generators**, and refinements narrow
them:

```cure
check Greenhouse
  ## Only generates temperatures below the threshold — the refinement
  ## narrows the generator, no filtering, no discarded runs.
  prop fan_off_when_cool(t: {c: Float | c < 30.0}) =
    Climate.step(t).fan == Off

check Semver
  prop roundtrip(v: Version) =
    parse(show(v)) == Ok(v)

check Door
  ## Temporal property over generated message sequences — bounded
  ## model checking, without ever saying those words.
  prop faults_are_announced(msgs: List(Door.Msg)) =
    run(Door, msgs)
    |> always(fn(step) ->
         step.state == Fault implies step.emissions.contains(Faulted))
```

Generator derivation rules: `Bounded(3)` generates `0..2`; `{x: Int | x > 0}`
generates positives; ADTs generate structurally (size-bounded via the same
recursion structure the totality checker already computed); a `packet`
generates *valid frames*; a `reducer`'s `Msg` generates message sequences.
Shrinking is type-aware: a shrunk counterexample **stays inside its
refinement**, so no shrink step is wasted on inputs the property can't even
receive (a classic QuickCheck pain, solved by construction).

#### The static-discharge pass — the signature move

Before running anything, `check` asks the type system whether a property is
**already proved**. Many properties a user instinctively writes are theorems
of the declarations:

```
$ cure test
check Door
  ✓ roundtrip            (200 runs)
  ✓ retries_bounded      proved by construction — Opening.retries : Bounded(3); 0 runs
  ✗ no_reopen_while_open (74 runs, shrunk to 3 messages)
      msgs = [OpenPressed, MotorReachedOpen, OpenPressed]
      after step 3: OpenPressed from Open was rejected (no edge
      Open --OpenPressed--> …). Expected: door re-opens. Add the edge,
      or assert the rejection.
```

That middle line is the product moment: the dependent types surface exactly
once, as *tests you don't have to run*. This inverts the usual pitch —
instead of asking users to believe in types, `check` shows types **deleting
work they already understand**.

#### Certificate elevation — SMT-proved props without user proofs

(Operator question, 2026-07-08.) Between "proved by construction" and "tested"
there is a third rung: **SMTCoq-style certificate reconstruction**. This is
the designed-for "someday" in the locked SMT trust-boundary decision — Z3
stays out of the TCB, but a *proof-producing* solver run can be lifted into
the kernel by reconstruction. Pipeline, per prop, best-effort:

1. Negate the prop; hand it to a certificate-producing solver.
2. On UNSAT, take the certificate (Alethe/LFSC-class proof object).
3. An **untrusted reconstructor** (elaborator-side, like everything else)
   translates the certificate into an ordinary **Core proof term** — a chain
   of `Eq` lemmas, case splits, and arithmetic steps. Ground arithmetic
   discharges by *computation* via the K2 delta table, so certificates only
   bridge the symbolic steps.
4. The kernel checks that term exactly as it checks any term. The prop
   reports `proved (certificate)`.
5. **Any failure at any stage falls back to property testing**, reported
   honestly as `tested (N runs)`. Elevation is monotone and non-blocking —
   solver flakiness or an unimplemented reconstruction rule can never fail a
   build, only demote a rung.

```
  ✓ fan_off_when_cool   proved (certificate — arithmetic, 14 steps kernel-checked)
```

**TCB delta: zero.** The kernel never sees the solver or the certificate —
only a Core term. The alternative architecture (a *trusted* certificate
checker inside the TCB — SMTCoq's verified checker minus the verification) is
**rejected** by uniform strictness. This puts Cure in the
Isabelle-`smt`/SMTCoq family and explicitly not in the Dafny/F* family
(trust-the-solver), consistent with the locked boundary.

Why Cure is unusually well-positioned for reconstruction:

- `prop` bodies are **Bool-valued, hence decidable** — the classical steps in
  an SMT resolution proof reconstruct constructively (`¬¬b == b` holds for
  `Bool`), sidestepping the classical/constructive gap that makes this hard
  in vanilla Coq.
- Ground facts are free: the delta table computes them in-kernel.
- Inductive `Eq` + K/UIP (task #90) is the exact term language derivations
  need.
- Refinement domains (bounded ints, enums, bit-fields) sit inside
  QF_LIA/QF_BV — the fragment where solvers are complete *and* certificates
  are well-understood.

**Honest boundary:** elevation covers the arithmetic/finite fragment —
thresholds, bounds, bit-field disjointness, enum case analysis; i.e. most
obligations arising from `board`/`driver`/`config`/units and many `reducer`
guards. It does **not** cover inductive properties (`parse ∘ show` roundtrips
need structural induction, which SMT does not produce) — those stay tested,
or are proved once by hand in the library as today. The three-rung vocabulary
stays truthful: *proved by construction* / *proved (certificate)* / *tested
(N runs)*.

Operational bonus: the reconstructed Core term is a plain artifact — cache it
and **CI re-checks the proof without invoking the solver at all** (kernel
replay is fast and deterministic; the solver runs only when the prop or its
dependencies change).

#### Macro-shipped property templates

Macro authors ship properties alongside syntax, so users get suites they
never wrote (*"your macros write your tests"*):

- `packet`/`codec` ship `parse ∘ encode == Ok` (§6.3's central proof,
  re-run as a template on the user's own declarations).
- `reducer` ships graph conformance (only declared edges are ever taken;
  the catch-all rejects everything else) and init-schema validity.
- `api` ships "every route parses its own generated requests" and
  "rejections carry the declared reject type".
- `driver` ships "no register write can produce a reserved-bit pattern".

#### Machinery & lineage

- Backend: Antigen's swappable StreamData-style generator backend, reused
  directly; coverage-guided generation (the 2026-07-04 coverage-guided
  fuzzing design) inherits as corpus-driven input search for hard branches.
- Known-label discipline: `prop` + expected verdict is exactly Antigen's
  generator-is-the-oracle pattern — the compiler's kernel and the user's
  greenhouse are tested by the same machinery, which is itself a trust story
  worth telling in the docs.
- Sim integration: props can drive `cure run --sim`'s virtual GPIO — e.g.
  time-indexed flow properties ("the relay never switches faster than 1Hz")
  run against the simulated clock. On-device property runs over the serial
  harness are a deferred follow-up.

Open decisions for this macro are ledgered in §9 (generator strategy for
solver-narrowed refinements; static-discharge reporting UX; the
property-template interface).

### 7.6 Play & learning — `sim`, `pattern`, games

- **`sim`** — agent-based modeling (flocking, epidemics, ecosystems): every
  agent is an actor; BEAM runs a hundred thousand of them on a laptop; the
  clock is a `Signal`. A natural classroom vehicle.
- **`pattern`** — live-coded music, Sonic Pi / TidalCycles style: patterns
  with time indices, hot-swapped over the REPL (§2.5). The BEAM is *proven*
  here — Sonic Pi's own timing core is Erlang — and totality means a pattern
  cannot run away. A pure joy-magnet for exactly the demographic that made
  Arduino big.
- **Games** — `reducer` + `view` is already a game loop; terminal/grid games
  are the teaching vehicle that exercises the whole Elm architecture with
  zero hardware.

This catalog is deliberately non-exhaustive — §5's entire point is that none
of these need compiler work, so the ecosystem can write the ones we don't.

---

## 8. Priorities

By adoption-leverage ÷ effort, given where the codebase stands:

1. Toolchain-in-one-binary + host sim (§2.1–2.2)
2. Error-explainer architecture (§4)
3. `board` DSL (§6.1)
4. `driver`/`regmap` (§6.2)
5. `flow` (§6.4 — already on its own track)

The first two are unglamorous and feel like a detour from the kernel work —
but the kernel cleanup is exactly what makes them safe to build on, and
invisible dependent types are only a *product* if the fifteen-minute path
exists. Everything else is downstream of a user who blinked an LED on day one
and got one good error message on day two.

The `macro` facility does not appear in this list because its *ordering* is
itself an open decision (§9): either it lands first and the catalog ships as
libraries from day one, or early DSLs (`board`, `driver`) ship semi-built-in
for speed and migrate onto the facility once it exists. The decision rule:
whichever gets a real user blinking an LED sooner without creating a second
permanent implementation path.

## 9. Open decisions (deliberately unresolved until implementation)

Recorded per the operator's instruction (2026-07-08): fold everything in now,
resolve when it's time to build. None of these blocks the direction; each is a
fork the implementing spec/plan must close explicitly.

**Facility-level**

1. **Bootstrap order** — macro facility first vs. semi-built-in early DSLs
   that migrate (see §8).
2. **Meta-grammar notation** — the `category` / `syntax` / `::=` sketch, the
   typed non-terminal inventory (`Duration`, `Block`, `RecordTypeBlock`,
   `Many(..)`, `Indented(..)`, `(..)?`), and how literal rules (`500ms`) hook
   the lexer.
3. **Quoted-AST representation** — auto-derived record types per syntax
   category (as assumed in §5.5) vs. one generic `Syntax` type; typing rules
   for `quote` / `$()` splices.
4. **Hygiene mechanics** — `$fresh` semantics, capture rules, cross-macro
   name collisions when two imported macros export the same keyword.
5. **Tier-4 reflection API** — what `elab` may ask the elaborator (needed by
   `flow` and `reducer`'s `clause_to_arm`, which constructs GADT arms against
   macro-derived types). Smallest API that passes the dogfood test wins.
6. **Staging / name resolution** — user `type` declarations may reference
   macro-derived names (`DoorReject` mentions `Door.State`/`Door.Msg`
   before the `reducer` block elaborates) ⇒ needs two-pass resolution or
   forward-declaration semantics.
7. **Migration of existing containers** — whether `fsm`/`actor`/`sup`
   actually move onto the facility or remain built-in (dogfood test §5.4 only
   requires they *could*).
8. **Explainer interface** — failure-shape pattern language, provenance
   metadata format, and how explainers compose when nested macros both
   match.

**`reducer`-level**

9. **Clock sample-vs-merge trigger** — Door samples (`with_latest`), Debounce
   merges `clock.tick` as an internal message; is the merge inferred from
   "some clause consumes a tick message" or opted into explicitly?
10. **Family tag semantics** — `reducer Name fsm`: what other families does
    the tag admit (`reducer Name flow`?), and is a GenServer-lowering adapter
    offered for non-Flow contexts?
11. **Guard-coverage strategy** — multiple graph edges per (state, message)
    pair are resolved by `when` guards; completeness across guarded
    alternatives is undecidable in general ⇒ mandatory catch-all is the
    current answer; decide whether the refinement checker should additionally
    prove per-pair guard exhaustiveness when it can (e.g. `retries < 2` /
    `retries == 2` over `Bounded(3)`).
12. **Catch-all binder shape** — `on _ with (model, msg)` binds the dependent
    pair with `model.state` as index projection sugar; confirm the sugar.
13. **Singleton rule scope** — bare constructor in type position ⇒ singleton
    refinement (`motor: Stopped`): a general language rule or per-macro
    elaboration?

**Surface-level (catalog)**

14. **Module-level `let`** for hardware bindings (elaborates into the
    generated `start/0`) — new surface with ordering/effect questions.
15. **Auto-generated `start/0`** — exact trigger (board decl + containers?),
    interaction with a hand-written `start/0`, and runtime-boot ordering.
16. **Guard→refinement-context flow** — clauses rely on `when` guards
    discharging refinement obligations (`retries + 1 : Bounded(3)` under
    `retries < 2`); confirm the refinement checker's reach here and specify
    the fallback error (§5.5's explainer) when it falls short.
17. **`check` (§7.5)** — generator strategy for solver-narrowed refinements
    (constructive sampling vs. rejection sampling vs. Z3 model enumeration —
    the SMT trust boundary permits Z3 *generation*, since every generated
    value is checked, not trusted); static-discharge reporting UX (report
    "proved" vs. silently skip); the macro property-template interface
    (how `packet`/`reducer`/`api` attach template props to user
    declarations).
18. **Certificate elevation (§7.5)** — which solver produces certificates
    (Z3's proof format is under-specified; cvc5/veriT emit Alethe — Z3 can
    stay the lint solver per the locked decision while a different solver
    produces certificates); reconstruction rule coverage order (resolution +
    CNF + `la_generic`/Farkas first, quantifier instantiation later);
    certificate/term caching policy for solver-free CI replay; whether
    elevated props still run a token K sanity tests (belt-and-braces) or
    honestly report 0 runs.

## 10. Non-goals

- No new kernel/TCB machinery — every DSL elaborates to the Final-Core grammar
  as specified; where a DSL wants an unlanded axis (cost, linearity, IFC), it
  ships the *surface* only when the grade wave lands its enforcement.
- No proof-authoring surface for beginners, ever. If a DSL would need users to
  write a proof, the DSL is wrong (principle 2 or 3).
- No AVR/classic-Arduino target.
- This document does not schedule work; it defines direction and surfaces so
  individual DSLs can be specced/planned per the normal process.
