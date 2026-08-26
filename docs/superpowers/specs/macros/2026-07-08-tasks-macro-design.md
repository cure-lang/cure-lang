# `every` / `on` — Periodic Tasks & Event Handlers

**Date:** 2026-07-08
**Status:** design (operator-requested). Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
(§6.5); built as a `macro` (§5) — **Tier-2 template sugar** per §5.2. The
`Every` macro definition sketched verbatim in parent §5.1 is canonical; this
spec completes it and extends the same treatment to `on`.

---

## 1. Purpose

The two verbs every embedded program needs — *do this periodically* and *do
this when the pin changes* — as one-line module-level containers with no
process vocabulary, no `start/0`, no supervision plumbing. Handlers are
ordinary total Cure, so size-change termination delivers the headline
guarantee **today**: callbacks provably terminate — sold to the user as
**"your board cannot hang; the watchdog never fires because of your logic."**
Raw `receive`/`spawn` are compiler-rejected (E043); these containers are the
sanctioned path, and they cost the user zero concepts.

## 2. Surface

```cure
mod Greenhouse
  board :esp32c3
  let fan = gpio.out(pin.gpio5)

  every 500ms
    gpio.toggle(fan)

  on rising(pin.gpio9) debounce 20ms
    fan.toggle()
```

Rules:

- **`every <duration>`** + indented block. The duration is a units-macro
  literal (`500ms`, `2s`, `10us` — parent §6.6); a bare number is an error
  (§6, E115 style).
- **`on <edge>(<pin>) [debounce <duration>]`** + indented block. Edges:
  `rising`, `falling`, `change`. The pin must carry the `input` capability
  from the board declaration; `debounce` is optional and takes a duration
  literal.
- Both are **module-level containers** (same family as `fsm`/`actor`/`sup`),
  brought in by `use Hardware.Tasks`. Any number per module.
- **Reserved, not enforced:** `every 500ms within 5ms` / `on rising(...)
  within 5ms` — a deadline annotation that parses today and rides the
  reserved cost/WCET grade axis (Final-Core grammar §B.1). Until that axis
  lands its enforcement, `within` produces a "not yet checked" note, never
  silence pretending to be a guarantee.

## 3. Lowering

Pure `expand` templates onto the real, ESP32-proven `fsm` container.

**`every`** — parent §5.1's template, canonical:

```cure
every $period $body ~>
  fsm $fresh(Tick) with Unit
    Idle --tick--> Idle
    @timer $period
    on_timer
      (:idle, s) -> { $body; %[:ok, s] }
```

**`on`** — same shape, driven by the GPIO interrupt NIF instead of `@timer`.
AtomVM's GPIO driver delivers edge interrupts **as messages** to a subscribed
process; the generated fsm subscribes at init (`gpio.set_int(pin, :rising)` via
`@extern`) and consumes those messages as its event. Debounce is a timestamp
guard in the fsm payload — no extra process, no timer juggling:

```cure
on rising($pin) debounce $window $body ~>
  fsm $fresh(Watch) with Int              # payload: last accepted edge, ms
    Armed --edge--> Armed
    on_init  -> gpio.set_int($pin, :rising)
    on_edge
      (:armed, last) ->
        let now = monotonic_ms()
        if now - last >= $window then { $body; %[:ok, now] }
        else %[:ok, last]
```

(Without `debounce`, the guard is elided.) `$fresh` names are hygienic; the
user cannot collide with or observe the generated machine.

**Supervision & boot.** All task fsms in a module are children of one
generated `sup`, which the auto-generated `start/0` (parent §2) boots along
with the FSM runtime. A crashing handler restarts alone; the blink survives
the button handler's bug. The user wrote neither the sup nor `start/0`.

## 4. Invisible machinery

- **Totality = the watchdog story.** The block body becomes an ordinary
  `on_timer`/`on_edge` clause body — checked by the same size-change
  termination pass as all Cure code. No annotation, no opt-in: an `every`
  block that can loop forever does not compile (§6).
- **Pin capability.** `rising(pin.gpio9)` demands the `input` capability on
  the board-indexed pin type (parent §6.1) — discharged by literal
  computation, surfaced only on failure, in hardware vocabulary.
- **Effects — the honest v1 story.** Handlers do **not** run in a true ISR.
  On the BEAM, AtomVM interrupts arrive as messages to a scheduled process;
  the VM serializes handler execution with everything else. So the classic
  ISR constraints (no allocation, no blocking, reentrancy) do not apply and
  v1 imposes none — claiming otherwise would be theater. What v1 *does*
  check, composing with the `!` effect discipline (companion spec): handler
  bodies get an implicit handler-context effect set, and calls whose
  signatures carry long-blocking effects (bus transactions with deadlines,
  network sends, `sleep`) inside an `on` body produce a **lint** — "this
  handler can be delayed behind gpio events it hasn't consumed; move slow
  work into an `every` task or an actor." When the parent's `:isr` context
  effect (§6.10) becomes real (native-ISR targets, cost axis), the lint
  hardens into the error it is pretending toward — additively.

## 5. Explainers

Bare number (the E115 exemplar, shared with units):

```
error[E115]: every expects a duration, got a bare number
  --> main.cure:7
  Write the unit: every 500ms, every 2s.
```

Non-terminating handler (size-change failure, translated):

```
error[E150]: this handler might never finish
  --> main.cure:9
  The loop inside this `every` block has no exit — nothing in it gets
  smaller each time around. A handler must finish before its next tick;
  a handler that runs forever is how boards hang and watchdogs fire.
  Move ongoing work into its own `every` task, or make the loop count down.
```

Pin without input capability:

```
error[E151]: pin gpio21 cannot watch for edges
  --> main.cure:12
  gpio21 is claimed as uart0.tx (board default) and has no input capability
  here. Input-capable free pins on your board right now: gpio3, gpio9, gpio10.
```

## 6. `check` integration (shipped templates)

- **Termination** reports as *proved by construction* (static discharge,
  parent §7.5) — 0 runs; the product moment where the type system deletes a
  test the user expected to need.
- **Debounce** — against the sim clock: two edges inside the window produce
  exactly one body invocation; edges a window apart produce two. Runs on
  `cure run --sim` virtual GPIO.
- **Periodic liveness** — over simulated time, an `every 500ms` body runs at
  least once per period + scheduling slack (slack honesty per §8.1).

## 7. Relations

- **`board`** (parent §6.1) supplies the typed pins and capabilities `on`
  checks against; module-level `let` bindings (the `fan` handle) are in scope
  in task bodies because both elaborate into the same generated `start/0`.
- **units** (§6.6) owns duration literals; this macro only *demands*
  `Duration`, it defines nothing about it.
- **`flow`** (§6.4): `source temp = sensor.celsius every 2s` inside a flow
  block is the same `every` machinery feeding a `Signal` instead of running
  a block — one lowering, two surfaces.
- **`fleet`**: tasks inside a node block are per-device; the fleet spec
  places them, this spec defines them.
- **`driver`**: data-ready interrupt lines (`on drdy_pin rising` inside a
  driver) are ledgered driver-side (driver spec §8.3) — same mechanism, but
  pin ownership must thread from the user's board block into the driver.

## 8. Open decisions (ledger)

1. **Scheduling honesty & jitter.** BEAM scheduling is soft real-time:
   `every 500ms` means "≥ 500ms apart, usually a few ms of jitter, more under
   load" — never a hard deadline. Decide where this is documented (task docs?
   a first-run note?) and whether the sim injects representative jitter so
   host runs don't over-promise. Hard bounds wait for the cost axis
   (`within`).
2. **Drift-free periodics.** Fixed-rate (next tick at t₀+n·p, drift-free)
   vs. fixed-delay (p after handler completion — `@timer`'s natural reading).
   Fixed-rate is what "every 500ms" means in plain English and the likely
   default; requires the generated fsm to schedule against an absolute
   monotonic deadline rather than a relative timer. Decide, and decide
   whether the other mode gets surface (`every 500ms after_each`?).
3. **Alignment.** Do three `every 1s` tasks in one module fire together
   (phase-aligned burst) or spread? Bursts are surprising load spikes;
   deliberate phase offsets are surprising semantics. Likely answer: no
   alignment guarantee stated, independent timers in practice.
4. **Debounce semantics.** The specced guard is *leading-edge* (first edge
   fires, window suppresses the rest). Buttons often want trailing or both.
   Ship leading-only v1, or `debounce 20ms trailing`?
5. **Runtime handles.** Tasks are anonymous and eternal in v1. Start/stop/
   re-rate at runtime (`let t = every 500ms ...; t.pause()`) is real demand
   (deep sleep, modes) but makes tasks values — expression position, escape
   analysis. Defer, but reserve nothing that blocks it.
6. **Deep-sleep interaction.** `sleep.deep(...)` vs. a live task schedule:
   which `on` pins become wake sources, does an `every` schedule spanning
   sleep resume or restart, and does entering sleep with un-pausable tasks
   error (composes with §6.9 peripheral-release enforcement)?

## 9. Non-goals

- **No preemptive or hard-real-time semantics.** BEAM scheduling, honestly
  described (§8.1); deadlines arrive with the cost/WCET grade axis, not
  before.
- **No general cron surface.** Calendar scheduling (`job` — parent §7.3) is
  host-side and a different macro.
- **No true ISR-context code in v1.** AtomVM delivers interrupts as
  messages; we do not pretend to run user code in interrupt context, and we
  do not impose fake ISR restrictions on code that doesn't (§4).
