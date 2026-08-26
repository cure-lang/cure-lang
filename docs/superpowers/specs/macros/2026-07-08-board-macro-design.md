# `board` — Typed Hardware in One Line

**Date:** 2026-07-08
**Status:** design (operator-requested). Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
(§6.1); built as a `macro` (§5). Priority #3 in the surfaces spec — **the
foundation**: every other embedded macro (`driver`, `every`/`on`, `flow`
sinks, `fleet`) consumes what `board` provides, and it kills the single most
common category of beginner hardware bug (wrong / incapable / nonexistent
pin) at zero user-visible type cost.

---

## 1. Purpose

Selecting a board is **one line**. That line brings three things into scope:

1. A **typed `pin` namespace** — `pin.gpio4` exists iff the board has a
   gpio4, and it knows what that pin can do.
2. **Bus handles with board-default wiring** — `i2c0`, `uart0`, pre-wired to
   the pins the board designer chose, so `Bme280.on(i2c0)` works with no
   wiring ceremony.
3. The **flash map** consumed by `cure flash` — a human never types
   `0x250000` again (surfaces spec §2.1).

Boards ship with Cure or as packages. Users *select*; board authors
*declare* (`boarddef`, §3). The two audiences never see each other's
surface.

## 2. User surface

The whole point is this one line:

```cure
mod Blink
  board :esp32c3

  let led = gpio.out(pin.gpio4)

  every 500ms
    gpio.toggle(led)
```

Rules:

- **`board :name`** — one per module, at module top. It scopes the `pin`
  namespace, the bus handles, and the flash manifest to that board. Two
  `board` lines in one module is an error (a fleet of heterogeneous devices
  is `fleet`'s job — one node block per board, §6).
- **`pin.gpioN`** — a plain value at runtime (an int); a board-indexed,
  capability-refined type at compile time (§4). Nonexistent pins fail at
  name resolution with the board's real pin range in the message.
- **Bus handles** (`i2c0`, `uart0`, `spi0`, …) — values carrying their wiring
  as indices. `driver`'s `over I2c(…)` demands an i2c-capable handle; passing
  `uart0` is a domain error, not a unification dump.
- **Module-level `let`** for hardware bindings is new surface: it elaborates
  into the auto-generated `start/0`, which also boots the AtomVM runtimes
  (`Cure.FSM.Runtime.start_link` etc.) per the parent's zero-boilerplate
  rule (§2). Ordering and hand-written-`start/0` interaction are ledgered in
  the parent (§9 items 14–15) — this spec inherits whatever those decide and
  deliberately does not re-decide them.
- No `start/0`, no runtime boot, no flash offsets, no visible types.

## 3. Author surface — `boarddef`

A board definition is declarative data (macro power tier 1): chip, flash
geometry, pin ranges, per-pin capabilities, and bus defaults. The shipped
ESP32-C3 definition, essentially complete:

```cure
boarddef Esp32c3
  ## Espressif ESP32-C3 (RISC-V single core). TRM v1.1.

  chip   :esp32c3
  flash  4mb, app_offset 0x250000, libs_offset 0x1d0000

  pins   gpio0..gpio21

  caps   gpio0..gpio4:   [input, output, adc]        # ADC1 channels
  caps   gpio5:          [input, output, adc]        # ADC2 (see ledger §8.5)
  caps   gpio6..gpio7:   [input, output]
  caps   gpio2:          [input, output, adc, strapping]   # boot-mode pin
  caps   gpio8..gpio9:   [input, output, strapping]        # boot-mode pins
  caps   gpio10..gpio17: [input, output]
  caps   gpio18..gpio19: [input, output, usb]        # USB-Serial-JTAG D-/D+
  caps   gpio20..gpio21: [input, output]

  bus    i2c0  (sda: gpio8,  scl: gpio9)
  bus    uart0 (tx: gpio21, rx: gpio20)
  bus    spi0  (mosi: gpio7, miso: gpio2, sck: gpio6, cs: gpio10)
```

Rules:

- **`chip`** selects the prebuilt VM image family and the NIF surface
  (which `@extern` targets exist).
- **`flash`** is the manifest `cure flash` reads: size plus app/libs
  offsets. The C3 values above are exactly the phase-3 map that today lives
  in a shell script and a human's head.
- **`caps`** — later lines override earlier for overlapping ranges (gpio2
  above), so the common capability is stated once and exceptions stack.
  The capability vocabulary (`input`, `output`, `adc`, `strapping`, `usb`,
  `touch`, `dac`, …) is a fixed set in v1 (ledgered §8.4).
- **Asymmetric capabilities are the payoff case:** classic ESP32 has
  input-only gpio34–39 — its boarddef simply declares
  `caps gpio34..gpio39: [input, adc]` (no `output`), and the E102 error
  (§5) falls out with zero special-casing. The C3 has no such pins, which
  is why the flagship error example uses `:esp32`.
- **`bus`** — named handle + default pin assignment. The pins named here
  must exist and carry the needed capabilities — checked when the boarddef
  elaborates, so a broken board package fails at *its* build, never at a
  user's.

## 4. Invisible machinery

- **`pin.gpioN : Pin(Board, n)`** — the landed `Bounded`/Fin builtin,
  indexed by the board. The pin range in the boarddef fixes the bound;
  `pin.gpio22` on the C3 is out of `Bounded(22)` and fails at elaboration
  with the range in the message.
- **Capabilities are refinements on the index.** `caps` lines elaborate to
  a per-board capability table (delta-reducible global data);
  `gpio.out(p)` demands `has_cap(Board, p, output)`. Because every pin the
  user writes is a **literal**, the obligation discharges by pure
  computation — whnf + the delta table, zero solver, no proof term, no goal
  ever surfaced (hiding principle 3, powered by the Final-Core delta-globals
  work).
- **Strapping pins warn, never error.** `strapping` is a capability like any
  other, but its check emits a *warning* with a boot-mode explanation
  (gpio9 low at reset ⇒ download mode) — using one is often deliberate.
  Warn-once-per-pin vs. per-use is ledgered (§8.6).
- **Bus handles are indexed values.** `i2c0 : Bus(Board, :i2c, %[sda: 8, scl: 9])`
  (shape illustrative) — `driver`'s `over I2c(…)` pattern-matches the bus
  kind; the wiring index is what a future explicit-rewire surface would
  override (§8.3).
- **Erasure: pins are plain ints at runtime.** The board index, the bound,
  and the capability refinements all erase (the Nat→Int erasure story);
  `gpio.out(pin.gpio4)` compiles to the same NIF call the hand-written
  `@extern` program makes today. Zero-footprint on the ESP32.
- **The flash manifest never reaches the type system** — it is plain data
  the boarddef exports; `cure flash` reads it from the build artifact
  (consumption format ledgered §8.7).

## 5. Representative error explainers

The flagship (parent §4, reproduced as this macro's `explain` output — on
`:esp32`, where input-only pins exist):

```
error[E102]: pin gpio34 cannot be used as an output
  --> blink.cure:5
   |
 5 |   let led = gpio.out(pin.gpio34)
   |                      ^^^^^^^^^^
  ESP32 pins 34–39 are input-only (no output driver hardware).
  Free output-capable pins on your board right now: gpio4, gpio5, gpio16, gpio17.
```

The last line is load-bearing: "free … *right now*" means the explainer can
query elaboration state (which pins this module has already claimed via
`let` bindings and bus defaults) — a capability the error-explainer
infrastructure spec must provide, noted here as a **dependency**: explainers
receive not just the failure shape and provenance but a read-only view of
the macro's accumulated declarations.

Others in the family:

```
error[E103]: this board has no pin gpio25
  --> blink.cure:5
  The ESP32-C3 has gpio0..gpio21. Did you mean gpio2? (Pin numbers differ
  between ESP32 variants — check your board, not the tutorial's.)
```

```
warning[W104]: gpio9 is a strapping pin
  --> doorbell.cure:8
  gpio9 selects the boot mode at reset: held low, the chip enters download
  mode instead of running your program. Fine as a button input after boot —
  just don't hold the button while resetting. Prefer gpio10 if unsure.
```

All errors speak hardware vocabulary; none mentions `Bounded`, refinements,
or unification (raw kernel errors reaching users are a defect by
definition, parent §4).

## 6. `check` integration (shipped templates)

`board` is declarations-only, so its templates mostly guard *board authors*
and *downstream macros*:

- **Boarddef self-consistency** — bus pins exist and carry the needed caps;
  capability ranges cover every declared pin; flash offsets fit the declared
  size and don't overlap. Static (elaboration-time), reported as
  `proved by construction` in `cure test`.
- **Pin arithmetic round-trip** — `pin.gpioN` erases to `N` and back; the
  generator draws from `Bounded(pin_count)` for free.
- **Sim conformance** — `cure run --sim`'s virtual GPIO instantiates from
  the boarddef (pin count, capabilities), so a program that runs in sim
  cannot have referenced a pin the real board lacks. Downstream `driver`
  mocks attach to these virtual buses.

## 7. Relations

- **`driver`** (sibling spec) consumes the bus handles; `over I2c(…)`
  demands an i2c-capable bus, and the driver's wire level lowers through
  the board's handle to the chip's NIFs.
- **`every` / `on`** (parent §6.5): `on rising(pin.gpio9)` takes any pin
  with the `input` capability as an interrupt source; the same literal
  discharge applies.
- **`fleet`** (sibling spec): node blocks declare `on :esp32c3` — the fleet
  compiler instantiates this macro once per node kind, so heterogeneous
  fleets get per-board pin checking with one mechanism.
- **`config`** (parent §6.7) checks pin non-conflict against the board file.
- **Future linearity (grade wave):** claimed pins become linear resources —
  parent §6.9's E118 ("gpio21 was claimed as uart0.tx") is *this* macro's
  data (the claim registry) enforced by the usage-grade axis. Until then, a
  weaker elaboration-time conflict check is ledgered (§8.2).

## 8. Open decisions (ledger)

1. **Community board packages & naming** — `board-xiao-esp32c3`?
   Namespacing when two packages define the same chip on different
   breakouts; whether `board :name` resolves through the package manager or
   a local registry; who curates the "shipped with Cure" set.
2. **Whole-module pin-conflict detection before the grade wave** — a
   claimed-pins registry at elaboration (module-level `let`s + bus defaults
   feed it; double-claim is an immediate domain error) vs. waiting for
   linear pins to do it soundly. Recommendation: ship the registry — it
   catches the beginner case now, and the grade wave subsumes it later
   without surface change (the E118 message is already written).
3. **Board variants / revisions** — DevKitM vs. bare module, rev-dependent
   strapping; also whether users may rewire a bus
   (`bus i2c0 (sda: gpio6, scl: gpio7)` in *user* code) or must define a
   derived boarddef.
4. **Capability taxonomy** — fixed set (v1 position) vs. extensible by board
   packages. Extensible caps that downstream macros can *demand* need a
   shared vocabulary anyway; recommendation: fixed core set + ledgered
   escape hatch, revisit when a real board needs one we lack.
5. **ADC width / attenuation per board** — `adc.read(pin.gpio3) -> Raw12`
   (parent §6.6) implies the boarddef carries ADC resolution; attenuation
   and the C3's flaky ADC2 need a home (per-cap parameters?
   `adc(bits: 12)`).
6. **Strapping-warning UX** — warn once per pin per module vs. per use;
   suppression surface (`unsafe`? an attribute?) for the deliberate case.
7. **How `cure flash` consumes the manifest** — embedded in the `.avm`
   metadata vs. a sidecar file in the build dir; what `cure flash` does when
   the connected chip's ID disagrees with the manifest's `chip` (recommend:
   hard refuse — flashing a C3 image to a classic ESP32 bricks nothing but
   wastes an afternoon).

## 9. Non-goals

- **No AVR targets** — the parent's target-honesty rule (§1); a boarddef
  cannot make AtomVM fit an ATmega328.
- **No runtime pin remapping** — the pin table is compile-time data that
  elaborates away; devices ship only the NIF calls.
- **Not a general pin-mux configurator** for unsupported chips — `boarddef`
  describes what a supported chip's NIF surface can already do; it does not
  program IO_MUX/GPIO-matrix registers itself (that would be a `driver` for
  the mux, and out of v1 scope).
