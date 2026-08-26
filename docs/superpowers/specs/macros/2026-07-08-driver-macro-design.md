# `driver` — Datasheet-Declarative Peripheral Drivers

**Date:** 2026-07-08
**Status:** design (operator-requested). Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
(§6.2); built as a `macro` (§5). Priority #4 in the surfaces spec — **the
ecosystem play**: when contributing a driver is a declarative afternoon, the
package ecosystem writes itself, which is the actual thing that made Arduino
sticky.

---

## 1. Purpose

Declare a peripheral **from its datasheet** — registers, bit-fields, valid
ranges, modes, and the init handshake — and get a fully typed driver:
range-checked writes, mode- and init-gated operations, calibrated typed
readings, a generated *simulated device* for host testing, and error messages
that cite the datasheet. The user of a driver never sees any of this; they
write `Bme280.on(i2c0)` and call methods.

## 2. Surface

Flagship (Bosch BME280, the hobbyist rite of passage):

```cure
driver Bme280 over I2c(0x76 | 0x77)          # address set — checked at attach
  ## Bosch BME280 temperature / pressure / humidity sensor (datasheet v1.23).

  reg chip_id   at 0xD0, read                # Byte by default
  reg reset     at 0xE0, write
  reg ctrl_hum  at 0xF2, read_write
    field osrs_h: bits(2..0)
  reg status    at 0xF3, read
    field measuring: bits(3..3)
  reg ctrl_meas at 0xF4, read_write
    field osrs_t: bits(7..5)
    field osrs_p: bits(4..2)
    field mode:   bits(1..0)
  reg config    at 0xF5, read_write
    field t_sb:   bits(7..5)
    field filter: bits(4..2)
    # bits(1..1) is reserved — undeclared ⇒ unwritable, by construction
  reg raw_data  at 0xF7, read, bytes(8)      # burst read: press+temp+hum
  reg calib0    at 0x88, read, bytes(26)

  mode Sleep, Forced, Normal governed_by ctrl_meas.mode  # typestate axis

  init
    expect read(chip_id) == 0x60 else :wrong_chip_id
    write(reset, 0xB6)
    wait_until read(status).measuring == 0 within 10ms
    let calib = read(calib0) |> Calibration.parse()
    write(ctrl_hum,  %{osrs_h: 1})
    write(ctrl_meas, %{osrs_t: 1, osrs_p: 1, mode: Sleep})

  fn celsius(d: Bme280) ! Bus -> Celsius requires mode in [Forced, Normal] =
    raw_data |> read() |> Readings.parse() |> compensate_t(d.calib)

  fn wake(d: Bme280) ! Bus -> Bme280 in Normal =
    write(ctrl_meas, %{mode: Normal})
```

User side (the whole API most people touch):

```cure
let sensor = Bme280.on(i2c0)          # runs init; Result(Bme280 in Sleep, DriverError)
let awake  = sensor.wake()
let t      = awake.celsius()
```

Surface rules:

- **`reg`** — address, direction, width (`Byte` default, `bytes(n)` for
  bursts, `word(be|le)` ledgered §8.4). Direction is enforced: writing a
  `read` register is a compile error.
- **`field`** — a named bit-window on its register. Windows are checked
  **non-overlapping** at elaboration; **undeclared bits are reserved and
  unwritable by construction** — whole-register writes are expressed as
  field-maps (`%{osrs_t: 1, …}`), and the elaborator proves untouched bits
  are preserved (read-modify-write) or zero-per-datasheet (declared
  `reset_value`, ledgered §8.4). A field's value type is the refinement
  `{v: Int | 0 <= v and v < 2^width}` — narrower declared ranges allowed.
- **`mode … governed_by`** — declares the device's operating modes as a
  typestate axis *bound to a field*, so the type-level mode and the
  register-level mode cannot drift: the only way to change the typestate is
  writing the governing field, and writing it *is* the typestate transition
  (`wake` above returns `Bme280 in Normal` because it wrote `mode: Normal` —
  checked, not asserted).
- **`init`** — the attach protocol. `expect … else :reason` and
  `wait_until … within …` are the two datasheet idioms (identity check,
  status poll with deadline). Runs inside `Type.on(bus)`; any failure yields
  `Error(DriverError)` with the step named.
- **`fn`** — ordinary Cure with three driver-specific affordances:
  `requires mode in […]` (a precondition on the typestate index), `in Mode`
  on the return type (a transition), and register names as readable/writable
  values. Effects: driver fns carry `! Bus` (the effect-discipline spec's
  capability manifest).

## 3. Typestate — one GADT, two axes

The device handle is indexed by **attachment** (unattached type-level-only →
attached) and **mode** (the `governed_by` axis):

- `Bme280.on(i2c0)` is the only constructor of an attached handle — so
  "`read` before init" is not an error case, it is **unrepresentable**
  (hiding principle 2).
- `requires mode in [Forced, Normal]` compiles to the mode index; calling
  `celsius()` on a `Bme280 in Sleep` is a compile error:

```
error[E110]: BME280 is asleep here — celsius() needs Forced or Normal mode
  --> greenhouse.cure:14
  The handle has mode Sleep (set by init, driver line 31).
  Call sensor.wake() first (datasheet §3.3: measurements only run
  outside sleep mode).
```

This is the landed GADT-ctor machinery; per the singleton/erasure story the
mode index costs zero bytes — the runtime handle is `{bus, address, calib}`.

## 4. The generated simulator — the sleeper feature

The declaration is complete enough to **synthesize a mock device**: registers
become state, fields enforce their windows, the init protocol must be
followed, `governed_by` transitions animate mode, and declared reset values
populate power-on state. `cure run --sim` wires the mock onto the virtual
bus automatically:

- Driver *authors* test against the mock before touching hardware; `check`
  templates (§6) run against it for free.
- Driver *users* run whole programs (`Greenhouse` end-to-end) on a laptop
  with plausible sensor behavior (mock readings scriptable:
  `sim.bme280.set(celsius: 31.0)`).
- The mock is derived, never hand-written — it cannot drift from the
  declaration. (Behavioral quirks beyond the regmap — conversion timing,
  measurement noise — are optional `sim` blocks, ledgered §8.6.)

## 5. Wire level

Register access lowers to the board's bus handles (board spec §6.1) and
thence to `@extern` NIF calls (AtomVM `i2c`/`spi_`/`uart` drivers, or Linux
`/dev` on generic-unix). Multi-byte registers ride the `packet` machinery for
layout/endianness. The macro emits burst reads where the declaration shows
contiguous `bytes(n)` (raw_data above is one transaction, not eight).

## 6. `check` integration (shipped templates)

- **Reserved-bit safety** — mostly static (unwritable by construction); the
  template exercises the read-modify-write codegen against the mock: after
  any generated write, undeclared bits are unchanged.
- **Init conformance** — generated attach runs against the mock: every
  `expect`/`wait_until` path reachable; wrong-chip and timeout paths return
  the declared errors.
- **Mode discipline** — random legal call sequences against the mock never
  observe a governed field disagreeing with the typestate index.
- Field range round-trips come free from the refinement generators.

## 7. Relations

- **`board`** (§6.1) supplies typed bus handles and pin capabilities;
  `over I2c(…)` demands an I2C-capable bus.
- **`units`** (§6.6) types the outputs (`Celsius`, `Pascal`) — a driver
  returning bare `Float` is a lint.
- **`packet`** (§6.3) does multi-byte layout; **`protocol`** shares the
  "at this step…" explainer vocabulary (an init block is morally a
  single-role session against silicon; no machinery unified — the silicon
  can't run our endpoint).
- **`fleet`**: a node block instantiates drivers; nothing special.

## 8. Open decisions (ledger)

1. **Calibration/compensation placement** — BME280-class devices need
   nontrivial arithmetic (`compensate_t`); plain `fn`s (as specced) vs. a
   declarative `calib` sub-language. Start with `fn`s; revisit if drivers
   repeat structure.
2. **Multi-instance & address sets** — `I2c(0x76 | 0x77)`: attach-time probe
   order, and two instances of one driver on one bus (should just work —
   handles are values — confirm no global state sneaks in).
3. **Interrupt lines** — `on drdy_pin rising -> …` inside a driver (data-ready
   patterns); composes with `on` tasks (§6.5) but needs pin *ownership*
   threading from the user's board block into the driver. Defer to the grade
   wave's linear pins?
4. **Register width/endianness surface** — `word(be)`, 24-bit quantities,
   register pairs; and declared `reset_value` per register (needed for the
   whole-register-write proof and the mock's power-on state).
5. **Timing-critical protocols** — WS2812/DHT22-class bit-banged timing does
   NOT fit this macro (µs-level waveforms need the future cost/WCET grade
   axis or dedicated NIFs). Honest scope note in docs; NIF-backed escape
   hatch (`@extern`) is the interim answer.
6. **`sim` behavior blocks** (§4) — optional scripted dynamics for mocks
   (conversion delay, drift); surface TBD.
7. **Registry conventions** — package naming (`driver-bme280`?), datasheet
   version pinning in the header, and a `cure driver report` (rendered
   regmap doc, per the fleet/protocol report philosophy).

## 9. Non-goals

- Not a general HAL: no USB, no timing-critical bit-bang (§8.5), no DMA
  orchestration in v1.
- Not auto-ingesting vendor SVD/datasheet PDFs (attractive later; the
  declaration format is chosen to make that mechanical when attempted).
- No runtime reflection on regmaps — the declaration elaborates away;
  devices ship only the access code.
