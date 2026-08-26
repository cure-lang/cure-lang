# `units` — Literal Units of Measure for Embedded Quantities

**Date:** 2026-07-08
**Status:** design (operator-requested). Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
(§6.6); built as a `macro` (§5) — the Tier-3 **literal rules** tier
(`literal $n ms ~> Duration.ms($n)`). The smallest macro in the catalog and
the one every other macro consumes.

---

## 1. Purpose

Make bare numbers illegal where a physical quantity is meant, and make the
unit part of the literal: `sleep(500)` is an error (§4, adapting parent
E115); `sleep(500ms)` is the fix. This kills the embedded bug class —
ms-vs-µs, percent-vs-fraction, raw-ADC-counts-vs-millivolts, baud typos —
**at the literal**, before a value ever flows anywhere.

## 2. Scope decision — additive units only, no dimensional algebra

**Decided.** v1 units support: same-unit addition, subtraction, and
comparison; multiplication by a bare scalar; and **explicit, named
conversions** (`raw.millivolts(vref)`, `d.as_ms()`). There is **no** unit
multiplication or division producing derived dimensions — no `m/s²`, no
`v * a = w`, no dimension-exponent vectors in the type system.

This is deliberate: the bugs this macro exists to prevent are *confusions
between quantities*, and additive units catch every one of them. F#-style
dimensional analysis buys physics simulation, not blink-an-LED correctness,
at a real type-level cost; ledgered with a revisit trigger (§8.1).

## 3. Surface

Literal suffixes for the quantities embedded code actually uses:

```cure
sleep(500ms)                      # time:  10us, 500ms, 2s
pwm.set(fan, 20khz, 80pct)        # frequency: 50hz, 20khz; duty: 0..=100
uart.open(pin.tx, 115200baud)     # baud rate
power.check(3.3v)                 # voltage: 3.3v, 330mv
let raw = adc.read(pin.gpio3)     # -> Raw12 (0..4095)
let mv  = raw.millivolts(3300mv)  # explicit conversion, vref named
```

The v1 unit inventory (each a Tier-3 literal rule):

| Quantity | Suffixes | Target type | Carrier |
|---|---|---|---|
| Time | `us`, `ms`, `s` | `Duration` | Int (µs, §5.3) |
| Frequency | `hz`, `khz` | `Frequency` | Int (Hz) |
| Percent | `pct` | `Percent` | `{n: Int \| 0 <= n and n <= 100}` |
| Baud | `baud` | `Baud` | Int |
| Voltage | `mv`, `v` | `Voltage` | Int (mV; `3.3v ~> 3300`) |
| Temperature | *(no literal)* | `Celsius` | Float |

`Celsius` has no literal suffix in v1 — drivers return it (`Bme280.celsius()
-> Celsius`, driver spec §2) and `flow` thresholds compare against it;
ambient code rarely writes temperature literals. A `c` suffix is trivially
addable if usage demands it.

What works on a unit value, uniformly:

- `a + b`, `a - b`, `a < b`, `a == b` — **same unit only**. `500ms + 3.3v`
  is a compile error (§4).
- `n * d` / `d * n` — scalar times unit yields the unit (`3 * 500ms = 1500ms`).
- Named conversions: `Duration.as_ms/as_us/as_s`, `Voltage.as_mv`,
  `Raw12.millivolts(vref: Voltage)`. Conversions are **explicit, named, and
  lossy-aware**: `as_s()` on `1500ms` is Int division and the docs say so;
  nothing converts implicitly except comparison over a common carrier (§8.6).
- The only escape to a bare number is an `as_*` conversion — and it is
  rarely needed: every DSL sink in the catalog takes the unit type.

## 4. Explainers

Registered per §4 of the parent; the fixed template is *what you wrote → why
forbidden → what to write instead*.

```
error[E115]: sleep expects a duration, got a bare number
  --> main.cure:9
   |
 9 |   sleep(500)
   |         ^^^
  500 of what? Milliseconds and microseconds differ by 1000x — this is the
  classic embedded bug. Write the unit: sleep(500ms), sleep(2s), sleep(10us).
```

```
error[E116]: can't add 500ms to 3.3v — different quantities
  A Duration and a Voltage have no common sum. If you meant a threshold
  comparison, compare each against its own kind of value.

error[E117]: 120pct is not a percentage
  Duty cycle is 0 to 100. If you wanted "20% over", compute it from a
  legal base: duty + duty / 5.
```

E117 fires **at the literal** — `120pct` fails the refinement before the
value exists, not at the `pwm.set` call site.

## 5. Invisible machinery

### 5.1 Zero runtime cost — say it loudly

Each unit is a refinement/phantom-indexed wrapper over a native `Int` (or
`Float` for `Celsius`), riding the **landed Nat→Int erasure**: after
elaboration, a `Duration` **is a plain integer at runtime**. No tag, no
wrapper struct, no arithmetic indirection — `sleep(500ms)` compiles to the
same BEAM code as `sleep(500)` did, minus the bug. This is the embedded
credibility point — the safety is free on a $3 microcontroller — and the
docs must lead with it.

### 5.2 Literal rules

Each suffix is one Tier-3 macro rule: `literal $n ms ~> Duration.ms($n)`,
`literal $n pct ~> Percent.of($n)`, `literal $x v ~> Voltage.mv($x * 1000)`
(the `v` rule scales at elaboration — the Float literal never reaches the
Int carrier unscaled). The constructor's refinement is checked where the
literal elaborates — that is what makes `120pct` fail at the literal.
Same-unit arithmetic is ordinary functions over the wrapper; cross-unit
arithmetic has no applicable function, and E116 translates the no-instance
failure.

### 5.3 The Duration carrier

**One µs-backed Int carrier** for all time; `us`/`ms`/`s` are constructors
scaling into it (`Duration.ms(n) = n * 1000` µs, folded at elaboration for
literals). On 64-bit BEAM ints, 2^60 µs is ~36,000 years — overflow is not a
practical concern — and one carrier means `10us + 500ms` needs no conversion
machinery: same unit, same integer. Honesty note: AtomVM on 32-bit targets
boxes integers past the small-int range, so a large `Duration` may cost a
heap word there; sub-hour durations (the overwhelming embedded case) stay
small-int. If profiling ever shows this matters, the carrier is revisited
via ledger §8.7 — the suffix surface is carrier-agnostic.

### 5.4 `Raw12` and composing range refinements

`adc.read` returns `Raw12`, a `{n: Int | 0 <= n and n < 4096}` wrapper —
12-bit ADC counts are *not* millivolts and must not add to them. The one way
out is `raw.millivolts(vref)`, which takes the reference voltage explicitly
(no hidden 3.3 constant) and documents its Int-division rounding. Other ADC
widths get their own `RawN` the same way (ledgered with §8.2).

Range refinements compose: `80pct` inhabits `{n: Int | 0 <= n and n <= 100}`
— the same refinement language as everything else — so an API taking
`{p: Percent | p <= 50}` rejects `80pct` at the call site with the ordinary
machinery, and `check` generators (§6) respect the narrowing.

## 6. `check` integration

Nothing to build. Refinement-derived generators (parent §7.5) already
respect units: a prop over `{d: Duration | d < 1s}` generates in-range
durations because the refinement *is* the generator spec; `Percent`
generates `0..100`, `Raw12` `0..4095`, and shrinking stays inside the
refinement as always. No unit-specific property templates are needed —
units have no behavior to template, only ranges, and ranges come free.

## 7. Relations

- **`every` / tasks (§6.5)** and `sleep`: all periods and delays are
  `Duration` — E115 is the front door most users meet first.
- **`driver` (§6.2)**: typed outputs (`Celsius`, `Pascal`); a driver `fn`
  returning bare `Float` for a physical reading is a **lint** (driver spec
  §7) — a nudge, not a block, for ports of sloppy datasheets.
- **`board` / adc (§6.1)**: `adc.read` returns `Raw12`; pin machinery
  untouched.
- **`flow` (§6.4)**: time operators take durations — `hold_for(10s)`,
  `debounce 20ms` — so the FRP surface never sees a bare tick count.
- **Beyond the MCU** (parent §7): currency is the same pattern — a `usd`
  literal rule over an Int-cents carrier, additive-only — one line here,
  designed by whoever builds the money macro.

## 8. Open decisions (ledger)

1. **Dimensional algebra** — out of v1 (§2). Revisit trigger: a real macro
   (motor control? power budgeting?) needs a *derived* quantity (`v * a`)
   badly enough that its authors hand-roll unsafe `as_*` round-trips. Then
   evaluate F#-style exponent vectors as a Tier-4 elaboration, not kernel.
2. **User-defined units surface** — probably yes; shape:
   `unit Rpm over Int suffix rpm range 0..=20000` / `unit Pascal over Float`
   — carrier, optional suffix, optional range; additive algebra derived.
   Suffix-claim collisions ride the macro facility's hygiene ledger.
3. **Float-carried units and NaN** — `Celsius` is Float-backed; NaN excluded
   by refinement at construction, or propagated as in plain Float? Leaning:
   exclude — a NaN reading is a driver error, not a temperature.
4. **Formatting/printing** — `show(1500ms)`: `"1500ms"` (faithful) vs
   `"1.5s"` (friendly)? Locale-free either way. Leaning: faithful default,
   a `humanize()` helper for logs.
5. **Overflow/saturation on conversions** — `as_ms()` on a huge Duration,
   `millivolts()` near vref: wrap, saturate, or refine the input? Decide per
   conversion when the stdlib entries are written; document each.
6. **Cross-suffix equality** — `1s == 1000ms`: recommend **yes** — same
   µs-carrier integer, so equality is structural and free. Ledgered because
   it commits us: if §8.7 ever splits the carrier, equality must stay
   quantity-level or programs silently change meaning.
7. **Duration carrier revisit** — the single-µs-Int choice (§5.3), reopened
   only on measured 32-bit AtomVM boxing cost in real programs.

## 9. Non-goals

- **No dimensional analysis in v1** (§2) — no derived dimensions, no
  exponent arithmetic in types.
- **No unit inference** — a bare `500` never becomes a `Duration` by context;
  the whole point is that the unit is written at the literal.
- **No SI completeness** — not a units library for science; the six
  quantities embedded code confuses, plus §8.2 to add your own. Candela
  can wait.
