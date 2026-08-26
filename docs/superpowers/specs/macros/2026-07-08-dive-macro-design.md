# `dive` — Recreational Dive Planning Where the Refinement Is the Physiology

**Date:** 2026-07-08
**Status:** design. Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
(idea backlog #35, promoted); built as a `macro` (§5). Consumes
[`units`](2026-07-08-units-macro-design.md) heavily.

---

## 1. Purpose

Plan a recreational scuba dive — ordered depth/time segments on declared
breathing gases, surface intervals between repetitive dives — and have the
compiler check every plan against the physiology **before you get wet**: no
segment exceeds its no-decompression limit, ascents never break the maximum
rate, no gas is breathed past its maximum operating depth, safety stops are
covered, and the gas plan holds a reserve against computed consumption.

This is the sharpest marketing story refinement types will ever get.
Everywhere else in this catalog, "the type error prevents a crash" means a
*software* crash — a leaked secret, a buffer overrun, a wedged event loop.
Here the refinement **is the physiology**. A no-deco limit, an ascent-rate
ceiling, a gas MOD — these are not analogies for correctness; they are the
actual constraints that keep a diver's tissues, lungs, and central nervous
system inside survivable bounds. The type checker rejects a plan for the same
reason a good instructor would.

And the domain is technically perfect for the thesis (parent §1). The indices
are concrete literals: `30m`, `25min`, `EAN32`. Every obligation is closed
arithmetic over those literals — table lookups, a rate division, a partial-
pressure multiply. Everything discharges by pure computation (whnf + delta
globals); **no solver, no proof term, no hole ever reaches the user.** This is
the purest case of "indices-are-literals ⇒ everything discharges by
computation" in the whole catalog.

## 2. Surface

A `dive` block is an ordered plan: gas declarations, then segments, with
optional surface intervals separating repetitive dives.

```cure
use Std.Dive.Padi          # which agency's tables ship (§8)

dive Reef
  gas air    = O2 21pct, N2 79pct
  gas nitrox = O2 32pct, N2 68pct     # EAN32

  descend to 18m on nitrox
  segment 18m for 40min  on nitrox
  ascend  to  5m
  stop    at  5m for  3min            # safety stop
  ascend  to surface

  surface_interval 1h 30min           # repetitive dive follows

  descend to 14m on nitrox
  segment 14m for 35min  on nitrox
  ascend  to  5m
  stop    at  5m for  3min
  ascend  to surface

  sac 20L/min                         # surface air consumption (personal)
  tank air:    12L at 200bar
  tank nitrox: 12L at 200bar
```

Surface rules:

- **`gas`** — a named breathing mix declared by fractions that must sum to
  100% (checked at elaboration). `air` and common nitrox mixes are library
  constants; declaring your own is one line.
- **`segment D for T on G`** — the bottom phase: hold depth `D` for duration
  `T` breathing gas `G`. `descend`/`ascend`/`stop` are the connecting phases;
  each carries an implied rate the checker sees.
- **`surface_interval T`** — time on the surface off-gassing before the next
  dive. Everything after it is a *repetitive* dive that inherits residual
  nitrogen (§4).
- **`sac`** — surface air consumption rate in `L/min`, a personal figure.
- **`tank`** — a cylinder: volume and fill pressure, per gas.

Units (`m`, `min`, `h`, `bar`, `L`, `L/min`, `pct`) come from the `units`
macro throughout. Imperial is supported strictly as **named unit
conversions** — `60ft`, `psi`, `cuft` are literal rules over the same metric
carriers (feet→metres, psi→bar). There is never an ambient-unit ambiguity:
depth is a `Depth`, pressure a `Pressure`, and `60ft` and `18m` are the same
value in the same carrier (§7 units relation).

## 3. The refinement-is-the-physiology story

Each check is a refinement whose bound is a physiological fact, discharged by
computation over the plan's literals. No approximations, no runtime, no solver.

- **No-decompression limit (NDL).** Each `segment` at depth `D` carries a
  refinement `{t: Duration | t <= ndl(D, gas, residual)}`. In v1 `ndl` is a
  **declared constant table** — the published recreational limits of the
  chosen agency (§8), shipped as delta-reducible global data, *not* a live
  decompression algorithm. The obligation `25min <= ndl(30m, air, 0)` reduces
  to comparing two literals. Proved by lookup.
- **Ascent rate.** Between two depths at two times, rate `= (D₁ − D₂) / Δt`,
  refined `{r: Rate | r <= 9m/min}`. Pure division over literals. The
  standard recreational ceiling of 9 m/min is the default (`config` may
  tighten it — §7).
- **Maximum operating depth (MOD).** For a gas with O₂ fraction `f`, the
  ambient partial pressure of oxygen at depth `D` is
  `ppO2 = f × (1 + D/10)` bar (10 m of seawater ≈ 1 bar). The refinement is
  `{ppO2: Pressure | ppO2 <= 1.4bar}`. Every `segment … on G` discharges
  `f × (1 + D/10) <= 1.4` — one multiply, one compare, all literal.
- **Safety-stop coverage.** Any dive to `> 10m` or near its NDL must include a
  3–5 min stop in the 3–6 m band before surfacing. Expressed as a
  correct-by-construction requirement over the phase list: a `dive` that
  ascends from the bottom straight to the surface without a covering `stop`
  fails to elaborate (hiding principle 2 — the omission is a *shape* error,
  not a proof obligation).
- **Gas planning.** Consumption for a segment is
  `sac × (1 + D/10) × T` litres (SAC scaled by ambient pressure). Summed over
  the dive and converted to bar via tank volume, the plan must leave a
  declared reserve — **rule of thirds** (⅓ out, ⅓ back, ⅓ reserve) or an
  explicit reserve fraction — as a refinement
  `{used: Pressure | used <= capacity − reserve}`. Again: arithmetic over the
  declared `sac`, `tank`, and segment literals.

Every one of these is a `{x | x ⊑ bound}` refinement whose bound is a number
the physiology fixes and whose subject is a number the plan states. The kernel
never does anything cleverer than reduce and compare.

## 4. Repetitive dives — residual nitrogen threads through

Recreational tables model repetitive diving with **pressure/residual-nitrogen
groups**: a dive leaves you in a letter group; a surface interval moves you to
a cleaner group by a table lookup; the next dive's NDL is reduced by the
residual you carried in.

The macro threads this purely. Each dive segment produces a residual-nitrogen
group (a table lookup keyed by depth and time). `surface_interval T` applies
the surface-interval credit table to that group, producing the entry group for
the next dive. That group feeds the `residual` argument of the next segment's
`ndl(D, gas, residual)` refinement — so a repetitive dive's NDL is
*automatically* the reduced one. It is still nothing but table lookups over
literals: the group is data, the interval credit is data, the adjusted NDL is
data. No algorithm, no state, no runtime — the whole repetitive chain
discharges at compile time.

If a surface interval is too short to clear enough nitrogen for the planned
second dive, the second segment's NDL refinement simply fails, and the
explainer (§5) says so in group terms.

## 5. Explainers

Registered per parent §4; template is *what you planned → why the physiology
forbids it → what to change*. Diver vocabulary, no type-theory, ever.

```
error[E210]: segment 2 exceeds the no-decompression limit at 30m
  --> reef.cure:9
  25min planned, but the table allows 20min at 30m on air.
  Shorten this segment to 20min, or split it into two dives with a
  surface interval between them.
```

```
error[E211]: EAN36 below 29m exceeds a ppO2 of 1.4 bar
  --> reef.cure:5
  At 30m on 36% oxygen the partial pressure is 1.44 bar.
  1.4 is the recreational ceiling — that is how divers convulse underwater.
  Use a leaner mix (air reaches 56m) or keep this gas above 29m.
```

```
error[E212]: ascent from 30m to 5m in 90s is 16.7 m/min
  --> reef.cure:11
  The maximum ascent rate is 9 m/min. Take at least 167s for this ascent,
  or add intermediate stops.
```

```
error[E213]: this dive surfaces without a safety stop
  --> reef.cure:12
  You planned a bottom segment at 18m then a direct ascent to the surface.
  Add:  stop at 5m for 3min   before surfacing.
```

```
error[E214]: the second dive exceeds its no-deco limit for your surface interval
  --> reef.cure:18
  Dive 1 left you in pressure group G. 1h30min on the surface clears you to
  group D, which allows 30min at 14m — you planned 35min.
  Extend the surface interval, or shorten the second dive to 30min.
```

```
error[E215]: gas plan fails the rule of thirds
  --> reef.cure:22
  Planned consumption is 148 bar of a 200 bar fill; the rule of thirds
  reserves 67 bar (leaving 133 usable). Shorten the dive, carry a larger
  tank, or lower your SAC assumption only if you have logged data for it.
```

## 6. `check`

Mostly **static discharge** (parent §7.5). A plan that violates no limit is
*proved-by-construction* — `check` reports the physiological props as theorems
of the declarations, run zero times:

```
$ cure test
check Reef
  ✓ ndl_respected        proved by construction — every segment ≤ table NDL; 0 runs
  ✓ ppo2_within_limit    proved by construction — max ppO2 1.28 bar; 0 runs
  ✓ ascent_rate_ok       proved by construction — max ascent 8.0 m/min; 0 runs
  ✓ safety_stop_covered  proved by construction — 5m/3min stop present; 0 runs
  ✓ gas_reserve_held     proved by construction — 148 bar used ≤ 133 usable; 0 runs
```

Macro-shipped property templates exercise the *table edges* on
generated plans: `prop`s generate depth/time/gas combinations that sit exactly
on published NDL and MOD boundaries and assert the verdict flips at the right
literal (this is how a mistranscribed table constant gets caught). And a
round-trip property asserts **imperial↔metric never changes a verdict** — a
plan written in `ft`/`psi` and its `m`/`bar` transliteration must produce
identical proved/rejected outcomes, since they share a carrier. That property
is the guardrail on the whole conversion story.

## 7. Relations

- **`units`** (heavy). `m`, `min`, `h`, `bar`, `L`, `L/min`, `pct` are all
  `units` literals; imperial suffixes (`ft`, `psi`, `cuft`) are additional
  literal rules over the same carriers. `percent`-O₂ gas fractions ride the
  `Percent` refinement (`0..100`, and per-gas fractions sum-check to 100).
  A dive plan is essentially a `units`-typed data structure with physiological
  refinements bolted on.
- **`config`** — personal-conservatism settings, with a **monotone-safety
  rule** stated as law: config may only *tighten* a refinement, never loosen
  it. A diver may set `ascent_max: 6m/min` (stricter than the 9 default),
  `ppo2_max: 1.2bar`, `reserve: half` (stricter than thirds), or a
  conservatism factor that shrinks NDLs. The macro statically rejects any
  config that would relax a bound past the agency default. Conservatism is a
  one-way ratchet toward safety.
- **`check`** — as §6: static discharge plus table-edge templates plus the
  imperial round-trip property.
- **Report generation** — a `dive report` renders a printable **dive plan**
  (a slate-style depth/time/gas profile, group letters, run times) and a
  **gas plan** (per-tank consumption, turn pressure, reserve). Same
  report philosophy as `driver`/`fleet`. This is the artifact a diver
  actually carries — and it is generated from the same declaration the
  checker proved safe, so the slate cannot disagree with the plan.

## 8. Safety honesty

This section is load-bearing and unhedged.

**`dive` is a planning and teaching aid. It is not a dive computer, not a dive
buddy, and not a substitute for training.** It does not replace a certification
course, a briefing, a buddy check, or the dive computer on your wrist. It plans
a dive on paper; the ocean does not read your plan.

**v1 is planning-only.** It computes a plan before the dive and prints a slate.
It has no concept of what is actually happening underwater — your real depth,
your real time, your real breathing, your real ascent. Nothing in this macro
runs during a dive.

**Do not build a real-time dive computer with this — explicitly.** Because
Cure targets AtomVM on ESP32, someone will want to put this on a wrist device
and drive a live NDL countdown. **Don't.** A real-time dive computer is
life-support firmware: it must track tissue loading continuously, tolerate
sensor failure, degrade safely, and carry certification and liability that no
hobby project has. The moment a display tells a diver "you have 4 minutes of
no-deco time left," a bug in that number can kill them. That is categorically
beyond hobby scope and beyond this macro's design. This is ledgered as a
hard warning (§9), and the docs must carry it on page one.

**The tables are conservative by design, and their constants are not yours to
tune.** Recreational tables build in a safety margin over the underlying
model. The physiological constants — the NDLs, the ppO₂ ceiling, the ascent
rate, the surface-interval credits — are shipped as fixed agency data. A user
**cannot** edit them from ordinary surface syntax; `config` may only tighten
(§7). The single escape hatch is the language-wide `unsafe` marker (parent §3
principle 4): loosening a physiological constant requires `unsafe`, is
greppable, and shouts in every explainer and report that this plan left the
agency's numbers. There is no quiet way to make a plan look safe by editing the
biology.

## 9. Open decisions (ledger)

1. **Algorithm upgrade path.** v1 is table-based (published recreational limits
   as constants). A **later, heavily-caveated** addition could compute NDLs
   from a real model — **Bühlmann ZH-L16 with gradient factors** is the
   obvious candidate. This is a large step up in responsibility: it moves the
   macro from "reprints a published table" to "computes decompression," which
   is exactly the boundary the safety section polices. Decision deferred; if
   taken, it ships behind explicit opt-in, still planning-only, with its own
   safety review. Staying table-based indefinitely is a legitimate outcome.
2. **Which agency's tables ship.** Constants are data, and agencies differ
   (PADI RDP, NAUI, BSAC, SSI, DSAT). Design intent: **pluggable table
   packages** (`use Std.Dive.Padi` / `.Bsac` / …), each a delta-reducible
   constant set, so a plan names its authority explicitly and the report cites
   it. No default agency is blessed in v1; the user must choose one, on the
   principle that a diver should know which tables they are planning against.
3. **Altitude diving.** NDLs and ascent rates change at altitude (reduced
   surface pressure). Out of v1; a later altitude-correction layer would be
   another pluggable constant transform over the base tables, gated by an
   explicit `altitude` declaration. Ledgered, not built.
4. **Multi-gas / decompression diving.** Gas switches, deco stops, staged
   ascents, CCR — beyond recreational limits and **probably a permanent
   non-goal.** Planning technical dives is a different discipline with a
   different liability profile; if it is ever attempted it is a separate
   macro with its own safety spec, not an extension of this one.
5. **Device crossover warning.** See §8: real-time on-device dive computing is
   explicitly discouraged and ledgered here as a hard, permanent warning, not
   a future feature.
6. **Salt vs. fresh water.** The `1 + D/10` ambient-pressure approximation is
   seawater; fresh water is ~1/10.3. v1 uses the seawater constant (matching
   the tables); a fresh-water constant is a trivial pluggable follow-up if a
   lake-diving user asks.

## 10. Non-goals

- **No real-time decompression computation on a device.** Not a dive computer;
  see §8. This is the firmest non-goal in the spec.
- **No technical or decompression diving.** Recreational, no-deco, single- and
  repetitive-dive planning only (§9.4).
- **Not a replacement for certification, training, a briefing, a buddy, or a
  dive computer.** A planning aid, full stop.
- **No medical or fitness-to-dive advice.** The macro knows depths, times,
  and gases — not the diver. It cannot and does not assess anyone's health,
  and says so.
