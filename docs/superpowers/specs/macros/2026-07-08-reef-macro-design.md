# `reef` — Voted Multi-Sensor Aquarium Control (Shuttle-Grade Redundancy)

**Date:** 2026-07-08
**Status:** design (operator-requested flagship; backlog #99 promoted).
Child of [`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md);
built as a `macro` (§5). Heaviest consumer of
[`fleet`](2026-07-08-fleet-macro-design.md),
[`driver`](2026-07-08-driver-macro-design.md),
[`units`](2026-07-08-units-macro-design.md), and
[`check`](2026-07-08-check-macro-design.md).

**Operator direction (verbatim intent):** NASA-level multi-sensor redundancy —
whether the sensors live on one ESP or several — the way the Shuttle used
multiple computers voting to decide things in case of fault. Especially for
optical water level and salinity.

---

## 1. Prior art — and the gap this fills

- **Reef-Pi** (open-source Raspberry Pi controller): the module taxonomy this
  macro inherits — equipment, ATO, temperature, pH, dosing, lighting,
  timers, macros. Single sensor per function; no redundancy concept.
  (reef-pi.github.io, github.com/reef-pi/reef-pi)
- **Neptune Apex ATK** (the commercial reference for top-off): a four-layer
  **hierarchical fallback ladder** — primary optical sensor → backup optical
  sensor above it → "IQ-Fill" learned-volume timeout (won't add more than
  double the learned amount, then alarms) → a **mechanical float valve** as
  the final, electronics-independent backstop. Layers, not voting: each layer
  acts only when the one below has already failed.
- **Hydros Collective** (CoralVue): every controller is a "brain"; if one
  fails, others take over its tasks automatically; power-supply fault
  domains are managed by data-only cables between units. **Controller-level
  failover** — no sensor-level voting, and no analysis of whether the
  redundancy actually covers a fault.
- **Space Shuttle DPS** (the operator's reference model): four GPCs in a
  redundant set voting on outputs; a fifth running **dissimilar** software
  (the BFS) against common-mode bugs; *analytic redundancy* (model-derived
  estimates checking physical sensors); the **fail-operational / fail-safe**
  criterion — first failure: keep flying; second: get safe.

The gap, precisely: the industry has fallback *ladders* and controller
*failover*, but *no one* has (a) declared sensor **quorums with voting
semantics**, (b) **dissimilarity** as a first-class, checked property, or
(c) **compile-time common-mode analysis** — proof that no single fault
domain (node, bus, power rail, mounting point) can defeat a quorum. All
three are exactly what a type-checked fleet language can do statically.
That is this macro.

## 2. The hazard model (why voting, and why the operator's two callouts)

Reef tanks die from control failures, not chemistry surprises:

- **ATO runaway** — a fouled level sensor (the canonical failure: a snail or
  algae film on the optical prism) drives fresh water in until **salinity
  crashes** — or the floor floods. The operator's callout #1.
- **Salinity misreading** — conductivity probes drift and foul; a single
  trusted probe silently mis-reports while ATO/AWC "corrects" toward
  disaster. Callout #2.
- **Heater runaway** — the most common total-loss event in the hobby: a
  welded relay cooks the tank. Stuck-off chills it (slower, survivable).
- **Dosing runaway** — an alkalinity pump that doesn't stop.

All four share the shape: **one lying sensor or one stuck actuator, trusted
absolutely.** The fix is never a better sensor; it is arranging that no
single device is ever believed alone — and *proving* the arrangement has no
single point of belief.

## 3. The redundancy model — Shuttle practice, typed

| Shuttle | `reef` |
|---|---|
| Redundant set of GPCs voting | **Sensor quorums** — k-of-n voting per measured quantity |
| Dissimilar BFS (different software) | **Dissimilar channels** — mixed sensor kinds + analytic channels; dissimilarity is tracked in types and requirable |
| Analytic redundancy | **`derived` channels** — model-based estimates that vote alongside physical sensors (Apex's IQ-Fill, generalized) |
| Force-fight / hardware voting at actuators | **Actuator interlocks** — max-runtime and limit sensors enforced *below* the control loop |
| Fail-operational → fail-safe | **Degradation ladder** — declared per loop, coverage-checked |
| A mechanical backup no computer can override | **Kept.** The float valve stays. Software voting never replaces the hardware backstop; the macro *documents* it in the plan report. |

## 4. Surface

A complete two-node build (sump controller + display-side node + host
dashboard):

```cure
reef Display90
  fleet
    node sump on :esp32c3
      let opt_a  = OpticalLevel.on(pin.gpio4)     # driver macro
      let flt_a  = FloatSwitch.on(pin.gpio5)
      let cond_1 = Conductivity.on(i2c0(0x64))
      let tmp_1  = Ds18b20.on(pin.gpio6)
      let ato    = gpio.out(pin.gpio12)
      let heat   = gpio.out(pin.gpio13)
    node rim on :esp32c3                          # display-side node
      let opt_b  = OpticalLevel.on(pin.gpio4)
      let cond_2 = Conductivity.on(i2c0(0x64))
      let tmp_2  = Ds18b20.on(pin.gpio6)
    node host on :unix                            # dashboard + alerts

  quantity sump_level: Level
    channel a = sump.opt_a   kind :optical, mount :sump_bracket
    channel b = rim.opt_b    kind :optical, mount :rim_bracket
    channel c = sump.flt_a   kind :float,   mount :sump_bracket
    vote 2 of 3
    require dissimilar kinds >= 2                 # optical alone can't decide
    stale after 10s                               # a silent channel abstains

  quantity salinity: Salinity                     # ppt, temp-compensated
    channel p1 = sump.cond_1 with temp(tank_temp), calibrated within 30d
    channel p2 = rim.cond_2  with temp(tank_temp), calibrated within 30d
    channel vol = derived TopOffAccounting(ato, tank_volume: 340l)
    vote 2 of 3, agree within 0.5ppt over 10min

  quantity tank_temp: Celsius
    channel t1 = sump.tmp_1
    channel t2 = rim.tmp_2
    vote 2 of 2, agree within 0.4c                # 2oo2: disagreement = degrade

  actuator ato
    fail_safe :off
    interlock max_on 90s per 30min                # enforced below the loop
  actuator heat
    fail_safe :off
    interlock cutoff when tank_temp.any_channel > 28.5c   # any single voter trips it

  control TopOff
    when sump_level == Low and salinity in 33ppt..36ppt -> ato.on
    else -> ato.off
    on degraded(sump_level) -> ato.off; alert(:level_quorum_degraded)
    on lost(sump_level)     -> ato.off; alert(:level_quorum_lost)
    on lost(salinity)       -> ato.off; alert(:salinity_unknown)

  control Heat
    hold tank_temp at 25.5c band 0.3c -> heat
    on degraded(tank_temp) -> heat.off; alert(:temp_sensors_disagree)
    on lost(tank_temp)     -> heat.off; alert(:temp_unknown)

  mode feed for 10min  -> [return_pump.off, skimmer.off]   # auto-reverting
  mode water_change    -> [ato.off, heat.off, return_pump.off]
```

Surface rules:

- **`quantity`** declares one physical measurement with N **channels**.
  Channels carry `kind`, `mount`, node (implicit from the binding), optional
  calibration window, optional temperature compensation. The quorum
  (`vote k of n`), agreement band, and staleness window are per-quantity.
- **Control loops read only voted quantities** — there is no syntax for
  reading a single channel inside a `control` block (correct-by-construction:
  trusting one sensor is *inexpressible*). Interlocks (§7) are the one place
  a single channel acts, and only in the safe direction.
- **`on degraded(..)` / `on lost(..)` clauses are coverage-checked** — a
  control loop touching a quantity must say what happens when its quorum
  degrades or dies, exactly as `fleet` forces `NodeLost` handling. You
  cannot write a reef controller that hasn't decided what to do when its
  sensors disagree.

## 5. Voting semantics

- **Boolean quantities** (level reached): k-of-n majority over fresh,
  eligible channels.
- **Analog quantities** (salinity, temperature): the vote is the **median**
  of eligible channels; a channel deviating from the median beyond the
  declared `agree within` band for longer than the declared window is marked
  **suspect** and removed from eligibility (it keeps reporting; it stops
  counting). Suspicion is sticky until the channel re-agrees for the same
  window, or is manually cleared.
- **Abstention** — a channel does not vote if it is: **stale** (no sample
  within its window — on cross-node channels this is fleet's
  heartbeat/staleness machinery doing double duty), **uncalibrated/expired**
  (§8), or **out of physical range** (self-test bounds from the driver's
  declared measurement range — a conductivity probe reading 0.0 mS/cm is
  broken, not reporting fresh water).
- **Quorum states**, in the fail-op/fail-safe ladder: `Full` (all eligible)
  → `Degraded` (≥ k eligible but < n — still operational, alarmed) →
  `Lost` (< k eligible — the quantity has **no value**; reads of it don't
  produce a number, they produce the `lost` branch). A `Lost` quantity is
  not "last known value" — stale confidence is how tanks die; the type
  system simply withdraws the number.
- **Dependency propagation**: salinity channels compensated by `tank_temp`
  inherit its degradation — if the temperature quorum is `Lost`, the
  conductivity channels' compensation is unknown, so they abstain, and
  salinity follows to `Lost`. Declared compensation edges make this
  propagation automatic and visible in the report (§10).

## 6. Common-mode analysis — the crown jewel

Every channel has a computed **fault-domain vector** from declarations the
system already has: `{node, bus, power_rail, mount, kind, excitation}`
(`excitation`: contacting conductivity cells inject AC into the water —
un-isolated cells in one body of water cross-talk, so shared
excitation/ground is itself a common-mode domain; see Appendix A) — node from the
fleet block, bus from the board wiring, power rail from the boarddef, mount
and kind declared on the channel. At compile time, for every quorum:

> For each single fault domain D, remove all channels sharing D. If the
> survivors cannot still reach k votes, that domain defeats the quorum —
> **error or warning, naming the domain.**

```
warning[reef]: sump_level survives any single fault EXCEPT mount :sump_bracket
  channels a (optical) and c (float) share mount :sump_bracket —
  one fouling event (the snail) removes both, leaving 1 of 3 < quorum 2.
  Move the float to the rim bracket, or add a fourth channel.

error[reef]: salinity quorum is defeated by node :sump
  channels p1 and vol both live on sump — a sump-node failure leaves only
  p2, below quorum 2. Move the derived channel's evaluation to host
  (`derived ... at host`) or add a channel on another node.
```

`require dissimilar kinds >= 2` is the same analysis over the `kind` axis —
the typed answer to common-mode *sensor* failure (every optical sensor fails
the same way to the same algae film; the Shuttle's BFS argument). The
analysis is pure arithmetic over declared topology — static, solver-free,
and printed in full by `cure reef report` (§10). **This is the feature no
commercial controller has**: not redundancy, but *proof about the
redundancy*.

Single-ESP builds are first-class — quorums within one node are still worth
having (sensor faults dwarf node faults) — but the analysis will say plainly
that `node` is a defeating domain, so the honest ceiling of a one-ESP build
is visible, not implied.

## 7. Actuator interlocks — defense in depth below the vote

Interlocks are enforced at the actuator driver layer, **beneath** the
control loops, so no logic bug — not even a wrong vote — can override them:

- **`max_on N per W`** (the ATO case): duty-cycle refinement; exceeding it
  latches the actuator to `fail_safe` and alarms. This is Apex's learned-
  volume timeout, made declarative and checked against the plan (the
  compiler warns if the control loop's own duty expectation exceeds the
  interlock — a plan that can't work is a compile error, not a 3am alarm).
- **`cutoff when <single-channel predicate>`** (the heater case): interlocks
  may read single channels — in the **safe direction only** (a false trip
  costs comfort; a missed trip costs the tank). Any single temperature
  voter above the cutoff kills the heater regardless of the quorum's
  opinion. Asymmetric trust, declared.
- **Latching + manual reset**: a tripped interlock does not auto-resume;
  reset is an explicit operator action (Apex's AUTO/OFF slider convention).
- **The mechanical layer is documented, not replaced**: the plan report
  (§10) carries a `hardware backstops` section the user fills (float valve
  on the ATO line, bimetal cutout on the heater) and nags — politely — when
  the ATO plan has none. Software that believes software is the failure
  mode; the spec is explicit that the last layer must not run Cure.

## 8. Calibration typestate

A conductivity/pH probe channel is **ineligible until calibrated** and
becomes ineligible again when its declared window (`calibrated within 30d`)
lapses — expiry demotes the channel to *advisory* (plotted, never voting).
Calibration is a guided flow (two-point, temperature-noted) whose record —
solutions used, date, slope — persists via `schema`; slope degradation
across calibrations is surfaced as probe-aging advice. The typestate makes
the classic failure — trusting a probe calibrated eleven months ago —
inexpressible inside a control loop.

## 9. Dosing safety (brief — same principles, smaller stakes)

Dosing pumps get the same actuator treatment: `max_ml per day` refinements
per supplement, minimum spacing between interacting supplements
(`alkalinity` and `calcium` ≥ 30min apart — a scheduling constraint checked
statically against declared dose schedules), reservoir-volume accounting
(a doser whose reservoir math says empty abstains and alarms rather than
running dry — the analytic-channel trick again).

## 10. Tooling — the report and the drill

- **`cure reef report`** — the whole safety case, printed: every quantity's
  channels/kinds/mounts/nodes, quorum rules, the **full common-mode
  matrix** (fault domain × quorum → survives/defeated), interlock table,
  declared hardware backstops, alert routing. This is the document you'd
  show another reefer — or an insurance adjuster.
- **Fault drills in sim** — `cure run --sim` + `check` templates: stick any
  channel high/low/frozen, foul any mount group, kill any node or bus,
  freeze the clock — then assert the **single-fault criterion**:

  ```cure
  check Display90
    prop single_fault_safe(f: SingleFault) =
      sim(Display90) |> inject(f) |> run(48h)
      |> always(fn(t) ->
           t.salinity_true in 30ppt..38ppt and t.heater_duty <= safe_duty)
  ```

  `SingleFault` generates from the declared topology (every channel × every
  failure mode × every fault domain), so the drill sweep is derived, not
  hand-listed. Where the common-mode analysis already proves a fault
  can't defeat a quorum, the prop reports **proved by construction**; the
  dynamic runs cover the control-loop dynamics the static analysis can't.
  This is the Shuttle's fail-op criterion as a `cure test` line.

## 11. What the dependent types do invisibly

- Reading a single channel in a control loop: no syntax for it (§4).
- A `Lost` quantity has no value to read — the degraded/lost branches are
  the only access path (coverage-checked).
- Units: SG/ppt/mS-cm (temp-compensated conversions explicit), dKH, °C, ml,
  litres — mixing salinity units without conversion is a type error.
- Calibration/staleness eligibility are typestate on the channel.
- The common-mode matrix is pure compile-time arithmetic over Fin-indexed
  fleet topology; erasure ships none of it to the ESP32.
- Interlock duty refinements are checked against declared schedules.

## 12. Explainers

Codes deferred to the error-explainer registry (new block; see ledger).
Representative, in reefer vocabulary:

```
error[reef]: TopOff doesn't say what happens when sump_level's sensors disagree
  Add: on degraded(sump_level) -> ato.off (recommended: top-off can wait;
  wrong top-off cannot be undone).

warning[reef]: ato interlock allows 90s/30min but the TopOff loop under
  worst-case evaporation (declared 2.5l/day) needs at most 41s/30min —
  consider tightening max_on toward the need; slack is runaway allowance.
```

## 13. Relations

- **`fleet`** — nodes, channels-as-edges, staleness/NodeLost machinery,
  hub-illusion control loops (a control loop is hub logic; the vote lands at
  the actuator's node per fleet's ownership rule 4).
- **`driver`** — every sensor/probe is a declared driver with measurement
  ranges (feeding §5's self-test abstention) and generated mocks (feeding
  §10's drills). Conductivity, DS18B20, optical/float, peristaltic, pH.
- **`units`, `config`** (personal bands tighten only — dive's monotone-safety
  rule), **`schema`** (calibration + emission logs), **`view`** (host
  dashboard), **`check`** (drills), **`workflow`** (maintenance schedules —
  water changes, media swaps — with `after 14d` timers).
- **`home`/`grow`** (backlog) — the quantity/quorum/interlock core specced
  here is domain-neutral; if a second domain adopts it, extract a shared
  `quorum` sub-macro (ledgered).

## 14. Safety honesty

This is livestock and property, not human life: the framing is honest
engineering, not certification. The macro's guarantees are about
*declared* topology (it cannot know about the snail — only that you gave the
snail two brackets to defeat); sensors it doesn't know about don't exist;
and the last line of defense must remain mechanical and dumb (§7). The docs
lead with the Apex comparison: same ladder philosophy, plus voting, plus a
machine-checked safety case.

## 15. Deployment profiles — `:home` / `:shop` (operator addition, same day)

A reef controller in a **shop** lives in different physics: water leaves the
system *on purpose*, all day — every livestock sale bags a litre of
saltwater. A home-profile ATO reading that as evaporation and replacing it
with RO water dilutes the system sale by sale; over a busy Saturday that is
a salinity crash administered by the controller itself. `profile` makes the
regime a declared, compiler-enforced property of the whole block:

```cure
reef ShopSystem
  profile :shop            # :home is the default and matches §4's behavior
```

### 15.1 What `:shop` requires (profile-as-requirements)

Profiles are not a settings toggle; they change what the compiler demands.
Under `:shop`:

- **Plain automatic ATO is a compile error.** `when depth == Low -> ato.on`
  is rejected: *"shop profile: an automatic RO top-up needs a drop
  classification — a sudden drop might be a sale."* The only path to a pump
  is through the classifier (§15.3).
- **Level must be quantitative** (a `Depth` in mm/litres, §15.2), not a
  boolean threshold — you cannot classify a drop you cannot measure.
- **A saltwater make-up reservoir must be declared**, with its own voted
  `Salinity` quantity and volume accounting.

`:home` keeps §4's semantics unchanged; the classifier is available but
optional there.

### 15.2 Quantitative level metrology — ladders and strips

Two channel forms upgrade `Level` (boolean) to `Depth` (quantitative,
united, via declared sump geometry `mm × footprint → litres`):

```cure
  quantity depth: Depth
    channel strip = sump.kamoer_strip            kind :optical_strip,
                                                 range 0mm..150mm, mount :sump_wall
    channel stack = ladder [ sump.opt_lo  at 40mm,
                             rim.opt_mid  at 70mm,
                             sump.opt_hi  at 100mm ]  kind :optical, mounts :diagonal
    vote 2 of 2, agree within 5mm
    geometry footprint 30cm x 40cm               # depth ↔ volume conversion
```

- **`ladder`** — discrete sensors at declared heights, *diagonally offset*
  (per the operator's design): resolution = spacing, drop magnitude = rungs
  crossed, rate = rungs over time. The offset does double duty, and the
  compiler sees both: it is the metrology (each rung reads a clean
  air/water transition unobstructed by the sensor above) **and** it spreads
  `mount` fault domains, so the §6 common-mode matrix credits the geometry
  automatically — the layout that measures drops cleanly is the same layout
  no single fouling event defeats.
- **`kamoer_strip`** — a continuous long-optical channel (Kamoer-style, as
  used in their KWC water changer): one declared range covering normal
  band, drop, **and overflow** — the top-of-range reading is a first-class
  `Overflow` event (return pump off + alarm, both profiles).

Both are ordinary channels; the vote, agreement band, staleness, and
common-mode analysis apply unchanged.

### 15.3 Drop classification — dual-witness, or it doesn't act

The classifier is a `derived` discriminator over two **dissimilar
witnesses**, in the §3 sense:

1. **Rate profile** (from `depth`): evaporation is slow and sustained
   (≤ the declared rate, e.g. 3 l/day); a **sale is a step** (≥ 0.5 l inside
   a minute, then stable); a **leak is sustained-fast** (a step that never
   stabilizes).
2. **Salinity trend** (the physics witness): evaporation removes water and
   leaves the salt — salinity *rises*; a sale or leak removes *saltwater* —
   salinity is *flat*. The trend is slower and noisier than the rate
   profile, so it acts as a **confirming witness on a longer window**: it
   ratifies or retroactively vetoes classifications rather than co-timing
   them.

```cure
  classify drop_cause from depth, salinity
    evaporation: rate <= 3l/day sustained    confirmed by salinity rising
    removal:     step >= 0.5l within 60s, then stable
                                             confirmed by salinity flat
    leak:        rate >= 5l/hour sustained   confirmed by salinity flat
    else -> :unknown
```

Static discipline: the declared bands must be **mutually exclusive**
(overlap = compile error) and anything between them falls to `:unknown`
(gaps are warned, never silently absorbed). `:unknown` is a coverage-checked
branch like `degraded`/`lost` — a shop controller that hasn't decided what
an unclassifiable drop means does not compile.

### 15.4 Shop responses

```cure
  control ShopTopOff
    on evaporation           -> ato_ro.on            # normal RO, §7 interlocks apply
    on removal(v: Litres)
      when reservoir_sal agrees tank_sal within 0.3ppt ->
        ato_salt.dispense(v)                          # replace what left: saltwater
    on removal(_)            -> alert(:reservoir_salinity_mismatch)   # no auto-dispense
    on leak                  -> ato_ro.off; ato_salt.off; return_pump.off; alert(:leak)
    on unknown               -> ato_ro.off; ato_salt.off; alert(:drop_unclassified)
```

- **Salinity-dependent saltwater top-up:** the dispensed volume is the
  *measured* drop (rungs crossed / strip delta × footprint — units end to
  end), and auto-dispense is **gated on reservoir-tank salinity agreement**;
  a mismatched reservoir alarms instead of acting. `ato_salt` carries its
  own §7 interlocks (max per event, max per day, reservoir volume
  accounting — a doser whose arithmetic says the reservoir is empty
  abstains).
- **Retro-veto:** if the salinity trend later contradicts a classification
  the controller already acted on (dispensed as `removal`, but salinity is
  drifting), further auto-dispense is **suspended** and the discrepancy
  alarmed — the trend witness is slow, so its authority is retrospective
  and latching, per §5's sticky-suspicion rule.
- Leak beats everything: it shares the sale's salinity signature and is
  distinguished purely by time profile, so it is classified conservatively
  (a `removal` that keeps falling *becomes* a leak) and its response is
  everything-off-plus-alarm. In a shop, staff are present — alarms are
  cheap; wrong water is not.

### 15.5 What this adds to `cure test`

```
  ✓ classifier_bands_exclusive    proved by construction — no overlap, gap 3–5 l/hour → :unknown (warned)
  ✓ dispense_bounded              proved by construction — ≤ 2l/event, ≤ 10l/day, ≤ reservoir accounting
  ✓ shop_no_blind_ato             proved by construction — no pump reachable except via drop_cause
  ✗ saturday_rush                 tested (seeded) — 40 sales + evaporation + one leak injected
                                  over a simulated day: salinity 34.8→35.1ppt, leak caught in 4min
```

The `saturday_rush` template ships with the profile: a generated business
day of interleaved sales, evaporation, and one fault, asserting salinity
stays in band and the leak is isolated — the shop-mode single-fault
criterion.

## 16. Open decisions (ledger)

1. **Quorum sub-macro extraction** (§13) — decide when `home`/`grow` want
   it; premature now.
2. **Error-code block** — register a reef block (E2xx range) with the
   explainer registry; also allocate blocks for the other promoted-twelve
   macros in the same pass.
3. **Redundant actuators** — dual return pumps / dual heaters
   (alternation, wear-leveling, failover): natural next step, design
   deferred until the sensor side lands.
4. **Commercial hardware interop** — driving Apex/Hydros modules vs. pure
   DIY sensor set for v1 (recommend: DIY + published driver declarations;
   interop invites reverse-engineering churn).
5. **AWC (auto water change)** — coupled dual-pump volume accounting;
   rides dosing + analytic channels; v1.5.
6. **Leak sensors & power monitoring** — more fault domains (a leak rope is
   just another boolean quantity; PSU voltage as an analytic health
   channel); additive.
7. **Anomaly detection beyond bands** (trend/ML) — advisory-only if ever;
   the voting core stays arithmetic.
8. **`derived` channel placement syntax** (`at host`) — confirm it reuses
   fleet's `at` annotation verbatim.
9. **Corrective blending** (`:shop`) — make-up water salinity chosen to
   nudge a drifted tank back to target, vs. v1's match-within-band gate;
   defer until the plain gate has run in a real shop.
10. **Multi-tank shop topologies** — a shop is many display tanks on shared
    sumps: quantities per tank, shared reservoirs, per-tank classifiers;
    fleet handles the nodes, but the quantity-sharing surface needs design.
11a. **Salinity channel driver declarations** — ship `driver`s for the
    Appendix-A kinds: EZO-EC (isolated) contacting cell, toroidal inductive
    cell, dual-MS5837 hydrostatic density standpipe, and an inline
    refractometer (Pyxis RT-50-class) for `:shop`; excitation interleaving
    schedule for un-isolated cells.
11. **Kamoer-strip driver declaration** — range/resolution/protocol of the
    KWC-style long optical sensor as a shipped `driver`; plus ladder-channel
    sugar (`ladder [...] at heights`) as macro surface vs. plain channels.

## 17. Non-goals

- No certification claims of any kind.
- No replacement of mechanical backstops (§7 — designed-in humility).
- No cloud dependency: the tank must not care that the internet is down
  (host node optional; alerts degrade to local buzzer/display).
- No chemistry *management* advice (the macro controls; reef chemistry
  targets are the keeper's numbers, entered in `config`).

## Appendix A — Salinity channels: the full survey (2026-07-08)

The dissimilarity requirement (§4) is only as good as the *buyable* kinds.
This appendix is the market survey plus the design consequences it forced.

### A.1 Naming things: "the usual probe" IS the resistance-based probe

The standard hobby salinity probe — Neptune, GHL, any BNC lab cell — is a
**contacting conductivity cell**: two graphite or platinum electrodes
reading the solution's resistance. It *must* be driven with **AC excitation**
(bipolar square wave, kHz-range): DC polarizes the electrodes within
seconds and electrolyzes the water, so "a driver board that provides AC" is
not an optional nicety, it is how conductivity measurement works at all.

The off-the-shelf answer is the **Atlas Scientific EZO-EC** carrier: AC
excitation + measurement on one module, I²C/UART out (a clean `driver`
regmap declaration), accepts any standard BNC K=1.0 cell — including the
Neptune and GHL probes reefers already own. ~$60–120 per channel with an
isolated carrier.

### A.2 The four buyable kinds

**`:conductivity_contacting`** — EZO-EC + BNC cell (above). The workhorse.
Failure modes: electrode fouling, polarization drift, calibration decay —
which is why two of these alone satisfy redundancy but not dissimilarity
(`require dissimilar kinds >= 2` exists for exactly this).

**`:conductivity_inductive`** — toroidal (electrodeless) cells: two coils
transformer-coupled through a loop of the water itself. No electrodes ⇒ no
polarization, no fouling drift. Industrial gear (surplus ~$150–400). Same
measured quantity as contacting cells but **dissimilar failure modes** —
the cheap seat between full physics-dissimilarity and mere duplication.

**`:density_hydrostatic`** — the sleeper: two MS5837-class pressure sensors
at a declared vertical separation on a standpipe. Δp = ρ·g·Δh → density →
salinity, for **~$30**. Dissimilar *physics*: blind to everything that
fools conductivity (temperature-compensation error, electrode state,
organics). The honest resolution math: full reef salinity range (≈1.020 →
1.028 SG) spans only ~16 Pa over a 20 cm column, against ~2 Pa RMS
per-sample sensor noise — marginal per sample, **but salinity is a slow
quantity**, and minutes of averaging make this an excellent *confirming*
voter (§5's longer-window witness role, same as the shop profile's trend
witness). Declare the separation and column geometry; the units machinery
does the rest.

**`:refractive`** — to the direct question: **yes, inline refractometer
probes exist** — the electronic version of the hobbyist's handheld
refractometer, measuring critical-angle refractive index continuously in a
flow cell. They are industrial process instruments: **Pyxis RT-50** is the
accessible end (~$1.5k class); Atago PRM, Anton Paar L-Rix, MISCO MVP, and
Vaisala Polaris sit above it, quote-priced. Not a `:home` recommendation —
but entirely plausible for **`:shop`**, where one premium optical channel
on the shared sump serves the whole system. Needs temperature compensation
and a flow cell; true optical dissimilarity from everything above.

**`derived :volume_accounting`** — the $0 analytic channel already specced
(§4): the top-off ledger's predicted salinity motion voting against the
physical sensors.

### A.3 The design consequence — excitation is a fault domain

Atlas's own documentation states that conductivity excitation **injects
electrical interference into the water**, that this matters critically with
multiple probes in one water body, and that galvanic isolation is "100%
effective" against it. For a quorum architecture that is not a shopping
note — it is a **correlated-failure channel**: two un-isolated contacting
cells voting in the same sump can corrupt *each other*, which is precisely
the class of coupled failure the whole design exists to defeat.

Hence (§6): the fault-domain vector carries an `excitation` axis. Isolated
carriers clear it; un-isolated cells are treated as sharing a domain AND
get compiler-scheduled **interleaved excitation windows** at the driver
layer (never energized simultaneously). The common-mode matrix reports
shared excitation like any other defeating domain, and `cure reef report`
shows which carriers the plan assumes are isolated.

### A.4 Recommended quorums

- **`:home`** — two contacting cells (isolated carriers, different nodes,
  different brackets) + one hydrostatic-density standpipe + the derived
  channel: **three dissimilar kinds, `vote 2 of 4`, ~$100 over the usual
  single-probe build.**
- **`:shop`** — the same, plus one inline refractometer (Pyxis-class) on
  the shared sump as the premium fourth kind; it also strengthens the shop
  profile's salinity-trend witness (§15.3) with an instrument whose drift
  is uncorrelated with every conductivity channel.

Driver declarations for all four kinds, including the excitation-
interleaving schedule, are ledgered (§16.11a).

### A.5 Survey sources

- Atlas Scientific EZO-EC (AC-excitation carrier + isolation guidance):
  https://atlas-scientific.com/embedded-solutions/ezo-conductivity-circuit/
  (datasheet: https://www.openhacks.com/uploadsproductos/ec_ezo_datasheet.pdf)
- Pyxis RT-50 / RT-100 inline refractometers:
  https://www.pyxis-lab.com/product/rt-50-prism-inline-refractometer/
- Atago PRM inline series: https://www.atago.net/en/products-prm-top.php
- Anton Paar L-Rix: https://www.anton-paar.com/us-en/products/details/l-rix/
- MISCO MVP: https://www.misco.com/product/mvp-inline-process-refractometer-sensor/
- Vaisala Polaris: https://www.vaisala.com/en/industrial-measurements/products/liquid-concentration

## Sources (prior art reviewed 2026-07-08)

- reef-pi: https://reef-pi.github.io/ and https://github.com/reef-pi/reef-pi
- Neptune ATK layered failsafes: https://www.reef2reef.com/ams/neptune-apex-programming-tutorials-part-3-automatic-top-off-kit-atk.692/ and https://www.bulkreefsupply.com/atk-v2-auto-top-off-kit-neptune-systems.html
- Neptune optical sensor practice: https://www.bulkreefsupply.com/content/post/brstv-product-spotlight-neptune-systems-os-1-v2-optical-sensor
- Hydros Collective (multi-brain failover, power-domain cabling): https://www.coralvuehydros.com/product-support/hydros-control/hydros-collective-101/
