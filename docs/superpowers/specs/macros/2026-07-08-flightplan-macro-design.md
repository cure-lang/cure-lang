# `flightplan` — VFR Flight Planning with Weight & Balance as a Refinement

**Date:** 2026-07-08
**Status:** design. Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
(idea backlog #52, promoted); companion of
[`2026-07-08-checklist-macro-design.md`](2026-07-08-checklist-macro-design.md),
specced in parallel. Built as a `macro` (§5) — zero compiler special-casing.

---

## 1. Purpose

The classic VFR cross-country killers are arithmetic. Weight & balance
outside the envelope. Fuel below legal reserve. Density-altitude
performance exceeding the runway. None require judgment to catch — only
that someone actually do the numbers for *this* loading, *this*
temperature, *this* runway, and redo them when anything changes. All three
are refinements over concrete declared numbers, so per the parent's thesis
(§1) all three discharge by pure computation: no solver, no proof term, no
hole. An out-of-CG loading, a landing below reserve, or 1,850 ft of ground
roll on a 1,600 ft strip is a **compile error**, in pilot vocabulary,
before anyone drives to the airport.

## 2. Surface

Two declarations: an `aircraft` profile (the POH transcribed as data, once
per airframe) and a `flight` block (this trip). Units — `kt`, `nm`, `ft`,
`gal`, `lb`, `in`, `degC`, `min` — come from the units macro throughout;
`flightplan` is its heaviest consumer, shipping the aviation unit pack via
units §8.2.

```cure
aircraft N735QD                       # 1977 C172N, from the POH + last W&B
  empty  1441lb at 39.4in
  fuel   40gal usable, at 48.0in, density 6.0lb per gal

  station front_seats at 37.0in
  station rear_seats  at 73.0in
  station baggage_a   at 95.0in, max 120lb

  envelope Normal                     # declared polygon: (weight, CG) points
    (1500lb, 35.0in) (1950lb, 35.0in) (2300lb, 38.5in)
    (2300lb, 47.3in) (1500lb, 47.3in)

  cruise                              # POH table 5-7, declared as data
    at 6000ft: 105kt, 8.1gal per hr
    at 8000ft: 108kt, 7.7gal per hr

  takeoff_roll                        # POH table 5-4; landing_roll likewise
    at pressure_alt 0ft,    15degC: 865ft
    at pressure_alt 5000ft, 25degC: 1500ft
```

```cure
flight KPAO_to_KTRK                   # night VFR, Palo Alto → Truckee
  aircraft N735QD
  rules night                         # selects the 45min legal reserve
  loading
    front_seats: 340lb                # two adults
    rear_seats:  330lb                # two more
    baggage_a:   40lb
    fuel:        40gal                # full tanks at start
  leg KPAO -> O22   at 7500ft, tas 105kt, wind 310 at 15kt
  leg O22  -> KTRK  at 9500ft, tas 108kt, wind 290 at 25kt
  depart KPAO runway 31 length 2443ft, elevation 4ft,    temp 18degC, altimeter 29.92
  arrive KTRK runway 29 length 4654ft, elevation 5904ft, temp 24degC, altimeter 30.05
```

Everything is a concrete literal — weights, arms, winds, temperatures,
runway lengths. That is the whole trick: the indices are declared numbers,
so every check below reduces away at compile time (parent §1, principle 3).

## 3. Weight & balance — the envelope refinement

The centerpiece. CG is pure moment arithmetic over the declared loading:
each station's weight times its arm, summed, divided by total weight. The
envelope is a **2D refinement region** — the declared polygon — and
membership is point-in-polygon over declared coordinates: still concrete
arithmetic, still discharged by computation.

The check runs at **two** weights, and the second is the one that matters:

1. **Takeoff** — total weight and CG with declared fuel at start.
2. **Landing** — the fuel burned per the leg computation (§4) shrinks the
   fuel station's moment and **the CG moves**. Every pilot computes takeoff
   W&B; the landing check is the one that gets skipped, because it needs
   the fuel-burn numbers first. The compiler has them, so it always runs.

The flagship failure, and the macro's reason to exist:

```
error[E1xx]: landing CG is outside the Normal envelope
  --> ktrk_trip.cure:8
  Takeoff is fine: 2291lb at 41.2in, inside Normal. But after burning
  22.4gal en route, landing is 2157lb at 42.9in — 0.6in aft of the
  envelope at that weight. The fuel you burn sits forward of your
  passengers; as it goes, the CG walks aft. Move 20lb from baggage_a
  forward, or shift a rear-seat passenger, and re-check BOTH points.
```

Where a profile declares a maximum zero-fuel weight, ZFW is a third
intermediate check — same machinery, one more concrete point. Station `max`
limits (`baggage_a max 120lb`) are ordinary range refinements, checked at
the loading declaration before any envelope math runs.

## 4. Fuel discipline

Per-leg fuel is computed, not estimated: leg distance, declared winds
aloft, and the declared cruise table give groundspeed, time en route, and
gallons burned — wind triangle, table interpolation, multiply by time, all
closed-form arithmetic over declared numbers. The legal floor is a
refinement on the **fuel remaining at landing**, in minutes at cruise
consumption: day VFR `{remaining | remaining >= 30min}`, night VFR
`>= 45min`. A plan landing below reserve does not compile; `rules night`
selects the floor, and there is no way to select "no reserve".

Personal minimums come from `config` and obey the **monotone-safety rule**,
stated as law exactly as in the dive spec: config may only *tighten* a
refinement, never loosen it. A club sets `fuel_reserve: 60min` and every
plan under that config holds the stricter floor; nothing anywhere can push
the reserve below the legal figure. The legal minimum is the type;
personal minimums intersect with it.

## 5. Performance

Density altitude is computed from the declared field elevation,
temperature, and altimeter setting — standard corrections, all concrete
arithmetic. Takeoff and landing distances are interpolated from the
declared POH tables at that density altitude and weight (bilinear;
extrapolation past the table's edge is a compile error — the POH doesn't
know either). The runway check is a refinement with a declared safety
factor:

```
required_distance * safety_factor <= declared runway length
```

The default factor is **1.5** — the 50% margin every instructor teaches —
and per the monotone-safety rule config can only raise it. Both runways are
checked at their respective computed weights: the arrival check uses
landing weight at the arrival density altitude, which on a hot afternoon at
Truckee is precisely the number nobody runs in their head.

## 6. Generated artifacts

A compiling plan generates the paperwork, print-first (the kneeboard is
primary, exactly as the checklist macro treats paper as primary): a
**navlog** (per leg: magnetic heading with wind correction, groundspeed,
time, fuel burned and remaining); a **W&B sheet** (the envelope polygon
plotted with **both** points marked, takeoff and landing, plus the moment
table); a **fuel plan** (per-leg burn, reserve floor, margin). Rendering
the same artifacts on a device or EFB display is one line — the
`display`/`board` crossover — but the printed kneeboard set is the
deliverable v1 optimizes.

## 7. Explainers

Registered per the parent's §4 (codes allocated in the error-explainer
registry); every message speaks ramp vocabulary and names a fix:

```
error[E1xx]: takeoff CG out of envelope
  With 4 adults and full fuel, takeoff CG is 2.1in aft of the envelope
  at 2450lb. Reduce baggage or fuel — and re-check the landing CG after
  any change, because burning fuel moves it further aft.

error[E1xx]: fuel reserve below night VFR minimum
  Leg 3 arrives with 22min of fuel at cruise burn — night VFR requires
  a 45min reserve. Add a fuel stop, carry more fuel (re-check W&B), or
  replan the altitude for better winds.

error[E1xx]: runway too short for computed takeoff performance
  Density altitude 8,200ft: ground roll 1,850ft exceeds runway 09's
  1,600ft — and that is before the 50% safety factor. Wait for cooler
  air, reduce weight, or use runway 29 (4,654ft).
```

## 8. `check` integration

Most of what a user would test is already static: a compiling plan has
*proved* its envelope, reserve, and runway refinements — the report reads
`proved by construction; 0 runs`, the signature static-discharge moment
(parent §7.5). Shipped property templates cover what varies:

- **Envelope sweep** — generated loadings walk the declared polygon's
  corners and edges, asserting the point-in-polygon verdict flips exactly
  at the boundary — a test of the *profile transcription*, catching a
  mistyped envelope point.
- **Unit round-trips** — converting fuel `gal ↔ lb` through the declared
  fuel density and back never changes any verdict.
- **Wind sensitivity** — the plan re-run with generated wind errors inside
  a declared margin (default ±10kt) must stay legal on fuel; reported, not
  enforced, so the pilot sees how brittle the plan is.

## 9. Relations

- **`units`** — the heaviest consumer in the catalog: kt, nm, ft, gal, lb,
  in, degC, min in every declaration; ships the aviation unit pack per
  units §8.2. No bare number anywhere in a plan.
- **`config`** — personal minimums (reserve, safety factor) under the
  monotone-safety rule (§4, §5).
- **`checklist`** — companion macro: the preflight card references the
  computed numbers ("Fuel — 40gal CONFIRMED per plan"), and a plan's phase
  transitions are natural checklist triggers; ledgered on both sides.
- **Report generation** — the navlog/W&B/fuel artifacts (§6) ride the
  general print/display rendering surface.
- **`dive`** — sibling safety-refinement macro: the same pattern of legal
  floors as types with config-only-tightens on top, over different tables.

## 10. Safety honesty

Stated once, unhedged. This is a **planning aid** — not an EFB replacement,
not certified, meeting no software assurance standard for flight
operations. The POH numbers remain authoritative: the macro checks
arithmetic *over* the profile the owner transcribed, and a transcription
error is the owner's to catch (the §8 envelope sweep helps; it does not
absolve). Weather, winds aloft, NOTAMs, and TFRs are **runtime data this v1
does not fetch** — winds and temperatures are declared inputs, entered from
a briefing. Live-data integration is ledgered (§11.1) with the explicit
note that stale-data risk changes the product class: a tool that silently
plans on yesterday's winds is more dangerous than one that visibly demands
today's. The pilot in command owns the go decision; the macro's job is
to make the arithmetic impossible to skip, not to make it.

## 11. Open decisions (ledger)

1. **Live weather/NOTAM integration** — fetching winds aloft and METARs at
   plan time. Deferred: freshness, source authority, and the stale-data
   product-class shift (§10) all need answers first.
2. **IFR** — non-goal for v1, possibly permanent: alternates, approach
   minima, a far wider regulatory surface, mostly judgment not arithmetic.
3. **Non-US reserve rules** — EASA/CASA/Transport Canada differ; ship
   regulation packages as declared data (as the dive macro ships tables),
   selected in the flight block, monotone rule intact.
4. **Multiple aircraft profiles / club fleets** — profile storage, revision
   after a new W&B or an STC, distribution to members; likely rides
   `schema` + `fleet` like checklist revisions.
5. **Glide-range rings** — terrain-aware glide coverage per leg; needs
   elevation data, which reopens the runtime-data question.
6. **Helicopter W&B** — lateral CG, two-axis envelopes, rotor performance:
   different math, out of this macro.

## 12. Non-goals

- **No IFR** (v1; see §11.2).
- **Not a certified EFB** and not trying to become one (§10).
- **No live data in v1** — declared inputs only.
- **Not flight instruction** — the macro checks a plan, it does not teach
  planning; its errors assume the vocabulary a human instructor teaches.
