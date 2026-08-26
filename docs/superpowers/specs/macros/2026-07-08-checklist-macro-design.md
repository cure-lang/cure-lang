# `checklist` — Aviation-Style Checklists as Typestate

**Date:** 2026-07-08
**Status:** design. Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
(idea backlog #37, promoted); companion of
[`2026-07-08-flightplan-macro-design.md`](2026-07-08-flightplan-macro-design.md)
(being specced in parallel). Built as a `macro` (§5) — zero compiler
special-casing.

---

## 1. Purpose

Aviation is the one culture that already *thinks* in typestate. Ordered items,
challenge-and-response, abnormal branches, memory items — pilots have run a
state machine out loud for ninety years. What they have never had is a
compiler enforcing it: nothing today catches the checklist that references a
switch no earlier item set, the abnormal procedure nothing can reach, or the
emergency flow that trails off without a terminal instruction. The discipline
pre-exists; the tool is the missing half. `checklist` supplies the tool.

The macro generalizes past the cockpit — pre-op surgical checklists, lab
startup, boat pre-departure, ham field day are the same shape — but aviation
vocabulary leads: its conventions (challenge → response, normal/abnormal/
emergency, memory items) are the most precise available, and everyone else's
checklists are informal copies of them.

**Safety honesty, stated once and plainly:** this is a supplemental aid for
GA and hobby use. It is not certified avionics, and the printed card plus the
pilot's trained flow remain authoritative in the aircraft. The macro makes
*the checklist document* provably coherent; it does not make the device a
required instrument.

## 2. Surface

A `checklist` block holds **procedures** — `normal`, `abnormal`, `emergency` —
each a sequence of items. An item is a `challenge -> expected response` pair:

```cure
checklist C172S
  use Std.Measurements          # kt, degC, psi, deg via the units macro

  normal BeforeStart
    "Preflight inspection" -> "COMPLETE"
    "Fuel selector"        -> "BOTH"
    "Avionics master"      -> "OFF"
    "Flaps"                -> set 10deg           # establishes flap state

  normal EngineStart
    after BeforeStart
    "Mixture"       -> "RICH"
    "Master switch" -> "ON"
    "Ignition"      -> "START"
    "Oil pressure"  -> {p: Psi | p >= 25psi} within 30s
      if oil_pressure < 25psi -> goto AbnormalStart
    "Flaps"         -> check 10deg                # references established state

  abnormal AbnormalStart
    "Ignition"      -> "OFF"
    "Mixture"       -> "IDLE CUTOFF"
    "Master switch" -> "OFF"
    resolve EngineSecured

  emergency EngineFireOnStart
    memory                                        # executable without the card
    "Ignition"      -> "CONTINUE CRANKING"
    "Mixture"       -> "IDLE CUTOFF"
    "Fuel selector" -> "OFF"
    "Fire"          -> "EXTINGUISH"
    resolve EngineSecured
```

- **Responses** are plain strings where no data exists (`"RICH"`), typed
  values where sensors or state do (`set 10deg`, `{p: Psi | p >= 25psi}`) —
  units ride the units macro, so a knots/mph or °C/°F confusion is the
  same compile error it is everywhere else in Cure.
- **Branch points** are `if <condition> -> goto <Procedure>` lines attached
  to an item; the condition ranges over state established by items or sensed
  values (§5).
- **`after`** declares procedure ordering; **`resolve`** names the defined
  end state a procedure terminates in (a terminal, or a handoff procedure).
- **`memory`** flags a procedure (or its leading section) as memory items:
  the part crews must execute without the card. Memory sections are
  **length-refined** — `{items | length(items) <= 6}` — because "memory
  items fit in working memory" is a real human-factors rule, here a
  refinement rather than a style guide. Exceeding it is a compile error.

## 3. Typestate & flow discipline

Execution order is typestate: **item N is only executable once items 1..N−1
are complete** — the same GADT-index machinery as `protocol`'s handles and
`driver`'s init blocks, pointed at a checklist. On top of the per-item order,
four static disciplines hold over the whole document (per hiding principle 3,
none ever surfaces a goal):

1. **Coverage** — every condition and every `goto` target names a procedure
   that exists. A typo'd branch target is caught at compile time, not at
   2,000 ft.
2. **Reachability** — every `abnormal` procedure is reachable from some
   normal item's branch point, or carries a declared `entry` (procedures a
   pilot enters directly). Dead procedures are errors: an unreachable
   abnormal is a maintenance trap.
3. **No dead ends** — every procedure terminates in a defined state
   (`resolve`, or a `goto` chain that does). Totality over the procedure
   graph — the same size-change story as everywhere in Cure, here reading
   as "you cannot write a checklist that strands the crew."
4. **State provenance** — an item that *references* state (`check 10deg`, a
   branch condition over `flaps`) must be preceded by an item that
   *establishes* it (`set 10deg`). "Item 7 checks flaps 10° but no earlier
   item sets flaps" is a compile error — the check no paper process has ever
   had, and exactly the defect that creeps in as checklists are edited over
   years.

## 4. Execution surfaces

One declaration, three surfaces:

1. **Printable kneeboard cards** — the primary surface, because paper is
   primary in cockpits and the macro respects that. `cure checklist print`
   renders normal/abnormal/emergency card sets, memory sections boxed, in
   standard challenge–response layout. The proofs ride along invisibly: a
   card printed from a compiled checklist is one whose branches all resolve.
2. **An ESP32 / e-paper cockpit checklist device** — the `display` + `board`
   crossover, and a real product niche (panel-mount checklist devices exist
   and are expensive). Items advance by button or sensor (§5); procedure,
   position, and completed-item set persist via `schema` — worth calling
   out: **a checklist interrupted by a master-switch cycle resumes exactly
   where it was**, because execution state is a persisted, schema-migrated
   record, not RAM. A device that forgets its place during an electrical
   abnormal is worse than paper; this one provably doesn't.
3. **Voice callouts** — challenge spoken, response acknowledged. Ledgered
   (§9.1); the typestate is surface-agnostic, so voice is rendering, not
   semantics.

Underneath all three, execution lowers onto `reducer`: states are
(procedure, position) pairs, messages are acknowledgements and sensor
readings, emissions are the display/print/voice events. §3's typestate
guarantees become the reducer's edge-coverage guarantees for free.

## 5. Sensor-assisted items

Where the device has data — via `fleet`/`driver`, e.g. a connected engine
monitor (EMS) — a typed-response item **auto-verifies**: `"Oil pressure" ->
{p: Psi | p >= 25psi}` completes itself when the sensed value satisfies the
refinement, and its branch condition fires itself when it doesn't. Unsensed
items are manually acknowledged.

The typestate does not care which: **completion is completion.** Both paths
advance the same state index, so a checklist runs identically on a bare
device, a partially-sensed panel, and a fully-instrumented one — graceful
degradation by construction. Which items may *never* auto-verify is a policy
question, not a type question; see §9.5.

## 6. Explainers

In cockpit vocabulary, per the parent's §4 template (codes allocated in the
error-explainer registry):

```
error[E1xx]: item 7 checks flaps 10° but no earlier item sets flaps
  --> c172s.cure:18
  "Flaps" -> check 10deg reads flap state, but no item in BeforeStart or
  EngineStart establishes it. Add a `set` item before this one, or move
  the flap item from BeforeTakeoff.
```

```
error[E1xx]: EMERGENCY: Engine Fire has no terminating item
  --> c172s.cure:31
  Every emergency procedure must end in a defined state — resolve to
  EngineSecured, LAND AS SOON AS POSSIBLE, or a handoff procedure. A crew
  must never run off the end of an emergency flow.
```

## 7. `check` integration

Shipped property templates (parent §7.5):

- **Reachable and total** — all branches reachable, no dead ends. These are
  §3's static checks, so the report line reads `proved by construction —
  procedure graph total; 0 runs`: the signature static-discharge moment.
- **Interruption/resume** — generated interruption sequences (power cycle at
  every position, mid-abnormal, mid-branch) drive the schema-persisted
  state; resume must never lose position or re-run a completed item. This
  one runs, because persistence glue is code, not types.
- **Sensor/manual agreement** — for every sensed item, a trace where the
  sensor auto-verifies and one where the same value is manually acknowledged
  must produce identical execution states downstream.

## 8. Relations

- **`display` / `board`** — the cockpit device (§4.2) is an ordinary board
  program; the e-paper rendering is the display surface's job.
- **`schema`** — execution-state persistence and its migrations (a firmware
  update mid-annual must not lose checklist state semantics).
- **`reducer`** — the execution state machine underneath every surface (§4).
- **`flightplan`** — companion macro, specced in parallel
  ([`2026-07-08-flightplan-macro-design.md`](2026-07-08-flightplan-macro-design.md));
  a plan's phase transitions are natural checklist triggers ("entering
  DESCENT ⇒ offer the Descent checklist").
- **`units`** — every typed response with a magnitude (kt, °C, psi, deg)
  goes through units; no bare numbers in responses.
- **`fleet` / `driver`** — the sensor path for auto-verification (§5).

## 9. Open decisions (ledger)

1. **Voice callout surface** — TTS on-device vs. paired phone; how a spoken
   response is acknowledged (button, voice, timeout-to-manual).
2. **Revision control** — checklists change with aircraft modifications
   (STCs, avionics swaps). Versioning plus *diff in checklist vocabulary*
   ("rev 4 moves Flaps from BeforeTakeoff to EngineStart; state provenance
   re-checked") — likely riding the schema-migration machinery.
3. **Fleet distribution** — pushing checklist revisions to a club's or
   school's devices via `fleet`, with the mixed-version questions that
   implies (shared with protocol §10.5).
4. **Two-pilot challenge-response mode** — one device, two roles (PF/PM):
   who acknowledges, whether `protocol` models the exchange, whether a
   second device is involved.
5. **Auto-sensing integration ceiling** — which items may NEVER auto-verify
   even when sensed (gear down is the canonical argument: the sensor can be
   the thing that failed). Recommendation: a `manual_only` item marker, so
   the ceiling is declared in the checklist itself and the device cannot be
   configured around it.

## 10. Non-goals

- **No certification.** Part 23/25 software assurance is out of scope,
  permanently for this macro; see §1's honesty statement.
- **Not a POH replacement.** The macro encodes and checks a checklist the
  owner writes; the POH's procedures and limitations remain the authority.
- **No auto-generation from POH PDFs.** Attractive, someday plausible, but
  extraction-from-PDF correctness is exactly the silent-error surface this
  macro exists to eliminate. Out of scope.
