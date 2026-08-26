# `fleet` — Distributed Hub Illusion via Endpoint Projection

**Date:** 2026-07-08
**Status:** design (operator-requested). Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
(§7.4); built as a `macro` (§5), so zero compiler special-casing.
**Operator goal (verbatim intent):** write a `hub` logic section that
coordinates every item of the fleet *as if it ran on a beefier central hub* —
but the compiler **distributes that logic among the nodes**, which communicate
directly with each other. No actual hub exists at runtime.

---

## 1. The idea has a name — and Cure dissolves its hardest part

Writing one global program and compiling per-node code is **choreographic
programming** / **endpoint projection** (Choral, HasChor, Pirouette; multiparty
session types underneath) and **multitier programming** (ScalaLoci, ML5,
Links: placement types on one program). The classically hard parts:

1. **Knowledge of choice** — when the global program branches, every node
   whose behavior differs across the branch must *learn* which branch was
   taken; projection must insert those notification messages correctly.
2. **State placement** — "the hub's variable" must live somewhere.
3. **Partial failure** — a real hub is one failure domain; a projected hub is
   many. The illusion leaks under partition unless the design says exactly
   what happens.

Cure's structure defuses (1) and most of (2) before we start:

- **Hub logic is Flow logic — control flow is reified as data flow.** A
  choreography's `if` is, in FRP, just a `Bool`-valued signal flowing to its
  consumers. Knowledge of choice *is* the dataflow edge; projection inserts
  no special selection messages because the "choice" is already a stream with
  declared consumers.
- **Pure derivations replicate for free.** A pure signal function computes
  the same value from the same inputs on every node — so any node that needs
  a derived signal can compute its own copy locally from the streams it
  already receives. No coordination, no canonical copy, semantics preserved.
  (This is the deep reason hub-illusion is *sound* here and unsound in an
  imperative language: purity is what makes replication invisible.)
- **Effects already name their location.** A `sink` is declared on a node's
  hardware; a scan's owner is inferable from who consumes it (§4).

What remains genuinely hard is (3) failure and the small residue of (2)
(truly shared, order-sensitive state). The design's stance: **the illusion is
checked, not faked** (§5) — hub logic that projects cleanly compiles to
direct peer messaging; hub logic that secretly requires global agreement is
a *compile-time diagnostic naming the exact conflict*, never silent
best-effort.

## 2. Surface

```cure
fleet Greenhouse
  transport espnow                    # or mqtt("broker.local"), udp(:lan)

  node sensor(3) on :esp32c3          # three identical nodes; identity is Fin(3)
    let bme = Bme280.on(i2c0)
    source temp = bme.celsius every 2s

  node valve on :esp32c3
    let relay = gpio.out(pin.gpio5)
    sink water                        # Command(WaterCmd) — actuator surface

  node display on :pico
    sink screen                       # rendered by a `view`

  hub
    ## Written as if every signal lives in one place.
    let avg  = sensor.temp.mean()     # sensor.temp : Vector(3, Signal(Celsius))
    let dry  = avg |> above(29.0)

    valve.water   <- dry |> hold_for(10s)
    display.screen <- render(avg, dry)

    on NodeLost(sensor(i)) ->         # failure is a message — coverage-checked
      display.screen <- warn("sensor " <> show(i) <> " offline")
      valve.water    <- Closed        # fail-safe posture

    on NodeBack(sensor(i)) ->
      display.screen <- info("sensor " <> show(i) <> " back")
```

Surface rules:

- `node Name(k) on :board` declares role `Name` with `k` replicas — node
  identity is `Fin(k)` (the landed `Bounded` builtin); `sensor.temp` is a
  `Vector(k, Signal(..))`. Membership is **static and declared** (hiding
  principle 1: indices flow from declarations). Dynamic membership is
  ledgered (§9).
- `hub` contains ordinary Flow code over role-qualified signals/sinks, plus
  `on NodeLost/NodeBack` clauses. **There is no `hub` node in the generated
  system** — the block is a projection source only.
- Everything inside `node` blocks is the normal single-board surface
  (`board`, drivers, `source`/`sink`).

## 3. What projection emits

For the example above, `cure build` produces one image per role (three
instances of `sensor` differ only in a burned-in `Fin(3)` identity):

- **sensor(i):** samples `temp`, broadcasts it on the fleet transport every
  2s (latest-value semantics, §6) with a heartbeat piggybacked.
- **valve:** subscribes to all three `temp` streams; computes `mean`, `above`,
  `hold_for` **locally** (pure ⇒ replicated); drives the relay; holds the
  fail-safe rule for missing sensors.
- **display:** subscribes to the same three streams; computes its own `avg`
  and `dry` copies; renders. (Note `avg` is computed twice in the fleet —
  once on valve, once on display. That is correct and free: purity means the
  copies cannot disagree on the same inputs, and two local computations are
  cheaper than one "canonical" computation plus a consensus on its value.)
- **Channels:** every cross-node edge in the flow graph becomes a generated
  `packet` layout + `protocol` session (the §7.4 "one declaration, both ends
  of the wire" machinery) — typed at both endpoints, versioned (§9).

## 4. Projection rules (the ownership algorithm)

Applied to the hub's flow graph, in order:

1. **Sources** live where declared (the node that owns the hardware).
2. **Sinks** live where declared. A sink is the only place an effect happens.
3. **Pure derivations** (`map`, `mean`, `above`, `merge`, …) are **replicated
   into every consumer node** that needs their output. No owner exists.
4. **Stateful combinators** (`scan`, `hold_for`, debounce, any `reducer`)
   need a single owner — state is where the illusion can break. Owner
   inference: the node hosting the (unique) sink downstream of the scan. If
   exactly one node consumes it, it lives there — done, zero coordination.
5. **Residue — the checked illusion (§5):** a stateful combinator consumed by
   sinks on *multiple* nodes, where message arrival order could make the
   replicas diverge. This is the only case that cannot be projected silently.

Cross-node edges created by rules 1–4 get **heartbeats and staleness
tracking** generated automatically; a subscription that misses its expected
rate long enough synthesizes `NodeLost` (§6).

## 5. The projectability diagnostic — never lie about distribution

For rule-5 residue, the compiler refuses to guess, and names the conflict in
hub vocabulary:

```
error[E13x]: `session_count` (hub, line 41) is stateful and drives sinks on
  BOTH valve and display, and its updates do not commute — the two nodes
  could observe different orders and disagree.

  Choose one:
    1. own it:    `let session_count = scan(...) at valve`
                  (valve computes; display receives valve's copy — one hop
                  of extra latency, no disagreement)
    2. merge it:  make the update commutative (a counter, max, set-union —
                  `scan` over a declared merge) — replicas converge without
                  coordination            [CRDT semantics, spelled `merge`]
    3. agree on it: `at quorum(...)` — a real agreement round per update
                  (expensive on MCUs; only for decisions that must be unique)
```

- Option 1 (`at <node>`) is one annotation and covers the overwhelming
  majority of real cases (the single-writer principle).
- Option 2 asks the user to declare a commutative-monoid merge; the
  `check` macro ships a template property that *tests* the claimed
  commutativity/associativity (and certificate elevation can often prove it
  for arithmetic merges).
- Option 3 is deliberately loud and rare; the consensus primitive choice is
  ledgered (§9) — v1 may ship with options 1–2 only.

Commutativity detection for the *silent* path is conservative: only
recognized-by-construction merges (counters, max/min, set union — a small
library of `merge`-blessed combinators) project silently; everything else in
rule 5 gets the diagnostic. No solver heuristics deciding distribution
semantics.

## 6. Failure model — the illusion's honest edge

A real hub fails totally; a projected hub fails partially. The design makes
partial failure **impossible to ignore rather than impossible to have**:

- **`NodeLost`/`NodeBack` are ordinary messages into hub logic**, synthesized
  from heartbeat/staleness tracking on generated channels. The existing
  coverage discipline applies: **hub logic that never handles `NodeLost` is
  a compile error** (with an explainer suggesting the fail-safe idiom). You
  cannot write a fleet that pretends partition can't happen — the Cure move
  of "totality as product feature" applied to distributed systems.
- **Delivery semantics per stream kind:** `Signal` edges are
  **latest-value** (idempotent re-broadcast; a lost packet is healed by the
  next sample; no acks, no buffering — right for sensor data). `Event`/
  command edges are **acked sessions** with bounded retry (generated
  `protocol`); exhausting retries surfaces as `NodeLost` to the sender's
  logic. Both defaults overridable per edge (ledgered).
- **Fail-safe idiom:** actuator nodes own their scan state (rule 4), so a
  valve keeps enforcing its last-known rule through a partition, and the
  `NodeLost` clause states the degraded posture explicitly (`valve.water <-
  Closed`). The projected system is *more* robust than a real hub — there is
  no single node whose death stops everything — and the spec says so in the
  docs, because it is the payoff for handling `NodeLost` clauses.

## 7. Time

- `clock.now` and `elapsed`/`hold_for`/debounce guards are **node-local** —
  they project fine (each owner uses its own clock).
- **Comparing timestamps captured on different nodes is flagged** at
  projection (same philosophy as §5: no silent lies; wall clocks on two
  ESP32s are not comparable).
- An opt-in hybrid-logical-clock (HLC) mode for cross-node ordering is
  ledgered (§9), not in v1. The FRP causality indices already order events
  *within* each dataflow edge, which covers most real hub programs.

## 8. Transport & AtomVM reality

**No distributed Erlang on AtomVM** — dist is far too heavy for ESP32-class
targets, and the `Std.Http`/`:inets` dead-end is already proven. Projection
therefore rides Cure's own stack:

- Generated channels are `packet` layouts over pluggable transports:
  `espnow` (broker-less ESP32↔ESP32, the default for pure-ESP32 fleets),
  `udp(:lan)` (multicast/unicast on shared WiFi; works on generic-unix +
  Pico W), `mqtt(broker)` (when infrastructure exists / NAT traversal
  needed). Transport is declared once on the fleet; per-edge overrides
  ledgered.
- Heartbeats piggyback on data where rates allow; explicit tiny heartbeat
  packets otherwise (generated, invisible).
- A host node (RPi / laptop, generic-unix AtomVM or full BEAM) is just
  another `node` role — dashboards (`view`) live there; a mixed
  ESP32+host fleet is the flagship demo shape.

## 9. Tooling — the projection must be inspectable

- **`cure fleet report`** — prints the *projected* system: which computations
  landed on which node, every generated channel with its packet layout,
  expected message rates, and per-link bandwidth budget. The hub illusion is
  for writing, not for hiding: one command shows exactly what will happen on
  the air.
- **Whole-fleet host simulation** — `cure run --sim` runs *all* nodes as BEAM
  processes with a simulated transport supporting **loss/latency/partition
  injection**. Combined with `check`:

  ```cure
  check Greenhouse
    prop fail_safe_on_partition(cut: SubsetOf(sensor)) =
      sim(Greenhouse) |> partition(cut) |> settle(15s)
      |> always(fn(f) -> f.valve.water == Closed or f.reachable(sensor) != [])
  ```

  Chaos-testing your greenhouse on a laptop, with generated fault cases —
  before anything is flashed.
- OTA/rollout: per-node images from one program; **mixed-version fleets
  during rollout** are a real state — generated channels carry a fleet
  version, and cross-version compatibility rules are ledgered (§10).

## 10. What the dependent types do invisibly

- Node identity is `Fin(k)`; role streams are `Vector(k, Signal(..))` —
  "sensor 4 of 3" is a compile error, and `on NodeLost(sensor(i))` binds a
  bounded `i`.
- Every generated channel is session/packet-typed at both ends from one
  declaration — wire mismatches within a fleet version are inexpressible.
- Coverage checking forces `NodeLost` handling (§6): partition-blindness is
  a compile error.
- `merge` declarations (§5 option 2) carry algebraic obligations tested by
  `check` templates and, where arithmetic, provable by certificate elevation.
- Erasure keeps all of it off the wire and out of RAM: identities, indices,
  and session types cost zero bytes at runtime.

## 11. Open decisions (ledger)

1. **Dynamic membership** — v1 is static/declared. Join/leave beyond
   `NodeLost` (true elasticity) is a different problem class; revisit after
   real fleets exist.
2. **Consensus primitive** (§5 option 3) — ship v1 with options 1–2 only, or
   include a minimal arbiter-lease? If included: which algorithm, and is it
   viable on ESP32-class RAM?
3. **HLC opt-in** (§7) and its surface.
4. **Per-edge overrides** — delivery semantics (latest vs. acked), transport,
   rate limits. Rate/bandwidth budgets as a future cost-grade axis is the
   long-horizon hook.
5. **Mixed-version rollout rules** (§9) — strict lockstep vs. declared
   compatibility windows on generated channels.
6. **Merge-blessed combinator set** (§5 option 2) — initial CRDT library
   scope (counter, max/min, LWW-register, set-union?) and its `check`
   obligation templates.
7. **Projection of `reducer`s in hub logic** — a hub-level reducer is a
   stateful combinator (rule 4); its emissions may fan out to several nodes.
   Same ownership rules should apply; confirm no extra cases.
8. **Security** — fleet transport encryption/authentication (ESP-NOW keys,
   MQTT TLS), and whether the IFC `secret` axis should refuse to project a
   secret onto an unencrypted edge (a genuinely novel check — likely yes,
   eventually).

## 12. Non-goals

- Not a general dynamic cluster framework (no gossip membership, no
  auto-sharding) — fleets are small, declared, and hobbyist-scale (2–50
  nodes).
- Not a CRDT research library — a handful of blessed merges (§11.6).
- Not Raft-on-ESP32 in v1 (§11.2).
- Not hiding distribution — §9's report and §5's diagnostic exist precisely
  so the illusion stays a *writing* convenience, never an operational lie.
