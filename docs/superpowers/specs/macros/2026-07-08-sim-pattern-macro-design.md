# `sim` & `pattern` — Play & Learning Macros (+ Games Scoping Note)

**Date:** 2026-07-08
**Status:** design. Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
(§7.6); built as `macro`s (§5), zero compiler special-casing. The four
hiding principles (§3) are law: no user ever sees an index or a kernel error.

---

## 1. Purpose

These are the joy-magnets — macros for the demographic that made Arduino
big, before they own hardware at all. `sim` turns the BEAM's actual superpower
(100k+ lightweight processes on a laptop) into agent-based modeling; `pattern`
turns its *proven* live-music pedigree (Sonic Pi's timing core is famously
Erlang) into live-coded music with hot code push. Both pay off Cure's
foundations in beginner currency: **simulations that reproduce exactly** and
**patterns that provably cannot hang the beat**.

## 2. `sim` — agent-based modeling

### 2.1 Surface

Worked example: an SIR epidemic (picked over boids — more teachable, and the
S/I/R states map onto an ADT beautifully):

```cure
type Health =
  Susceptible
  | Infected(days: Nat)
  | Recovered

sim Epidemic
  space grid(100, 100)                 # library space; macro is space-agnostic
  seed 42                              # same seed ⇒ same run, exactly
  clock every 50ms                     # one tick = one simulated day

  agents person(2000)                  # identity is Fin(2000), like fleet nodes
    state health: Health = Susceptible

    rule infect (self, nbhd, rng) ->
      match self.health
        Susceptible when nbhd.count(is_infected) > 0
                    and rng.chance(0.3)   -> self with { health: Infected(0) }
        Infected(d) when d >= 14          -> self with { health: Recovered }
        Infected(d)                       -> self with { health: Infected(d + 1) }
        _                                 -> self

  observe s = agents.person.count(fn(p) -> p.health == Susceptible) every tick
  observe i = agents.person.count(is_infected) every tick
  observe r = agents.person.count(fn(p) -> p.health == Recovered) every tick
```

Surface rules:

- **`agents role(n)`** declares a population; each agent is an `actor` under
  the hood (GenServer-backed, exhaustiveness-checked `on_message`); identity
  is `Fin(n)` — the same landed `Bounded` machinery as fleet node identity,
  so "person 2001 of 2000" is a compile error nobody sees as a type.
- **`rule`** clauses run in declaration order each tick; each is a **pure
  function of `(self, nbhd, rng)`** — own state, neighborhood *snapshot*,
  per-agent PRNG. That signature is the whole determinism contract (§2.2);
  the macro makes anything else inexpressible (correct-by-construction).
- **`space`** is a library value, not macro syntax. v1 ships the two
  classics: `grid(w, h)` (cellular automata, epidemics) and `plane(w, h)`
  (continuous 2D — flocking, `nbhd.within(radius)`). A space is anything with
  the snapshot/neighborhood interface; graphs/3D come later (§8.1).
- **`observe name = expr every tick`** declares an observation stream — a
  `Signal` of per-tick aggregates feeding charts, `view` dashboards, and
  `check` props. **`clock`** is itself a `Signal` of ticks (parent §7.6)
  driving rounds.

### 2.2 Determinism — the flagship feature

**Same seed, same simulation, exactly.** This needs an honest mechanism —
BEAM message ordering between actors is *not* deterministic, so 2000
free-running actors would make every run unique. The mechanism is **lockstep
rounds**: each tick, (1) the runtime snapshots the world; (2) every agent
computes its next state as a pure function of `(own state, snapshot, own
PRNG)` — no live reads, the rule signature makes them inexpressible; (3)
results **commit synchronously** at the tick boundary, space conflicts
resolved by deterministic order (agent identity `Fin(n)` is the tiebreak).

Purity pays twice, the same dividend as fleet's replication rule ("pure
derivations replicate for free"): because steps are pure over a snapshot,
**parallelism is safe** (schedulers may run the 2000 steps on all cores in
any order — results cannot differ) **and determinism is real** (the round
structure, not scheduler luck, defines the semantics). Randomness: one root
`seed` splits into per-agent PRNG streams (keyed by identity), threaded
explicitly as `rng` — no global random state. Reproducibility is what makes
`check` over simulations meaningful (§6): a property about run 42 is a
property about *the* run 42.

### 2.3 Speed modes

Same semantics, three tick sources: **real-time** (wall-clock ticks — watch
it live), **fast-forward** (ticks fire as fast as commits complete — for
experiments and `check`; a 10,000-tick epidemic in seconds), and
**single-step** (ticks on keypress/REPL command — the debugger and the
classroom mode; observations still fire per tick, so dashboards step along).

## 3. `pattern` — live-coded music

### 3.1 Surface

TidalCycles/Sonic Pi register: patterns are cyclic sequences with time
structure, built from mini-notation plus combinators.

```cure
use Play.Pattern

pattern kick  = beat "x _ _ x _ _ x _"
pattern hats  = beat "_ x _ x _ x _ x" |> fast 2
pattern bass  = notes "c2 _ eb2 g1" |> every 4 rev

live Set
  tempo 120bpm
  out osc("localhost", 57120)          # SuperCollider / any OSC synth
  play stack(kick, hats, bass)
```

- **Mini-notation** (`beat`/`notes`): one cycle per string; `x`/note names
  are events, `_` rests; subdivision/groups follow the Tidal lineage. The
  grammar is finalized via the `parse` macro (§8.4) — pleasing dogfood:
  the music notation is itself a Cure grammar.
- **Combinators**: `fast n`, `slow n`, `rev`, `every n f`, `stack(..)`,
  `cat(..)` — pure pattern → pattern functions; a pattern is a value.
- **`tempo`** declares the clock the runtime schedules against — the timing
  discipline the BEAM is proven for: Sonic Pi's own timing core is Erlang,
  and this design is deliberately the same shape.

### 3.2 Hot-swap — the REPL dependency

`pattern`'s hard dependency is the toolchain REPL / hot code push (parent
§2.5). Live coding *is* redefinition mid-performance: edit `bass`, push, and
the runtime swaps the pattern **at the next cycle boundary** — never mid-note,
no glitch. The tempo clock runs through the swap; a push that fails to compile
changes nothing (the old pattern plays on). The music never stops — the demo
that ends arguments about hot code push.

### 3.3 Totality and time indices

A pattern is total Cure — size-change termination covers every combinator and
user function mapped over a pattern. Product translation: **a pattern cannot
run away or hang the audio thread**; an infinite loop in a transform is a
compile error, not a dropped beat at the gig.

Combinators are also cycle-length-aware: each pattern's cycle length is an
invisible index, so `stack` over mismatched lengths is *detected*. Mismatch
is ambiguous, though — 3-against-4 polymeter is legitimate music; a 7-step
hat line meant to be 8 is a typo. So: **warn, not error**, silenced by
declaring intent (`polymeter` is an identity annotation whose only job is
recording that the drift is deliberate):

```
warn[P021]: stacking a 3-step pattern with a 4-step pattern
  --> set.cure:8
  These drift against each other (realign every 12 steps). If that's the
  groove you want, say so:  stack(kick, hats) |> polymeter
```

### 3.4 Audio output — not in the BEAM

**No in-BEAM synthesis.** v1 output is **OSC to an external synth**
(SuperCollider first; any OSC synth works) — exactly Sonic Pi's architecture:
Erlang does the timing, a dedicated synth does the DSP. MIDI out is ledgered
(§8.6). **On-device crossover:** the pattern algebra is output-agnostic, and
an event stream on a tempo clock is exactly what GPIO wants — buzzers, relays,
and LED strips on an ESP32 (`out gpio(pin.gpio5)`, `out ledstrip(..)`) are
supported targets of the *same* patterns. Write a light show on the laptop,
flash it to the tree.

## 4. Games — a scoping note, not a macro

`reducer` (update) + `view` (render) + `on` (input) **already is the game
loop** — the Elm architecture at 30fps. Terminal snake is a `reducer` over
`%[snake, food, score]`, an `on keypress` feeding it, a `view` drawing the
grid. **Decision: games ship as tutorials plus a tiny `terminal_view` helper
library, NOT as a macro.** The parent's bar for a macro is new declaration
semantics that manufacture types (§3, §5); a game introduces none, so a `game`
keyword would be branding, not machinery. The tutorials are the point: grid
games exercise the whole reducer/view/flow stack with zero hardware, and
"impossible UI states are unrepresentable" demos vividly when the game-over
screen literally cannot render mid-play.

## 5. Explainers

Per the parent's error-explainer architecture (§4), representative targets
(plus the polymeter warn, §3.3). Raw kernel vocabulary reaching a `sim` or
`pattern` user is a defect by definition.

```
error[S014]: rule `infect` reads live agent state
  --> epidemic.cure:19
  Agents may only read the neighborhood snapshot (`nbhd`) — reading another
  agent's live state would make runs irreproducible (results would depend on
  which agent stepped first). Use nbhd.count(..) / nbhd.states(..) instead.

error[P010]: mini-notation: unexpected token
  --> set.cure:3
   |
 3 |  pattern kick = beat "x _ _ x ! _ x _"
   |                              ^
  `!` is not a step. Steps are `x` (hit), `_` (rest), or a [group].
```

## 6. `check` integration

Determinism (§2.2) is what makes props over simulations meaningful — runs
reproduce, so a property about a seed is a property about *that* run.

```cure
check Epidemic
  ## Macro-shipped reproducibility template — every sim inherits it.
  prop reproducible(seed: Nat) =
    run(Epidemic, seed, ticks: 100).observations
      == run(Epidemic, seed, ticks: 100).observations

  ## Conservation — the SIR classic.
  prop population_conserved(seed: Nat, t: Bounded(365)) =
    let obs = run(Epidemic, seed, ticks: t).at(t)
    obs.s + obs.i + obs.r == 2000
```

(Static discharge may report conservation *proved by construction* — `Health`
is a closed ADT over a fixed `Fin(2000)` population, so the partition is a
theorem of the declarations.) `pattern` ships algebra laws as templates —
cute and real; generated patterns come from the mini-notation grammar (a
`parse` grammar is a generator read backwards):

```cure
check PatternLaws
  prop rev_involutive(p: Pattern) = rev(rev(p)) == p
  prop fast_slow_id(p: Pattern)   = fast 2 (slow 2 p) == p
```

## 7. Relations

- **`actor`/`fsm`** — every sim agent is an actor; the lockstep round is a
  barrier over the population. Nothing new at runtime.
- **`flow`** — observation streams *are* `Signal`s; sim clock and tempo
  clock live on the Flow runtime. Both macros are Flow citizens.
- **`view`/dataviz** — `observe` streams plug straight into `view` charts
  (the live-drawing S/I/R curves are the classroom moment).
- **`check`** (parent §7.5) — §6; sim reproducibility is the enabling
  decision, made here, consumed there.
- **`fleet`** — a genuinely useful bridge: a `sim` prototypes a fleet's logic
  before hardware exists (node roles as agent roles, hub logic on simulated
  sensors), then the same Flow code moves into a `fleet` block.
- **Toolchain REPL** (parent §2.5) — `pattern`'s hard dependency (§3.2);
  `sim` single-step rides it too. If §2.5 slips, `pattern` slips.

## 8. Open decisions (ledger)

1. **Space library scope** — v1 is `grid` + `plane`; graphs (social-network
   epidemics), toroidal wrap, 3D. Interface fixed; shipped set is not.
2. **Observation sampling vs. memory** — `every tick` on a 10⁶-tick run is a
   lot of points; default downsampling/windowing and retention policy.
3. **Sim distribution across cores** — lockstep purity makes BEAM-scheduler
   parallelism nearly free (§2.2); confirm the commit-barrier design (one
   process per agent vs. batched chunks per scheduler at 100k+).
4. **Mini-notation grammar finalization** — via the `parse` macro; pick the
   Tidal-subset v1 (`[..]` groups, `*n`, `?` chance) and freeze it.
5. **OSC schema / synth presets** — SuperCollider event schema (SonicPi- or
   SuperDirt-compatible for Tidal refugees?) and a preset bank so `play kick`
   makes a sound in minute one.
6. **MIDI out** — hardware-synth users will ask immediately; host-side only?
7. **Latency compensation** — schedule-ahead with per-output offsets (OSC
   bundle timestamps do the work; GPIO needs its own budget).
8. **Classroom packaging** — a `cure learn` bundle (sim + pattern + game
   tutorials + dashboard, one install)? Decide the bundle boundary here.

## 9. Non-goals

- **No physics engine** — spaces provide neighborhoods, not collision
  dynamics; physics is a library on the space interface.
- **No 3D rendering** — dashboards are charts and grids.
- **No DAW ambitions** — `pattern` is live-coding, not arrangement or mixing.
- **No in-BEAM audio synthesis** — timing in the BEAM, DSP in the synth
  (§3.4); the Sonic Pi split is the proven architecture, and we keep it.
