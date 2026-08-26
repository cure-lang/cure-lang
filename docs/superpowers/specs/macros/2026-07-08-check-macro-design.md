# `check` — Property Testing Derived From Types

**Date:** 2026-07-08
**Status:** design (operator-requested). Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
(§7.5); built as a `macro` (§5) — zero compiler special-casing. Consumed
by every sibling macro that ships property templates (§6).

---

## 1. Purpose

`check` is Antigen's generator technology — the machinery that soundness-tests
Cure's own kernel — productized for end users. Pitch: **"your types write
your tests."** It pays off the invisible dependent types three ways at once:

1. **Generation for free** — a prop's typed parameters *are* its generators.
2. **Tests you don't have to run** — static discharge (`proved by construction`).
3. **Suites you didn't write** — macro-attached template props
   (*"your macros write your tests"*).

Per the hiding principles (parent §3, LAW): users write Bool-valued
properties; the macro manufactures generators, discharge attempts, and
counterexample explanations. No proof term, goal, or solver artifact is
ever surfaced. The trust story is worth telling: kernel and greenhouse are
tested by the same machinery.

## 2. Surface

A `check` block holds `prop` declarations (and plain `example` assertions,
§11). A prop's **arguments are ordinary typed parameters — the types ARE the
generators**, and refinements narrow them:

```cure
check Greenhouse
  ## Only generates temperatures below 30 — the refinement IS the generator.
  prop fan_off_when_cool(t: {c: Float | c < 30.0}) =
    Climate.step(t).fan == Off

check Semver
  prop roundtrip(v: Version) =
    parse(show(v)) == Ok(v)
```

(Temporal props over sequences: §7.) Prop bodies are Bool-valued —
load-bearing: Bool is decidable, which makes certificate elevation
constructive (§5) and the verdict vocabulary honest.

### The three-rung ladder

Every prop lands on exactly one rung per run, with fixed reporting vocabulary:

| Rung | Report line | Meaning |
|---|---|---|
| 1 | `proved by construction — <fact>; 0 runs` | static discharge: the prop is a theorem of the declarations |
| 2 | `proved (certificate — <fragment>, N steps kernel-checked)` | a solver certificate reconstructed into a Core term, kernel-checked |
| 3 | `tested (N runs)` | property testing, the honest floor |

Elevation is **monotone, best-effort, and never blocks a build**: any
failure at any stage — solver timeout, unimplemented reconstruction rule,
kernel rejection — silently demotes the prop a rung; solver flakiness can
fail an *elevation*, never a build. A rung-3 failure fails the suite the
ordinary way, with a counterexample.

## 3. Generator derivation rules

Derivation is total over the declarable surface — no "no generator for this
type" error exists:

- **Refinements narrow; they never filter.** `{x: Int | x > 0}` generates
  positives directly; `Bounded(3)` generates `0..2`. No generate-then-
  discard step, so no discard-ratio failure mode (QuickCheck's classic `==>`
  pain, solved by construction).
- **ADTs generate structurally, size-bounded** — the size bound reuses the
  recursion structure the totality checker already computed for the type.
- **Indexed/macro types generate valid inhabitants.** A `packet` generates
  *valid frames* (length fields consistent, CRC correct, `const` fields
  fixed); a `reducer`'s `Msg` generates message *sequences*; a `protocol`
  generates legal traces; fleet's `SubsetOf(role)` generates node subsets.
  A macro that manufactures a type registers its generator, via the same
  derivation interface the core rules use.
- **Solver-narrowed refinements** (predicates the constructive rules cannot
  invert) are the one open corner — ledgered (§10.1). The locked SMT boundary
  permits Z3 *model enumeration* as a generation strategy: every generated
  value is checked against the refinement before use, not trusted.

**Shrinking is type-aware and stays inside refinements** — a shrunk
counterexample still inhabits its parameter's type, so no shrink step is
wasted on inputs the property can't even receive; the reported minimum is
always a *legal* input (a classic QuickCheck pain, solved by construction).

Backend: Antigen's swappable StreamData-style generator backend, reused
directly; coverage-guided generation (the 2026-07-04 fuzzing design)
inherits as corpus-driven input search for hard branches. Known-label
discipline carries over: `prop` + expected verdict is exactly Antigen's
generator-is-the-oracle pattern.

## 4. The static-discharge pass — the signature move

Before running anything, `check` asks the type system whether each prop is
**already proved** — many properties a user instinctively writes are
theorems of the declarations. Mechanically: the prop body is elaborated
under its parameter types; if it normalizes to `true` by computation (delta
table, refinement subsumption, index arithmetic — the whnf-before-unify
machinery every DSL obligation uses), it is rung 1.

```
$ cure test
check Door
  ✓ roundtrip            (200 runs)
  ✓ retries_bounded      proved by construction — Opening.retries : Bounded(3); 0 runs
  ✗ no_reopen_while_open (74 runs, shrunk to 3 messages)
      msgs = [OpenPressed, MotorReachedOpen, OpenPressed]
      after step 3: OpenPressed from Open was rejected (no edge
      Open --OpenPressed--> …). Expected: door re-opens. Add the edge,
      or assert the rejection.
```

That middle line is the product moment: the dependent types surface exactly
once, as *tests you don't have to run*. The pass **reports** each discharge
with the discharging fact in user vocabulary — never a proof term (UX:
§10.2). A failed attempt costs and says nothing; the prop just runs.

## 5. Certificate elevation — solver-proved props, TCB delta zero

Between rungs 1 and 3 sits SMTCoq-style certificate reconstruction — the
designed-for "someday" in the locked SMT trust-boundary decision. The solver
stays out of the TCB; a *proof-producing* run is lifted into the kernel by
reconstruction. Pipeline, per prop, best-effort:

1. Negate the prop; hand it to a certificate-producing solver.
2. On UNSAT, take the certificate (Alethe/LFSC-class proof object).
3. An **untrusted reconstructor** (elaborator-side, like everything else)
   translates the certificate into an ordinary **Core proof term** — a chain
   of `Eq` lemmas, case splits, and arithmetic steps. Ground arithmetic
   discharges by *computation* via the K2 delta table, so certificates only
   bridge the symbolic steps.
4. The kernel checks that term exactly as it checks any term. The prop
   reports `proved (certificate — arithmetic, N steps kernel-checked)`.
5. **Any failure at any stage falls back to property testing**, reported
   honestly as `tested (N runs)`.

**TCB delta: zero.** The kernel never sees the solver or the certificate —
only a Core term. The alternative — a *trusted* certificate checker inside
the TCB (SMTCoq's verified checker minus the verification) — is **rejected**
by uniform strictness: the Isabelle-`smt`/SMTCoq family, not the Dafny/F*
trust-the-solver family, consistent with the locked boundary.

Cure is unusually well-positioned for reconstruction: `prop` bodies are
**Bool-valued, hence decidable** — the classical steps in an SMT resolution
proof reconstruct constructively (`¬¬b == b` holds for `Bool`), sidestepping
the classical/constructive gap that makes this hard in vanilla Coq. Ground
facts are free in-kernel (the delta table). Inductive `Eq` + K/UIP is the
exact term language derivations need. And refinement domains (bounded ints,
enums, bit-fields) sit inside QF_LIA/QF_BV, where solvers are complete
*and* certificates are well-understood.

**Honest boundary:** elevation covers the arithmetic/finite fragment —
thresholds, bounds, bit-field disjointness, enum case analysis; i.e. most
obligations from `board`/`driver`/`config`/units and many `reducer` guards.
It does **not** cover inductive properties: `parse(show(v)) == Ok(v)` needs
structural induction, which SMT does not produce. Those stay `tested`, or
are proved once at the library level (the `packet` round-trip) — never by
the user. The three-rung vocabulary stays truthful.

**Caching for CI:** the reconstructed Core term is a plain build artifact,
cached keyed by the prop and its dependency closure; CI **re-checks the
cached term without invoking the solver at all** — kernel replay is fast and
deterministic. The solver runs only on change (invalidation: §10.7).

## 6. Macro-shipped property templates

Macro authors ship properties alongside syntax — suites users never
wrote. Mechanism: a fourth `macro` section (after `syntax`, `expand`/
`elab`, `explain`):

```cure
macro Packet
  ...
  templates for $p:PacketDecl
    prop roundtrip(f: $(p.name)) =
      $(p.name).parse($(p.name).encode(f)) == Ok(f)
```

- **Attachment is per-declaration.** When the macro elaborates a user
  declaration, each `templates for` block matching its syntax category is
  instantiated with the declaration's quoted AST spliced in; the props join
  the suite in an auto-named block — `check Frame (packet templates)` —
  visibly distinct from hand-written props but treated identically.
- **Templates are ordinary props** riding the whole ladder — statically
  discharged, certificate-elevated, or tested; never special-cased.
- **Provenance is dual** — macro name + user declaration line — so a
  failing template explains itself against *the user's declaration* ("your
  `Frame.length` permits 255 but `payload` caps at 128"), per parent §4.
- **Central proof, local re-check.** Where the library proves a template's
  schema once (packet round-trip, parent §6.3), the per-declaration instance
  re-exercises the *generated code* — codegen is code, not types, and the
  template is its regression net.
- Opt-out (`skip roundtrip`) and parametrization ledgered (§10.3).

The shipped inventory across siblings (each named in its own spec):

| Macro | Templates |
|---|---|
| `packet`/`codec` | round-trip: `parse ∘ encode == Ok` on generated valid frames |
| `reducer` | graph conformance (only declared edges are ever taken; the catch-all rejects everything else); init-schema validity |
| `api` | every route parses its own generated requests; rejections carry the declared reject type |
| `driver` (spec §6) | reserved-bit safety (after any generated write against the mock, undeclared bits unchanged); init conformance (every `expect`/`wait_until` path reachable; wrong-chip/timeout paths return the declared errors); mode discipline (random legal call sequences never observe a governed field disagreeing with the typestate index) |
| `protocol` (spec §7) | conformance (random valid traces drive both endpoints in-process; each side accepts every legal message); fault injection (drop/duplicate/delay/corrupt frames in `--sim`; every run ends in a defined `SessionError` or completion — never a hang, never an out-of-protocol state) |
| `fleet` (spec §9) | partition chaos props (`sim |> partition(cut) |> settle(..) |> always(..)`); merge-combinator algebraic obligations |
| `config` | "no secret reaches a public sink" — a *static report* (rung 1 by construction: the IFC axis makes it a theorem or a compile error; the template exists so the guarantee appears where users look for it) |

## 7. Temporal properties

Props over generated *sequences* are bounded model checking, without ever
saying those words. Two combinators over a run trace:

```cure
prop faults_are_announced(msgs: List(Door.Msg)) =
  run(Door, msgs)
  |> always(fn(step) ->
       step.state == Fault implies step.emissions.contains(Faulted))
```

- `run(Reducer, msgs)` folds the reducer's `Signal.scan` body over the
  sequence, yielding the trace of `Step`s — pure, deterministic, clock-stubbed.
- `always(pred)` / `eventually(pred)` quantify over the trace. Bounded by
  construction: the generated sequence is finite, so both are decidable and
  the prop stays Bool-valued (ladder-eligible).
- Fleet's chaos shape composes the same way over the whole-fleet simulation
  (fleet spec §9): `sim(Greenhouse) |> partition(cut) |> settle(15s) |> always(..)`.

Temporal counterexamples report the shrunk *sequence* plus the first
violating step — §4's Door trace is the canonical shape.

## 8. Runner & tooling

- **`cure test`** runs every `check` block: static discharge, then elevation
  (or cached replay), then generation. Output as in §4 — one line per prop,
  exact rung vocabulary; failures show the shrunk counterexample + fix hint.
- **Seeds & reproducibility.** Every generated run derives from one printed
  seed. A failure prints `re-run: cure test --seed 8412 Door.no_reopen_while_open`;
  the pinned run regenerates the identical sequence (backend determinism is
  an Antigen invariant). CI records the seed.
- **Run counts.** Default 200 per tested prop; override globally
  (`--runs`), per block, or per prop. Rung-1/2 props default to 0 runs
  (token-run option: §10.6).
- **Sim integration.** Props may drive `cure run --sim`'s virtual hardware:
  GPIO/UART pin states are assertable trace values ("the relay never
  switches faster than 1Hz" against the simulated clock), driver mocks
  serve register-level templates, and the simulated transport's loss/
  latency/partition injection serves protocol/fleet fault templates. The
  clock is virtual — time-indexed props run at CPU speed.
- **CI certificate replay.** CI re-checks cached Core terms through the
  kernel with no solver installed; a cache miss demotes to `tested` for that
  run, re-elevating when a solver is available. Rung movement is reported,
  never an error.
- **Explainers.** `check` registers explainers (parent §4) like any macro;
  its distinctive output is the **counterexample explanation** — shrunk,
  minimal, in the vocabulary of the macro that owns the failing value
  (reducer: states, messages, missing edges; packet: fields, offsets;
  fleet: nodes, partitions). Declaration provenance lets it say "add the
  edge, or assert the rejection" instead of dumping a term. Raw generator
  output reaching a user is a defect, same rule as raw kernel errors.
- On-device property runs over the serial harness: deferred (§10.8).

## 9. Relations

- **Antigen** — upstream engine: generators, shrinking, known-label
  discipline, corpus/coverage loop (incl. the 2026-07-04 fuzzing design,
  §3); `check` is the productization.
- **`packet`/`codec`, `reducer`, `api`, `driver`, `protocol`, `fleet`,
  `config`** — template suppliers and generator registrars (§6).
- **SMT lint (2026-07-03) & the locked trust boundary** — Z3 remains the
  always-present *lint* solver; certificates may come from a different
  solver (§10.4); nothing widens the TCB.
- **Final-Core / kernel** — sole checker of reconstructed terms; no
  `check`-specific kernel machinery exists or may be added.

## 10. Open decisions (ledger — seeded from parent §9 items 17–18, expanded)

1. **Generator strategy for solver-narrowed refinements** — constructive
   sampling vs. bounded rejection vs. Z3 model enumeration (permitted:
   generated values are checked, not trusted — the boundary constrains
   *proof*, not *search*). Likely tiered: constructive where invertible,
   enumeration fallback; rejection never (no-discard).
2. **Static-discharge report vs. skip** — always-report is the default (the
   product moment); decide `--quiet` collapse and CI-summary treatment.
3. **Template attachment interface** — exact `templates for $x:Category`
   binding rules, opt-out surface (`skip <name>`), per-template
   parametrization, naming under multi-macro attachment.
4. **Certificate solver choice** — Z3's proof format is under-specified;
   cvc5/veriT emit Alethe. Z3 stays the lint solver per the locked decision
   while another solver certifies; pick the default; absence: warn vs. silent.
5. **Reconstruction rule coverage order** — resolution + CNF +
   `la_generic`/Farkas first (QF_LIA cores), bit-vectors next, quantifier
   instantiation later; unimplemented rule ⇒ demotion, so coverage grows
   release by release without breaking anyone.
6. **Token sanity runs for elevated props** — K cases on rung-1/2 props
   (belt-and-braces against reconstructor/discharge bugs) vs. honest 0
   runs; leaning token runs locally, 0 in CI replay, verdict unchanged.
7. **Certificate cache invalidation** — dependency-closure hash granularity
   (function vs. module), cache location, committed vs. ephemeral.
8. **On-device property runs** — over the serial harness on real hardware
   (observable-verification rule). Deferred; sim covers semantics, hardware
   covers timing/electrical reality.

## 11. Non-goals

- **Not a replacement for example-based tests.** Plain assertions coexist —
  `example closed_stays_closed = run(Door, [MotorTimeout]).state == Closed`
  — run once, no generation, reported alongside props.
- **No mutation testing** — a different product; nothing here precludes it.
- **No fuzzing of arbitrary FFI** — `@extern` boundaries are opaque to
  generation; props stop at typed Cure surfaces (mocks stand in for silicon).
- **No proof-authoring surface, ever** — a property that would need a user
  proof gets a library lemma or an honest `tested (N runs)`, never a goal.
- **No trusted solver, no trusted certificate checker** — rung 2 exists only
  via kernel-checked Core terms (§5); this is locked, not open.
