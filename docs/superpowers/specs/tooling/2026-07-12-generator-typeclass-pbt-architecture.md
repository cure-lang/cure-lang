# Property-Based Testing — `Generator` Typeclass + Engine Architecture

> **STATUS: DESIGN, phased. Not scheduled as an autopilot SP yet.** Recorded 2026-07-12
> from an operator design session during the macro-facility build. Decides the
> architecture for (a) user-facing property testing and (b) SP3's generative
> expansion proof, which turn out to share one core. **Operator decision: build the
> "middle path" now; re-base it on a ported Hypothesis *conjecture* model later.**
> This document is the durable record of that decision and its rationale.

## 1. The one-sentence decision

**Ship a `Generator(a)` typeclass (stdlib conformance + `deriving`) as the single source
of "how to generate an `a`," shared by user property tests and by SP3's macro fuzzer;
keep the *engine* (drive-loop + shrinking + example database) separate from that *domain*
layer (Hegel's lesson), using our existing host engine (Antigen) for the compile-time
fuzzer and `Std.Test` at runtime for users. Later, port Hypothesis's choice-sequence
"conjecture" model underneath so shrinking becomes internal and free for every conforming
type, and re-base both runners on it.**

## 2. Why this shape (the three inputs that produced it)

Three operator observations, in order, converged here:
1. *"Use Cure's inbuilt gen/test"* — Cure already has `lib/std/gen.cure` (QuickCheck-style
   generators with explicit shrinkers) + `lib/std/test.cure` (a `forall` property runner).
   So the user-facing surface exists; we build on it, not from zero.
2. *"Hypothesis-style / Hegel-style from the start"* — Hegel ([hegel.dev](https://hegel.dev/explanation/why-hegel))
   is Hypothesis's engine centralized behind a protocol with thin per-language clients; its
   thesis is **don't reimplement the PBT engine per context — centralize it.** Applied here:
   don't rebuild a conjecture engine in three places; have one engine, thin domain clients.
3. *"All stdlib types should have a generator typeclass conformance"* — the ergonomic core:
   `forall(fn(x: MyType) -> Bool = …)` with the generator resolved by the typeclass, no
   hand-written generator at the call site (QuickCheck's `Arbitrary` / Hypothesis `from_type`).

## 3. Two audiences at two phases — the distinction that keeps "user magic" safe

The critical clarification (operator asked "if we use Antigen do we give up any of this?"):
**no — because user PBT never runs on Antigen.** There are two runners for two audiences:

| | Runs when | Runs where | Runner | Tests |
|---|---|---|---|---|
| **User PBT** | runtime | BEAM / AtomVM | `Std.Test.forall` (Cure) | the user's own code |
| **SP3 macro fuzzer** | compile time | host | Antigen (Elixir) | that macro expansions type-check |

The user only ever touches the top row. Whatever SP3 uses for its runner is invisible to
them. So **the full magic — `Generator` typeclass, `deriving`, `forall` on any type,
(eventually) free shrinking — lives in the `Std.Gen`/`Std.Test` layer and is delivered to
users regardless of the SP3 engine choice.** Choosing Antigen for SP3 costs the user nothing.

What choosing Antigen *would* cost, if done naively, is **internal unification**: if SP3 used
Antigen's *own* Elixir term generators, there'd be two generator systems (the user's Cure
`Generator` instances + Antigen's Elixir generators). The **middle path avoids that** — see §5.

## 4. The `Generator(a)` typeclass (the domain layer — user-facing)

```
interface Generator(a)
  generate : Gen(a)          # a plan for producing an `a` from the draw source
```

- **Base instances** for the stdlib: `Int`, `Float`, `Bool`, `Atom`, `Char`, `String`
  (= `List(Char)`), `List(a)`, `Maybe(a)`, `Result(a, e)`, `Tuple(…)`, `Map(k, v)`,
  `Set(a)`, `Vector(n, a)`.
- **`deriving`** for user ADTs/records — the multiplier that makes "all types" real:
  a **sum** type generates by drawing a constructor then generating its fields; a **product**
  generates each field. A user writes `type Foo = … deriving Generator` (or it derives by
  coherence) and `forall` on `Foo` just works, zero boilerplate.
- **Dependent / indexed types take the index** — this is where Cure beats QuickCheck:
  `Generator(Vector(n, a))` draws exactly `n` elements; `Generator(Fin(n))` draws in-range;
  `Generator(Bounded(k))` respects the bound. Generators produce *exactly well-typed
  inhabitants by construction*, because the types carry the index. Worth leaning into as a
  differentiator.
- The **hard instance** is `Code`/`Block` (an arbitrary well-typed expression) — this needs
  the reflection API (SP4) to build a term of a required type. It is the same "generate an
  expression of type T" whether a user or SP3 needs it — so it is written once, as a
  `Generator` instance, not bespoke fuzzer code.

## 5. The middle path (Hegel pattern) — engine ⟂ domain

Separate the **engine** (drives generate → run property → shrink; owns the choice source
and the example database) from the **domain** (the `Generator` instances + the properties):

- **Domain = the one Cure `Generator` typeclass** (§4). Authored/derived in Cure. Shared.
- **Engine = phase-appropriate runner:**
  - user PBT → `Std.Test` on the BEAM (runtime);
  - SP3 macro fuzzer → **Antigen** on the host (compile time), invoking the *same* Cure
    `Generator` instances to fill typed holes, then checking each expansion elaborates.

So SP3's "type-directed hole generation" becomes literally *"resolve `Generator(Duration)`
for a `<t: Duration>` hole"* — the user's typeclass, not a second system. One source of
generators, two runners by phase. That is the Hegel insight (one engine role, thin domain
client) applied to *our* existing engine instead of an external Python server — which we
explicitly reject (a Cure compiler must not depend on a running Python Hypothesis process to
compile a macro; it breaks the self-contained BEAM/AtomVM toolchain and deterministic builds).

**Enabler / sequencing:** SP3 invoking Cure `Generator` instances at compile time rests on
**Tier-3 staged-host Cure execution (SP2)** + **the reflection API (SP4)** — which are
*already* SP3's prerequisites in the program graph. So the middle path lands naturally at SP3,
resting on SP2 + SP4; no reordering.

## 6. Phase 1 (now) vs Phase 2 (later — the "ported conjecture")

- **Phase 1 — build the middle path on what exists.** `Generator` typeclass + stdlib
  instances + `deriving`, over `Std.Gen`'s *current* generation model (QuickCheck-style,
  explicit shrinkers where shrinking is needed). `Std.Test.forall` for users; Antigen +
  the Cure `Generator` instances for SP3. Fully magical for users *today* (auto-resolved
  generators); shrinking is the older explicit-shrinker style.
- **Phase 2 — port Hypothesis's conjecture / choice-sequence model** underneath. Generators
  draw from an underlying **choice sequence** (a random int/byte stream); every value is a
  function of that stream; **shrinking operates on the stream**, so it is **internal,
  composable, and free for every conforming type** — including `deriving`d user types — with
  no per-generator shrinker. Add the **example database** (persist + replay failing draws)
  — which unifies with Antigen's existing `corpus.sexp`/`seeds.sexp` replay store. Then
  **re-base both runners** (`Std.Test` and the SP3 engine) on the conjecture core. The
  `Generator` typeclass *interface* (§4) is designed to survive this re-base unchanged — only
  the `Gen(a)` implementation swaps from explicit-shrinker to choice-sequence — so user code
  and derived instances do not churn.

The phasing is deliberate: get the ergonomic typeclass + `deriving` shipping and driving SP3
now; invest in the (hard, high-value) conjecture engine once the surface is proven and stable.

## 7. Open questions to verify before the Phase-1 foundation slice

- **Antigen's current shrinking model** — conjecture/internal, or explicit shrinkers? Sets
  how much of Phase 2's engine is genuinely new vs already present on the host side.
- **Can the host engine invoke a Cure `Generator` instance at compile time?** The load-bearing
  assumption for the middle path's "one generator system." Likely via Tier-3 staged execution
  (SP2). If not feasible, Phase 1 falls back to Antigen's own generators for SP3 (two systems,
  temporary) with the unification deferred to Phase 2 — user magic unaffected either way.
- **How much of `deriving` is actually built** for typeclasses today (the design approved it;
  implementation status unconfirmed). Determines whether "all stdlib + user types conform"
  needs the deriving machinery built first.
- **`Gen(a)` representation** that survives the Phase-1 → Phase-2 re-base (an opaque strategy
  type, so swapping explicit-shrinker → choice-sequence doesn't change the typeclass surface).

## 8. Relationship to the macro-facility program

- Feeds **SP3** (generative expansion proof) directly: SP3 = "resolve `Generator` per hole
  category, run through the engine, assert each expansion elaborates" — most of SP3 becomes
  typeclass resolution rather than bespoke fuzzing.
- Depends on **SP2** (Tier-3, to run Cure generators at compile time) and **SP4** (reflection,
  for the `Code`/expression `Generator` instance) — SP3's existing prerequisites.
- The **Phase-1 `Generator`-typeclass foundation slice** is a candidate to build alongside/just
  before SP3 (it is also independently useful to users the moment it lands). TCB delta ZERO
  (stdlib + typeclass + test tooling; no `lib/cure/core/*`).

## 9. What the user is guaranteed, in every phase

`forall(fn(x: AnyType) -> Bool = …)` works with the generator auto-resolved; user types
conform by `deriving`; property tests run in Cure on the BEAM. Phase 1 gives that with
older-style shrinking; Phase 2 makes shrinking internal and free. **No phase, and no engine
choice for SP3, removes any of that from the user.**
