# Effects as Data — the Agda-Purist Pathway (Evaluated Alternative)

**Date:** 2026-07-09
**Status:** evaluated alternative — **not chosen**. The operator selected the
inert `Effect` type former
([`2026-07-09-effect-type-former-design.md`](2026-07-09-effect-type-former-design.md)).
This spec exists so the rejection is conscious, the trade-offs are recorded
with numbers, and the staging design (§5) — which is independently valuable
and partially reusable — is not lost.

---

## 1. The idea

Zero kernel change. Effects are an **ordinary inductive family** in Core —
a free monad over a trusted operation signature (ctor shapes illustrative):

```cure
type EffectM(A: Type)
  = Pure(A)
  | Send(Pid, Msg, Unit -> EffectM(A))          # continuation-passing ctors
  | SelfPid(Pid -> EffectM(A))
  | Sleep(Int, Unit -> EffectM(A))
  | Extern(Atom, Atom, List(Dyn), Dyn -> EffectM(A))
```

A handler *returns a description*: a pure tree of effect constructors. The
tree is interpreted by a trusted runtime module:

```elixir
# Cure.Effect.Runtime — the ONLY place effects happen (trusted, ~50 lines)
def run({:Pure, a}), do: a
def run({:Send, pid, msg, k}), do: (send(pid, msg); run(k.(:unit)))
def run({:Sleep, ms, k}),      do: (:timer.sleep(ms); run(k.(:unit)))
...
```

This is the literal generalization of the Safe-FRP architecture already
landed in this repo: `SF` is a pure indexed GADT describing a signal
network; a trusted runtime executes it. `EffectM` does the same for OTP
effects.

## 2. What it buys (the honest pro column)

1. **TCB delta: zero kernel lines.** `EffectM` is just an inductive; the
   kernel already checks inductives. The trusted addition is the ~50-line
   runtime interpreter (and, with staging, part of Emit — see §5.4, this
   claim degrades).
2. **Effects are provable data.** "This handler sends exactly one message,"
   "no `Send` after `Stop`," session-protocol conformance as an index on
   `EffectM` — all *ordinary theorems about ordinary data*, provable with
   the existing kernel today. The inert-`Effect` design cannot state these
   (its ops are opaque; that's the point of inertness).
3. **Testing without mocks.** A handler is pure: call it, pattern-match the
   tree, assert. No process spawning in unit tests.
4. **Duplication/discard hazards vanish rather than being fenced.**
   Duplicating a *description* is copying a tuple; only `run/1` performs.
   Every §5 door in the sibling spec (surface substitution, NbE readback,
   erasure) is simply not a hazard here — descriptions are values.

## 3. What it costs

1. **Ergonomics.** Handler code becomes CPS constructor chains, or needs
   monadic sugar that elaborates to them — and then *every* effectful line
   of Cure is written against a DSL rather than being ordinary code. Given
   the operator's "ergonomics trumps purity," this is the headline objection.
2. **Naive performance** (§4): interpretation overhead per effect op, felt
   most on AtomVM.
3. **First-order restriction pressure.** Continuations inside ctors are
   functions — fine — but proving things about trees containing closures
   runs into function extensionality immediately; the provability payoff
   (§2.2) is strongest for the fragment with first-order/defunctionalized
   continuations, which is another representation decision to carry.

## 4. Naive performance estimate (no staging)

Per effect operation executed at runtime:

| cost | naive `EffectM` | inert `Effect` / today's bespoke code |
|---|---|---|
| description ctor (tagged tuple) alloc | 1 | 0 |
| continuation closure alloc | 1 | 0 |
| interpreter dispatch (case on tag) + tail call | 1 | 0 |
| the effect itself (e.g. `erlang:send/2`) | 1 | 1 |

So roughly **3 allocations + 1 dispatch of pure overhead per op**, plus the
handler builds its whole tree before anything runs (peak-heap ∝ ops per
handler invocation). Estimates, not benchmarks:

- **Effect-dense handlers** (message routing, a send or two and little
  compute — the fsm/actor norm): **~3–10× slower per handler invocation**
  than direct calls. The work *is* the effects, so overhead dominates.
- **Compute-heavy handlers**: overhead amortizes toward noise (<10%).
- **AtomVM/ESP32 multiplier**: small per-process heaps make the closure/
  tuple churn disproportionately expensive — more frequent GC pauses in
  exactly the latency-sensitive message path. The naive form is plausibly
  unacceptable on-device even where it is tolerable on generic-unix.

## 5. Staging — recovering the overhead (first Futamura projection)

The key observation: **the kernel's own NbE is already the staging engine.**
Unlike the sibling spec's inert ops, `EffectM` constructors are *transparent*
to `Normalise.nf` — they're ordinary ctors, and `Eval` reduces ctor trees,
β-redexes, and δ-certified globals eagerly. So at emit time:

### 5.1 The mechanism

For each handler body `h : ... -> EffectM(R)`:

1. **Normalize:** `nf(body)` under the def's Core env. Every statically-
   determined part of the tree computes out: binds collapse, helper calls
   δ-unfold (where totality-certified — the existing M7 gate), the result is
   a literal constructor tree whose leaves are runtime expressions
   (neutrals on the handler's parameters).
2. **Compile the tree, don't ship it:** a new Emit pass walks the normal
   form and emits direct code —
   - `Pure(a)` → `<emit a>`
   - `Send(p, m, k)` → `erlang:send(<emit p>, <emit m>), <emit (k unit)>`
     (the continuation is applied *at compile time* — another nf step — and
     its body compiled inline)
   - a **stuck `case`** (tree shape depends on a runtime value) → an Erlang
     `case` with each arm staged recursively
   - a **neutral `EffectM` value** (genuinely dynamic: a first-class tree
     received as an argument, or built by recursion over runtime data) →
     residual call `'Cure.Effect.Runtime':run(<emit tree>)`.

This is precisely specializing the interpreter to a static program — the
first Futamura projection — with NbE doing the specialization and neutrals
marking exactly the residual (dynamic) boundary. No new partial-evaluation
machinery: `nf` already goes under binders (`nf_struct`'s closure clauses)
and already leaves runtime-dependent structure as readable neutrals.

### 5.2 What stages fully, what residualizes

| handler shape | staged result |
|---|---|
| straight-line effects, statically-shaped branches on runtime data | **identical code to the inert-`Effect` design — 0% overhead** |
| effect structure folded over a *runtime* list (e.g. broadcast to a runtime pid list) | residualizes to a recursive function; if the fold *body* is static (it always is in practice), the loop compiles with the effect inline — overhead ≈ one tail-call per element, ~0% |
| first-class `EffectM` values passed around as data | interpreter fallback for those values only (~the naive cost, locally) |

Real fsm/actor handlers are overwhelmingly the first row. Post-staging,
this design and the inert-`Effect` design emit essentially the same BEAM
code for the entire motivating workload.

### 5.3 Staging synergy and preconditions

- **δ-certification is the staging throttle**: a helper the handler calls
  stages through only if totality-certified (else it's a neutral global and
  residualizes as a call — still fine, just a call boundary). The existing
  M7 gate thus directly controls staging power; no new analysis.
- Compile time rises: every handler body is fully normalized at emit. For
  handler-sized terms this is milliseconds; it is not a scaling worry until
  someone writes a 10k-op handler, at which point the residual-call boundary
  (don't δ-unfold) is the natural knob.

### 5.4 The catch — where the trust went

Staged emit is a **compile-time effect interpreter**: the pass that turns
`Send(p, m, k)` into `send(P, M), …` is now responsible for effect *ordering
and multiplicity* — exactly the property the sibling spec locates in a
4-rule direct-style lowering. The "zero kernel lines" claim (§2.1) survives,
but the *trusted-code* claim doesn't: trusted-emit grows by a tree-walking
compiler that is strictly more code, with more cases (stuck-case staging,
continuation application, residual boundaries), than the inert design's
bind-chain lowering. The TCB doesn't shrink; it relocates and grows.

## 6. Why this lost (decision rationale)

1. **Ergonomics** — the operator's stated priority. Ordinary effectful code
   beats a description DSL, even sugared.
2. **Trusted-surface accounting** (§5.4): after staging — which the AtomVM
   target makes mandatory, per §4 — this path carries *more* trusted code
   than the inert design, inverting its headline advantage.
3. **The provability payoff is recoverable later**: reflecting a fragment of
   the op algebra into an inductive *on top of* the inert design (sibling
   spec ledger #6) buys the theorems where wanted, without making every
   handler pay the representation.
4. Performance ties only after building the staging pass; the inert design
   is at 0% overhead with no staging pass at all.

## 7. Conditions to revisit

- Kernel-inertness turns out buggy or unmaintainable in practice (Antigen
  finds inertness violations that keep recurring structurally).
- Proof-carrying effect protocols (session types as theorems about handler
  trees) become a headline feature rather than a nice-to-have.
- A verified-compilation push: staged-emit-from-normal-forms is the shape a
  certified emitter would want, and §5 is the design to resurrect.
