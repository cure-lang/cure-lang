# Antigen `ChoiceSeq` backend — design (reference / backlog)

**Status:** REFERENCE ONLY — not scheduled. Captured now so the design exists when
we need it. Gated behind a decision (see §9): build this only if the cheaper
value-level post-shrink (bundled with the ill-typed mutation corpus) proves
insufficient on real counterexamples. Do **not** implement ahead of that evidence.

**Parity ledger:** expansion A8 follow-on (the deferred `Backend.ChoiceSeq` item
listed in the Tier-B report §"Reach left open").

**Author-intent one-liner:** give Antigen Hypothesis-style *internal* shrinking —
minimization that operates on the generator's underlying choice buffer and stays
effective through the deep `bind`/`lazy` chains the lazy `gen_term` now produces —
so that when the generator finds a counterexample, the banked antibody is a
*minimal* witness rather than a depth-12 monster.

---

## 1. Problem

Antigen's term generator (`Antigen.Generators.Term`) is now *lazy* (commit
`4d3eeed`): `gen/3` defers construction behind `Gen.lazy`, so it reaches genuinely
deep dependent terms (`@max_size` raised 3 → 12; observed structural depth well
past 10). That is exactly the regime where the current shrinking story is weakest:

1. **The default backend's shrinking isn't even in the loop.** `Antigen.Runner`
   draws with `Backend.StreamData.interp(gen) |> Enum.take(count)`
   (`runner.ex:206`) and runs assays manually. It never uses
   `StreamData.check_all`/`property`, which is what triggers StreamData's
   integrated shrink-on-failure. So today, on a real infection, we bank the **raw**
   generated value with **zero** minimization.
2. **Integrated shrinking degrades through deep binds anyway.** StreamData's
   Hedgehog-style shrink tree is woven into the `bind`/`frequency` structure;
   shrinking the head of a `bind` re-runs the continuation as a *fresh* draw, so
   for a deep dependent term (a long `bind` chain) it tends to stall at a
   non-minimal local optimum.

Choice-sequence ("internal") shrinking, the technique Hypothesis uses, sidesteps
both: the generator is driven by a flat integer buffer, and minimization operates
on that buffer, re-running the *same* deterministic generator each time. A flat
buffer is far easier to reduce than a tree, and because our generator only ever
emits well-typed terms (interleaved generation-and-checking), any buffer that
drives generation to completion yields a well-typed term — so buffer-level shrinks
that still parse are **valid by construction**, no per-candidate re-typecheck
needed for validity (only for the violation predicate).

**Non-goal:** this does NOT replace StreamData for generation. StreamData stays the
default. `ChoiceSeq` is a second implementation of the `Antigen.Backend` behaviour,
selected only when we want internal shrinking. The two must agree on generation
(see §7 differential test).

---

## 2. Why not just "hand off from StreamData"

Rejected (this was explicitly considered). StreamData's shrink state is an
integrated lazy *tree* woven into the generator; it is not a choice buffer and
cannot be re-driven as one. There is no representation to hand off — "let
StreamData reduce partway, then finish in Hypothesis style" is a category error.
Getting choice-sequence shrinking requires the generator to *be* a pure function
of a buffer, which is this backend. It is `instead-of` StreamData for shrinking
runs, not `on-top-of`.

---

## 3. The choice sequence

A **choice sequence** (buffer) is a finite list/array of non-negative integers —
the "tape" the generator reads its decisions from. Generation is a total-ish pure
function:

```
drive(gen :: Gen.t(), buf :: [non_neg_integer()], size :: non_neg_integer())
  :: {:ok, value, consumed :: non_neg_integer()} | {:underflow} | {:reject}
```

- `:ok` — generation completed; `value` is the produced term, `consumed` is how
  many draws were read (a shrink pass may truncate the tail past `consumed`).
- `:underflow` — the generator asked for more draws than the buffer holds. During
  random sampling this never happens (we extend the buffer on demand, §5). During
  shrinking it means "this shrunk buffer is too short" → discard candidate.
- `:reject` — the generator hit a dead choice (e.g. a `frequency` branch that a
  guard then refuses). v1 `gen_term` avoids hard rejects by construction (canon
  fallback), so `:reject` should be rare; treat like `:underflow` when shrinking.

**Draw primitive.** A single `draw(buf_cursor, bound)` reads the next integer and
returns `rem(n, bound)` (bound = number of choices at this point). Smaller buffer
integers ⇒ earlier/simpler choices ⇒ this is what makes lexicographic buffer
minimization correspond to structural minimization. **The generator's branch
ordering therefore matters:** rules must be ordered simplest-first so that "draw 0"
is the simplest inhabitant. This is a new constraint the generator must honor for
the shrinker to be effective (see §6).

---

## 4. Interpreting the `Gen` AST against a buffer

`Antigen.Backend.ChoiceSeq` implements `drive/3` by structural recursion over
`Antigen.Gen.t()`. Draw budget per node:

| Node | Draws | Semantics |
|---|---|---|
| `{:return, x}` | 0 | yield `x` |
| `{:member_of, xs}` | 1 (bound `length(xs)`) | `Enum.at(xs, draw)` |
| `{:one_of, gs}` | 1 (bound `length(gs)`) + sub | pick branch, then `drive` it |
| `{:frequency, ws}` | 1 (bound `sum(weights)`) + sub | weighted pick by cumulative weight, then `drive` chosen |
| `{:bind, g, f}` | draws(g) + draws(f(x)) | drive `g` → `x`, then drive `f.(x)` |
| `{:sized, f}` | draws(f(size)) | call `f.(size)` with the driver's size, drive result |
| `{:resize, n, g}` | draws(g) at size `n` | drive `g` with size overridden to `n` |
| `{:tagged, _t, g}` | draws(g) | passthrough (tags are StreamData hints; ignored here) |
| `{:lazy, fun}` | draws(fun()) | force `fun.()`, drive result (0 extra draws — pure deferral) |

`lazy` is the crux: forcing happens only when the driver reaches the node, so a
recursively-built generator unfolds one buffer-driven path at a time — the same
O(depth) property the StreamData backend gets, preserved here.

**Size.** Buffer drives *choices*; `size` drives *scale* and is a driver parameter
(as in StreamData, ramped during sampling — §5). `sized`/`resize` read it. Keeping
size out of the buffer keeps the buffer purely about branch selection, which makes
shrink passes cleaner; an outer shrink pass may additionally try smaller sizes
(§6, pass 4).

---

## 5. Sampling (generation) via the behaviour

The `Antigen.Backend` behaviour is extended (additive; StreamData keeps working):

```elixir
@callback interp(Gen.t()) :: native
@callback sample(native, count) :: [value]                     # existing
# NEW, for shrink-capable backends (optional callbacks):
@callback sample_with_seed(Gen.t(), count, opts) :: [{value, replay :: term()}]
@callback shrink(Gen.t(), replay :: term(), (value -> boolean())) :: {value, replay}
```

- `sample_with_seed/3` draws with an explicit, reproducible PRNG. Implementation:
  seed `:rand` with a **fixed, caller-supplied seed** (NEVER an ambient clock —
  reproducibility is mandatory), generate a fresh random buffer per sample
  (extending on `:underflow` and retrying), ramp `size` across the stream the way
  StreamData does. `replay` is `{buffer, size}` — enough to regenerate `value`
  byte-for-byte.
- `shrink/3` is the minimizer (§6). `pred` is "does this value still violate the
  assay?" — the Runner supplies a closure that re-runs the specific assay.

StreamData may leave `sample_with_seed`/`shrink` unimplemented (it is not a
choice-sequence backend); the Runner uses them only when the selected backend
exports them.

---

## 6. Shrinking (`shrink/3`)

Greedy fixpoint over standard Hypothesis-style buffer passes. Each pass proposes a
candidate buffer; accept it iff `drive` returns `:ok` AND `pred.(value)` is true
(still violates). Repeat all passes until a full sweep makes no change.

Passes, cheapest/most-impactful first:

1. **Truncation / structural chop** — cut the buffer at each `consumed` prefix
   boundary; a shorter buffer that still completes = a structurally smaller term
   (fewer constructors). Biggest wins come first here.
2. **Region deletion** — delete contiguous draw ranges (halving/√ strides, à la
   Hypothesis' `delete` pass) to remove whole subterms.
3. **Individual-value minimization** — for each remaining draw, binary-search it
   toward 0 (simpler branch / smaller numeral), keeping the violation.
4. **Size reduction** — retry `drive` at smaller `size` values; accept the
   smallest size that still reproduces (shrinks depth independent of buffer).
5. **Canonicalization sweep** — re-order/normalize equal-cost draws to a canonical
   form so semantically-identical minimal witnesses dedupe to one antibody.

**Validity is free.** Because `gen_term` interleaves checking (only well-typed
terms are ever emitted), any `:ok` candidate is well-typed — the shrinker never
needs a separate type re-check for *validity*. It only evaluates `pred` (the
assay). This is the key advantage over value-level term rewriting, where every
edit must be re-typechecked to stay in the well-typed subset.

**Generator obligation (branch ordering).** For pass 1/3 to shrink toward the
*simplest* term, `Term`'s rule lists must be ordered simplest-first (canon/var
before app/case/INDIR), so "draw 0" is the simplest inhabitant at every choice.
This is a generator change that ships WITH this backend, guarded by a test that
asserts the size-0 / all-zero-buffer term equals `SigMenu.canon`.

---

## 7. Testing strategy (for when it is built)

Red-green TDD; the artifact is executable code.

1. **Determinism** — same `{buffer, size}` ⇒ identical value (property).
2. **Backend agreement (differential)** — for the finite fragments where
   `Gen.support/1` returns `{:finite, s}`, the *set* of values `ChoiceSeq` can
   produce equals StreamData's support. Guards against the two backends diverging
   on generation semantics.
3. **Validity** — every sampled value type-checks (`Kernel.infer` ok), same
   invariant the StreamData path already asserts.
4. **Shrink soundness** — `shrink/3` output still satisfies `pred` and still
   type-checks (it must, by §6, but assert it).
5. **Shrink monotonicity** — the shrunk value's size measure ≤ the input's; a full
   sweep is idempotent (re-shrinking a minimal witness is a no-op).
6. **Known-monster → known-minimum (the headline red test)** — construct/seed a
   deep term that trips a *deliberately planted* violation (reuse a mutation-corpus
   antibody, §9) and assert `shrink/3` reduces it to the expected minimal witness.
   Without a real violation to shrink there is nothing to test — hence the §9 gate.

---

## 8. Architecture & constraints

- Lives at `lib/antigen/backend/choice_seq.ex` as `Antigen.Backend.ChoiceSeq`,
  implementing `Antigen.Backend`. It is inherently StreamData-free, so the
  quarantine test (`architecture_test.exs`: no `StreamData` under
  `generators/`/`assays/`) is unaffected — and note ChoiceSeq must itself never be
  referenced from `Generators.*`/`Assays.*` either; only the Runner selects a
  backend.
- **Reproducibility is non-negotiable:** all randomness via `:rand` seeded from a
  caller-supplied seed. No ambient clock, no unseeded `:rand`. This mirrors the
  banked-seed replay contract the corpus already depends on.
- **Backend selection:** `Runner.draw/2` currently hardcodes
  `Backend.StreamData`. Introduce a single configured backend module
  (`@backend`), defaulting to StreamData; shrinking is invoked only when the
  configured backend exports `shrink/3`. Keep generation on whichever backend is
  configured so §7.2 agreement stays meaningful.
- The `Gen` AST does not change. `ChoiceSeq` is a second *interpreter* of the same
  reified program — this is precisely the payoff of the swappable-backend design.

---

## 9. Decision gate (why this is backlog, not next)

Shrinking only pays off when there is a counterexample to shrink, and the
generator currently finds **0 infections**. The correct next step is the
**ill-typed mutation corpus** (deliberately malformed terms → assays that catch
the kernel wrongly accepting one), which is what will *produce* counterexamples.

That work introduces a *value-level greedy post-shrink* (rewrite the reified
`%{ctx, type, term}` artifact directly, re-validating each edit through the
kernel) — cheaper, backend-independent, and testable against the mutation corpus'
known antibodies. Build `ChoiceSeq` **only if** value-level post-shrink proves
insufficient on those real counterexamples (e.g. it stalls at non-minimal
witnesses for deep terms). Concretely, the gate is:

> After the mutation corpus + value-level post-shrink land, take the deepest real
> antibodies and measure post-shrink minimality. If they remain
> visibly-non-minimal (extra subterms/context a human would delete by hand), build
> `ChoiceSeq`. Otherwise leave this spec on the shelf.

For terms, value-level greedy shrinking usually suffices; expect `ChoiceSeq` to
stay on the shelf unless the term fragment grows much richer.

---

## 10. Estimated shape (when built)

~1 new module (`choice_seq.ex`, the `drive`/`sample_with_seed`/`shrink` trio), an
additive extension to the `Antigen.Backend` behaviour (two optional callbacks),
the `Runner` backend-selection seam, the generator branch-ordering change +
its guard test, and the §7 test suite. No changes to `Gen`, the assays, the
challenge model, or the corpus format.
