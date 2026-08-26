# Antigen V4 — Erasure & Relevance Soundness — Completion Report

**Branch:** `autopilot/antigen-tier-b` · **Date:** 2026-07-03 · **Mode:** autopilot via `/loop` (autonomous continuation)

Fifth phase of the untrusted-machinery initiative (task #66), after V3/V1/V2/V5. Tests
the untrusted `{0,ω}` erasure/relevance machinery — `Cure.Elab.Erase.erase/2` and
`Cure.Elab.Relevance.check/4`. No `Cure.Core.*`/`Cure.Elab.*` edits, no `:meck`, no new dep.

## 🔴 HEADLINE FINDING — `Erase.erase/2` is non-idempotent (a real, dormant bug)

**Antigen found its first genuine soundness-relevant defect in the untrusted
machinery.** `erase(env, erase(env, t)) ≠ erase(env, t)` whenever a constructor (or
a global def) has an **`:erased`-before-`:present`** quantity ordering.

**Mechanism** (traced in spec review, confirmed empirically at execution): the
`:ctor` and `:app`-head clauses re-read the **original full-length** quantity vector
and `Enum.zip` it **positionally** against the args they are given. After the first
erase shrinks the args to only the `:present` positions, a second erase zips the
same full vector against the now-shorter list — `zip` pairs by index, so survivors
re-align to the vector's *leading* entries and get dropped if a leading entry is
`:erased`:

```
qs = [:erased, :present], args = [a, b]
  erase¹ → {:ctor, c, [b]}     # keeps the :present position (index 1)
  erase² → zip [b] with [:erased,:present] → pairs b with :erased → {:ctor, c, []}
```

Confirmed on **both** erase surfaces (ctor `:MkP` and app-head `:g`). It is not
synthetic — the production `seq` ctor (`[:erased×5, :present×2]`, already in
`erase_test.exs`) collapses to `{:ctor, :seq, []}` on a second application by the
identical mechanism.

**Severity: dormant, not live-pipeline.** `erase/2` is only ever invoked **once** per
def body (verified at both `emit.ex` call sites — each reads the raw body fresh from
`Env`), so no current code path double-erases. And `erase.ex` is **untrusted**
(elaborator, not TCB) — a wrong erasure is caught downstream or produces a wrong
runtime value, not an unsound *type*. So this is a real algebraic defect worth
fixing, not an emergency. **Per the locked V4 non-goal, Antigen reports it; it does
NOT patch it** — the fix is a separate, separately-authorized change. The fix is
straightforward (drop by original position, or shrink the quantity vector in lockstep
with the args), but out of V4's scope.

The `erasure/idempotent` assay itself is **correct** — it faithfully reports the
non-idempotence as `{:violation, {:erase_not_idempotent, _}}`. Two dedicated tests
assert exactly that (ctor + app-head), documenting the finding as a true-positive;
they are kept out of the clean-catalog sweep so the wiring test stays all-`:ok`.

## What shipped — four assays

| id | engine | property | oracle |
|---|---|---|---|
| `erasure/idempotent` | `Erase` | `erase∘erase == erase` + hole preservation | intrinsic |
| `erasure/selective` | `Erase` | keeps exactly `:present` positions (ctor + app-head) | `ctor_quantities` / def `quantities` |
| `erasure/wellformed` | `Erase` | `term?(t) ⟹ term?(erase t)` | `Term.term?` |
| `relevance/soundness` | `Relevance` | erased-binder-used-relevantly ⟹ rejected (4 sites) | construction |

Plus `Antigen.Generators.ErasureTerm` (mixed-quantity envs via `Inductive.ctor/4` +
`Env.add_def/5`) and `assay_module/1` dispatch for the four ids. V4 does **not**
duplicate the existing surface-program `elab/erasure` assay — it targets the
Core-level functions directly.

## Result of running it

Beyond the erase finding: `selective` confirms real `erase` keeps exactly the
`:present` positions on both surfaces; `wellformed` confirms `term?` is preserved;
`relevance/soundness` confirms all four relevant-use sites (`:returned`,
`:applied`, `:scrutinee`, `:present_arg`) are correctly rejected, and a clean body
accepted. The eight negative controls each infect (including the V2/V5-lesson
controls added at plan review for `:clean_body_rejected` and `:relevance_wrong_site`).

## Stage-by-stage outcomes

| Stage | Outcome | Commit(s) |
|---|---|---|
| 0 — Spec | V4 Core-level two-family design | `<spec>` |
| 1 — Spec review (Sonnet) | 7 passes; **traced + confirmed the erase non-idempotence bug**; fixed `Term.valid?`→`term?/1`; added the app-head second surface; corrected `Inductive.ctor/4` template | `7166002` |
| 2 — Plan | 6-task TDD plan (3 reconciliations incl. known-finding handling) | `6710800` |
| 3 — Plan review (Sonnet) | 4 passes; **independently confirmed the relevance-site de Bruijn indexing**; added the missing app-head known-finding test + 2 relevance negative controls | `34aa026` |
| 4 — Execute (Opus, TDD) | red → green per task, ghost-authored | `7e25c07`, `928003e`, `4aa2eb3`, `c9807c3`, `f5af782` |
| 5 — Verify | full suite green; quarantine clean | (this report) |

### Per-task execution (Stage 4)

1. **`7e25c07`** — `erasure/idempotent` (+ the ctor & app-head known-finding assertions). Green 6/6 — **erase non-idempotence confirmed empirically on both surfaces.**
2. **`928003e`** — `erasure/selective` (ctor + app-head, leaf-arg differential). Green 10/10.
3. **`4aa2eb3`** — `erasure/wellformed` (`term?` preserved; `term?` correctly rejects the unknown-tag stub — contingency not needed). Green 12/12.
4. **`c9807c3`** — `relevance/soundness` (4 sites + clean control + 3 negative controls). Green 20/20 — all sites classify as traced.
5. **`f5af782`** — `ErasureTerm` catalogs + dispatch + `:erasure_term` kind + `@known_atoms`. Green 22/22 — clean catalog all `:ok`.

## Verification

- **Full suite (single authorized run):** `2713 passed` (3 doctests, 2710 tests),
  0 failures — +22 from V5's 2691.
- **StreamData quarantine:** `architecture_test.exs` green (constraint pre-banked).
- **Working tree:** clean (test-run seed side-effect reverted).
- Every commit ghost-authored (`Made In Heaven`), no `Co-Authored-By`.

## Recommended follow-up (operator decision)

Fix `Erase.erase/2`'s zip-realignment so erasure is idempotent — either drop args by
their **original** position index (not by re-zipping a shrunk list), or shrink the
quantity vector in lockstep. This is a small untrusted-code change; the V4
`erasure/idempotent` assay will flip the two known-finding assertions from
`{:violation, …}` to `:ok` once fixed (those tests document the current bug and are
the natural regression guard for the fix).

## Boundaries

V4 **finds**; it does not fix (the erase bug is reported, not patched). Curated
fixed catalog, not a fuzzer. `erase` structural validity is asserted via `term?`
(kernel-acceptance-at-runtime-type is a non-goal — erased terms are non-dependent
runtime forms). V4b tests `Relevance.check/4` directly on Core bodies (complements,
does not duplicate, `elab/erasure`). No change to the locked `{0,ω}` semantics. No SMT (V6).

## Next phase (umbrella roadmap, task #66)

- **V6 SMT lint** (framed by the locked "Z3 out of the TCB" decision) — the last
  umbrella vertical.

**Do NOT auto-merge.** Operator merges `autopilot/antigen-tier-b` on return.
