# Weak-Head Normalization Before Unification (#11, pivoted) — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans (inline) to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax.

**Goal:** Make Cure's elaborator unifier reduce both sides to weak-head normal form before structural comparison, so reducible redexes (e.g. `plus(Z, ?m)` → `?m`) are handled, reaching dependent-inference inputs Idris accepts. E-layer only; reuses the trusted `Normalise.whnf` unchanged; no TCB.

**Architecture:** In `Cure.Elab.Unify`, add a meta-aware whnf (substitute unsolved metavariables with opaque-global placeholders → `Normalise.whnf` → reverse-map) and call it on both sides at the start of the unify step, recursing on the reduced terms only if a side changed (Lean's reduce-then-recurse loop). No `MetaCtx` change, no constraint queue, no `occurs?` change.

**Tech Stack:** Elixir; Cure compiler (`lib/cure/elab/unify.ex`, `lib/cure/core/normalise.ex` — read-only reuse); differential oracle (`mix cure.oracle`, `idris2 --check`); ExUnit.

## Global Constraints

- **Layer: E only.** Touch `lib/cure/elab/unify.ex`, `test/**`, `docs/**`. **No `lib/cure/core/*` diff** (verify at the gate: `git diff --stat main -- lib/cure/core/` is empty). No TCB, no Antigen antibody (kernel re-checks; reduction reused is already trusted).
- **Ghost-writer commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, NO `Co-Authored-By`, no Claude signature.
- **Explicit-pathspec staging only:** `git add -- <path>`. NEVER `git add -A`/`.` (a concurrent agent may share this worktree).
- **One build at a time.** Never two `mix` suites concurrently. Prefer scoped `mix test <file>`; full `mix test` once, alone, at the gate.
- **Oracle discipline:** the `cure`/`idris` verdict fields come from `mix cure.oracle whnf`, never hand-written; freeze into `test/oracle/whnf/verdicts.json`; `mix test test/oracle_replay_test.exs` green before any fixture-touching commit. The `relation`/`reason` metadata fields are the one exception — `Oracle.consistent/1` requires them to encode a divergence's cause in prose the tool cannot generate, so hand-setting them (Task 1 Step 7.5; Task 3 Step 3) is the established, required discipline, not a violation of this rule.
- **`mix run` unavailable** for probes (throws `unknown registry: Cure.Pipeline.Events.Registry`). Dump Cure reasons via a throwaway test-env module calling `Cure.Elab.Program.elaborate/1`.
- **Tests immutable once green**; behavioral.

## File Structure

- `lib/cure/elab/unify.ex` — NEW `whnf_meta_aware(term, ctx, sig, depth \\ 0, opts \\ [])` helper in the `Unify` module (`@doc false` + `def`, NOT `defp` — Task 2's unit tests call it directly from a separate test module, which is impossible for a private function in Elixir; this mirrors the existing `Normalise.whnf_value/3` idiom of "public but undocumented" for internal-surface functions); a reduction step inserted into `unify_d/5` (unify.ex:101) between `force_d` and `do_unify`.
- `test/cure/elab/unify_whnf_test.exs` — NEW unit tests for the meta-aware whnf helper.
- `test/oracle/whnf/whnf0{1,2,3,4}_*.{cure,idr}` + `verdicts.json` — NEW oracle probes.

---

## Task 1 — Author + freeze the oracle probes (gate already passed empirically)

The reachability gate passed during the pivot (verified `cure=reject
{:cannot_unify, plus(Z,?0), S(Z)}` / `idris=accept`). This task re-creates the
probes cleanly under `test/oracle/whnf/`, adds the two negatives, and freezes.

**Files:**
- Create: `test/oracle/whnf/whnf01_computed_index.{cure,idr}`,
  `whnf02_two_arg_shared_index.{cure,idr}`, `whnf03_stuck_meta_neg.{cure,idr}`,
  `whnf04_concrete_mismatch_neg.{cure,idr}`
- Create (throwaway, deleted at task end): `test/zzz_probe_test.exs`

**Interfaces:**
- Produces: frozen `test/oracle/whnf/verdicts.json` — `whnf01`/`whnf02`
  `cure=reject,idris=accept` (pre-fix); `whnf03`/`whnf04` `reject/reject`.
  Consumed as the red/regression tests in Task 3.

- [ ] **Step 1: Author `whnf01_computed_index`** (verified confound-free during pivot):
```
# whnf01_computed_index.cure
mod Whnf01
  type Nat = Z | S(Nat)
  fn plus(a: Nat, b: Nat) -> Nat = match a
    Z() -> b
    S(k) -> S(plus(k, b))
  type Vec indices (n: Nat)
    vz : Vec(Z)
    vs : Vec(k) -> Vec(S(k))
  fn needlen({m: Nat}, v: Vec(plus(Z, m)), r: Nat) -> Nat = r
  fn use() -> Nat = needlen(vs(vz()), Z())
end
```
```
-- whnf01_computed_index.idr
%default total
data Nat2 = Z | S Nat2
plus : Nat2 -> Nat2 -> Nat2
plus Z n = n
plus (S k) n = S (plus k n)
data Vec : Nat2 -> Type where
  VZ : Vec Z
  VS : Vec k -> Vec (S k)
needlen : {m : Nat2} -> Vec (plus Z m) -> Nat2 -> Nat2
needlen _ r = r
use : Nat2
use = needlen (VS VZ) Z
```

- [ ] **Step 2: Author `whnf02_two_arg_shared_index`** — same as `whnf01` but the
  function is `twovec({m}, w: Vec(plus(Z, m)), v: Vec(m), r: Nat) -> Nat = r` and
  `use() = twovec(vs(vz()), vs(vz()), Z())`; `.idr` transliterates identically
  (`twovec : {m} -> Vec (plus Z m) -> Vec m -> Nat2 -> Nat2`).

- [ ] **Step 3: Author `whnf03_stuck_meta_neg`** — the genuinely-stuck negative:
  `stuck({m}, v: Vec(plus(m, Z)), r: Nat) -> Nat = r`, `use() = stuck(vs(vz()),
  Z())`. `plus(m, Z)` is stuck on `?m` (meta in the scrutinee position) — nothing
  determines `?m`. `.idr` transliterates. EXPECT reject/reject (Idris: unsolved
  `m`; Cure: `cannot_unify`/unsolved-meta on the stuck neutral).

- [ ] **Step 4: Author `whnf04_concrete_mismatch_neg`** — reduction succeeds but
  reduced forms differ: `mismatch(v: Vec(plus(Z, Z))) -> Nat = Z()` applied to a
  `vs(vz()) : Vec(S(Z))`, forcing `plus(Z,Z)=Z =? S(Z)` → genuine disequality.
  (No implicit needed; both sides concrete.) `.idr` transliterates. EXPECT
  reject/reject. Guards that whnf-then-compare still rejects real mismatches.

- [ ] **Step 5: Run the oracle.** `mix cure.oracle whnf` → writes
  `test/oracle/whnf/verdicts.json`.

- [ ] **Step 6: Verify reasons (not confounds).** Throwaway test dumping
  `Cure.Elab.Program.elaborate(File.read!("…cure"))` for each probe:
```elixir
# test/zzz_probe_test.exs
defmodule ZzzProbeTest do
  use ExUnit.Case
  for n <- ~w(whnf01_computed_index whnf02_two_arg_shared_index whnf03_stuck_meta_neg whnf04_concrete_mismatch_neg) do
    test "reason #{n}" do
      IO.inspect(Cure.Elab.Program.elaborate(File.read!("test/oracle/whnf/#{unquote(n)}.cure")),
        label: ">>> #{unquote(n)}", limit: :infinity)
    end
  end
end
```
`mix test test/zzz_probe_test.exs`. CONFIRM: `whnf01`/`whnf02` reject with a
`{:cannot_unify, plus(Z, {:meta,_}), …}` / `{:index_mismatch, …}` reason (NOT
erasure `{:erased_used_relevantly}` — do not return the implicit; NOT
`{:unsolved_metavariables, :vz}` — the monomorphic `Vec` has no element-type
meta). `whnf03` reject with a stuck-`plus(m,Z)` unify/unsolved reason; `whnf04`
reject with a `Z =? S(Z)` mismatch. If any reason is a confound, fix the probe
and re-run before freezing.

- [ ] **Step 7: Delete the throwaway test** (`rm test/zzz_probe_test.exs`; never commit it).

- [ ] **Step 7.5: Set the relation for the two divergent probes.** `Oracle.consistent/1`
  (lib/cure/oracle.ex:167-174) requires EITHER `relation == "same"` with
  `cure == idris`, OR `relation ∈ ["cure_stricter", "idris_only"]` with a
  non-empty `reason` and `cure=="reject"`/`idris=="accept"`. Step 5's fresh
  `mix cure.oracle whnf` run defaulted every new pair's `relation` to `"same"`
  (`Mix.Tasks.Cure.Oracle`'s `Map.get(prior, name, %{"relation" => "same", ...})`
  — there is no prior fixture yet), which is INCONSISTENT for `whnf01`/`whnf02`
  (`cure="reject"`, `idris="accept"`) and will fail Step 8's replay untouched.
  Hand-edit `test/oracle/whnf/verdicts.json`: set `whnf01`/`whnf02`'s
  `"relation"` to `"cure_stricter"` with a written `"reason"` (e.g. "whnf-before-
  compare not yet wired in (#11) — plus(Z, ?m) is a reducible redex the
  unreduced-comparison unifier cannot see; fixed by Task 3"). `whnf03`/`whnf04`
  need no edit (`cure == idris == "reject"`, already consistent under
  `relation: "same"`). This is the established discipline for a known, transient
  gap in this codebase (see `docs/superpowers/plans/2026-07-03-postponed-
  constraints-plan.md:70`, which set the identical `cure_stricter` relation for
  its own pre-fix divergent probes) — it edits only the relation/reason
  metadata, never the `cure`/`idris` verdict fields themselves, so it does not
  violate the Global Constraints' "verdicts from `mix cure.oracle`, never
  hand-written" rule.

- [ ] **Step 8: Replay + commit.** `mix test test/oracle_replay_test.exs`
  (Expected PASS — fixture keys match the four paired files, and `consistent/1`
  holds for every entry now that Step 7.5 set `whnf01`/`whnf02`'s relation).
  Then:
```bash
git add -- test/oracle/whnf/
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "test(oracle): #11 whnf probes — computed-index inference (reject; idris accept)"
```

---

## Task 2 — Meta-aware whnf helper (TDD unit)

**Files:**
- Modify: `lib/cure/elab/unify.ex` (Unify module — add `whnf_meta_aware/…`)
- Test: `test/cure/elab/unify_whnf_test.exs`

**Interfaces:**
- Consumes: the lower-level `Eval.eval/2` + `Normalise.whnf_value/3` +
  `Quote.reify/2` trio, called directly with a hand-built env (NOT
  `Cure.Core.Normalise.whnf/3`, which needs a `Core.Context.t()` the unifier
  cannot cleanly construct — see spec §3.3: `Context.t()` carries a `types`
  field the unifier has no values for, and no existing call site or public API
  builds a length-only, types-unknown `Context`; `types` is provably unread by
  the whnf path, so bypassing `Context` entirely is the correct, non-hand-waved
  choice, not a shortcut); `MetaCtx` solutions (via existing `zonk/2`).
- Produces: `Unify.whnf_meta_aware(term, ctx, sig, depth \\ 0, opts \\ [])` ::
  `Core.Term.t()` (a single `def` with two default args — callable at arity 3,
  4, or 5) — `ctx` here is the `MetaCtx.t()` (for `zonk`), `sig` is the
  `Core.Env.t()` signature, `depth` is the de Bruijn depth to build the env at
  (defaults to 0, matching most of Task 2's own unit tests below; Task 3's
  wiring inside `unify_d/5` passes the live `depth` explicitly), `opts` accepts
  `fuel:` (default `:infinity`, mirroring `Normalise`'s own default — see
  `normalize_opts/1`, normalise.ex:94-99), threaded to `Normalise.with_fuel/2`
  around the reduction (Step 3). Returns the whnf of `term` with unsolved metas
  preserved as neutrals, or the (zonked) input unchanged on `:fuel_exhausted`/any
  anomaly. Consumed by Task 3.

- [ ] **Step 1: Write failing unit tests.**
```elixir
# test/cure/elab/unify_whnf_test.exs
defmodule Cure.Elab.UnifyWhnfTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{MetaCtx, Unify}
  # `ctx` (the elaborator's MetaCtx, for `zonk`) needs no metas solved for these
  # cases — `MetaCtx.new()` suffices. `sig` (a Core.Env) must have `plus` defined
  # as a certified-total global — pin its exact construction in Step 3 by reading
  # how `test/cure/core/*` or `test/oracle` build signatures; if that is
  # heavyweight, drive these cases through `Cure.Elab.Program.elaborate/1` on a
  # tiny module instead, asserting acceptance — but a direct unit on the helper
  # is preferred.

  test "whnf reduces plus(Z, ?m) to ?m (meta passes through)" do
    # plus(Z, ?0) must reduce to {:meta, 0}
    t = {:app, {:app, {:global, :plus}, {:ctor, :Z, []}}, {:meta, 0}}
    assert Unify.whnf_meta_aware(t, MetaCtx.new(), sig_with_plus()) == {:meta, 0}
  end

  test "whnf leaves plus(?m, Z) stuck (meta in scrutinee position)" do
    t = {:app, {:app, {:global, :plus}, {:meta, 0}}, {:ctor, :Z, []}}
    assert Unify.whnf_meta_aware(t, MetaCtx.new(), sig_with_plus()) == t
  end

  test "whnf on a meta-free reducible term matches Normalise.whnf" do
    t = {:app, {:app, {:global, :plus}, {:ctor, :Z, []}}, {:ctor, :S, [{:ctor, :Z, []}]}}
    assert Unify.whnf_meta_aware(t, MetaCtx.new(), sig_with_plus()) == {:ctor, :S, [{:ctor, :Z, []}]}
  end

  test "whnf falls back to the zonked input on :fuel_exhausted (never crashes, never fabricates)" do
    # A term whose certified-global unfold chain cannot finish within a tiny
    # fuel budget must come back unchanged (zonked), matching Normalise.whnf's
    # own :fuel_exhausted contract (normalise.ex:69-81) — pin the exact
    # low-fuel-triggering term in Step 3 against how `whnf_meta_aware` threads
    # `Normalise.with_fuel/2` (e.g. a deeply-recursive certified `plus` call
    # under a fuel budget too small to finish it).
    t = deep_plus_redex()
    assert Unify.whnf_meta_aware(t, MetaCtx.new(), sig_with_plus(), 0, fuel: 1) == t
  end
end
```

- [ ] **Step 2: Run, verify fail.** `mix test test/cure/elab/unify_whnf_test.exs`
  — Expected: FAIL (`whnf_meta_aware` undefined at whichever arity each call site uses).

- [ ] **Step 3: Implement `whnf_meta_aware(term, ctx, sig, depth \\ 0, opts \\ [])`.**
  1. `z = zonk(term, ctx)` (apply known solutions; `ctx` here is the `MetaCtx.t()`).
  2. `{subst, map} = replace_metas_with_placeholders(z)` — walk `z`; each
     remaining `{:meta, id}` → `{:global, :"$meta$#{id}"}`, recording `id` in
     `map` (a MapSet or map placeholder-atom→id; the atom prefix `"$meta$"` is not
     a legal Cure identifier, so no collision with a user global).
  3. Reduce via the low-level trio directly — NOT `Normalise.whnf/3` (which
     needs a `Core.Context.t()` the unifier cannot cleanly build; see spec §3.3
     and this task's Interfaces section above):
     ```elixir
     env = for level <- (depth - 1)..0//-1, do: {:vneutral, {:nvar, level}}
     value = Eval.eval(subst, env)
     reduced_value = Normalise.whnf_value(value, sig, delta: :certified, stuck_cases: :preserve)
     reduced = Quote.reify(reduced_value, depth)
     ```
     (`depth - 1 .. 0//-1` is empty when `depth == 0`, giving `env = []` —
     matching `Context.env/1`'s own `length: 0` clause.) `Normalise.whnf_value/3`
     cannot itself signal `:fuel_exhausted` (that check lives in `Normalise`'s
     `run_with_fuel` wrapper around the whole `whnf/3` call, which this path
     does not go through) — so wrap the whole reduction (the `Eval.eval` +
     `whnf_value` + `Quote.reify` sequence above) in `Normalise.with_fuel/2`
     (public, normalise.ex:68-81), passing `Keyword.get(opts, :fuel, :infinity)`
     as its first argument: `Normalise.with_fuel(fuel, fn -> ... end)`. This
     reproduces `whnf/3`'s own fuel-exhaustion contract exactly — `spend_fuel`
     (called deep inside `unfold_certified_head`/`reduce_unfolded`) reads/writes
     the fuel counter via the process dictionary, not via any argument
     `whnf_value` threads explicitly, so wrapping the call site is sufficient;
     `with_fuel` catches the thrown exhaustion and returns `:fuel_exhausted` from
     the `fn -> ... end`. On `:fuel_exhausted` → return `z` (fallback).
  4. `restore_placeholders(reduced)` — walk; each `{:global, :"$meta$" <> _}` →
     `{:meta, id}` via `map` (or by parsing the id out of the atom). Return it.
  Structural walks (steps 2 & 4) must cover every subterm-bearing Core shape —
  mirror `Unify.zonk/2`'s generic tuple/list walk (unify.ex:407-414) so no shape
  is missed.

- [ ] **Step 4: Run, verify pass.** `mix test test/cure/elab/unify_whnf_test.exs`
  — Expected: PASS (all four).

- [ ] **Step 5: Commit.**
```bash
git add -- lib/cure/elab/unify.ex test/cure/elab/unify_whnf_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(elab): meta-aware whnf (placeholder reuse of Normalise.whnf) (#11)"
```

---

## Task 3 — Wire whnf into the unify step (oracle red-green)

**Files:**
- Modify: `lib/cure/elab/unify.ex` (`unify_d/5` at :101)
- Test (red): the Task-1 oracle probes.

**Interfaces:**
- Consumes: `whnf_meta_aware(t, meta_ctx, sig, depth)` (Task 2; `meta_ctx` is the
  live `MetaCtx.t()` already threaded through `unify_d`, NOT a fresh one).
- Produces: `whnf01`/`whnf02` flip to accept; `whnf03`/`whnf04` stay reject.

- [ ] **Step 1: Red — probes still reject.** `mix cure.oracle whnf`; confirm
  `whnf01`/`whnf02` still `cure=reject` (standing red before the wire-in).

- [ ] **Step 2: Wire whnf into `unify_d/5`.** Currently:
  `do_unify(force_d(t1, ctx, depth), force_d(t2, ctx, depth), ctx, sig, depth)`.
  Change to: whnf both forced sides via `whnf_meta_aware(forced, ctx, sig, depth)`
  (passing the live `MetaCtx.t()` `ctx` and `depth` explicitly — do NOT rely on
  the `depth \\ 0` default here, since `unify_d` is called at nonzero depth
  under binders); if EITHER changed, re-enter `unify_d` on the reduced pair
  (bounded: whnf is idempotent, so the recursion terminates when neither side
  changes); else fall through to `do_unify` exactly as today. Guard against
  infinite recursion by comparing pre/post terms (`reduced == forced` → no
  change → structural). Only reduce when `sig != nil` (whnf needs the
  signature; `sig == nil` callers keep today's behavior).

- [ ] **Step 3: Green — verify the flip + negatives hold.** `mix cure.oracle whnf`:
  `whnf01`, `whnf02` → `cure=accept`; `whnf03`, `whnf04` → still `reject/reject`.
  This regenerates `cure`/`idris` fields but PRESERVES whatever `relation`/
  `reason` Task 1 froze (`Mix.Tasks.Cure.Oracle` carries prior `relation`/
  `reason` forward — lib/mix/tasks/cure.oracle.ex `Map.get(prior, name, ...)`).
  Since `whnf01`/`whnf02` now have `cure == idris == "accept"`, their frozen
  `relation` (`"cure_stricter"`, set in Task 1) is now STALE and will fail
  `Oracle.consistent/1` (lib/cure/oracle.ex:167-174 — the `"same"` clause
  requires `relation == "same"`; the divergent clause requires `cure=="reject"`,
  which no longer holds). Hand-edit `test/oracle/whnf/verdicts.json` to reset
  `whnf01`/`whnf02`'s `"relation"` back to `"same"` (this edits only the
  relation/reason metadata, never the `cure`/`idris` verdict fields themselves —
  those still come solely from the oracle run, satisfying the Global
  Constraints' "verdicts from `mix cure.oracle`, never hand-written" rule).

- [ ] **Step 4: Replay + no regression.** `mix test test/oracle_replay_test.exs`
  (auto-discovers ALL `test/oracle/*` — confirms no other cluster: dep, guard,
  match, rewrite, with, etc. regressed). Then the unit tests:
  `mix test test/cure/elab/unify_whnf_test.exs test/cure/elab/unify_test.exs`.
  Also run the unifier-adjacent suites that exercise `do_unify`/`solve`:
  `mix test test/cure/elab/unify_meta_completeness_test.exs test/cure/elab/miller_unify_test.exs test/cure/elab/higher_order_unify_test.exs`
  (pin the exact existing filenames by `ls test/cure/elab/`; run whichever exist).
  Expected: all PASS.

- [ ] **Step 5: Commit.**
```bash
git add -- lib/cure/elab/unify.ex test/oracle/whnf/
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(elab): whnf both sides before structural unification (#11)"
```

---

## Task 4 — Roadmap update + final verification gate

**Files:**
- Modify: `docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md` (§2 row #11)

- [ ] **Step 1: Update roadmap row #11** → **landed (whnf-before-compare)**: name
  the four `whnf` probes, the meta-aware-whnf mechanism (placeholder reuse of the
  trusted `Normalise.whnf`, no TCB), the kernel-backstop note, and that
  postponement is deferred as a secondary follow-up. Note the pivot from the
  superseded postponement design.

- [ ] **Step 2: No-TCB verification.** `git diff --stat main -- lib/cure/core/`
  — Expected: EMPTY. If non-empty, STOP.

- [ ] **Step 3: Full suite, once, alone.** `mix test` — Expected: all green
  (oracle replay + unit + everything). Record the pass count.

- [ ] **Step 4: Commit.**
```bash
git add -- docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "docs(spec): #11 whnf-before-unification landed — roadmap update"
```

---

## Self-Review

**Spec coverage:** §2 probes → Task 1. §3.2 meta-aware whnf → Task 2. §3.1 wire
at unify step → Task 3. §9 DoD (no-TCB, roadmap, full suite) → Task 4. §3.4
does-not-fix (stuck) → `whnf03` negative. §3.2 fuel fallback → Task 2 Step 3 +
unit intent.

**Placeholder scan:** The one remaining "pin against the code" spot — the
unit-test signature fixture (`sig_with_plus()`, Task 2 Step 1) — names the exact
place to pin against (`Program`/`Declarations` sig-building). The `Context`
plumbing question is NO LONGER a placeholder: it is resolved (not just
"pinned") by bypassing `Context.t()` entirely and calling `Eval.eval/2` +
`Normalise.whnf_value/3` + `Quote.reify/2` directly with a hand-built env (spec
§3.3; Task 2 Step 3), which is verified achievable against the actual
`Context`/`Eval`/`Quote` public APIs — not hand-waved.

**Type consistency:** `whnf_meta_aware(term, ctx, sig, depth \\ 0, opts \\ [])
:: Core.Term.t()` consistent across Tasks 2 & 3 (Task 3 always passes `ctx`
and `depth` explicitly at their live values; Task 2's unit tests rely on the
`depth \\ 0` default for their all-top-level terms, except the fuel test which
also supplies `opts`). Placeholder atom prefix `"$meta$"` consistent (sub +
restore). Recurse-on-change guard (`reduced == forced`) consistent. Oracle
`relation` lifecycle (`"same"` → `"cure_stricter"` at Task 1 freeze → back to
`"same"` at Task 3's post-fix flip) is now explicit at both transition points
(Task 1 Step 7.5; Task 3 Step 3), matching `Oracle.consistent/1`'s actual
contract and the established precedent in the superseded postponement plan.

**Risk:** the `Context`/`depth` plumbing for reduction was the one non-trivial
unknown; it is resolved by construction (bypassing `Context.t()`, whose `types`
field is verified unread by the whnf codepath) rather than left for Task 2 to
discover. Task 2's unit tests (which build the exact `plus(Z,?m)` term) still
force the reduction correct via red-green before any wiring. If the reduction
cannot be driven at the needed depth cleanly for some unforeseen reason, the
fallback (`return zonked input`) degrades gracefully to today's behavior —
never a crash or a wrong accept.
