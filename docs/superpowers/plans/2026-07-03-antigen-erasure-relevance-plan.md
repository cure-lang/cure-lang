# Antigen V4 — Erasure & Relevance Soundness Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** four new Antigen assays testing the untrusted erasure/relevance machinery — `Cure.Elab.Erase.erase/2` (idempotence, hole-preservation, selective drop over ctor **and** app-head surfaces, structural validity) and `Cure.Elab.Relevance.check/4` (erased-binder-used-relevantly rejection across four sites). V4a is **expected to surface a real, spec-review-traced non-idempotence bug in `erase/2`** — the assays are correct; the finding is reported, not patched.

**Architecture:** A new `Antigen.Assays.Erasure` (4 assay ids) re-checks the machinery through an injectable op-map seam. A new `Antigen.Generators.ErasureTerm` produces fixed catalogs of Core terms + mixed-quantity envs. Wired via `assay_module/1` + a dedicated test — the established fixed-catalog pattern, no Corpus/Coverage surgery.

**Tech Stack:** Elixir; ExUnit (`async: true`); no new deps; `MIX_ENV=test` for all mix invocations (dev env crashes).

## Global Constraints

- **Ghost-authored commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`; NEVER a `Co-Authored-By` trailer.
- **Branch:** stay on `autopilot/antigen-tier-b` (no new worktree).
- **No `Cure.Core.*` / `Cure.Elab.*` edits.** Reached read-only through the op-map. No `:meck`, no new dependency. **In particular: do NOT fix the `erase/2` non-idempotence bug** — V4 *finds*, it does not patch (spec §7); the fix is a separate, separately-authorized change.
- **StreamData quarantine:** `lib/antigen/assays/erasure.ex` must contain NO literal `StreamData` token — moduledoc/comments included (V1 tripped on a comment).
- **Assay `run/1,2` returns only `:ok | {:violation, term()}`** — no third outcome kind.
- **No `@assay_fuel`/`Conv`** — `erase`/`has_hole?`/`check` are static structural walks; no term is evaluated.
- **One build/test run at any moment.** Tests immutable once written. Run mix from the worktree root.

## Reconciliations with the spec (resolved deviations, for the reviewer)

1. **The known `erase/2` non-idempotence finding is asserted as a violation in a
   DEDICATED test, and its terms are NOT members of the `erase_challenges/0`
   catalog sweep.** The spec (§3, §9-2/§9-3) requires exercising an
   erased-before-present quantity ordering, which — traced against source — makes
   the real `erase` non-idempotent (`Enum.zip` re-aligns the full-length quantity
   vector against the shrunk args on the second pass). This plan honors the
   spec's non-vacuity requirement by building those exact terms and **asserting
   `run(t) == {:violation, {:erase_not_idempotent, _}}`** (a true-positive: the
   assay correctly catches the bug), in a dedicated `describe "known erase/2
   non-idempotence finding"` block. They are kept OUT of `erase_challenges/0` so
   the "whole clean catalog is `:ok`" wiring test (Task 5) stays all-`:ok`, exactly
   as in every prior vertical. This is NOT weakening or dodging (spec §6): the
   finding is fully exercised, explicitly asserted, and headlined in the Stage-6
   report — it is simply asserted at its true verdict rather than pretended to be
   `:ok`. Stopping the whole vertical would be over-reaction for a dormant,
   non-TCB, spec-review-confirmed defect the operator will review in the report.
2. **Selective-drop terms use LEAF args, so the differential compares raw
   present-position args with no recursive erase.** If the selective oracle
   recursively erased kept args via the injected `k.erase`, a weakened `erase`
   negative control would corrupt BOTH the oracle and the actual output equally
   (self-consistent, undetectable — the V2 fixpoint lesson). Using leaf args
   (`{:int_lit, n}` / `{:var, k}`, which `erase` passes through unchanged) means
   the oracle is just "the original args at `:present` positions" — no `k.erase`
   call in the oracle — so a drop-present `erase` stub is genuinely caught.
3. **Fixed catalog + `:erasure_term` kind** (spec §8-4). Add a `:erasure_term`
   kind (typespec-only); `Runner.assay_module/1` gets four explicit clauses (it
   has no catch-all — an unmatched id raises `FunctionClauseError`). New atoms
   added to `Challenge.@known_atoms`. No `to_pieces`/`from_pieces` (catalog
   replayed from the generator function, not banked).

## File structure

- **New** `lib/antigen/assays/erasure.ex` — `Antigen.Assays.Erasure`; `run/1`+`run/2` for the 4 ids; `@real` op-map; local `present_args/2` + `app_spine/2`.
- **New** `lib/antigen/generators/erasure_term.ex` — `erase_challenges/0`, `relevance_challenges/0`; mixed-quantity env builders.
- **Modify** `lib/antigen/runner.ex` — 4 `assay_module/1` clauses.
- **Modify** `lib/antigen/challenge.ex` — add `:erasure_term` to `@type kind`; add new atoms to `@known_atoms`.
- **New** `test/antigen/assays/erasure_test.exs` — all tests (incl. the dedicated known-finding block).

## Interfaces (verified against source)

- `Cure.Elab.Erase.erase(env, term) :: term`; `Cure.Elab.Erase.has_hole?(term) :: boolean`.
- `Cure.Elab.Relevance.check(env, name, quantities, body) :: :ok | {:error, {:erased_used_relevantly, %{def, binder, site}}}`; `site ∈ {:returned, :present_arg, :scrutinee, :applied}`; `quantities` is a flat list indexed by parameter position.
- `Cure.Core.Inductive`: `declare(env, family, ctors)`; `family(name, params, indices, level)`; `ctor(name, arg_tele, result_indices, quantities)` (arity-4, explicit quantities, no arity check); `ctor_quantities(env, cname) :: [:present|:erased] | nil`.
- `Cure.Core.Env`: `empty/0`; `add_def(env, name, type, body, quantities)` (arity-5, per-param quantities); `get_def(env, name) :: %{quantities: …} | nil`.
- `Cure.Core.Term.term?(term) :: boolean` (shape-only; `lib/cure/core/term.ex:51`).

## Shared env + term helpers (test + generator)

```elixir
alias Cure.Core.{Env, Inductive}
defp il(n), do: {:int_lit, n}                     # leaf
# ctor :MkQ present-first [:present,:erased]  (erase idempotent — CLEAN)
# ctor :MkP erased-first  [:erased,:present]  (erase NON-idempotent — the finding)
defp ctor_env do
  Env.empty()
  |> Inductive.declare(Inductive.family(:P, [], [], 0), [
       Inductive.ctor(:MkQ, [{:a, {:int_type}}, {:b, {:int_type}}], [], [:present, :erased]),
       Inductive.ctor(:MkP, [{:a, {:int_type}}, {:b, {:int_type}}], [], [:erased, :present])
     ])
end
# app-head defs: f present-first (clean), g erased-first (the finding)
defp app_env(env) do
  ty = {:pi, {:int_type}, {:pi, {:int_type}, {:int_type}}}   # Int -> Int -> Int
  env
  |> Env.add_def(:f, ty, {:int_lit, 0}, [:present, :erased])
  |> Env.add_def(:g, ty, {:int_lit, 0}, [:erased, :present])
end
defp app2(head, x0, x1), do: {:app, {:app, head, x0}, x1}
```

---

### Task 1: `Antigen.Assays.Erasure` — `erasure/idempotent` (V4a: idempotence + hole preservation)

**Files:** Create `lib/antigen/assays/erasure.ex`; Create `test/antigen/assays/erasure_test.exs`.

- [ ] **Step 1: Write failing tests**

```elixir
defmodule Antigen.Assays.ErasureTest do
  use ExUnit.Case, async: true
  alias Antigen.{Assays.Erasure, Challenge}
  alias Antigen.Generators.ErasureTerm
  alias Cure.Core.{Env, Inductive}

  defp il(n), do: {:int_lit, n}
  defp ctor_env do
    Env.empty()
    |> Inductive.declare(Inductive.family(:P, [], [], 0), [
         Inductive.ctor(:MkQ, [{:a, {:int_type}}, {:b, {:int_type}}], [], [:present, :erased]),
         Inductive.ctor(:MkP, [{:a, {:int_type}}, {:b, {:int_type}}], [], [:erased, :present])
       ])
  end

  defp idem_ch(env, t) do
    Challenge.new(kind: :erasure_term, assay: "erasure/idempotent", label: :positive,
      payload: %{env: env, term: t}, seed: 1)
  end

  # app-head defs: f present-first (clean), g erased-first (the finding). Defined
  # once here at module level (NOT re-declared by Task 2's describe block) so both
  # this task's app-head known-finding test and Task 2's selective tests share it.
  defp app_env(env) do
    ty = {:pi, {:int_type}, {:pi, {:int_type}, {:int_type}}}
    env
    |> Env.add_def(:f, ty, {:int_lit, 0}, [:present, :erased])
    |> Env.add_def(:g, ty, {:int_lit, 0}, [:erased, :present])
  end
  defp app2(head, x0, x1), do: {:app, {:app, head, x0}, x1}

  test "idempotent baseline: present-first ctor erases idempotently" do
    env = ctor_env()
    assert Erasure.run(idem_ch(env, {:ctor, :MkQ, [il(1), il(2)]})) == :ok
  end

  test "hole-preservation baseline: a hole-free term stays hole-free after erase" do
    env = ctor_env()
    assert Erasure.run(idem_ch(env, {:ctor, :MkQ, [il(1), il(2)]})) == :ok
  end

  test "idempotent negative control: a wrapping erase stub is not a fixpoint" do
    env = ctor_env()
    k = %{Erasure.__real__() | erase: fn _e, t -> {:ctor, :Wrap, [t]} end}
    assert {:violation, {:erase_not_idempotent, _}} = Erasure.run(idem_ch(env, {:ctor, :MkQ, [il(1), il(2)]}), k)
  end

  test "hole negative control: an erase stub that introduces a hole is caught" do
    env = ctor_env()
    k = %{Erasure.__real__() | erase: fn _e, _t -> {:hole, :x} end}
    assert {:violation, {:hole_introduced, _}} = Erasure.run(idem_ch(env, {:ctor, :MkQ, [il(1), il(2)]}), k)
  end

  describe "known erase/2 non-idempotence finding (spec §3, §9-2/§9-3)" do
    # These terms are NOT in erase_challenges/0 (reconciliation #1). The assay is
    # CORRECT — it reports the real erase's non-idempotence as a violation. This
    # documents a genuine, spec-review-traced, currently-dormant erase/2 defect.
    test "ctor erased-before-present ordering: real erase is non-idempotent (TRUE POSITIVE)" do
      env = ctor_env()
      assert {:violation, {:erase_not_idempotent, _}} = Erasure.run(idem_ch(env, {:ctor, :MkP, [il(1), il(2)]}))
    end

    # Second surface (spec §3/§9-item-3): the app-head clause has the identical
    # zip-realignment hazard as the :ctor clause. `g`'s quantities are
    # [:erased, :present]; once = erase(env, app2(g,1,2)) = {:app,{:global,g},il(2)}
    # (arg 0 dropped, arg 1 kept); twice re-erases from a 1-arg spine against the
    # SAME full 2-element quantity vector, re-zipping the survivor to qs[0] =
    # :erased and dropping it -> {:global, g} (bare head, no args). This is the
    # app-head counterpart to the ctor finding above — NOT a member of
    # erase_challenges/0 (Task 5), for the same reason.
    test "app-head erased-before-present ordering: real erase is non-idempotent (TRUE POSITIVE)" do
      env = app_env(ctor_env())
      assert {:violation, {:erase_not_idempotent, _}} =
               Erasure.run(idem_ch(env, app2({:global, :g}, il(1), il(2))))
    end
  end
end
```

- [ ] **Step 2: RED** — `MIX_ENV=test mix test test/antigen/assays/erasure_test.exs` → FAIL (module undefined).

- [ ] **Step 3: Implement** — Create `lib/antigen/assays/erasure.ex`:

```elixir
defmodule Antigen.Assays.Erasure do
  @moduledoc """
  Property tests for the untrusted {0,ω} erasure/relevance machinery
  `Cure.Elab.Erase` / `Cure.Elab.Relevance` (spec: antigen-erasure-relevance).

    * erasure/idempotent — `erase∘erase == erase` + hole preservation (V4a).
    * erasure/selective  — erase keeps exactly the :present positions (ctor + app-head).
    * erasure/wellformed — `term?(t) ⟹ term?(erase t)`.
    * relevance/soundness — an :erased binder used relevantly must be rejected.

  Machinery ops go through an injectable @real map (run/2); negative controls
  weaken the code-under-test without touching `Cure.Elab`/`Cure.Core` or :meck.
  """
  alias Antigen.Challenge
  alias Cure.Elab.{Erase, Relevance}
  alias Cure.Core.{Inductive, Env, Term}

  @real %{
    erase: &Erase.erase/2,
    has_hole?: &Erase.has_hole?/1,
    ctor_quantities: &Inductive.ctor_quantities/2,
    get_def: &Env.get_def/2,
    term?: &Term.term?/1,
    relevance_check: &Relevance.check/4
  }
  @doc false
  def __real__, do: @real

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :erasure_term} = c), do: run(c, @real)

  def run(%Challenge{kind: :erasure_term, assay: "erasure/idempotent", payload: %{env: env, term: t}}, k) do
    once = k.erase.(env, t)
    twice = k.erase.(env, once)

    cond do
      k.has_hole?.(t) == false and k.has_hole?.(once) == true -> {:violation, {:hole_introduced, t}}
      twice != once -> {:violation, {:erase_not_idempotent, t}}
      true -> :ok
    end
  end
end
```

- [ ] **Step 4: GREEN** — `MIX_ENV=test mix test test/antigen/assays/erasure_test.exs` → PASS (6). Both known-finding tests (ctor `:MkP`, app-head `:g`) pass because the assay correctly returns `{:violation, {:erase_not_idempotent, _}}` on the real non-idempotent erase for each surface. If either present-first baseline instead fails, trace `Inductive.ctor_quantities(env, :MkQ)` / `Env.get_def(env, :f)` and the erase output — the clean ordering must be genuinely idempotent on both surfaces.

- [ ] **Step 5: Commit** — `feat(antigen): erasure/idempotent assay — erase idempotence + hole preservation (finds erase/2 non-idempotence, ctor + app-head)`

---

### Task 2: `erasure/selective` (V4a: ctor + app-head differential vs quantities)

**Files:** Modify `lib/antigen/assays/erasure.ex`; append tests.

- [ ] **Step 1: Write failing tests**

```elixir
describe "erasure/selective (V4a)" do
  # `app_env/1` and `app2/3` are already defined at module level by Task 1 (it
  # needs the fuller version — both `:f` and `:g` — for its app-head
  # known-finding test); reused here as-is. Do NOT redeclare them in this
  # `describe` block — a second `defp app_env(env)`/`defp app2(h,x0,x1)` clause
  # with the same head shape would just add an unreachable duplicate clause.
  defp sel_ch(env, t, surface) do
    Challenge.new(kind: :erasure_term, assay: "erasure/selective", label: :positive,
      payload: %{env: env, term: t, surface: surface}, seed: 1)
  end

  test "ctor selective baseline: keeps exactly the :present positions (leaf args)" do
    env = ctor_env()
    assert Erasure.run(sel_ch(env, {:ctor, :MkQ, [il(1), il(2)]}, :ctor)) == :ok
  end

  test "app-head selective baseline: keeps exactly the :present def positions (leaf args)" do
    env = app_env(ctor_env())
    assert Erasure.run(sel_ch(env, app2({:global, :f}, il(1), il(2)), :app)) == :ok
  end

  test "ctor selective negative control: an erase stub dropping the :present position" do
    env = ctor_env()
    k = %{Erasure.__real__() | erase: fn _e, {:ctor, c, _args} -> {:ctor, c, []} end}
    assert {:violation, {:wrong_positions_kept, :MkQ}} = Erasure.run(sel_ch(env, {:ctor, :MkQ, [il(1), il(2)]}, :ctor), k)
  end

  test "app-head selective negative control: an erase stub dropping a :present arg" do
    env = app_env(ctor_env())
    k = %{Erasure.__real__() | erase: fn _e, _t -> {:global, :f} end}  # drops all args
    assert {:violation, {:wrong_positions_kept, :f}} = Erasure.run(sel_ch(env, app2({:global, :f}, il(1), il(2)), :app), k)
  end
end
```

- [ ] **Step 2: RED.**

- [ ] **Step 3: Implement** — add to `erasure.ex`:

```elixir
def run(%Challenge{kind: :erasure_term, assay: "erasure/selective", payload: %{env: env, term: {:ctor, c, args} = t, surface: :ctor}}, k) do
  qs = k.ctor_quantities.(env, c) || List.duplicate(:present, length(args))
  expected = present_args(args, qs)             # ORIGINAL args at :present positions (leaf -> erase is identity)
  case k.erase.(env, t) do
    {:ctor, ^c, kept} when kept == expected -> :ok
    _ -> {:violation, {:wrong_positions_kept, c}}
  end
end

def run(%Challenge{kind: :erasure_term, assay: "erasure/selective", payload: %{env: env, term: t, surface: :app}}, k) do
  {head, args} = app_spine(t, [])
  {:global, name} = head
  qs = case k.get_def.(env, name) do
    %{quantities: q} when is_list(q) -> q
    _ -> List.duplicate(:present, length(args))
  end
  padded = qs ++ List.duplicate(:present, max(0, length(args) - length(qs)))
  expected = present_args(args, padded)
  {_h, kept} = app_spine(k.erase.(env, t), [])
  if kept == expected, do: :ok, else: {:violation, {:wrong_positions_kept, name}}
end

defp present_args(args, qs) do
  args |> Enum.zip(qs) |> Enum.filter(fn {_a, q} -> q == :present end) |> Enum.map(fn {a, _q} -> a end)
end

# collect an application spine head + args (left-to-right), mirroring Erase.spine/2
defp app_spine({:app, f, x}, acc), do: app_spine(f, [x | acc])
defp app_spine(head, acc), do: {head, acc}
```

> Selective terms use LEAF args (`{:int_lit, _}`), which `erase` passes through unchanged (reconciliation #2), so `expected` (raw present-position args) equals `erase`'s kept args with no recursive-erase call in the oracle — the drop-present negative control is genuinely distinguishable.

- [ ] **Step 4: GREEN.** **Step 5: Commit** — `feat(antigen): erasure/selective assay — keeps exactly :present positions (ctor + app-head)`

---

### Task 3: `erasure/wellformed` (V4a: `term?` preservation)

**Files:** Modify `lib/antigen/assays/erasure.ex`; append tests.

- [ ] **Step 1: Write failing tests**

```elixir
describe "erasure/wellformed (V4a)" do
  defp wf_ch(env, t) do
    Challenge.new(kind: :erasure_term, assay: "erasure/wellformed", label: :positive,
      payload: %{env: env, term: t}, seed: 1)
  end

  test "baseline: term?(t) => term?(erase t)" do
    env = ctor_env()
    assert Erasure.run(wf_ch(env, {:ctor, :MkQ, [il(1), il(2)]})) == :ok
  end

  test "negative control: an erase stub returning a malformed term" do
    env = ctor_env()
    k = %{Erasure.__real__() | erase: fn _e, _t -> {:not_a_node, :garbage, 999} end}
    assert {:violation, {:erase_ill_formed, _}} = Erasure.run(wf_ch(env, {:ctor, :MkQ, [il(1), il(2)]}), k)
  end
end
```

- [ ] **Step 2: RED.**

- [ ] **Step 3: Implement** — add to `erasure.ex`:

```elixir
def run(%Challenge{kind: :erasure_term, assay: "erasure/wellformed", payload: %{env: env, term: t}}, k) do
  # only meaningful on inputs that are themselves well-formed
  if k.term?.(t) and not k.term?.(k.erase.(env, t)) do
    {:violation, {:erase_ill_formed, t}}
  else
    :ok
  end
end
```

> Confirm `Term.term?/1` returns `false` on `{:not_a_node, :garbage, 999}` (an unknown tag) — if `term?` is total and rejects unknown tags, the negative control fires. If `term?` raises on unknown shapes instead of returning false, wrap the malformed-output stub to return a shape `term?` recognizes as invalid (e.g. `{:type, 99}` — universe level above the ceiling), which `term?` checks explicitly.

- [ ] **Step 4: GREEN.** **Step 5: Commit** — `feat(antigen): erasure/wellformed assay — term? preserved under erase`

---

### Task 4: `relevance/soundness` (V4b: four sites + clean control)

**Files:** Modify `lib/antigen/assays/erasure.ex`; append tests.

- [ ] **Step 1: Write failing tests** — one rejected body per site + clean control + negative control:

```elixir
describe "relevance/soundness (V4b)" do
  # quantities = [:erased] — binder 0 is erased; a body using {:var, 0} relevantly must be rejected.
  defp rel_ch(env, body, site) do
    Challenge.new(kind: :erasure_term, assay: "relevance/soundness", label: :negative,
      payload: %{env: env, name: :d, quantities: [:erased], body: body, site: site}, seed: 1)
  end

  test "returned site: erased binder is the body result — rejected" do
    assert Erasure.run(rel_ch(Env.empty(), {:var, 0}, :returned)) == :ok
  end

  test "applied site: erased binder applied as a function head — rejected" do
    assert Erasure.run(rel_ch(Env.empty(), {:app, {:var, 0}, {:int_lit, 0}}, :applied)) == :ok
  end

  test "scrutinee site: erased binder matched in a case — rejected" do
    assert Erasure.run(rel_ch(Env.empty(), {:case, {:var, 0}, {:int_lit, 0}, []}, :scrutinee)) == :ok
  end

  test "present_arg site: erased binder passed in a :present ctor position — rejected" do
    env = ctor_env()
    # MkQ position 0 is :present; putting {:var,0} there is a relevant use of an erased binder
    assert Erasure.run(rel_ch(env, {:ctor, :MkQ, [{:var, 0}, {:int_lit, 0}]}, :present_arg)) == :ok
  end

  test "clean-body control: erased binder unused is accepted" do
    ch = Challenge.new(kind: :erasure_term, assay: "relevance/soundness", label: :positive,
      payload: %{env: Env.empty(), name: :d, quantities: [:erased], body: {:int_lit, 7}, site: nil}, seed: 1)
    assert Erasure.run(ch) == :ok
  end

  test "negative control: a relevance_check stub that accepts a relevant body" do
    k = %{Erasure.__real__() | relevance_check: fn _e, _n, _q, _b -> :ok end}
    assert {:violation, {:relevance_unsound, :returned}} = Erasure.run(rel_ch(Env.empty(), {:var, 0}, :returned), k)
  end

  test "clean-body negative control: a relevance_check stub that rejects a clean body" do
    ch = Challenge.new(kind: :erasure_term, assay: "relevance/soundness", label: :positive,
      payload: %{env: Env.empty(), name: :d, quantities: [:erased], body: {:int_lit, 7}, site: nil}, seed: 1)
    k = %{Erasure.__real__() | relevance_check: fn _e, _n, _q, _b ->
      {:error, {:erased_used_relevantly, %{def: :d, binder: 0, site: :returned}}}
    end}
    assert {:violation, {:clean_body_rejected, :d}} = Erasure.run(ch, k)
  end

  test "wrong-site negative control: a relevance_check stub reporting a mismatched site" do
    k = %{Erasure.__real__() | relevance_check: fn _e, _n, _q, _b ->
      {:error, {:erased_used_relevantly, %{def: :d, binder: 0, site: :applied}}}
    end}
    assert {:violation, {:relevance_wrong_site, :returned, :applied}} =
             Erasure.run(rel_ch(Env.empty(), {:var, 0}, :returned), k)
  end
end
```

- [ ] **Step 2: RED.**

- [ ] **Step 3: Implement** — add to `erasure.ex` (clean control has `site: nil`):

```elixir
def run(%Challenge{kind: :erasure_term, assay: "relevance/soundness", payload: %{env: env, name: n, quantities: qs, body: body, site: nil}}, k) do
  case k.relevance_check.(env, n, qs, body) do
    :ok -> :ok
    {:error, _} -> {:violation, {:clean_body_rejected, n}}
  end
end

def run(%Challenge{kind: :erasure_term, assay: "relevance/soundness", payload: %{env: env, name: n, quantities: qs, body: body, site: site}}, k) do
  case k.relevance_check.(env, n, qs, body) do
    {:error, {:erased_used_relevantly, %{site: ^site}}} -> :ok
    {:error, {:erased_used_relevantly, %{site: other}}} -> {:violation, {:relevance_wrong_site, site, other}}
    :ok -> {:violation, {:relevance_unsound, site}}
  end
end
```

> If a site's expected classification differs from what `Relevance.walk/4` actually reports (spec §8-2 traced them, but confirm at GREEN), the `:relevance_wrong_site` branch fires and names the actual site — adjust the catalog's `site` field to the real classification (this is fixing the test's *expectation of the oracle*, not weakening the property; the property "a relevant use is rejected" still holds, only the site label is corrected). Do this only if GREEN reveals a mismatch.

- [ ] **Step 4: GREEN.** **Step 5: Commit** — `feat(antigen): relevance/soundness assay — erased-binder-used-relevantly rejection across four sites`

---

### Task 5: `ErasureTerm` catalogs + runner wiring + atoms

**Files:** Create `lib/antigen/generators/erasure_term.ex`; Modify `lib/antigen/runner.ex`, `lib/antigen/challenge.ex`; append tests.

- [ ] **Step 1: Write failing tests**

```elixir
describe "generator + runner wiring" do
  alias Antigen.Runner

  test "each catalog is non-empty and correctly tagged" do
    assert ErasureTerm.erase_challenges() != []
    assert ErasureTerm.relevance_challenges() != []
    ids = MapSet.new(ErasureTerm.erase_challenges(), & &1.assay)
    assert "erasure/idempotent" in ids and "erasure/selective" in ids and "erasure/wellformed" in ids
    assert Enum.all?(ErasureTerm.relevance_challenges(), & &1.assay == "relevance/soundness")
  end

  test "runner dispatches all four ids and the whole clean catalog is :ok" do
    all = ErasureTerm.erase_challenges() ++ ErasureTerm.relevance_challenges()
    assert Enum.all?(all, fn c -> Runner.replay_one(c) == :ok end)
  end
end
```

- [ ] **Step 2: RED** — `ErasureTerm` undefined; `assay_module("erasure/idempotent")` no clause.

- [ ] **Step 3: Implement** —

Create `lib/antigen/generators/erasure_term.ex` with the env builders (`ctor_env`, `app_env` — the fuller version registering both `:f` and `:g`, matching Task 1) and:
- `erase_challenges/0` — ONLY entries expected `:ok` under real ops (reconciliation #1): present-first ctor idempotent + hole; present-first app-head idempotent; ctor + app-head selective (leaf args); a `term?` wellformed entry. **NOT** the erased-first `:MkP`/`:g` terms (those are dedicated known-finding test fixtures in Task 1 — §"known erase/2 non-idempotence finding", which now covers both the ctor and app-head surfaces — not catalog members).
- `relevance_challenges/0` — the four per-site rejected bodies (§8-2 constructions) + the clean control.

In `lib/antigen/runner.ex` add four `assay_module/1` clauses → `Antigen.Assays.Erasure`. In `lib/antigen/challenge.ex` add `| :erasure_term` to `@type kind` and add `:erasure_term, :P, :MkQ, :MkP, :f, :g, :d, :a, :b, :Wrap` to `@known_atoms` (skip any already present — verify against the current list).

- [ ] **Step 4: GREEN.** If a catalog entry unexpectedly fails, trace it — a real infection on a supposedly-clean entry is a NEW finding (STOP and report); a construction error is a generator fix.

- [ ] **Step 5: Commit** — `feat(antigen): ErasureTerm catalogs + erasure/* runner dispatch`

---

### Task 6: Full-suite verification + finding report

- [ ] **Step 1:** `MIX_ENV=test mix test test/antigen/assays/erasure_test.exs` — all green (incl. the known-finding assertion).
- [ ] **Step 2:** `MIX_ENV=test mix test test/antigen/architecture_test.exs` — quarantine green.
- [ ] **Step 3:** `MIX_ENV=test mix test` (single authorized run) — all pass; count = prior + new rows.
- [ ] **Step 4:** `git status --short`; revert `test/antigen/seeds.sexp` if touched; confirm clean. No commit here (the Stage-6 report commit is part of autopilot Stage 5, and MUST headline the `erase/2` non-idempotence finding: what it is, that it is dormant (erase called once per body), that erasure.ex is not TCB, and that V4 reports rather than patches it).

## Self-review

**Spec coverage:** §3 V4a idempotence+hole → Task 1 (+ known-finding block, BOTH ctor `:MkP` and app-head `:g` surfaces per §9 item 3); selective (ctor+app-head) → Task 2; wellformed → Task 3; §3 V4b four sites+clean → Task 4 (+ `:relevance_wrong_site`/`:clean_body_rejected` negative controls); §4 op-map seam → Task 1 `@real`; §4 negative controls → each task, every violation branch has a dedicated negative control (`:erase_not_idempotent`, `:hole_introduced`, `:wrong_positions_kept` ×2 surfaces, `:erase_ill_formed`, `:relevance_unsound`, `:relevance_wrong_site`, `:clean_body_rejected`); §5 catalogs + mixed-quantity registration → Task 5 (+ shared helpers); §6 invariants (no engine edits/fix, no StreamData token, `:ok|{:violation}` only, known-finding handling per reconciliation #1); §7 non-goals (no fix, no elab/erasure dup, no kernel-accept differential, no {0,ω} change); §8-1/§8-2/§8-3/§8-4 resolved (Inductive.ctor/4 + add_def/5; per-site constructions; term?/1; :erasure_term kind + assay_module clauses); §9 tests 1-15 distributed across Tasks 1-5, including item 3's app-head erased-first sub-case (Task 1).

**Placeholder scan:** none — concrete code/commands throughout. Two GREEN-time contingencies named with explicit fallbacks (Term.term? on unknown tags → use a level-overflow shape; a site-classification mismatch → correct the catalog's `site` label, not the property).

**Type consistency:** op-map keys `erase/has_hole?/ctor_quantities/get_def/term?/relevance_check` identical in `@real` and every control. Infection tags `{:erase_not_idempotent,…}`, `{:hole_introduced,…}`, `{:wrong_positions_kept,…}`, `{:erase_ill_formed,…}`, `{:relevance_unsound,…}`, `{:relevance_wrong_site,…}`, `{:clean_body_rejected,…}` consistent code↔tests. Payload shapes: idempotent/wellformed `%{env, term}`, selective `%{env, term, surface}`, relevance `%{env, name, quantities, body, site}` — each produced by its catalog and consumed by its `run` clause.
