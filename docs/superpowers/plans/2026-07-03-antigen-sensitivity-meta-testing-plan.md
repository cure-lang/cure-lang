# Antigen Sensitivity Meta-Testing — Implementation Plan (Run C)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans. Steps use `- [ ]` checkboxes.

**Goal:** Prove Antigen's assays are *sensitive* — that a green run is load-bearing — by running the real assays against deliberately weakened kernels (one rule made too-permissive) and characterizing, per weakening, whether an assay fires an infection (a **sensitivity coverage matrix**).

**Architecture:** A new `Antigen.Meta.WeakKernel` supplies named one-rule weakenings as a kernel-op map (`real/0` = the identity/real map; `weaken/1` = `real/0` with one key overridden by a permissive stub). Five soundness-relevant assays gain an **additive** `run/2` that reads its kernel ops from an injected map (private `@real_kernel` subset as the `run/1` default — byte-identical behavior); `mutation` already has such a seam. A meta-test drives 8 catalog rows, each a baseline (real kernel → sound verdict) + weakened (→ expected cell) assertion pair.

**Tech Stack:** Elixir; `Cure.Core.{Kernel, Conv, Inductive, Eval}`; `Antigen.{Challenge, Assays.*, Generators.*, Meta.WeakKernel}`.

## Global Constraints

- Ghost-authored commits: `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, **no** `Co-Authored-By` / co-sign trailer.
- `MIX_ENV=test mix test …` (dev env crashes); macOS has no `timeout`; **one build/test run at a time** (never concurrent — a past concurrent full-suite run caused a kernel panic).
- **No `Cure.Core.*` (TCB) edits** — only read-only calls into its public API. **No `:meck`, no new dependency.**
- **No `StreamData` literal** under `lib/antigen/generators/` or `lib/antigen/assays/` (grep-enforced by `test/antigen/architecture_test.exs`; its glob is `lib/antigen/{generators,assays}/**/*.ex`, so `lib/antigen/meta/` is outside it — `WeakKernel` need not avoid the literal, though it contains none regardless).
- **Seams are additive + behavior-preserving:** every touched assay keeps its existing `run/1` byte-identical (it delegates to the new `run/2` with the assay's private `@real_kernel`). The seam only *adds* an arity/clause. The regression guard is the existing suite passing unchanged.
- Tests immutable once correct (change impl, not the test).
- Assays carry their own `@real_kernel` subset map and do **not** reference `WeakKernel` — no production dependency on the meta module.

### The kernel-op map (shared shape)

`WeakKernel.real/0` returns the full map; each assay reads only the keys it uses (a weakened map is a superset, so reading a subset always succeeds):

```
%{
  infer:        &Cure.Core.Kernel.infer/2,       # (ctx, term) -> {:ok, Value} | {:error, _}
  check:        &Cure.Core.Kernel.check/3,       # (ctx, term, type_value) -> :ok | {:error, _}
  conv_within:  &Cure.Core.Conv.conv_within?/6,  # (t, t', val_env, depth, sig_env, fuel) -> {:ok, bool} | :fuel_exhausted
  positive?:    &Cure.Core.Inductive.positive?/2,# (env, family) -> :ok | {:error, _}
  check_def:    &Cure.Core.Kernel.check_def/2,   # (env, def_name) -> :ok | {:error, _}
  check_family: &Cure.Core.Kernel.check_family/2,# (env, family) -> :ok | {:error, _}
  check_ctor:   &Cure.Core.Kernel.check_ctor/3   # (env, family, ctor) -> :ok | {:error, _}
}
```

### The 8-row catalog (fixed, hand-built fixtures; every row = baseline + weakened)

| # | weakening key | target assay | fixture | baseline (real) | weakened outcome | cell |
|---|---|---|---|---|---|---|
| 1 | `:infer_accepts_all` | `Mutation` (existing `run/2`) | ill-typed `:mutant_term`, term `{:app, Z, Z}` | `:ok` | `{:violation, {:accepted_ill_typed, …}}` | CAUGHT |
| 2 | `:infer_wrong_type` | `Term` `term/infer_check` | well-typed `:typed_term`, term `S(Z)` : Nat | `:ok` | `{:violation, {:check_disagrees, …}}` | CAUGHT |
| 3 | `:check_accepts_all` | `Term` `term/infer_check` | same `S(Z)` term | `:ok` | `:ok` | SLIP (gap) |
| 4 | `:positive_accepts_all` | `Positivity` | `Generators.Positivity.negative_family/0` | `:ok` | `{:violation, {:wrongly_accepted, :Bad}}` | CAUGHT |
| 5 | `:universe_accepts_all` | `Universes` | `Generators.Universes.type_in_type(:ill_typed)` | `:ok` | `{:violation, {:wrongly_accepted, :u}}` | CAUGHT |
| 6 | `:conv_always_true` | `StuckElimDelta` | hand-built negative `:stuck_elim`, `(t,t') = (Z, S(Z))`, empty env | `:ok` | `{:violation, {:unsound_verdict, …}}` | CAUGHT |
| 7 | `:conv_always_true` | `Reflexivity` | `Generators.Forcing.forcing_pair/0` | `:ok` | `:ok` | SLIP (by design — verdict-blind) |
| 8 | `:conv_exhausts_fuel` | `Reflexivity` | same `forcing_pair` | `:ok` | `{:violation, {:non_normalizing, …}}` | CAUGHT |

`:universe_accepts_all` overrides all three `check_*` keys (spec §3); every other weakening overrides exactly one key.

---

## Task 1: `Antigen.Meta.WeakKernel` — real map + named weakenings

**Files:** Create `lib/antigen/meta/weak_kernel.ex`; Test `test/antigen/meta/weak_kernel_test.exs`.

**Interfaces:**
- Produces: `WeakKernel.real() :: map()` (7 keys → real kernel captures); `WeakKernel.weaken(atom()) :: map()` (real/0 with one key — or the three `check_*` keys for `:universe_accepts_all` — overridden by a permissive stub). Consumes `Cure.Core.{Kernel, Conv, Inductive, Eval}`.

- [ ] **Step 1: Write the failing test** — create `test/antigen/meta/weak_kernel_test.exs`:

```elixir
defmodule Antigen.Meta.WeakKernelTest do
  use ExUnit.Case, async: true
  alias Antigen.Meta.WeakKernel

  @single [
    infer_accepts_all: :infer,
    infer_wrong_type: :infer,
    check_accepts_all: :check,
    positive_accepts_all: :positive?,
    conv_always_true: :conv_within,
    conv_exhausts_fuel: :conv_within
  ]

  test "real/0 maps each op to the real kernel capture" do
    r = WeakKernel.real()
    assert r.infer == (&Cure.Core.Kernel.infer/2)
    assert r.check == (&Cure.Core.Kernel.check/3)
    assert r.conv_within == (&Cure.Core.Conv.conv_within?/6)
    assert r.positive? == (&Cure.Core.Inductive.positive?/2)
    assert r.check_def == (&Cure.Core.Kernel.check_def/2)
    assert r.check_family == (&Cure.Core.Kernel.check_family/2)
    assert r.check_ctor == (&Cure.Core.Kernel.check_ctor/3)
  end

  test "each single-key weakening overrides exactly its key, leaving the rest real" do
    r = WeakKernel.real()
    for {name, mapkey} <- @single do
      w = WeakKernel.weaken(name)
      refute Map.fetch!(w, mapkey) == Map.fetch!(r, mapkey)
      for {k, v} <- r, k != mapkey, do: assert(Map.fetch!(w, k) == v)
    end
  end

  test "universe_accepts_all overrides all three check_* keys, leaving the rest real" do
    r = WeakKernel.real()
    w = WeakKernel.weaken(:universe_accepts_all)
    for k <- [:check_def, :check_family, :check_ctor], do: refute(Map.fetch!(w, k) == Map.fetch!(r, k))
    for k <- [:infer, :check, :conv_within, :positive?], do: assert(Map.fetch!(w, k) == Map.fetch!(r, k))
  end

  test "the permissive stubs behave as specified" do
    assert WeakKernel.weaken(:check_accepts_all).check.(:ctx, :t, :ty) == :ok
    assert WeakKernel.weaken(:positive_accepts_all).positive?.(:env, :fam) == :ok
    assert WeakKernel.weaken(:universe_accepts_all).check_def.(:env, :dn) == :ok
    assert WeakKernel.weaken(:universe_accepts_all).check_family.(:env, :fam) == :ok
    assert WeakKernel.weaken(:universe_accepts_all).check_ctor.(:env, :fam, :ctor) == :ok
    assert WeakKernel.weaken(:conv_always_true).conv_within.(1, 2, 3, 4, 5, 6) == {:ok, true}
    assert WeakKernel.weaken(:conv_exhausts_fuel).conv_within.(1, 2, 3, 4, 5, 6) == :fuel_exhausted
    # accept-all infer returns {:ok, _} even for a blatantly ill-typed term
    assert {:ok, _} = WeakKernel.weaken(:infer_accepts_all).infer.(Cure.Core.Context.empty(Cure.Core.Env.empty()), {:app, {:ctor, :Z, []}, {:ctor, :Z, []}})
  end
end
```

- [ ] **Step 2: Run — expect FAIL** (`MIX_ENV=test mix test test/antigen/meta/weak_kernel_test.exs`) — `Antigen.Meta.WeakKernel` undefined.

- [ ] **Step 3: Implement** — create `lib/antigen/meta/weak_kernel.ex`:

```elixir
defmodule Antigen.Meta.WeakKernel do
  @moduledoc """
  Sensitivity meta-testing support (Run C spec §3). `real/0` is the identity map:
  every kernel op bound to its real `Cure.Core.*` capture. `weaken/1` returns
  `real/0` with exactly one rule (or, for `:universe_accepts_all`, the three
  `check_*` rules) replaced by a deliberately **too-permissive** stub — a
  simulated soundness hole. The real kernel is never modified; weakenings are used
  only by the sensitivity meta-test, injected through each assay's `run/2` seam.
  """
  alias Cure.Core.{Kernel, Conv, Inductive, Eval}

  @spec real() :: map()
  def real do
    %{
      infer: &Kernel.infer/2,
      check: &Kernel.check/3,
      conv_within: &Conv.conv_within?/6,
      positive?: &Inductive.positive?/2,
      check_def: &Kernel.check_def/2,
      check_family: &Kernel.check_family/2,
      check_ctor: &Kernel.check_ctor/3
    }
  end

  @spec weaken(atom()) :: map()
  def weaken(:infer_accepts_all),
    do: %{real() | infer: fn _ctx, _t -> {:ok, Eval.eval({:type, 0}, [])} end}

  # real infer, but on success return a type value distinct from any well-typed
  # term's real type in the catalog fixture (Type 0 ≠ Nat), so a real `check`
  # against it disagrees. Passes kernel errors through untouched.
  def weaken(:infer_wrong_type) do
    %{real() | infer: fn ctx, t ->
        case Kernel.infer(ctx, t) do
          {:ok, _v} -> {:ok, Eval.eval({:type, 0}, [])}
          err -> err
        end
      end}
  end

  def weaken(:check_accepts_all), do: %{real() | check: fn _ctx, _t, _ty -> :ok end}
  def weaken(:positive_accepts_all), do: %{real() | positive?: fn _env, _fam -> :ok end}

  def weaken(:universe_accepts_all) do
    %{
      real()
      | check_def: fn _env, _dn -> :ok end,
        check_family: fn _env, _fam -> :ok end,
        check_ctor: fn _env, _fam, _ctor -> :ok end
    }
  end

  def weaken(:conv_always_true), do: %{real() | conv_within: fn _t, _tp, _e, _d, _s, _f -> {:ok, true} end}
  def weaken(:conv_exhausts_fuel), do: %{real() | conv_within: fn _t, _tp, _e, _d, _s, _f -> :fuel_exhausted end}
end
```

- [ ] **Step 4: Run — expect PASS** (`MIX_ENV=test mix test test/antigen/meta/weak_kernel_test.exs`).

- [ ] **Step 5: Commit**
```bash
git add lib/antigen/meta/weak_kernel.ex test/antigen/meta/weak_kernel_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): WeakKernel — real map + named one-rule kernel weakenings"
```

---

## Task 2: `Term` seam + rows 2 & 3 (infer_wrong_type CAUGHT / check_accepts_all SLIP)

**Files:** Modify `lib/antigen/assays/term.ex`; Create `test/antigen/meta/sensitivity_test.exs`.

**Interfaces:**
- Produces: `Term.run(challenge, kernel_map)` — same as `run/1` but every `Kernel.infer`/`Kernel.check` call reads from `kernel_map`. `run/1` delegates with the private `@real_kernel`.

- [ ] **Step 1: Write the failing test** — create `test/antigen/meta/sensitivity_test.exs`:

```elixir
defmodule Antigen.Meta.SensitivityTest do
  @moduledoc "Run C sensitivity matrix: real kernel → sound; weakened kernel → the catalog cell."
  use ExUnit.Case, async: true
  alias Antigen.Meta.WeakKernel
  alias Antigen.Challenge

  @nat {:data, :Nat, [], []}
  @z {:ctor, :Z, []}
  @sz {:ctor, :S, [{:ctor, :Z, []}]}

  # -- Rows 2 & 3: Term term/infer_check --------------------------------------
  defp typed_term_ch,
    do: Challenge.new(kind: :typed_term, assay: "term/infer_check", label: :well_typed,
                      payload: %{sig: :v1, ctx: [], type: @nat, term: @sz})

  test "row 2 — infer_wrong_type is CAUGHT by term/infer_check" do
    ch = typed_term_ch()
    assert :ok = Antigen.Assays.Term.run(ch, WeakKernel.real())
    assert {:violation, {:check_disagrees, _}} = Antigen.Assays.Term.run(ch, WeakKernel.weaken(:infer_wrong_type))
  end

  test "row 3 — check_accepts_all SLIPS past term/infer_check (documented gap)" do
    ch = typed_term_ch()
    assert :ok = Antigen.Assays.Term.run(ch, WeakKernel.real())
    # a consistency assay only ever calls `check` on the correctly-inferred type,
    # where :ok is the RIGHT answer — so an accept-all `check` is invisible to it.
    assert :ok = Antigen.Assays.Term.run(ch, WeakKernel.weaken(:check_accepts_all))
  end
end
```

- [ ] **Step 2: Run — expect FAIL** (`MIX_ENV=test mix test test/antigen/meta/sensitivity_test.exs`) — `Antigen.Assays.Term.run/2` undefined (only `run/1` exists).

- [ ] **Step 3: Implement** — in `lib/antigen/assays/term.ex`, thread a kernel map through. Add the module attribute (near `@assay_fuel`):

```elixir
  @real_kernel %{infer: &Kernel.infer/2, check: &Kernel.check/3}
```

Change `run/1` to delegate, and add `run/2` + `dispatch/5` (replacing the `dispatch/4` calls). The body is the current one with `Kernel.infer`/`Kernel.check` replaced by `k.infer`/`k.check`; all other calls (`Normalise`, `Conv`, `Serialize`, `Context`) stay direct:

```elixir
  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :typed_term} = c), do: run(c, @real_kernel)

  @doc "Same as `run/1` but with an injectable kernel-op map (sensitivity test seam)."
  def run(%Challenge{kind: :typed_term, assay: assay, payload: p}, k) do
    env = SigMenu.env_of(p.sig)
    ctx = SigMenu.rebuild_context(env, p.ctx)

    case k.infer.(ctx, p.term) do
      {:ok, inferred} -> dispatch(assay, ctx, p, inferred, k)
      {:error, e} -> {:violation, {:infer_failed, e}}
    end
  end

  defp dispatch("term/infer_check", ctx, p, inferred, k) do
    depth = Context.length(ctx)
    inferred_term = Normalise.quote(inferred, depth)

    cond do
      k.check.(ctx, p.term, inferred) != :ok ->
        {:violation, {:check_disagrees, k.check.(ctx, p.term, inferred)}}

      not converges?(inferred_term, p.type, ctx) ->
        {:violation, {:inferred_type_mismatch, inferred_term, p.type}}

      true -> :ok
    end
  end

  defp dispatch("term/subject_reduction", ctx, p, inferred, k) do
    case Normalise.nf(ctx, p.term, fuel: @assay_fuel) do
      :fuel_exhausted -> {:violation, {:fuel_exhausted, :nf}}
      nf ->
        case k.check.(ctx, nf, inferred) do
          :ok -> :ok
          err -> {:violation, {:nf_ill_typed, err}}
        end
    end
  end

  defp dispatch("term/normalization", ctx, p, inferred, k) do
    with nf when nf != :fuel_exhausted <- Normalise.nf(ctx, p.term, fuel: @assay_fuel),
         nf2 when nf2 != :fuel_exhausted <- Normalise.nf(ctx, nf, fuel: @assay_fuel) do
      cond do
        nf2 != nf -> {:violation, {:not_idempotent, nf, nf2}}
        k.check.(ctx, nf, inferred) != :ok -> {:violation, {:nf_ill_typed, nf}}
        not round_trips?(nf) -> {:violation, {:c2_round_trip, nf}}
        true -> :ok
      end
    else
      :fuel_exhausted -> {:violation, {:fuel_exhausted, :nf}}
    end
  end
```

(Leave `converges?/3`, `round_trips?/1`, aliases, and `@assay_fuel`/`assay_fuel/0` unchanged. The `@real_kernel` default makes `run/1` byte-identical: the same `Kernel.infer`/`Kernel.check` are now reached through the map.)

- [ ] **Step 4: Run — expect PASS** — both new rows AND the existing `test/antigen/assays/term_test.exs` (regression: `run/1` unchanged). Run:
```
MIX_ENV=test mix test test/antigen/meta/sensitivity_test.exs test/antigen/assays/term_test.exs
```

- [ ] **Step 5: Commit**
```bash
git add lib/antigen/assays/term.ex test/antigen/meta/sensitivity_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): Term run/2 kernel seam + sensitivity rows 2,3 (infer_wrong_type, check_accepts_all)"
```

---

## Task 3: `Positivity` seam + row 4 (positive_accepts_all CAUGHT)

**Files:** Modify `lib/antigen/assays/positivity.ex`; extend `test/antigen/meta/sensitivity_test.exs`.

**Interfaces:**
- Produces: `Positivity.run(%Challenge{kind: :family}, kernel_map)` — the `:family` clause with `Inductive.positive?` read from the map. `run/1` `:family` clause delegates with `@real_kernel`; the `:indexed_case` clause is unchanged.

- [ ] **Step 1: Write the failing test** — append to `test/antigen/meta/sensitivity_test.exs`:

```elixir
  # -- Row 4: Positivity ------------------------------------------------------
  test "row 4 — positive_accepts_all is CAUGHT by positivity (negative-label family)" do
    ch = Antigen.Generators.Positivity.negative_family()
    assert :ok = Antigen.Assays.Positivity.run(ch, WeakKernel.real())
    assert {:violation, {:wrongly_accepted, :Bad}} =
             Antigen.Assays.Positivity.run(ch, WeakKernel.weaken(:positive_accepts_all))
  end
```

- [ ] **Step 2: Run — expect FAIL** (`MIX_ENV=test mix test test/antigen/meta/sensitivity_test.exs`) — `Positivity.run/2` undefined.

- [ ] **Step 3: Implement** — in `lib/antigen/assays/positivity.ex`, add the attribute and a delegating `run/2` for the `:family` clause:

```elixir
  @real_kernel %{positive?: &Inductive.positive?/2}

  def run(%Challenge{kind: :family} = c), do: run(c, @real_kernel)

  def run(%Challenge{kind: :family, label: label, payload: %{family: fam}} = c, k) do
    env = Generators.Positivity.env_of(c)
    verdict = k.positive?.(env, Inductive.get_family(env, fam.name))

    case {label, verdict} do
      {:positive, :ok} -> :ok
      {:negative, {:error, _}} -> :ok
      {:positive, {:error, reason}} -> {:violation, {:wrongly_rejected, reason}}
      {:negative, :ok} -> {:violation, {:wrongly_accepted, fam.name}}
    end
  end
```

Replace the existing `run(%Challenge{kind: :family, …})` **`run/1`** clause with the `run/1`-delegates + `run/2`-body pair above (the `:indexed_case` `run/1` clause stays exactly as-is). The `@real_kernel` default keeps `run/1` byte-identical.

- [ ] **Step 4: Run — expect PASS** — the new row AND `test/antigen/assays/positivity_test.exs`:
```
MIX_ENV=test mix test test/antigen/meta/sensitivity_test.exs test/antigen/assays/positivity_test.exs
```

- [ ] **Step 5: Commit**
```bash
git add lib/antigen/assays/positivity.ex test/antigen/meta/sensitivity_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): Positivity run/2 kernel seam + sensitivity row 4 (positive_accepts_all)"
```

---

## Task 4: `Universes` seam + row 5 (universe_accepts_all CAUGHT)

**Files:** Modify `lib/antigen/assays/universes.ex`; extend `test/antigen/meta/sensitivity_test.exs`.

**Interfaces:**
- Produces: `Universes.run(%Challenge{kind: :indexed_case}, kernel_map)` — the def-shaped clause with `Kernel.check_def` read from the map. `run/1` `:indexed_case` clause delegates with `@real_kernel`; the `:family` clause is unchanged.

- [ ] **Step 1: Write the failing test** — append to `test/antigen/meta/sensitivity_test.exs`:

```elixir
  # -- Row 5: Universes -------------------------------------------------------
  test "row 5 — universe_accepts_all is CAUGHT by universes (Type-in-Type ill_typed def)" do
    ch = Antigen.Generators.Universes.type_in_type(:ill_typed)
    assert :ok = Antigen.Assays.Universes.run(ch, WeakKernel.real())
    assert {:violation, {:wrongly_accepted, :u}} =
             Antigen.Assays.Universes.run(ch, WeakKernel.weaken(:universe_accepts_all))
  end
```

- [ ] **Step 2: Run — expect FAIL** (`MIX_ENV=test mix test test/antigen/meta/sensitivity_test.exs`) — `Universes.run/2` undefined.

- [ ] **Step 3: Implement** — in `lib/antigen/assays/universes.ex`, add the attribute and a delegating `run/2` for the `:indexed_case` clause:

```elixir
  @real_kernel %{check_def: &Kernel.check_def/2}

  def run(%Challenge{kind: :indexed_case} = c), do: run(c, @real_kernel)

  def run(%Challenge{kind: :indexed_case, label: label, payload: %{def_name: dn}} = c, k) do
    env = Generators.Universes.env_of(c)
    judge(label, k.check_def.(env, dn), dn)
  end
```

Replace the existing `run(%Challenge{kind: :indexed_case, …})` **`run/1`** clause with the pair above (the `:family` `run/1` clause and `judge/3` stay as-is). `@real_kernel` keeps `run/1` byte-identical. (The weakened map from `weaken(:universe_accepts_all)` carries `check_family`/`check_ctor` stubs too, but this clause reads only `check_def` — matching row 5's def-shaped fixture.)

- [ ] **Step 4: Run — expect PASS** — the new row AND `test/antigen/assays/universes_test.exs`:
```
MIX_ENV=test mix test test/antigen/meta/sensitivity_test.exs test/antigen/assays/universes_test.exs
```

- [ ] **Step 5: Commit**
```bash
git add lib/antigen/assays/universes.ex test/antigen/meta/sensitivity_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): Universes run/2 kernel seam + sensitivity row 5 (universe_accepts_all)"
```

---

## Task 5: `Reflexivity` seam + rows 7 & 8 (conv_always_true SLIP / conv_exhausts_fuel CAUGHT)

**Files:** Modify `lib/antigen/assays/reflexivity.ex`; extend `test/antigen/meta/sensitivity_test.exs`.

**Interfaces:**
- Produces: `Reflexivity.run(%Challenge{kind: :forcing_pair}, kernel_map)` — `Conv.conv_within?` read from the map. `run/1` delegates with `@real_kernel`.

- [ ] **Step 1: Write the failing test** — append to `test/antigen/meta/sensitivity_test.exs`:

```elixir
  # -- Rows 7 & 8: Reflexivity ------------------------------------------------
  test "row 7 — conv_always_true SLIPS past reflexivity (verdict-blind by design)" do
    ch = Antigen.Generators.Forcing.forcing_pair()
    assert :ok = Antigen.Assays.Reflexivity.run(ch, WeakKernel.real())
    # reflexivity is a non-termination detector: `{:ok, _} -> :ok`. A wrong
    # *verdict* is out of its contract (that is stuck_elim_delta's job, row 6).
    assert :ok = Antigen.Assays.Reflexivity.run(ch, WeakKernel.weaken(:conv_always_true))
  end

  test "row 8 — conv_exhausts_fuel is CAUGHT by reflexivity (its actual contract: halting)" do
    ch = Antigen.Generators.Forcing.forcing_pair()
    assert :ok = Antigen.Assays.Reflexivity.run(ch, WeakKernel.real())
    assert {:violation, {:non_normalizing, _}} =
             Antigen.Assays.Reflexivity.run(ch, WeakKernel.weaken(:conv_exhausts_fuel))
  end
```

- [ ] **Step 2: Run — expect FAIL** (`MIX_ENV=test mix test test/antigen/meta/sensitivity_test.exs`) — `Reflexivity.run/2` undefined.

- [ ] **Step 3: Implement** — in `lib/antigen/assays/reflexivity.ex`, add the attribute and delegating `run/2`:

```elixir
  @real_kernel %{conv_within: &Conv.conv_within?/6}

  def run(%Challenge{kind: :forcing_pair} = c), do: run(c, @real_kernel)

  def run(%Challenge{kind: :forcing_pair, payload: %{t: t, tprime: tprime}} = c, k) do
    env = Generators.Forcing.certified_env_of(c)

    case k.conv_within.(t, tprime, [], 0, env, @fuel) do
      :fuel_exhausted -> {:violation, {:non_normalizing, :conv_exceeded_fuel}}
      {:ok, _} -> :ok
    end
  end
```

Replace the existing `run/1` clause with the pair above. `@real_kernel` keeps `run/1` byte-identical.

- [ ] **Step 4: Run — expect PASS** — the new rows AND `test/antigen/assays/reflexivity_test.exs`:
```
MIX_ENV=test mix test test/antigen/meta/sensitivity_test.exs test/antigen/assays/reflexivity_test.exs
```

- [ ] **Step 5: Commit**
```bash
git add lib/antigen/assays/reflexivity.ex test/antigen/meta/sensitivity_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): Reflexivity run/2 kernel seam + sensitivity rows 7,8 (conv verdict-blind vs halting)"
```

---

## Task 6: `StuckElimDelta` seam + row 6 (conv_always_true CAUGHT)

**Files:** Modify `lib/antigen/assays/stuck_elim_delta.ex`; extend `test/antigen/meta/sensitivity_test.exs`.

**Interfaces:**
- Produces: `StuckElimDelta.run(%Challenge{kind: :stuck_elim}, kernel_map)` — `Conv.conv_within?` read from the map. `run/1` delegates with `@real_kernel`.

**Regression note:** `stuck_elim_delta.ex` has **no** dedicated `test/antigen/assays/stuck_elim_delta_test.exs`; its `run/1` regression coverage is `test/antigen/corpus_replay_test.exs` (replays banked `:stuck_elim` records). Run that file, not a same-named assay test, at Step 4.

- [ ] **Step 1: Write the failing test** — append to `test/antigen/meta/sensitivity_test.exs`:

```elixir
  # -- Row 6: StuckElimDelta --------------------------------------------------
  # A minimal negative :stuck_elim control — two DISTINCT closed normal forms
  # (Z ≠ S(Z)) the kernel must not equate. The sensitivity target is the assay's
  # verdict-vs-committed-label decision (a permissive conv breaks it regardless of
  # whether the δ-of-stuck-eliminator seam fires), so an empty env + already-normal
  # pair exercises that decision deterministically.
  defp neg_stuck_elim_ch,
    do: Challenge.new(kind: :stuck_elim, assay: "stuck_elim_delta", label: :negative,
                      payload: %{defs: [], focus: [], t: @z, tprime: @sz})

  test "row 6 — conv_always_true is CAUGHT by stuck_elim_delta (negative control)" do
    ch = neg_stuck_elim_ch()
    assert :ok = Antigen.Assays.StuckElimDelta.run(ch, WeakKernel.real())
    assert {:violation, {:unsound_verdict, %{expected: false, got: true}}} =
             Antigen.Assays.StuckElimDelta.run(ch, WeakKernel.weaken(:conv_always_true))
  end
```

- [ ] **Step 2: Run — expect FAIL** (`MIX_ENV=test mix test test/antigen/meta/sensitivity_test.exs`) — `StuckElimDelta.run/2` undefined.

- [ ] **Step 3: Implement** — in `lib/antigen/assays/stuck_elim_delta.ex`, add the attribute and delegating `run/2`:

```elixir
  @real_kernel %{conv_within: &Conv.conv_within?/6}

  def run(%Challenge{kind: :stuck_elim} = c), do: run(c, @real_kernel)

  def run(%Challenge{kind: :stuck_elim, label: label, payload: %{t: t, tprime: tprime} = p}, k) do
    env = certified_env_of(p)
    expected = label == :positive

    case k.conv_within.(t, tprime, [], 0, env, @fuel) do
      :fuel_exhausted ->
        {:violation, {:non_normalizing, :conv_exceeded_fuel}}

      {:ok, ^expected} ->
        :ok

      {:ok, other} ->
        {:violation, {:unsound_verdict, %{expected: expected, got: other}}}
    end
  end
```

Replace the existing `run/1` clause with the pair above (leave `certified_env_of/1` and `@fuel` unchanged). `@real_kernel` keeps `run/1` byte-identical.

- [ ] **Step 4: Run — expect PASS** — the new row AND the corpus-replay regression:
```
MIX_ENV=test mix test test/antigen/meta/sensitivity_test.exs test/antigen/corpus_replay_test.exs
```

- [ ] **Step 5: Commit**
```bash
git add lib/antigen/assays/stuck_elim_delta.ex test/antigen/meta/sensitivity_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): StuckElimDelta run/2 kernel seam + sensitivity row 6 (conv_always_true)"
```

---

## Task 7: Row 1 (mutation, existing seam) + matrix roster completeness

**Files:** extend `test/antigen/meta/sensitivity_test.exs` (no lib changes — mutation already has `run/2`).

**Interfaces:**
- Consumes: `Antigen.Assays.Mutation.run(challenge, infer_fun)` (existing bare-fn seam).

- [ ] **Step 1: Write the failing test** — append to `test/antigen/meta/sensitivity_test.exs`:

```elixir
  # -- Row 1: Mutation (existing bare-fn run/2 seam; no new lib code) ----------
  defp mutant_ch,
    do: Challenge.new(kind: :mutant_term, assay: "mutation/rejection", label: :ill_typed,
          payload: %{sig: :v1, ctx: [], type: @nat, term: {:app, @z, @z},
                     fault: %{kind: :app_domain, witness: :head, expected_head: :Nat, injected_head: :Nat}})

  test "row 1 — infer_accepts_all is CAUGHT by mutation/rejection" do
    ch = mutant_ch()
    assert :ok = Antigen.Assays.Mutation.run(ch)
    assert {:violation, {:accepted_ill_typed, _, _}} =
             Antigen.Assays.Mutation.run(ch, WeakKernel.weaken(:infer_accepts_all).infer)
  end

  # Completeness roster: the 8 rows this file asserts, as a single source of truth
  # for the Stage-5 matrix. A CAUGHT row means the weakened assay returned a
  # violation; a SLIP row means it stayed :ok. This test fails loudly if a row is
  # dropped, keeping the committed matrix honest.
  @roster [
    {1, :infer_accepts_all, "mutation/rejection", :caught},
    {2, :infer_wrong_type, "term/infer_check", :caught},
    {3, :check_accepts_all, "term/infer_check", :slip},
    {4, :positive_accepts_all, "positivity", :caught},
    {5, :universe_accepts_all, "universes", :caught},
    {6, :conv_always_true, "stuck_elim_delta", :caught},
    {7, :conv_always_true, "reflexivity", :slip},
    {8, :conv_exhausts_fuel, "reflexivity", :caught}
  ]

  test "matrix roster covers all 8 rows with 6 CAUGHT / 2 SLIP" do
    assert length(@roster) == 8
    assert Enum.count(@roster, fn {_, _, _, c} -> c == :caught end) == 6
    assert Enum.count(@roster, fn {_, _, _, c} -> c == :slip end) == 2
    assert Enum.map(@roster, fn {n, _, _, _} -> n end) == Enum.to_list(1..8)
  end
```

- [ ] **Step 2: Run — expect FAIL** (`MIX_ENV=test mix test test/antigen/meta/sensitivity_test.exs`) — row 1 is red first (before this step the file lacks it); confirm the file now fails only on the newly-added assertions and that all prior rows still pass. (Row 1 uses only the pre-existing `Mutation.run/2`, so it goes green immediately once the test is written — its "red" is purely the absence of the test; the roster test is a pure data assertion. Re-run to confirm GREEN in Step 4.)

- [ ] **Step 3: Implement** — none. Row 1 exercises the existing `Mutation.run/2`; the roster is a static assertion. (If Step 2 shows row 1 already green, that is expected — mutation's seam predates this run.)

- [ ] **Step 4: Run — expect PASS** — the full sensitivity file (all 8 rows + roster):
```
MIX_ENV=test mix test test/antigen/meta/sensitivity_test.exs
```

- [ ] **Step 5: Commit**
```bash
git add test/antigen/meta/sensitivity_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "test(antigen): sensitivity row 1 (mutation) + 8-row matrix roster"
```

---

## Stage 5 (verify) — full suite + matrix report

Run the full suite ONCE (`MIX_ENV=test mix test`); expect all green (prior baseline 2577 + the new WeakKernel/sensitivity tests, 0 regressions — the additive seams keep every `run/1` byte-identical). Then write the completion report `docs/superpowers/reports/2026-07-03-antigen-sensitivity-meta-testing-report.md` with the rendered 8-row matrix (from the roster), per-task commits, and the honesty line (testing the tests, not proof; SLIP cells are surviving mutants reported openly; boundary-only reach, meck follow-on deferred).

---

## Self-Review

**Spec coverage:** §2 mechanism (per-fn seam, no TCB/meck) → Tasks 1–6 (map + additive `run/2`). §2.1 negative-expectation requirement → rows 2/4/5/6 CAUGHT via disagreement/negative-label/negative-control; row 3/7 SLIP because the assay lacks the needed negative expectation. §3 catalog (7 weakenings, 8 rows) → Task 1 (weakenings) + Tasks 2–7 (rows). §4 discipline (baseline+weakened pairs, characterize observed, SLIP as `:ok`) → every row is a pair; SLIP rows assert `:ok`. §5 files → `weak_kernel.ex`, five seamed assays, `sensitivity_test.exs`, report; regression split (dedicated files for term/positivity/universes/reflexivity/mutation, corpus-replay for stuck_elim) honored in Steps 4. §6 non-goals (no TCB, no meck, `run/1` unchanged, curated) respected. §7 follow-ons → Stage-5 report only.

**Placeholder scan:** none — every step has concrete code; fixtures are fully specified terms.

**Type consistency:** `WeakKernel.real/0`/`weaken/1` return maps read as `k.infer`/`k.check`/`k.conv_within`/`k.positive?`/`k.check_def` (Tasks 1→2–6). `conv_within` arity 6 matches `Conv.conv_within?/6` (reflexivity/stuck_elim/term call-sites confirm order `(t, t', val_env, depth, sig_env, fuel)`). Each seamed assay's `run/2` returns `:ok | {:violation, _}` exactly as its `run/1`. Row-1 uses `Mutation.run/2`'s bare-fn seam (passes `weaken(:infer_accepts_all).infer`, an arity-2 fn) — distinct from the map seam, matching mutation's pre-existing signature.

**Ordering:** Task 1 (WeakKernel) before any seam consumes it; Tasks 2–6 each independent (own assay + own rows + own regression file); Task 7 needs only the pre-existing mutation seam + the roster. Stage 5 is the single full-suite run.
