# Antigen V1 — Normalizer Soundness Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** three new Antigen assays testing the untrusted `Cure.Types.Reduce` type-level normalizer against the trusted kernel — differential `normalize` (V1a), differential `equal?` soundness (V1b), and intrinsic idempotence + monotone-size on the untranslatable fragment (V1c).

**Architecture:** A new `Antigen.Assays.Normalizer` (3 assay ids) re-checks `Reduce`'s output against an *independent* surface→Core encoding evaluated by the trusted kernel. A new `Antigen.Generators.SurfaceExpr` produces fixed catalogs of `{ast, bindings, core_expected}` triples (independent encoder owned by the generator). Wired via `assay_module/1` dispatch and run through a dedicated test — the elab-family pattern — with NO corpus/Coverage surgery.

**Tech Stack:** Elixir; ExUnit (`async: true`); no new deps; `MIX_ENV=test` for all mix invocations (dev env crashes).

## Global Constraints

- **Ghost-authored commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`; NEVER a `Co-Authored-By` trailer.
- **Branch:** stay on `autopilot/antigen-tier-b` (no new worktree).
- **No `Cure.Core.*` / `Cure.Types.*` edits.** Both are reached read-only, only through the assay's `@real` op-map.
- **No new dependency, no `:meck`.** The `run/2` op-map is the only injection path.
- **StreamData quarantine:** the assay (`lib/antigen/assays/normalizer.ex`) must contain NO `StreamData` literal; the generator (`lib/antigen/generators/surface_expr.ex`) may.
- **One build/test run at any moment.** Never launch concurrent suites.
- **Tests immutable** once written (sole exception: a test proven to encode wrong behavior, argued explicitly first).
- **Run mix from the worktree root** `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/antigen-tier-b`.
- **Fuel floor** for kernel normalization is the committed `500_000` (matches `Reflexivity`/`Term`/`Elab`).

## Reconciliations with the spec (resolved deviations, for the reviewer)

1. **Fixed catalog, not corpus-banked (spec §7.6 wiring avoided).** `Challenge.new/1`
   uses `struct!` — it does not validate `kind`, and `Runner.replay_one/1` calls
   only `apply(assay_module(a), :run, [c])`, never `to_pieces`/`Coverage`. So V1
   adds a lightweight `:surface_expr` kind (typespec entry only) and runs as a
   fixed catalog via a dedicated test — exactly the elab family's pattern
   (`completeness_challenges/0` + `elab_completeness_test.exs`). It is NOT added to
   `default_gen`, and needs NO `Challenge.to_pieces/from_pieces`,
   `Coverage.terms_of`, or corpus-banking clause (those pattern-match on `kind`
   and assume Core terms — a surface-AST payload doesn't fit and isn't needed for
   replay-based running). This keeps V1 self-contained.
2. **Op-map injects the code-under-test (`normalize`/`equal`), not `Reduce`'s
   internals.** The spec §4/§5 wording ("inject a `from_core`/`substitute`")
   cannot be done without reimplementing or mutating `Reduce` (forbidden). The
   Run C sensitivity pattern injects the thing under test at the assay boundary:
   the op-map's `normalize`/`equal` keys default to `&Reduce.normalize/2` /
   `&Reduce.equal?/3`; a negative control passes a *stub* that simulates the buggy
   behavior (a normal form with a dropped substitution, a corrupted read-back, an
   unsound `true`). This proves the assay's comparison is load-bearing (it CAN
   fail) exactly as the spec intends, without touching `Cure.Types`. The oracle
   ops (`eval`/`reify`/`conv`/`to_core`) stay real.

## File structure

- **New** `lib/antigen/assays/normalizer.ex` — `Antigen.Assays.Normalizer`, `run/1`+`run/2` for the three ids, `@real` op-map, `@assay_fuel`, private property checkers + `term_size/1`.
- **New** `lib/antigen/generators/surface_expr.ex` — `differential_challenges/0`, `equal_challenges/0`, `intrinsic_challenges/0`; the independent `encode/2` surface→Core encoder.
- **Modify** `lib/antigen/runner.ex` — `assay_module/1` clauses for the three ids.
- **Modify** `lib/antigen/challenge.ex` — add `:surface_expr` to the `@type kind` union (documentation only; `struct!` does not enforce it).
- **New** `test/antigen/assays/normalizer_test.exs` — all tests.

## Interfaces (locked signatures, verified against source)

- `Cure.Types.Reduce.normalize(ast, bindings :: map) :: ast` — under test.
- `Cure.Types.Reduce.equal?(a, b, bindings :: map) :: boolean` — under test.
- `Cure.Types.CoreBridge.to_core(ast) :: {:ok, Cure.Core.Term.t()} | :error`; `from_core(core) :: ast`. Grammar (verified): `{:literal, _, int} → {:int_lit, n}`; `{:literal, _, bool} → {:ctor, :True|:False, []}`; `{:variable, _, name} → {:global, atom}`; `{:binary_op, [operator: op], [l, r]} → {:prim, core_op, [l', r']}` where `core_op` is **`op` translated through `CoreBridge`'s private `@binops` table**, NOT `op` itself: `+→:add, -→:sub, *→:mul, /→:div, %→:rem, ==→:eq, !=→:ne, <→:lt, <=→:le, >→:gt, >=→:ge` (`and`/`or` pass through unchanged as `:and`/`:or`); `{:tuple, _, [a, b]} → {:pair, …}`; else `:error`. **This distinction is load-bearing**: `Cure.Core.Eval.fold/2` (the kernel's arithmetic folder) has clauses keyed on the CORE names (`:add`, `:sub`, …) — it has no clause for the surface symbol `:+` itself, so `eval({:prim, :+, [...]})` never folds and stays a stuck neutral. Every hand-built `core_expected`/`core_a`/`core_b` term below (and the independent encoder) MUST use the translated core-op atom, never the raw surface operator.
- `Cure.Core.Eval.eval(term, env :: list) :: value`.
- `Cure.Core.Quote.reify(value, depth \\ 0) :: term`.
- `Cure.Core.Conv.conv?(t1, t2, env :: list, depth :: non_neg_integer, sig \\ nil) :: boolean` — takes **terms**, evaluates internally. For this fragment (no `{:var,k}`, no certified global): `env = []`, `depth = 0`, `sig = nil`.
- `Antigen.Challenge.new(fields) :: Challenge.t()`.

## The independent encoder (generator-owned, §2 of the spec)

`SurfaceExpr.encode(ast, bindings)` — a **second, hand-written** surface→Core encoder, structurally independent of `CoreBridge.to_core`, that folds `bindings` in directly:

```elixir
# generator-owned; mirrors CoreBridge's grammar but is separate code so a
# CoreBridge/do_substitute bug shows up as a real mismatch, not a mirrored one.
#
# `@ops` is this module's OWN copy of the surface->core operator-name table —
# separate data from `CoreBridge`'s private `@binops`, so the two stay
# independent code paths, but it MUST carry the same surface->core mapping
# (verified against `Cure.Types.CoreBridge`'s `@binops` and required because
# `Cure.Core.Eval.fold/2` folds on the CORE names, not the surface symbols —
# `{:prim, :+, [...]}` never reduces; `{:prim, :add, [...]}` does).
@ops %{
  +: :add, -: :sub, *: :mul, /: :div, %: :rem,
  ==: :eq, !=: :ne, <: :lt, <=: :le, >: :gt, >=: :ge,
  and: :and, or: :or
}
def encode({:variable, _m, name}, b) do
  case Map.fetch(b, name) do
    {:ok, bound} -> encode(bound, b)          # substitution folded at encode time
    :error -> {:global, String.to_atom(name)}
  end
end
def encode({:literal, _m, n}, _b) when is_integer(n), do: {:int_lit, n}
def encode({:literal, _m, x}, _b) when is_boolean(x), do: {:ctor, (if x, do: :True, else: :False), []}
def encode({:binary_op, meta, [l, r]}, b),
  do: {:prim, Map.fetch!(@ops, Keyword.fetch!(meta, :operator)), [encode(l, b), encode(r, b)]}
def encode({:tuple, _m, [a, c]}, b), do: {:pair, encode(a, b), encode(c, b)}
```

---

### Task 1: `Antigen.Assays.Normalizer` — differential `normalize` (V1a)

**Files:** Create `lib/antigen/assays/normalizer.ex`; Create `test/antigen/assays/normalizer_test.exs`.

**Interfaces:** Produces `Normalizer.run/1`+`run/2` for `assay: "normalizer/differential"`, `Normalizer.__real__/0`. Consumes `CoreBridge.to_core`, `Eval.eval`, `Quote.reify`, `Conv.conv?`.

- [ ] **Step 1: Write the failing tests**

Create `test/antigen/assays/normalizer_test.exs`:

```elixir
defmodule Antigen.Assays.NormalizerTest do
  use ExUnit.Case, async: true
  alias Antigen.{Assays.Normalizer, Challenge}
  alias Antigen.Generators.SurfaceExpr

  # {:binary_op, [operator: :+], [3, 5]} and its independent core encoding.
  # NOTE: the core-side op atom is `:add`, NOT the surface `:+` — `CoreBridge.to_core`
  # translates through its `@binops` table, and `Eval.fold/2` only has clauses for
  # the translated core names. `{:prim, :+, [...]}` would never fold (see Interfaces).
  defp lit(n), do: {:literal, [subtype: :integer], n}
  defp add(a, b), do: {:binary_op, [operator: :+], [a, b]}

  defp diff_ch(ast, bindings, core_expected) do
    Challenge.new(kind: :surface_expr, assay: "normalizer/differential",
      label: :translatable, payload: %{ast: ast, bindings: bindings, core_expected: core_expected}, seed: 1)
  end

  test "V1a baseline: normalize(3+5) agrees with the kernel norm of the independent encoding" do
    ch = diff_ch(add(lit(3), lit(5)), %{}, {:prim, :add, [{:int_lit, 3}, {:int_lit, 5}]})
    assert Normalizer.run(ch) == :ok
  end

  test "V1a from_core-style negative control: a normalize stub with a corrupted result infects" do
    ch = diff_ch(add(lit(3), lit(5)), %{}, {:prim, :add, [{:int_lit, 3}, {:int_lit, 5}]})
    k = %{Normalizer.__real__() | normalize: fn _ast, _b -> lit(7) end}  # wrong: says 7, not 8
    assert {:violation, {:normalize_disagrees_with_kernel, _, _}} = Normalizer.run(ch, k)
  end

  test "V1a substitution negative control: a normalize stub that drops a binding infects" do
    # ast = n + 1 with n=4 ; core_expected folds n->4 => 4+1. A stub that leaves `n`
    # unsubstituted returns `n + 1` (a {:variable} survives) -> to_core gives a
    # {:global,:n} the kernel norm of core_expected (5) is not convertible to.
    ast = add({:variable, [], "n"}, lit(1))
    ch = diff_ch(ast, %{"n" => lit(4)}, {:prim, :add, [{:int_lit, 4}, {:int_lit, 1}]})
    k = %{Normalizer.__real__() | normalize: fn a, _b -> a end}  # identity: never substitutes
    assert {:violation, {:normalize_disagrees_with_kernel, _, _}} = Normalizer.run(ch, k)
  end

  test "V1a untranslatable-result negative control: a normalize stub returning an untranslatable AST infects" do
    # {:refinement, ...} is outside CoreBridge.to_core's grammar (to_core -> :error),
    # so this exercises the `with ... else :error -> ...` branch that no other test
    # here reaches (Reduce.normalize itself always stays inside the translatable
    # fragment for a translatable input; only a broken stub can violate that).
    ch = diff_ch(add(lit(3), lit(5)), %{}, {:prim, :add, [{:int_lit, 3}, {:int_lit, 5}]})
    k = %{Normalizer.__real__() | normalize: fn _ast, _b -> {:refinement, [], [lit(8)]} end}
    assert {:violation, {:normalize_disagrees_with_kernel, _, {:untranslatable_result, _}}} =
             Normalizer.run(ch, k)
  end
end
```

- [ ] **Step 2: Run to verify RED**

Run: `MIX_ENV=test mix test test/antigen/assays/normalizer_test.exs`
Expected: FAIL — `Antigen.Assays.Normalizer` undefined.

- [ ] **Step 3: Implement the differential assay**

Create `lib/antigen/assays/normalizer.ex`:

```elixir
defmodule Antigen.Assays.Normalizer do
  @moduledoc """
  Property tests for the untrusted type-level normalizer `Cure.Types.Reduce`
  against the trusted `Cure.Core` kernel (spec: antigen-normalizer-soundness).

    * normalizer/differential — `Reduce.normalize(ast)` agrees with the kernel
      normal form of an INDEPENDENT surface->Core encoding (V1a).
    * normalizer/equal — `Reduce.equal?` never returns a false `true` vs the
      kernel (V1b, the soundness direction).
    * normalizer/intrinsic — on the untranslatable fragment, `normalize` is a
      fixpoint and never grows the term (V1c).

  All kernel ops go through an injectable `@real` map (run/2) so negative
  controls can weaken the thing under test without touching `Cure.Types`/`Cure.Core`
  or using `:meck`.
  """
  alias Antigen.Challenge
  alias Cure.Types.{Reduce, CoreBridge}
  alias Cure.Core.{Eval, Quote, Conv}

  @assay_fuel 500_000
  @real %{
    normalize: &Reduce.normalize/2,
    equal: &Reduce.equal?/3,
    to_core: &CoreBridge.to_core/1,
    eval: &Eval.eval/2,
    reify: &Quote.reify/1,
    conv: &Conv.conv?/5
  }
  @doc false
  def __real__, do: @real

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :surface_expr} = c), do: run(c, @real)

  def run(%Challenge{kind: :surface_expr, assay: "normalizer/differential", payload: p}, k) do
    actual = k.normalize.(p.ast, p.bindings)

    with {:ok, actual_core} <- k.to_core.(actual) do
      expected_core = k.reify.(k.eval.(p.core_expected, []))

      if Cure.Core.Normalise.with_fuel(@assay_fuel, fn -> k.conv.(actual_core, expected_core, [], 0, nil) end) == true do
        :ok
      else
        {:violation, {:normalize_disagrees_with_kernel, p.ast, %{actual: actual, expected: expected_core}}}
      end
    else
      :error -> {:violation, {:normalize_disagrees_with_kernel, p.ast, {:untranslatable_result, actual}}}
    end
  end
end
```

> Note: `with_fuel` returns the fun's value (`true`/`false`) or `:fuel_exhausted`; the `== true` guard treats both `false` and `:fuel_exhausted` as non-agreement (the latter is defensive — this fragment is structurally terminating). If a distinct `:fuel_exhausted` tag is wanted, the plan-reviewer may split it; not required for V1a's translatable fragment.

- [ ] **Step 4: Run to verify GREEN** — `MIX_ENV=test mix test test/antigen/assays/normalizer_test.exs` → PASS (4).

- [ ] **Step 5: Commit** — `feat(antigen): normalizer/differential assay — Reduce.normalize vs independent kernel encoding`

---

### Task 2: `normalizer/equal` — `equal?` soundness (V1b)

**Files:** Modify `lib/antigen/assays/normalizer.ex`; append tests.

- [ ] **Step 1: Write failing tests**

```elixir
describe "normalizer/equal (V1b soundness)" do
  defp eq_ch(a, ca, b, cb, label) do
    Challenge.new(kind: :surface_expr, assay: "normalizer/equal", label: label,
      payload: %{a: a, b: b, bindings: %{}, core_a: ca, core_b: cb}, seed: 1)
  end

  # Same `:add`-not-`:+` note as Task 1 applies to every hand-built core_a/core_b here.
  test "baseline: equal?(3+5, 8)=true and kernel agrees; equal?(3+5, 9)=false and kernel agrees" do
    t = eq_ch(add(lit(3), lit(5)), {:prim, :add, [{:int_lit,3},{:int_lit,5}]}, lit(8), {:int_lit, 8}, :kernel_equal)
    f = eq_ch(add(lit(3), lit(5)), {:prim, :add, [{:int_lit,3},{:int_lit,5}]}, lit(9), {:int_lit, 9}, :kernel_unequal)
    assert Normalizer.run(t) == :ok
    assert Normalizer.run(f) == :ok
  end

  test "unsound negative control: equal? returns true for a kernel-unequal pair infects" do
    f = eq_ch(add(lit(3), lit(5)), {:prim, :add, [{:int_lit,3},{:int_lit,5}]}, lit(9), {:int_lit, 9}, :kernel_unequal)
    k = %{Normalizer.__real__() | equal: fn _a, _b, _bnd -> true end}  # unsound: claims 8 == 9
    assert {:violation, {:equal_unsound, _, _}} = Normalizer.run(f, k)
  end
end
```

- [ ] **Step 2: RED** — the `normalizer/equal` clause is undefined.

- [ ] **Step 3: Implement** — add to `normalizer.ex`:

```elixir
def run(%Challenge{kind: :surface_expr, assay: "normalizer/equal", payload: p}, k) do
  surface_eq = k.equal.(p.a, p.b, p.bindings)
  kernel_eq = Cure.Core.Normalise.with_fuel(@assay_fuel, fn -> k.conv.(p.core_a, p.core_b, [], 0, nil) end)

  # Soundness direction ONLY (V1b, per the moduledoc): `equal?` must never claim
  # `true` when the kernel disagrees. The converse ("surface says false, kernel
  # says true") is a completeness/reach-gap question, out of scope here — and
  # MUST NOT be surfaced as a third outcome kind: `Runner.replay_one/1` passes
  # the return straight through with no case-match (verified against
  # `lib/antigen/runner.ex`, so it wouldn't crash there), but `Runner.explore/1`'s
  # dispatch `case` recognizes only `:ok` and `{:violation, _}` with NO catch-all
  # clause — any third shape raises `CaseClauseError` if this assay is ever run
  # through `explore/1`. The declared `@spec` above is also `:ok | {:violation,
  # term()}`; introducing `{:incomplete, _}` would violate it. So: :ok.
  if surface_eq and kernel_eq != true do
    {:violation, {:equal_unsound, p.a, p.b}}
  else
    :ok
  end
end
```

- [ ] **Step 4: GREEN.**  **Step 5: Commit** — `feat(antigen): normalizer/equal assay — equal? soundness vs kernel Conv`

---

### Task 3: `normalizer/intrinsic` — idempotence + monotone-size (V1c)

**Files:** Modify `lib/antigen/assays/normalizer.ex`; append tests.

- [ ] **Step 1: Write failing tests** (untranslatable-headed term so `structural_congruence` governs; a refinement-marker head that `to_core` rejects):

```elixir
describe "normalizer/intrinsic (V1c)" do
  # {:refinement, ...} is outside CoreBridge's grammar (to_core -> :error).
  defp intr_ch(ast) do
    Challenge.new(kind: :surface_expr, assay: "normalizer/intrinsic", label: :untranslatable,
      payload: %{ast: ast}, seed: 1)
  end
  defp untranslatable(inner), do: {:refinement, [], [inner]}

  test "baseline: normalize is a fixpoint and does not grow the term" do
    assert Normalizer.run(intr_ch(untranslatable(add(lit(3), lit(5))))) == :ok
  end

  test "not-idempotent negative control" do
    # Must NOT also grow the term, or it trips :size_increased first (the
    # implementation checks size before idempotence — see Step 3's note). This
    # stub retags {:refinement,...} <-> {:not_fixed,...} with the SAME child
    # count each call (term_size is tag-blind), so the size guard passes and
    # the oscillation exposes genuine non-idempotence: once != p.ast's shape,
    # twice flips back, so twice != once.
    k = %{Normalizer.__real__() | normalize: fn
      {:refinement, m, [inner]}, _b -> {:not_fixed, m, [inner]}
      {:not_fixed, m, [inner]}, _b -> {:refinement, m, [inner]}
      ast, _b -> ast
    end}
    assert {:violation, {:not_idempotent, _, _}} = Normalizer.run(intr_ch(untranslatable(lit(1))), k)
  end

  test "size-increase negative control" do
    k = %{Normalizer.__real__() | normalize: fn ast, _b -> {:dup, [], [ast, ast]} end}  # strictly larger
    assert {:violation, {:size_increased, _, _}} = Normalizer.run(intr_ch(untranslatable(lit(1))), k)
  end
end
```

- [ ] **Step 2: RED.**

- [ ] **Step 3: Implement** — add to `normalizer.ex` the intrinsic clause + `term_size/1`:

```elixir
def run(%Challenge{kind: :surface_expr, assay: "normalizer/intrinsic", payload: p}, k) do
  once = k.normalize.(p.ast, %{})
  twice = k.normalize.(once, %{})

  cond do
    term_size(once) > term_size(p.ast) -> {:violation, {:size_increased, p.ast, %{in: term_size(p.ast), out: term_size(once)}}}
    twice != once -> {:violation, {:not_idempotent, p.ast, %{once: once, twice: twice}}}
    true -> :ok
  end
end

# node count over the {tag, meta, children} grammar; meta excluded, scalar leaves count 1.
defp term_size({_tag, _meta, children}) when is_list(children),
  do: 1 + Enum.sum(Enum.map(children, &term_size/1))
defp term_size(_leaf), do: 1
```

> Check the size guard first so a stub that both grows AND is non-idempotent reports `:size_increased` deterministically. `term_size` must handle both composite `{tag, meta, [children]}` and scalar payloads (`{:literal, meta, 3}` — here `3` is the child position but not a list; the `_leaf` clause covers a non-list third element). Plan-reviewer: confirm `{:literal, meta, n}` (n scalar) hits the leaf clause, not the composite one — it does, since `n` is not a list, so the first clause's `when is_list(children)` guard fails and it falls to `_leaf` = size 1.

- [ ] **Step 4: GREEN.**  **Step 5: Commit** — `feat(antigen): normalizer/intrinsic assay — idempotence + monotone-size on untranslatable fragment`

---

### Task 4: `SurfaceExpr` catalogs + runner wiring

**Files:** Create `lib/antigen/generators/surface_expr.ex`; Modify `lib/antigen/runner.ex`, `lib/antigen/challenge.ex`; append tests.

- [ ] **Step 1: Write failing tests**

```elixir
describe "generator + runner wiring" do
  alias Antigen.Runner

  test "each catalog is non-empty and correctly tagged" do
    assert SurfaceExpr.differential_challenges() != []
    assert Enum.all?(SurfaceExpr.differential_challenges(), & &1.assay == "normalizer/differential")
    assert Enum.all?(SurfaceExpr.equal_challenges(), & &1.assay == "normalizer/equal")
    assert Enum.all?(SurfaceExpr.intrinsic_challenges(), & &1.assay == "normalizer/intrinsic")
  end

  test "runner dispatches each normalizer/* id and every catalog entry is clean under the real kernel" do
    all = SurfaceExpr.differential_challenges() ++ SurfaceExpr.equal_challenges() ++ SurfaceExpr.intrinsic_challenges()
    assert Enum.all?(all, fn c -> Runner.replay_one(c) == :ok end)
  end
end
```

- [ ] **Step 2: RED** — `SurfaceExpr` undefined; `assay_module("normalizer/*")` has no clause.

- [ ] **Step 3: Implement** — Create `lib/antigen/generators/surface_expr.ex` with `encode/2` (from the "independent encoder" section above), a small fixed catalog per family (each entry built as `{ast, bindings, encode(ast, bindings)}` for differential; a should-be-equal and should-be-unequal pair for equal, with `core_a`/`core_b` likewise computed via `encode(ast, bindings)` — NEVER hand-written `{:prim, surface_op, …}` literals, the exact mistake Task 1/2's tests had to fix, since `encode/2` is the only place that correctly applies the `@ops` surface→core translation; untranslatable-headed terms for intrinsic), and `differential_challenges/0`/`equal_challenges/0`/`intrinsic_challenges/0` returning `Challenge.new(kind: :surface_expr, …)` lists. In `lib/antigen/runner.ex` add three `assay_module/1` clauses → `Antigen.Assays.Normalizer`. In `lib/antigen/challenge.ex` add `| :surface_expr` to the `@type kind` union.

- [ ] **Step 4: GREEN.** If a catalog entry legitimately fails, that is a REAL infection in `Types.Reduce` — STOP and report (do not weaken the test).

- [ ] **Step 5: Commit** — `feat(antigen): SurfaceExpr catalogs + normalizer/* runner dispatch`

---

### Task 5: Full-suite verification

- [ ] **Step 1:** `MIX_ENV=test mix test` (single authorized run) — all pass; count = prior + normalizer_test rows.
- [ ] **Step 2:** `MIX_ENV=test mix test test/antigen/architecture_test.exs` — quarantine green (assay has no `StreamData` literal).
- [ ] **Step 3:** `git status --short`; revert `test/antigen/seeds.sexp` if the run touched it; confirm clean.
- [ ] **Step 4:** No commit (verification).

## Self-review

**Spec coverage:** §2 independence (independent `encode/2`) → Task 4's encoder consumed by Task 1's substitution control; V1a → Task 1; V1b soundness → Task 2; V1c laws → Task 3; §3 generator → Task 4 (reconciled to fixed catalog); §4 op-map seam → Task 1's `@real`/`run/2` (reconciled to `normalize`/`equal` code-under-test injection); §5 tests #1-9 distributed; §6 invariants pinned; §8 non-goals respected (no `Cure.Types`/`Cure.Core` edit, no fix, no SMT).

**Placeholder scan:** none — concrete code/commands throughout. The remaining plan-reviewer notes (fuel-tag split, `term_size` leaf shape) are explicit bounded checks with named fallbacks; the `:incomplete` runner-handling question raised in an earlier draft is resolved (Task 2 now returns only `:ok | {:violation, _}}`, matching its `@spec` and both `Runner.replay_one/1` and `Runner.explore/1`).

**Type consistency:** op-map keys `normalize/equal/to_core/eval/reify/conv` identical in `@real` and every negative control. Infection tags `{:normalize_disagrees_with_kernel,…}`, `{:equal_unsound,…}`, `{:not_idempotent,…}`, `{:size_increased,…}` consistent spec↔code↔tests. `:surface_expr` payload shapes: differential `%{ast, bindings, core_expected}`, equal `%{a, b, bindings, core_a, core_b}`, intrinsic `%{ast}` — each produced by its catalog and consumed by its `run` clause.
