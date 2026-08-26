# Nat→Int Runtime Erasure Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Land the foundation's Phase 2 — canonical `Std.Nat` values become BEAM machine integers at emit time (`Z()`→`0`, `S(e)`→`e+1`, case-on-Nat → zero-test + predecessor bind), plus the elaborator eta-expansion that makes first-class `S` elaborate — spec `docs/superpowers/specs/kernel/2026-07-08-nat-int-erasure-design.md` (hardened `cca019b`).

**Architecture:** Two emit hooks in `lib/cure/elab/emit.ex` mirroring the Bool→atom precedent (registry-keyed, nominal); one elaborator fix in `resolve_free` (general bare-positive-arity-ctor eta-expansion, E-layer); a new Antigen `elab/nat_rep` representation-agreement assay (kernel certified-δ normalisation as oracle vs BEAM execution as SUT).

**Tech Stack:** Elixir, Erlang abstract format (`emit.ex`), `Cure.Core.Normalise`, ExUnit, Antigen.

## Global Constraints (from the spec — every task implicitly includes these)

- Working dir: `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/kernel-parity-batch`, branch `autopilot/kernel-parity-batch` (already checked out; no new branches/worktrees).
- Files touched: `lib/cure/elab/emit.ex`, `lib/cure/elab/elaborator.ex` (Task 2 only: `resolve_free` + its stale comment), `lib/antigen/generators/elab_nat_rep.ex` (new), `lib/antigen/assays/elab.ex`, `lib/antigen/runner.ex`, `lib/antigen/challenge.ex` (Task 3 only: one `@elab_keys` whitelist entry, confirmed required — see Task 3), `docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md` (one status sentence), new test files. **NOTHING under `lib/cure/core/` changes.** No changes to `lib/cure/elab/erase.ex`, `lib/cure/types/*`, `lib/cure/compiler/*` (two-pipeline discipline: the latter two are the NON-dependent decoy pipeline).
- **Nominal rule:** the Int rep fires ONLY for the family `Inductive.builtin(env, :nat)` (the auto-prelude `Std.Nat`). Every existing test fixture declaring a LOCAL `type Nat = Z | S(Nat)` (≈46 files under `test/cure/elab/`, plus `test/cure/compiler/dependent_vec_codegen_test.exs`) keeps tuples and must pass UNMODIFIED — they are the nominal-no-op regression pins. Spec §4 (review-verified): the flip bucket is EMPTY — no existing test combines canonical Std.Nat with a runtime-shape assertion; Task 1 re-verifies with a grep and STOPs if that changed.
- Strict red-green TDD; tests behavioral and immutable once green. ONE mix command at a time, ever (past concurrent run caused a kernel panic); scoped `mix test <file>` per step; the full gate runs ONCE, alone, in Task 4.
- Git: commit per task; EVERY commit `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`; NO Co-Authored-By/trailers; explicit-pathspec staging only.
- Do not run `mix cure.oracle` (destructive; replay inside the full suite covers it).
- STOP-and-report (do not improvise) if: any local-Nat pin fails; the plan-time flip-bucket grep is non-empty; the parametricity sweep (Task 1 Step 0) finds a ctor pattern elaborating against a type-parameter-typed scrutinee; a `test/cure/core/*` or erased-Core-shape test fails; anything would touch `lib/cure/core/` or `erase.ex`.

## File Structure

- `lib/cure/elab/emit.ex` — `nat_ctor?/2` helper; Nat arm in `lower({:ctor,…})`; `nat_branch_clause/3` dispatched from `branch_clause/3`.
- `lib/cure/elab/elaborator.ex` — `resolve_free/2` ctor arm → `eta_expand_bare_ctor/2`; stale comment fix at ~4732.
- `test/cure/elab/nat_int_erasure_test.exs` — NEW: Tasks 1–2 behavioral tests.
- `lib/antigen/generators/elab_nat_rep.ex` — NEW: fixed catalog + seeded corpus of closed canonical-Nat programs.
- `lib/antigen/assays/elab.ex` — one `run/1` clause for `"elab/nat_rep"` + private oracle/decode helpers.
- `lib/antigen/runner.ex` — one registry line.
- `lib/antigen/challenge.ex` — one `@elab_keys` whitelist entry (`"functions" => :functions`).
- `test/antigen/elab_nat_rep_test.exs` — NEW: discrimination + catalog gate + round-trip + wiring.

---

### Task 1: emit-layer Nat hooks (rules 1–3) + nominal pins

**Files:**
- Modify: `lib/cure/elab/emit.ex` (`lower({:ctor,…})` at ~158-169; `branch_clause/3` at ~308-333; helpers near `bool_ctor?` at ~363)
- Test: `test/cure/elab/nat_int_erasure_test.exs` (new)

**Interfaces:**
- Produces: no new public API — behavior only. Task 3's assay relies on: canonical-Nat programs execute to ints on BEAM.

- [ ] **Step 0: Pre-flight sweeps (read-only; STOP conditions)**

1. Flip-bucket re-grep (spec §4): `grep -rl "use Std.Nat" test/` cross-referenced against `grep -rl "compile_and_load\|apply(mod" test/` — expected intersection: EMPTY (review-time fact). Non-empty → STOP and report the files.
2. Parametricity sweep (spec §2.3): confirm `elaborate_match`'s constructor dispatch requires a `{:vdata, …}` scrutinee type (grep `vdata` in the `elaborate_match`/`constructor_pattern` region of `lib/cure/elab/elaborator.ex`) — i.e. no path elaborates `Z()/S(k)` arms against a bare type-parameter-typed scrutinee. If such a path exists → STOP.

- [ ] **Step 1: Write the failing tests**

Note: `Std.Nat` AUTO-LOADS into every module — `test/cure/elab/auto_prelude_test.exs` pins that a bare `Nat` type annotation and the `plus` def resolve without `use`, but that test does NOT exercise bare ctor construction. The evidence that bare `S(...)/Z()` also resolves is architectural, not that single pin: `Cure.Elab.Program`'s `auto_prelude_imports(ast) ++ imports(ast)` (`program.ex:545`) feeds BOTH auto-loaded and explicit `use` sources through the identical `shadow_resolved_imports`/`module_slice_env` merge pipeline — there is no separate, more restricted code path for auto-prelude sources. And `test/cure/elab/type_shadowing_test.exs:95` (`fn imported_one() -> Std.Nat = S(Z())`, mirrored by the `test/oracle/shadow/shadow03_unshadowed_visible.cure` fixture) proves that path DOES resolve bare `S`/`Z` to the imported canonical ctors when `use Std.Nat` supplies them and nothing local shadows the bare names. Since auto-prelude and `use` are the same mechanism, bare ctor construction is expected to resolve the same way with no `use` at all. Canonical-Nat programs need no `use` and must NOT declare a local `type Nat`. All arithmetic defs are written locally in the fixture (over the canonical Nat) so the emitted module is self-contained.

```elixir
defmodule Cure.Elab.NatIntErasureTest do
  @moduledoc """
  Spec 2026-07-08-nat-int-erasure: canonical Std.Nat (auto-prelude, @builtin(:nat))
  erases to BEAM machine integers at emit; locally-redeclared Nat keeps tuples
  (nominal, not structural). Kernel/erased-Core stay inductive — pinned elsewhere
  (test/cure/core/*, global_namespace_soundness_test.exs).
  """
  use ExUnit.Case, async: false

  alias Cure.Elab.{Emit, Program}

  defp run(src, mod_name, fns) do
    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: mod_name, functions: fns)
    mod
  end

  test "rule 1: constructors build machine ints" do
    src = "mod M\n  fn two() -> Nat = S(S(Z()))\n  fn zero() -> Nat = Z()\nend\n"
    mod = run(src, :"Cure.NatInt1", [:two, :zero])
    assert apply(mod, :two, []) == 2
    assert apply(mod, :zero, []) == 0
  end

  test "rule 2: matching S(k) binds the predecessor" do
    src =
      "mod M\n" <>
        "  fn pred(n: Nat) -> Nat = match n\n" <>
        "    Z() -> Z()\n" <>
        "    S(k) -> k\n" <>
        "  fn t() -> Nat = pred(S(S(Z())))\n" <>
        "  fn z() -> Nat = pred(Z())\nend\n"

    mod = run(src, :"Cure.NatInt2", [:pred, :t, :z])
    assert apply(mod, :t, []) == 1
    assert apply(mod, :z, []) == 0
  end

  test "rule 2, deep: S(S(m)) composes two predecessor binds and the body uses m" do
    src =
      "mod M\n" <>
        "  fn sub2(n: Nat) -> Nat = match n\n" <>
        "    S(S(m)) -> m\n" <>
        "    x -> Z()\n" <>
        "  fn t() -> Nat = sub2(S(S(S(Z()))))\nend\n"

    mod = run(src, :"Cure.NatInt3", [:sub2, :t])
    assert apply(mod, :t, []) == 1
  end

  test "rule 3: recursive arithmetic over the Int rep computes correctly" do
    src =
      "mod M\n" <>
        "  fn add(a: Nat, b: Nat) -> Nat = match a\n" <>
        "    Z() -> b\n" <>
        "    S(k) -> S(add(k, b))\n" <>
        "  fn t() -> Nat = add(S(S(Z())), S(S(S(Z()))))\nend\n"

    mod = run(src, :"Cure.NatInt4", [:add, :t])
    assert apply(mod, :t, []) == 5
  end

  test "generics (§2.3 pin): a polymorphic container holds int Nats through generic code" do
    src =
      "mod M\n" <>
        "  type Pair(a: Type, b: Type) = MkP(a, b)\n" <>
        "  fn swap({a: Type}, {b: Type}, p: Pair(a, b)) -> Pair(b, a) = match p\n" <>
        "    MkP(x, y) -> MkP(y, x)\n" <>
        "  fn t() -> Pair(Nat, Nat) = swap(MkP(Z(), S(S(Z()))))\nend\n"

    mod = run(src, :"Cure.NatInt5", [:swap, :t])
    assert apply(mod, :t, []) == {:MkP, 2, 0}
  end

  test "nominal no-op (§2.4 pin): a locally-redeclared Nat still builds tuples" do
    src =
      "mod M\n  type Nat = Z | S(Nat)\n" <>
        "  fn two() -> Nat = S(S(Z()))\nend\n"

    mod = run(src, :"Cure.NatIntLocal", [:two])
    assert apply(mod, :two, []) == {:S, {:S, :Z}}
  end
end
```

Adjustment latitude: if the `swap` fixture's implicit-argument surface shape doesn't elaborate as written (check `test/cure/elab/polymorphic_function_test.exs` for the landed calling convention and mirror it), fix the FIXTURE's surface syntax, never the int-shape assertions. If it still doesn't fit, a monomorphic `Pair(Nat, Nat)` container test (`type P = MkP(Nat, Nat)`, build and deconstruct) is the fallback §2.3 pin — note the substitution in the report.

- [ ] **Step 2: Run to verify the right failures**

Run: `mix test test/cure/elab/nat_int_erasure_test.exs`
Expected: the nominal no-op test PASSES (today's behavior, tuples); the other 5 FAIL with assertion errors showing today's tuple/atom representation, exactly:
- rule 1: `apply(mod, :two, [])` expected `2`, got `{:S, {:S, :Z}}`; `apply(mod, :zero, [])` expected `0`, got `:Z`.
- rule 2: `apply(mod, :t, [])` expected `1`, got `{:S, :Z}`; `apply(mod, :z, [])` expected `0`, got `:Z`.
- rule 2 deep: `apply(mod, :t, [])` expected `1`, got `{:S, :Z}` (the `S(S(m))` match binds `m = {:S, :Z}`, i.e. today's tuple-1).
- rule 3: `apply(mod, :t, [])` expected `5`, got `{:S, {:S, {:S, {:S, {:S, :Z}}}}}`.
- generics: `apply(mod, :t, [])` expected `{:MkP, 2, 0}`, got `{:MkP, {:S, {:S, :Z}}, :Z}`.
If a fixture fails to ELABORATE (not just wrong shape), fix the fixture per Step 1's latitude before proceeding.

- [ ] **Step 3: Implement the emit hooks**

(a) Helper, next to `bool_ctor?` (~emit.ex:363):

```elixir
  # The canonical Std.Nat family (registry-keyed, nominal): its values are BEAM
  # machine integers (spec 2026-07-08-nat-int-erasure). A locally-redeclared
  # structural twin has a different family-id and keeps tuples.
  defp nat_ctor?(env, name) do
    fam = Inductive.builtin(env, :nat)
    fam != nil and Inductive.ctor_family(env, name) == fam
  end
```

(b) `lower(env, {:ctor, name, args}, ctx)` — add the Nat arm to the existing `cond`:

```elixir
  defp lower(env, {:ctor, name, args}, ctx) do
    cond do
      args == [] and bool_ctor?(env, name) ->
        {:atom, @line, bool_atom(name)}

      nat_ctor?(env, name) ->
        case args do
          [] -> {:integer, @line, 0}
          [n] -> {:op, @line, :+, lower(env, n, ctx), {:integer, @line, 1}}
        end

      true ->
        case Enum.map(args, &lower(env, &1, ctx)) do
          [] -> {:atom, @line, name}
          forms -> {:tuple, @line, [{:atom, @line, name} | forms]}
        end
    end
  end
```

(The `[]`/`[n]` shapes are exhaustive by the validated `:nat` schema `[{:Z,0},{:S,1}]` — `Builtins.validate!` guarantees no other arity can be registered under `:nat`.)

(c) `branch_clause/3` — dispatch Nat branches to a dedicated builder; each branch decides by its OWN ctor (so an impossible-branch-omitted single-branch Nat case still lowers correctly):

At the top of `branch_clause(env, {cname, arity, body}, ctx)`:

```elixir
  defp branch_clause(env, {cname, arity, body}, ctx) do
    if nat_ctor?(env, cname) do
      nat_branch_clause(env, {cname, arity, body}, ctx)
    else
      # ... existing body unchanged ...
    end
  end
```

New builder (spec §2.2a/c — this introduces emit.ex's FIRST non-empty clause guard and FIRST multi-statement clause body; treat both as deliberate):

```elixir
  # case-on-Nat (spec §2.2): the zero ctor's branch matches literal 0; the succ
  # ctor's branch matches a fresh N with guard `N > 0` (belt-and-braces: a rep
  # bug crashes loudly instead of binding k = -1) and binds the predecessor as
  # the body's first statement — Erlang patterns/guards cannot compute-and-bind,
  # so `K = N - 1` must open the body, making it a two-form list. The body's
  # de Bruijn frame still counts the field (index 0 = predecessor), exactly as
  # the tuple form would have bound it.
  defp nat_branch_clause(env, {_zero, 0, body}, ctx) do
    {:clause, @line, [{:integer, @line, 0}], [], [lower(env, body, ctx)]}
  end

  defp nat_branch_clause(env, {_succ, 1, body}, ctx) do
    base = length(ctx)
    k = :"V#{base}"
    n = :"N#{base}"
    body_form = lower(env, body, [k | ctx])
    k_var = underscore_if_unused({:var, @line, k}, body_form)
    bind = {:match, @line, k_var, {:op, @line, :-, {:var, @line, n}, {:integer, @line, 1}}}
    guard = [[{:op, @line, :>, {:var, @line, n}, {:integer, @line, 0}}]]
    {:clause, @line, [{:var, @line, n}], guard, [bind, body_form]}
  end
```

Implementation notes:
- `underscore_if_unused/2` is the existing helper (used in the present-fields comprehension) — reusing it keeps `erl_lint`'s `unused_var` clean when the S-branch body ignores the predecessor.
- The guard list shape is `[[test]]` (list of conjunct-lists) in the abstract format.
- Do NOT touch the erased-field slot logic of the generic path; the canonical S has one `:present` field by schema, so the Nat builder handles quantities implicitly.

- [ ] **Step 4: Run to verify green**

Run: `mix test test/cure/elab/nat_int_erasure_test.exs`
Expected: 6 tests, 0 failures.

- [ ] **Step 5: Run the nominal/layering pin suites (one at a time)**

- `mix test test/cure/elab/` (the WHOLE directory, not a sample — Task 1's emit-hook change is exactly what could regress any of the ≈46 local-Nat fixture files the Global Constraints call out, and it must be isolated to Task 1 BEFORE Task 2's elaborator change lands, so a regression can't be misattributed to the wrong commit): expected all pass unchanged, local-Nat fixtures included.
- `mix test test/cure/core/` — kernel pins: expected all pass unchanged.
- `mix test test/cure/compiler/dependent_vec_codegen_test.exs` — local-Nat codegen pin (outside `test/cure/elab/`, so not covered by the directory run above): expected pass unchanged.

Any failure here → STOP and report (these are the spec's do-not-touch pins).

- [ ] **Step 6: Commit**

```bash
git add -- lib/cure/elab/emit.ex test/cure/elab/nat_int_erasure_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(emit): Nat->Int runtime erasure — canonical Std.Nat lowers to machine ints" \
  -- lib/cure/elab/emit.ex test/cure/elab/nat_int_erasure_test.exs
```

---

### Task 2: first-class constructors — `resolve_free` eta-expansion (rule 4)

**Files:**
- Modify: `lib/cure/elab/elaborator.ex` (`resolve_free/2` at ~4745-4772 and the stale "only ever yields the NULLARY" comment at ~4732)
- Test: `test/cure/elab/nat_int_erasure_test.exs` (append)

**Interfaces:**
- Consumes: `Inductive.get_ctor/2` → `%{args: telescope [{atom, Term}], quantities: [:present|:erased], result_params: [Term], result_indices: [Term]}`.
- Produces: bare positive-arity ctor references elaborate (checked position) for ctors with all-`:present` args and empty `result_params`/`result_indices`.

- [ ] **Step 1: Append the failing tests**

```elixir
  describe "rule 4: first-class constructors (resolve_free eta-expansion)" do
    test "S passed to a HOF applies as the increment function" do
      src =
        "mod M\n" <>
          "  fn ap(f: Nat -> Nat, n: Nat) -> Nat = f(n)\n" <>
          "  fn t() -> Nat = ap(S, S(Z()))\nend\n"

      mod = run(src, :"Cure.NatIntEta1", [:ap, :t])
      assert apply(mod, :t, []) == 2
    end

    test "eta-expansion is general: a non-Nat positive-arity ctor works first-class" do
      src =
        "mod M\n  type Box = Mk(Int)\n" <>
          "  fn ap(f: Int -> Box, i: Int) -> Box = f(i)\n" <>
          "  fn t() -> Box = ap(Mk, 3)\nend\n"

      mod = run(src, :"Cure.NatIntEta2", [:ap, :t])
      assert apply(mod, :t, []) == {:Mk, 3}
    end
  end
```

- [ ] **Step 2: Run to verify the right failures**

Run: `mix test test/cure/elab/nat_int_erasure_test.exs`
Expected: 8 tests, the 2 new ones fail at ELABORATION — `run/3`'s `{:ok, env} = Program.elaborate(src)` MatchError, with the underlying error being the kernel's `{:error, :ctor_arity}`-shaped rejection (bare `S`/`Mk` resolves to a nullary `{:ctor, _, []}` today). Capture the exact error term in the report.

- [ ] **Step 3: Implement the eta-expansion**

Replace `resolve_free/2`'s first cond arm (`Inductive.get_ctor(env, atom) -> {:ok, {:ctor, atom, []}}`) with:

```elixir
      Inductive.get_ctor(env, atom) ->
        eta_expand_bare_ctor(env, atom)
```

Add (near `resolve_free`):

```elixir
  # A bare positive-arity constructor reference eta-expands to nested lambdas
  # (`S` becomes `λ n:Nat. S(n)`) so first-class ctor values elaborate instead
  # of dying at the kernel's arity check (:ctor_arity) — the general gap behind
  # spec 2026-07-08-nat-int-erasure rule 4 (Idris allows bare `S` everywhere).
  # Scope: ctors whose args are all explicit/:present and whose result carries
  # no params/indices. An implicit-carrying or indexed ctor keeps today's
  # nullary resolution (and today's downstream error): a lambda-typed value
  # cannot receive implicit insertion at its call sites, so eta-expanding it
  # would produce an unusable value rather than a working one.
  defp eta_expand_bare_ctor(env, atom) do
    %{args: tele, quantities: qs, result_params: rp, result_indices: ri} =
      Inductive.get_ctor(env, atom)

    k = length(tele)

    if k > 0 and Enum.all?(qs, &(&1 == :present)) and rp == [] and ri == [] do
      body_args = for i <- (k - 1)..0//-1, do: {:var, i}
      body = {:ctor, atom, body_args}

      {:ok,
       Enum.reduce(Enum.reverse(tele), body, fn {_name, dom}, acc -> {:lam, dom, acc} end)}
    else
      {:ok, {:ctor, atom, []}}
    end
  end
```

(Telescope domains are already de Bruijn-scoped over the earlier args, so wrapping inner-to-outer lines the binders up; the first arg is `{:var, k-1}` under `k` binders. `result_params`/`result_indices` ARE `[]` for a plain ctor, confirmed at review time: `lib/cure/core/inductive.ex`'s `ctor/3` (line ~155) and `ctor/4` (line ~160) both default through to `ctor/5` (line ~172, `%{... result_indices: result_indices, result_params: result_params, ...}`) with a literal `[]` for the omitted arguments — never `nil`. No `iex` needed to confirm this; it's read directly off the builder chain.)

Also update the now-stale comment at ~elaborator.ex:4732 ("`resolve_free` only ever yields the NULLARY `{:ctor, atom, []}`") to say the saturated-call clause builds the saturated ctor directly while `resolve_free` eta-expands bare positive-arity ctors (all-present, unindexed) and yields the nullary form otherwise.

- [ ] **Step 4: Run to verify green**

Run: `mix test test/cure/elab/nat_int_erasure_test.exs`
Expected: 8 tests, 0 failures.

- [ ] **Step 5: Neighboring suites (resolution/scoping is touchy — verify no fallout)**

Run (one at a time): `mix test test/cure/elab/resolution_test.exs test/cure/elab/type_shadowing_test.exs test/cure/elab/global_namespace_soundness_test.exs`, then `mix test test/cure/elab/`.
Expected: all pass. A failure implicating `resolve_free` → STOP and report (the eta-expansion must be additive: it only changes behavior for terms that previously FAILED to elaborate; any previously-passing program that now elaborates differently is a real finding).

- [ ] **Step 6: Commit**

```bash
git add -- lib/cure/elab/elaborator.ex test/cure/elab/nat_int_erasure_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(elab): eta-expand bare positive-arity constructors (first-class S; general fix)" \
  -- lib/cure/elab/elaborator.ex test/cure/elab/nat_int_erasure_test.exs
```

---

### Task 3: Antigen `elab/nat_rep` representation-agreement assay

**Files:**
- Create: `lib/antigen/generators/elab_nat_rep.ex`
- Modify: `lib/antigen/assays/elab.ex` (one `run/1` clause + private helpers, inserted after the `"elab/guard_lint"` relation clause, before `elab/soundness`)
- Modify: `lib/antigen/runner.ex` (one line after `defp assay_module("elab/guard_lint")`)
- Modify: `lib/antigen/challenge.ex` (`@elab_keys` whitelist: add `"functions" => :functions`) — CONFIRMED required, not a maybe: read at review time, the whitelist (`challenge.ex:491-500`) has no `functions` entry and `from_pieces(:elab_program, ...)` raises `ArgumentError, "unknown elab payload key functions"` for any key not in the map. The round-trip test's payload carries `functions: [...]`, so this fires deterministically once the generator exists (Step 4) — this is not conditional on what "the red run demands."
- Test: `test/antigen/elab_nat_rep_test.exs`

**Interfaces:**
- Consumes: `Challenge.new/1`; `Cure.Core.Normalise.nf(Context.empty(sig_env), term, delta: :certified, mode: :nf)` (spec §3's verified oracle call — NOT `Eval.eval/2`, which leaves globals as stuck neutrals); `Cure.Elab.Emit.compile_and_load/2`.
- Produces: `Antigen.Generators.ElabNatRep.nat_rep_challenges/0`, `catalog/0`, `source/1`; assay label `"elab/nat_rep"`.

This is genuinely new Antigen plumbing (spec §3's verified note): no existing assay combines kernel normalisation with BEAM execution. Every generated program is fully self-contained — canonical auto-prelude `Nat` (NO local `type Nat`, NO `use`), local arithmetic defs only (no cross-module def references reach the emitted BEAM module), one 0-ary `fn main() -> Nat`.

- [ ] **Step 1: Write the failing tests**

```elixir
defmodule Antigen.ElabNatRepTest do
  @moduledoc """
  Spec 2026-07-08-nat-int-erasure §3: representation agreement. The kernel's
  certified-δ normalisation of `main` (inductive semantics, decoded S-spine →
  integer) must equal BEAM execution of the emitted module (Int rep). Kernel is
  the oracle; emit is the system under test.
  """
  use ExUnit.Case, async: false

  alias Antigen.Challenge
  alias Antigen.Assays.Elab, as: Assay
  alias Antigen.Generators.ElabNatRep, as: Gen

  test "assay discrimination: an unelaborable program is a violation" do
    c =
      Challenge.new(
        kind: :elab_program,
        assay: "elab/nat_rep",
        label: :none,
        payload: %{id: "broken", src: "mod P\n  fn\nend\n", functions: [:main]},
        note: "discrimination"
      )

    assert {:violation, {:nat_rep_program_rejected, "broken", _}} = Assay.run(c)
  end

  test "catalog gate: every cell agrees (kernel int == BEAM int)" do
    challenges = Gen.nat_rep_challenges()
    assert length(challenges) >= 8

    for c <- challenges do
      assert Assay.run(c) == :ok, "nat_rep cell #{c.payload.id} disagreed"
    end
  end

  test "corpus round-trip survives to_pieces/from_pieces" do
    [c | _] = Gen.nat_rep_challenges()
    {scaffold, pieces} = Challenge.to_pieces(c)
    c2 = Challenge.from_pieces(:elab_program, c.assay, c.label, c.seed, c.note, scaffold, pieces)
    assert Assay.run(c2) == :ok
  end

  test "runner registry resolves the assay" do
    assert Antigen.Runner.assay_module_for("elab/nat_rep") == Antigen.Assays.Elab
  end
end
```

`Challenge.to_pieces/from_pieces` WILL reject the `functions` payload key: `lib/antigen/challenge.ex`'s `@elab_keys` whitelist (lines 491-500) has no `functions` entry, and `from_pieces(:elab_program, ...)` raises `ArgumentError, "unknown elab payload key functions"` for any key outside the whitelist. Confirmed at review time, not a hypothetical — see Step 3(d) below. (The atom-list VALUE itself is fine: `Corpus`'s actual wire format is `:erlang.term_to_binary/Base.encode64`, not JSON, so an atom list round-trips through the scaffold with no encoding change needed — only the key needs whitelisting.)

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/antigen/elab_nat_rep_test.exs`
Expected, per test:
- discrimination: `FunctionClauseError` in `Antigen.Assays.Elab.run/1` (no `"elab/nat_rep"` clause matches the challenge).
- catalog gate: `UndefinedFunctionError` — `Antigen.Generators.ElabNatRep.nat_rep_challenges/0` is undefined.
- corpus round-trip: `UndefinedFunctionError` on the same call (fails before `to_pieces`/`from_pieces` is ever reached).
- runner registry: `UndefinedFunctionError` or a non-matching return from `Antigen.Runner.assay_module_for/1` (no `"elab/nat_rep"` registry line).

- [ ] **Step 3: Implement generator, assay clause, registry line, and the `@elab_keys` whitelist entry**

(a) `lib/antigen/generators/elab_nat_rep.ex`:

```elixir
defmodule Antigen.Generators.ElabNatRep do
  @moduledoc """
  Representation-agreement corpus for Nat->Int erasure (spec
  2026-07-08-nat-int-erasure §3): closed, self-contained programs over the
  CANONICAL auto-prelude Std.Nat (no local `type Nat`, no `use`) with local
  arithmetic defs and a 0-ary `main`. The assay compares the kernel's
  certified-δ normalisation of `main` (decoded ctor spine) against BEAM
  execution of the emitted module. Fixed cells cover each lowering rule;
  seeded cells add depth-varied arithmetic expressions (deterministic per
  seed — no runtime randomness).
  """

  alias Antigen.Challenge

  @defs """
    fn add(a: Nat, b: Nat) -> Nat = match a
      Z() -> b
      S(k) -> S(add(k, b))
    fn dbl(n: Nat) -> Nat = match n
      Z() -> Z()
      S(k) -> S(S(dbl(k)))
    fn pred(n: Nat) -> Nat = match n
      Z() -> Z()
      S(k) -> k
  """

  @functions [:add, :dbl, :pred, :main]

  defp program(main_expr),
    do: "mod P\n" <> @defs <> "  fn main() -> Nat = " <> main_expr <> "\nend\n"

  defp nat_lit(0), do: "Z()"
  defp nat_lit(n) when n > 0, do: "S(" <> nat_lit(n - 1) <> ")"

  @fixed [
    {"ctor/zero", "Z()"},
    {"ctor/three", "S(S(S(Z())))"},
    {"match/pred", "pred(S(S(Z())))"},
    {"match/pred_zero", "pred(Z())"},
    {"arith/add", "add(S(S(Z())), S(S(S(Z()))))"},
    {"arith/dbl", "dbl(S(S(Z())))"},
    {"arith/nested", "add(dbl(S(Z())), pred(S(S(S(Z())))))"},
    {"arith/deep", "dbl(dbl(dbl(S(Z()))))"}
  ]

  # Deterministic seeded arithmetic expressions (pure function of the seed —
  # Antigen scripts/tests must not use runtime randomness).
  defp seeded_expr(seed) do
    a = rem(seed * 7, 5)
    b = rem(seed * 13, 4)

    case rem(seed, 3) do
      0 -> "add(" <> nat_lit(a) <> ", dbl(" <> nat_lit(b) <> "))"
      1 -> "dbl(add(" <> nat_lit(a) <> ", " <> nat_lit(b) <> "))"
      2 -> "pred(add(" <> nat_lit(a + 1) <> ", " <> nat_lit(b) <> "))"
    end
  end

  @doc "All representation-agreement challenges (8 fixed + 6 seeded)."
  @spec nat_rep_challenges() :: [Challenge.t()]
  def nat_rep_challenges do
    fixed =
      Enum.map(@fixed, fn {id, expr} ->
        challenge(id, expr)
      end)

    seeded = for s <- 1..6, do: challenge("seeded/#{s}", seeded_expr(s))

    fixed ++ seeded
  end

  @doc "Catalog ids with their main expressions."
  @spec catalog() :: [{String.t(), String.t()}]
  def catalog, do: Enum.map(@fixed, fn {id, expr} -> {id, expr} end)

  @doc "Full module source for a fixed cell id."
  @spec source(String.t()) :: String.t() | nil
  def source(id) do
    case Enum.find(@fixed, fn {i, _} -> i == id end) do
      {_id, expr} -> program(expr)
      nil -> nil
    end
  end

  defp challenge(id, expr) do
    Challenge.new(
      kind: :elab_program,
      assay: "elab/nat_rep",
      label: :agree,
      payload: %{id: id, src: program(expr), functions: @functions},
      note: "kernel-vs-BEAM agreement for `#{expr}`"
    )
  end
end
```

(b) Assay clause in `lib/antigen/assays/elab.ex` (after the `"elab/guard_lint"` relation clause). No new alias needed: `Context` is already aliased there (used unqualified, e.g. `Context.empty(env)` at `elab.ex:216`), but `Normalise` is NOT — the file's one existing `Normalise` call (`Cure.Core.Normalise.with_fuel/2`, `elab.ex:224`) is already written fully-qualified, so match that precedent rather than introducing a new alias for a module the file has deliberately kept qualified:

```elixir
  # elab/nat_rep — representation agreement (spec 2026-07-08-nat-int-erasure §3):
  # the kernel's certified-δ normalisation of `main` (inductive semantics; the
  # trusted oracle) must decode to the same integer BEAM execution returns
  # (Int-rep emit; the system under test). NOT Eval.eval/2 — that leaves
  # `{:global, _}` heads as stuck neutrals and cannot reduce `add(...)`.
  def run(%Challenge{kind: :elab_program, assay: "elab/nat_rep", payload: p}) do
    case elaborate(p.src) do
      {:ok, env} ->
        kernel = kernel_nat(env)
        beam = beam_nat(env, p)

        cond do
          match?({:stuck, _}, kernel) ->
            {:violation, {:nat_rep_kernel_stuck, p.id, elem(kernel, 1)}}

          match?({:failed, _}, beam) ->
            {:violation, {:nat_rep_beam_failed, p.id, elem(beam, 1)}}

          kernel != beam ->
            {:violation, {:nat_rep_mismatch, p.id, %{kernel: kernel, beam: beam}}}

          true ->
            :ok
        end

      other ->
        # `other` cannot be `{:ok, _}` here (already matched above), so
        # `verdict_bit(other)` would always be the tautological `:reject` —
        # carry the actual rejection term instead, so a real corpus regression
        # is debuggable rather than reporting a constant.
        {:violation, {:nat_rep_program_rejected, p.id, other}}
    end
  end

  defp kernel_nat(env) do
    ctx = Context.empty(env)

    case Cure.Core.Normalise.nf(ctx, {:global, :main}, delta: :certified, mode: :nf) do
      :fuel_exhausted -> {:stuck, :fuel_exhausted}
      term -> decode_nat(term)
    end
  end

  # Bare atoms only: none of this corpus's fixed/seeded programs declare a
  # local `type Nat` (§2.4 nominal rule), so the canonical `:Z`/`:S` ctors
  # never collide and are never re-keyed (verified: `Cure.Elab.Resolution`'s
  # re-key path only fires when a LOCAL declaration shadows an import, and
  # even then uses a `"Mod#name"` atom, e.g. `:"Std.Nat#Z"` — never the
  # `"Std.Nat.Z"` dot-form). If a future corpus addition ever needs a
  # colliding-import case, add the real `#`-separated guard then; don't
  # speculate here.
  defp decode_nat({:ctor, :Z, []}), do: {:nat, 0}

  defp decode_nat({:ctor, :S, [inner]}) do
    case decode_nat(inner) do
      {:nat, n} -> {:nat, n + 1}
      other -> other
    end
  end

  defp decode_nat(other), do: {:stuck, other}

  defp beam_nat(env, p) do
    mod_name = :"Antigen.NatRep.#{:erlang.phash2(p.id)}"

    case Cure.Elab.Emit.compile_and_load(env, module: mod_name, functions: p.functions) do
      {:ok, mod} ->
        case apply(mod, :main, []) do
          n when is_integer(n) -> {:nat, n}
          other -> {:failed, {:non_integer, other}}
        end

      err ->
        {:failed, err}
    end
  rescue
    e -> {:failed, {:raised, e}}
  end
```

Implementation notes:
- `decode_nat` matches only the bare `:Z`/`:S` atoms (confirmed the canonical form — see the comment above it). If a future red run somehow surfaces a different atom (e.g. this corpus grows a colliding-import fixture later), that is itself a finding to investigate, not a signal to silently widen the guard.
- `kernel_nat` requires `Std.Nat`'s… actually the local `add/dbl/pred` defs to be certified for δ-unfolding — they are structurally recursive, exactly what `maybe_certify` certifies during ordinary elaboration. If `nf` returns a stuck `{:global, …}` head at red time, that's a `{:nat_rep_kernel_stuck, …}` violation to investigate, not to paper over.
- If `Normalise.nf`'s option names differ (`mode: :nf` may be implicit/absent), read `lib/cure/core/normalise.ex:36-37,97-231` and use the real option set; the spec's requirement is `delta: :certified`.

(c) `lib/antigen/runner.ex`: after the `"elab/guard_lint"` line:

```elixir
  defp assay_module("elab/nat_rep"), do: Antigen.Assays.Elab
```

(d) `lib/antigen/challenge.ex`'s `@elab_keys` whitelist (confirmed required — see the Files note above): add one entry so the payload's `functions` key survives `to_pieces`/`from_pieces`:

```elixir
  @elab_keys %{
    "id" => :id,
    "src" => :src,
    "transform" => :transform,
    "base_src" => :base_src,
    "variant_src" => :variant_src,
    "expect" => :expect,
    "relation" => :relation,
    "expect_error" => :expect_error,
    "functions" => :functions
  }
```

- [ ] **Step 4: Run to verify green**

Run: `mix test test/antigen/elab_nat_rep_test.exs`
Expected: 4 tests, 0 failures (catalog gate = 14 agreeing cells). A `{:nat_rep_mismatch, …}` here is a REAL representation bug in Task 1's emit hooks — fix emit (with a new focused unit test in `nat_int_erasure_test.exs` reproducing it), never the oracle or the catalog.

- [ ] **Step 5: Neighboring Antigen suites**

Run: `mix test test/antigen/elab_guard_lint_test.exs test/antigen/elab_dot_forcing_test.exs test/antigen/elab_erasure_test.exs`
Expected: all pass (clause insertion must not disturb existing dispatch).

- [ ] **Step 6: Commit**

```bash
git add -- lib/antigen/generators/elab_nat_rep.ex lib/antigen/assays/elab.ex lib/antigen/runner.ex lib/antigen/challenge.ex test/antigen/elab_nat_rep_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(antigen): elab/nat_rep representation-agreement assay (kernel nf vs BEAM)" \
  -- lib/antigen/generators/elab_nat_rep.ex lib/antigen/assays/elab.ex lib/antigen/runner.ex lib/antigen/challenge.ex test/antigen/elab_nat_rep_test.exs
```

---

### Task 4: roadmap note + full gate + final verification

**Files:**
- Modify: `docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md` (§4.2 status prose)

- [ ] **Step 1: Roadmap status sentence**

In `docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md`, §4.2 "Current focus + explicit deferral (2026-07-03)", the first paragraph ends "...the mechanism does double duty." (confirmed at review time — this is the paragraph's last line). Append a new paragraph immediately after it (before the "**DEFERRED to work on the above...**" paragraph): "Phase 2 landed (spec 2026-07-08-nat-int-erasure): canonical Std.Nat erases to BEAM machine ints (Z→0, S→+1, case→zero-test/predecessor-bind), nominal-only (local Nat redeclarations keep tuples); bare positive-arity constructors now eta-expand (first-class `S`, general fix); representation agreement pinned by the Antigen elab/nat_rep assay (kernel certified-δ nf vs BEAM)."

- [ ] **Step 2: Commit the doc**

```bash
git add -- docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "docs: roadmap §4.2 — Nat->Int erasure (foundation Phase 2) landed" \
  -- docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md
```

- [ ] **Step 3: Full gate (ONE at a time, alone, in this order)**

1. `mix test test/antigen/` — expected: 490 tests (486 + 4 new), 0 failures.
2. `mix test` — expected: ~3238 tests (3226 + 8 elab + 4 antigen — recount against the actual suite the red steps produced), 0 failures; includes oracle replay green (verdicts are representation-independent). One known non-reproducible Antigen-seed flake exists: if exactly one Antigen seed failure appears, re-run the full suite once (alone); if it doesn't reproduce, note it honestly. Any other failure = STOP and report.

- [ ] **Step 4: Final verification**

- `git diff --stat <task1-commit>~1 HEAD -- lib/cure/core/ lib/cure/types/ lib/cure/compiler/ lib/cure/elab/erase.ex` must be EMPTY.
- `git log --format='%an %ae' <task1-commit>~1..HEAD` shows only `Made In Heaven madeinheaven@madeinheaven.com`.
- Spot-confirm acceptance §7.4: `mix test test/cure/compiler/dependent_vec_codegen_test.exs` was already green in Task 1 Step 5 (local-Nat tuples intact).

---

## Self-review notes (spec-coverage map)

- §1 rules 1–3 → Task 1; rule 4 → Task 2 (elaborator, per the spec's verified §2.1 third bullet). §2.2a/c guard + multi-statement body → Task 1 Step 3(c) with the dedicated deep-pattern red test. §2.2b compositionality → the `S(S(m))` test. §2.3 pin → Task 1's generics test (+ Step 0 parametricity sweep with STOP). §2.4 nominal pins → Task 1's local-Nat test + Step 5 suites. §2.5 layering pins → Task 1 Step 5 + Task 4 Step 4 diffs. §3 representation agreement → Task 3 (with the spec's verified `Normalise.nf` oracle call and the new-plumbing budget note). §4 flip policy → Task 1 Step 0 re-grep (expected empty) + STOP protocol. §7 acceptance criteria 1-7 → Tasks 1/2/1/1/3/4-Step-4/4-Step-3 respectively.
- Deliberate scope boundary (from the spec's §2.1): eta-expansion covers all-present unindexed ctors; implicit-carrying/indexed ctors keep today's behavior — the plan's Task 2 comment documents why (implicit insertion cannot target lambda-typed values).
- Follow-ups NOT in this plan (spec §6): Std.Nat arithmetic native inlining; `use Std.Nat` lint; Bounded/Fin.
