# Local Type/Constructor Shadowing Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make a module's local `type Nat = Zero | Suc` fully shadow an imported/auto-imported namesake — including its constructors — so `match` coverage no longer demands the imported ctors (`{:missing_branch, :S}`), while keeping the imported family reachable via a qualified escape hatch (`Std.Nat.Z`).

**Architecture:** A new **E-layer resolution module** (`lib/cure/elab/resolution.ex`) sits over the bare-atom registry. Collision detection runs in `program.ex` before elaboration, driven by an **AST-own-declaration provenance scan over the full transitive import closure** (each reachable module's *own* declared family names — not just direct imports — so a family owned by a module reached only transitively is still correctly attributed, while transitively-reached DUPLICATE copies of the same module are not phantom sources). Colliding imported families are **re-keyed** per-slice (`:Nat` → `:"Std.Nat#Nat"`, `:Z` → `:"Std.Nat#Z"`) *before* the import merge, and residual bare copies are dropped (by family name, across the whole merged env, regardless of which slice contributed them) before the local module merges on top — so `Inductive.ctors_of/2` naturally returns the disowned set with zero kernel change. Qualified references and shadow diagnostics are **derived from the already-re-keyed env** (no new parameter threading, no core `Env` field). The only C-layer touch teaches codegen's purely-syntactic call dispatch to recognize a qualified constructor reference (`Std.Nat.Z()`) BEFORE its generic qualified-call (remote-function-call) branch — codegen never sees the elaborator's re-keyed atoms at all, so no runtime-tag stripping logic is needed once the dispatch is corrected.

**Tech Stack:** Elixir; Cure dependent elaborator (`lib/cure/elab/*`) + kernel registry (`lib/cure/core/*`, read-only for term shapes); differential oracle (`mix cure.oracle`, `idris2`); ExUnit.

## Global Constraints

- **No kernel/TCB change.** `lib/cure/core/*` is NOT modified. The resolution layer and its Core-term rewrite live entirely in `lib/cure/elab/*`; term shapes in `term.ex` are read (matched), never edited.
- **No core `Env` struct field added.** The resolution info is either baked into the re-keyed env's existing maps or derived from them on demand. `lib/cure/core/env.ex` (`inductive.ex`'s `Cure.Core.Env`) is untouched.
- **R6 non-regression is byte-for-byte on the non-collision path.** Every currently-green program must elaborate identically. Baseline: `mix test` at 2843/0 (or higher), `mix test test/oracle_replay_test.exs` green.
- **Auto-prelude skip is RETAINED (lowest-risk choice per spec §3.1).** `auto_prelude_imports/1` keeps skipping `Std.Bool`/`Std.Nat` when the module declares a same-named type. Re-keying is validated against **explicit `use`**. Existing `test/cure/elab/auto_prelude_test.exs` must stay green.
- **Runtime constructor tags stay bare** (AtomVM value invariant): codegen emits the same bare `:z` tag for `Std.Nat.Z()` (qualified/escape-hatch) as it does for a plain unqualified `Z()` — achieved by recognizing the qualified constructor call syntactically before codegen's generic qualified-call (remote-call) dispatch, not by stripping a registry-internal separator codegen never sees (see Task 11).
- **Ghost-writer commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, NO `Co-Authored-By`, no Claude signature.
- **Explicit-pathspec staging only:** `git add -- <path>` (never `-A`/`.`). A concurrent agent may share the worktree.
- **One build at a time.** Never run two `mix` suites concurrently. Prefer scoped `mix test <file>`; run the full suite once, alone, at the gate.
- **Oracle probes** are faithful `.cure`/`.idr` transliterations (`.idr` carries `%default total`, no `module` line). Never hand-write a verdict; `mix cure.oracle shadow` generates `verdicts.json`.

---

## File Structure

- **Create** `lib/cure/elab/resolution.ex` — `Cure.Elab.Resolution`: the whole resolution layer. Pure functions over `Cure.Core.Env`. Responsibilities: (1) `rekey_term/2` Core-term atom substitution; (2) `rekey_module_env/3` re-key one module's owned families/ctors/defs; (3) `classify/2` collision detection over AST provenance; (4) `resolve_qualified/3` dotted-path → registry key; (5) `shadowed_origin/2` + `ambiguous_modules/2` diagnostic helpers.
- **Modify** `lib/cure/elab/program.ex` — `check_ast/1` and the import pipeline: build distinct per-module slices, classify, re-key losers, drop residual bare keys, merge local on top.
- **Modify** `lib/cure/elab/elaborator.ex` — resolve qualified ctor keys at `constructor_pattern` callers (`partition_arms`, `partition_rematch_arms`) and `elaborate_named_call`; the R5 `:shadowed_ctor` diagnostic at the unknown-constructor gate; R7 `:ambiguous_name` on bare value lookup.
- **Modify** `lib/cure/elab/declarations.ex` — `idx_to_core` `{:function_call,…}` and `{:attribute_access,…}` clauses + `resolve_index_name` for qualified type-slot references and R7 on bare type lookup.
- **Modify** `lib/cure/compiler/codegen.ex` — `compile_function_call/3` gains a dispatch clause recognizing a qualified constructor call (e.g. `Std.Nat.Z()`) before its generic qualified/remote-call branch; `constructor_tag/1` itself is unmodified.
- **Create** `test/cure/elab/resolution_test.exs` — unit tests for the `Resolution` module (rekey_term, rekey_module_env, classify, resolve_qualified).
- **Create** `test/cure/elab/type_shadowing_test.exs` — end-to-end `Program.elaborate/1` behavioral tests (R1–R5, R7).
- **Create** `test/oracle/shadow/` — oracle cluster: `shadow01`–`shadow08` `.cure`/`.idr` pairs (shadow07 is import-vs-import ambiguity, added last in Task 10; shadow08 is the transitive-import case, added in Task 5) + generated `verdicts.json`.

---

## Interfaces (the contract every task shares)

The `Resolution` module's public surface, defined across Tasks 2–4, 6, 9, 10 and consumed by Tasks 5, 7, 8, 9, 10:

```
Cure.Elab.Resolution.rekey_term(term :: Core.Term.t(), atom_map :: %{atom() => atom()}) :: Core.Term.t()
Cure.Elab.Resolution.rekey_module_env(env :: Env.t(), module_id :: String.t(), owned_family_names :: MapSet.t(atom())) :: Env.t()
Cure.Elab.Resolution.classify(family_owners :: %{atom() => MapSet.t(String.t())}, local_families :: MapSet.t(atom())) :: %{losers: %{String.t() => MapSet.t(atom())}, ambiguous: MapSet.t(atom())}
Cure.Elab.Resolution.resolve_qualified(env :: Env.t(), dotted :: String.t(), slot :: :type | :value) :: {:ok, atom()} | :error
Cure.Elab.Resolution.shadowed_origin(env :: Env.t(), bare :: atom()) :: {:ok, module_id :: String.t(), rekeyed :: atom()} | :error
Cure.Elab.Resolution.ambiguous_modules(env :: Env.t(), bare :: atom()) :: [String.t()]   # ≥2 ⇒ ambiguous
```

`module_id` is a canonical dotted path string, e.g. `"Std.Nat"`. A re-keyed atom is `:"<module_id>#<bare>"`, e.g. `:"Std.Nat#Z"`. The qualified surface path uses `.` (`"Std.Nat.Z"`); the registry key uses `#` (`:"Std.Nat#Z"`). Task 6's `resolve_qualified` is the single place that bridges `.`→`#`.

---

### Task 1: Red repro — oracle cluster + failing behavioral test

**Files:**
- Create: `test/oracle/shadow/shadow01_explicit_use_local_shadow.cure`
- Create: `test/oracle/shadow/shadow01_explicit_use_local_shadow.idr`
- Create: `test/cure/elab/type_shadowing_test.exs`

**Interfaces:**
- Consumes: `Cure.Elab.Program.elaborate/1` (existing).
- Produces: the `shadow` cluster directory; the `type_shadowing_test.exs` file that later tasks extend.

- [ ] **Step 1: Write the failing oracle probe (`.cure`)**

`test/oracle/shadow/shadow01_explicit_use_local_shadow.cure`:
```
mod ExplicitShadow
  use Std.Nat
  type Nat = Zero | Suc(Nat)
  fn add(a: Nat, b: Nat) -> Nat = match a
    Zero() -> b
    Suc(m) -> Suc(add(m, b))
end
```

- [ ] **Step 2: Write the faithful Idris transliteration (`.idr`)**

`test/oracle/shadow/shadow01_explicit_use_local_shadow.idr`:
```idris
%default total

data Nat' = Zero | Suc Nat'

add : Nat' -> Nat' -> Nat'
add Zero b = b
add (Suc m) b = Suc (add m b)
```
(Idris' own `Nat` is always in scope from its prelude; a local `data Nat'` faithfully models "a local datatype shadowing a same-named library one" without fighting Idris' prelude. The behavior under test — local datatype + its own constructors cover the match — is identical.)

- [ ] **Step 3: Write the red behavioral test**

`test/cure/elab/type_shadowing_test.exs`:
```elixir
defmodule Cure.Elab.TypeShadowingTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.Program

  defp elaborate(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    Program.check_ast(ast)
  end

  test "R1a: explicit `use Std.Nat` + local `Nat = Zero|Suc` — local ctors cover the match" do
    src = """
    mod ExplicitShadow
      use Std.Nat
      type Nat = Zero | Suc(Nat)
      fn add(a: Nat, b: Nat) -> Nat = match a
        Zero() -> b
        Suc(m) -> Suc(add(m, b))
    end
    """

    assert {:ok, _env} = elaborate(src)
  end
end
```

- [ ] **Step 4: Run the test to confirm it fails with the target bug**

Run: `mix test test/cure/elab/type_shadowing_test.exs`
Expected: FAIL — `elaborate/1` returns `{:error, {:missing_branch, :S}}` (the exact bug the spec §1.1 reproduces), so the `assert {:ok, _}` fails.

- [ ] **Step 5: Commit**

```bash
git add -- test/oracle/shadow/shadow01_explicit_use_local_shadow.cure test/oracle/shadow/shadow01_explicit_use_local_shadow.idr test/cure/elab/type_shadowing_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "test(shadow): red repro for local Nat shadowing missing_branch bug"
```

---

### Task 2: `Resolution.rekey_term/2` — Core-term atom substitution

**Files:**
- Create: `lib/cure/elab/resolution.ex`
- Create: `test/cure/elab/resolution_test.exs`

**Interfaces:**
- Consumes: `Cure.Core.Term` node shapes (read-only): `{:data, name, params, indices}`, `{:ctor, name, args}`, `{:case, scrut, motive, [{cname, arity, body}]}`, and all structural nodes (`:pi`, `:lam`, `:sigma`, `:app`, `:pair`, `:fst`, `:snd`, `:eq`, `:refl`, `:rewrite`, `:prim`), plus leaves (`:var`, `:type`, `:global`, `:int_type`, `:int_lit`, `:float_type`, `:float_lit`).
- Produces: `Cure.Elab.Resolution.rekey_term/2`.

- [ ] **Step 1: Write the failing unit tests**

`test/cure/elab/resolution_test.exs`:
```elixir
defmodule Cure.Elab.ResolutionTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Resolution

  describe "rekey_term/2" do
    setup do
      %{map: %{Nat: :"Std.Nat#Nat", Z: :"Std.Nat#Z", S: :"Std.Nat#S"}}
    end

    test "rewrites a :data head", %{map: m} do
      assert Resolution.rekey_term({:data, :Nat, [], []}, m) == {:data, :"Std.Nat#Nat", [], []}
    end

    test "rewrites a :ctor head and recurses into args", %{map: m} do
      assert Resolution.rekey_term({:ctor, :S, [{:ctor, :Z, []}]}, m) ==
               {:ctor, :"Std.Nat#S", [{:ctor, :"Std.Nat#Z", []}]}
    end

    test "rewrites a :case branch TAG (the position distinct from {:ctor,…})", %{map: m} do
      term = {:case, {:var, 0}, {:lam, {:data, :Nat, [], []}, {:type, 0}},
              [{:Z, 0, {:var, 0}}, {:S, 1, {:ctor, :Z, []}}]}
      assert Resolution.rekey_term(term, m) ==
               {:case, {:var, 0}, {:lam, {:data, :"Std.Nat#Nat", [], []}, {:type, 0}},
                [{:"Std.Nat#Z", 0, {:var, 0}}, {:"Std.Nat#S", 1, {:ctor, :"Std.Nat#Z", []}}]}
    end

    test "leaves a :global untouched (functions keep bare names)", %{map: m} do
      assert Resolution.rekey_term({:global, :Z}, m) == {:global, :Z}
    end

    test "recurses through structural nodes and leaves unmapped atoms alone", %{map: m} do
      term = {:pi, {:data, :Nat, [], []}, {:data, :Other, [], []}}
      assert Resolution.rekey_term(term, m) == {:pi, {:data, :"Std.Nat#Nat", [], []}, {:data, :Other, [], []}}
    end
  end
end
```

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/cure/elab/resolution_test.exs`
Expected: FAIL — `Cure.Elab.Resolution` is undefined.

- [ ] **Step 3: Create the module with `rekey_term/2`**

`lib/cure/elab/resolution.ex`:
```elixir
defmodule Cure.Elab.Resolution do
  @moduledoc """
  E-layer resolution over the bare-atom registry (Approach B). Detects
  family-name collisions between imported modules and the local module, re-keys
  the shadowed imports to qualified atoms (`:"Mod#Name"`), and resolves qualified
  surface references + shadow diagnostics from the re-keyed env. The kernel/TCB
  (`lib/cure/core/*`) is never modified; this module only reads Core term shapes.
  """

  alias Cure.Core.{Env, Inductive}

  @doc """
  Substitute constructor/family atoms in a Core term per `atom_map`
  (`%{bare => rekeyed}`). Rewrites the three bare-atom term positions —
  `:data` heads, `:ctor` heads, and `:case` branch tags — and recurses through
  every structural node. Leaves `:global` (function references keep bare names)
  and all literals untouched. An atom absent from `atom_map` is passed through.
  """
  @spec rekey_term(term, %{atom() => atom()}) :: term when term: tuple()
  def rekey_term(term, m)

  def rekey_term({:data, n, ps, is}, m),
    do: {:data, Map.get(m, n, n), Enum.map(ps, &rekey_term(&1, m)), Enum.map(is, &rekey_term(&1, m))}

  def rekey_term({:ctor, n, args}, m),
    do: {:ctor, Map.get(m, n, n), Enum.map(args, &rekey_term(&1, m))}

  def rekey_term({:case, s, mo, brs}, m),
    do:
      {:case, rekey_term(s, m), rekey_term(mo, m),
       Enum.map(brs, fn {cn, ar, b} -> {Map.get(m, cn, cn), ar, rekey_term(b, m)} end)}

  def rekey_term({:pi, dom, cod}, m), do: {:pi, rekey_term(dom, m), rekey_term(cod, m)}
  def rekey_term({:lam, dom, body}, m), do: {:lam, rekey_term(dom, m), rekey_term(body, m)}
  def rekey_term({:sigma, a, b}, m), do: {:sigma, rekey_term(a, m), rekey_term(b, m)}
  def rekey_term({:app, f, a}, m), do: {:app, rekey_term(f, m), rekey_term(a, m)}
  def rekey_term({:pair, a, b}, m), do: {:pair, rekey_term(a, m), rekey_term(b, m)}
  def rekey_term({:fst, p}, m), do: {:fst, rekey_term(p, m)}
  def rekey_term({:snd, p}, m), do: {:snd, rekey_term(p, m)}
  def rekey_term({:eq, ty, a, b}, m), do: {:eq, rekey_term(ty, m), rekey_term(a, m), rekey_term(b, m)}
  def rekey_term({:refl, a}, m), do: {:refl, rekey_term(a, m)}

  def rekey_term({:rewrite, proof, motive, body}, m),
    do: {:rewrite, rekey_term(proof, m), rekey_term(motive, m), rekey_term(body, m)}

  def rekey_term({:prim, op, args}, m), do: {:prim, op, Enum.map(args, &rekey_term(&1, m))}

  # Leaves: :var, :type, :global, :int_type, :int_lit, :float_type, :float_lit.
  def rekey_term(leaf, _m), do: leaf
end
```

- [ ] **Step 4: Run to verify pass**

Run: `mix test test/cure/elab/resolution_test.exs`
Expected: PASS (5 tests).

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/elab/resolution.ex test/cure/elab/resolution_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): Resolution.rekey_term Core-atom substitution (data/ctor/case-tag)"
```

---

### Task 3: `Resolution.rekey_module_env/3` — re-key one module's owned families

**Files:**
- Modify: `lib/cure/elab/resolution.ex`
- Modify: `test/cure/elab/resolution_test.exs`

**Interfaces:**
- Consumes: `rekey_term/2` (Task 2); `Cure.Core.Env` struct (`families`, `ctors`, `ctor_to_family`, `defs` maps); record shapes `family: %{name, params, indices, level}`, `ctor: %{name, args, result_indices, result_params, quantities}`, `def: %{name, type, body, quantities}`; telescope `[{atom, Term}]`.
- Produces: `Cure.Elab.Resolution.rekey_module_env/3`.

- [ ] **Step 1: Write the failing unit test**

Add to `test/cure/elab/resolution_test.exs`:
```elixir
  describe "rekey_module_env/3" do
    setup do
      # A tiny Std.Nat-shaped env: family Nat (nullary), ctors Z / S(Nat), and a
      # def `plus` that matches on Nat via a :case whose branch tags are Z / S.
      env =
        %Cure.Core.Env{}
        |> Cure.Core.Inductive.declare(
          Cure.Core.Inductive.family(:Nat, [], [], 0),
          [
            Cure.Core.Inductive.ctor(:Z, [], []),
            Cure.Core.Inductive.ctor(:S, [{:n, {:data, :Nat, [], []}}], [])
          ]
        )
        |> Cure.Core.Env.add_def(
          :plus,
          {:pi, {:data, :Nat, [], []}, {:data, :Nat, [], []}},
          {:case, {:var, 0}, {:lam, {:data, :Nat, [], []}, {:data, :Nat, [], []}},
           [{:Z, 0, {:ctor, :Z, []}}, {:S, 1, {:ctor, :S, [{:var, 0}]}}]}
        )

      %{env: env}
    end

    test "moves family + ctor keys to :\"Mod#Name\" and repoints ctor_to_family", %{env: env} do
      out = Cure.Elab.Resolution.rekey_module_env(env, "Std.Nat", MapSet.new([:Nat]))

      assert Map.has_key?(out.families, :"Std.Nat#Nat")
      refute Map.has_key?(out.families, :Nat)
      assert out.families[:"Std.Nat#Nat"].name == :"Std.Nat#Nat"

      assert Map.has_key?(out.ctors, :"Std.Nat#Z")
      assert Map.has_key?(out.ctors, :"Std.Nat#S")
      refute Map.has_key?(out.ctors, :Z)
      assert out.ctor_to_family[:"Std.Nat#Z"] == :"Std.Nat#Nat"
      assert out.ctor_to_family[:"Std.Nat#S"] == :"Std.Nat#Nat"
    end

    test "rewrites embedded terms in ctor arg types", %{env: env} do
      out = Cure.Elab.Resolution.rekey_module_env(env, "Std.Nat", MapSet.new([:Nat]))
      assert [{:n, {:data, :"Std.Nat#Nat", [], []}}] = out.ctors[:"Std.Nat#S"].args
    end

    test "rewrites embedded terms in def bodies including :case branch tags", %{env: env} do
      out = Cure.Elab.Resolution.rekey_module_env(env, "Std.Nat", MapSet.new([:Nat]))
      body = out.defs[:plus].body
      assert {:case, _, _, [{:"Std.Nat#Z", 0, _}, {:"Std.Nat#S", 1, _}]} = body
      assert out.defs[:plus].type == {:pi, {:data, :"Std.Nat#Nat", [], []}, {:data, :"Std.Nat#Nat", [], []}}
    end

    test "leaves a non-owned family in the same env untouched", %{env: env} do
      env2 =
        Cure.Core.Inductive.declare(env, Cure.Core.Inductive.family(:Bool, [], [], 0),
          [Cure.Core.Inductive.ctor(:True, [], []), Cure.Core.Inductive.ctor(:False, [], [])])

      out = Cure.Elab.Resolution.rekey_module_env(env2, "Std.Nat", MapSet.new([:Nat]))
      assert Map.has_key?(out.families, :Bool)
      assert Map.has_key?(out.ctors, :True)
    end
  end
```

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/cure/elab/resolution_test.exs`
Expected: FAIL — `rekey_module_env/3` undefined.

- [ ] **Step 3: Implement `rekey_module_env/3`**

Add to `lib/cure/elab/resolution.ex` (inside the module):
```elixir
  @doc """
  Re-key every family named in `owned_family_names` (and each of its
  constructors) within `env`'s slice to `:"<module_id>#<name>"`. Renames the
  `families`/`ctors`/`ctor_to_family` map keys, updates each record's `:name`
  field, and rewrites every embedded Core term (family/ctor telescopes,
  ctor result indices/params, and ALL def bodies+types in the slice) via
  `rekey_term/2`. Families/ctors NOT owned are left untouched. Functions keep
  their bare `defs` keys (only embedded family/ctor references are rewritten).
  """
  @spec rekey_module_env(Env.t(), String.t(), MapSet.t(atom())) :: Env.t()
  def rekey_module_env(%Env{} = env, module_id, owned_family_names) do
    # Owned ctor names: ctors whose family is an owned family name.
    owned_ctor_names =
      for {cname, fname} <- env.ctor_to_family, MapSet.member?(owned_family_names, fname), into: MapSet.new(), do: cname

    # bare -> rekeyed atom map covering both owned families and their ctors.
    amap =
      Enum.reduce(owned_family_names, %{}, fn f, acc -> Map.put(acc, f, rekey_atom(module_id, f)) end)

    amap =
      Enum.reduce(owned_ctor_names, amap, fn c, acc -> Map.put(acc, c, rekey_atom(module_id, c)) end)

    %Env{
      env
      | families: rekey_families(env.families, owned_family_names, amap),
        ctors: rekey_ctors(env.ctors, owned_ctor_names, amap),
        ctor_to_family: rekey_c2f(env.ctor_to_family, amap),
        defs: rekey_defs(env.defs, amap)
    }
  end

  defp rekey_atom(module_id, bare), do: String.to_atom(module_id <> "#" <> Atom.to_string(bare))

  defp rekey_families(families, owned, amap) do
    Map.new(families, fn {k, fam} ->
      if MapSet.member?(owned, k) do
        {Map.fetch!(amap, k),
         %{fam | name: Map.fetch!(amap, k),
                 params: rekey_tele(fam.params, amap), indices: rekey_tele(fam.indices, amap)}}
      else
        {k, %{fam | params: rekey_tele(fam.params, amap), indices: rekey_tele(fam.indices, amap)}}
      end
    end)
  end

  defp rekey_ctors(ctors, owned_ctor_names, amap) do
    Map.new(ctors, fn {k, c} ->
      c2 = %{c |
        name: Map.get(amap, c.name, c.name),
        args: rekey_tele(c.args, amap),
        result_indices: Enum.map(c.result_indices, &rekey_term(&1, amap)),
        result_params: Enum.map(c.result_params, &rekey_term(&1, amap))
      }

      if MapSet.member?(owned_ctor_names, k), do: {Map.fetch!(amap, k), c2}, else: {k, c2}
    end)
  end

  defp rekey_c2f(c2f, amap) do
    Map.new(c2f, fn {c, f} -> {Map.get(amap, c, c), Map.get(amap, f, f)} end)
  end

  defp rekey_defs(defs, amap) do
    Map.new(defs, fn {k, d} ->
      {k, %{d | type: rekey_term(d.type, amap), body: rekey_term(d.body, amap)}}
    end)
  end

  defp rekey_tele(tele, amap), do: Enum.map(tele, fn {n, t} -> {n, rekey_term(t, amap)} end)
```

- [ ] **Step 4: Run to verify pass**

Run: `mix test test/cure/elab/resolution_test.exs`
Expected: PASS (all rekey tests).

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/elab/resolution.ex test/cure/elab/resolution_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): Resolution.rekey_module_env — re-key one module's owned families"
```

---

### Task 4: `Resolution.classify/2` — collision detection with module-identity provenance

**Files:**
- Modify: `lib/cure/elab/resolution.ex`
- Modify: `test/cure/elab/resolution_test.exs`

**Interfaces:**
- Consumes: `family_owners :: %{atom() => MapSet(module_id)}` and `local_families :: MapSet(atom())` (both built by Task 5 from AST scans).
- Produces: `Cure.Elab.Resolution.classify/2` → `%{losers: %{module_id => MapSet(family_name)}, ambiguous: MapSet(family_name)}`.

- [ ] **Step 1: Write the failing unit tests**

Add to `test/cure/elab/resolution_test.exs`:
```elixir
  describe "classify/2" do
    test "local declaration shadows a single imported owner: that import is a loser" do
      owners = %{Nat: MapSet.new(["Std.Nat"])}
      out = Cure.Elab.Resolution.classify(owners, MapSet.new([:Nat]))
      assert out.losers == %{"Std.Nat" => MapSet.new([:Nat])}
      assert out.ambiguous == MapSet.new()
    end

    test "one import owner, no local: NOT a collision (no re-key)" do
      owners = %{Nat: MapSet.new(["Std.Nat"])}
      out = Cure.Elab.Resolution.classify(owners, MapSet.new())
      assert out.losers == %{}
      assert out.ambiguous == MapSet.new()
    end

    test "same module owning a name (diamond dedup already applied): still ONE owner, no collision" do
      # Std.Vector's transitive Nat is attributed to Std.Nat by the AST scan, so
      # owners(Nat) = {Std.Nat} — a single owner even though reached two ways.
      owners = %{Nat: MapSet.new(["Std.Nat"]), Vector: MapSet.new(["Std.Vector"])}
      out = Cure.Elab.Resolution.classify(owners, MapSet.new())
      assert out.losers == %{}
      assert out.ambiguous == MapSet.new()
    end

    test "two distinct import owners, no local: ambiguous, both losers" do
      owners = %{Nat: MapSet.new(["Std.Foo", "Std.Bar"])}
      out = Cure.Elab.Resolution.classify(owners, MapSet.new())
      assert out.ambiguous == MapSet.new([:Nat])
      assert out.losers == %{"Std.Foo" => MapSet.new([:Nat]), "Std.Bar" => MapSet.new([:Nat])}
    end

    test "two distinct import owners WITH a local: local wins, both imports lose, not ambiguous" do
      owners = %{Nat: MapSet.new(["Std.Foo", "Std.Bar"])}
      out = Cure.Elab.Resolution.classify(owners, MapSet.new([:Nat]))
      assert out.ambiguous == MapSet.new()
      assert out.losers == %{"Std.Foo" => MapSet.new([:Nat]), "Std.Bar" => MapSet.new([:Nat])}
    end
  end
```

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/cure/elab/resolution_test.exs`
Expected: FAIL — `classify/2` undefined.

- [ ] **Step 3: Implement `classify/2`**

Add to `lib/cure/elab/resolution.ex`:
```elixir
  @doc """
  Classify family-name collisions. A family name `N` collides when its set of
  sources — the distinct import modules that OWN it (declare it in their own
  AST) plus the local module if it declares `N` — has size ≥ 2. In every
  collision the winner of the unqualified name is the LOCAL module if present
  (only the local module can win); therefore every import owner of a colliding
  name is a loser. When no local declares a colliding name, the name is
  additionally `ambiguous` (unqualified use is an error, §3.4) — but its
  owners are still re-keyed so both stay reachable qualified.
  """
  @spec classify(%{atom() => MapSet.t(String.t())}, MapSet.t(atom())) :: %{
          losers: %{String.t() => MapSet.t(atom())},
          ambiguous: MapSet.t(atom())
        }
  def classify(family_owners, local_families) do
    Enum.reduce(family_owners, %{losers: %{}, ambiguous: MapSet.new()}, fn {name, owners}, acc ->
      local? = MapSet.member?(local_families, name)
      n_sources = MapSet.size(owners) + if local?, do: 1, else: 0

      cond do
        n_sources < 2 ->
          acc

        true ->
          losers =
            Enum.reduce(owners, acc.losers, fn mod, ls ->
              Map.update(ls, mod, MapSet.new([name]), &MapSet.put(&1, name))
            end)

          ambiguous = if local?, do: acc.ambiguous, else: MapSet.put(acc.ambiguous, name)
          %{losers: losers, ambiguous: ambiguous}
      end
    end)
  end
```

- [ ] **Step 4: Run to verify pass**

Run: `mix test test/cure/elab/resolution_test.exs`
Expected: PASS (all classify tests).

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/elab/resolution.ex test/cure/elab/resolution_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): Resolution.classify — module-identity collision detection"
```

---

### Task 5: Wire collision detection + re-key into `program.ex` (the core bug fix)

**Files:**
- Modify: `lib/cure/elab/program.ex:29-36` (`check_ast/1`), and the import pipeline `import_env/2`/`import_source_env/2`/`merge_env/2`.
- Modify: `test/cure/elab/type_shadowing_test.exs`
- Test: `test/cure/elab/auto_prelude_test.exs` (must stay green — R6)

**Interfaces:**
- Consumes: `Resolution.classify/2`, `Resolution.rekey_module_env/3`; existing `declared_type_names/1`, `imports/1`, `declarations/1`, `merge_env/2`.
- Produces: a re-keyed merged env from `check_ast/1`. After this task, `Inductive.ctors_of(sig, :Nat)` on a shadowing module returns only the local ctors.

**Design (per spec §3.1/§3.2, robust to transitive imports):**
1. Resolve `auto_prelude_imports(ast) ++ imports(ast)` to distinct `{module_id, path}` (dedup by `module_id`) — this is `distinct_import_modules/1`, used for the SLICE list (step 4 below).
2. **Ownership must be computed over the full transitive import closure, not just the direct list.** A module reached only *transitively* — e.g. `Std.Nat`, never `use`d directly but pulled in because `priv/std/vector.cure` itself does `use Std.Nat` — still OWNS the family it declares (`Nat`), and a local `type Nat` must collide with it exactly as if the program had written `use Std.Nat` itself. If ownership were scanned only over `distinct_import_modules/1`'s direct list, a program with `use Std.Vector` (no explicit `use Std.Nat`) plus a local `type Nat` would never see `Nat` as a key of `family_owners` at all (Vector's own AST doesn't declare `Nat`) — no collision, no re-key, and `Inductive.ctors_of(:Nat)` would still return the imported `Z`/`S` alongside the local ctors, reproducing the exact `{:missing_branch,_}` bug this task exists to fix. So: walk the **full transitive module closure** (`transitive_import_modules/1`, a BFS over each visited module's own `imports/1`, deduped by `module_id`, cycle-safe) and scan `owned_family_names(path)` (family names declared in *that module's own AST*) for every module in the closure — not just the direct ones. Build `family_owners` from that.
3. `classify(family_owners, declared_type_names(ast))`.
4. Build each **directly-imported** module's per-module env slice (`distinct_import_modules/1` — nested/transitive modules are pulled in automatically as part of their parent's own recursive `module_slice_env`, exactly as today); re-key that slice's owned loser families via `rekey_module_env/3`; merge all slices.
5. **Drop residual bare collision keys** from the merged-imports env (transitive copies that survived re-keying): for every colliding family name, delete any leftover bare family key + bare ctors pointing to it. This guarantees the local module merges clean. Because this step operates on the *merged* env by family **name**, not by which slice contributed the bare copy, it correctly cleans up a transitively-carried bare `Nat`/`Z`/`S` that arrived via `Std.Vector`'s own slice even though `Std.Vector` itself was never re-keyed — as long as step 2 correctly put `Nat` in `family_owners` (which is exactly what the transitive-closure scan buys).
6. Merge `seeded` (builtins) + local declarations on top, exactly as today.

- [ ] **Step 1: Add the shadow02 + shadow03 behavioral tests (red)**

Add to `test/cure/elab/type_shadowing_test.exs`:
```elixir
  test "R1 full: local `Nat = Z|S` fully shadows same-named imported ctors" do
    src = """
    mod FullShadow
      use Std.Nat
      type Nat = Z | S(Nat)
      fn two() -> Nat = S(S(Z()))
      fn pred(n: Nat) -> Nat = match n
        Z() -> Z()
        S(m) -> m
    end
    """

    assert {:ok, _env} = elaborate(src)
  end

  test "R2: unshadowed imported ctors Z/S stay visible when local uses Zero/Suc" do
    src = """
    mod PartialShadow
      use Std.Nat
      type Nat = Zero | Suc(Nat)
      fn imported_one() -> Std.Nat = S(Z())
      fn local_one() -> Nat = Suc(Zero())
    end
    """

    assert {:ok, _env} = elaborate(src)
  end

  test "R1 via transitive import: local `Nat` collides with a family reached only through `use Std.Vector` (no explicit `use Std.Nat`)" do
    # priv/std/vector.cure itself does `use Std.Nat` (confirmed by reading the
    # source) — Nat is reached here purely transitively. Collision detection
    # must attribute `Nat` to its OWNING module (Std.Nat) even though Std.Nat
    # is never a direct import of this program, or this local shadow silently
    # fails to disown the imported Z/S (the exact bug this plan fixes, one
    # import-hop removed).
    src = """
    mod TransitiveShadow
      use Std.Vector
      type Nat = Zero | Suc(Nat)
      fn two() -> Nat = Suc(Suc(Zero()))
      fn pred(n: Nat) -> Nat = match n
        Zero() -> Zero()
        Suc(m) -> m
    end
    """

    assert {:ok, _env} = elaborate(src)
  end
```
(The `R2` test's `Std.Nat` return type + unqualified `S`/`Z` referring to the imported family will fully pass only after Tasks 7–8; here it asserts the *coverage*/registry side is unblocked. If it still errors on the qualified `Std.Nat` return type at this task, split it: keep only the `local_one` half green now and move the `imported_one` half to Task 8. Run first and see which applies before committing.)

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/cure/elab/type_shadowing_test.exs`
Expected: FAIL — R1a/R1-full/the transitive-import case still `{:missing_branch, _}` (the transitive case fails even after a naive direct-only `family_owners` scan — that is precisely the gap step 3 below must close).

- [ ] **Step 3: Add helpers + rewrite the import pipeline in `program.ex`**

Add these private helpers to `lib/cure/elab/program.ex` (near `import_env/2`). Both `distinct_import_modules/1` and `transitive_import_modules/1` reuse the existing `import_source_path/1` for canonical-id + path resolution.
```elixir
  # Distinct {module_id, path} for every DIRECT import source, deduped by
  # module_id. Used for the merged-slice list (§3.2 re-keying/merging operates
  # only at this granularity — nested imports are pulled in automatically by
  # each direct module's own recursive `module_slice_env`).
  defp distinct_import_modules(sources) do
    sources
    |> Enum.map(&import_source_path/1)
    |> Enum.flat_map(fn
      {:ok, module_name, path} -> [{to_string(module_name), path}]
      :not_stdlib -> []
    end)
    |> Enum.uniq_by(fn {mod_id, _path} -> mod_id end)
  end

  # Every module reachable via the import graph (direct AND transitive),
  # deduped by module_id, cycle-safe (BFS with a `seen` set). Collision
  # DETECTION (family_owners, below) must scan this closure, not just the
  # direct list: a family declared in a module reached only transitively
  # (e.g. Std.Nat, pulled in solely because `priv/std/vector.cure` itself
  # does `use Std.Nat`) still needs to be attributed to its owning module, or
  # a local declaration of the same name is never classified as a collision
  # and the disowning never happens for that family — see the Design note
  # above. `distinct_import_modules/1` remains the right list for slice-
  # building/re-keying/merging; only ownership-scanning needs the closure.
  defp transitive_import_modules(sources), do: bfs_import_modules(sources, MapSet.new(), [])

  defp bfs_import_modules([], _seen, acc), do: Enum.reverse(acc)

  defp bfs_import_modules([source | rest], seen, acc) do
    case import_source_path(source) do
      {:ok, module_name, path} ->
        mod_id = to_string(module_name)

        if MapSet.member?(seen, mod_id) do
          bfs_import_modules(rest, seen, acc)
        else
          nested =
            with {:ok, src} <- File.read(path),
                 {:ok, tokens} <- Lexer.tokenize(src, emit_events: false),
                 {:ok, nested_ast} <- Parser.parse(tokens, emit_events: false) do
              imports(nested_ast)
            else
              _ -> []
            end

          bfs_import_modules(nested ++ rest, MapSet.put(seen, mod_id), [{mod_id, path} | acc])
        end

      :not_stdlib ->
        bfs_import_modules(rest, seen, acc)
    end
  end

  # Family names DECLARED in a module's own source (transitive imports excluded).
  defp owned_family_names(path) do
    with {:ok, source} <- File.read(path),
         {:ok, tokens} <- Lexer.tokenize(source, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, emit_events: false) do
      declared_type_names(ast)
    else
      _ -> MapSet.new()
    end
  end

  # Build ONE module's flat env slice (own decls + its own imports), as today.
  defp module_slice_env(path) do
    with {:ok, source} <- File.read(path),
         {:ok, tokens} <- Lexer.tokenize(source, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, emit_events: false),
         {:ok, env0} <- import_env(imports(ast), MapSet.new()),
         {:ok, env} <- elaborate_declarations(declarations(ast), env0) do
      TotalityClosure.certify_type_level(env)
    end
  end

  # Delete residual bare keys for a colliding family name left by transitive copies.
  defp drop_bare_family(%Env{} = env, name) do
    ctors = for {c, f} <- env.ctor_to_family, f == name, into: [], do: c

    %Env{
      env
      | families: Map.delete(env.families, name),
        ctors: Map.drop(env.ctors, ctors),
        ctor_to_family: Map.drop(env.ctor_to_family, [name | ctors])
    }
  end

  # The full shadow-aware imported-env builder.
  defp shadow_resolved_imports(ast) do
    sources = auto_prelude_imports(ast) ++ imports(ast)
    modules = distinct_import_modules(sources)

    # Ownership scans the FULL transitive closure (not `modules`, which is
    # direct-only) — see the Design note + `transitive_import_modules/1` doc.
    family_owners =
      sources
      |> transitive_import_modules()
      |> Enum.reduce(%{}, fn {mod_id, path}, acc ->
        Enum.reduce(owned_family_names(path), acc, fn name, a ->
          Map.update(a, name, MapSet.new([mod_id]), &MapSet.put(&1, mod_id))
        end)
      end)

    local = declared_type_names(ast)
    %{losers: losers, ambiguous: ambiguous} = Resolution.classify(family_owners, local)

    collisions =
      losers |> Map.values() |> Enum.reduce(MapSet.new(), &MapSet.union/2)

    with {:ok, merged} <-
           Enum.reduce_while(modules, {:ok, Env.empty()}, fn {mod_id, path}, {:ok, acc} ->
             case module_slice_env(path) do
               {:ok, slice} ->
                 slice =
                   case Map.get(losers, mod_id) do
                     nil -> slice
                     owned_losers -> Resolution.rekey_module_env(slice, mod_id, owned_losers)
                   end

                 {:cont, {:ok, merge_env(acc, slice)}}

               {:error, _} = err ->
                 {:halt, err}
             end
           end) do
      # Drop residual bare copies of every collision name (transitive leftovers).
      cleaned = Enum.reduce(collisions, merged, fn name, e -> drop_bare_family(e, name) end)
      {:ok, cleaned, ambiguous}
    end
  end
```

- [ ] **Step 4: Rewrite `check_ast/1` to use the shadow-resolved imports**

Replace `check_ast/1` (`lib/cure/elab/program.ex:29-36`):
```elixir
  def check_ast(ast) do
    with {:ok, imported, _ambiguous} <- shadow_resolved_imports(ast),
         seeded = Cure.Core.Builtins.seed(Env.empty(), declared_type_names(ast)),
         env0 = merge_env(seeded, imported),
         {:ok, env} <- elaborate_declarations(declarations(ast), env0, prelude_source?(ast)) do
      TotalityClosure.certify_type_level(env)
    end
  end
```
(The `_ambiguous` set is consumed in Task 10 for R7. `merge_env(seeded, imported)` then `elaborate_declarations` of the local decls layers local families on top of the cleaned imports, exactly as before — but now the imports carry no bare `:Nat` when the local module shadows it. Add `alias Cure.Elab.Resolution` to the module's alias list if not already present.)

- [ ] **Step 5: Run the shadow tests**

Run: `mix test test/cure/elab/type_shadowing_test.exs`
Expected: PASS for R1a, R1-full (shadow01/shadow02), and the transitive-import case. R2 per the Step-1 note (fully green after Task 8; keep the `local_one` half green now).

- [ ] **Step 6: Run the auto-prelude + oracle-replay regression guard (R6)**

Run: `mix test test/cure/elab/auto_prelude_test.exs test/oracle_replay_test.exs`
Expected: PASS (auto-prelude skip retained; no probe regressed). If any diamond/auto+explicit case regresses, the dedup or residual-drop is wrong — fix before committing.

- [ ] **Step 7: Add the shadow02 + shadow03 + shadow08 oracle probes**

`test/oracle/shadow/shadow02_full_shadow.cure`:
```
mod FullShadow
  use Std.Nat
  type Nat = Z | S(Nat)
  fn two() -> Nat = S(S(Z()))
  fn pred(n: Nat) -> Nat = match n
    Z() -> Z()
    S(m) -> m
end
```
`test/oracle/shadow/shadow02_full_shadow.idr`:
```idris
%default total

data Nat' = Z | S Nat'

two : Nat'
two = S (S Z)

pred' : Nat' -> Nat'
pred' Z = Z
pred' (S m) = m
```

`test/oracle/shadow/shadow03_unshadowed_visible.cure`:
```
mod PartialShadow
  use Std.Nat
  type Nat = Zero | Suc(Nat)
  fn local_one() -> Nat = Suc(Zero())
end
```
`test/oracle/shadow/shadow03_unshadowed_visible.idr`:
```idris
%default total

data Nat' = Zero | Suc Nat'

localOne : Nat'
localOne = Suc Zero
```

`test/oracle/shadow/shadow08_transitive_shadow.cure` (the transitive-import case — the real `Std.Vector`/`Std.Nat` stdlib, no scratch modules needed):
```
mod TransitiveShadow
  use Std.Vector
  type Nat = Zero | Suc(Nat)
  fn two() -> Nat = Suc(Suc(Zero()))
  fn pred(n: Nat) -> Nat = match n
    Zero() -> Zero()
    Suc(m) -> m
end
```
`test/oracle/shadow/shadow08_transitive_shadow.idr`:
```idris
%default total

data Nat' = Zero | Suc Nat'

two : Nat'
two = Suc (Suc Zero)

pred' : Nat' -> Nat'
pred' Zero = Zero
pred' (Suc m) = m
```
(Idris has no notion of "transitively imported" here — its own prelude `Nat` is simply always in scope, same as shadow01/02's modeling; the point under test is Cure-side only: the local shadow must disown the imported family even though it is reached solely via `Std.Vector`'s own `use Std.Nat`, not a direct `use Std.Nat` of this module.)

- [ ] **Step 8: Regenerate verdicts and confirm `same`**

Run: `mix cure.oracle shadow`
Expected: `verdicts.json` written with `shadow01`/`shadow02`/`shadow03`/`shadow08` = `{"cure":"accept","idris":"accept","relation":"same"}`.

- [ ] **Step 9: Commit**

```bash
git add -- lib/cure/elab/program.ex test/cure/elab/type_shadowing_test.exs test/oracle/shadow/shadow02_full_shadow.cure test/oracle/shadow/shadow02_full_shadow.idr test/oracle/shadow/shadow03_unshadowed_visible.cure test/oracle/shadow/shadow03_unshadowed_visible.idr test/oracle/shadow/shadow08_transitive_shadow.cure test/oracle/shadow/shadow08_transitive_shadow.idr test/oracle/shadow/verdicts.json
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): re-key shadowed imports on collision — fixes missing_branch (R1/R2)"
```

---

### Task 6: `Resolution.resolve_qualified/3` — dotted path → registry key

**Files:**
- Modify: `lib/cure/elab/resolution.ex`
- Modify: `test/cure/elab/resolution_test.exs`

**Interfaces:**
- Consumes: the re-keyed `Env` (`families`, `ctors` maps); `Inductive.family?/2`, `Inductive.get_ctor/2`.
- Produces: `Cure.Elab.Resolution.resolve_qualified/3`.

**Resolution rule (§3.6, soundness-load-bearing ordering — qualified key FIRST, bare fallback SECOND):**
- `slot == :value` (a ctor path `Std.Nat.Z`): module = all-but-last segment (`"Std.Nat"`), name = last (`Z`). Try `:"Std.Nat#Z"` in ctors; else bare `:Z` in ctors.
- `slot == :type` (a type path `Std.Nat` or `Std.Nat.Nat`): try the **module==typename collapse** first — module = whole path (`"Std.Nat"`), name = last segment (`Nat`) → `:"Std.Nat#Nat"` in families; else the explicit form module = all-but-last, name = last → `:"Std.Nat#Nat"`; else bare last-segment `:Nat` in families.

- [ ] **Step 1: Write the failing unit tests**

Add to `test/cure/elab/resolution_test.exs`:
```elixir
  describe "resolve_qualified/3" do
    setup do
      # env where Std.Nat has been re-keyed (loser), and an unshadowed Std.Bool.
      env =
        %Cure.Core.Env{}
        |> Cure.Core.Inductive.declare(Cure.Core.Inductive.family(:"Std.Nat#Nat", [], [], 0),
             [Cure.Core.Inductive.ctor(:"Std.Nat#Z", [], []),
              Cure.Core.Inductive.ctor(:"Std.Nat#S", [{:n, {:data, :"Std.Nat#Nat", [], []}}], [])])
        |> Cure.Core.Inductive.declare(Cure.Core.Inductive.family(:Bool, [], [], 0),
             [Cure.Core.Inductive.ctor(:True, [], []), Cure.Core.Inductive.ctor(:False, [], [])])

      %{env: env}
    end

    test "value path resolves a re-keyed ctor", %{env: env} do
      assert Cure.Elab.Resolution.resolve_qualified(env, "Std.Nat.Z", :value) == {:ok, :"Std.Nat#Z"}
    end

    test "type path resolves via module==typename collapse", %{env: env} do
      assert Cure.Elab.Resolution.resolve_qualified(env, "Std.Nat", :type) == {:ok, :"Std.Nat#Nat"}
    end

    test "type path resolves the explicit .Nat spelling identically", %{env: env} do
      assert Cure.Elab.Resolution.resolve_qualified(env, "Std.Nat.Nat", :type) == {:ok, :"Std.Nat#Nat"}
    end

    test "falls back to a bare key for an unshadowed module", %{env: env} do
      assert Cure.Elab.Resolution.resolve_qualified(env, "Std.Bool.True", :value) == {:ok, :True}
      assert Cure.Elab.Resolution.resolve_qualified(env, "Std.Bool", :type) == {:ok, :Bool}
    end

    test "returns :error for an unresolvable path", %{env: env} do
      assert Cure.Elab.Resolution.resolve_qualified(env, "Std.Nope.Gone", :value) == :error
    end
  end
```

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/cure/elab/resolution_test.exs`
Expected: FAIL — `resolve_qualified/3` undefined.

- [ ] **Step 3: Implement `resolve_qualified/3`**

Add to `lib/cure/elab/resolution.ex`:
```elixir
  @doc """
  Resolve a flattened dotted surface path (`"Std.Nat.Z"`) to a registry key,
  trying the qualified `:"Mod#Name"` key FIRST and a bare-atom key second (the
  ordering is load-bearing: under a local shadow the loser is only reachable at
  its qualified key, and a bare fallback must never grab the local winner —
  which is safe precisely because a shadowed import is always re-keyed, so its
  bare key is absent). `slot` selects type vs value candidate shapes.
  """
  @spec resolve_qualified(Env.t(), String.t(), :type | :value) :: {:ok, atom()} | :error
  def resolve_qualified(%Env{} = env, dotted, :value) do
    segs = String.split(dotted, ".")
    {mod_segs, [last]} = Enum.split(segs, length(segs) - 1)
    mod = Enum.join(mod_segs, ".")
    try_keys(env, [rekey_atom(mod, String.to_atom(last)), String.to_atom(last)], :value)
  end

  def resolve_qualified(%Env{} = env, dotted, :type) do
    segs = String.split(dotted, ".")
    last = List.last(segs)
    {mod_segs, [explicit_last]} = Enum.split(segs, length(segs) - 1)

    candidates = [
      # module==typename collapse: whole path is the module, name repeats the tail.
      rekey_atom(dotted, String.to_atom(last)),
      # explicit Mod.Type spelling.
      rekey_atom(Enum.join(mod_segs, "."), String.to_atom(explicit_last)),
      # unshadowed bare fallback.
      String.to_atom(last)
    ]

    try_keys(env, candidates, :type)
  end

  defp try_keys(env, keys, slot) do
    present? =
      case slot do
        :type -> fn k -> Inductive.family?(env, k) end
        :value -> fn k -> not is_nil(Inductive.get_ctor(env, k)) end
      end

    case Enum.find(keys, present?) do
      nil -> :error
      key -> {:ok, key}
    end
  end
```
(Confirm `Inductive.family?/2` exists — it is used in `declarations.ex` `resolve_index_name`; if the arity differs, use `Map.has_key?(env.families, k)` directly.)

- [ ] **Step 4: Run to verify pass**

Run: `mix test test/cure/elab/resolution_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/elab/resolution.ex test/cure/elab/resolution_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): Resolution.resolve_qualified — dotted path to registry key"
```

---

### Task 7: Wire qualified resolution into the value + pattern call sites (R3, escape hatch)

**Files:**
- Modify: `lib/cure/elab/elaborator.ex` — `partition_arms` (~2752-2796) and `partition_rematch_arms` (~1257-1283) constructor-key normalization; `elaborate_named_call/5` (~171).
- Modify: `test/cure/elab/type_shadowing_test.exs`
- Create: `test/oracle/shadow/shadow04_escape_hatch.cure` / `.idr`

**Interfaces:**
- Consumes: `Resolution.resolve_qualified/3`.
- Produces: a `resolve_ctor_key/2` helper in `elaborator.ex` that normalizes a possibly-dotted ctor atom to a registry key.

- [ ] **Step 1: Write the failing test (expression + pattern positions)**

Add to `test/cure/elab/type_shadowing_test.exs`:
```elixir
  test "R3: shadowed ctor reachable qualified in expression and pattern position" do
    src = """
    mod EscapeHatch
      use Std.Nat
      type Nat = Zero | Suc(Nat)
      fn imported_two() -> Std.Nat = Std.Nat.S(Std.Nat.Z())
      fn is_zero(n: Std.Nat) -> Nat = match n
        Std.Nat.Z() -> Zero()
        Std.Nat.S(k) -> Suc(Zero())
    end
    """

    assert {:ok, _env} = elaborate(src)
  end
```

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/cure/elab/type_shadowing_test.exs`
Expected: FAIL — the qualified `Std.Nat.Z` flattens to atom `:"Std.Nat.Z"`, unknown to `get_ctor` → `{:unknown_pattern_constructor, :"Std.Nat.Z"}` (or an `elaborate_named_call` global miss). (The `Std.Nat` *type-slot* on the params is completed in Task 8; if this test blocks on the type slot before reaching the ctor logic, temporarily annotate the params with a local type to isolate the ctor paths, then restore in Task 8. Verify which by reading the actual error.)

- [ ] **Step 3: Add `resolve_ctor_key/2` and apply it at the two `partition_*` gates**

Add near the top of the private helpers in `lib/cure/elab/elaborator.ex`:
```elixir
  # Normalize a constructor atom that may be a flattened dotted path
  # (`:"Std.Nat.Z"`) to a registry key via the resolution layer; a bare atom
  # with no "." is returned unchanged.
  defp resolve_ctor_key(env, cname) do
    s = Atom.to_string(cname)

    if String.contains?(s, ".") do
      case Cure.Elab.Resolution.resolve_qualified(env, s, :value) do
        {:ok, key} -> key
        :error -> cname
      end
    else
      cname
    end
  end
```

In `partition_arms`, immediately after `{:ok, {cname, _vars}} ->` (the successful `constructor_pattern` clause), rebind `cname`:
```elixir
          {:ok, {cname0, _vars}} ->
            cname = resolve_ctor_key(env, cname0)

            cond do
              Inductive.get_ctor(env, cname) == nil ->
```
(The rest of the `cond` is unchanged — it now sees the resolved key. Note `Map.put(acc, cname, …)` and the `pattern` value stay as they are; only the key used for lookup/coverage is the resolved one.)

Apply the identical rebind in `partition_rematch_arms` after `with {:ok, {cname, _vars}} <- constructor_pattern(with_pattern),` — capture as `cname0` and add `cname = resolve_ctor_key(env, cname0)` before the `cond`.

- [ ] **Step 4: Apply qualified resolution in `elaborate_named_call/5`**

In `lib/cure/elab/elaborator.ex:171`, after `atom = String.to_atom(name)`, add a resolved-atom binding and use it for the ctor branch:
```elixir
  defp elaborate_named_call(meta, args, names, ctx, env) do
    name = Keyword.fetch!(meta, :name)
    atom = String.to_atom(name)

    resolved =
      if String.contains?(name, ".") do
        case Cure.Elab.Resolution.resolve_qualified(env, name, :value) do
          {:ok, key} -> key
          :error -> atom
        end
      else
        atom
      end

    cond do
      name == "refl" and length(args) == 1 ->
        ...

      Inductive.get_ctor(env, resolved) ->
        result =
          with {:ok, present} <- map_present_args(args, names, ctx, env) do
            elaborate_ctor_app(env, resolved, present, ctx)
          end

        case result do
          {:ok, _, _} = ok ->
            ok

          {:error, _} = orig ->
            case elaborate_ctor_app_infer_bidirectional(env, resolved, args, names, ctx) do
              {:ok, _, _} = ok -> ok
              {:error, _} -> orig
            end
        end
        ...
```
(Change the `Inductive.get_ctor(env, atom)` guard, the `elaborate_ctor_app(env, atom, …)` call, **and** the `elaborate_ctor_app_infer_bidirectional(env, atom, args, names, ctx)` retry call in that ctor branch to use `resolved` — all three, not just the first two. The retry is reached whenever the primary `elaborate_ctor_app` fails because a nested argument is underdetermined until an implicit parameter is solved (the existing `Cons(Z(), Nil())`-style case, e.g. a qualified `Std.Vector.prepend(x, Std.Vector.prepend(y, Std.Vector.empty()))` where the length index is erased/inferred); passing the stale, still-dotted `atom` there would silently break qualified resolution for exactly this shape. Every other use of `atom` — the global-def path, error messages — stays `atom` so a non-dotted name is byte-for-byte unchanged: `resolved == atom` when `name` has no dot.)

- [ ] **Step 4b: Add a targeted test for the bidirectional-retry path**

`elaborate_ctor_app_infer_bidirectional/5` (`elaborator.ex:3821`) is reached only
when a constructor call's own `map_present_args`/`elaborate_ctor_app` fails on
up-front inference — its own doc comment names the trigger precisely: "a nested
underdetermined constructor as a bare argument, `Cons(Z(), Nil())`, whose inner
`Nil()` no expected type reaches," and it applies **only to a parametric
family** (a non-parametric family like `Std.Nat`'s `Zero|Suc` never needs it —
there is no family parameter to solve, so its constructors never take this
path). `Std.Vector(a, n)` is the only parametric family in the stdlib, so this
scenario can only be exercised through it. Do not hand-copy an unverified
`.cure` program here — construct it empirically:
1. Start from the exact known-working nested-constructor shape already proven
   to hit this class of issue in `test/cure/elab/dependent_construction_test.exs`
   (its `@vec` fixture + `prepend(Z(), prepend(S(Z()), empty()))`) and
   `test/cure/elab/cross_arg_implicit_test.exs`.
2. Re-derive a variant where the OUTER constructor call under test is written
   **qualified** (`Std.Vector.prepend(...)`/`Std.Vector.empty()`, after `use
   Std.Vector`, optionally combined with a local `type Nat` shadow to also
   exercise R1+R3 together) and appears in a position that is elaborated by
   *inference*, not by checking against an annotated return type (the checking
   path routes through the sibling `elaborate_ctor_app_bidirectional` instead,
   which this task does not touch and does not need `resolved` threaded into,
   since that path already receives whatever key `constructor_pattern`/its own
   caller resolved).
3. Run it. If it does not yet fail before the fix, that means this exact
   invocation doesn't reach the retry branch — adjust (nest one level deeper,
   or move the call into an argument position of another call) until it does.
4. Add the resulting program as a red test asserting `{:ok, _env} =
   elaborate(src)` in `test/cure/elab/type_shadowing_test.exs`.
5. Confirm it is red for the RIGHT reason: temporarily revert only the
   `elaborate_ctor_app_infer_bidirectional(env, resolved, …)` argument back to
   `atom` and re-run — the test must fail specifically then (proving it
   exercises the retry call, not some unrelated path), then re-apply the fix
   and confirm green.
This is the same "verify against the actual code, adjust the specifics"
discipline already used in Task 7 Step 2 and Task 11 Step 5 — the mechanism
and verification method are exact; the literal source text is intentionally
left for empirical construction rather than asserted here unverified.

- [ ] **Step 5: Run the value/pattern half green**

Run: `mix test test/cure/elab/type_shadowing_test.exs`
Expected: the expression + pattern positions resolve (the whole `R3` test passes once Task 8 lands the `Std.Nat` type slot; if isolated per Step-2 note, the isolated version passes now).

- [ ] **Step 6: Commit**

```bash
git add -- lib/cure/elab/elaborator.ex test/cure/elab/type_shadowing_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): resolve qualified ctors in pattern + expression positions (R3)"
```

---

### Task 8: Wire qualified resolution into the type-slot call sites (R4 + finish R3)

> **Amendment (uniform bare-name resolution — added during execution, operator-approved).**
> The plan as originally written was internally contradictory: R2-full asserts bare
> `S(Z())` resolves under a local `Nat = Zero|Suc` shadow, but Task 8 Step 5 declined to
> resolve shadowed bare names (calling "absent" acceptable), and the re-key removes the
> bare `:Z`/`:S` keys — so R2-full could not pass, contradicting spec §3.3 / line 305 /
> spec-shadow03 ("unqualified `Z`/`S` still refers to imported `Std.Nat`"). Resolution
> (operator directive: align with Idris/Agda per-name scoping): add ONE shared helper
> `Resolution.resolve_bare_shadowed(env, bare) :: {:ok, atom} | :none | {:ambiguous, [mod]}`
> — a bare name ABSENT from the registry but present under EXACTLY ONE re-keyed
> `:"Mod#Name"` variant resolves to that variant (≥2 ⇒ ambiguous/R7; 0 ⇒ none). It is
> consulted at ALL FOUR bare-name sites, only AFTER the bare key is confirmed absent:
> `elaborate_named_call` (value/infer), `elaborate_expr_checked` ctor branch (value/check,
> via `cres`), `resolve_index_name` (type slot; exactly-one resolves, ambiguous → R7),
> and the pattern path (`resolve_ctor_key`, used by `partition_arms` +
> `partition_rematch_arms`) BEFORE the `get_ctor == nil` gate. Sound (pure name
> resolution; the kernel re-checks the assembled term; oracle guards parity), R6-safe
> (fires only when a re-keyed variant exists, i.e. only in shadowing programs, so no
> currently-passing program changes). R1 still holds: when the local redeclares `Z`
> (`Nat = Z|S`), bare `:Z` is present → the "absent" precondition fails → local wins.
> Consequence: R5 re-anchors to the family-mismatch gate (see Task 9 amendment). The
> plan's watered-down shadow03 is restored to its full bare-`Z`/`S` form; `shadow09`
> (bare `Z()`/`S(k)` patterns on an imported `Std.Nat` scrutinee) is the faithfulness
> proof (accept/accept). shadow03/09 verdicts committed with the uniform-resolution work.

**Files:**
- Modify: `lib/cure/elab/declarations.ex` — `idx_to_core` `{:function_call,…}` clause (~726) and `{:attribute_access,…}` clause (~820); `resolve_index_name/2` (~832).
- Modify: `test/cure/elab/type_shadowing_test.exs`
- Create: `test/oracle/shadow/shadow04_escape_hatch.{cure,idr}`, `shadow05_module_typename_collapse.{cure,idr}`

**Interfaces:**
- Consumes: `Resolution.resolve_qualified/3`.
- Produces: qualified type-slot resolution for the nullary (shape (a), `attribute_access`) case, exercised end-to-end by shadow04/shadow05. The `function_call` clause patch also covers a qualified *parameterized* type reference (shape (b), e.g. `Std.Vector(Nat)`) in principle, but **this sub-case is unverified against the actual grammar and no test in this plan exercises it** — tracing `parse_type_expr` (parser.ex ~3961) suggests a qualified parameterized type reference does not actually parse as a `function_call` today (its `Name(A,B)` branch only fires when `(` follows the single identifier just consumed, not after a full dotted chain), so this patch may be inert dead code for that shape. Do not treat it as delivering R3/R4 for parameterized qualified types — only the nullary case is claimed as covered by this task's own tests.

- [ ] **Step 1: Write the shadow05 behavioral test (red)**

Add to `test/cure/elab/type_shadowing_test.exs`:
```elixir
  test "R4: `Std.Nat` in a type slot resolves to the imported type (module==typename collapse)" do
    src = """
    mod Collapse
      use Std.Nat
      type Nat = Zero | Suc(Nat)
      fn imported_zero() -> Std.Nat = Std.Nat.Z()
    end
    """

    assert {:ok, _env} = elaborate(src)
  end
```

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/cure/elab/type_shadowing_test.exs`
Expected: FAIL — `Std.Nat` in the return-type slot. As call-flattening leaves `Nat` reference either as an `attribute_access` (no parens) or a `function_call` name `"Std.Nat"`; today `idx_to_core` errors `{:bad_projection,_}` or builds a dangling `{:global, :"Std.Nat"}`.

- [ ] **Step 3: Add qualified handling to the `function_call` clause of `idx_to_core`**

In `lib/cure/elab/declarations.ex:726`, add a resolved-key short-circuit at the top of the non-function-type branch, before the existing `cond`:
```elixir
  defp idx_to_core({:function_call, fmeta, args}, scope, fam, env) do
    if Keyword.get(fmeta, :function_type) do
      arrow_to_pi(args, scope, fam, env)
    else
      name = Keyword.fetch!(fmeta, :name)
      atom = String.to_atom(name)

      with {:ok, core_args} <- map_idx_to_core(args, scope, fam, env) do
        qualified =
          if String.contains?(name, ".") do
            Cure.Elab.Resolution.resolve_qualified(env, name, :type)
          else
            :error
          end

        cond do
          match?({:ok, _}, qualified) ->
            {:ok, key} = qualified
            {params, indices} = Enum.split(core_args, Inductive.param_count(env, key))
            {:ok, {:data, key, params, indices}}

          idx = Enum.find_index(scope, &(&1 == name)) ->
            {:ok, Enum.reduce(core_args, {:var, idx}, fn a, acc -> {:app, acc, a} end)}

          atom == :Eq and length(core_args) == 3 ->
            ...
```
(Only the new `qualified` binding + the leading `match?({:ok, _}, qualified) ->` cond clause are added; the rest of the `cond` is untouched. For a non-dotted `name`, `qualified == :error`, so behavior is identical.)

- [ ] **Step 4: Add a qualified/module clause to `idx_to_core`'s `attribute_access` (shape (a), nullary no-parens)**

Replace the `{:attribute_access,…}` clause in `lib/cure/elab/declarations.ex:820` so a dotted module/type path is tried before the `.1`/`.2` projection interpretation:
```elixir
  defp idx_to_core({:attribute_access, meta, [inner_ast]} = node, scope, fam, env) do
    attr = Keyword.fetch!(meta, :attribute)

    dotted =
      case Cure.Compiler.Parser.dotted_path_of(node) do
        nil -> nil
        s -> s
      end

    cond do
      # A qualified TYPE reference like Std.Nat / Std.Nat.Nat (no call parens).
      is_binary(dotted) and match?({:ok, _}, Cure.Elab.Resolution.resolve_qualified(env, dotted, :type)) ->
        {:ok, key} = Cure.Elab.Resolution.resolve_qualified(env, dotted, :type)
        {:ok, {:data, key, [], []}}

      attr in ["1", "2"] ->
        with {:ok, inner} <- idx_to_core(inner_ast, scope, fam, env) do
          case attr do
            "1" -> {:ok, {:fst, inner}}
            "2" -> {:ok, {:snd, inner}}
          end
        end

      true ->
        {:error, {:bad_projection, attr}}
    end
  end
```
This needs a small public helper on the parser to reconstruct the dotted string from an `attribute_access` node (the parser already has the private `extract_dotted_path/1`). Add to `lib/cure/compiler/parser.ex`:
```elixir
  @doc "Reconstruct a dotted path string from an attribute_access/variable node, or nil."
  def dotted_path_of(node), do: extract_dotted_path(node)
```

- [ ] **Step 5: Extend `resolve_index_name/2` for bare names that are only reachable qualified**

`resolve_index_name/2` (`declarations.ex:832`) handles a *bare* type name in a type slot. It already prefers a family over a ctor. No change is required for shadowing itself (a shadowed bare name is simply the local winner or absent), but confirm it is unaffected: after re-keying, a bare `Nat` resolves to the local family key `:Nat` (present), unchanged. Add a regression assertion rather than code — see Step 6. (R7's ambiguity teaching for this function lands in Task 10.)

- [ ] **Step 6: Run behavioral + finish R2/R3/R4**

Run: `mix test test/cure/elab/type_shadowing_test.exs`
Expected: PASS — R2 (full, including the `imported_one`/`Std.Nat` return type), R3 (full), R4 all green.

- [ ] **Step 7: Add shadow04 + shadow05 oracle probes**

`test/oracle/shadow/shadow04_escape_hatch.cure`:
```
mod EscapeHatch
  use Std.Nat
  type Nat = Zero | Suc(Nat)
  fn imported_two() -> Std.Nat = Std.Nat.S(Std.Nat.Z())
  fn is_zero(n: Std.Nat) -> Nat = match n
    Std.Nat.Z() -> Zero()
    Std.Nat.S(k) -> Suc(Zero())
end
```
`test/oracle/shadow/shadow04_escape_hatch.idr`:
```idris
%default total

data Local = Zero | Suc Local

importedTwo : Nat
importedTwo = S (S Z)

isZero : Nat -> Local
isZero Z = Zero
isZero (S k) = Suc Zero
```
(Idris' prelude `Nat`/`Z`/`S` play the role of the "imported, still-reachable" family while `Local` is the shadowing type — a faithful model of "a distinct local type coexisting with the library one, both used".)

`test/oracle/shadow/shadow05_module_typename_collapse.cure`:
```
mod Collapse
  use Std.Nat
  type Nat = Zero | Suc(Nat)
  fn imported_zero() -> Std.Nat = Std.Nat.Z()
end
```
`test/oracle/shadow/shadow05_module_typename_collapse.idr`:
```idris
%default total

data Local = Zero | Suc Local

importedZero : Nat
importedZero = Z
```

- [ ] **Step 8: Regenerate verdicts**

Run: `mix cure.oracle shadow`
Expected: `shadow04`/`shadow05` = `same` (accept/accept).

- [ ] **Step 9: Run the regression guard**

Run: `mix test test/cure/elab/auto_prelude_test.exs test/oracle_replay_test.exs`
Expected: PASS.

- [ ] **Step 10: Commit**

```bash
git add -- lib/cure/elab/declarations.ex lib/cure/compiler/parser.ex test/cure/elab/type_shadowing_test.exs test/oracle/shadow/shadow04_escape_hatch.cure test/oracle/shadow/shadow04_escape_hatch.idr test/oracle/shadow/shadow05_module_typename_collapse.cure test/oracle/shadow/shadow05_module_typename_collapse.idr test/oracle/shadow/verdicts.json
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): qualified type-slot resolution + module==typename collapse (R3/R4)"
```

---

### Task 9: R5 — `:shadowed_ctor` targeted diagnostic

> **Amendment (R5 re-anchor — consequence of Task 8's uniform bare-name resolution).**
> The original plan intercepted at the `get_ctor == nil` gate (bare `Z` was absent
> after re-keying). With uniform resolution (Task 8 amendment), the pattern path's
> `resolve_ctor_key` now resolves bare `Z` on a local-`Nat` scrutinee to the present
> re-keyed `:"Std.Nat#Z"`, so it PASSES the nil gate and instead hits the
> family-mismatch gate `ctor_family(sig, cname) != dname`. R5 is therefore intercepted
> THERE: a shared `shadowed_or_foreign_ctor(env, sig, cname0, cname, dname)` helper
> checks `Resolution.shadowed_origin(env, cname0)` on the ORIGINAL bare name — if it
> was shadowed off the registry, emit `{:shadowed_ctor, ctor: cname0, shadowed_module,
> local_family: dname, local_ctors, hint: "Mod.ctor"}`; otherwise the existing
> `{:foreign_ctor, cname}` (a genuine cross-family match) is unchanged. The nil gate
> keeps returning `:unknown_pattern_constructor` for a genuinely-unknown bare ctor
> (`resolve_bare_shadowed` → `:none`, so it stays bare and absent). Applied at both
> `partition_arms` and `partition_rematch_arms`. `shadow06` stays reject/reject (`same`).

**Files:**
- Modify: `lib/cure/elab/resolution.ex` — add `shadowed_origin/2`.
- Modify: `lib/cure/elab/elaborator.ex` — intercept the `{:unknown_pattern_constructor, cname}` raise in `partition_arms` and `partition_rematch_arms`.
- Modify: `test/cure/elab/type_shadowing_test.exs`
- Create: `test/oracle/shadow/shadow06_shadow_diagnostic.{cure,idr}`

**Interfaces:**
- Consumes: the re-keyed env; `resolve_ctor_key/2` (Task 7).
- Produces: `Resolution.shadowed_origin/2`; the `{:shadowed_ctor, …}` error tuple.

**Anchor (spec §5):** after re-keying, a bare `Z()` used on a local-`Nat` scrutinee is *absent* from the registry, so it fails the `Inductive.get_ctor(env, cname) == nil` gate → today `{:unknown_pattern_constructor, cname}`. Intercept there.

- [ ] **Step 1: Write the failing diagnostic test**

Add to `test/cure/elab/type_shadowing_test.exs`:
```elixir
  test "R5: using a shadowed bare ctor on the local family yields a targeted :shadowed_ctor error" do
    src = """
    mod WrongCtor
      use Std.Nat
      type Nat = Zero | Suc(Nat)
      fn bad(n: Nat) -> Nat = match n
        Z() -> Zero()
        S(m) -> Suc(m)
    end
    """

    assert {:error, {:shadowed_ctor, info}} = elaborate(src)
    assert info[:ctor] == :Z
    assert info[:shadowed_module] == "Std.Nat"
    assert info[:hint] == "Std.Nat.Z"
    assert info[:local_family] == :Nat
  end
```

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/cure/elab/type_shadowing_test.exs`
Expected: FAIL — currently returns `{:error, {:unknown_pattern_constructor, :Z}}` (bare `Z` was re-keyed off the registry) or `{:missing_branch, _}`; the specific `:shadowed_ctor` assertion fails.

- [ ] **Step 3: Add `shadowed_origin/2` to `Resolution`**

```elixir
  @doc """
  If a bare constructor/family name was shadowed (re-keyed off the bare atom),
  find the re-keyed variant `:"Mod#bare"` still present in the env and report
  its origin module + re-keyed atom. Returns `:error` if no shadowed variant
  exists (the name is genuinely unknown, not shadowed).
  """
  @spec shadowed_origin(Env.t(), atom()) :: {:ok, String.t(), atom()} | :error
  def shadowed_origin(%Env{ctors: ctors, families: families}, bare) do
    suffix = "#" <> Atom.to_string(bare)

    match =
      Enum.find_value(Map.keys(ctors) ++ Map.keys(families), fn k ->
        s = Atom.to_string(k)
        if String.ends_with?(s, suffix), do: {String.trim_trailing(s, suffix), k}, else: nil
      end)

    case match do
      {mod_id, key} -> {:ok, mod_id, key}
      nil -> :error
    end
  end
```

- [ ] **Step 4: Intercept the unknown-constructor gate in `partition_arms`**

In `partition_arms`, replace the `Inductive.get_ctor(env, cname) == nil ->` branch body with a shadow check:
```elixir
              Inductive.get_ctor(env, cname) == nil ->
                case Cure.Elab.Resolution.shadowed_origin(env, cname) do
                  {:ok, mod_id, _key} ->
                    {:halt,
                     {:error,
                      {:shadowed_ctor,
                       [
                         ctor: cname,
                         shadowed_module: mod_id,
                         local_family: dname,
                         local_ctors: Enum.map(Inductive.ctors_of(Context.signature(ctx), dname), & &1.name),
                         hint: mod_id <> "." <> Atom.to_string(cname)
                       ]}}}

                  :error ->
                    {:halt, {:error, {:unknown_pattern_constructor, cname}}}
                end
```
Apply the same interception in `partition_rematch_arms` at its `Inductive.get_ctor(env, cname) == nil ->` branch (using the same `dname`/`sig` in scope).

- [ ] **Step 5: Run to verify pass**

Run: `mix test test/cure/elab/type_shadowing_test.exs`
Expected: PASS — the `:shadowed_ctor` error with the exact fields.

- [ ] **Step 6: Add the shadow06 oracle probe (reject/reject)**

`test/oracle/shadow/shadow06_shadow_diagnostic.cure`: the `WrongCtor` module above.
`test/oracle/shadow/shadow06_shadow_diagnostic.idr`:
```idris
%default total

data Nat' = Zero | Suc Nat'

bad : Nat' -> Nat'
bad Z = Zero
bad (S m) = Suc m
```
(Idris rejects `Z`/`S` as constructors of `Nat'` — an out-of-family constructor error — so both sides reject: relation `same` on *reject*, reason pinned to "shadowed/wrong constructor family".)

- [ ] **Step 7: Regenerate verdicts + confirm reject/reject**

Run: `mix cure.oracle shadow`
Expected: `shadow06` = `{"cure":"reject","idris":"reject","relation":"same","reason":"shadowed constructor used on local family"}`.

- [ ] **Step 8: Commit**

```bash
git add -- lib/cure/elab/resolution.ex lib/cure/elab/elaborator.ex test/cure/elab/type_shadowing_test.exs test/oracle/shadow/shadow06_shadow_diagnostic.cure test/oracle/shadow/shadow06_shadow_diagnostic.idr test/oracle/shadow/verdicts.json
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): :shadowed_ctor targeted diagnostic (R5)"
```

---

### Task 10: R7 — `:ambiguous_name` for distinct import-vs-import collisions

> **Amendment (shadow07 unit-only; wiring interaction with uniform resolution).**
> `import_source_path/1` resolves only `Std.*` modules from the single stdlib source
> dir, so two GENUINELY-distinct modules both declaring `type Nat` cannot be loaded
> without mutating the shared stdlib dir (unsafe under the concurrent-agent
> constraint), and the real stdlib has no such pair. Per Step 7's own fallback,
> **shadow07 is unit-covered only** — `ambiguous_modules/2`'s ExUnit tests
> (`resolution_test.exs`) pin the mechanism; no oracle probe is added. Wiring stands
> as planned: `resolve_index_name` (type) emits `{:ambiguous_name, atom, mods}` before
> `{:global, atom}` and its `{:variable,…}` caller turns it into `{:error, …}`;
> `elaborate_named_call` (value) checks `ambiguous_modules/2 >= 2` right after the ctor
> branch, before `implicit_def?`. Note the uniform-resolution helper
> `resolve_bare_shadowed/2` already returns `{:ambiguous, mods}` for ≥2 variants and is
> consulted first — so an ambiguous name never mis-resolves to a single variant; it
> falls through to this R7 branch.

**Files:**
- Modify: `lib/cure/elab/resolution.ex` — add `ambiguous_modules/2`.
- Modify: `lib/cure/elab/declarations.ex` — `resolve_index_name/2` checks ambiguity before falling to `{:global, atom}`.
- Modify: `lib/cure/elab/elaborator.ex` — `elaborate_named_call/5` checks ambiguity before the global-def fallback (value position).
- Modify: `test/cure/elab/type_shadowing_test.exs`
- Create: two scratch stdlib-style modules for the probe + `test/oracle/shadow/shadow07_ambiguous.{cure,idr}`

**Interfaces:**
- Consumes: the re-keyed env (an ambiguous name has ≥2 `:"Mod#Name"` variants and NO bare key).
- Produces: `Resolution.ambiguous_modules/2`; the `{:ambiguous_name, name, [modules]}` error.

- [ ] **Step 1: Create two scratch distinct modules that both declare `type Nat`**

`test/oracle/shadow/support/foo.cure`:
```
mod Std.Foo
  type Nat = FZero | FSucc(Nat)
end
```
`test/oracle/shadow/support/bar.cure`:
```
mod Std.Bar
  type Nat = BZero | BSucc(Nat)
end
```
(These are scratch sources loaded by the test via an explicit path, not installed into `priv/std`. The test writes them to a temp dir or references them relatively — see Step 3. The probe's point is two GENUINELY distinct modules providing `Nat`.)

- [ ] **Step 2: Write the failing ambiguity test**

Add to `test/cure/elab/type_shadowing_test.exs` (using the real stdlib is cleaner if two same-family modules exist; since they don't, drive ambiguity directly through `Resolution` + a crafted env, plus an end-to-end check if the scratch-module loader supports arbitrary paths):
```elixir
  test "R7: ambiguous_modules reports ≥2 origins for a name re-keyed off the bare atom" do
    env =
      %Cure.Core.Env{}
      |> Cure.Core.Inductive.declare(Cure.Core.Inductive.family(:"Std.Foo#Nat", [], [], 0),
           [Cure.Core.Inductive.ctor(:"Std.Foo#FZero", [], [])])
      |> Cure.Core.Inductive.declare(Cure.Core.Inductive.family(:"Std.Bar#Nat", [], [], 0),
           [Cure.Core.Inductive.ctor(:"Std.Bar#BZero", [], [])])

    mods = Cure.Elab.Resolution.ambiguous_modules(env, :Nat)
    assert Enum.sort(mods) == ["Std.Bar", "Std.Foo"]
  end
```

- [ ] **Step 3: Implement `ambiguous_modules/2`**

```elixir
  @doc """
  All origin modules that provide family `bare` under a re-keyed `:"Mod#bare"`
  family key. ≥2 ⇒ the unqualified name is ambiguous (no local winner claimed
  the bare key). Returns [] when the bare key is present (a winner exists) or
  the name is unknown.
  """
  @spec ambiguous_modules(Env.t(), atom()) :: [String.t()]
  def ambiguous_modules(%Env{families: families}, bare) do
    if Map.has_key?(families, bare) do
      []
    else
      suffix = "#" <> Atom.to_string(bare)

      families
      |> Map.keys()
      |> Enum.flat_map(fn k ->
        s = Atom.to_string(k)
        if String.ends_with?(s, suffix), do: [String.trim_trailing(s, suffix)], else: []
      end)
    end
  end
```

- [ ] **Step 4: Teach `resolve_index_name/2` to raise ambiguity (type slot)**

`resolve_index_name/2` returns a bare Core node today; to surface an error it must be allowed to fail. The lowest-churn approach: keep `resolve_index_name/2` returning a node, but have its caller detect the ambiguous case. Concretely, add a guard clause BEFORE the existing `true -> {:global, atom}` fallback:
```elixir
  defp resolve_index_name(name, env) do
    atom = String.to_atom(name)

    cond do
      primitive_type(name) != nil -> primitive_type(name)
      Inductive.family?(env, atom) -> {:data, atom, [], []}
      Inductive.get_ctor(env, atom) -> {:ctor, atom, []}
      length(Cure.Elab.Resolution.ambiguous_modules(env, atom)) >= 2 ->
        {:ambiguous_name, atom, Cure.Elab.Resolution.ambiguous_modules(env, atom)}
      true -> {:global, atom}
    end
  end
```
`resolve_index_name/2`'s only caller is the `{:variable, _meta, name}` clause of `idx_to_core` (`declarations.ex:719-724`):
```elixir
  defp idx_to_core({:variable, _meta, name}, scope, _fam, env) do
    case Enum.find_index(scope, &(&1 == name)) do
      nil -> {:ok, resolve_index_name(name, env)}
      index -> {:ok, {:var, index}}
    end
  end
```
Change the `nil ->` branch to detect the ambiguous case before wrapping in `{:ok, _}`:
```elixir
  defp idx_to_core({:variable, _meta, name}, scope, _fam, env) do
    case Enum.find_index(scope, &(&1 == name)) do
      nil ->
        case resolve_index_name(name, env) do
          {:ambiguous_name, atom, mods} -> {:error, {:ambiguous_name, atom, mods}}
          node -> {:ok, node}
        end

      index ->
        {:ok, {:var, index}}
    end
  end
```
(A local-scope hit — `index -> {:ok, {:var, index}}` — is unaffected, so a bound variable named the same as an ambiguous global still shadows it correctly, unchanged from today.)

- [ ] **Step 5: Teach `elaborate_named_call/5` to raise ambiguity (value slot)**

`elaborate_named_call/5`'s `cond` (post-Task-7) has no single labeled "unknown global" branch to insert before — its actual final shape is `refl` → `Inductive.get_ctor(env, resolved)` (Task 7) → `implicit_def?(env, atom)` → a lambda-argument bidirectional branch → a catch-all `true ->` that always attempts generic elaboration (with its own bidirectional retry on failure; `elaborator.ex:242-267`). None of those later branches is a clean insertion point — the ambiguity check must run *before all of them*, right after the ctor branch, so an ambiguous bare name is caught before it falls through to `implicit_def?`/the generic path and produces an unrelated, confusing error instead of `:ambiguous_name`. Add the new clause immediately after the (Task-7-patched) `Inductive.get_ctor(env, resolved) -> ...` branch and its retry, using the ORIGINAL unresolved `atom` (an ambiguous name has no dot — it is a plain bare name with ≥2 re-keyed origins and no winner, so `resolved == atom` here always; `ambiguous_modules/2` is keyed on the bare atom regardless):
```elixir
      Inductive.get_ctor(env, resolved) ->
        ...
        # (Task 7's ctor branch + retry, unchanged)

      length(Cure.Elab.Resolution.ambiguous_modules(env, atom)) >= 2 ->
        {:error, {:ambiguous_name, atom, Cure.Elab.Resolution.ambiguous_modules(env, atom)}}

      implicit_def?(env, atom) ->
        ...
```
(Inserted as a new `cond` clause between the ctor branch and `implicit_def?(env, atom)`.)

- [ ] **Step 6: Run the unit + behavioral tests**

Run: `mix test test/cure/elab/type_shadowing_test.exs test/cure/elab/resolution_test.exs`
Expected: PASS — `ambiguous_modules/2` returns both origins; if the scratch-module end-to-end loader is wired, the bare `Nat` use errors `{:ambiguous_name, :Nat, ["Std.Bar", "Std.Foo"]}`.

- [ ] **Step 7: Add shadow07 oracle probe (documented reject)**

If the scratch modules can be resolved by the oracle's import path, add `test/oracle/shadow/shadow07_ambiguous.cure` importing both and using bare `Nat`; the `.idr` models two same-named datatypes in separate namespaces used unqualified (Idris reports an ambiguity). Relation: `same` on reject (or `cure_stricter` with the reason "ambiguous unqualified name across distinct imports"). If the oracle cannot load scratch modules outside `priv/std`, SKIP the oracle probe and rely on the unit + behavioral assertions — and `log`/note in the commit body that shadow07 is unit-covered only (no silent gap).

- [ ] **Step 8: Regenerate verdicts (if probe added)**

Run: `mix cure.oracle shadow`
Expected: `shadow07` present, or documented as unit-only.

- [ ] **Step 9: Commit**

```bash
git add -- lib/cure/elab/resolution.ex lib/cure/elab/declarations.ex lib/cure/elab/elaborator.ex test/cure/elab/type_shadowing_test.exs test/cure/elab/resolution_test.exs test/oracle/shadow/
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): :ambiguous_name for distinct import-vs-import collisions (R7)"
```

---

### Task 11: Codegen — recognize a qualified constructor call BEFORE the generic qualified-call dispatch

> **Amendment (Erlang.Length hazard — found by the full-suite gate).** The plan's
> `String.contains?(name, ".") and constructor?(tail)` guard is NOT sufficient: a
> qualified FFI call whose function is PascalCase in Cure source — `Erlang.Length(x)`
> (→ `erlang:length`, exercised by `Cure.Types.ProtocolTest`) — has a PascalCase tail
> too, so the bare guard hijacked it into a bogus `{:length, …}` tuple, failing the
> full suite. Fix: also require `cure_qualified_module?(name)` — the module prefix must
> resolve (via `cure_module_to_atom/1`) to a `Cure.*` module, NOT a special BEAM module
> like `Erlang` (`:erlang`). A qualified constructor escape hatch (`Std.Nat.Z`) always
> lives in a Cure module; a BEAM-FFI remote call does not, so it stays a remote call.
> Regression pinned by a `Erlang.Length` codegen test.

**Corrected mechanism (supersedes an earlier "strip `Mod#` prefix in `constructor_tag/1`" draft — verified wrong against the source, see below).** `lib/cure/compiler/codegen.ex` has **zero** references to `Cure.Core`/`Cure.Elab` anywhere in the file — it never sees the elaborator's internal `Mod#Name`-rekeyed `Env` atoms at all; it compiles directly off the raw parser AST using purely syntactic string heuristics (`constructor?/1` is itself just a PascalCase check on a string). So a `Mod#Ctor`-shaped atom never reaches codegen, and the originally-planned `constructor_tag/1` "#"-stripping fix targets data that cannot occur.

The REAL problem is upstream of `constructor_tag/1` entirely: `compile_function_call/3` (codegen.ex ~1126) has this dispatch —
```elixir
      form =
        cond do
          # Qualified call: Mod.fun(args) -- must come before constructor check
          String.contains?(name, ".") ->
            compile_qualified_call(name, arg_forms, line)

          # ADT constructor: PascalCase name -> tagged tuple
          constructor?(name) ->
            compile_constructor_call(name, arg_forms, line)
          ...
```
— any dotted call `name` (e.g. the parser-flattened `"Std.Nat.Z"` from `Std.Nat.Z()`, per §3.6(b)) is routed to `compile_qualified_call/3` **before** the constructor check ever runs. `compile_qualified_call/3` unconditionally treats it as a remote function call (`'Cure.Std.Nat':z(...)`, splitting the LAST segment off as a function name via `mangle_fn_name/1`) — never as a tagged tuple. So `Std.Nat.Z()`, written anywhere in a Cure program today (and unchanged by the originally-planned patch), compiles to a call to a non-existent remote function, not `{z}`. `constructor_tag/1` is never even reached for a qualified constructor call.

**Files:**
- Modify: `lib/cure/compiler/codegen.ex` — `compile_function_call/3`'s `cond` (~1161-1169), add one clause before the `String.contains?(name, ".")` branch. `constructor_tag/1` itself is **unmodified** (once the dispatch is fixed, it only ever receives a bare segment, exactly like today's unqualified case).
- Create: `test/cure/compiler/shadow_codegen_test.exs`

**Interfaces:**
- Consumes: `Cure.Compiler.Codegen.compile_expr/1` (existing public entry, the simplest way to reach `compile_function_call/3` in isolation — no `Env`/elaboration needed, since the whole fix is syntactic) and `compile_module/2` (existing public entry — NOT `compile/1`, which does not exist).
- Produces: a bare tagged-tuple form `{:tuple, _, [{:atom, _, :z}]}` for a qualified nullary constructor call `Std.Nat.Z()`, matching what the unqualified `Z()` already produces.

**Invariant (spec §3.5):** the BEAM value tag must be bare so AtomVM's value format is unchanged and a qualified/escape-hatch constructor reference is runtime-indistinguishable from its bare form.

- [ ] **Step 1: Write the failing codegen unit test**

`test/cure/compiler/shadow_codegen_test.exs`:
```elixir
defmodule Cure.Compiler.ShadowCodegenTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Codegen

  test "a qualified nullary constructor call compiles to the same tagged tuple as its bare form" do
    {:ok, qualified_form} = Codegen.compile_expr({:function_call, [name: "Std.Nat.Z"], []})
    {:ok, bare_form} = Codegen.compile_expr({:function_call, [name: "Z"], []})

    assert qualified_form == bare_form
    assert {:tuple, _line, [{:atom, _, :z}]} = qualified_form
  end

  test "a qualified constructor call with args compiles to a tagged tuple, not a remote call" do
    {:ok, form} =
      Codegen.compile_expr({:function_call, [name: "Std.Nat.S"], [{:function_call, [name: "Std.Nat.Z"], []}]})

    assert {:tuple, _line, [{:atom, _, :s}, {:tuple, _, [{:atom, _, :z}]}]} = form
  end

  test "a qualified NON-constructor call (lowercase tail) is still a remote call, unchanged" do
    {:ok, form} = Codegen.compile_expr({:function_call, [name: "Std.Nat.plus"], []})
    assert {:call, _line, {:remote, _, {:atom, _, _mod}, {:atom, _, :plus}}, []} = form
  end
end
```

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/cure/compiler/shadow_codegen_test.exs`
Expected: FAIL — the first two tests currently produce a `{:call, _, {:remote, ...}, ...}` form (a bogus remote call to a non-existent `z`/`s` function), not a tagged tuple; they do not match `bare_form`/the expected tuple shape.

- [ ] **Step 3: Add the qualified-constructor dispatch clause**

`lib/cure/compiler/codegen.ex`, in `compile_function_call/3`'s `cond` (~1161):
```elixir
      form =
        cond do
          # A qualified CONSTRUCTOR reference (escape hatch, e.g. `Std.Nat.Z()`):
          # the last dotted segment is PascalCase, i.e. a constructor by the
          # same bare-name heuristic `constructor?/1` already uses everywhere
          # else in this module. Checked BEFORE the generic qualified-call
          # branch below, or a qualified constructor call compiles to a bogus
          # remote call to a non-existent function instead of a tagged tuple.
          # Codegen never sees the elaborator's internal `Mod#Name`-keyed Env
          # atoms (this module has no dependency on `Cure.Core`/`Cure.Elab` at
          # all — verified) — it works purely off the surface AST string, so
          # the bare name it needs is just the last segment of the dotted path.
          String.contains?(name, ".") and constructor?(qualified_ctor_tail(name)) ->
            compile_constructor_call(qualified_ctor_tail(name), arg_forms, line)

          # Qualified call: Mod.fun(args) -- must come before constructor check
          String.contains?(name, ".") ->
            compile_qualified_call(name, arg_forms, line)

          # ADT constructor: PascalCase name -> tagged tuple
          constructor?(name) ->
            compile_constructor_call(name, arg_forms, line)
          ...
```
Add the helper near `compile_constructor_call/3`:
```elixir
  # The final dotted segment of a qualified surface name, e.g.
  # "Std.Nat.Z" -> "Z". Used only to decide/extract a qualified CONSTRUCTOR
  # reference; codegen has no Env, so this is a pure string operation.
  defp qualified_ctor_tail(name), do: name |> String.split(".") |> List.last()
```
(`constructor_tag/1` is untouched — it now only ever receives a bare segment like `"Z"`, exactly as it does for an unqualified constructor today, so no separator-stripping logic is needed there at all.)

- [ ] **Step 4: Run to verify pass**

Run: `mix test test/cure/compiler/shadow_codegen_test.exs`
Expected: PASS (all three tests, including the "still a remote call" regression check).

- [ ] **Step 5: Host codegen sanity for the escape-hatch path (gate item 4)**

Compile the shadow04 program end-to-end through the real `compile_module/2` entry point and assert the module assembles with no error and no leftover dotted/qualified atom in the emitted forms. Add to `test/cure/compiler/shadow_codegen_test.exs`:
```elixir
  test "a program using Std.Nat.Z compiles to a module with a bare :z tag, not a dotted/remote artifact" do
    src = """
    mod EscapeCodegen
      use Std.Nat
      type Nat = Zero | Suc(Nat)
      fn imported_zero() -> Std.Nat = Std.Nat.Z()
    end
    """

    {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)
    {:ok, forms} = Codegen.compile_module(ast, emit_events: false)

    dump = inspect(forms)
    refute String.contains?(dump, "Std.Nat.Z")
    refute String.contains?(dump, "#")
    assert String.contains?(dump, ":z}")
  end
```
(This is a stronger assertion than "no # present" — it positively confirms the bare `:z` tag actually appears, not merely that no `#`/dotted artifact survives, which the pre-fix broken remote-call form would also satisfy vacuously.)

- [ ] **Step 6: Run to verify pass**

Run: `mix test test/cure/compiler/shadow_codegen_test.exs`
Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add -- lib/cure/compiler/codegen.ex test/cure/compiler/shadow_codegen_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(codegen): recognize qualified constructor calls before the remote-call dispatch"
```

---

### Task 12: Full gate — replay, full suite, verdicts, final report

**Files:**
- No new production code; verification + any verdicts.json finalization.

**Interfaces:**
- Consumes: everything above.
- Produces: a green gate confirming R1–R7 + R6 non-regression.

- [ ] **Step 1: Regenerate + freeze the shadow cluster verdicts**

Run: `mix cure.oracle shadow`
Expected: `shadow01`–`shadow06` and `shadow08` present with their intended relations (shadow07 present or documented unit-only per Task 10). Review `test/oracle/shadow/verdicts.json` for any unintended `cure_stricter` — each must have a written reason.

- [ ] **Step 2: Oracle replay (no other probe regressed)**

Run: `mix test test/oracle_replay_test.exs`
Expected: PASS.

- [ ] **Step 3: Full suite ONCE, alone**

Run: `mix test`
Expected: PASS at 2843/0 baseline or higher (new shadow + resolution + codegen tests added). Zero regressions. If any pre-existing test changed behavior, STOP — the non-collision path must be byte-for-byte identical; investigate before proceeding.

- [ ] **Step 4: Auto-prelude guard (explicit re-confirm of the retained skip)**

Run: `mix test test/cure/elab/auto_prelude_test.exs`
Expected: PASS — the auto-prelude skip (retained per Global Constraints) is intact.

- [ ] **Step 5: Commit any verdicts finalization**

```bash
git add -- test/oracle/shadow/verdicts.json
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "test(shadow): freeze shadow-cluster verdicts (R1–R7 gate green)"
```
(If nothing changed since Task 10/11, skip this commit.)

- [ ] **Step 6: Update the parity ledger**

The shadowing fix is a correctness defect gating ledger row #5's auto-generalization path; note its resolution in `docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md` (a one-line pointer near #4/#5), then commit:
```bash
git add -- docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "docs(parity): note local type/ctor shadowing fix (unblocks #5)"
```

---

## Self-Review

**1. Spec coverage:**
- R1 (per-name type+ctor shadowing) → Tasks 5 (re-key) + shadow01/02/08 (08 = transitive-import case). ✓
- R2 (non-shadowed imports stay visible) → Task 5 (residual-drop keeps only losers re-keyed) + Task 8 (`Std.Nat` return) + shadow03. ✓
- R3 (qualified escape hatch) → Tasks 7 (value/pattern) + 8 (type slot) + shadow04. ✓
- R4 (module==typename collapse) → Task 8 (`resolve_qualified` type-slot collapse candidate) + shadow05. ✓
- R5 (shadow-aware diagnostics) → Task 9 (`:shadowed_ctor` at the unknown-ctor gate) + shadow06. ✓
- R6 (no regression) → residual-drop (Task 5) + Tasks 5/8/12 auto-prelude + replay + full-suite guards; every new cond clause is a no-op for non-dotted/non-collision inputs. ✓
- R7 (import-vs-import ambiguity) → Tasks 4 (classify) + 10 (`:ambiguous_name`) + shadow07. ✓
- §3.2 `:case` branch-tag rewrite → Task 2 (explicit test) + Task 3 (def-body rewrite). ✓
- §3.1 dedup/over-detection (diamond + auto+explicit) → Task 4 (classify tests) + Task 5 (distinct_import_modules + AST-own provenance for over-detection; transitive_import_modules for under-detection of a family reached only transitively, pinned by the transitive-import red test). ✓
- §3.5 bare runtime tags → Task 11 (corrected mechanism: codegen call-dispatch fix, not `constructor_tag/1` prefix-stripping — codegen never sees re-keyed Env atoms). ✓
- §3.6 all three call sites → Tasks 7 (`constructor_pattern`, `elaborate_named_call` — 2 sites) fully covered; Task 8's `idx_to_core` covers the nullary `attribute_access` shape (a) fully, but the THIRD site — `idx_to_core`'s `function_call` clause, for a qualified *parameterized* type reference like `Std.Vector(Nat)` — is **unverified and likely unreachable under today's grammar**: tracing `parse_type_expr` (parser.ex ~3961) shows its `Name(A,B)` call-argument branch only fires when `(` immediately follows the single identifier just consumed ("Std"), not after a full dotted chain, so `Std.Vector(Nat)` in a type slot falls into `maybe_parse_type_projection` instead, which does not resume call-argument parsing — leaving `(Nat)` unconsumed (likely a parse error upstream, before `idx_to_core` is ever reached). No task's oracle probe or unit test exercises this shape (the plan itself notes, at shadow04, that the parameterized case is "not this probe's concern"), so this does not block any claimed-green test — but the coverage claim for this specific sub-case is downgraded from ✓ to **unverified/likely moot**; Task 8's own patch to `idx_to_core`'s `function_call` clause remains harmless dead code for it either way (a plain-atom, non-dotted qualified type reference is unaffected).

**2. Placeholder scan:** Every code step shows real code grounded in the verbatim anchors. Three deliberate "verify which error applies / adjust entry-point name / construct empirically" notes (Task 7 Step 2, Task 7 Step 4b, Task 11 Step 5) are read-the-actual-code instructions, not placeholders — they name the exact search target and verification method.

**3. Type consistency:** `rekey_atom/2`, `rekey_term/2`, `resolve_qualified/3`, `shadowed_origin/2`, `ambiguous_modules/2`, `classify/2`, `rekey_module_env/3` names + arities are consistent across Tasks 2–11 and match the Interfaces block. Registry key form `:"<module_id>#<bare>"` and surface form `"<module_id>.<bare>"` are used consistently; the `.`→`#` bridge lives only in `resolve_qualified/3` (Task 6) and `rekey_atom/2` (Task 3).

**Residual scope note (mirrors the spec's own caveats):** the *diamond + local shadow* case (`use Std.Vector` + `use Std.Nat` + a local `Nat`, both imports explicit) and the *transitive-only + local shadow* case (`use Std.Vector` alone + a local `Nat`, no explicit `use Std.Nat`) are both handled by the combination of the transitive-closure ownership scan (`transitive_import_modules/1`) and the residual-bare-drop (`drop_bare_family`) — Task 5. The transitive-only case is now pinned by BOTH a dedicated behavioral red test (Task 5 Step 1, "R1 via transitive import") AND a paired oracle probe (`shadow08`, Task 5 Step 7); the explicit-diamond case remains guarded only by the full-suite/replay run, not a dedicated probe (the stdlib has no such combined program today). If Stage-4 execution surfaces a gap in the explicit-diamond case, add a `shadow09` probe rather than widening scope silently.
