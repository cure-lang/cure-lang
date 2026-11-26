defmodule Cure.Core.UniversePolymorphismCharacterizationTest do
  @moduledoc """
  U0 characterization tests for Phase 5 (C2) — universe polymorphism.

  **Authority:** `docs/superpowers/specs/types/2026-07-20-agda-style-universe-polymorphism-design.md`
  §18 Phase U0: "Add red characterization tests for arbitrary closed levels,
  open level variables, `universe_max`, universe-polymorphic identity, limit
  sorting, and erasure."

  **Inventory:** `docs/LEAN4_PHASE5_U0_INVENTORY.md`.

  Canonical representation and small predicative judgments replace the retired
  fixed-ceiling baseline. U4 and U5 cases assert their intended source/library
  behavior, not historical acceptance of unresolved universe names. There are
  no optional module guards or vacuous missing-family passes.

  Phase tags identify outstanding work for intermediate stage diagnostics only.
  Final Phase 5 acceptance runs every test without phase exclusions.
  """

  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Env, Eval, Kernel, LevelValue, Sort, Term, UniverseLevel}

  # ---------------------------------------------------------------------------
  # U2 — canonical payloads, with explicit legacy integer refusal.
  # ---------------------------------------------------------------------------

  describe "U2 canonical representation replaces the fixed integer hierarchy" do
    test "legacy integer universe syntax is refused rather than silently lifted" do
      for level <- [-1, 0, 2, 3, 37], do: refute(Term.term?({:type, level}))
      assert Term.term?({:type, Sort.finite_closed(37)})
    end

    test "closed sorts retain strict predicative successors without a ceiling" do
      ctx = Context.empty()

      for level <- [0, 1, 2, 37] do
        next = level + 1

        assert {:ok, {:vtype, {:finite, %LevelValue{constant: ^next, atoms: []}}}} =
                 Kernel.infer(ctx, {:type, Sort.finite_closed(level)})

        assert {:error, _} =
                 Kernel.check(
                   ctx,
                   {:type, Sort.finite_closed(level)},
                   Eval.eval({:type, Sort.finite_closed(level)}, [])
                 )
      end
    end

    test "level values and limit sorts have actual Core representations" do
      assert Term.term?({:level_type})
      assert Term.term?({:level_value, UniverseLevel.zero()})
      assert Term.term?({:type, Sort.omega(37)})
    end
  end

  # ---------------------------------------------------------------------------
  # U4 — actual source-level universe resolution, not unresolved globals.
  # ---------------------------------------------------------------------------

  describe "U4: surface universe syntax is resolved as universes" do
    @describetag :u4

    test "Type37 is a real universe in a binder position" do
      source = """
      mod Char.Type37Misread
        fn identity({a: Type37}, x: a) -> a = x
      end
      """

      assert {:ok, _module} = compile(source, "char_type37_misread.cure")
    end

    test "a Type37 identity accepts a small carrier by cumulativity" do
      source = """
      mod Char.Type37Inert
        fn identity({a: Type37}, x: a) -> a = x
        fn use_it(n: Int) -> Int = identity(n)
      end
      """

      assert {:ok, _module} = compile(source, "char_type37_inert.cure")
    end

    test "TypeLimit is a real limit universe in a binder position" do
      source = """
      mod Char.TypeLimitMisread
        fn identity({a: TypeLimit}, x: a) -> a = x
      end
      """

      assert {:ok, _module} = compile(source, "char_typelimit_misread.cure")
    end

    test "Type(0) is rejected instead of treating a Nat as a level" do
      source = """
      mod Char.TypeApplicationMisread
        fn identity({a: Type(0)}, x: a) -> a = x
      end
      """

      assert {:error, _} = compile(source, "char_type_application_misread.cure")
    end

    test "a UniverseLevel binder elaborates to an erased level-typed Core binder" do
      source = """
      mod Char.UniverseLevelAst
        fn identity({l: UniverseLevel}, {a: Type}, x: a) -> a = x
      end
      """

      assert {:ok, env} = Cure.Elab.Program.elaborate(source)
      assert %{type: {:pi, :erased, {:level_type}, _}} = Env.get_def(env, :"Char.UniverseLevelAst#identity")
    end
  end

  # ---------------------------------------------------------------------------
  # U1 — canonical level algebra (spec §6, §19.1)
  # ---------------------------------------------------------------------------

  describe "U1: canonical maximum-plus level algebra" do
    @describetag :u1

    test "closed levels are arbitrary precision, not bounded by 2" do
      do_universe_level_algebra()
    end

    defp do_universe_level_algebra do
      alias Cure.Core.UniverseLevel

      # §6.2: `max(0)` is the unique zero normal form; a closed level is a
      # constant with no atoms.
      zero = UniverseLevel.zero()
      assert UniverseLevel.equal?(zero, UniverseLevel.closed(0), nil)

      # §19.1: arbitrary-precision constants. `Type37 : Type38` must not build
      # 38 successor nodes.
      big = UniverseLevel.closed(37)
      assert UniverseLevel.equal?(UniverseLevel.succ(big), UniverseLevel.closed(38), nil)

      # §6.3: `a <= succ a`, and `a + 1 <= a` is FALSE.
      assert UniverseLevel.leq?(big, UniverseLevel.succ(big), nil)
      refute UniverseLevel.leq?(UniverseLevel.succ(big), big, nil)

      # §6.2 canonicalization: `max(a, a) = a`, `max(a, 0) = a`.
      assert UniverseLevel.equal?(UniverseLevel.max(big, big), big, nil)
      assert UniverseLevel.equal?(UniverseLevel.max(big, zero), big, nil)
    end
  end

  # ---------------------------------------------------------------------------
  # U3 — trusted sorting and cumulativity (spec §8, §19.2, §19.3)
  # ---------------------------------------------------------------------------

  describe "U3: universe formation beyond the ceiling" do
    @describetag :u3

    test "Type37 : Type38 is accepted (no ceiling)" do
      assert {:ok, {:vtype, {:finite, %LevelValue{constant: 38, atoms: []}}}} =
               Kernel.infer(Context.empty(), {:type, Sort.finite_closed(37)})
    end

    test "Type(a) is rejected at Type(a) for an open level a (no Type-in-Type)" do
      ctx = Context.extend(Context.empty(), {:vlevel_type}, :erased)
      type = {:type, Sort.finite(UniverseLevel.atom({:var, 0}))}
      assert {:ok, {:vtype, _}} = Kernel.infer(ctx, type)
      assert {:error, _} = Kernel.check(ctx, type, Eval.eval(type, Context.env(ctx)))
    end
  end

  # ---------------------------------------------------------------------------
  # U5 — standard-library polymorphism (spec §11.4)
  # ---------------------------------------------------------------------------

  describe "U5: standard families are polymorphic, not Type0 haircuts" do
    @describetag :u5

    test "the canonical Equivalent family quantifies its carrier's level" do
      assert {:ok, env} = Cure.Elab.Program.elaborate("mod GeneralizedEquivalentProbe\n  use Std.Equivalent\nend\n")
      family = Cure.Core.Inductive.get_family(env, :Equivalent)

      assert family
      assert :ok = Kernel.check_family(env, family)

      assert [
               {_level_name, {:level_type}},
               {_carrier_name, {:type, {:finite, %UniverseLevel{constant: 0, atoms: [{{:var, 0}, 0}]}}}}
             ] = family.params
    end
  end

  # ---------------------------------------------------------------------------
  # helpers
  # ---------------------------------------------------------------------------

  defp compile(source, file) do
    Cure.Compiler.compile_and_load(source, file: "universe_characterization/#{file}")
  end
end
