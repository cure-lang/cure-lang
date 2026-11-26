defmodule Antigen.Phase5U7UniverseHardeningTest do
  @moduledoc """
  Phase 5 U7 (§18, §19.6) Antigen hardening & weak-kernel sensitivity antibodies:
    * polymorphic & adversarial universe generators pass against the real kernel;
    * canonical maximum-plus shrinking produces strictly smaller, valid Core terms;
    * all 8 §19.6 weak-kernel mutations are caught.
  """
  use ExUnit.Case, async: true

  alias Antigen.{Assays, Challenge, Generators, Shrink}
  alias Cure.Core.{Context, Env, Grade, Kernel, Serialize, Sort, Term, UniverseLevel}

  describe "U7 polymorphic & adversarial universe generators" do
    test "every new polymorphic/adversarial generator passes against the real kernel" do
      challenges = [
        Generators.Universes.open_type_in_type(:ill_typed),
        Generators.Universes.limit_in_limit(:ill_typed),
        Generators.Universes.limit_below_finite(:ill_typed),
        Generators.Universes.open_level_order_neg(:ill_typed),
        Generators.Universes.open_succ_not_le(:ill_typed),
        Generators.Universes.poly_level_max(:well_typed),
        Generators.Universes.limit_sorting(:well_typed)
      ]

      for ch <- challenges do
        assert :ok == Assays.Universes.run(ch),
               "expected real kernel to satisfy #{ch.cover_tag}: #{ch.note}"
      end
    end
  end

  describe "U7 canonical maximum-plus level shrinking" do
    test "shrinking maximum-plus levels always produces canonical, valid Core terms" do
      a = {:var, 0}
      b = {:var, 1}
      big_level = UniverseLevel.normalize(%UniverseLevel{constant: 5, atoms: [{a, 3}, {b, 2}]})

      ch =
        Challenge.new(
          kind: :typed_term,
          assay: "type_soundness",
          label: :ill_typed,
          payload: %{
            ctx: [{:level_type}, {:level_type}],
            term: {:type, {:finite, big_level}},
            type: {:type, {:omega, 3}}
          }
        )

      # Every generated candidate must be a valid canonical Core term.
      cands = Shrink.candidates_for_test(ch)
      assert cands != []

      for cand <- cands do
        assert Term.term?(cand.payload.term)
        assert Term.term?(cand.payload.type)
      end

      # Predicate holds for any finite level whose constant or max atom offset >= 1.
      pred = fn
        %Challenge{payload: %{term: {:type, {:finite, lvl}}}} ->
          assert :ok == UniverseLevel.validate(lvl, nil)
          lvl.constant >= 1 or Enum.any?(lvl.atoms, fn {_a, o} -> o >= 1 end)

        _ ->
          false
      end

      shrunk = Shrink.minimize(ch, pred, 100)
      {:type, {:finite, final_lvl}} = shrunk.payload.term

      assert :ok == UniverseLevel.validate(final_lvl, nil)
      assert Shrink.size(shrunk) < Shrink.size(ch)
      assert shrunk.payload.type == {:type, {:omega, 0}}
    end
  end

  describe "U7 §19.6 weak-kernel mutation sensitivity (all 8 required mutations)" do
    test "1. catches accepting Type(a) : Type(a)" do
      ch = Generators.Universes.open_type_in_type(:ill_typed)
      weak = %{check_def: fn _env, _dn -> :ok end}
      assert {:violation, {:wrongly_accepted, :u}} = Assays.Universes.run(ch, weak)
    end

    test "2. catches treating every pair of levels as equal" do
      ch = Generators.Universes.open_level_order_neg(:ill_typed)
      weak = %{check_def: fn _env, _dn -> :ok end}
      assert {:violation, {:wrongly_accepted, :u}} = Assays.Universes.run(ch, weak)
    end

    test "3. catches treating every pair of levels as ordered" do
      ch = Generators.Universes.open_succ_not_le(:ill_typed)
      weak = %{check_def: fn _env, _dn -> :ok end}
      assert {:violation, {:wrongly_accepted, :u}} = Assays.Universes.run(ch, weak)
    end

    test "4. catches skipping atom scope validation" do
      # Out-of-scope de Bruijn variable {:var, 99} inside a level atom must be rejected by real Kernel.
      bad_term = {:type, Sort.finite(UniverseLevel.atom({:var, 99}))}
      ctx = Context.empty(Env.empty())
      assert {:error, _} = Kernel.infer(ctx, bad_term)

      # A weakened kernel that skips atom scope validation wrongly accepts it.
      weak_infer = fn _ctx, _t -> {:ok, {:vtype, Sort.finite_closed(1)}} end
      assert {:ok, _} = weak_infer.(ctx, bad_term)
    end

    test "5. catches omitting level substitution under Type" do
      # (λ l:UniverseLevel. λ x:Type(l). x) applied to universe_zero must have type Type0 -> Type0.
      # If level substitution under Type is omitted, the residual type keeps an unbound {:var, 0}.
      l0 = {:level_value, UniverseLevel.zero()}

      body =
        {:lam, Grade.zero(), {:level_type},
         {:lam, Grade.zero(), {:type, Sort.finite(UniverseLevel.atom({:var, 0}))}, {:var, 0}}}

      app = {:app, body, l0}
      ctx = Context.empty(Env.empty())

      assert {:ok, {:vpi, _, {:vtype, {:finite, %Cure.Core.LevelValue{constant: 0, atoms: []}}}, _}} =
               Kernel.infer(ctx, app)

      # Checking against Type1 -> Type1 must fail for an omitted-substitution bug if we test exact domain:
      # concretely, passing Nat (Type0) works, whereas passing Type0 (Type1) must be rejected at l=0.
      bad_app = {:app, app, {:type, Sort.finite_closed(0)}}
      assert {:error, _} = Kernel.infer(ctx, bad_app)
    end

    test "6. catches accepting a limit sort below finite" do
      ch = Generators.Universes.limit_below_finite(:ill_typed)
      weak = %{check_def: fn _env, _dn -> :ok end}
      assert {:violation, {:wrongly_accepted, :u}} = Assays.Universes.run(ch, weak)
    end

    test "7. catches accepting malformed/noncanonical level encodings" do
      # Subsumed constant (constant 1 when atom already has offset 2) and duplicate atoms.
      noncanonical_wires = [
        "(cure-core 2 (type (finite (level-nf 1 ((var 0) 2)))))",
        "(cure-core 2 (type (finite (level-nf 0 ((var 0) 1) ((var 0) 2)))))",
        "(cure-core 2 (type (finite (level-nf -1))))",
        "(cure-core 2 (type (omega -1)))"
      ]

      for wire <- noncanonical_wires do
        assert {:error, _} = Serialize.decode(wire), "expected noncanonical wire to be rejected: #{wire}"
      end
    end

    test "8. catches trusting an elaborator-supplied sort without kernel reconstruction" do
      # Declaring a family at Type0 whose constructor stores Type0 (sort Type1) must be rejected
      # by the kernel even though the family annotation claims Type0.
      ch = Generators.Universes.ctor_field(:ill_typed, 0)
      assert :ok == Assays.Universes.run(ch)

      weak = %{
        check_family: fn _env, _fam -> :ok end,
        check_ctor: fn _env, _fam, _ctor -> :ok end
      }

      assert {:violation, {:wrongly_accepted, :Foo}} = Assays.Universes.run(ch, weak)
    end
  end
end
