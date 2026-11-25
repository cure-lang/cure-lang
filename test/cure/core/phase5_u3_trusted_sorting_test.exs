defmodule Cure.Core.Phase5U3TrustedSortingTest do
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Env, Eval, Grade, Inductive, Kernel, LevelValue, Sort, UniverseLevel}

  defp finite(level), do: {:type, Sort.finite(level)}
  defp finite_closed(n), do: {:type, Sort.finite_closed(n)}
  defp omega(n), do: {:type, Sort.omega(n)}
  defp atom(term), do: UniverseLevel.atom(term)

  describe "U3 §19.2 kernel positives" do
    test "Type(a) : Type(universe_succ(a)) for open level variable a" do
      ctx = Context.extend(Context.empty(), {:vlevel_type}, :erased)
      a = atom({:var, 0})
      expected_sort = Sort.finite(UniverseLevel.succ(a))

      assert {:ok, inferred} = Kernel.infer(ctx, finite(a))
      assert :ok = Kernel.check(ctx, finite(a), Eval.eval({:type, expected_sort}, Context.env(ctx)))
      assert {:vtype, {:finite, %LevelValue{constant: 0, atoms: [{_, 1}]}}} = inferred
    end

    test "Type37 : Type38 without constructing 38 successor nodes" do
      assert {:ok, {:vtype, {:finite, %LevelValue{constant: 38, atoms: []}}}} =
               Kernel.infer(Context.empty(), finite_closed(37))
    end

    test "A : Type(a) is accepted at Type(universe_max(a, b)) by cumulativity" do
      ctx =
        Context.empty()
        |> Context.extend({:vlevel_type}, :erased)
        |> Context.extend({:vlevel_type}, :erased)

      # var 1 = a, var 0 = b
      a = atom({:var, 1})
      ctx_with_type = Context.extend(ctx, Eval.eval(finite(a), Context.env(ctx)), :erased)

      # var 2 = a, var 1 = b, var 0 = A : Type(a)
      max_ab = UniverseLevel.max(atom({:var, 2}), atom({:var, 1}))
      assert :ok = Kernel.check(ctx_with_type, {:var, 0}, Eval.eval(finite(max_ab), Context.env(ctx_with_type)))
    end

    test "Pi(A : Type(a)). Type(b) is sorted at Type(max(succ(a), succ(b)))" do
      ctx =
        Context.empty()
        |> Context.extend({:vlevel_type}, :erased)
        |> Context.extend({:vlevel_type}, :erased)

      # var 1 = a, var 0 = b
      pi = {:pi, :erased, finite(atom({:var, 1})), finite(atom({:var, 1}))}
      # Under binder A: var 2 = a, var 1 = b. So domain is Type(a) : Type(succ a), codomain is Type(b) : Type(succ b).
      expected_level = UniverseLevel.max(UniverseLevel.succ(atom({:var, 1})), UniverseLevel.succ(atom({:var, 0})))

      assert :ok = Kernel.check(ctx, pi, Eval.eval(finite(expected_level), Context.env(ctx)))
    end

    test "(l : UniverseLevel) -> Type(l) is sorted at TypeLimit (omega 0)" do
      pi = {:pi, :erased, {:level_type}, finite(atom({:var, 0}))}
      assert {:ok, {:vtype, {:omega, 0}}} = Kernel.infer(Context.empty(), pi)
      assert :ok = Kernel.check(Context.empty(), pi, Eval.eval(omega(0), []))
    end

    test "finite sorts are accepted below every TypeLimitN, and limit cumulativity holds by closed index" do
      ctx = Context.extend(Context.empty(), {:vlevel_type}, :erased)
      a = atom({:var, 0})

      for n <- [0, 1, 5] do
        assert :ok = Kernel.check(ctx, finite(a), Eval.eval(omega(n), Context.env(ctx)))
        assert :ok = Kernel.check(ctx, finite_closed(37), Eval.eval(omega(n), Context.env(ctx)))
      end

      assert :ok = Kernel.check(Context.empty(), omega(0), Eval.eval(omega(1), []))
      assert :ok = Kernel.check(Context.empty(), omega(0), Eval.eval(omega(5), []))
    end
  end

  describe "U3 §19.3 kernel negatives (antibodies)" do
    test "Type(a) is rejected at Type(a) and TypeLimitN is rejected at itself" do
      ctx = Context.extend(Context.empty(), {:vlevel_type}, :erased)
      a = atom({:var, 0})

      assert {:error, _} = Kernel.check(ctx, finite(a), Eval.eval(finite(a), Context.env(ctx)))

      for n <- [0, 1, 5] do
        assert {:error, _} = Kernel.check(Context.empty(), omega(n), Eval.eval(omega(n), []))
      end
    end

    test "TypeLimitN is rejected below every finite sort" do
      ctx = Context.extend(Context.empty(), {:vlevel_type}, :erased)
      a = atom({:var, 0})

      assert {:error, _} = Kernel.check(ctx, omega(0), Eval.eval(finite_closed(0), Context.env(ctx)))
      assert {:error, _} = Kernel.check(ctx, omega(0), Eval.eval(finite_closed(37), Context.env(ctx)))
      assert {:error, _} = Kernel.check(ctx, omega(0), Eval.eval(finite(a), Context.env(ctx)))
    end

    test "unrelated open levels do not compare and a + 1 <= a is rejected" do
      ctx =
        Context.empty()
        |> Context.extend({:vlevel_type}, :erased)
        |> Context.extend({:vlevel_type}, :erased)

      a = atom({:var, 1})

      ctx_a = Context.extend(ctx, Eval.eval(finite(a), Context.env(ctx)), :erased)
      # var 2 = a, var 1 = b, var 0 = A : Type(a)
      assert {:error, _} = Kernel.check(ctx_a, {:var, 0}, Eval.eval(finite(atom({:var, 1})), Context.env(ctx_a)))

      ctx_succ = Context.extend(ctx, Eval.eval(finite(UniverseLevel.succ(a)), Context.env(ctx)), :erased)
      # var 2 = a, var 0 = A : Type(succ a) must NOT check at Type(a)
      assert {:error, _} =
               Kernel.check(ctx_succ, {:var, 0}, Eval.eval(finite(atom({:var, 2})), Context.env(ctx_succ)))
    end

    test "non-UniverseLevel term and out-of-scope atom are rejected as Type index" do
      ctx_int = Context.extend(Context.empty(), {:vint_type}, Grade.unrestricted())
      assert {:error, _} = Kernel.infer(ctx_int, finite(atom({:var, 0})))
      assert {:error, _} = Kernel.infer(Context.empty(), finite(atom({:var, 0})))
    end

    test "constructor field whose sort exceeds the family sort is rejected" do
      env =
        Env.empty()
        |> Inductive.declare(
          Inductive.family(:Small, [], [], Sort.finite_closed(0)),
          [Inductive.ctor(:MkSmall, [{:t, finite_closed(0)}], [])]
        )

      family = Inductive.get_family(env, :Small)
      ctor = Inductive.get_ctor(env, :MkSmall)
      assert {:error, :universe_level} = Kernel.check_ctor(env, family, ctor)
    end

    test "uncertified function in a level atom never unfolds during conversion" do
      env =
        Env.empty()
        |> Env.add_def(:uncert_zero, {:level_type}, {:level_value, UniverseLevel.zero()}, [])

      ctx = Context.empty(env)
      t1 = finite(atom({:global, :uncert_zero}))
      t2 = finite_closed(0)

      assert {:ok, _} = Kernel.infer(ctx, t1)
      refute Cure.Core.Conv.conv?(t1, t2, [], 0, env)
    end
  end
end
