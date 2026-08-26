defmodule Cure.Core.BuiltinOpTest do
  @moduledoc """
  Task #15 / K2 wave (spec 2026-07-09-prim-delta-globals): primitive arithmetic
  as registry-keyed builtin-op GLOBALS with literal acceleration in the
  certified-δ engine (Lean reduce_nat / Idris Builtin-op analog). §G.1 rules
  preserved: partial ops stay neutral; open spines stay stuck (congruence).
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Builtins, Context, Conv, Env, Kernel, Normalise}

  defp env, do: Builtins.seed(Env.empty())
  defp ctx, do: Context.empty(env())

  defp app2(g, a, b), do: {:app, {:app, {:global, g}, a}, b}
  defp app3(g, ty, a, b), do: {:app, app2(g, ty, a), b}

  test "int_add types as an ordinary global Pi" do
    assert {:ok, {:vpi, _g, _, _}} = Kernel.infer(ctx(), {:global, :int_add})
  end

  # NB Normalise.nf/3 returns a reified TERM, not a value (normalise.ex:36-44;
  # precedent: stuck_elim_delta_test.exs:56, sig_menu_test.exs:24).
  test "saturated literal spine folds under certified delta: 3 + 5 => 8" do
    t = Normalise.nf(ctx(), app2(:int_add, {:int_lit, 3}, {:int_lit, 5}), delta: :certified)
    assert {:int_lit, 8} = t
  end

  test "comparison folds to the inductive Bool ctor" do
    t = Normalise.nf(ctx(), app2(:int_lt, {:int_lit, 1}, {:int_lit, 2}), delta: :certified)
    assert {:ctor, :"Std.Bool#True", []} = t
  end

  test "G.1 rule 1: div/rem by literal zero stays neutral (never crashes)" do
    for g <- [:int_div, :int_rem] do
      t = Normalise.nf(ctx(), app2(g, {:int_lit, 7}, {:int_lit, 0}), delta: :certified)
      assert app2(g, {:int_lit, 7}, {:int_lit, 0}) == t
    end
  end

  test "open spine stays stuck; conversion is spine congruence" do
    # under a binder: int_add x 1 vs int_add x 1 convertible; vs int_add x 2 not.
    # Conv.conv?/5 is conv?(t1, t2, value_env, depth, sig) — conv.ex:47-51,
    # precedent stuck_elim_delta_test.exs:72.
    ctx1 = Context.extend(ctx(), {:vdata, :"Std.Int#Int", []})
    t1 = app2(:int_add, {:var, 0}, {:int_lit, 1})
    t2 = app2(:int_add, {:var, 0}, {:int_lit, 2})
    assert {:ok, {:vdata, :"Std.Int#Int", []}} = Kernel.infer(ctx1, t1)
    assert t1 == Normalise.nf(ctx1, t1, delta: :certified)
    venv = Context.env(ctx1)
    refute Conv.conv?(t1, t2, venv, 1, env())
    assert Conv.conv?(t1, t1, venv, 1, env())
  end

  test "R1 pin: a user-registered int_add with its OWN body is never builtin-folded" do
    # Register int_add as an ORDINARY def (constant-42 body) in a NON-seeded env:
    # the builtin marker comes only from Builtins.seed, so this def has none.
    # Env.certify/2 accepts it (closed lam body — inductive.ex:68-82).
    ty =
      {:pi, Cure.Core.Grade.unrestricted(), {:int_type},
       {:pi, Cure.Core.Grade.unrestricted(), {:int_type}, {:int_type}}}

    body =
      {:lam, Cure.Core.Grade.unrestricted(), {:int_type},
       {:lam, Cure.Core.Grade.unrestricted(), {:int_type}, {:int_lit, 42}}}

    env = Env.empty() |> Env.add_def(:int_add, ty, body) |> Env.certify(:int_add)
    ctx = Context.empty(env)
    t = Normalise.nf(ctx, app2(:int_add, {:int_lit, 3}, {:int_lit, 5}), delta: :certified)
    assert {:int_lit, 42} = t
  end

  # Amendment A1 (spec §1-A): polymorphic structural equality globals. Verbatim
  # semantics of the retiring `{:prim, :eq/:ne}`: folds IFF both VALUE args whnf
  # to int/float literals (late-instantiated polymorphic operands); NEUTRAL on
  # everything else (ADT equality stays kernel-neutral — R8c). Type arg ignored.
  describe "Amendment A1: struct_eq/struct_ne" do
    test "struct_eq types as a global Pi" do
      assert {:ok, {:vpi, _g, _, _}} = Kernel.infer(ctx(), {:global, :struct_eq})
    end

    test "struct_eq folds on two int literals (polymorphic instantiation)" do
      t =
        Normalise.nf(ctx(), app3(:struct_eq, {:int_type}, {:int_lit, 3}, {:int_lit, 3}), delta: :certified)

      assert {:ctor, :"Std.Bool#True", []} = t

      t2 =
        Normalise.nf(ctx(), app3(:struct_ne, {:int_type}, {:int_lit, 3}, {:int_lit, 4}), delta: :certified)

      assert {:ctor, :"Std.Bool#True", []} = t2
    end

    test "struct_eq and struct_ne fold on Atom literals" do
      assert {:ctor, :"Std.Bool#True", []} =
               Normalise.nf(
                 ctx(),
                 app3(:struct_eq, {:atom_type}, {:atom_lit, :node}, {:atom_lit, :node}),
                 delta: :certified
               )

      assert {:ctor, :"Std.Bool#False", []} =
               Normalise.nf(
                 ctx(),
                 app3(:struct_eq, {:atom_type}, {:atom_lit, :node}, {:atom_lit, :leaf}),
                 delta: :certified
               )

      assert {:ctor, :"Std.Bool#True", []} =
               Normalise.nf(
                 ctx(),
                 app3(:struct_ne, {:atom_type}, {:atom_lit, :node}, {:atom_lit, :leaf}),
                 delta: :certified
               )
    end

    test "Atom equality remains neutral for open and cross-kind values" do
      ctx = Context.extend(ctx(), {:vatom_type})
      open = app3(:struct_eq, {:atom_type}, {:var, 0}, {:atom_lit, :node})

      assert ^open = Normalise.nf(ctx, open, delta: :certified)

      mixed = app3(:struct_eq, {:atom_type}, {:atom_lit, :node}, {:int_lit, 1})
      assert ^mixed = Normalise.nf(ctx(), mixed, delta: :certified)
    end

    test "struct_eq stays NEUTRAL on constructor args (ADT equality never computes in-kernel)" do
      spine = app3(:struct_eq, {:data, :"Std.Nat#Nat", [], []}, {:ctor, :"Std.Nat#Z", []}, {:ctor, :"Std.Nat#Z", []})
      assert spine == Normalise.nf(ctx(), spine, delta: :certified)
    end

    test "R1 pin: a user-registered struct_eq with its OWN body is never builtin-folded" do
      ty =
        {:pi, Cure.Core.Grade.unrestricted(), {:int_type},
         {:pi, Cure.Core.Grade.unrestricted(), {:int_type}, {:int_type}}}

      body =
        {:lam, Cure.Core.Grade.unrestricted(), {:int_type},
         {:lam, Cure.Core.Grade.unrestricted(), {:int_type}, {:int_lit, 42}}}

      env = Env.empty() |> Env.add_def(:struct_eq, ty, body) |> Env.certify(:struct_eq)
      ctx = Context.empty(env)
      t = Normalise.nf(ctx, app2(:struct_eq, {:int_lit, 3}, {:int_lit, 5}), delta: :certified)
      assert {:int_lit, 42} = t
    end
  end

  test "R4 guard: check_def/validate_certificate accept a builtin-op def without touching its nil body" do
    # Spec §1.2's ordering protects the normalise path only. check_def
    # (kernel.ex:310-323) matches %{type:, body:} and would call
    # check(ctx, nil, _) → infer has NO nil clause → crash. Reachable via
    # TotalityClosure.certify_type_level once builtin-op spines appear in TYPE
    # positions (post-Phase-2 dependent-index arithmetic). Behavioral pin: both
    # entries succeed on a seeded op.
    assert :ok = Kernel.check_def(env(), :int_add)
    assert {:ok, env2} = Kernel.validate_builtin_certificate(env(), :int_add)
    assert Env.certified?(env2, :int_add)
  end
end
