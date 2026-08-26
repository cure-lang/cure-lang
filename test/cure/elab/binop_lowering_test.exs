defmodule Cure.Elab.BinopLoweringTest do
  @moduledoc """
  K2 Phase 2 (spec 2026-07-09-prim-delta-globals + Amendment A1 §1-A): surface
  arithmetic/comparison operators lower to registry-keyed builtin-op GLOBAL
  spines, not `{:prim, op, args}` nodes. Comparison `==`/`!=` dispatch: the
  concrete primitive operands keep their fast paths (Bool → Std.Bool eq/ne, Int →
  int_eq/int_ne, Float → float_eq/float_ne) as optimisations of the single route,
  while an ADT operand routes through the `Equatable` typeclass — `==` dispatches
  to the coherence-registered instance method for the operand's head (whose body
  is the structural `struct_eq` spine), and `!=` to the `where`-constrained
  `Std.Equatable#!=`. There is no longer an inline `struct_eq`/`struct_ne`
  fallback in `build_binop`; the typeclass is the sole route (Task 2.6).
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Builtins, Env}
  alias Cure.Elab.{Emit, Program}

  defp seeded, do: Builtins.seed(Env.empty())

  @int2 {:pi, Cure.Core.Grade.unrestricted(), {:int_type},
         {:pi, Cure.Core.Grade.unrestricted(), {:int_type}, {:int_type}}}

  # Body of a top-level fn `name`.
  defp body(src, name) do
    {:ok, env} = Program.elaborate("mod M\n  use Std.Bool\n" <> src <> "end\n")
    Env.get_def(env, name).body
  end

  defp app2(g, a, b), do: {:app, {:app, {:global, g}, a}, b}

  # Builtin ops lower to owner-qualified globals (`Std.Builtin#int_add`), matching
  # both `Builtins.seed`'s registration key and the elaborator's emission.
  defp bop(op), do: Cure.Elab.Name.qualify("Std.Builtin", op)

  # No {:prim, _, _} node anywhere in the term.
  defp no_prim?(t) when is_tuple(t) do
    case t do
      {:prim, _, _} -> false
      _ -> t |> Tuple.to_list() |> Enum.all?(&no_prim?/1)
    end
  end

  defp no_prim?(l) when is_list(l), do: Enum.all?(l, &no_prim?/1)
  defp no_prim?(_), do: true

  test "Int `+` lowers to an int_add global spine, no prim" do
    b = body("  fn f(x: Int) -> Int = x + 1\n", :f)

    assert {:lam, Cure.Core.Grade.unrestricted(), {:data, :"Std.Int#Int", [], []},
            app2(bop(:int_add), {:var, 0}, {:int_lit, 1})} == b

    assert no_prim?(b)
  end

  test "Float `+` lowers to float_add" do
    b = body("  fn g(x: Float) -> Float = x + 1.0\n", :g)

    assert {:lam, Cure.Core.Grade.unrestricted(), {:float_type}, app2(bop(:float_add), {:var, 0}, {:float_lit, 1.0})} ==
             b

    assert no_prim?(b)
  end

  test "Int `==` lowers to int_eq (guard-position shape)" do
    b = body("  fn eq0(n: Int) -> Bool = n == 0\n", :eq0)

    assert {:lam, Cure.Core.Grade.unrestricted(), {:data, :"Std.Int#Int", [], []},
            app2(bop(:int_eq), {:var, 0}, {:int_lit, 0})} == b

    assert no_prim?(b)
  end

  test "Int `!=` lowers to int_ne; Float `==` to float_eq" do
    assert {:lam, Cure.Core.Grade.unrestricted(), {:data, :"Std.Int#Int", [], []},
            app2(bop(:int_ne), {:var, 0}, {:int_lit, 3})} ==
             body("  fn t(n: Int) -> Bool = n != 3\n", :t)

    assert {:lam, Cure.Core.Grade.unrestricted(), {:float_type}, app2(bop(:float_eq), {:var, 0}, {:float_lit, 2.0})} ==
             body("  fn u(x: Float) -> Bool = x == 2.0\n", :u)
  end

  test "ADT `==` routes through the registered Equatable instance method (sole route)" do
    b = body("  fn t(a: Nat, b: Nat) -> Bool = a == b\n", :t)
    nat = {:data, :"Std.Nat#Nat", [], []}
    eq_impl = :"Std.Equatable#__impl_Equatable_Std.Nat#Nat_=="

    assert {:lam, Cure.Core.Grade.unrestricted(), nat,
            {:lam, Cure.Core.Grade.unrestricted(), nat, app2(eq_impl, {:var, 1}, {:var, 0})}} == b

    # No inline `struct_eq` fast path in the lowered term: the structural spine
    # lives inside the instance body, reached only through the instance global.
    assert no_prim?(b)
  end

  test "ADT `!=` routes through the where-constrained Std.Equatable#!=" do
    b = body("  fn t(a: Nat, b: Nat) -> Bool = a != b\n", :t)
    nat = {:data, :"Std.Nat#Nat", [], []}
    omega = Cure.Core.Grade.unrestricted()

    # `!=` is the derived, dictionary-passing function; at a concrete operand type
    # its `where Equatable(t)` dictionary is resolved to the `Nat` instance. Assert
    # only the outer dispatch: the body applies `Std.Equatable#!=` (not any inline
    # `struct_ne`), which is the sole-route lowering for ADT inequality.
    assert {:lam, ^omega, ^nat, {:lam, ^omega, ^nat, inner}} = b

    assert refers_to?(inner, :"Std.Equatable#!=")
    refute refers_to?(inner, bop(:struct_ne))
  end

  # Does the term mention `{:global, g}` anywhere?
  defp refers_to?(t, g) when is_tuple(t) do
    case t do
      {:global, ^g} -> true
      _ -> t |> Tuple.to_list() |> Enum.any?(&refers_to?(&1, g))
    end
  end

  defp refers_to?(l, g) when is_list(l), do: Enum.any?(l, &refers_to?(&1, g))
  defp refers_to?(_, _), do: false

  test "non-numeric arithmetic still rejects (unchanged from decision 3)" do
    assert {:error, _} =
             Program.elaborate("mod M\n  use Std.Bool\n  fn t(a: Nat, b: Nat) -> Nat = a + b\nend\n")
  end

  describe "emit: first-class builtin-op globals (core-level, spec §1.5 b/c)" do
    # Surface Cure cannot name `int_add` as a value, so the bare-reference and
    # partial-spine emit paths are reachable only from hand-built Core: a lambda
    # applied to the bare global (closure application is curried, one arg at a
    # time), and to a 1-arg partial spine. Pre-retarget the generic global path
    # emits a call to a nonexistent `int_add/0` — compile error (the red).
    test "bare builtin-op global as a value runs via a curried wrapper" do
      body =
        {:app, {:lam, Cure.Core.Grade.unrestricted(), @int2, {:app, {:app, {:var, 0}, {:int_lit, 3}}, {:int_lit, 4}}},
         {:global, :int_add}}

      env = Env.add_def(seeded(), :use_bare, {:int_type}, body, [])
      {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.BopBare", functions: [:use_bare])
      assert apply(mod, :use_bare, []) == 7
    end

    test "1-arg PARTIAL builtin-op spine runs via wrapper + curried application" do
      body =
        {:app,
         {:lam, Cure.Core.Grade.unrestricted(), {:pi, Cure.Core.Grade.unrestricted(), {:int_type}, {:int_type}},
          {:app, {:var, 0}, {:int_lit, 4}}}, {:app, {:global, :int_add}, {:int_lit, 3}}}

      env = Env.add_def(seeded(), :use_partial, {:int_type}, body, [])

      {:ok, mod} =
        Emit.compile_and_load(env, module: :"Cure.BopPartial", functions: [:use_partial])

      assert apply(mod, :use_partial, []) == 7
    end
  end
end
