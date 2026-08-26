defmodule Cure.Core.NestedRedexConvTest do
  @moduledoc """
  Characterises nested-redex-scrutinee conversion (the Phase-4a gap): a stuck
  `case` must compare its SCRUTINEE up to definitional equality — forcing a
  scrutinee that is itself a certified-global redex to WHNF — not structurally.

  Reference-grounded: Lean kernel `type_checker.cpp` `is_def_eq_app` compares
  every argument of a stuck application with full `is_def_eq`; Agda
  `Conversion.hs` `compareAtom` compares blocked terms' eliminations with
  `compareElims`. Without this, `plus (plus Z y) z ≢ plus y z` even though
  `plus Z y` δι-reduces to `y` — the stuck-`++`-index crux of the FRP port.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Conv, Env, Inductive}

  @nat {:data, :Nat, [], []}
  @z {:ctor, :Z, []}
  defp s(x), do: {:ctor, :S, [x]}

  @slist {:data, :SList, [], []}
  @snil {:ctor, :SNil, []}

  # plus a b = case a of Z => b | S k => S (plus k b)   (recursion on 1st arg)
  defp plus_body do
    z_branch = {:Z, 0, {:var, 0}}
    s_branch = {:S, 1, s({:app, {:app, {:global, :plus}, {:var, 0}}, {:var, 1}})}

    {:lam, Cure.Core.Grade.unrestricted(), @nat,
     {:lam, Cure.Core.Grade.unrestricted(), @nat,
      {:case, {:var, 1}, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}, [z_branch, s_branch]}}}
  end

  # app xs ys = case xs of SNil => ys | SCons x r => SCons x (app r ys)
  defp app_body do
    nil_branch = {:SNil, 0, {:var, 0}}

    cons_branch =
      {:SCons, 2, {:ctor, :SCons, [{:var, 1}, {:app, {:app, {:global, :append}, {:var, 0}}, {:var, 2}}]}}

    {:lam, Cure.Core.Grade.unrestricted(), @slist,
     {:lam, Cure.Core.Grade.unrestricted(), @slist,
      {:case, {:var, 1}, {:lam, Cure.Core.Grade.unrestricted(), @slist, @slist}, [nil_branch, cons_branch]}}}
  end

  defp env do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Nat, [], [], 0), [
      Inductive.ctor(:Z, [], []),
      Inductive.ctor(:S, [{:n, @nat}], [])
    ])
    |> Inductive.declare(Inductive.family(:SList, [], [], 0), [
      Inductive.ctor(:SNil, [], []),
      Inductive.ctor(:SCons, [{:x, @nat}, {:r, @slist}], [])
    ])
    |> Env.add_def(
      :plus,
      {:pi, Cure.Core.Grade.unrestricted(), @nat, {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}},
      plus_body()
    )
    |> Env.certify(:plus)
    |> Env.add_def(
      :append,
      {:pi, Cure.Core.Grade.unrestricted(), @slist, {:pi, Cure.Core.Grade.unrestricted(), @slist, @slist}},
      app_body()
    )
    |> Env.certify(:append)
  end

  defp plus(a, b), do: {:app, {:app, {:global, :plus}, a}, b}
  defp append(a, b), do: {:app, {:app, {:global, :append}, a}, b}

  # Two distinct neutral variables y (var 1) and z (var 0).
  @conv_env [{:vneutral, {:nvar, 1}}, {:vneutral, {:nvar, 0}}]
  @depth 2
  @y {:var, 1}
  @zz {:var, 0}

  test "conv decides plus (plus Z y) z ≡ plus y z (nested redex scrutinee)" do
    assert Conv.conv?(plus(plus(@z, @y), @zz), plus(@y, @zz), @conv_env, @depth, env())
  end

  test "conv decides append (append SNil y) z ≡ append y z (the ++ crux)" do
    assert Conv.conv?(append(append(@snil, @y), @zz), append(@y, @zz), @conv_env, @depth, env())
  end

  test "conv decides the flipped orientation too" do
    assert Conv.conv?(plus(@y, @zz), plus(plus(@z, @y), @zz), @conv_env, @depth, env())
  end

  test "stuck cases over genuinely distinct neutral scrutinees stay distinct" do
    refute Conv.conv?(plus(@y, @zz), plus(@zz, @zz), @conv_env, @depth, env())
    refute Conv.conv?(plus(plus(@z, @y), @zz), plus(@zz, @zz), @conv_env, @depth, env())
  end

  test "reduction only fires under δ: without a signature the comparison stays structural" do
    refute Conv.conv?(plus(plus(@z, @y), @zz), plus(@y, @zz), @conv_env, @depth, nil)
  end
end
