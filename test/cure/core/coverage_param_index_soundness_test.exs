defmodule Cure.Core.CoverageParamIndexSoundnessTest do
  @moduledoc """
  Index unification for coverage must instantiate a constructor's result indices
  at the scrutinee's actual PARAMETERS before unifying. Result indices live in the
  ctor frame `args(inner) ++ params(outer)`, so a family parameter buried in a
  result-index spine (`MkFoo : Foo a [a]`) is a de Bruijn var `≥ arity` — the same
  range a scrutinee index var shifts into. Left un-instantiated, the occurs/Cycle
  rule mistook the (distinct) param var and scrutinee var for a cyclic
  self-occurrence and verdicted `:impossible`, letting an empty `case` on an
  inhabited `Foo a i` pass coverage (ex-falso).
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Context, Env, Inductive, Kernel}

  # Foo (a : Type0) : Type0 -> Type0   with   MkFoo : Foo a (Cons a Nil)   (arity 0)
  defp env do
    fam = Inductive.family(:Foo, [{:a, {:type, 0}}], [{:i, {:type, 0}}], 0)
    # result index buries the parameter `a` (de Bruijn 0 at arity 0) in a ctor spine.
    mk =
      Inductive.ctor(:MkFoo, [], [{:ctor, :Cons, [{:var, 0}, {:ctor, :Nil, []}]}], [], [{:var, 0}])

    Inductive.declare(Env.empty(), fam, [mk])
  end

  # A context with two binders: level 0 = the parameter `a`, level 1 = the index `i`.
  defp ctx, do: Context.extend(Context.extend(Context.empty(env()), {:vtype, 0}), {:vtype, 0})

  test "MkFoo over a free index is SOLVABLE, not impossible (i := Cons(a, Nil))" do
    a_val = {:vneutral, {:nvar, 0}}
    i_val = {:vneutral, {:nvar, 1}}

    verdict = Kernel.branch_unify(ctx(), :Foo, :MkFoo, [i_val], [a_val])
    refute verdict == :impossible, "MkFoo builds Foo a [a]; it can match a free index"
    assert match?({:solved, _}, verdict) or verdict == :trivial
  end

  test "a genuine index clash is still impossible (control)" do
    # Scrutinee index fixed to `Nil` cannot equal `Cons a Nil` — really impossible.
    a_val = {:vneutral, {:nvar, 0}}
    nil_val = {:vctor, :Nil, []}

    assert :impossible == Kernel.branch_unify(ctx(), :Foo, :MkFoo, [nil_val], [a_val])
  end
end
