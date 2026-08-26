defmodule Cure.Core.PositivityNestedTest do
  @moduledoc """
  Nested / mutual strict positivity (Agda `Positivity.hs`, Coq's
  "check the instantiated constructors" rule, Idris `Positivity.idr`).

  A family may occur inside ANOTHER family's parameter argument
  (`Node (List Rose)`, `Yield (Option (IterStep a))`) — but only when that other
  family uses the parameter STRICTLY POSITIVELY. The old checker blanket-rejected
  every occurrence of the family in another family's arguments
  (`inductive.ex` `strictly_positive?`, the `:data`-other clause), which is sound
  but rejects genuinely-positive nested types the stdlib needs (`Std.Json.Value`'s
  `Array(List(Value))`, `Std.Iter`'s mutual `Iter`/`IterStep`).

  The fix instantiates the other family's constructor fields with the ACTUAL
  arguments and re-checks positivity: a positive parameter (`List`, `Option`)
  keeps the family positive; a negative parameter (`Neg t = t -> Empty`) drops it
  left of an arrow and is still rejected. A constructorless / opaque carrier has
  unknowable polarity and is conservatively rejected.

  These tests build Core families directly (de Bruijn), independent of the
  elaborator: params are the OUTERMOST binders, so at ctor-field position `i` the
  family's single parameter is `{:var, i}` (mirrors the built-in `List` `Cons:
  [_a0: {:var,0}, _a1: {:data,:List,[var: 1],[]}]`).
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive}

  @empty {:data, :Empty, [], []}

  # Lst(a) = LNil | LCons(a, Lst(a)) — a genuinely positive parametric list.
  defp with_lst(env) do
    Inductive.declare(env, Inductive.family(:Lst, [a: {:type, 0}], [], 0), [
      Inductive.ctor(:LNil, [], []),
      Inductive.ctor(
        :LCons,
        [{:x, {:var, 0}}, {:xs, {:data, :Lst, [{:var, 1}], []}}],
        []
      )
    ])
  end

  defp base do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Empty, [], [], 0), [])
    |> with_lst()
  end

  test "a family nested in a POSITIVE parameter of another family is accepted (Rose = Node(Lst(Rose)))" do
    # Rose(a) = RNode(Lst(Rose(a))): Rose occurs inside Lst's (positive) param.
    rose_a = {:data, :Rose, [{:var, 0}], []}

    env =
      Inductive.declare(base(), Inductive.family(:Rose, [a: {:type, 0}], [], 0), [
        Inductive.ctor(:RNode, [{:t, {:data, :Lst, [rose_a], []}}], [])
      ])

    assert :ok == Inductive.positive?(env, Inductive.get_family(env, :Rose))
  end

  test "a NEGATIVE nested occurrence is still rejected (Bad = MkBad(Neg(Bad)), Neg t = MkNeg(t -> Empty))" do
    # Neg uses its parameter to the LEFT of an arrow, so nesting Bad through it
    # is the classic paradox constructor and MUST be rejected.
    env =
      base()
      |> Inductive.declare(Inductive.family(:Neg, [t: {:type, 0}], [], 0), [
        Inductive.ctor(:MkNeg, [{:f, {:pi, Cure.Core.Grade.unrestricted(), {:var, 0}, @empty}}], [])
      ])
      |> Inductive.declare(Inductive.family(:Bad, [], [], 0), [
        Inductive.ctor(:MkBad, [{:g, {:data, :Neg, [{:data, :Bad, [], []}], []}}], [])
      ])

    assert {:error, {:non_strictly_positive, :MkBad}} ==
             Inductive.positive?(env, Inductive.get_family(env, :Bad))
  end

  test "a family nested in a CONSTRUCTORLESS carrier's parameter is conservatively rejected" do
    # Box has a parameter but no constructors, so its polarity is unknowable —
    # the checker cannot issue a positive certificate.
    env =
      base()
      |> Inductive.declare(Inductive.family(:Box, [a: {:type, 0}], [], 0), [])
      |> Inductive.declare(Inductive.family(:Foo, [], [], 0), [
        Inductive.ctor(:MkFoo, [{:b, {:data, :Box, [{:data, :Foo, [], []}], []}}], [])
      ])

    assert {:error, {:non_strictly_positive, :MkFoo}} ==
             Inductive.positive?(env, Inductive.get_family(env, :Foo))
  end

  test "mutual recursion through a positive parameter is accepted (Iter/IterStep via Option)" do
    # Option(a) = ONone | OSome(a)  — positive parameter.
    # Iter(a)     = MkIter(Tok -> Option(IterStep(a)))
    # IterStep(a) = Yield(a, Iter(a))
    # IterStep occurs nested in Option (positive) in Iter's field, and Iter
    # occurs recursively in IterStep — the shape of `Std.Iter`.
    iterstep_a = {:data, :IterStep, [{:var, 0}], []}
    iter_a = {:data, :Iter, [{:var, 1}], []}

    env =
      base()
      |> Inductive.declare(Inductive.family(:Tok, [], [], 0), [Inductive.ctor(:MkTok, [], [])])
      |> Inductive.declare(Inductive.family(:Option, [a: {:type, 0}], [], 0), [
        Inductive.ctor(:ONone, [], []),
        Inductive.ctor(:OSome, [{:v, {:var, 0}}], [])
      ])
      |> Inductive.declare(Inductive.family(:Iter, [a: {:type, 0}], [], 0), [
        Inductive.ctor(
          :MkIter,
          [{:f, {:pi, Cure.Core.Grade.unrestricted(), {:data, :Tok, [], []}, {:data, :Option, [iterstep_a], []}}}],
          []
        )
      ])
      |> Inductive.declare(Inductive.family(:IterStep, [a: {:type, 0}], [], 0), [
        Inductive.ctor(:Yield, [{:hd, {:var, 0}}, {:tl, iter_a}], [])
      ])

    assert :ok == Inductive.positive?(env, Inductive.get_family(env, :IterStep))
    assert :ok == Inductive.positive?(env, Inductive.get_family(env, :Iter))
  end
end
