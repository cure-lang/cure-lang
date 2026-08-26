defmodule Cure.Elab.GoalSolvedLambdaDomainTest do
  @moduledoc """
  A function's implicit TYPE parameters, once solved from the concrete
  return-type GOAL, must be propagated *before* its lambda arguments are
  elaborated — so an inline getter lambda like `fn(x) -> x.1`, whose domain is
  fixed ONLY by that goal, receives a concrete (tuple) domain and its `.i`
  projection lowers.

  `mk(fn(x) -> x.1) : Box(Tuple(Int,Int), Int)` failed with
  `:unsupported_expression`: the implicit `s`/`a` of
  `mk : {s} -> {a} -> (s -> a) -> Box(s,a)` were left as metavariables while the
  lambda argument was elaborated, so `x : ?s` was not known to be a tuple and
  `x.1` had no projection to lower. When no *later* argument constrains the
  implicit (both siblings are unannotated lambdas, or there is only one), the
  cross-argument deferral path (`cross_arg_implicit_test`) cannot rescue it — the
  domain stays a metavar to the end. The bidirectional applicator now seeds
  implicit solving from any concrete goal (not only union goals) by unifying the
  codomain against it first, which is ordinary bidirectional propagation
  (Idris/Agda/Lean). This is the surface that lets optic getters be written
  inline (`lens(fn(x) -> x.1, …)`) instead of as named helper functions.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Emit}

  @pre "mod M\n" <>
         "  type Box(s: Type, a: Type) = MkBox((s) -> a)\n" <>
         "  fn mk({s: Type}, {a: Type}, get: (s) -> a) -> Box(s, a) = MkBox(get)\n" <>
         "  fn run({s: Type}, {a: Type}, b: Box(s, a), x: s) -> a = match b\n" <>
         "    MkBox(f) -> f(x)\n"

  test "a projection getter lambda lowers when the goal solves its domain" do
    src =
      @pre <>
        "  fn box() -> Box(Tuple(Int, Int), Int) = mk(fn(x) -> x.1)\n" <>
        "  fn fst() -> Int = run(box(), %[7, 8])\nend\n"

    {:ok, env} = Program.elaborate(src)

    {:ok, mod} =
      Emit.compile_and_load(env, module: :"Cure.GoalLam1", functions: [:mk, :run, :box, :fst])

    assert apply(mod, :fst, []) == 7
  end

  test "an identity lambda lowers when the goal solves its domain" do
    src =
      @pre <>
        "  fn idbox() -> Box(Int, Int) = mk(fn(x) -> x)\n" <>
        "  fn go() -> Int = run(idbox(), 42)\nend\n"

    {:ok, env} = Program.elaborate(src)

    {:ok, mod} =
      Emit.compile_and_load(env, module: :"Cure.GoalLam2", functions: [:mk, :run, :idbox, :go])

    assert apply(mod, :go, []) == 42
  end
end
