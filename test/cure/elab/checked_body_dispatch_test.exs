defmodule Cure.Elab.CheckedBodyDispatchTest do
  @moduledoc """
  Wave 4: `:list` and `:pickup` function-body / match-arm-body nodes reach CHECKED
  elaboration (receive the declared return type), so a bare `[]` body / `[] -> []`
  arm / `:pickup`-with-`[]`-then-branch pins its element type from the goal instead
  of failing with `{:unsolved_metavariables, :Nil}`. Elaborator-only; closes the
  third-dispatch-layer gap ledgered since Wave 1.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  test "a bare [] top-level body elaborates + runs" do
    src = "mod M\n  fn e() -> List(Int) = []\nend\n"
    assert {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.CBD1", functions: [:e])
    assert apply(mod, :e, []) == []
  end

  test "a [] -> [] arm body elaborates + runs" do
    src =
      "mod M\n  fn f(xs: List(Int)) -> List(Int) =\n" <>
        "    match xs\n      [] -> []\n      [h | t] -> t\nend\n"

    assert {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.CBD2", functions: [:f])
    assert apply(mod, :f, [[]]) == []
    assert apply(mod, :f, [[1, 2, 3]]) == [2, 3]
  end

  test "a :pickup body with a bare-[] then-branch elaborates + runs (take shape)" do
    src =
      "mod M\n  fn g(n: Int) -> List(Int) =\n" <>
        "    pickup\n      n <= 0 -> []\n      else -> [n]\nend\n"

    assert {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.CBD3", functions: [:g])
    assert apply(mod, :g, [0]) == []
    assert apply(mod, :g, [5]) == [5]
  end

  test "REGRESSION GUARD — head-bearing list body + inferrable pickup still work" do
    src =
      "mod M\n  fn h(x: Int, t: List(Int)) -> List(Int) = [x | t]\n" <>
        "  fn p(xs: List(Int)) -> List(Int) =\n" <>
        "    pickup\n      true -> xs\n      else -> xs\nend\n"

    assert {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.CBD4", functions: [:h, :p])
    assert apply(mod, :h, [1, [2, 3]]) == [1, 2, 3]
    assert apply(mod, :p, [[9]]) == [9]
  end

  test "Std.List smoke — a real previously-blocked function (tail) elaborates + runs" do
    # Verbatim tail/2 shape from lib/std/list.cure (its `[] -> []` arm was the
    # blocker). tail is at list.cure:72; copied here with Nat elements.
    src =
      @nat <>
        "  fn tail(xs: List(Nat)) -> List(Nat) =\n" <>
        "    match xs\n      [] -> []\n      [h | t] -> t\nend\n"

    assert {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.CBD5", functions: [:tail])
    assert apply(mod, :tail, [[]]) == []
    assert apply(mod, :tail, [[:Z, :Z]]) == [:Z]
  end

  test "a ctor-arm body with an unannotated lambda in a type-var-domain field elaborates + runs" do
    # The Std.Optic shape (optic.cure:165, `MkAffineRep(Some(MkLensRep(v, fn(new) ->
    # put(new)(x))))`): a match arm returns a constructor whose field is an arrow
    # `(a) -> a` over a TYPE VARIABLE, filled by an unannotated lambda. Inference
    # cannot type such a lambda (its domain has no source but the field type), so the
    # constructor-arm path must fall back from `:unsupported_expression` to CHECKED
    # elaboration. Before that fallback existed, this failed as
    # `{:unsupported_expression, {:lambda, ...}}`. `mk`'s arms build the box; `unbox`
    # applies the stored lambda so the run exercises the actual closure.
    src =
      "mod M\n  type Box(a: Type) = MkBox(a, (a) -> a)\n" <>
        "  fn unbox({a: Type}, b: Box(a), x: a) -> a =\n" <>
        "    match b\n      MkBox(v, f) -> f(x)\n" <>
        "  fn mk({a: Type}, sel: Int, v: a, g: (a) -> a) -> Box(a) =\n" <>
        "    match sel\n" <>
        "      0 -> MkBox(v, fn(new) -> g(new))\n" <>
        "      other -> MkBox(v, fn(new) -> g(g(new)))\n" <>
        "  fn demo(sel: Int, start: Int) -> Int =\n" <>
        "    unbox(mk(sel, 0, fn(n) -> n + 1), start)\nend\n"

    assert {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.M", functions: [:demo, :mk, :unbox])
    # sel=0: one application of `+1` to start; sel=1 (other): two applications.
    assert apply(mod, :demo, [0, 5]) == 6
    assert apply(mod, :demo, [1, 5]) == 7
  end
end
