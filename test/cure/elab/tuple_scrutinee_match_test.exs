defmodule Cure.Elab.TupleScrutineeMatchTest do
  @moduledoc """
  A tuple SCRUTINEE — `match %[xs, ys] | %[C(…), D(…)] -> …` (Idris'
  simultaneous `case (xs, ys) of`) — is desugared, one column at a time, into a
  nested single-scrutinee match `match xs | C(…) -> match ys | D(…) -> …`, so the
  existing dependent machinery handles it. The impossible cross-constructor cases
  (`%[empty, prepend]` / `%[prepend, empty]` over two `Vector`s that share index
  `n`) are elided by the inner index-refined match's coverage — exactly as the
  hand-written nested form (dep04) already relies on.

  Oracle `dep/dep10_tuple_simultaneous` pins accept/accept; these tests also run
  the compiled result so the desugaring is semantics-preserving, not just
  acceptance.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Emit}

  @vec "mod M\n  type Nat = Z | S(Nat)\n" <>
         "  type Vector(a: Type) indices (n: Nat)\n" <>
         "    empty : Vector(a, Z)\n" <>
         "    prepend : a -> Vector(a, n) -> Vector(a, S(n))\n"

  test "zipAdd over a 2-tuple scrutinee elaborates, nests, and runs" do
    src =
      @vec <>
        "  fn add(x: Nat, y: Nat) -> Nat = match x\n    Z() -> y\n    S(p) -> S(add(p, y))\n" <>
        "  fn zipAdd({n: Nat}, xs: Vector(Nat, n), ys: Vector(Nat, n)) -> Vector(Nat, n) = match %[xs, ys]\n" <>
        "    %[empty(), empty()] -> empty()\n" <>
        "    %[prepend(x, xr), prepend(y, yr)] -> prepend(add(x, y), zipAdd(xr, yr))\n" <>
        "  fn v() -> Vector(Nat, S(S(Z))) = prepend(S(Z()), prepend(Z(), empty()))\n" <>
        "  fn g() -> Vector(Nat, S(S(Z))) = zipAdd(v(), v())\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.TupZipAdd", functions: [:add, :zipAdd, :v, :g])

    # zipAdd([1,0], [1,0]) = [2, 0]
    assert apply(mod, :g, []) == {:prepend, {:S, {:S, :Z}}, {:prepend, :Z, :empty}}
  end

  test "heterogeneous generic zip_with over a 2-tuple scrutinee elaborates" do
    src =
      @vec <>
        "  fn zip_with({a: Type},{b: Type},{c: Type},{n: Nat}, xs: Vector(a, n), ys: Vector(b, n), f: a -> b -> c) -> Vector(c, n) = match %[xs, ys]\n" <>
        "    %[empty(), empty()] -> empty()\n" <>
        "    %[prepend(x, xr), prepend(y, yr)] -> prepend(f(x)(y), zip_with(xr, yr, f))\nend\n"

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "generic same-type zip_with over a 2-tuple scrutinee elaborates" do
    src =
      @vec <>
        "  fn zip_same({a: Type},{n: Nat}, xs: Vector(a, n), ys: Vector(a, n), f: a -> a -> a) -> Vector(a, n) = match %[xs, ys]\n" <>
        "    %[empty(), empty()] -> empty()\n" <>
        "    %[prepend(x, xr), prepend(y, yr)] -> prepend(f(x)(y), zip_same(xr, yr, f))\nend\n"

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "a tuple-of-variables scrutinee with nested rows reaches its catchall" do
    src = """
    mod TupleCatchall
      fn add_heads(xs: List(Int), ys: List(Int)) -> Int = match %[xs, ys]
        %[[x | _], [y | _]] -> x + y
        _ -> 0

      fn add_heads_explicit(xs: List(Int), ys: List(Int)) -> Int =
        let key = %[xs, ys]
        match key
          %[[x | _], [y | _]] -> x + y
          %[_, _] -> 0
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert apply(module, :add_heads, [[2], [3]]) == 5
    assert apply(module, :add_heads, [[], [3]]) == 0
    assert apply(module, :add_heads_explicit, [[2], [3]]) == 5
    assert apply(module, :add_heads_explicit, [[], [3]]) == 0
  end

  test "a non-tuple scrutinee is untouched by the desugaring" do
    src =
      @vec <>
        "  fn f({a: Type},{m: Nat}, ys: Vector(a, S(m))) -> a = match ys\n" <>
        "    prepend(y, yr) -> y\nend\n"

    assert {:ok, _env} = Program.elaborate(src)
  end
end
