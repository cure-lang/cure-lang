defmodule Cure.Elab.SharedIndexMatchTest do
  @moduledoc """
  Matching an indexed value when a *sibling* in scope shares the same index
  variable — the essence of `zipWith`/`lookup` over length-indexed vectors
  (Idris parity). `match ys` where both `xs, ys : Vector(a, S(m))` failed
  `:branch_type`.

  Root cause: `detect_carried_index` fired the carried-equation transport for
  *any* non-variable (computed) index term mentioned by a sibling. But a
  constructor spine like `S(m)` (or the refined `S(xr_len)` a nested match
  produces) is INVERTIBLE by ordinary index refinement — Idris's `yr : Vect m a`
  in the `(::)` branch — and needs no equation. Forcing the transport onto the
  sibling, with a fresh-variable constructor index, spuriously failed even when
  the branch body never used the sibling. `invertible_index?` now excludes a
  constructor-spine-over-variables index from carried-eq detection; only a
  non-invertible computed index (a defined-function application like `app(p,q)`)
  still carries the equation (guarded by `carried_index_sibling_test`).

  Oracle `dep/dep04_zipwith_shared_index` pins accept/accept.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Emit}

  @vec "mod M\n  type Nat = Z | S(Nat)\n" <>
         "  type Vector(a: Type) indices (n: Nat)\n" <>
         "    empty : Vector(a, Z)\n" <>
         "    prepend : a -> Vector(a, n) -> Vector(a, S(n))\n"

  test "matching a vector when a sibling shares its index variable" do
    src =
      @vec <>
        "  fn f({a: Type},{m: Nat}, xs: Vector(a, S(m)), ys: Vector(a, S(m))) -> a = match ys\n" <>
        "    prepend(y, yr) -> y\n" <>
        "  fn one() -> Vector(Nat, S(Z)) = prepend(S(Z()), empty())\n" <>
        "  fn g() -> Nat = f(one(), one())\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.SharedHd", functions: [:f, :one, :g])

    # head of [S(Z)] is S(Z)
    assert apply(mod, :g, []) == {:S, :Z}
  end

  test "zipWith over two equal-length vectors elaborates, nests, and runs" do
    src =
      @vec <>
        "  fn add(x: Nat, y: Nat) -> Nat = match x\n    Z() -> y\n    S(p) -> S(add(p, y))\n" <>
        "  fn zipAdd({n: Nat}, xs: Vector(Nat, n), ys: Vector(Nat, n)) -> Vector(Nat, n) = match xs\n" <>
        "    empty() -> empty()\n" <>
        "    prepend(x, xr) -> match ys\n      prepend(y, yr) -> prepend(add(x, y), zipAdd(xr, yr))\n" <>
        "  fn v() -> Vector(Nat, S(S(Z))) = prepend(S(Z()), prepend(Z(), empty()))\n" <>
        "  fn g() -> Vector(Nat, S(S(Z))) = zipAdd(v(), v())\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.ZipAdd", functions: [:add, :zipAdd, :v, :g])

    # zipAdd([1,0], [1,0]) = [2, 0]
    assert apply(mod, :g, []) == {:prepend, {:S, {:S, :Z}}, {:prepend, :Z, :empty}}
  end

  test "generic zipWith over two equal-length vectors elaborates" do
    src =
      @vec <>
        "  fn zipSame({a: Type},{n: Nat}, xs: Vector(a, n), ys: Vector(a, n), f: a -> a -> a) -> Vector(a, n) = match xs\n" <>
        "    empty() -> empty()\n" <>
        "    prepend(x, xr) -> match ys\n      prepend(y, yr) -> prepend(f(x)(y), zipSame(xr, yr, f))\nend\n"

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "two vectors with DISTINCT index variables still elaborate (no false coupling)" do
    src =
      @vec <>
        "  fn f({a: Type},{m: Nat},{k: Nat}, xs: Vector(a, S(m)), ys: Vector(a, S(k))) -> a = match ys\n" <>
        "    prepend(y, yr) -> y\nend\n"

    assert {:ok, _env} = Program.elaborate(src)
  end
end
