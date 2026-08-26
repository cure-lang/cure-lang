defmodule Cure.Elab.TupleTypeSurfaceTest do
  # `Tuple(T, U)` is the honest arity-2 surface tuple type. Increment 1 makes it a
  # parser alias for the existing non-dependent Sigma, so `%[a,b]` already
  # elaborates/emits against it (probe A confirmed arity-2 works vs a defined Sigma).
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  test "a fn returning Tuple(Int, Int) elaborates and emits a flat 2-tuple" do
    src = """
    mod M
      fn mk(a: Int, b: Int) -> Tuple(Int, Int) = %[a, b]
      fn fst(a: Int, b: Int) -> Int = mk(a, b).1
      fn snd(a: Int, b: Int) -> Int = mk(a, b).2
    """

    assert {:ok, env} = Program.elaborate(src)
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.M", functions: [:mk, :fst, :snd])
    assert apply(m, :mk, [7, 9]) == {7, 9}
    assert apply(m, :fst, [7, 9]) == 7
    assert apply(m, :snd, [7, 9]) == 9
  end

  test "dependent arity-2 Tuple(m: Nat, Vector(Int, m)) still checks the later position" do
    src = """
    mod M
      type Nat = Zero | Suc(Nat)
      type Vector(a: Type) indices (n: Nat)
        empty : Vector(a, Zero)
        prepend : a -> Vector(a, n) -> Vector(a, Suc(n))
      fn one(v: Vector(Int, Suc(Zero))) -> Tuple(m: Nat, Vector(Int, m)) = %[Suc(Zero()), v]
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end
