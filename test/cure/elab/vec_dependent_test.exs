defmodule Cure.Elab.VecDependentTest do
  @moduledoc """
  A genuinely length-indexed vector `Vector(a, n)` — the canonical dependent type —
  must elaborate and kernel-check through the real pipeline, replacing the faked
  `Std.Vector` whose length lived only in a runtime tuple.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.Inductive
  alias Cure.Elab.Program

  @vec_core """
  type Nat = Z | S(Nat)
  type Vector(a: Type) indices (n: Nat)
    empty : Vector(a, Z)
    prepend : a -> Vector(a, n) -> Vector(a, S(n))
  """

  test "the length-indexed Vector family elaborates with a Type parameter and Nat index" do
    assert {:ok, env} = Program.elaborate(@vec_core)
    # `a` is a uniform parameter (never matched); `n` is the sole index.
    assert %{params: [a: {:type, 0}], indices: [n: {:data, :"Main#Nat", [], []}]} =
             Inductive.get_family(env, :Vector)
  end

  test "a total recursive plus over Nat elaborates and certifies" do
    src =
      @vec_core <>
        """
        fn plus(m: Nat, n: Nat) -> Nat = match m
          Z() -> n
          S(k) -> S(plus(k, n))
        """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "append's length index adds up via the total plus" do
    src =
      @vec_core <>
        """
        fn plus(m: Nat, n: Nat) -> Nat = match m
          Z() -> n
          S(k) -> S(plus(k, n))
        fn append({a: Type}, {m: Nat}, {n: Nat}, xs: Vector(a, m), ys: Vector(a, n)) -> Vector(a, plus(m, n)) = match xs
          empty() -> ys
          prepend(x, rest) -> prepend(x, append(rest, ys))
        """

    assert {:ok, _env} = Program.elaborate(src)
  end
end
