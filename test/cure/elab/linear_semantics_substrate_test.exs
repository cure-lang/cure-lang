defmodule Cure.Elab.LinearSemanticsSubstrateTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.{Emit, Program}

  test "an earlier total recursive definition reduces in a later equality proof" do
    source = """
    mod RecursiveDeltaProof
      use Std.Nat
      use Std.List
      use Std.Equivalent

      fn sum(xs: List(Nat)) -> Nat = match xs
        [] -> Z()
        [x | rest] -> plus(x, sum(rest))

      fn sum_empty() -> Equivalent(Nat, sum(Nil()), Z()) = reflexive(Z())
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "computed result-index variables erase without surviving as free runtime variables" do
    source = """
    mod ComputedIndexErasure
      use Std.Nat
      use Std.List
      use Std.Equivalent

      type Vec indices (n: Nat)
        VNil : Vec(Z())
        VCons : Vec(n) -> Vec(S(n))

      type Added indices (left: List(Nat), right: List(Nat), result: List(Nat))
        AddedNil : Added(Nil(), Nil(), Nil())
        AddedCons : Added(lefts, rights, results) -> Added(Cons(left, lefts), Cons(right, rights), Cons(plus(left, right), results))

      fn keep(lefts: List(Nat), rights: List(Nat), results: List(Nat), proof: Added(lefts, rights, results)) -> Added(lefts, rights, results) = match proof
        AddedNil() -> AddedNil()
        AddedCons(rest) -> AddedCons(rest)
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    functions = Program.reachable_def_names(env, [:keep])
    assert {:ok, _module} = Emit.compile_and_load(env, module: :ComputedIndexErasureRuntime, functions: functions)
  end

  test "constructor-refined aligned recursion exposes dot base and step equations" do
    source = """
    mod AlignedDotProof
      use Std.Nat
      use Std.Int
      use Std.List
      use Std.Equivalent
      use Std.Proof.IntOrder

      fn dot(xs: List(Int), ys: List(Int)) -> Int = match xs
        [] -> int_zero()
        [x | xr] -> match ys
          [] -> int_zero()
          [y | yr] -> add_int(multiply_int(x, y), dot(xr, yr))

      type ZeroAt indices (coefficients: List(Int), values: List(Int))
        ZeroNil : ZeroAt(Nil(), Nil())
        ZeroCons : ZeroAt(coefficients, values) -> ZeroAt(Cons(int_zero(), coefficients), Cons(value, values))

      fn dot_zero(coefficients: List(Int), values: List(Int), aligned: ZeroAt(coefficients, values)) -> Equivalent(Int, dot(coefficients, values), int_zero()) = match aligned
        ZeroNil() -> reflexive(int_zero())
        ZeroCons(rest) -> match coefficients
          [zero | coefficients_rest] -> match values
            [_ | values_rest] -> rewrite dot_zero(coefficients_rest, values_rest, rest) in reflexive(int_zero())
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end
end
