defmodule Cure.E2E.FlatTelescopeTest do
  @moduledoc """
  Flat n-ary telescope tuples (unified-tuple design, Option B). `Tuple(T1,…,Tn)`
  is the unit-terminated nested Σ `Sigma(T1, … Sigma(Tn, Unit))`; at CODEGEN it
  lowers to a FLAT BEAM tuple `{a,…,n}` (the `unit` terminator is the marker emit
  keys on, erased before runtime). Positional `.i` and telescope patterns also
  understand the flat lowering. Nesting is opt-in: `Tuple(A, Tuple(B,C))` → `{a,{b,c}}`.

  Every probe is end-to-end: elaborate → emit → load → run on the host BEAM.
  """
  use ExUnit.Case, async: false

  alias Cure.Elab.{Program, Emit}

  defp elab(src) do
    try do
      Program.elaborate(src)
    rescue
      e -> {:raise, Exception.message(e)}
    catch
      k, v -> {:raise, "#{inspect(k)}: #{inspect(v)}"}
    end
  end

  defp build(src, mod, fns) do
    case elab(src) do
      {:ok, env} ->
        try do
          Emit.compile_and_load(env, module: mod, functions: fns)
        rescue
          e -> {:raise, Exception.message(e)}
        catch
          k, v -> {:raise, "#{inspect(k)}: #{inspect(v)}"}
        end

      other ->
        other
    end
  end

  @flat3 """
  mod FlatT3
    fn t3() -> Tuple(Int, Int, Int) = %[1, 2, 3]
    fn start() -> Tuple(Int, Int, Int) = t3()
  """
  test "arity-3 telescope value lowers to a FLAT BEAM tuple {1,2,3}" do
    assert {:ok, mod} = build(@flat3, :"Cure.FlatT3", [:t3, :start])
    assert apply(mod, :t3, []) == {1, 2, 3}
  end

  @flat2 """
  mod FlatT2
    fn t2() -> Tuple(Int, Int) = %[1, 2]
    fn start() -> Tuple(Int, Int) = t2()
  """
  test "arity-2 telescope value lowers to a FLAT BEAM tuple {1,2}" do
    assert {:ok, mod} = build(@flat2, :"Cure.FlatT2", [:t2, :start])
    assert apply(mod, :t2, []) == {1, 2}
  end

  @nested """
  mod NestedT
    fn t() -> Tuple(Int, Tuple(Int, Int)) = %[1, %[2, 3]]
    fn start() -> Tuple(Int, Tuple(Int, Int)) = t()
  """
  test "opt-in nesting Tuple(A, Tuple(B,C)) lowers to {a, {b,c}}" do
    assert {:ok, mod} = build(@nested, :"Cure.NestedT", [:t, :start])
    assert apply(mod, :t, []) == {1, {2, 3}}
  end

  # --- positional projection `.i` (type Ti, emit element(i)) -----------------

  @proj2 """
  mod Proj2
    fn t() -> Tuple(Int, Int) = %[10, 20]
    fn snd() -> Int = t().2
    fn start() -> Int = snd()
  """
  test "positional .2 on an arity-2 telescope projects the 2nd element (type Int)" do
    assert {:ok, mod} = build(@proj2, :"Cure.Proj2", [:t, :snd, :start])
    assert apply(mod, :snd, []) == 20
  end

  @proj3 """
  mod Proj3
    fn t() -> Tuple(Int, Int, Int) = %[10, 20, 30]
    fn second() -> Int = t().2
    fn third() -> Int = t().3
    fn start() -> Int = third()
  """
  test "positional .2 and .3 on an arity-3 telescope project the right elements" do
    assert {:ok, mod} = build(@proj3, :"Cure.Proj3", [:t, :second, :third, :start])
    assert apply(mod, :second, []) == 20
    assert apply(mod, :third, []) == 30
  end

  # --- telescope pattern `%[p1..pn]` (routes through positional projection) ---

  @pat3 """
  mod Pat3
    fn sum(t: Tuple(Int, Int, Int)) -> Int = match t
      %[a, b, c] -> a + b + c
    fn start() -> Int = sum(%[100, 20, 3])
  """
  test "an arity-3 telescope pattern binds all three components positionally" do
    assert {:ok, mod} = build(@pat3, :"Cure.Pat3", [:sum, :start])
    assert apply(mod, :sum, [{100, 20, 3}]) == 123
  end

  # --- Std.Tuple's own shapes (first/second/swap/third) over flat telescopes --
  # Mirrors lib/std/tuple.cure's bodies in-module (the ad-hoc single-source
  # builder cannot link a `use`-d module's beam for emit). `swap` exercises
  # construction-from-projections; the stdlib module elaborating green is the
  # cross-module acceptance.

  @tupleapi """
  mod TupleApi
    fn second(t: Tuple(a, b)) -> b = t.2
    fn swap(t: Tuple(a, b)) -> Tuple(b, a) = %[t.2, t.1]
    fn third(t: Tuple(a, b, c)) -> c = t.3
    fn start() -> Int = second(%[10, 20])
  """
  test "first/second/swap/third shapes elaborate and run over flat telescopes" do
    assert {:ok, mod} = build(@tupleapi, :"Cure.TupleApi", [:second, :swap, :third, :start])
    assert apply(mod, :second, [{10, 20}]) == 20
    assert apply(mod, :swap, [{10, 20}]) == {20, 10}
    assert apply(mod, :third, [{1, 2, 3}]) == 3
  end
end
