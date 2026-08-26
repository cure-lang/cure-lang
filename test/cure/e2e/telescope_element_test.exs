defmodule Cure.E2E.TelescopeElementTest do
  @moduledoc """
  Dependent n-ary projection on telescopes / tuples. A single `element(t, i)`
  gives the i-th component, typed at the true `Ti` (NOT a numbered `tproj_i`
  family), with a COMPILE-TIME bounds check: `element(t, i)` where `i` exceeds
  the telescope's arity must be REJECTED at elaboration, not crash at runtime.
  `t.i` is surface sugar for `element(t, i)`. All of it applies to `Tuple`,
  which is a telescope. Runtime rep stays the flat BEAM tuple.

  Every probe is end-to-end: elaborate → (emit → load → run) on the host BEAM.
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

  test "element(t, i) projects the i-th component and runs on the BEAM" do
    src = """
    mod ElemRun
      fn t3() -> Tuple(Int, Int, Int) = %[10, 20, 30]
      fn e1() -> Int = element(t3(), 1)
      fn e2() -> Int = element(t3(), 2)
      fn e3() -> Int = element(t3(), 3)
      fn start() -> Int = e3()
    """

    assert {:ok, mod} = build(src, :"Cure.ElemRun", [:t3, :e1, :e2, :e3, :start])
    assert apply(mod, :e1, []) == 10
    assert apply(mod, :e2, []) == 20
    assert apply(mod, :e3, []) == 30
  end

  test "t.i sugar is equivalent to element(t, i)" do
    src = """
    mod ElemSugar
      fn t3() -> Tuple(Int, Int, Int) = %[10, 20, 30]
      fn viaDot() -> Int = t3().3
      fn viaElem() -> Int = element(t3(), 3)
      fn start() -> Int = viaDot()
    """

    assert {:ok, mod} = build(src, :"Cure.ElemSugar", [:t3, :viaDot, :viaElem, :start])
    assert apply(mod, :viaDot, []) == 30
    assert apply(mod, :viaElem, []) == 30
  end

  test "element(t, i) beyond the arity is a COMPILE-TIME error, not a runtime crash" do
    src = """
    mod ElemOOB
      fn t3() -> Tuple(Int, Int, Int) = %[10, 20, 30]
      fn bad() -> Int = element(t3(), 9)
      fn start() -> Int = bad()
    """

    assert {:error, _} = elab(src)
  end

  test "the projection type is the true i-th component type (heterogeneous)" do
    # Second component is a nested Tuple; projecting it must type at that tuple,
    # so a further `.1` on the result is well-typed. A wrong (collapsed) type
    # would make the inner projection ill-typed.
    src = """
    mod ElemHetero
      fn t() -> Tuple(Int, Tuple(Int, Int), Int) = %[1, %[2, 3], 4]
      fn inner() -> Int = element(t(), 2).1
      fn start() -> Int = inner()
    """

    assert {:ok, mod} = build(src, :"Cure.ElemHetero", [:t, :inner, :start])
    assert apply(mod, :inner, []) == 2
  end
end
