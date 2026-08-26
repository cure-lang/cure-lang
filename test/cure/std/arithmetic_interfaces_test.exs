defmodule Cure.Std.ArithmeticInterfacesTest do
  @moduledoc """
  Task 2.5: the arithmetic interfaces `Additive`/`Multiplicative`/`Divisible`/
  `Integral` (Std.Arithmetic) with Int/Float instances. ADDITIVE and DORMANT —
  operators do NOT route through these interfaces yet (`build_binop` still
  hardcodes the primitive by operand kind; that rewiring is Task 2.6). These
  tests exercise the new methods by their backtick operator name directly,
  proving the interfaces + instances elaborate, emit, and compute correctly.

  Harness: the real elaborate -> reachable -> emit -> apply pipeline, copied
  from `test/cure/std/minimal_basis_test.exs` (Task 2.4). Each expression is
  wrapped in a fresh `mod` with a unique BEAM module atom per case.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  # Wrap `expr` (which must have type Int) in a module + nullary function, then
  # elaborate/emit/apply it, returning the plain Elixir integer.
  defp eval_int(expr, mod) do
    src = """
    mod T
      use Std.Arithmetic
      fn f() -> Int = #{expr}
    """

    {:ok, env} = Program.elaborate(src)
    fns = Program.reachable_def_names(env, [:f])
    {:ok, m} = Emit.compile_and_load(env, module: mod, functions: fns)
    apply(m, :f, [])
  end

  # Wrap `expr` (which must have type Float) in a module + nullary function,
  # then elaborate/emit/apply it, returning the plain Elixir float.
  defp eval_float(expr, mod) do
    src = """
    mod T
      use Std.Arithmetic
      fn f() -> Float = #{expr}
    """

    {:ok, env} = Program.elaborate(src)
    fns = Program.reachable_def_names(env, [:f])
    {:ok, m} = Emit.compile_and_load(env, module: mod, functions: fns)
    apply(m, :f, [])
  end

  test "Additive/Multiplicative/Divisible/Integral methods compute on Int and Float" do
    assert eval_int("`+`(2, 3)", :"Cure.ArithAddInt") == 5
    assert eval_int("`*`(2, 3)", :"Cure.ArithMulInt") == 6
    assert eval_int("`/`(6, 2)", :"Cure.ArithDivInt") == 3
    assert eval_int("`%`(7, 3)", :"Cure.ArithRemInt") == 1
    assert eval_int("negate(5)", :"Cure.ArithNegInt") == -5
    assert eval_float("`+`(2.0, 0.5)", :"Cure.ArithAddFloat") == 2.5
  end
end
