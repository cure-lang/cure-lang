defmodule Cure.Elab.OperatorRerouteDifferentialTest do
  @moduledoc """
  Phase 2: re-routed operators evaluate identically to the builtin path.

  This is a *regression lock*, not an initially-red test. Each operator
  expression (arithmetic, comparison, equality, boolean, Semigroup concat, and
  ADT structural equality) is evaluated end-to-end on the BEAM. The recorded
  values are the pre-change baseline; if any re-route step (point the fallbacks
  at bare-name methods, delete `build_binop`'s `==`/`<` hardcoding, auto-derive
  structural `Equatable`) changes a result, this test goes red.

  The two ADT `==` cases (`Some(1) == Some(1)` / `Some(1) == None()`) are the
  regression lock proving the auto-derived structural `Equatable` instance
  matches the old builtin `struct_eq` exactly.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Emit, Program}

  @src """
  mod DiffM
    use Std.Option
    use Std.Semigroup
    fn arith_a() -> Int = 1 + 2 * 3
    fn arith_b() -> Int = 10 / 2 - 1
    fn cmp_lt() -> Bool = 1 < 2
    fn cmp_ge() -> Bool = 2 >= 2
    fn eq_int() -> Bool = 1 == 1
    fn concat() -> List(Int) = [1, 2] <> [3]
    fn bool_and() -> Bool = true and false
    fn bool_not() -> Bool = not true
    fn eq_str() -> Bool = "a" == "a"
    fn none_int() -> Option(Int) = None()
    fn eq_adt_same() -> Bool = Some(1) == Some(1)
    fn eq_adt_diff() -> Bool = Some(1) == none_int()
  end
  """

  @funcs [
    :arith_a,
    :arith_b,
    :cmp_lt,
    :cmp_ge,
    :eq_int,
    :concat,
    :bool_and,
    :bool_not,
    :eq_str,
    :none_int,
    :eq_adt_same,
    :eq_adt_diff
  ]

  defp load do
    {:ok, env} = Program.elaborate(@src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.DiffM", functions: @funcs)
    mod
  end

  test "arithmetic, comparison, equality, boolean, concat, ADT — identical results" do
    mod = load()

    assert apply(mod, :arith_a, []) == 7
    assert apply(mod, :arith_b, []) == 4
    assert apply(mod, :cmp_lt, []) == true
    assert apply(mod, :cmp_ge, []) == true
    assert apply(mod, :eq_int, []) == true
    assert apply(mod, :concat, []) == [1, 2, 3]
    assert apply(mod, :bool_and, []) == false
    assert apply(mod, :bool_not, []) == false
    assert apply(mod, :eq_str, []) == true
    assert apply(mod, :eq_adt_same, []) == true
    assert apply(mod, :eq_adt_diff, []) == false
  end
end
