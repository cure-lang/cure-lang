defmodule Cure.Std.MinimalBasisTest do
  @moduledoc """
  Phase 2 (Task 2.4): the minimal-basis `Std.Equatable`/`Std.Comparable` derive
  the full comparison surface from the two primitives `==` and `<`, with results
  identical to the pre-migration stdlib.

  Two flavours of assertion:

    * operator expressions (`1 == 1`, `2 <= 2`, …) — a *differential* guard.
      These do NOT route through the interface today (`build_binop` hardcodes the
      primitive by operand kind), so they exercise the live lowering and lock in
      that the rewritten stdlib still compiles and evaluates identically.

    * method-by-name calls to the NEW basis (`` `!=`(1, 2) ``, `` `<`(1, 2) ``,
      the new `Equatable for Char` `` `==` ``) — these exercise the rewritten
      interface directly. They FAIL on the pre-rewrite stdlib (method was `eq`/
      `compare`, no `` `!=` ``/`` `<` `` method, no Char instance) and PASS after.

  Harness: the real elaborate -> reachable -> emit -> apply pipeline copied from
  `test/cure/stdlib/comparable_compare_test.exs`. Each expression is wrapped in a
  fresh `mod` with a unique BEAM module atom per case.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  # Wrap `expr` (which must have type Bool) in a module + nullary function, then
  # elaborate/emit/apply it, returning the plain Elixir boolean.
  defp eval_bool(expr, mod) do
    src = """
    mod T
      use Std.Equatable
      use Std.Comparable
      use Std.Char
      use Std.String
      use Std.Bool
      fn f() -> Bool = #{expr}
    """

    {:ok, env} = Program.elaborate(src)
    fns = Program.reachable_def_names(env, [:f])
    {:ok, m} = Emit.compile_and_load(env, module: mod, functions: fns)
    apply(m, :f, [])
  end

  # Fold an Ordering-valued `compare(...)` expression to a boolean at the Cure
  # source level (the approach the existing suite uses), then evaluate it.
  defp eval_ordering(expr, ctor, mod) do
    eval_bool("#{expr} == #{ctor}()", mod)
  end

  describe "derived comparison operators (differential guard)" do
    test "== / != / < / <= / > / >= on Int" do
      assert eval_bool("1 == 1", :"Cure.MinBasisEqInt") == true
      assert eval_bool("1 != 2", :"Cure.MinBasisNeInt") == true
      assert eval_bool("1 < 2", :"Cure.MinBasisLtInt") == true
      assert eval_bool("2 <= 2", :"Cure.MinBasisLeInt") == true
      assert eval_bool("3 > 2", :"Cure.MinBasisGtInt") == true
      assert eval_bool("3 >= 3", :"Cure.MinBasisGeInt") == true
    end

    test "Float equality via float_eq (IEEE-correct primitive path)" do
      # No `nan()` facility exists and BEAM 0.0/0.0 raises rather than yielding
      # a NaN value, so NaN==NaN is untestable honestly. The Float `==` instance
      # binds `float_eq`, which IS IEEE-correct; validate the primitive path with
      # distinct values instead of faking a NaN.
      assert eval_bool("1.0 == 1.0", :"Cure.MinBasisEqFloatT") == true
      assert eval_bool("1.0 == 2.0", :"Cure.MinBasisEqFloatF") == false
    end
  end

  describe "compare is derived and still returns Ordering" do
    test "Int compare returns the three Ordering constructors" do
      assert eval_ordering("compare(1, 2)", "LessThan", :"Cure.MinBasisCmpLt") == true
      assert eval_ordering("compare(2, 2)", "EqualTo", :"Cure.MinBasisCmpEq") == true
      assert eval_ordering("compare(3, 2)", "GreaterThan", :"Cure.MinBasisCmpGt") == true
    end
  end

  describe "Char equality/order via the new Char instances" do
    test "Char == and <" do
      assert eval_bool("'a' == 'a'", :"Cure.MinBasisCharEq") == true
      assert eval_bool("'a' < 'b'", :"Cure.MinBasisCharLt") == true
    end
  end

  describe "new minimal basis exercised by method name" do
    test "derived `!=` default on Int" do
      assert eval_bool("`!=`(1, 2)", :"Cure.MinBasisNeMethodT") == true
      assert eval_bool("`!=`(2, 2)", :"Cure.MinBasisNeMethodF") == false
    end

    test "primitive `<` method on Int" do
      assert eval_bool("`<`(1, 2)", :"Cure.MinBasisLtMethodT") == true
      assert eval_bool("`<`(2, 1)", :"Cure.MinBasisLtMethodF") == false
    end

    test "primitive `==` method on the new Char instance" do
      assert eval_bool("`==`('a', 'a')", :"Cure.MinBasisCharEqMethodT") == true
      assert eval_bool("`==`('a', 'b')", :"Cure.MinBasisCharEqMethodF") == false
    end
  end
end
