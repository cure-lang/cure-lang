defmodule Cure.Elab.BoolConnectiveLoweringTest do
  @moduledoc """
  Phase 2 of retiring the Boolean-connective primitives: the surface operators
  `and`/`or`/`not` and Bool-typed `==`/`!=` now elaborate to APPLICATIONS of the
  `Std.Bool` prelude defs instead of `{:prim, :and/:or/:not/:eq/:ne}` nodes.

  `==`/`!=` are operand-type-directed (K2 phase 2, spec 2026-07-09): numeric
  (Int/Float) operands lower to the monomorphic builtin-op globals
  `int_eq`/`int_ne`/`float_eq`/`float_ne` spines; Bool operands lower to `eq`/`ne`.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program
  alias Cure.Core.Env

  # Body of a nullary top-level fn `name` (no lambda wrapper).
  defp body(src, name) do
    {:ok, env} = Program.elaborate("mod M\n  use Std.Bool\n" <> src <> "end\n")
    Env.get_def(env, name).body
  end

  # Builtin ops lower to owner-qualified globals (`Std.Builtin#int_eq`), matching
  # both `Builtins.seed`'s registration key and the elaborator's emission.
  defp bop(op), do: Cure.Elab.Name.qualify("Std.Builtin", op)
  defp bool_def(name), do: Cure.Elab.Name.qualify("Std.Bool", name)

  @tt {:ctor, :"Std.Bool#True", []}
  @ff {:ctor, :"Std.Bool#False", []}

  test "`and` lowers to an `and` application, not a :and prim" do
    assert body("  fn t() -> Bool = true and false\n", :t) ==
             {:app, {:app, {:global, bool_def(:and)}, @tt}, @ff}
  end

  test "`or` lowers to an `or` application" do
    assert body("  fn t() -> Bool = true or false\n", :t) ==
             {:app, {:app, {:global, bool_def(:or)}, @tt}, @ff}
  end

  test "`not` lowers to a `not` application" do
    assert body("  fn t() -> Bool = not true\n", :t) ==
             {:app, {:global, bool_def(:not)}, @tt}
  end

  test "Int `==` lowers to the int_eq builtin-op global" do
    assert body("  fn t() -> Bool = 1 == 2\n", :t) ==
             {:app, {:app, {:global, bop(:int_eq)}, {:int_lit, 1}}, {:int_lit, 2}}
  end

  test "Float `==` lowers to the float_eq builtin-op global" do
    assert body("  fn t() -> Bool = 1.0 == 2.0\n", :t) ==
             {:app, {:app, {:global, bop(:float_eq)}, {:float_lit, 1.0}}, {:float_lit, 2.0}}
  end

  test "Int `!=` lowers to the int_ne builtin-op global" do
    assert body("  fn t() -> Bool = 1 != 2\n", :t) ==
             {:app, {:app, {:global, bop(:int_ne)}, {:int_lit, 1}}, {:int_lit, 2}}
  end

  test "Bool `==` lowers to an `eq` application" do
    assert body("  fn t() -> Bool = true == false\n", :t) ==
             {:app, {:app, {:global, bool_def(:eq)}, @tt}, @ff}
  end

  test "Bool `!=` lowers to a `ne` application" do
    assert body("  fn t() -> Bool = true != false\n", :t) ==
             {:app, {:app, {:global, bool_def(:ne)}, @tt}, @ff}
  end

  test "a mixed Int/Bool `==` is rejected" do
    assert {:error, _} =
             Program.elaborate("mod M\n  use Std.Bool\n  fn t() -> Bool = 1 == true\nend\n")
  end
end
