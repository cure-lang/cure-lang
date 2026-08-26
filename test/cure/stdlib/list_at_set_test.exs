defmodule Cure.Stdlib.ListAtSetTest do
  @moduledoc """
  `Std.List.at/2` and `set_at/3`: the total, `Option`-returning random-access
  read and the replace-or-unchanged write. These are the partial getter/putter
  the `ix` list-index affine is built on, so they must be total at both ends of
  range and on the empty list. `Option` lowers OTP-lowercase (`{:some, v}` /
  `:none`).
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  defp load(body, root) do
    src = "mod M\n  use Std.List\n  use Std.Option\n" <> body
    assert {:ok, env} = Program.elaborate(src)
    fns = Program.reachable_def_names(env, [root])
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.MListAtSet", functions: fns)
    m
  end

  test "at/2 is Some in range and None past either end, on [], and negative" do
    m = load("  fn at_(xs: List(Int), i: Int) -> Option(Int) = Std.List.at(xs, i)\n", :at_)
    assert apply(m, :at_, [[10, 20, 30], 0]) == {:some, 10}
    assert apply(m, :at_, [[10, 20, 30], 2]) == {:some, 30}
    assert apply(m, :at_, [[10, 20, 30], 3]) == :none
    assert apply(m, :at_, [[], 0]) == :none
    assert apply(m, :at_, [[10, 20, 30], -1]) == :none
  end

  test "set_at/3 replaces in range and is a no-op past either end, on [], and negative" do
    m = load("  fn set_(xs: List(Int), i: Int, v: Int) -> List(Int) = Std.List.set_at(xs, i, v)\n", :set_)
    assert apply(m, :set_, [[10, 20, 30], 0, 99]) == [99, 20, 30]
    assert apply(m, :set_, [[10, 20, 30], 2, 99]) == [10, 20, 99]
    assert apply(m, :set_, [[10, 20, 30], 3, 99]) == [10, 20, 30]
    assert apply(m, :set_, [[], 0, 99]) == []
    assert apply(m, :set_, [[10, 20, 30], -1, 99]) == [10, 20, 30]
  end
end
