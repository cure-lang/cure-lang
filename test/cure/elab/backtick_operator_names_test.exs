defmodule Cure.Elab.BacktickOperatorNamesTest do
  @moduledoc "Phase 2: a function may be named by an operator lexeme via backticks."
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  test "a function named `+` elaborates and is callable by that name" do
    src = """
    mod M
      fn `+`(a: Int, b: Int) -> Int = Std.Builtin.int_add(a, b)
      fn use_it(x: Int) -> Int = `+`(x, x)
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end
