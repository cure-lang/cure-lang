defmodule CureSiteWeb.EvalTest do
  use ExUnit.Case, async: false

  alias CureSiteWeb.Eval

  test "compiles, loads, and runs main through the current compiler pipeline" do
    source = """
    mod SiteEvalCurrentCompiler
      fn main() -> Int = 40 + 2
    """

    assert {:ok, "", "42"} = Eval.eval(source)
  end

  test "renders a dependent compiler diagnostic" do
    source = """
    mod SiteEvalCurrentDiagnostic
      fn main() -> Int = missing_value
    """

    assert {:error, message} = Eval.eval(source)
    assert message =~ "UNKNOWN VALUE"
    assert message =~ "missing_value"
  end
end
