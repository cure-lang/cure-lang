defmodule CureSiteWeb.Commands.CureEvalTest do
  use ExUnit.Case, async: false

  test "compile failures retain submitted source in the diagnostic" do
    session = %Yeesh.Session{context: %{}}

    assert {:error, message, ^session} =
             CureSiteWeb.Commands.CureEval.execute(["missing_name"], session)

    assert message =~ "[E091]"
    assert message =~ "missing_name"
    assert message =~ "^^^^^^^^^^^^"
    refute message =~ "{:unknown_global"
  end
end
