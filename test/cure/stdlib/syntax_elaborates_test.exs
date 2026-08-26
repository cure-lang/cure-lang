defmodule Cure.Stdlib.SyntaxElaboratesTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  test "Std.Syntax elaborates on the dependent pipeline" do
    assert {:ok, _env} = Program.elaborate(File.read!("lib/std/syntax.cure"))
  end
end
