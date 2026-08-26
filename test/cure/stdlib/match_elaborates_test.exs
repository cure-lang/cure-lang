defmodule Cure.Stdlib.MatchElaboratesTest do
  use ExUnit.Case, async: false

  alias Cure.Elab.Program

  @moduletag :stdlib

  test "lib/std/match.cure elaborates through the dependent pipeline" do
    src = File.read!("lib/std/match.cure")
    assert {:ok, _env} = Program.elaborate(src)
  end
end
