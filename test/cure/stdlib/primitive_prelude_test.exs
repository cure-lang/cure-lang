defmodule Cure.Stdlib.PrimitivePreludeTest do
  @moduledoc """
  Std.Binary is wholesale auto-preluded (spec 2026-07-10-primitive-type-
  declarations §3): `Binary`, `to_binary`/`from_binary`, and `Char` are all
  available in a bare module with no `use`.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  test "to_binary and Char are available with no `use`" do
    src = "mod M\n  fn enc(cs: List(Char)) -> Binary = to_binary(cs)\nend\n"
    assert {:ok, _env} = Program.elaborate(src)
  end
end
