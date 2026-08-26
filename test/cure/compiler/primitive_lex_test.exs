defmodule Cure.Compiler.PrimitiveLexTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.Lexer

  test "`primitive` lexes as a keyword token" do
    {:ok, tokens} = Lexer.tokenize("primitive Int\n")
    assert Enum.any?(tokens, &match?(%{type: :keyword, value: :primitive}, &1))
  end
end
