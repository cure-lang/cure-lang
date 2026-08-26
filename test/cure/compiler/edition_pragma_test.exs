# test/cure/compiler/edition_pragma_test.exs
defmodule Cure.Compiler.EditionPragmaTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp parse(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    Parser.parse(toks, emit_events: false)
  end

  test "a file-leading @edition pragma parses without error" do
    assert {:ok, _ast} = parse("@edition(\"2026\")\nmod M\n  fn f() -> Int = 1\n")
  end

  test "an @edition pragma that is not file-leading is a hard parse error" do
    assert {:error, errors} = parse("mod M\n  @edition(\"2026\")\n  fn f() -> Int = 1\n")
    assert Enum.any?(errors, &match?({:edition_pragma_placement, %{span: %Cure.Diagnostic.Span{}}}, &1))
  end
end
