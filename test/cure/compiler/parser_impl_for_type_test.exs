defmodule Cure.Compiler.ParserImplForTypeTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  test "impl's meta retains the parsed for_type AST, not just its derived name" do
    src = "mod M\n  impl P for Int\n    fn e(a: Int) -> Bool = true\n"
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)
    [{:container, meta, _}] = find_impl(ast)
    assert match?({:variable, _, "Int"}, Keyword.get(meta, :for_type))
  end

  defp find_impl({:container, meta, ch} = node) do
    if Keyword.get(meta, :container_type) == :trait,
      do: [node],
      else: Enum.flat_map(ch, &find_impl/1)
  end

  defp find_impl({_, _, ch}) when is_list(ch), do: Enum.flat_map(ch, &find_impl/1)
  defp find_impl(_), do: []
end
