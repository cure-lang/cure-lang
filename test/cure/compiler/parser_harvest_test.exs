defmodule Cure.Compiler.ParserHarvestTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Compiler.Parser.BuiltinFixity

  defp harvest(src, base \\ nil) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    Parser.harvest(tokens, "test.cure", base || BuiltinFixity.table(), Cure.Edition.current())
  end

  test "harvest returns fixity declaration nodes even when a later body uses an unknown operator" do
    src = """
    mod M
      use Std.Operators
      infix `<?>` : Additive
      fn go() -> Int = 1 <?> 2
    end
    """

    nodes = harvest(src)
    fixities = for {:fixity, meta, _} <- deep(nodes), do: Keyword.get(meta, :operator)
    assert "<?>" in fixities
  end

  test "harvest surfaces import (use) nodes" do
    src = "mod M\n  use Std.Operators\nend\n"
    sources = for {:import, meta, _} <- deep(harvest(src)), do: Keyword.get(meta, :source)
    assert "Std.Operators" in sources
  end

  # deep-walk helper: flatten the AST into a node list
  defp deep(nodes) when is_list(nodes), do: Enum.flat_map(nodes, &deep/1)
  defp deep({_t, _m, children} = node) when is_list(children), do: [node | deep(children)]
  defp deep(other) when is_tuple(other), do: other |> Tuple.to_list() |> deep()
  defp deep(_), do: []
end
