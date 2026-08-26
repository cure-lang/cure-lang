defmodule Cure.Compiler.BuiltinDecoratorParseTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  # Walk the top-level {:container, [container_type: :module], body} wrapper's
  # body for an enum container named `name`.
  defp find_type_decl(ast, name) do
    body =
      case ast do
        {:container, _meta, body} -> body
        list when is_list(list) -> list
        _ -> []
      end

    Enum.find(body, fn
      {:container, meta, _variants} ->
        Keyword.get(meta, :container_type) == :enum and Keyword.get(meta, :name) == name

      _ ->
        false
    end)
  end

  test "@builtin(:bool) attaches to the following type declaration" do
    src = "mod M\n  @builtin(:bool)\n  type Bool = False | True\n"
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    type_node = find_type_decl(ast, "Bool")
    assert type_node != nil, "expected an enum container named Bool in #{inspect(ast)}"
    assert {:decorator, [name: :builtin], [{:literal, _, :bool}]} = Keyword.get(elem(type_node, 1), :decorator)
  end
end
