defmodule Cure.Compiler.PrimitiveParseTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp parse!(src) do
    {:ok, tokens} = Lexer.tokenize(src)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  defp primitive_node(ast) do
    ast
    |> flatten()
    |> Enum.find(fn
      {:container, meta, _} when is_list(meta) ->
        Keyword.get(meta, :container_type) == :primitive

      _ ->
        false
    end)
  end

  # Unwrap {:block, _, items} / module containers to a flat node list.
  defp flatten({:block, _, items}), do: Enum.flat_map(items, &flatten/1)

  defp flatten({:container, meta, body} = c) when is_list(meta) do
    [c | Enum.flat_map(List.wrap(body), &flatten/1)]
  end

  defp flatten(other), do: [other]

  test "`primitive Int` parses to a primitive container carrying its name" do
    node = primitive_node(parse!("primitive Int\n"))
    assert {:container, meta, []} = node
    assert Keyword.get(meta, :name) == "Int"
  end

  test "`@builtin(:int) primitive Int` attaches the builtin tag to the container" do
    node = primitive_node(parse!("@builtin(:int) primitive Int\n"))
    {:container, meta, []} = node
    assert {:decorator, [name: :builtin], [{:literal, _, :int}]} = Keyword.get(meta, :decorator)
  end
end
