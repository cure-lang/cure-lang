defmodule Cure.Compiler.ModuleDocDecoratorTest do
  @moduledoc """
  A leading `##` block above a module describes the MODULE, and must survive any
  decorators standing between the doc and `mod`.

  Not every decorator attaches to the declaration that follows it: `@prelude`
  above `mod` (and `@group` when another decorator intervenes) parses as a
  standalone `{:decorator, …}` sibling of the module container, which is how
  whole-module prelude membership is discovered. A doc block must not be
  consumed by that sibling — decorators are not documentable declarations — or
  the module silently loses its documentation. `lib/std/core.cure` is the real
  case: it keeps its module doc above `@group(:core)` / `@prelude`.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}

  defp module_docs(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    collect_docs(ast)
  end

  defp collect_docs({:container, meta, _body}) when is_list(meta),
    do: [Keyword.get(meta, :doc)]

  defp collect_docs({:block, _meta, items}) when is_list(items),
    do: Enum.flat_map(items, &collect_docs/1)

  defp collect_docs(list) when is_list(list), do: Enum.flat_map(list, &collect_docs/1)
  defp collect_docs(_other), do: []

  @body "mod M\n  fn f() -> Int = 1\n"

  test "a doc above @group reaches the module" do
    assert module_docs("## Doc line.\n@group(:core)\n" <> @body) == ["Doc line."]
  end

  test "a doc above @prelude reaches the module" do
    assert module_docs("## Doc line.\n@prelude\n" <> @body) == ["Doc line."]
  end

  test "a doc above stacked @group/@prelude reaches the module" do
    assert module_docs("## Doc line.\n@group(:core)\n@prelude\n" <> @body) == ["Doc line."]
    assert module_docs("## Doc line.\n@prelude\n@group(:core)\n" <> @body) == ["Doc line."]
  end

  test "a blank line splits the module doc from the first definition's doc" do
    {:ok, tokens} = Lexer.tokenize("mod M\n  ## Module.\n\n  ## Function.\n  fn f() -> Int = 1\n", emit_events: false)
    {:ok, {:container, meta, [{:function_def, fn_meta, _}]}} = Parser.parse(tokens, emit_events: false)

    assert Keyword.get(meta, :doc) == "Module."
    assert Keyword.get(fn_meta, :doc) == "Function."
  end

  test "a doc block touching the first definition documents that definition" do
    for doc <- ["  ## Adds.\n", "  ###\n  Adds.\n  ###\n"] do
      {:ok, tokens} = Lexer.tokenize("mod M\n" <> doc <> "  fn add(a: Int) -> Int = a\n", emit_events: false)
      {:ok, {:container, meta, [{:function_def, fn_meta, _}]}} = Parser.parse(tokens, emit_events: false)

      assert Keyword.get(meta, :doc) == nil
      assert Keyword.get(fn_meta, :doc) == "Adds."
    end
  end

  test "a lone doc block followed by a blank line documents the module" do
    {:ok, tokens} = Lexer.tokenize("mod M\n  ## Module.\n\n  fn f() -> Int = 1\n", emit_events: false)
    {:ok, {:container, meta, [{:function_def, fn_meta, _}]}} = Parser.parse(tokens, emit_events: false)

    assert Keyword.get(meta, :doc) == "Module."
    assert Keyword.get(fn_meta, :doc) == nil
  end
end
