defmodule Cure.Compiler.GroupDecoratorTest do
  @moduledoc """
  `@group(:g)` placed ABOVE `mod` attaches to the module container (spec
  2026-07-10-group-decorator-placement). This test file grows across the
  expand→migrate→contract tasks; the in-body placement is a tolerated deprecation
  (parses, emits `E-GROUP-PLACEMENT`) so `cure migrate` can hoist it.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}

  # Parse a source string to its AST, asserting no parse errors.
  defp parse!(src) do
    {:ok, tokens} = Lexer.tokenize(src)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  # Parse a source string and return the parser's error list ({:ok, _} -> []).
  defp parse_errors(src) do
    {:ok, tokens} = Lexer.tokenize(src)

    case Parser.parse(tokens, emit_events: false) do
      {:ok, _ast} -> []
      {:error, errors} -> errors
    end
  end

  # The module container node in a parsed program (unwraps a {:block, _, items}).
  defp module_node(ast) do
    items =
      case ast do
        {:block, _, xs} -> xs
        xs when is_list(xs) -> xs
        other -> [other]
      end

    Enum.find(items, &match?({:container, meta, _} when is_list(meta), &1))
  end

  test "@group above mod attaches the group to the module container meta" do
    ast = parse!("@group(:core)\nmod M\n  fn f(x: Int) -> Int = x\nend\n")
    {:container, meta, _body} = module_node(ast)
    assert {:decorator, [name: :group], [{:literal, _, :core}]} = Keyword.get(meta, :decorator)
  end

  test "@group inside the mod body is tolerated (deprecated), not a hard error" do
    src = "mod M\n  @group(:core)\n  fn f(x: Int) -> Int = x\nend\n"

    assert parse_errors(src) == [],
           "in-body @group must parse so the @group-hoist migration can relocate it"

    # It survives as an un-hoisted in-body decorator node, ready for the migration.
    assert deep_has_decorator?(parse!(src)),
           "expected the in-body @group to remain as a :decorator node"
  end

  # True iff the tree carries a `{:decorator, meta, _}` node naming `group`.
  defp deep_has_decorator?({:decorator, meta, _}), do: Keyword.get(meta, :name) in [:group, "group"]
  defp deep_has_decorator?({_tag, _meta, children}), do: deep_has_decorator?(children)
  defp deep_has_decorator?(list) when is_list(list), do: Enum.any?(list, &deep_has_decorator?/1)
  defp deep_has_decorator?(_), do: false
end
