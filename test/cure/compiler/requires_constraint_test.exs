defmodule Cure.Compiler.RequiresConstraintTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser, Printer}

  defp parse!(source) do
    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  test "requires carries multiple function interface constraints" do
    ast = parse!("fn choose(a: t, b: t) -> String requires Comparable(t), Show(t) = show(a)")
    assert {:function_def, meta, [_]} = ast
    assert [comparable, show] = meta[:constraints]
    assert {:function_call, comparable_meta, _} = comparable
    assert {:function_call, show_meta, _} = show
    assert comparable_meta[:name] == "Comparable"
    assert show_meta[:name] == "Show"
  end

  test "printer canonicalizes legacy constraint where to requires" do
    ast = parse!("fn same(a: t, b: t) -> Bool where Equatable(t) = a == b")
    rendered = Printer.quoted_to_string(ast)
    assert rendered =~ "requires Equatable(t)"
    refute rendered =~ " where Equatable(t)"
  end

  test "legacy constraint-position where emits a migration event" do
    Cure.Pipeline.Events.subscribe(:parser, :deprecation)
    assert {:ok, tokens} = Lexer.tokenize("fn same(a: t) -> t where Eq(t) = a", emit_events: false)
    assert {:ok, _ast} = Parser.parse(tokens, emit_events: true)

    assert_receive {
      Cure.Pipeline.Events,
      :parser,
      :deprecation,
      {:constraint_where_deprecated, message, _location},
      _meta
    }

    assert message =~ "write `requires`"
  end

  test "implementation requirements use requires" do
    ast =
      parse!("""
      implementation Show for Box(t) requires Show(t)
        fn show(value: Box(t)) -> String = "box"
      """)

    assert {:implementation, meta, _} = ast
    assert [_] = meta[:constraints]
    assert Printer.quoted_to_string(ast) =~ "implementation Show for Box(t) requires Show(t)"
  end
end
