defmodule Cure.Compiler.ErgonomicsBatchTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}

  defp parse!(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  test "leading pipes continue an expression across lines" do
    source = """
      mod Pipe
        fn value() -> Int =
          1
          |> add(2)
          |> add(3)
    """

    ast = parse!(source)

    assert {:container, _, [{:function_def, _, [body]}]} = ast
    assert {:function_call, meta, [_arg, _]} = body
    assert Keyword.take(meta, [:name, :pipe]) == [name: "add", pipe: true]
    assert %Cure.MetaAST.SourceInfo{whole: whole, operator: operator} = meta[:source_info]
    assert source_slice(source, whole) == "1\n      |> add(2)\n      |> add(3)"
    assert source_slice(source, operator) == "|>"
  end

  defp source_slice(source, span), do: binary_part(source, span.start_byte, span.end_byte - span.start_byte)

  test "where functions attach to the enclosing function" do
    ast =
      parse!("""
      mod Local
        fn value(x: Int) -> Int = helper(x)
        where
          fn helper(y: Int) -> Int = y
      """)

    assert {:container, _, [{:function_def, meta, [_]}]} = ast

    assert [%{name: "helper"}] =
             Enum.map(Keyword.get(meta, :where), fn {:function_def, m, _} -> %{name: Keyword.fetch!(m, :name)} end)
  end

  test "where functions are lambda-lifted into private sibling definitions" do
    source = """
    mod LocalCompile
      fn value(x: Int) -> Int = helper(x)
      where
        fn helper(y: Int) -> Int = y
    """

    assert {:ok, _, _warnings} = Cure.Compiler.compile_string(source)
  end

  test "where functions capture enclosing parameters" do
    source = """
    mod LocalCapture
      fn add_to(base: Int, value: Int) -> Int = helper(value)
      where
        fn helper(next: Int) -> Int = base + next

      fn result() -> Int = add_to(40, 2)
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :result, []) == 42

    refute Enum.any?(module.module_info(:exports), fn {name, _arity} ->
             String.contains?(Atom.to_string(name), "$helper$")
           end)
  end

  test "where clause functions prepend captured parameters to every clause" do
    source = """
    mod LocalClauseCapture
      fn choose(fallback: Int, values: List(Int)) -> Int = helper(values)
      where
        fn helper(items: List(Int)) -> Int
          | [] -> fallback
          | [head | _] -> head

      fn empty_result() -> Int = choose(42, [])
      fn present_result() -> Int = choose(42, [7])
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :empty_result, []) == 42
    assert apply(module, :present_result, []) == 7

    refute Enum.any?(module.module_info(:exports), fn {name, _arity} ->
             String.contains?(Atom.to_string(name), "$helper$")
           end)
  end

  test "ordinary annotation-free bindings remain accepted" do
    source = """
    mod BindingInference
      fn id(x: Int) -> Int = x
      fn use_it() -> Int =
        let value = id(1)
        value
    """

    assert {:ok, _, _} = Cure.Compiler.compile_string(source)
  end
end
