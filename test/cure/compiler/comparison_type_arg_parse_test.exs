defmodule Cure.Compiler.ComparisonTypeArgParseTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.MetaAST.Metadata

  # A decidable-boolean reflection type like `IsTrue(claim: Bool)` is applied to
  # a *comparison* in ordinary type positions: `-> IsTrue(5 > 0)`. Comparison and
  # boolean-connective operators must therefore parse inside a type-application
  # argument, producing the same `{:binary_op, ...}` node the expression parser
  # yields — so the index elaborator can route it through the term elaborator.

  defp parse_decl(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)

    with {:ok, ast} <- Parser.parse(toks, emit_events: false),
         do: {:ok, Metadata.strip_diagnostics(ast)}
  end

  defp collect(node, acc) do
    acc = if is_tuple(node) and tuple_size(node) == 3, do: [node | acc], else: acc

    cond do
      is_tuple(node) -> Enum.reduce(Tuple.to_list(node), acc, &collect/2)
      is_list(node) -> Enum.reduce(node, acc, &collect/2)
      true -> acc
    end
  end

  defp type_app_arg(ast, name) do
    collect(ast, [])
    |> Enum.find_value(fn
      {:function_call, [name: ^name], [arg]} -> arg
      _ -> nil
    end)
  end

  test "a comparison parses as a type-application argument" do
    src = """
    mod M
      fn five_is_positive() -> IsTrue(5 > 0) = Confirmed()
    """

    {:ok, ast} = parse_decl(src)
    arg = type_app_arg(ast, "IsTrue")

    assert {:binary_op, meta, [left, right]} = arg
    assert Keyword.get(meta, :category) == :comparison
    assert Keyword.get(meta, :operator) == :>
    assert {:literal, _, 5} = left
    assert {:literal, _, 0} = right
  end

  test "a variable comparison parses as a type-application argument" do
    src = """
    mod M
      fn is_pos(n: Int) -> IsTrue(n > 0) = Confirmed()
    """

    {:ok, ast} = parse_decl(src)
    arg = type_app_arg(ast, "IsTrue")

    assert {:binary_op, meta, [{:variable, _, "n"}, {:literal, _, 0}]} = arg
    assert Keyword.get(meta, :operator) == :>
  end

  test "a boolean conjunction of comparisons parses as a type-application argument" do
    src = """
    mod M
      fn in_range(p: Int) -> IsTrue(0 <= p and p <= 100) = Confirmed()
    """

    {:ok, ast} = parse_decl(src)
    arg = type_app_arg(ast, "IsTrue")

    assert {:binary_op, and_meta, [lhs, rhs]} = arg
    assert Keyword.get(and_meta, :category) == :boolean
    assert Keyword.get(and_meta, :operator) == :and
    assert {:binary_op, l_meta, _} = lhs
    assert Keyword.get(l_meta, :operator) == :<=
    assert {:binary_op, r_meta, _} = rhs
    assert Keyword.get(r_meta, :operator) == :<=
  end

  test "an ordinary type application is unchanged (no comparison)" do
    src = """
    mod M
      type Vector(a: Type) indices (n: Nat)
        empty : Vector(a, Z)
    """

    {:ok, ast} = parse_decl(src)
    # `Vector(a, Z)` still parses as a plain type application with variable args.
    node =
      collect(ast, [])
      |> Enum.find(fn
        {:function_call, [name: "Vector"], [_, _]} -> true
        _ -> false
      end)

    assert {:function_call, [name: "Vector"], [{:variable, _, "a"}, {:variable, _, "Z"}]} = node
  end
end
