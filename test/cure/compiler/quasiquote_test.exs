# test/cure/compiler/quasiquote_test.exs
#
# SP5.1 — quasiquotation (`quote` / `$( )`). Stage-1 parser-level fixtures.
# Red until `parse_quote` + splice lexing land (Stages 2-3). The end-to-end
# byte-identical-Core port gate is exercised separately in Stage 5.
defmodule Cure.Compiler.QuasiquoteTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp parse!(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  # Pull the body expression of `fn f(...) = <body>` out of a parsed module.
  defp body!(ast) do
    find = fn find, n ->
      case n do
        {:function_def, meta, [b]} ->
          if to_string(Keyword.get(meta, :name)) == "f", do: b, else: nil

        {_t, _m, ch} when is_list(ch) ->
          Enum.find_value(ch, &find.(find, &1))

        _ ->
          nil
      end
    end

    find.(find, ast)
  end

  # Walk a tree collecting every node whose tag is in `tags`.
  defp collect(tree, tags) do
    case tree do
      {tag, _m, ch} when is_list(ch) ->
        here = if tag in tags, do: [tree], else: []
        here ++ Enum.flat_map(ch, &collect(&1, tags))

      list when is_list(list) ->
        Enum.flat_map(list, &collect(&1, tags))

      _ ->
        []
    end
  end

  test "`quote <expr>` parses to a :quoted_syntax node wrapping the inner form" do
    ast = parse!("mod M\n  fn f() -> Syntax = quote 1\nend")
    body = body!(ast)
    assert {:quoted_syntax, _meta, [_inner]} = body
  end

  test "`$(e)` inside a quote parses to a single :splice hole carrying the expr" do
    ast = parse!("mod M\n  fn f(x: Syntax) -> Syntax = quote g($(x))\nend")
    body = body!(ast)
    assert {:quoted_syntax, _m, [_]} = body
    [splice] = collect(body, [:splice])
    assert {:splice, _sm, [{:variable, _, "x"}]} = splice
  end

  test "`$(e ...)` inside a quote parses to a :splice_group hole" do
    ast = parse!("mod M\n  fn f(xs: List(Syntax)) -> Syntax = quote g($(xs ...))\nend")
    body = body!(ast)
    [group] = collect(body, [:splice_group])
    assert {:splice_group, _gm, [{:variable, _, "xs"}]} = group
  end

  test "a quote with no splices carries no splice holes" do
    ast = parse!("mod M\n  fn f() -> Syntax = quote foo(bar)\nend")
    body = body!(ast)
    assert {:quoted_syntax, _m, [_]} = body
    assert collect(body, [:splice, :splice_group]) == []
  end

  # -- Stage 3: quote lowers to a Std.Syntax value the elaborator accepts -----

  defp elaborates?(src) do
    match?({:ok, _}, Cure.Elab.Program.elaborate(src))
  end

  test "`quote` over a literal elaborates to a Syntax value" do
    assert elaborates?("""
           mod M
             use Std.Syntax
             fn f() -> Syntax = quote 1
           end
           """)
  end

  test "`quote` over a call form elaborates to a Syntax value" do
    assert elaborates?("""
           mod M
             use Std.Syntax
             fn f() -> Syntax = quote foo(bar)
           end
           """)
  end

  test "a single `$(e)` splice elaborates, injecting the Syntax argument" do
    assert elaborates?("""
           mod M
             use Std.Syntax
             fn f(x: Syntax) -> Syntax = quote g($(x))
           end
           """)
  end

  test "a `$(xs ...)` group splice elaborates, flattening the List(Syntax)" do
    assert elaborates?("""
           mod M
             use Std.Syntax
             use Std.List
             fn f(xs: List(Syntax)) -> Syntax = quote g($(xs ...))
           end
           """)
  end

  test "a group splice followed by a static child elaborates (append shape)" do
    assert elaborates?("""
           mod M
             use Std.Syntax
             use Std.List
             fn f(xs: List(Syntax)) -> Syntax = quote g($(xs ...), bar)
           end
           """)
  end

  # -- Stage 4: a wrong-category splice is a compile error --------------------

  test "an orphan `$(e)` outside any quote is rejected with a dedicated error" do
    assert {:error, error} =
             Cure.Elab.Program.elaborate("""
             mod M
               use Std.Syntax
               fn f(x: Syntax) -> Syntax = g($(x))
             end
             """)

    assert {:splice_outside_quote, %{form: :splice}} = Cure.Elab.Program.semantic_error(error)
  end

  test "an orphan `$(xs ...)` group splice outside any quote is rejected" do
    assert {:error, error} =
             Cure.Elab.Program.elaborate("""
             mod M
               use Std.Syntax
               fn f(xs: List(Syntax)) -> Syntax = g($(xs ...))
             end
             """)

    assert {:splice_outside_quote, %{form: :splice_group}} = Cure.Elab.Program.semantic_error(error)
  end

  test "splicing a non-Syntax expression is a compile error" do
    refute elaborates?("""
           mod M
             use Std.Syntax
             fn f(n: Int) -> Syntax = quote g($(n))
           end
           """)
  end
end
