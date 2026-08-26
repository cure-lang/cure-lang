defmodule Cure.Compiler.ParserDestructuringTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.MetaAST.Metadata

  defp parse!(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  describe "pin operator ^x" do
    test "pin inside match arm parses as {:pin, _, [{:variable, _, name}]}" do
      source = """
      mod M
        fn f(x: Int) -> Atom =
          match x
            ^target -> :hit
            _       -> :miss
      """

      ast = parse!(source)
      # Navigate: {:container, _, [{:function_def, _, [body]}]}
      {:container, _, body} = ast
      [fn_def | _] = body
      {:function_def, meta, [match_expr]} = fn_def
      assert Keyword.get(meta, :name) == "f"
      {:pattern_match, _, [_scrut, first_arm | _]} = match_expr
      {:match_arm, arm_meta, _body} = first_arm
      assert {:pin, _, [{:variable, _, "target"}]} = Keyword.get(arm_meta, :pattern)
    end
  end

  describe "field punning" do
    test "Point{x, y} pattern expands to x: x, y: y pairs" do
      source = """
      mod M
        fn f(p: Point) -> Int =
          match p
            Point{x, y} -> x
      """

      ast = parse!(source)
      {:container, _, [fn_def | _]} = ast
      {:function_def, _, [match_expr]} = fn_def
      {:pattern_match, _, [_scrut, arm | _]} = match_expr
      {:match_arm, arm_meta, _} = arm
      {:function_call, fn_meta, args} = Keyword.get(arm_meta, :pattern)
      assert Keyword.get(fn_meta, :record) == true
      assert Keyword.get(fn_meta, :name) == "Point"
      # Both args should be punning pairs
      args = Metadata.strip_diagnostics(args)

      assert [
               {:pair, [pun: true], [{:literal, [subtype: :symbol], :x}, {:variable, _, "x"}]},
               {:pair, [pun: true], [{:literal, [subtype: :symbol], :y}, {:variable, _, "y"}]}
             ] = args
    end
  end
end
