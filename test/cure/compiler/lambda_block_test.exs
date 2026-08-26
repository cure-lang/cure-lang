defmodule Cure.Compiler.LambdaBlockTest do
  @moduledoc """
  Tests for the v0.22.0 multi-statement lambda body surface:

    * single-expression form (unchanged from v0.19.0)
    * indented-block form (unchanged from v0.19.0)
    * brace-delimited form `fn (x) -> { s1; s2; final }`
    * `end`-terminated form `fn (x) -> s1; s2; final; end`

  Each form emits the same `{:block, [block_shape: :brace | :end, ...], exprs}`
  AST node that the v0.19.0 indented form already produced, so the rest
  of the compiler treats them uniformly.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}

  defp parse!(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  describe "single-expression body" do
    test "fn (x) -> x + 1" do
      ast = parse!("fn (x) -> x + 1")
      assert {:lambda, _, [body]} = ast
      assert match?({:binary_op, _, _}, body)
    end
  end

  describe "brace-delimited body" do
    test "wraps multiple statements in a :block node with :brace shape" do
      ast = parse!("fn (x) -> { let y = x + 1; y + 2 }")
      assert {:lambda, _, [{:block, meta, exprs}]} = ast
      assert Keyword.get(meta, :block_shape) == :brace
      assert [_, _] = exprs
    end

    test "empty braces fold to null literal" do
      ast = parse!("fn () -> { }")
      assert {:lambda, _, [{:literal, _, nil}]} = ast
    end
  end

  describe "end-terminated body" do
    test "consumes `end` after a single expression (single-expr body unwrapped)" do
      # When the block has only one statement the parser returns the
      # expression directly, matching the v0.19.0 single-expression
      # lambda shape. The `end` still terminates the body.
      ast = parse!("fn (x) -> x + 1 end")
      assert {:lambda, _, [body]} = ast
      assert match?({:binary_op, _, _}, body)
    end

    test "sequences separated by `;` terminated by `end`" do
      ast = parse!("fn (x) -> let y = x + 1; y * 2; end")
      assert {:lambda, _, [{:block, meta, exprs}]} = ast
      assert Keyword.get(meta, :block_shape) == :end
      assert [_, _] = exprs
    end
  end

  # The classic "codegen" describe block (asserting the `{:fun, …}` / `{:block, …}`
  # Erlang abstract form emitted by `Codegen.compile_expr/1`) was removed with the
  # classic pathway (#18); it was white-box-coupled to that deleted lowerer. The
  # parser coverage above stands.
end
