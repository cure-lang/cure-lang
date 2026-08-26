defmodule Cure.Compiler.InfixContinuationLayoutTest do
  @moduledoc """
  A trailing infix operator lets its operand sit on the next line, which means
  erasing the layout the lexer emitted between them. `infix_multiline_test`
  covers that the continuation parses; these tests cover the two things that
  parse either way and so need the AST asserted: the erasure must not reach
  past operand position, and it must not change how a chain associates.
  """

  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}

  defp parse(source) do
    with {:ok, tokens} <- Lexer.tokenize(source, emit_events: false) do
      Parser.parse(tokens, emit_events: false)
    end
  end

  describe "layout erasure stays inside operand position" do
    # `lib/std/operators.cure` declares `infix `>` : Comparison`, and the
    # closing angle bracket of a `<name: Type>` binder lexes as the same `:gt`.
    # Erasing layout after it deletes the `:indent` that opens the macro body,
    # the family parses as empty, and the first field line raises
    # `{:expected, :syntax_rule, …}`.
    test "a macro header closing a binder keeps its indented body" do
      assert {:ok, _ast} =
               parse("""
               mod T
                 macro app <name: ModuleName>
                   syntax family ApplicationDefinition
                     root ModuleName
                   accepts ApplicationDefinition
                   expands with derive_application_family
               """)
    end

    test "a syntax rule closing a binder keeps the field lines under it" do
      assert {:ok, _ast} =
               parse("""
               mod T
                 macro actor <name: ModuleName>
                   syntax family QueryDefinition
                     syntax on_call <request: Name> returns <reply_type: Type>
                     reply Expression
                   accepts QueryDefinition
                   expands with derive_query_family
               """)
    end
  end

  describe "the continuation's AST matches the single-line spelling" do
    test "a trailing dot takes the next line as its field, not as a statement" do
      assert {:ok, ast} = parse("value.\n  field")
      assert {:attribute_access, meta, [{:variable, _, "value"}]} = ast
      assert meta[:attribute] == "field"
    end

    test "a continuation does not close the block its operand sits in" do
      # The indented `2` makes the lexer emit an indent/dedent pair. The dedent
      # is layout the operand introduced, not the end of the branch list — if it
      # survives, the second branch lands outside the `match` and its `->`
      # raises `{:unexpected_token, :arrow, …}`.
      assert {:ok, ast} =
               parse("""
               mod T
                 fn f(n: Int) -> Int =
                   match n
                     0 -> 1 +
                       2
                     _ -> 3
               """)

      assert {:container, _meta, [{:function_def, _, [{:pattern_match, _, match_kids}]}]} = ast
      assert [{:variable, _, _} | arms] = match_kids
      assert length(arms) == 2
      assert Enum.all?(arms, &match?({:match_arm, _, _}, &1))
    end

    test "a sibling line beginning with an operator is not a continuation" do
      # `-` doubles as negation, so at the enclosing block's own level only
      # layout can say whether this line continues the one above it. Reading
      # the leading token against the fixity table instead makes every sibling
      # statement that starts with an operator lexeme — a macro production row
      # opening with `*`, say — get glued onto its predecessor. The pure
      # connectives are exempt and stay unindented; `ergonomics_batch_test`
      # covers leading `|>`.
      assert {:ok, ast} = parse("mod T\n  fn f(a: Int) -> Int =\n    a\n    - 1\n")

      assert {:container, _, [{:function_def, _, [{:block, _, stmts}]}]} = ast

      # Two statements, not one `binary_op`: that is what "not a continuation"
      # means. The second is a literal rather than a `unary_op` because a sign
      # applied directly to a numeral is folded into the literal's exact
      # descriptor (`fold_signed_numeric_literal/1`).
      assert [{:variable, _, "a"}, {:literal, _, -1}] = stmts
    end

    test "an indented line beginning with an operator continues the line above" do
      assert {:ok, ast} = parse("mod T\n  fn f(a: Int) -> Int =\n    a\n      - 1\n")

      assert {:container, _, [{:function_def, _, [{:binary_op, meta, _}]}]} = ast
      assert meta[:operator] == :-
    end

    test "a chain of continuations associates as the fixity table says" do
      assert {:ok, ast} = parse("true or\n  false or\n  true\n")

      # `or` is left-associative: `(true or false) or true`. If the layout
      # survives to the Pratt loop the sub-parse swallows the tail instead and
      # the tree silently flips to `true or (false or true)`.
      assert {:binary_op, outer, [{:binary_op, inner, [_true, _false]}, _tail]} = ast
      assert outer[:operator] == :or
      assert inner[:operator] == :or
    end
  end
end
