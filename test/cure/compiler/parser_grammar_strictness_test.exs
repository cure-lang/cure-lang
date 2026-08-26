defmodule Cure.Compiler.ParserGrammarStrictnessTest do
  @moduledoc """
  Two ways the parser accepted syntax the spec forbids.

  **A keyword slot that checked only the token type.** `expect(state, expected_type)`
  compares `token.type` and never `token.value`, so `expect(state, :keyword)` in a slot
  documented — by the comment directly above it — as consuming one specific keyword
  swallowed *any* keyword. `impl Show when Int` parsed as `impl Show for Int`. No error
  was recorded, and since the keyword's value never reaches the AST, no later stage could
  notice the substitution either. `expect_keyword/2`, which checks both, already existed
  and was already used elsewhere. The implementation forms still use it for `for`.
  Supervisor children have since moved to source-defined syntax-family productions;
  their literal `as` segment is checked by that grammar matcher instead.

  **Non-associativity that was never implemented.** The spec's operator table and
  `Precedence`'s moduledoc both say comparison, range, and the Melquiades send are
  non-associative and that the parser rejects chaining. It didn't. `right_bp = left_bp + 1`
  is exactly what a *left*-associative operator uses: it stops the operator from swallowing
  a peer on its own right-hand side, and does nothing to stop the Pratt loop from picking
  the freshly-built node back up as a new left operand at the caller's `min_bp`. So
  `a == b == c` left-chained, and `a <-| b <-| c` nested into two sends — the first send's
  return value re-sent to `c`, the exact fan-out `Precedence`'s moduledoc says
  non-associativity exists to prevent. Rejection now lives in the loop, where the token
  after the operator is visible.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Diagnostic.Renderer

  defp parse_raw(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    Parser.parse(tokens, emit_events: false)
  end

  defp parse!(source) do
    assert {:ok, ast} = parse_raw(source)
    ast
  end

  describe "a keyword slot accepts only its own keyword" do
    test "the documented supervisor surface accepts assignments and bare worker children" do
      source = """
      sup App.Root
        strategy = :one_for_one
        intensity = 3
        period = 5
        children
          Counter as counter
      """

      assert {:ok, _} = parse_raw(source)
    end

    test "the real compiler parser path accepts the supervisor header" do
      source = "sup App.Root\n  children []\n"
      assert {:ok, _} = Cure.Compiler.parse_source(source, file: "sup.cure")
    end

    test "`impl Proto for Type` rejects another keyword in place of `for`" do
      assert {:error, _} = parse_raw("impl Show when Int\n  fn show(x: Int) -> String = \"x\"\n")
    end

    test "`implementation Iface for Type` rejects another keyword in place of `for`" do
      assert {:error, _} =
               parse_raw("implementation Show when Int\n  fn show(x: Int) -> String = \"x\"\n")
    end

    test "a supervisor child production rejects another keyword in place of `as`" do
      assert {:error, _} =
               parse_raw("sup App.Root\n  children\n    actor Counter when counter\n")
    end

    test "the correct keyword still parses" do
      assert {:ok, _} = parse_raw("impl Show for Int\n  fn show(x: Int) -> String = \"x\"\n")
      assert {:ok, _} = parse_raw("sup App.Root\n  children\n    actor Counter as counter\n")
      assert {:ok, _} = parse_raw("sup App.Root\n  children []\n")
    end
  end

  describe "non-associative operators reject chaining" do
    test "comparison: `a == b == c`" do
      assert {:error, errors} = parse_raw("a == b == c")
      assert Enum.any?(errors, &match?({:non_associative, %{operator: :==, next_operator: :==}}, &1))
    end

    test "comparison, mixed operators at the same level: `a < b <= c`" do
      assert {:error, errors} = parse_raw("a < b <= c")
      assert Enum.any?(errors, &match?({:non_associative, %{operator: :<, next_operator: :<=}}, &1))
    end

    test "range: `a..b..c`" do
      assert {:error, errors} = parse_raw("a..b..c")
      assert Enum.any?(errors, &match?({:non_associative, %{operator: :.., next_operator: :..}}, &1))
    end

    test "Melquiades send: `a <-| b <-| c`" do
      source = "mod M\n  use Std.Otp\n  fn f(a: Int, b: Int, c: Int) -> Int = a <-| b <-| c\n"
      assert {:error, errors} = parse_raw(source)
      assert Enum.any?(errors, &match?({:non_associative, %{operator: :"<-|", next_operator: :"<-|"}}, &1))
    end

    test "the conflicting operators receive separate exact source labels" do
      source = "a == b == c"
      assert {:error, [{:non_associative, details} = reason]} = parse_raw(source)

      assert details.operator_span.start_column == 3
      assert details.operator_span.end_column == 5
      assert details.span.start_column == 8
      assert details.span.end_column == 10

      {diagnostic, registry} =
        Cure.Compiler.Errors.to_diagnostic({:parse_error, [reason]}, "operator.cure", source)

      rendered = Renderer.plain(diagnostic, registry, width: 80)
      assert diagnostic.code == "E094"
      assert diagnostic.key == :non_associative

      assert rendered ==
               String.trim_trailing("""
               -- OPERATOR CHAIN NEEDS PARENTHESES [E094] ----------------------- operator.cure

               The '==' operator cannot be chained without parentheses.

               at operator.cure:1:8
               1 | a == b == c
                 |   --   ^^ the conflicting operator is here; this second operator makes the chain ambiguous

               Hint: Add parentheses around the operation that should happen first
               """)

      lsp = Renderer.lsp(diagnostic, registry)

      assert lsp["range"] == %{
               "start" => %{"line" => 0, "character" => 7},
               "end" => %{"line" => 0, "character" => 9}
             }

      assert [%{"location" => %{"range" => first_range}, "message" => first_message}] =
               lsp["relatedInformation"]

      assert first_range == %{
               "start" => %{"line" => 0, "character" => 2},
               "end" => %{"line" => 0, "character" => 4}
             }

      assert first_message == "the conflicting operator is here"
    end
  end

  test "a bare brace explains the valid expression forms and keeps its exact source range" do
    source = "{\n"
    {:ok, tokens} = Lexer.tokenize(source, file: "unexpected.cure", emit_events: false)
    assert {:error, [{:unexpected_token, details} | _]} = Parser.parse(tokens, emit_events: false)
    assert details.observed == "{"

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [{:unexpected_token, details}]}, "unexpected.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- BRACE CANNOT START AN EXPRESSION [E094] --------------------- unexpected.cure

             A bare '{' does not begin a Cure expression. Write `Type{...}` for a record,
             `\#{...}` for a map, or use indentation for a block.

             at unexpected.cure:1:1
             1 | {
               | ^ choose record, map, or block syntax here
             """)

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 0, "character" => 0},
             "end" => %{"line" => 0, "character" => 1}
           }

    json = diagnostic |> Renderer.json() |> Jason.decode!()
    assert json["code"] == "E094"
    assert json["title"] == "Brace cannot start an expression"
    assert json["payload"]["kind"] == "bare_brace_expression"
    assert json["suggestions"] == []
  end

  test "an unmatched closing delimiter says that its opener is missing" do
    source = ")\n"
    {:ok, tokens} = Lexer.tokenize(source, file: "closer.cure", emit_events: false)
    assert {:error, [{:unexpected_token, details} | _]} = Parser.parse(tokens, emit_events: false)

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [{:unexpected_token, details}]}, "closer.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- CLOSING DELIMITER HAS NO OPENER [E094] -------------------------- closer.cure

             ')' closes a construct, but there is no matching opener here.

             at closer.cure:1:1
             1 | )
               | ^ this delimiter has nothing to close
             """)

    assert Renderer.lsp(diagnostic, registry)["data"]["key"] == "unmatched_closer"
    assert diagnostic.suggestions == []
  end

  test "a missing closing parenthesis at EOF names the construct and offers the unique insertion" do
    source = "(1"
    {:ok, tokens} = Lexer.tokenize(source, file: "unclosed.cure", emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)

    assert {:container_elements_syntax, %{kind: :container_unclosed, container: :grouped_expression, expected: :rparen}} =
             error = hd(errors)

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "unclosed.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- PARENTHESIZED EXPRESSION IS NOT CLOSED [E094] ----------------- unclosed.cure

             This parenthesized expression reaches the end of the source without its closing
             ')'.

             at unclosed.cure:1:3
             1 | (1
               | --^ this parenthesized expression starts here; the grouped expression ends here; close this parenthesized expression with `)`

             Hint: Insert `)` to close the construct
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ")", span: insertion}]}] =
             diagnostic.suggestions

    assert insertion.start_byte == 2
    assert insertion.end_byte == 2

    assert [%{"newText" => ")", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 0, "character" => 2},
             "end" => %{"line" => 0, "character" => 2}
           }
  end

  test "the real parser path replaces a mismatched closing delimiter" do
    source = "fn run(] -> Int = 1\n"
    {:ok, tokens} = Lexer.tokenize(source, file: "mismatch.cure", emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)

    assert {:expected_token, :rparen, :rbracket, "]", _line, _column, _span} =
             mismatch = Enum.find(errors, &match?({:expected_token, :rparen, :rbracket, _, _, _, _}, &1))

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [mismatch]}, "mismatch.cure", source)

    assert diagnostic.key == :mismatched_closer
    assert Renderer.plain(diagnostic, registry, width: 80) =~ "Hint: Replace ']' with `)`"

    assert [%{"newText" => ")", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 0, "character" => 7},
             "end" => %{"line" => 0, "character" => 8}
           }
  end

  test "a named function without a parameter list points before the return arrow" do
    source = "fn run -> Int = 1\n"
    {:ok, tokens} = Lexer.tokenize(source, file: "params.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:function_parameters_unparenthesized, details} = error
    assert details.function == "run"
    assert details.observed == "->"

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "params.cure", source)

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- FUNCTION PARAMETER LIST IS MISSING [E094] ----------------------- params.cure

             The function `run` needs a parenthesized parameter list after its name. Write
             `()` when it takes no parameters.

             at params.cure:1:8
             1 | fn run -> Int = 1
               |    --- ^^ this function name needs a parameter list after it; the parameter list belongs before this token

             Hint: Insert `()` after the function name
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "()", span: insertion}]}] =
             diagnostic.suggestions

    assert insertion.start_byte == 7
    assert insertion.end_byte == 7

    assert [%{"newText" => "()", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 0, "character" => 7},
             "end" => %{"line" => 0, "character" => 7}
           }
  end

  test "an unclosed function parameter list points to its opener and final parameter" do
    source = "fn run(x: Int"
    {:ok, tokens} = Lexer.tokenize(source, file: "params.cure", emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)

    error = Enum.find(errors, &match?({:container_elements_syntax, _}, &1))
    assert {:container_elements_syntax, %{kind: :container_unclosed, container: :parameters}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "params.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- FUNCTION PARAMETER LIST IS NOT CLOSED [E094] -------------------- params.cure

             This function's parameter list reaches the end of the source without its closing
             ')'.

             at params.cure:1:14
             1 | fn run(x: Int
               |       -------^ this parameter list starts here; the previous parameter ends here; close this parameter list with `)`

             Hint: Insert `)` to close the construct
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ")", span: insertion}]}] =
             diagnostic.suggestions

    assert insertion.start_byte == 13
    assert insertion.end_byte == 13
    assert length(Renderer.lsp(diagnostic, registry)["relatedInformation"]) == 2
  end

  test "adjacent function parameters get a zero-width comma insertion" do
    source = "fn run(x: Int y: Int) -> Int = 1"
    {:ok, tokens} = Lexer.tokenize(source, file: "param_separator.cure", emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)

    error = Enum.find(errors, &match?({:container_elements_syntax, _}, &1))
    assert {:container_elements_syntax, %{kind: :container_separator_missing, container: :parameters}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "param_separator.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- FUNCTION PARAMETERS NEED A COMMA [E094] ---------------- param_separator.cure

             This function has another parameter here, but consecutive parameters must be
             separated by a comma.

             at param_separator.cure:1:15
             1 | fn run(x: Int y: Int) -> Int = 1
               |       ------- ^ this parameter list starts here; the previous parameter ends here; insert a comma before this parameter

             Hint: Insert `,` between these parameters
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ", ", span: insertion}]}] =
             diagnostic.suggestions

    assert insertion.start_byte == 14
    assert insertion.end_byte == 14

    assert [%{"newText" => ", ", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 0, "character" => 14},
             "end" => %{"line" => 0, "character" => 14}
           }
  end

  test "an unclosed type application points to its argument list" do
    source = "typealias Value = Result(Int"
    {:ok, tokens} = Lexer.tokenize(source, file: "type_args.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)

    assert {:container_elements_syntax, %{kind: :container_unclosed, container: :type_arguments, type: "Result"}} =
             error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "type_args.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- TYPE APPLICATION IS NOT CLOSED [E094] ------------------------ type_args.cure

             The type application `Result` reaches the end of the source without the ')' that
             closes its arguments.

             at type_args.cure:1:29
             1 | typealias Value = Result(Int
               |                         ----^ these type arguments start here; the previous type argument ends here; close these type arguments with `)`

             Hint: Insert `)` to close the construct
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ")", span: insertion}]}] =
             diagnostic.suggestions

    assert insertion.start_byte == 28
    assert insertion.end_byte == 28
    assert length(Renderer.lsp(diagnostic, registry)["relatedInformation"]) == 2
  end

  test "adjacent type arguments get a zero-width comma insertion" do
    source = "typealias Value = Result(Int Bool)"
    {:ok, tokens} = Lexer.tokenize(source, file: "type_arg_separator.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)

    assert {:container_elements_syntax,
            %{kind: :container_separator_missing, container: :type_arguments, type: "Result"}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "type_arg_separator.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- TYPE ARGUMENTS NEED A COMMA [E094] ------------------ type_arg_separator.cure

             The type application `Result` has another argument here, but consecutive type
             arguments must be separated by a comma.

             at type_arg_separator.cure:1:30
             1 | typealias Value = Result(Int Bool)
               |                         ---- ^ these type arguments start here; the previous type argument ends here; insert a comma before this type argument

             Hint: Insert `,` between these type arguments
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ", ", span: insertion}]}] =
             diagnostic.suggestions

    assert insertion.start_byte == 29
    assert insertion.end_byte == 29

    assert [%{"newText" => ", ", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 0, "character" => 29},
             "end" => %{"line" => 0, "character" => 29}
           }
  end

  test "qualified type applications use the contextual family" do
    source = "typealias Value = Std.Result(Int"
    {:ok, tokens} = Lexer.tokenize(source, file: "qualified_type_args.cure", emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)
    error = Enum.find(errors, &match?({:container_elements_syntax, _}, &1))

    assert {:container_elements_syntax, %{kind: :container_unclosed, container: :type_arguments, type: "Std.Result"}} =
             error
  end

  test "constraint applications preserve their type and exact comma insertion" do
    source = "fn sort(xs: List) -> List requires Ord(Int Bool) = xs"
    {:ok, tokens} = Lexer.tokenize(source, file: "constraint_args.cure", emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)
    error = Enum.find(errors, &match?({:container_elements_syntax, _}, &1))

    assert {:container_elements_syntax, %{kind: :container_separator_missing, container: :type_arguments, type: "Ord"}} =
             error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "constraint_args.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- TYPE ARGUMENTS NEED A COMMA [E094] --------------------- constraint_args.cure

             The type application `Ord` has another argument here, but consecutive type
             arguments must be separated by a comma.

             at constraint_args.cure:1:44
             1 | fn sort(xs: List) -> List requires Ord(Int Bool) = xs
               |                                       ---- ^ these type arguments start here; the previous type argument ends here; insert a comma before this type argument

             Hint: Insert `,` between these type arguments
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ", ", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column} == {1, 44}
    assert insertion.start_byte == insertion.end_byte
  end

  test "qualified pattern type applications preserve their exact comma insertion" do
    source =
      "mod M\n  fn f(x: Int) -> Int = match x\n    n: Std.Pair.Pair(Int Bool) -> 1\n    _ -> 2\nend"

    {:ok, tokens} = Lexer.tokenize(source, file: "pattern_type_args.cure", emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)
    error = Enum.find(errors, &match?({:container_elements_syntax, _}, &1))

    assert {:container_elements_syntax,
            %{kind: :container_separator_missing, container: :type_arguments, type: "Std.Pair.Pair"}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "pattern_type_args.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- TYPE ARGUMENTS NEED A COMMA [E094] ------------------- pattern_type_args.cure

             The type application `Std.Pair.Pair` has another argument here, but consecutive
             type arguments must be separated by a comma.

             at pattern_type_args.cure:3:26
             3 |     n: Std.Pair.Pair(Int Bool) -> 1
               |                     ---- ^ these type arguments start here; the previous type argument ends here; insert a comma before this type argument

             Hint: Insert `,` between these type arguments
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ", ", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column} == {3, 26}
    assert insertion.start_byte == insertion.end_byte
  end

  test "a constructor-signature application inserts its closer before dedent" do
    source = "type SF indices (as: Type)\n  seq : SF(as"
    {:ok, tokens} = Lexer.tokenize(source, file: "ctor_type_args.cure", emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)
    error = Enum.find(errors, &match?({:container_elements_syntax, _}, &1))

    assert {:container_elements_syntax,
            %{kind: :container_unclosed, container: :type_arguments, type: "SF", token_type: :dedent}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "ctor_type_args.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- TYPE APPLICATION IS NOT CLOSED [E094] ------------------- ctor_type_args.cure

             The type application `SF` ends before the ')' that closes its arguments.

             at ctor_type_args.cure:2:14
             2 |   seq : SF(as
               |           ---^ these type arguments start here; the previous type argument ends here; close these type arguments with `)`

             Hint: Insert `)` to close the construct
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ")", span: insertion}]}] =
             diagnostic.suggestions

    assert insertion.start_line == 2
    assert insertion.start_column == 14
    assert insertion.start_byte == insertion.end_byte
  end

  test "an invalid lambda parameter is rejected at its authored token" do
    source = "fn(42) -> 1"
    {:ok, tokens} = Lexer.tokenize(source, file: "lambda_binder.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:invalid_parameter_name, %{lambda: true}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "lambda_binder.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- LAMBDA PARAMETER NEEDS A NAME [E094] --------------------- lambda_binder.cure

             42 cannot name a lambda parameter. Use a lower-case name such as `value`.

             at lambda_binder.cure:1:4
             1 | fn(42) -> 1
               |    ^^ write a lambda parameter name here

             Hint: Replace this with a descriptive lower-case parameter name
             """)

    assert [%{applicability: :manual, edits: []}] = diagnostic.suggestions
  end

  test "adjacent lambda parameters get a zero-width comma insertion" do
    source = "fn(x y) -> x"
    {:ok, tokens} = Lexer.tokenize(source, file: "lambda_separator.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)

    assert {:container_elements_syntax, %{kind: :container_separator_missing, container: :lambda_parameters}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "lambda_separator.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- LAMBDA PARAMETERS NEED A COMMA [E094] ----------------- lambda_separator.cure

             This lambda has another parameter here, but consecutive parameters must be
             separated by a comma.

             at lambda_separator.cure:1:6
             1 | fn(x y) -> x
               |   -- ^ this lambda parameter list starts here; the previous lambda parameter ends here; insert a comma before this lambda parameter

             Hint: Insert `,` between these lambda parameters
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ", ", span: insertion}]}] =
             diagnostic.suggestions

    assert insertion.start_byte == 5
    assert insertion.end_byte == 5
  end

  test "an unclosed lambda parameter list points to its final parameter" do
    source = "fn(x"
    {:ok, tokens} = Lexer.tokenize(source, file: "lambda_close.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:container_elements_syntax, %{kind: :container_unclosed, container: :lambda_parameters}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "lambda_close.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- LAMBDA PARAMETER LIST IS NOT CLOSED [E094] ---------------- lambda_close.cure

             This lambda's parameter list reaches the end of the source without its closing
             ')'.

             at lambda_close.cure:1:5
             1 | fn(x
               |   --^ this lambda parameter list starts here; the previous lambda parameter ends here; close this lambda parameter list with `)`

             Hint: Insert `)` to close the construct
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ")", span: insertion}]}] =
             diagnostic.suggestions

    assert insertion.start_byte == 4
    assert insertion.end_byte == 4
    assert length(Renderer.lsp(diagnostic, registry)["relatedInformation"]) == 2
  end

  test "a lambda without an arrow points between its header and body" do
    source = "fn(x) x"
    {:ok, tokens} = Lexer.tokenize(source, file: "lambda_arrow.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:lambda_arrow_missing, %{token_type: :identifier}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "lambda_arrow.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- LAMBDA ARROW IS MISSING [E094] ---------------------------- lambda_arrow.cure

             A lambda needs `->` between its parameter list and body expression.

             A valid continuation here starts with '->'.

             at lambda_arrow.cure:1:7
             1 | fn(x) x
               | --  - ^ this lambda starts here; its parameter list ends here; insert `->` before the lambda body

             Hint: Insert `->` before the lambda body
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "-> ", span: insertion}]}] =
             diagnostic.suggestions

    assert insertion.start_byte == 6
    assert insertion.end_byte == 6

    assert [%{"newText" => "-> ", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 0, "character" => 6},
             "end" => %{"line" => 0, "character" => 6}
           }
  end

  test "the malformed lambda fallback contextualizes a missing opening parenthesis" do
    source = "fn 42) -> 1"
    {:ok, tokens} = Lexer.tokenize(source, file: "lambda_open.cure", emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)

    assert Enum.any?(errors, fn
             {:lambda_parameters_unparenthesized, %{expected: :lparen}} -> true
             _ -> false
           end)
  end

  test "a missing lambda opener does not cascade into a generic closing-token error" do
    source = "fn [x) -> x"
    {:ok, tokens} = Lexer.tokenize(source, file: "lambda_recovery.cure", emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)

    assert Enum.any?(errors, &match?({:lambda_parameters_unparenthesized, _}, &1))
    refute Enum.any?(errors, &match?({:expected_token, :rparen, _, _, _, _, _}, &1))
  end

  test "an unclosed binary literal points to its opener and final segment" do
    source = "<<tag::utf8, payload"
    {:ok, tokens} = Lexer.tokenize(source, file: "binary.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)

    assert {:container_elements_syntax,
            %{kind: :container_unclosed, container: :binary_literal, expected: :binary_close}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "binary.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- BINARY LITERAL IS NOT CLOSED [E094] ----------------------------- binary.cure

             This binary literal reaches the end of the source without the '>>' that closes
             its segments.

             at binary.cure:1:21
             1 | <<tag::utf8, payload
               | --           -------^ this binary literal starts here; the previous binary segment ends here; close this binary literal with `>>`

             Hint: Insert `>>` to close the construct
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ">>", span: insertion}]}] =
             diagnostic.suggestions

    assert insertion.start_byte == 20
    assert insertion.end_byte == 20
    assert length(Renderer.lsp(diagnostic, registry)["relatedInformation"]) == 2
  end

  test "an unclosed binary generator points to its source expression" do
    source = "[b for <<b <- buf"
    {:ok, tokens} = Lexer.tokenize(source, file: "binary_generator.cure", emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)

    error =
      Enum.find(errors, fn
        {:container_elements_syntax, %{container: :binary_generator}} -> true
        _ -> false
      end)

    assert {:container_elements_syntax, %{kind: :container_unclosed, expected: :binary_close}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "binary_generator.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- BINARY GENERATOR IS NOT CLOSED [E094] ----------------- binary_generator.cure

             This binary generator reaches the end of the source without the '>>' after its
             source expression.

             at binary_generator.cure:1:18
             1 | [b for <<b <- buf
               |        --     ---^ this binary generator starts here; its source expression ends here; close this binary generator with `>>`

             Hint: Insert `>>` to close the construct
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ">>", span: insertion}]}] =
             diagnostic.suggestions

    assert insertion.start_byte == 17
    assert insertion.end_byte == 17

    assert [%{"newText" => ">>", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 0, "character" => 17},
             "end" => %{"line" => 0, "character" => 17}
           }
  end

  test "a pattern branch without an arrow points between its head and body" do
    source = "match value\n  Some(x) x"
    {:ok, tokens} = Lexer.tokenize(source, file: "match_arrow.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:branch_arrow_missing, %{family: :match_arm, token_type: :identifier}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "match_arrow.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- PATTERN BRANCH ARROW IS MISSING [E094] --------------------- match_arrow.cure

             A pattern branch needs `->` between its head and body expression.

             A valid continuation here starts with '->'.

             at match_arrow.cure:2:11
             2 |   Some(x) x
               |   ------- ^ this branch head ends here; insert `->` before this branch body

             Hint: Insert `->` before the branch body
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "-> ", span: insertion}]}] =
             diagnostic.suggestions

    assert insertion.start_byte == 22
    assert insertion.end_byte == 22
  end

  test "a pickup branch without an arrow gets the same precise repair" do
    source = "pickup\n  true 1"
    {:ok, tokens} = Lexer.tokenize(source, file: "pickup_arrow.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:branch_arrow_missing, %{family: :pickup_clause, token_type: :integer}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "pickup_arrow.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- PICKUP BRANCH ARROW IS MISSING [E094] --------------------- pickup_arrow.cure

             A pickup branch needs `->` between its head and body expression.

             A valid continuation here starts with '->'.

             at pickup_arrow.cure:2:8
             2 |   true 1
               |   ---- ^ this branch head ends here; insert `->` before this branch body

             Hint: Insert `->` before the branch body
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "-> ", span: insertion}]}] =
             diagnostic.suggestions

    assert insertion.start_byte == 14
    assert insertion.end_byte == 14

    assert [%{"newText" => "-> ", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 1, "character" => 7},
             "end" => %{"line" => 1, "character" => 7}
           }
  end

  test "a multi-clause function branch identifies its missing arrow" do
    source = "fn run(x: Int) -> Int\n  | 0 1"
    {:ok, tokens} = Lexer.tokenize(source, file: "clause_arrow.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:branch_arrow_missing, %{family: :function_clause, token_type: :integer}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "clause_arrow.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- FUNCTION CLAUSE ARROW IS MISSING [E094] ------------------- clause_arrow.cure

             A function clause needs `->` between its head and body expression.

             A valid continuation here starts with '->'.

             at clause_arrow.cure:2:7
             2 |   | 0 1
               |     - ^ this branch head ends here; insert `->` before this branch body

             Hint: Insert `->` before the branch body
             """)
  end

  test "multi-with and rematch arms retain their branch family" do
    cases = [
      {"with a b\n  Z(), Z() value", :with_arm},
      {"with a\n  Z() | VZ() value", :with_rematch_arm}
    ]

    for {source, family} <- cases do
      {:ok, tokens} = Lexer.tokenize(source, file: "with_arrow.cure", emit_events: false)
      assert {:error, errors} = Parser.parse(tokens, emit_events: false)
      error = Enum.find(errors, &match?({:branch_arrow_missing, _}, &1))
      assert {:branch_arrow_missing, %{family: ^family}} = error
    end
  end

  test "an invalid function parameter is rejected at the authored binder token" do
    source = "fn run(42) -> Int = 1\n"
    {:ok, tokens} = Lexer.tokenize(source, file: "binder.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:invalid_parameter_name, details} = error
    assert details.observed == 42

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "binder.cure", source)

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- FUNCTION PARAMETER NEEDS A NAME [E094] -------------------------- binder.cure

             42 cannot name a function parameter. Use a lower-case name such as `value`,
             optionally followed by `: Type`.

             at binder.cure:1:8
             1 | fn run(42) -> Int = 1
               |        ^^ write a parameter name here

             Hint: Replace this with a descriptive lower-case parameter name
             """)

    assert [%{applicability: :manual, edits: []}] = diagnostic.suggestions

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 0, "character" => 7},
             "end" => %{"line" => 0, "character" => 9}
           }
  end

  test "an invalid implicit parameter keeps both the brace and binder ranges" do
    source = "fn run({42}) -> Int = 1\n"
    {:ok, tokens} = Lexer.tokenize(source, file: "implicit.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:invalid_parameter_name, %{implicit: true} = details} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "implicit.cure", source)

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- FUNCTION PARAMETER NEEDS A NAME [E094] ------------------------ implicit.cure

             42 cannot name an implicit parameter. Write a lower-case binder such as `{type}`
             or `{type: Type}`.

             at implicit.cure:1:9
             1 | fn run({42}) -> Int = 1
               |        -^^ the construct starts here; write a parameter name here

             Hint: Replace this with a descriptive lower-case parameter name
             """)

    assert [related] = Renderer.lsp(diagnostic, registry)["relatedInformation"]
    assert related["message"] == "the construct starts here"

    assert related["location"]["range"] == %{
             "start" => %{"line" => 0, "character" => 7},
             "end" => %{"line" => 0, "character" => 8}
           }

    assert diagnostic.primary.span == details.span
  end

  test "a variadic marker without a binder points at the insertion boundary" do
    source = "fn run(*) -> Int = 1\n"
    {:ok, tokens} = Lexer.tokenize(source, file: "variadic.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:variadic_parameter_name_missing, %{kind: :variadic} = details} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "variadic.cure", source)

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- VARIADIC PARAMETER NEEDS A NAME [E094] ------------------------ variadic.cure

             The `*` marker must be followed by the name that receives extra positional
             arguments, for example `*values`.

             at variadic.cure:1:9
             1 | fn run(*) -> Int = 1
               |        -^ this variadic marker needs a binder; write the variadic parameter name here

             Hint: Add a descriptive lower-case name after the variadic marker
             """)

    assert [%{applicability: :manual, edits: []}] = diagnostic.suggestions

    assert diagnostic.primary.span.start_byte == 8
    assert diagnostic.primary.span.end_byte == 8
    assert details.marker_span.start_byte == 7
    assert details.marker_span.end_byte == 8

    lsp = Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 0, "character" => 8},
             "end" => %{"line" => 0, "character" => 8}
           }

    assert [%{"message" => "this variadic marker needs a binder"}] = lsp["relatedInformation"]
  end

  test "a keyword-variadic marker retains the complete two-star range" do
    source = "fn run(**) -> Int = 1\n"
    {:ok, tokens} = Lexer.tokenize(source, file: "keyword_variadic.cure", emit_events: false)
    assert {:error, [{:variadic_parameter_name_missing, details} | _]} = Parser.parse(tokens, emit_events: false)
    assert details.kind == :keyword_variadic
    assert details.marker_span.start_byte == 7
    assert details.marker_span.end_byte == 9

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic(
        {:parse_error, [{:variadic_parameter_name_missing, details}]},
        "keyword_variadic.cure",
        source
      )

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- VARIADIC PARAMETER NEEDS A NAME [E094] ---------------- keyword_variadic.cure

             The `**` marker must be followed by the name that receives extra named
             arguments, for example `**options`.

             at keyword_variadic.cure:1:10
             1 | fn run(**) -> Int = 1
               |        --^ this variadic marker needs a binder; write the variadic parameter name here

             Hint: Add a descriptive lower-case name after the variadic marker
             """)
  end

  test "a named keyword-variadic parameter reaches the intended AST form" do
    assert {:function_def, meta, _body} = parse!("fn run(**options) = 1")
    assert [{:param, parameter_meta, "options"}] = meta[:params]
    assert parameter_meta[:kind] == :keyword_variadic
  end

  test "an unclosed function call pairs EOF with its opener and offers a closing edit" do
    source = "fetch(1"
    {:ok, tokens} = Lexer.tokenize(source, file: "unclosed_call.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:call_arguments_syntax, %{kind: :call_unclosed}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "unclosed_call.cure", source)

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- FUNCTION CALL IS NOT CLOSED [E094] ----------------------- unclosed_call.cure

             The call to `fetch` reaches the end of the source without the ')' that closes
             its argument list.

             at unclosed_call.cure:1:8
             1 | fetch(1
               |      --^ this call's argument list starts here; the previous argument ends here; close this call with `)`

             Hint: Insert `)` to close the construct
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ")"}]}] =
             diagnostic.suggestions

    assert length(Renderer.lsp(diagnostic, registry)["relatedInformation"]) == 2
  end

  test "adjacent call arguments point between expressions and insert a comma" do
    source = "fetch(1 2)"
    {:ok, tokens} = Lexer.tokenize(source, file: "call_separator.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:call_arguments_syntax, %{kind: :call_argument_separator_missing}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "call_separator.cure", source)

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- CALL ARGUMENTS NEED A COMMA [E094] ---------------------- call_separator.cure

             The call to `fetch` has another argument here, but consecutive arguments must be
             separated by a comma.

             at call_separator.cure:1:9
             1 | fetch(1 2)
               |      -- ^ this call's argument list starts here; the previous argument ends here; insert a comma before this argument

             Hint: Insert `,` between these arguments
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ", ", span: insertion}]}] =
             diagnostic.suggestions

    assert insertion.start_byte == 8
    assert insertion.end_byte == 8

    assert [%{"newText" => ", ", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 0, "character" => 8},
             "end" => %{"line" => 0, "character" => 8}
           }
  end

  test "an unclosed list pairs EOF with its opener and offers a closing bracket" do
    source = "[1"
    {:ok, tokens} = Lexer.tokenize(source, file: "list.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:container_elements_syntax, %{kind: :container_unclosed, container: :list}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "list.cure", source)

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- LIST IS NOT CLOSED [E094] ----------------------------------------- list.cure

             This list reaches the end of the source without the ']' that closes its
             elements.

             at list.cure:1:3
             1 | [1
               | --^ this container starts here; the previous element ends here; close this container with `]`

             Hint: Insert `]` to close the construct
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "]"}]}] = diagnostic.suggestions
    assert length(Renderer.lsp(diagnostic, registry)["relatedInformation"]) == 2
  end

  test "adjacent tuple elements get a zero-width comma insertion" do
    source = "%[1 2]"
    {:ok, tokens} = Lexer.tokenize(source, file: "tuple.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:container_elements_syntax, %{kind: :container_separator_missing, container: :tuple}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "tuple.cure", source)

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- TUPLE ELEMENTS NEED A COMMA [E094] ------------------------------- tuple.cure

             This tuple has another element here, but consecutive elements must be separated
             by a comma.

             at tuple.cure:1:5
             1 | %[1 2]
               | --- ^ this container starts here; the previous element ends here; insert a comma before this element

             Hint: Insert `,` between these elements
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ", ", span: insertion}]}] =
             diagnostic.suggestions

    assert insertion.start_byte == 4
    assert insertion.end_byte == 4
  end

  test "list separators and tuple closers use the same contextual container family" do
    for {source, expected_kind, expected_container} <- [
          {"[1 2]", :container_separator_missing, :list},
          {"%[1", :container_unclosed, :tuple}
        ] do
      {:ok, tokens} = Lexer.tokenize(source, file: "container.cure", emit_events: false)
      assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)

      assert {:container_elements_syntax, %{kind: ^expected_kind, container: ^expected_container}} = error
    end
  end

  test "an unclosed map pairs EOF with its opener and offers a closing brace" do
    source = "%{a: 1"
    {:ok, tokens} = Lexer.tokenize(source, file: "map.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:container_elements_syntax, %{kind: :container_unclosed, container: :map}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "map.cure", source)

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- MAP IS NOT CLOSED [E094] ------------------------------------------- map.cure

             This map reaches the end of the source without the '}' that closes its entries.

             at map.cure:1:7
             1 | %{a: 1
               | ------^ this container starts here; the previous entry ends here; close this container with `}`

             Hint: Insert `}` to close the construct
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "}"}]}] =
             diagnostic.suggestions

    assert length(Renderer.lsp(diagnostic, registry)["relatedInformation"]) == 2
  end

  test "adjacent map entries get a zero-width comma insertion" do
    source = "%{a: 1 b: 2}"
    {:ok, tokens} = Lexer.tokenize(source, file: "map_separator.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:container_elements_syntax, %{kind: :container_separator_missing, container: :map}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "map_separator.cure", source)

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- MAP ENTRIES NEED A COMMA [E094] -------------------------- map_separator.cure

             This map has another entry here, but consecutive entries must be separated by a
             comma.

             at map_separator.cure:1:8
             1 | %{a: 1 b: 2}
               | ------ ^ this container starts here; the previous entry ends here; insert a comma before this entry

             Hint: Insert `,` between these entries
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ", ", span: insertion}]}] =
             diagnostic.suggestions

    assert insertion.start_byte == 7
    assert insertion.end_byte == 7

    assert [%{"newText" => ", ", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 0, "character" => 7},
             "end" => %{"line" => 0, "character" => 7}
           }
  end

  test "an unclosed record points from its opening brace to its last field" do
    source = "Point{x: 1"
    {:ok, tokens} = Lexer.tokenize(source, file: "record.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:container_elements_syntax, %{kind: :container_unclosed, container: :record}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "record.cure", source)

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- RECORD IS NOT CLOSED [E094] ------------------------------------- record.cure

             This record reaches the end of the source without the '}' that closes its
             fields.

             at record.cure:1:11
             1 | Point{x: 1
               |      -----^ this container starts here; the previous field ends here; close this container with `}`

             Hint: Insert `}` to close the construct
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "}"}]}] =
             diagnostic.suggestions

    assert length(Renderer.lsp(diagnostic, registry)["relatedInformation"]) == 2
  end

  test "adjacent record fields get a zero-width comma insertion" do
    source = "Point{x: 1 y: 2}"
    {:ok, tokens} = Lexer.tokenize(source, file: "record_separator.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:container_elements_syntax, %{kind: :container_separator_missing, container: :record}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "record_separator.cure", source)

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- RECORD FIELDS NEED A COMMA [E094] --------------------- record_separator.cure

             This record has another field here, but consecutive fields must be separated by
             a comma.

             at record_separator.cure:1:12
             1 | Point{x: 1 y: 2}
               |      ----- ^ this container starts here; the previous field ends here; insert a comma before this field

             Hint: Insert `,` between these fields
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ", ", span: insertion}]}] =
             diagnostic.suggestions

    assert insertion.start_byte == 11
    assert insertion.end_byte == 11

    assert [%{"newText" => ", ", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 0, "character" => 11},
             "end" => %{"line" => 0, "character" => 11}
           }
  end

  test "record updates use the same contextual closing-brace family" do
    source = "Point{point | x: 1"
    {:ok, tokens} = Lexer.tokenize(source, file: "record_update.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:container_elements_syntax, %{kind: :container_unclosed, container: :record}} = error
  end

  test "an unclosed list cons points to its tail expression" do
    source = "[head | tail"
    {:ok, tokens} = Lexer.tokenize(source, file: "cons.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:container_elements_syntax, %{kind: :container_unclosed, container: :list_cons}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "cons.cure", source)

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- LIST CONS IS NOT CLOSED [E094] ------------------------------------ cons.cure

             This list cons reaches the end of the source without the ']' after its tail
             expression.

             at cons.cure:1:13
             1 | [head | tail
               | -       ----^ this container starts here; the previous tail expression ends here; close this container with `]`

             Hint: Insert `]` to close the construct
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "]"}]}] =
             diagnostic.suggestions

    assert length(Renderer.lsp(diagnostic, registry)["relatedInformation"]) == 2
  end

  test "an unclosed comprehension points to its final generator clause" do
    source = "[x for x <- xs"
    {:ok, tokens} = Lexer.tokenize(source, file: "comprehension.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:container_elements_syntax, %{kind: :container_unclosed, container: :comprehension}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "comprehension.cure", source)

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- LIST COMPREHENSION IS NOT CLOSED [E094] ------------------ comprehension.cure

             This list comprehension reaches the end of the source without the ']' that
             closes its clauses.

             at comprehension.cure:1:15
             1 | [x for x <- xs
               | -      -------^ this container starts here; the previous clause ends here; close this container with `]`

             Hint: Insert `]` to close the construct
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "]"}]}] =
             diagnostic.suggestions

    assert length(Renderer.lsp(diagnostic, registry)["relatedInformation"]) == 2
  end

  test "a trailing list comma is blamed directly and can be removed safely" do
    source = "[1,]"
    {:ok, tokens} = Lexer.tokenize(source, file: "trailing_list.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)

    assert {:container_elements_syntax, %{kind: :container_trailing_separator, container: :list}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "trailing_list.cure", source)

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- LIST ENDS WITH AN EXTRA COMMA [E094] --------------------- trailing_list.cure

             This list ends immediately after a comma, but every comma must be followed by
             another element.

             at trailing_list.cure:1:3
             1 | [1,]
               | --^ this container starts here; the previous element ends here; this comma has no following element

             Hint: Remove the trailing comma
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "", span: comma_span}]}] =
             diagnostic.suggestions

    assert binary_part(source, comma_span.start_byte, comma_span.end_byte - comma_span.start_byte) == ","

    assert [%{"newText" => "", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 0, "character" => 2},
             "end" => %{"line" => 0, "character" => 3}
           }
  end

  test "a trailing tuple comma uses the tuple-specific title and complete marker range" do
    source = "%[1,]"
    {:ok, tokens} = Lexer.tokenize(source, file: "trailing_tuple.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)

    assert {:container_elements_syntax, %{kind: :container_trailing_separator, container: :tuple}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "trailing_tuple.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) =~ "-- TUPLE ENDS WITH AN EXTRA COMMA [E094]"
    assert length(Renderer.lsp(diagnostic, registry)["relatedInformation"]) == 2
  end

  describe "associative operators still chain" do
    test "`a + b + c` left-associates" do
      assert {:binary_op, _, [{:binary_op, _, [_a, _b]}, _c]} = parse!("a + b + c")
    end

    test "`a + b == c + d` groups the comparison outermost" do
      assert {:binary_op, meta, [{:binary_op, _, _}, {:binary_op, _, _}]} = parse!("a + b == c + d")
      assert Keyword.get(meta, :operator) == :==
    end

    test "a single comparison of two arithmetic chains is not a chain" do
      assert {:ok, _} = parse_raw("a * b < c * d")
    end

    test "comparisons joined by `and` are not a chain" do
      assert {:ok, _} = parse_raw("a < b and b < c")
    end
  end
end
