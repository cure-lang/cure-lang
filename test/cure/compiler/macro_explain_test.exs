# test/cure/compiler/macro_explain_test.exs
defmodule Cure.Compiler.MacroExplainTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Errors, Lexer, Parser}
  alias Cure.Diagnostic.Renderer
  alias Cure.MetaAST.Metadata

  defp parse!(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    Metadata.strip_diagnostics(ast)
  end

  defp explain_entry({:macro_def, _, rules}), do: Enum.find(rules, &(&1[:kind] == :explain))
  defp explain_entry({_t, _m, ch}) when is_list(ch), do: Enum.find_value(ch, &explain_entry/1)
  defp explain_entry(_), do: nil

  test "an explain block parses its clauses (category + keyword points) onto the macro_def" do
    node =
      parse!(
        "macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n  explain\n    Duration =>\n      \"needs a duration\"\n    keyword \"every\" =>\n      \"a repeat rule starts with every\"\n"
      )

    ex = explain_entry(node)
    assert ex, "expected an :explain entry in the macro_def rules"
    points = Enum.map(ex.clauses, & &1.point)
    assert {:category, "Duration"} in points
    assert {:keyword, "every"} in points
  end

  test "a malformed explain point (stray '=>' with no preceding point) is a recorded parse error, not a crash" do
    source =
      "macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n  explain\n    => \"oops\"\n"

    {:ok, tokens} =
      Lexer.tokenize(
        source,
        file: "explain.cure",
        emit_events: false
      )

    assert {:error, errors} = Parser.parse(tokens, emit_events: false)

    assert [
             {:macro_nested_syntax,
              %{
                kind: :macro_explain_point_invalid,
                expected: :failure_category,
                alternatives: [:keyword],
                observed: "=>",
                token_type: :fat_arrow,
                span: %Cure.Diagnostic.Span{} = span,
                opener_span: %Cure.Diagnostic.Span{},
                previous_span: %Cure.Diagnostic.Span{},
                line: 4,
                column: 5
              }} = error
           ] = errors

    assert span.start_column == 5
    assert span.end_column == 7

    {diagnostic, registry} = Errors.to_diagnostic({:parse_error, [error]}, "explain.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- MACRO EXPLANATION POINT IS INVALID [E094] ---------------------- explain.cure

             '=>' cannot name a macro failure point. Use a failure category such as
             `Duration`, or `keyword "every"` for a literal token.

             A valid continuation here starts with a failure category or a keyword.

             at explain.cure:4:5
             3 |   explain
               |   ------- this explanation block starts here
             4 |     => "oops"
               |     ^^ name the failure point before `=>`

             Hint: Write `Category => message` or `keyword "word" => message`
             """)

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 3, "character" => 4},
             "end" => %{"line" => 3, "character" => 6}
           }
  end

  alias Cure.Compiler.MacroValidate

  defp macro_def!(src) do
    node = parse!(src)

    find = fn find, n ->
      case n do
        {:macro_def, _, _} = m -> m
        {_t, _m, ch} when is_list(ch) -> Enum.find_value(ch, &find.(find, &1))
        _ -> nil
      end
    end

    find.(find, node)
  end

  test "a macro whose explain omits a hole's category is missing_diagnosis" do
    md =
      macro_def!(
        "macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n  explain\n    keyword \"every\" =>\n      \"starts with every\"\n"
      )

    assert {:error, {:missing_diagnosis, points}} = MacroValidate.check_explain_exhaustive(md)
    assert {:hole_kind, "Duration"} in points

    rendered = Errors.format_error({:missing_diagnosis, points}, "m.cure")
    assert rendered =~ "Duration"
    refute rendered =~ ":missing_diagnosis"
  end

  test "the program validation path labels the explain block and rules for missing diagnoses" do
    source =
      "macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n  explain\n    keyword \"every\" => \"starts with every\"\n"

    {:ok, tokens} = Lexer.tokenize(source, file: "missing_explain.cure", emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)

    assert {:error, {:source_context, {:missing_diagnosis, [{:hole_kind, "Duration"}]}, context} = reason} =
             MacroValidate.check_program(ast, Cure.Core.Env.empty())

    assert %{
             span: %Cure.Diagnostic.Span{},
             explain_span: %Cure.Diagnostic.Span{},
             macro_span: %Cure.Diagnostic.Span{},
             rule_spans: [%Cure.Diagnostic.Span{}]
           } = context

    {diagnostic, registry} = Errors.to_diagnostic(reason, "missing_explain.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- MACRO EXPLANATIONS ARE INCOMPLETE [E092] --------------- missing_explain.cure

             The macro does not explain every declared failure point: Duration hole.

             at missing_explain.cure:3:3
             2 |   syntax every <t: Duration> becomes Timer.repeat(t)
               |   -------------------------------------------------- this rule declares an unexplained failure point
             3 |   explain
               >   ^^^^^^^
             4 |     keyword "every" => "starts with every"
               > ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ add clauses for the unexplained failure points

             Hint: Add one `explain` clause for each listed failure point
             """)

    lsp = Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 2, "character" => 2},
             "end" => %{"line" => 3, "character" => 42}
           }

    assert length(lsp["relatedInformation"]) == 1
  end

  test "a macro whose explain covers every structural point checks clean" do
    md =
      macro_def!(
        "macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n  explain\n    Duration =>\n      \"needs a duration\"\n    keyword \"every\" =>\n      \"starts with every\"\n"
      )

    assert :ok = MacroValidate.check_explain_exhaustive(md)
  end

  test "a macro with NO explain block reports every structural point as missing" do
    md = macro_def!("macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n")
    assert {:error, {:missing_diagnosis, points}} = MacroValidate.check_explain_exhaustive(md)
    assert {:hole_kind, "Duration"} in points
    assert {:keyword, "every"} in points
  end

  test "a fail declaration adds an author diagnosis point and keeps typed params" do
    md =
      macro_def!("""
      macro Protocol
        fail ReplyBeforeRequest(state: Code)
        explain
          ReplyBeforeRequest => "a reply needs an open request"
      """)

    assert [%{kind: :fail, name: "ReplyBeforeRequest", params: [param]}, %{kind: :explain}] = elem(md, 2)

    assert {:param, [type: {:variable, [scope: :local], "Code"}], "state"} = param
    assert :ok = MacroValidate.check_explain_exhaustive(md)
  end

  test "a fail declaration without a matching explain clause is missing_diagnosis" do
    md = macro_def!("macro Protocol\n  fail ReplyBeforeRequest(state: Code)\n")

    assert {:error, {:missing_diagnosis, [{:failure, "ReplyBeforeRequest"}]}} =
             MacroValidate.check_explain_exhaustive(md)

    rendered = Errors.format_error({:missing_diagnosis, [{:failure, "ReplyBeforeRequest"}]}, "m.cure")
    assert rendered =~ "author failure `ReplyBeforeRequest`"
    refute rendered =~ ":missing_diagnosis"
  end
end
