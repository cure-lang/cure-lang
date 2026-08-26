defmodule Cure.Compiler.ProofInductionTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser, Printer}
  alias Cure.Diagnostic.Renderer
  alias Cure.MetaAST.Metadata

  defp parse!(source) do
    assert {:ok, tokens} = Lexer.tokenize(source, file: "induction.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "induction.cure", emit_events: false)
    ast
  end

  @source """
  induction count
    case Z =>
      simplify

    case S(previous, induction_hypothesis) =>
      proof chain
        previous == previous
        because induction_hypothesis
  """

  test "induction has distinct subject, case, pattern, and body nodes" do
    assert {:induction, meta, [{:variable, _, "count"}, zero, successor]} = parse!(@source)
    info = Metadata.source_info(meta)
    assert source_slice(@source, info.whole) =~ "induction count"
    assert Enum.map(info.operands, &source_slice(@source, &1)) == ["count"]
    assert length(info.branches) == 2
    refute Keyword.has_key?(meta, :construct_span)
    refute Keyword.has_key?(meta, :subject_span)

    assert {:induction_case, zero_meta, [{:variable, _, "Z"}, {:simplify_command, _, []}]} = zero
    zero_info = Metadata.source_info(zero_meta)
    assert source_slice(@source, zero_info.whole) == "case Z =>\n    simplify"
    assert source_slice(@source, zero_info.opener) == "case"
    assert source_slice(@source, zero_info.operator) == "=>"
    assert source_slice(@source, zero_info.pattern) == "Z"
    assert source_slice(@source, zero_info.body) == "simplify"
    refute Keyword.has_key?(zero_meta, :pattern_span)
    refute Keyword.has_key?(zero_meta, :body_span)

    assert {:induction_case, successor_meta,
            [
              {:function_call, _, [{:variable, _, "previous"}, {:variable, _, "induction_hypothesis"}]},
              {:proof_chain, _, _}
            ]} = successor

    successor_info = Metadata.source_info(successor_meta)
    assert source_slice(@source, successor_info.pattern) == "S(previous, induction_hypothesis)"
    assert source_slice(@source, successor_info.operator) == "=>"
    assert source_slice(@source, successor_info.body) =~ "proof chain"
  end

  test "canonical printing round-trips induction blocks" do
    ast = parse!(@source)
    printed = Printer.quoted_to_string(ast)

    assert printed =~ "induction count"
    assert printed =~ "case S(previous, induction_hypothesis) =>"

    assert Metadata.strip_diagnostics(parse!(printed)) ==
             Metadata.strip_diagnostics(ast)
  end

  test "explicit impossible induction cases retain their coverage marker" do
    source = """
    induction witness
      case only => impossible
    """

    assert {:induction, _, [_, {:induction_case, meta, [_pattern, nil]}]} = parse!(source)
    assert meta[:impossible]
    info = Metadata.source_info(meta)
    assert source_slice(source, info.whole) == "case only => impossible"
    assert source_slice(source, info.body) == "impossible"
    assert Printer.quoted_to_string(parse!(source)) =~ "case only => impossible"
  end

  test "induction and case remain ordinary identifiers outside the block shape" do
    assert {:function_def, meta, [{:variable, _, "induction"}]} =
             parse!("fn keep(induction: Int, case: Int) -> Int = induction\n")

    assert [{:param, _, "induction"}, {:param, _, "case"}] = meta[:params]
  end

  test "an induction case gets its fat-arrow spelling and exact edit" do
    source = "induction count\n  case Z body"
    file = "induction_arrow.cure"
    {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)

    error = Enum.find(errors, &match?({:branch_arrow_missing, %{family: :induction_case}}, &1))

    assert {:branch_arrow_missing, %{family: :induction_case, expected: :fat_arrow, observed: "body"}} = error

    {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, file, source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- INDUCTION CASE ARROW IS MISSING [E094] ----------------- induction_arrow.cure

             An induction case needs `=>` between its pattern and body expression.

             A valid continuation here starts with '=>'.

             at induction_arrow.cure:2:10
             2 |   case Z body
               |   ---- - ^ this induction case starts here; the induction pattern ends here; insert `=>` before this induction case body

             Hint: Insert `=>` before the induction case body
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "=> ", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column} == {2, 10}
    assert insertion.start_byte == insertion.end_byte

    assert [%{"newText" => "=> ", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 1, "character" => 9},
             "end" => %{"line" => 1, "character" => 9}
           }
  end

  test "an induction case with no body gets no partial arrow edit" do
    source = "induction count\n  case Z"
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)
    error = Enum.find(errors, &match?({:branch_arrow_missing, %{family: :induction_case}}, &1))
    {diagnostic, _registry} = Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "nofile", source)
    assert diagnostic.suggestions == []
  end

  test "an induction branch without `case` points at the authored branch head" do
    source = "induction count\n  branch Z => simplify"
    file = "induction_case.cure"
    {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, file: file, emit_events: false)

    assert {:proof_command_syntax,
            %{
              kind: :induction_case_introducer_missing,
              expected: :case,
              observed: "branch",
              span: span
            }} = error

    assert {span.start_line, span.start_column, span.end_column} == {2, 3, 9}

    {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, file, source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- INDUCTION BRANCH NEEDS `CASE` [E094] -------------------- induction_case.cure

             Every branch in an induction block starts with `case`; 'branch' appears at the
             start of this branch.

             A valid continuation here starts with 'case'.

             at induction_case.cure:2:3
             1 | induction count
               | --------- this induction block starts here
             2 |   branch Z => simplify
               |   ^^^^^^ this induction branch must start with `case`
             """)

    assert diagnostic.suggestions == []

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 1, "character" => 2},
             "end" => %{"line" => 1, "character" => 8}
           }
  end

  defp source_slice(source, span), do: binary_part(source, span.start_byte, span.end_byte - span.start_byte)
end
