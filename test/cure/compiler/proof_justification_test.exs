defmodule Cure.Compiler.ProofJustificationTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Errors, Lexer, Parser, Printer}
  alias Cure.Diagnostic.Renderer
  alias Cure.MetaAST.{Metadata, SourceInfo}

  @source """
  proof chain
    x == x
    because
      have fact: Equivalent(Int, x, x) = reflexive(x)
      fact
  """

  defp parse!(source) do
    assert {:ok, tokens} = Lexer.tokenize(source, file: "because.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "because.cure", emit_events: false)
    ast
  end

  test "multiline because has a dedicated statement-list node and complete range" do
    assert {:proof_chain, _, [_, {:proof_step, _, [_, _, justification]}]} = parse!(@source)
    assert {:proof_justification, meta, [have, {:variable, _, "fact"}]} = justification
    assert {:assignment, have_meta, _} = have
    assert have_meta[:have]
    assert %SourceInfo{whole: whole, body: body} = Metadata.source_info(meta)
    assert whole && body
  end

  test "formatter emits the canonical compact proposition layout and round-trips" do
    ast = parse!(@source)
    printed = Printer.quoted_to_string(ast)
    assert printed == String.trim_trailing(@source)

    assert Metadata.strip_diagnostics(parse!(printed)) ==
             Metadata.strip_diagnostics(ast)
  end

  test "directed rewrite commands parse, retain selectors, and print canonically" do
    source = """
    proof chain
      x == y
      because
        rewrite using forward_proof
        rewrite backwards using reverse_proof at 2
        rewrite using local_proof in hypothesis
        final_proof
    """

    assert {:proof_chain, _, [_, {:proof_step, _, [_, _, {:proof_justification, _, statements}]}]} =
             ast = parse!(source)

    assert [forward_command, backward_command, local_command, {:variable, _, "final_proof"}] = statements
    assert {:rewrite_command, forward, [_]} = forward_command
    assert {:rewrite_command, backward, [_]} = backward_command
    assert {:rewrite_command, local, [_]} = local_command

    assert forward[:direction] == :forward and forward[:target] == :goal
    assert backward[:direction] == :backwards and backward[:target] == {:at, 2}
    assert local[:direction] == :forward and local[:target] == {:in, "hypothesis"}

    assert %SourceInfo{fields: %{direction: forward_direction}} = Metadata.source_info(forward)
    assert %SourceInfo{fields: %{direction: backward_direction}} = Metadata.source_info(backward)
    assert slice(source, forward_direction) == "rewrite"
    assert slice(source, backward_direction) == "backwards"

    assert Enum.all?(
             [forward, backward, local],
             &match?(%SourceInfo{whole: %Cure.Diagnostic.Span{}}, Metadata.source_info(&1))
           )

    printed = Printer.quoted_to_string(ast)
    assert printed == String.trim_trailing(source)
    assert Metadata.strip_diagnostics(parse!(printed)) == Metadata.strip_diagnostics(ast)
  end

  defp slice(source, span), do: binary_part(source, span.start_byte, span.end_byte - span.start_byte)

  test "a directed rewrite missing `using` has exact labels and a machine edit" do
    source = "rewrite backwards equality_proof"
    {diagnostic, registry} = syntax_diagnostic(source, "rewrite_using.cure")

    assert diagnostic.key == :rewrite_using_missing

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- REWRITE COMMAND NEEDS `USING` [E094] --------------------- rewrite_using.cure

             A directed rewrite introduces its equality proof with `using`; 'equality_proof'
             appears where `using` belongs.

             A valid continuation here starts with 'using'.

             at rewrite_using.cure:1:19
             1 | rewrite backwards equality_proof
               | ------- --------- ^ this rewrite command starts here; the rewrite direction ends here; insert `using` before the equality proof

             Hint: Insert `using` before the equality proof
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "using ", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column, insertion.start_byte, insertion.end_byte} == {1, 19, 18, 18}

    assert [%{"newText" => "using ", "range" => range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert range == %{
             "start" => %{"line" => 0, "character" => 18},
             "end" => %{"line" => 0, "character" => 18}
           }
  end

  test "rewrite selectors distinguish an invalid occurrence from an invalid hypothesis name" do
    {occurrence, _registry} = syntax_diagnostic("rewrite using equality_proof at 0", "rewrite_at.cure")
    assert occurrence.key == :rewrite_occurrence_invalid
    assert occurrence.primary.span.start_column == 33
    assert occurrence.primary.span.end_column == 34
    assert occurrence.primary.message == "write a positive occurrence number here"
    assert occurrence.suggestions == []

    {hypothesis, _registry} = syntax_diagnostic("rewrite using equality_proof in 42", "rewrite_in.cure")
    assert hypothesis.key == :rewrite_hypothesis_name_invalid
    assert hypothesis.primary.span.start_column == 33
    assert hypothesis.primary.span.end_column == 35
    assert hypothesis.primary.message == "write the local hypothesis name here"
    assert hypothesis.suggestions == []
  end

  test "a legacy rewrite missing `in` labels both sides and inserts the unique separator" do
    source = "rewrite equality_proof\nresult"
    {diagnostic, registry} = syntax_diagnostic(source, "rewrite_in_separator.cure")

    assert diagnostic.key == :rewrite_in_missing
    assert diagnostic.primary.span.start_line == 2
    assert diagnostic.primary.span.start_column == 1

    assert Enum.map(diagnostic.secondary, & &1.message) == [
             "this rewrite command starts here",
             "the equality proof ends here"
           ]

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "in ", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column, insertion.start_byte, insertion.end_byte} == {2, 1, 23, 23}

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 1, "character" => 0},
             "end" => %{"line" => 1, "character" => 0}
           }
  end

  defp syntax_diagnostic(source, file) do
    assert {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, file: file, emit_events: false)
    Errors.to_diagnostic({:parse_error, [error]}, file, source)
  end
end
