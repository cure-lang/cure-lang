defmodule Cure.Compiler.BinaryComprehensionTest do
  @moduledoc """
  Tests for the v0.22.0 binary comprehension generator surface:

      [body for <<pattern <- source>>]

  The parser emits a `:binary_generator` qualifier node that the codegen
  lowers to Erlang's `b_generate` qualifier inside the existing `:lc`
  comprehension form.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Diagnostic.Renderer

  defp parse!(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  describe "parser" do
    test "emits :binary_generator qualifier with a :bytes pattern" do
      ast = parse!("[b for <<b <- buf>>]")
      assert {:comprehension, _, [_body | qs]} = ast
      assert [{:binary_generator, generator_meta, [pattern, source]}] = qs

      assert %Cure.MetaAST.SourceInfo{opener: %Cure.Diagnostic.Span{}, closer: %Cure.Diagnostic.Span{}} =
               Keyword.fetch!(generator_meta, :source_info)

      assert {:literal, meta, [_seg]} = pattern
      assert Keyword.get(meta, :subtype) == :bytes
      assert match?({:variable, _, "buf"}, source)
    end

    test "accepts a segment specifier" do
      ast = parse!("[w for <<w::16 <- buf>>]")
      {:comprehension, _, [_ | [{:binary_generator, _, [pattern, _]}]]} = ast
      {:literal, _, [{:bin_segment, seg_meta, _}]} = pattern
      assert Keyword.get(seg_meta, :size) != nil
    end

    test "ordinary list generators still parse" do
      ast = parse!("[x for x <- [1, 2, 3]]")
      assert {:comprehension, _, [_ | [{:generator, _, _}]]} = ast
    end

    test "a missing binary-generator arrow is one contextual error with an exact edit" do
      source = "[b for <<b buf>>]"
      file = "binary_generator_arrow.cure"
      {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
      assert {:error, errors} = Parser.parse(tokens, emit_events: false)

      assert [error] =
               Enum.filter(
                 errors,
                 &match?({:declaration_separator_missing, %{kind: :binary_generator_arrow_missing}}, &1)
               )

      assert {:declaration_separator_missing, %{kind: :binary_generator_arrow_missing, expected: "<-", observed: "buf"}} =
               error

      {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, file, source)

      assert Renderer.plain(diagnostic, registry, width: 80) ==
               String.trim_trailing("""
               -- BINARY GENERATOR NEEDS AN ARROW [E094] ---------- binary_generator_arrow.cure

               This binary generator needs `<-` between its byte pattern and source expression.

               A valid continuation here starts with '<-'.

               at binary_generator_arrow.cure:1:12
               1 | [b for <<b buf>>]
                 |        --- ^ this binary generator starts here; the binary pattern ends here; insert `<-` before this generator source

               Hint: Insert `<-` before the generator source
               """)

      assert [%{applicability: :machine_applicable, edits: [%{replacement: "<- ", span: insertion}]}] =
               diagnostic.suggestions

      assert {insertion.start_line, insertion.start_column} == {1, 12}
      assert insertion.start_byte == insertion.end_byte

      assert [%{"newText" => "<- ", "range" => edit_range}] =
               Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

      assert edit_range == %{
               "start" => %{"line" => 0, "character" => 11},
               "end" => %{"line" => 0, "character" => 11}
             }
    end

    test "a binary generator with no source does not get a partial arrow edit" do
      source = "[b for <<b>>]"
      {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
      assert {:error, errors} = Parser.parse(tokens, emit_events: false)

      error =
        Enum.find(errors, &match?({:declaration_separator_missing, %{kind: :binary_generator_arrow_missing}}, &1))

      {diagnostic, _registry} = Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "nofile", source)
      assert diagnostic.suggestions == []
    end
  end

  test "byte generators compile and evaluate through the stdlib byte view" do
    source = """
    mod BinaryComprehensionTest
      use Std.List
      fn bytes(buf: Binary) -> List(Int) = [b for <<b <- buf>>]
      fn sum(buf: Binary) -> Int = Std.List.foldl(bytes(buf), 0, fn(b) -> fn(acc) -> acc + b)
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :bytes, [<<1, 2, 3>>]) == [1, 2, 3]
    assert apply(module, :sum, [<<1, 2, 3, 4>>]) == 10
  end
end
