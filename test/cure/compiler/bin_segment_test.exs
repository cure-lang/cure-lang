defmodule Cure.Compiler.BinSegmentTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Diagnostic.Renderer

  # -- Lexer -----------------------------------------------------------------

  describe "lexer: `::` token" do
    test "single colon stays :colon" do
      {:ok, tokens} = Lexer.tokenize("x: Int", emit_events: false)
      assert Enum.any?(tokens, &(&1.type == :colon))
      refute Enum.any?(tokens, &(&1.type == :colon_colon))
    end

    test "double colon emits :colon_colon" do
      {:ok, tokens} = Lexer.tokenize("x::utf8", emit_events: false)
      assert Enum.any?(tokens, &(&1.type == :colon_colon))
    end
  end

  # -- Parser ----------------------------------------------------------------

  describe "parser: {:bin_segment, ...} AST" do
    test "bare integer becomes a segment with default specifiers" do
      ast = parse_expr!("<<1, 2, 3>>")
      assert {:literal, meta, segments} = ast
      assert Keyword.get(meta, :subtype) == :bytes

      assert %Cure.MetaAST.SourceInfo{opener: %Cure.Diagnostic.Span{}, closer: %Cure.Diagnostic.Span{}} =
               Keyword.fetch!(meta, :source_info)

      assert [_, _, _] = segments

      Enum.each(segments, fn
        {:bin_segment, segment_meta, [_]} ->
          assert %Cure.MetaAST.SourceInfo{whole: %Cure.Diagnostic.Span{}} =
                   Keyword.fetch!(segment_meta, :source_info)
      end)
    end

    test "::utf8 is recorded as a type specifier" do
      ast = parse_expr!(~s(<<"abc"::utf8>>))
      assert {:literal, _, [{:bin_segment, meta, [_value]}]} = ast
      assert Keyword.get(meta, :type) == :utf8
    end

    test "::binary-size(n) records type and size together" do
      ast = parse_expr!("<<payload::binary-size(n)>>")
      assert {:literal, _, [{:bin_segment, meta, [_value]}]} = ast
      assert Keyword.get(meta, :type) == :binary
      # The size expression is an AST node; here it's a variable reference.
      assert {:variable, _, "n"} = Keyword.get(meta, :size)
    end

    test "::signed-big-32 chains type, signedness, endianness, and size" do
      ast = parse_expr!("<<x::signed-big-32>>")
      assert {:literal, _, [{:bin_segment, meta, [_value]}]} = ast
      assert Keyword.get(meta, :signedness) == :signed
      assert Keyword.get(meta, :endianness) == :big
      assert {:literal, _, 32} = Keyword.get(meta, :size)
    end

    test "bare integer specifier shorthand is size(n)" do
      ast = parse_expr!("<<x::8>>")
      assert {:literal, _, [{:bin_segment, meta, [_value]}]} = ast
      assert {:literal, _, 8} = Keyword.get(meta, :size)
    end

    test "multiple segments are parsed as a list of {:bin_segment, ...} nodes" do
      ast = parse_expr!("<<tag::utf8, size::16, rest::binary>>")
      assert {:literal, _, segments} = ast
      assert [_, _, _] = segments
      types = Enum.map(segments, fn {:bin_segment, m, _} -> Keyword.get(m, :type) end)
      assert types == [:utf8, nil, :binary]
      sizes = Enum.map(segments, fn {:bin_segment, m, _} -> Keyword.get(m, :size) end)
      assert match?([nil, {:literal, _, 16}, nil], sizes)
    end

    test "an unclosed call-style specifier is repaired before the binary closer" do
      source = "<<x::size(8>>"
      file = "bin_spec_close.cure"
      {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
      assert {:error, errors} = Parser.parse(tokens, emit_events: false)

      error =
        Enum.find(errors, &match?({:container_elements_syntax, %{container: :binary_specifier_arguments}}, &1))

      assert {:container_elements_syntax,
              %{
                kind: :container_unclosed,
                container: :binary_specifier_arguments,
                specifier: "size",
                observed: ">>"
              }} = error

      {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, file, source)

      assert Renderer.plain(diagnostic, registry, width: 80) ==
               String.trim_trailing("""
               -- BINARY SPECIFIER ARGUMENT IS NOT CLOSED [E094] ---------- bin_spec_close.cure

               The binary `size` specifier reaches the end of its argument without the closing
               ')'.

               at bin_spec_close.cure:1:12
               1 | <<x::size(8>>
                 |      ------^ this is the binary specifier; its argument starts here; the specifier argument ends here; close this binary specifier with `)`

               Hint: Insert `)` to close the construct
               """)

      assert [%{applicability: :machine_applicable, edits: [%{replacement: ")", span: insertion}]}] =
               diagnostic.suggestions

      assert {insertion.start_line, insertion.start_column} == {1, 12}
      assert insertion.start_byte == insertion.end_byte

      assert [%{"newText" => ")", "range" => edit_range}] =
               Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

      assert edit_range == %{
               "start" => %{"line" => 0, "character" => 11},
               "end" => %{"line" => 0, "character" => 11}
             }
    end

    test "unit specifiers share the contextual closer producer" do
      source = "<<x::unit(8>>"
      {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
      assert {:error, errors} = Parser.parse(tokens, emit_events: false)

      assert {:container_elements_syntax, %{container: :binary_specifier_arguments, specifier: "unit"}} =
               Enum.find(errors, &match?({:container_elements_syntax, %{container: :binary_specifier_arguments}}, &1))
    end
  end

  # -- Codegen + round-trip through the BEAM --------------------------------

  describe "codegen: binary construction" do
    test "<<1, 2, 3>> produces the expected binary" do
      assert eval_module_main!("""
             mod BinConst
               fn main() -> Int =
                 let bytes = <<1, 2, 3>>
                 byte_size(bytes)
             """) == 3
    end

    # Rich bit-syntax construction (`::16`, `::float`, `::size(n)`, …) is a
    # deferred value-surface case in the sole (dependent) pipeline: `of_bytes`
    # packs a list of 8-bit bytes and cannot express a wider segment. The
    # elaborator REJECTS a sized segment rather than silently dropping the size
    # and feeding a >255 value to `list_to_binary` (which crashed at runtime).
    test "a sized segment <<v::16>> is rejected, not mislowered" do
      assert {:error, reason} =
               Cure.Compiler.compile_and_load(
                 """
                 mod BinSize
                   fn main() -> Int =
                     let v = 258
                     let bytes = <<v::16>>
                     byte_size(bytes)
                 """,
                 emit_events: false
               )

      # Rejected at compile time (no BEAM emitted), naming the sized segment —
      # not silently lowered to `of_bytes([258])`, which crashed in
      # `list_to_binary` at runtime.
      rendered = inspect(reason)
      assert rendered =~ "bin_segment"
      assert rendered =~ "size:"
    end
  end

  # -- Helpers ---------------------------------------------------------------

  defp parse_expr!(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  defp eval_module_main!(source) do
    {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    apply(module, :main, [])
  end
end
