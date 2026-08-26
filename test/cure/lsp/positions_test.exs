defmodule Cure.LSP.PositionsTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.Span
  alias Cure.LSP.Positions
  alias Cure.LSP.Symbols

  test "converts source spans to all negotiated encodings" do
    source = "😀 café\nfn main() = 1\n"
    start_byte = byte_size("😀 ")
    end_byte = start_byte + byte_size("café")

    span =
      Span.new(
        source_id: :test,
        start_byte: start_byte,
        end_byte: end_byte,
        start_line: 1,
        start_column: 3,
        end_line: 1,
        end_column: 7
      )

    assert Positions.range(span, source, :utf8) == %{
             "start" => %{"line" => 0, "character" => 5},
             "end" => %{"line" => 0, "character" => 10}
           }

    assert Positions.range(span, source, :utf16) == %{
             "start" => %{"line" => 0, "character" => 3},
             "end" => %{"line" => 0, "character" => 7}
           }

    assert Positions.range(span, source, :utf32) == %{
             "start" => %{"line" => 0, "character" => 2},
             "end" => %{"line" => 0, "character" => 6}
           }
  end

  test "line fallback ends at the source line rather than a sentinel" do
    assert Positions.line_range(2, "mod M\n  fn main() = 1", :utf16)["end"] == %{"line" => 1, "character" => 15}
  end

  test "CRLF terminators are not counted as line characters" do
    source = "mod M\r\n  fn main() = 1\r\n"

    span =
      Span.new(
        source_id: :crlf,
        start_byte: byte_size("mod M\r\n"),
        end_byte: byte_size("mod M\r\n  fn main() = 1"),
        start_line: 2,
        start_column: 1,
        end_line: 2,
        end_column: 16
      )

    assert Positions.line_range(2, source, :utf8)["end"] == %{"line" => 1, "character" => 15}
    assert Positions.line_range(2, source, :utf16)["end"] == %{"line" => 1, "character" => 15}
    assert Positions.range(span, source, :utf8)["end"] == %{"line" => 1, "character" => 15}
  end

  test "document symbols use authored spans" do
    source = "mod M\n  fn main() -> Int = 1\n"
    {:ok, tokens} = Cure.Compiler.Lexer.tokenize(source, emit_events: false)
    {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)
    [module] = Symbols.extract(ast, source, :utf16)
    [function] = module["children"]

    refute inspect(module) =~ "999"
    assert module["range"]["start"] == %{"line" => 0, "character" => 0}
    assert function["range"]["start"] == %{"line" => 1, "character" => 2}
    assert function["selectionRange"]["start"] == %{"line" => 1, "character" => 5}
  end
end
