defmodule Cure.Compiler.Printer.ReservedWordsTest do
  @moduledoc """
  A function may be *named* with a reserved word via a backtick escape (see
  `test/cure/elab/backtick_operator_names_test.exs`). The printer must re-emit
  the backticks, or the name it prints re-lexes as the keyword/operator token
  and the source no longer reparses as the same definition.

  The words below are the ones a hand-maintained copy of the keyword list used
  to miss. The printer asks `Cure.Compiler.Lexer.reserved_word?/1` instead of
  keeping its own list, so this pins the round-trip rather than the membership:
  a word added to the lexer and nowhere else must still survive it.
  """
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser, Printer}

  @words ~w(opaque primitive quote band bor bxor bsl bsr bnot not and or)

  defp parse!(src) do
    {:ok, toks} = Lexer.tokenize(src, file: "m.cure", emit_events: false)
    {:ok, ast} = Parser.parse(toks, file: "m.cure", emit_events: false)
    ast
  end

  # The parser wraps a compilation unit in a block; the module container is the
  # child that carries the definitions.
  defp container_body({:block, _meta, children}) do
    Enum.find_value(children, fn
      {:container, _meta, body} -> body
      _ -> nil
    end)
  end

  defp container_body({:container, _meta, body}), do: body

  defp defines_function?(body, name) do
    Enum.any?(body, fn
      {:function_def, meta, _} -> Keyword.get(meta, :name) == name
      _ -> false
    end)
  end

  for word <- @words do
    test "a function named `#{word}` is printed backtick-quoted so it re-parses" do
      word = unquote(word)

      assert Lexer.reserved_word?(word),
             "the premise of this test: #{word} is a reserved word"

      out = parse!("mod M\n  fn `#{word}`(a: Int, b: Int) -> Int = a\nend\n") |> Printer.quoted_to_string()

      assert out =~ "`#{word}`",
             "expected printed source to backtick-quote the reserved name #{word}, got:\n#{out}"

      # The round-trip contract: printed source must re-lex and re-parse to the
      # same definition, not misparse because the bare name lexes as a keyword.
      body = out |> parse!() |> container_body()

      assert is_list(body), "expected the re-parsed AST to contain a module container, got:\n#{out}"

      assert defines_function?(body, word),
             "expected the re-parsed AST to still define #{word}, got:\n#{out}"
    end
  end
end
