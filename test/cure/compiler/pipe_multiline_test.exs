defmodule Cure.Compiler.PipeMultilineTest do
  @moduledoc """
  A trailing `|>` may sit at the end of a line with its right operand on the next line, so a pipeline can span
  several lines (`a |> \\n f() |> \\n g()`). `|>` always demands a right operand, so the parser skips the
  intervening newline to find it (regression: previously `:unexpected_token :newline` after `|>`). Verifies the
  multi-line form parses AND evaluates identically to the single-line form.
  """
  use ExUnit.Case, async: true

  test "a trailing-|> pipeline spanning multiple lines parses and evaluates like the single-line form" do
    src = """
    mod PipeM
      fn double(x: Int) -> Int = x + x
      fn inc(x: Int) -> Int = x + 1
      fn one_line() -> Int = 5 |> double() |> inc()
      fn multi_line() -> Int =
        5 |>
        double() |>
        inc()
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert apply(mod, :one_line, []) == 11
    assert apply(mod, :multi_line, []) == 11
  end
end
