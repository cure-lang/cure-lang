defmodule Cure.Stdlib.RegexSourceTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.Program

  test "the legacy regex engines and OTP runtime wrapper are absent" do
    legacy = Path.expand("../../../lib/cure/stdlib/cure_std_regex.ex", __DIR__)

    refute File.exists?(legacy)

    refute Enum.any?(Path.wildcard("lib/**/*.ex"), fn file ->
             File.read!(file) =~ ":re."
           end)

    regex_sources = Path.wildcard("lib/std/regex*.cure")

    refute Enum.any?(regex_sources, fn file ->
             source = File.read!(file)

             Enum.any?(
               ["type Regex =", "fn run_with", "fn repeat_all", "RawOptions", "ParseFailure"],
               &String.contains?(source, &1)
             )
           end)
  end

  test "thread deduplication uses intrinsic state slots rather than winner-list rescans" do
    source = File.read!("lib/std/regex.cure")

    assert source =~ "type ActiveWinnerSlots"
    assert source =~ "fn active_winner_seen"
    assert source =~ "fn record_active_winner"
    refute source =~ "fn contains_thread_state"
    refute source =~ "fn distinct_threads_seen"
  end

  test "slash literals retain the staged computed expansion entry" do
    {:ok, tokens} = Lexer.tokenize("fn f() = /[A-z]*/", emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)

    assert {:function_def, _meta,
            [
              {:computed_use, use_meta,
               [
                 {:variable, _, "expand_literal"},
                 {:macro_input, _,
                  [
                    {:literal, pattern_meta, "[A-z]*"},
                    {:literal, flags_meta, ""}
                  ]}
               ]}
            ]} = ast

    assert use_meta[:keyword] == "regex"
    assert use_meta[:home_source] =~ "lib/std/regex_syntax.cure"
    assert pattern_meta[:subtype] == :string
    assert flags_meta[:subtype] == :string
  end

  @tag timeout: 600_000
  test "a slash literal expands and elaborates without importing Std.Regex" do
    source = """
    mod RegexLiteralWithoutUse
      fn literal() = /a/
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  @tag timeout: 600_000
  test "a slash literal does not leak Std.Regex bare names into caller scope" do
    source = """
    mod RegexLiteralScope
      fn literal() = /a/
      fn leaked() -> RegexOptions = default_options()
    end
    """

    assert {:error, _diagnostic} = Program.elaborate(source)
  end

  @tag timeout: 600_000
  test "word-boundary and class-backspace syntax expand during elaboration" do
    source = """
    mod RegexBoundaryLiteralExpansion
      fn word_start() = /\\bcat\\B/
      fn unicode_word() = /\\bé\\b/u
      fn class_backspace() = /[\\b]/
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end
end
