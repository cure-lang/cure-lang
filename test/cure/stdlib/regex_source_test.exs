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

    regex_sources = Path.wildcard("lib/std_deps/regex/regex*.cure")

    refute File.exists?("lib/std/regex.cure")
    assert regex_sources != []

    refute Enum.any?(regex_sources, fn file ->
             source = File.read!(file)

             Enum.any?(
               ["type Regex =", "fn run_with", "fn repeat_all", "RawOptions", "ParseFailure"],
               &String.contains?(source, &1)
             )
           end)
  end

  test "thread deduplication uses intrinsic state slots rather than winner-list rescans" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

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
    assert use_meta[:home_source] =~ "lib/std_deps/regex/regex_syntax.cure"
    assert pattern_meta[:subtype] == :string
    assert flags_meta[:subtype] == :string
  end

  test "literal expansion carries checked Thompson IR into the verified parser" do
    runtime = File.read!("lib/std_deps/regex/regex_runtime.cure")
    proof = File.read!("lib/std_deps/regex/regex_proof.cure")
    emitter = File.read!("lib/std_deps/regex/regex_syntax_emitter.cure")

    assert runtime =~ "StagedRegex"
    assert runtime =~ "StagedCompilationHint"
    assert runtime =~ "type StagedMachine"
    assert runtime =~ "StagedMachineValue"
    assert proof =~ "proof_for_compilation"
    assert proof =~ "StagedCompilationHint(StagedMachineValue"
    assert emitter =~ "emit_staged_compilation"
    assert emitter =~ "emit_staged_conversion"
    assert emitter =~ "StagedMachineValue"
    assert emitter =~ "emit_staged_rows"
    refute emitter =~ ~s(runtime_call("thompson_machine")
  end

  test "generated literal artifact has no parser or Thompson dispatcher reference" do
    source = """
    mod RegexStagedArtifact
      use Std.Regex
      fn literal() = /a*/
    end
    """

    assert {:ok, env} = Program.elaborate(source)

    assert {:ok, forms} =
             Cure.Elab.Emit.compile_forms(env, :"Cure.RegexStagedArtifact", [
               :"RegexStagedArtifact#literal"
             ])

    assert {:ok, :"Cure.RegexStagedArtifact", beam, _warnings} = Cure.Compiler.BeamWriter.compile_forms(forms)

    {:beam_file, :"Cure.RegexStagedArtifact", _exports, _attrs, _info, functions} = :beam_disasm.file(beam)
    code = :erlang.term_to_binary(functions)
    refute code =~ "thompson_machine"
    refute code =~ "parse_pattern_full_verified"
    refute code =~ "certify_thompson"
  end

  test "literal expansion publishes transition rows instead of rebuilding closure machines" do
    emitter = File.read!("lib/std_deps/regex/regex_syntax_emitter.cure")

    assert emitter =~ "emit_staged_rows"
    refute emitter =~ "emit_staged_machine"
    refute emitter =~ ~s(runtime_call("concat_pattern_machine")
    refute emitter =~ ~s(runtime_call("alternate_pattern_machine")
    refute emitter =~ ~s(runtime_call("repeat_pattern_machine")
  end

  test "staged row construction builds each Thompson child once" do
    runtime = File.read!("lib/std_deps/regex/regex_runtime.cure")
    [_prefix, active] = String.split(runtime, "fn staged_machine_seed_from_compilation", parts: 2)
    [builder, _rest] = String.split(active, "fn direct_staged_rows_values_from_compilation", parts: 2)

    refute builder =~ "thompson_machine("
    assert builder =~ "let left_machine = staged_machine_seed_from_compilation(left)"
    assert builder =~ "let right_machine = staged_machine_seed_from_compilation(right)"
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
