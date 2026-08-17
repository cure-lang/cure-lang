defmodule Cure.Stdlib.DependentRegexEvidenceTest do
  use ExUnit.Case, async: false

  # `Std.Regex` is two layers. The `Pattern`/`Evidence` machine below is the
  # low-level code-point layer: its *input* is `List(Char)`, so
  # `pattern_evidence` and `pattern_prefix_evidence` take one and the residual
  # suffix of a prefix match comes back as a bare charlist. The `Regex`/`parse_*`
  # surface sits on top of it typed at `String`, and `parse_pattern_full` is the
  # seam -- it calls `Std.String.characters` on its input before handing it down.
  # So the source below converts explicitly at the evidence calls and passes
  # literals straight through to `parse_pattern_full`.
  #
  # `String` is nominal -- `rec String { characters: List(Char) }` -- so it
  # erases to the tagged pair `{:String, code_points}`. Both `StringEvidence`'s
  # payload and `Sem(StringC)` are `String`, hence the tags below; the
  # per-character evidence payloads stay bare code points.
  defp cure_string(chars), do: {:String, chars}

  setup_all do
    source = """
    mod RegexEvidenceRuntime
      use Std.Regex

      fn same(expected: Char) -> Char -> Bool =
        fn(actual) -> Std.Char.same(expected, actual)

      fn atom(char: Char) -> Pattern(CharC) = PatternPredicate(same(char))
      fn ab() -> Pattern(PairC(CharC, CharC)) = PatternConcat(atom('a'), atom('b'))
      fn ambiguous() -> Pattern(ChoiceC(CharC, CharC)) = PatternAlternate(atom('a'), atom('a'))
      fn many() -> Pattern(ListC(CharC)) = PatternRepeat(atom('a'))
      fn greedy_pair() -> Pattern(PairC(ListC(CharC), CharC)) = PatternConcat(many(), atom('a'))
      fn grouped() -> Pattern(StringC) = PatternGroup(ab())
      fn nested_group() -> Pattern(StringC) = PatternGroup(PatternGroup(ab()))

      fn pair_evidence() -> Option(List(Evidence)) = pattern_evidence(ab(), Std.String.characters("ab"))
      fn ambiguous_evidence() -> Option(List(Evidence)) = pattern_evidence(ambiguous(), Std.String.characters("a"))
      fn list_evidence() -> Option(List(Evidence)) = pattern_evidence(many(), Std.String.characters("aa"))
      fn greedy_evidence() -> Option(List(Evidence)) = pattern_evidence(greedy_pair(), Std.String.characters("aa"))
      fn group_evidence() -> Option(List(Evidence)) = pattern_evidence(grouped(), Std.String.characters("ab"))
      fn nested_group_evidence() -> Option(List(Evidence)) = pattern_evidence(nested_group(), Std.String.characters("ab"))
      fn failed_evidence() -> Option(List(Evidence)) = pattern_evidence(ab(), Std.String.characters("aa"))
      fn shortest_prefix() -> Option(EvidencePrefix) = pattern_prefix_evidence(many(), Std.String.characters("aaab"), false)
      fn longest_prefix() -> Option(EvidencePrefix) = pattern_prefix_evidence(many(), Std.String.characters("aaab"), true)
      fn parsed_pair() -> Option(Tuple(Char, Char)) = parse_pattern_full(ab(), "ab")
      fn parsed_left() -> Option(Choice(Char, Char)) = parse_pattern_full(ambiguous(), "a")
      fn parsed_list() -> Option(List(Char)) = parse_pattern_full(many(), "aaa")
      fn parsed_group() -> Option(String) = parse_pattern_full(grouped(), "ab")

    end
    """

    assert {:ok, runtime_module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    {:ok, runtime_module: runtime_module}
  end

  test "concatenation emits postfix pair evidence", %{runtime_module: module} do
    assert apply(module, :pair_evidence, []) ==
             {:some, [:PairEvidence, {:CharacterEvidence, ?b}, {:CharacterEvidence, ?a}]}
  end

  test "ordered deduplication retains the left alternative's evidence", %{runtime_module: module} do
    assert apply(module, :ambiguous_evidence, []) ==
             {:some, [:LeftEvidence, {:CharacterEvidence, ?a}]}
  end

  test "repetition emits balanced list evidence", %{runtime_module: module} do
    assert apply(module, :list_evidence, []) ==
             {:some,
              [
                :EndListEvidence,
                {:CharacterEvidence, ?a},
                {:CharacterEvidence, ?a},
                :BeginListEvidence
              ]}
  end

  test "greedy repetition keeps the consuming path needed by a following atom", %{runtime_module: module} do
    assert apply(module, :greedy_evidence, []) ==
             {:some,
              [
                :PairEvidence,
                {:CharacterEvidence, ?a},
                :EndListEvidence,
                {:CharacterEvidence, ?a},
                :BeginListEvidence
              ]}
  end

  test "groups replace child evidence with the exact consumed extent", %{runtime_module: module} do
    assert apply(module, :group_evidence, []) == {:some, [{:StringEvidence, cure_string(~c"ab")}]}
    assert apply(module, :nested_group_evidence, []) == {:some, [{:StringEvidence, cure_string(~c"ab")}]}
  end

  test "failed full matches produce no evidence", %{runtime_module: module} do
    assert apply(module, :failed_evidence, []) == :none
  end

  test "prefix modes choose the first or last accepting extent", %{runtime_module: module} do
    assert apply(module, :shortest_prefix, []) ==
             {:some, {:EvidencePrefix, [:EndListEvidence, :BeginListEvidence], ~c"aaab"}}

    assert apply(module, :longest_prefix, []) ==
             {:some,
              {:EvidencePrefix,
               [
                 :EndListEvidence,
                 {:CharacterEvidence, ?a},
                 {:CharacterEvidence, ?a},
                 {:CharacterEvidence, ?a},
                 :BeginListEvidence
               ], ~c"b"}}
  end

  test "shape-indexed extraction returns Pattern values without runtime casts", %{runtime_module: module} do
    assert apply(module, :parsed_pair, []) == {:some, {?a, ?b}}
    assert apply(module, :parsed_left, []) == {:some, {:ChoseLeft, ?a}}
    assert apply(module, :parsed_list, []) == {:some, ~c"aaa"}
    assert apply(module, :parsed_group, []) == {:some, cure_string(~c"ab")}
  end

  test "successful public parsing paths do not route through the fallible decoder" do
    source = File.read!("lib/std/regex.cure")

    [pattern_full_body] =
      Regex.run(
        ~r/fn parse_pattern_full\([^\n]+\).*? =(?<body>.*?)(?=\n\n  fn parse_program_full)/s,
        source,
        capture: :all_but_first
      )

    [program_full_body] =
      Regex.run(
        ~r/fn parse_program_full\([^\n]+\).*? =(?<body>.*?)(?=\n\n  fn parse_full)/s,
        source,
        capture: :all_but_first
      )

    [prefix_body] =
      Regex.run(
        ~r/fn parse_prefix_with\([^\n]+\).*? =(?<body>.*?)(?=\n\n  fn parse_prefix)/s,
        source,
        capture: :all_but_first
      )

    [positioned_prefix_body] =
      Regex.run(
        ~r/fn parse_prefix_at\([^\n]+\).*? =(?<body>.*?)(?=\n\n  fn parse_prefix)/s,
        source,
        capture: :all_but_first
      )

    [search_prefix_body] =
      Regex.run(
        ~r/fn pattern_prefix_program_at\([^\n]+\).*? =(?<body>.*?)(?=\n\n  fn list_length)/s,
        source,
        capture: :all_but_first
      )

    refute pattern_full_body =~ "decode_pattern_encoding"
    refute pattern_full_body =~ "extract_complete_encoding"
    refute program_full_body =~ "pattern_evidence"
    refute program_full_body =~ "convert_complete_extraction"
    refute prefix_body =~ "pattern_prefix_evidence"
    refute prefix_body =~ "convert_prefix_extraction"
    refute positioned_prefix_body =~ "pattern_prefix_evidence_at"
    refute positioned_prefix_body =~ "convert_prefix_extraction"
    refute search_prefix_body =~ "pattern_prefix_evidence_at"
    refute search_prefix_body =~ "convert_prefix_chars"
  end

  test "shape certificates are erased from emitted total extraction functions" do
    module = :"Cure.Std.Regex"

    {:ok, set} =
      Cure.Compiler.Artifacts.open_verified_set(
        kind: :stdlib,
        candidates: Cure.Stdlib.Paths.beam_dirs()
      )

    artifact =
      set.modules["Std.Regex"].artifacts
      |> Enum.find(&(&1.module == Atom.to_string(module)))

    beam = File.read!(Path.join(set.artifact_root, artifact.path))
    {:beam_file, ^module, _exports, _attrs, _info, functions} = :beam_disasm.file(beam)

    extraction_names = [
      :extract_encoding_result,
      :extract_many_encoding_result,
      :extract_encoding
    ]

    extraction_code =
      for {:function, name, _arity, _label, instructions} <- functions,
          name in extraction_names,
          do: instructions

    binary = :erlang.term_to_binary(extraction_code)
    refute binary =~ "Encodes"
    refute binary =~ "EvidenceAppend"
  end
end
