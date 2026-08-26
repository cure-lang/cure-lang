defmodule Cure.Stdlib.DependentRegexAssertionDecisionTest do
  use ExUnit.Case, async: false

  setup_all do
    source = ~S'''
    mod RegexAssertionDecisions
      use Std.Regex.Core
      use Std.Regex.Runtime

      fn positive_decision() -> Bool = match lookaround_search_decision(
        2,
        1,
        predicate_pattern_machine(fn(char) -> char == 'a'),
        subject_initial_position(),
        ['a'],
        [],
        [],
        [],
        AnyUnicodeNewline()
      )
        LookbehindSatisfied(_) -> true
        LookbehindRefuted(_) -> false

      fn negative_decision() -> Bool = match lookaround_search_decision(
        2,
        1,
        predicate_pattern_machine(fn(char) -> char == 'a'),
        subject_initial_position(),
        ['b'],
        [],
        [],
        [],
        AnyUnicodeNewline()
      )
        LookbehindSatisfied(_) -> false
        LookbehindRefuted(_) -> true

      fn negative_certificate_context() -> Bool = match lookaround_search_decision(
        2,
        1,
        predicate_pattern_machine(fn(char) -> char == 'a'),
        subject_initial_position(),
        ['b'],
        [],
        [],
        [],
        AnyUnicodeNewline()
      )
        LookbehindRefuted(LookbehindSearchExhausted(_, ['b'], [], [], AnyUnicodeNewline(), _)) -> true
        _ -> false

      fn nested_decision_evidence() -> Bool =
        let inner_machine = predicate_pattern_machine(fn(char) -> char == 'a')
        let constraint = BoundaryConstraint(false, false, false, false, false, false, false, false, false, AnyUnicodeNewline(), None(), Some(LookaheadCondition(true, %[1, inner_machine])))
        match lookaround_constraint_nested_decisions(
          2,
          constraint,
          position_boundary_for_history(subject_initial_position(), ['a'], []),
          ['a'],
          [],
          [],
          AnyUnicodeNewline()
        )
          [LookaheadNestedDecision(true, _)] -> true
          _ -> false

    end
    '''

    assert {:ok, runtime_module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    {:ok, runtime_module: runtime_module}
  end

  test "successful assertion decisions carry finite path evidence", %{runtime_module: module} do
    assert apply(module, :positive_decision, [])
    assert apply(module, :negative_decision, [])
    assert apply(module, :negative_certificate_context, [])
    assert apply(module, :nested_decision_evidence, [])
  end

  test "refutation branches retain a typed traversal-spine witness" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    assert Regex.match?(
             ~r/LookaroundPathDestinationActiveRejected\s*:.*?MachineStateMembers/s,
             source
           )

    assert Regex.match?(
             ~r/LookaroundPathDestinationAcceptedRejected\s*:.*?MachineStateMembers/s,
             source
           )

    assert Regex.match?(~r/LookaroundSearchActiveRejected\s*:.*?MachineStateMembers/s, source)
    assert Regex.match?(~r/LookaroundSearchAcceptedRejected\s*:.*?MachineStateMembers/s, source)
    assert Regex.match?(~r/LookaroundPathExhausted\s*:.*?ThreadActive\(source\)/s, source)
  end

  test "accepted consuming paths are indexed by an active source thread" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    assert Regex.match?(
             ~r/LookaroundAcceptedNextActive\s*:.*?\)\s*->\s*LookaroundAcceptingPath\([^\n]*ThreadActive\(source\)/s,
             source
           )

    assert Regex.match?(
             ~r/LookaroundAcceptedNextAccepted\s*:.*?\)\s*->\s*LookaroundAcceptingPath\([^\n]*ThreadActive\(source\)/s,
             source
           )

    assert Regex.match?(
             ~r/LookaroundPrefixNextActive\s*:.*?\)\s*->\s*LookaroundPrefixPath\([^\n]*ThreadActive\(source\)/s,
             source
           )

    assert Regex.match?(
             ~r/LookaroundPrefixNextAccepted\s*:.*?\)\s*->\s*LookaroundPrefixPath\([^\n]*ThreadActive\(source\)/s,
             source
           )
  end

  test "empty search refutations exclude accepting paths" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    assert Regex.match?(
             ~r/fn lookaround_search_path_excludes_empty_starts\b.*?LookaroundSearchFoundActive/s,
             source
           )

    assert Regex.match?(
             ~r/fn lookaround_search_path_excludes_empty_starts\b.*?LookaroundSearchFoundAccepted/s,
             source
           )

    assert Regex.match?(
             ~r/fn lookaround_search_failure_excludes_empty_starts\b.*?LookaroundSearchExhausted/s,
             source
           )
  end

  test "active paths cannot terminate without consuming a character" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    assert Regex.match?(
             ~r/fn impossible_lookaround_empty_active_path\b.*?LookaroundAcceptedNextActive.*?impossible/s,
             source
           )
  end

  test "path refutations retain canonical destination equations" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    assert Regex.match?(~r/LookaroundPathExhausted\s*:.*?destinations_equivalent/s, source)
    assert Regex.match?(~r/LookaroundPathStepExhausted\s*:.*?lookaround_machine_destinations/s, source)
    assert Regex.match?(~r/LookaroundPathDestinationActiveRejected\s*:.*?destinations_equivalent/s, source)
    assert Regex.match?(~r/LookaroundPathDestinationAcceptedRejected\s*:.*?destinations_equivalent/s, source)
  end
end
