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

    assert Regex.match?(~r/LookaroundAcceptedNextActive\s*:.*?\)\s*->\s*LookaroundAcceptingPath\([^\n]*ThreadActive\(source\)/s, source)
    assert Regex.match?(~r/LookaroundAcceptedNextAccepted\s*:.*?\)\s*->\s*LookaroundAcceptingPath\([^\n]*ThreadActive\(source\)/s, source)
    assert Regex.match?(~r/LookaroundPrefixNextActive\s*:.*?\)\s*->\s*LookaroundPrefixPath\([^\n]*ThreadActive\(source\)/s, source)
    assert Regex.match?(~r/LookaroundPrefixNextAccepted\s*:.*?\)\s*->\s*LookaroundPrefixPath\([^\n]*ThreadActive\(source\)/s, source)
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

  test "accepting paths are indexed by the candidate cursor" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    assert Regex.match?(
             ~r/type LookaroundAcceptingPath\(depth: Nat, n: Nat, machine: PatternMachine\(n\), candidates: List\(MachineState\(n\)\)\)/,
             source
           )

    assert Regex.match?(
             ~r/LookaroundAcceptedNextActive\s*:.*?edge: ListMember\(MachineState\(n\), Active\([^\n]*candidates\)/s,
             source
           )

    assert Regex.match?(~r/LookaroundAcceptedNextActive\s*:.*?members: MachineStateMembers/s, source)
    assert Regex.match?(~r/LookaroundPrefixNextActive\s*:.*?members: MachineStateMembers/s, source)
    assert Regex.match?(~r/LookaroundAcceptedNextActive\s*:.*?cursor: MachineStateCursor/s, source)
    assert Regex.match?(~r/LookaroundPrefixNextActive\s*:.*?cursor: MachineStateCursor/s, source)
  end

  test "path failures expose the generic accepting-path refutation theorem" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    assert Regex.match?(
             ~r/fn lookaround_path_failure_excludes_accepting_path\b.*?LookaroundPathFailure.*?LookaroundAcceptingPath/s,
             source
           )
  end

  test "empty member spines normalize through their canonical destination equation" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    assert Regex.match?(
             ~r/fn lookaround_empty_members_normalized\b.*?equivalence: Equivalent.*?MachineStateMembers\(n, empty_machine_states\(n\), Nil\(\)/s,
             source
           )
  end

  test "rejected path results preserve their traversal cursor" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    assert Regex.match?(
             ~r/LookaroundAcceptingPathRejected\s*:.*?MachineStateCursor/s,
             source
           )

    assert Regex.match?(
             ~r/LookaroundPrefixPathRejected\s*:.*?MachineStateCursor/s,
             source
    )
  end

  test "accepted path edges are forced to the cursor head" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")
    active = Enum.find(String.split(source, "\n"), &String.starts_with?(&1, "    LookaroundAcceptedNextActive :"))
    accepted = Enum.find(String.split(source, "\n"), &String.starts_with?(&1, "    LookaroundAcceptedNextAccepted :"))
    prefix = Enum.find(String.split(source, "\n"), &String.starts_with?(&1, "    LookaroundPrefixNextActive :"))
    prefix_accepted = Enum.find(String.split(source, "\n"), &String.starts_with?(&1, "    LookaroundPrefixNextAccepted :"))

    assert active =~ "members: MachineStateMembers"
    assert active =~ "candidate_equivalent: Equivalent(List(MachineState(n)), candidates, Cons(Active("
    assert active =~ "edge: ListMember(MachineState(n), Active("
    assert accepted =~ "candidate_equivalent: Equivalent(List(MachineState(n)), candidates, Cons(Accepted("
    assert prefix =~ "members: MachineStateMembers"
    assert prefix =~ "candidate_equivalent: Equivalent(List(MachineState(n)), candidates, Cons(Active("
    assert prefix =~ "edge: ListMember(MachineState(n), Active("
    assert prefix_accepted =~ "candidate_equivalent: Equivalent(List(MachineState(n)), candidates, Cons(Accepted("
  end

  test "every path failure carries its current cursor" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    for constructor <- [
          "LookaroundPathExhausted",
          "LookaroundPathStepExhausted",
          "LookaroundPathDestinationActiveRejected",
          "LookaroundPathDestinationAcceptedRejected"
        ] do
      line = Enum.find(String.split(source, "\n"), &String.starts_with?(&1, "    #{constructor} :"))
      assert line =~ "MachineStateCursor"
    end
  end

  test "public path rejection is a complete destination traversal" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")
    accepting = Enum.find(String.split(source, "\n"), &String.starts_with?(&1, "    LookaroundAcceptingPathRejected :"))
    prefix = Enum.find(String.split(source, "\n"), &String.starts_with?(&1, "    LookaroundPrefixPathRejected :"))

    assert accepting =~ "MachineStateCursor(n, destinations, destinations)"
    assert prefix =~ "MachineStateCursor(n, destinations, destinations)"
  end

  test "cursor suffixes compose for recursive refutation" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    assert source =~ "type MachineStateCursorSuffix"
    assert source =~ "MachineStateCursorSuffixDrop"
  end

  test "destination failures retain complete child traversals" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")
    active = Enum.find(String.split(source, "\n"), &String.starts_with?(&1, "    LookaroundPathDestinationActiveRejected :"))
    accepted = Enum.find(String.split(source, "\n"), &String.starts_with?(&1, "    LookaroundPathDestinationAcceptedRejected :"))

    assert active =~ "child_destinations, child_destinations"
    assert accepted =~ "child_destinations, child_destinations"
  end

  test "accepting paths carry recursive suffix relations" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    assert source =~ "child_cursor_suffix: MachineStateCursorSuffix"
    assert source =~ "cursor_suffix: MachineStateCursorSuffix(n, current, candidates)"
  end
end
