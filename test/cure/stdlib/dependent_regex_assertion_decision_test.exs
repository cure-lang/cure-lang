defmodule Cure.Stdlib.DependentRegexAssertionDecisionTest do
  use ExUnit.Case, async: false

  setup_all do
    source = ~S'''
    mod RegexAssertionDecisions
      use Std.Regex.Core
      use Std.Regex.Runtime

      fn assertion_accepts_a(char: Char) -> Bool = char == 'a'

      fn assertion_machine() -> PatternMachine(1) =
        predicate_pattern_machine(assertion_accepts_a)

      fn atomic_state_one() -> Bounded(3) = 1

      fn atomic_state_two() -> Bounded(3) = 2

      fn atomic_a_destinations() -> List(MachineState(3)) = Cons(
        Active(atomic_state_one(), [EndAtomic()], []),
        Cons(Active(atomic_state_two(), [EndAtomic()], []), [])
      )

      fn atomic_accepting_destination() -> List(MachineState(3)) =
        [Accepted([], [])]

      fn atomic_state_one_destination() -> List(MachineState(3)) =
        [Active(atomic_state_one(), [], [])]

      fn atomic_trace_next(state: Bounded(3), char: Char) -> List(MachineState(3)) = match state
        First() -> pickup
          char == 'a' -> atomic_a_destinations()
          else -> []
        Next(First()) -> pickup
          char == 'c' -> atomic_accepting_destination()
          else -> []
        Next(Next(First())) -> pickup
          char == 'b' -> atomic_state_one_destination()
          else -> []
        _ -> []

      fn atomic_trace_machine() -> PatternMachine(3) =
        MkPatternMachine([Active(0, [BeginAtomic()], [])], atomic_trace_next)

      fn certified_atomic_trace_rejects() -> Bool = match lookaround_prefix_search_decision(
        2,
        3,
        atomic_trace_machine(),
        subject_initial_position(),
        ['a', 'b', 'c'],
        [],
        [],
        [],
        AnyUnicodeNewline()
      )
        LookaheadSatisfied(_) -> false
        LookaheadRefuted(_) -> true
        LookaheadResourceExhausted(_, _, _, _, _) -> false

      fn atomic_trace_authority_rejects() -> Bool =
        not atomic_lookaround_accepts(
          2,
          3,
          atomic_trace_machine(),
          subject_initial_position(),
          ['a', 'b', 'c'],
          [],
          [],
          [],
          AnyUnicodeNewline()
        )

      fn certified_atomic_exact_trace_rejects() -> Bool = match lookaround_search_decision(
        2,
        3,
        atomic_trace_machine(),
        subject_initial_position(),
        ['a', 'b', 'c'],
        [],
        [],
        [],
        AnyUnicodeNewline()
      )
        LookbehindSatisfied(_) -> false
        LookbehindRefuted(_) -> true
        LookbehindResourceExhausted(_, _, _, _, _) -> false

      fn erase_lookahead_witness(
        @erased _witness: LookaheadWitness(1, assertion_machine())
      ) -> Unit = ()

      fn erase_lookahead_refutation(
        @erased _refutation: LookaheadRefutation(1, assertion_machine())
      ) -> Unit = ()

      fn lookahead_witness_erased() -> Unit = match lookaround_prefix_search_decision(
        2,
        1,
        assertion_machine(),
        subject_initial_position(),
        ['a'],
        [],
        [],
        [],
        AnyUnicodeNewline()
      )
        LookaheadSatisfied(witness) -> erase_lookahead_witness(witness)
        LookaheadRefuted(_) -> ()
        LookaheadResourceExhausted(_, _, _, _, _) -> ()

      fn lookahead_refutation_erased() -> Unit = match lookaround_prefix_search_decision(
        2,
        1,
        assertion_machine(),
        subject_initial_position(),
        ['b'],
        [],
        [],
        [],
        AnyUnicodeNewline()
      )
        LookaheadSatisfied(_) -> ()
        LookaheadRefuted(refutation) -> erase_lookahead_refutation(refutation)
        LookaheadResourceExhausted(_, _, _, _, _) -> ()

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
        LookbehindResourceExhausted(_, _, _, _, _) -> false

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
        LookbehindResourceExhausted(_, _, _, _, _) -> false

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

      fn depth_exhaustion_is_resource() -> Bool = match lookaround_child_lookahead(
        0,
        1,
        predicate_pattern_machine(fn(char) -> char == 'a'),
        position_boundary_for_history(subject_initial_position(), ['a'], []),
        ['a'],
        [],
        [],
        AnyUnicodeNewline()
      )
        LookaheadResourceExhausted(_, _, _, _, _) -> true
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
    assert apply(module, :depth_exhaustion_is_resource, [])
  end

  test "certified assertion decisions enforce atomic commitment", %{runtime_module: module} do
    assert apply(module, :atomic_trace_authority_rejects, [])
    assert apply(module, :certified_atomic_trace_rejects, [])
    assert apply(module, :certified_atomic_exact_trace_rejects, [])
  end

  test "assertion paths and refutation trees erase before emitted runtime", %{
    runtime_module: module
  } do
    assert apply(module, :lookahead_witness_erased, []) == :unit
    assert apply(module, :lookahead_refutation_erased, []) == :unit
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

    assert Regex.match?(~r/LookaroundSearchActiveRejectedEmpty\s*:.*?MachineStateMembers/s, source)
    assert Regex.match?(~r/LookaroundSearchActiveRejectedStep\s*:.*?MachineStateMembers/s, source)
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

  test "search refutations retain the exact unexamined start suffix" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    assert Regex.match?(
             ~r/type LookaroundSearchFailure\([^\n]*starts: List\(MachineState\(n\)\), current: List\(MachineState\(n\)\)\)/,
             source
           )

    assert Regex.match?(
             ~r/LookaroundSearchActiveRejectedEmpty\s*:.*?LookaroundSearchFailure\([^\n]*remaining_starts\).*?LookaroundSearchFailure\([^\n]*Cons\(Active/s,
             source
           )

    assert Regex.match?(
             ~r/LookaroundSearchActiveRejectedStep\s*:.*?LookaroundSearchFailure\([^\n]*remaining_starts\).*?LookaroundSearchFailure\([^\n]*Cons\(Active/s,
             source
           )

    assert Regex.match?(
             ~r/LookaroundSearchAcceptedRejected\s*:.*?LookaroundSearchFailure\([^\n]*remaining_starts\).*?LookaroundSearchFailure\([^\n]*Cons\(Accepted/s,
             source
           )

    assert Regex.match?(
             ~r/fn lookaround_search_failure_excludes_path\b.*?LookaroundSearchFailure.*?LookaroundSearchPath.*?-> Empty/s,
             source
           )
  end

  test "assertion depth exhaustion is not a semantic refutation" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    refute Regex.match?(~r/type LookaheadRefutation.*?LookaheadDepthExhausted/s, source)
    refute Regex.match?(~r/type LookbehindRefutation.*?LookbehindDepthExhausted/s, source)
    assert Regex.match?(~r/LookaheadResourceExhausted\s*:/, source)
    assert Regex.match?(~r/LookbehindResourceExhausted\s*:/, source)
    assert Regex.match?(~r/lookahead_decision_holds\b.*?LookaheadResourceExhausted\([^\n]*-> false/s, source)
    assert Regex.match?(~r/lookbehind_decision_holds\b.*?LookbehindResourceExhausted\([^\n]*-> false/s, source)
  end

  test "admitted lookaround states retain the constraints that produced nested evidence" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    filter =
      source
      |> String.split("fn lookaround_filter_boundary_states", parts: 2)
      |> List.last()
      |> String.split("fn capture_slot_markers_from_extended", parts: 2)
      |> List.first()

    assert filter =~ "Active(state, append_routine(routine, assertion_markers), constraints)"
    assert filter =~ "Accepted(append_routine(routine, assertion_markers), constraints)"
    refute filter =~ "append_routine(routine, assertion_markers), Nil()"
  end

  test "lookahead capture replay consumes the routine retained by its witness" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    witness =
      source
      |> String.split("type LookaheadWitness", parts: 2)
      |> List.last()
      |> String.split("type LookaheadDecision", parts: 2)
      |> List.first()

    lookbehind_witness =
      source
      |> String.split("type LookbehindWitness", parts: 2)
      |> List.last()
      |> String.split("type LookbehindDecision", parts: 2)
      |> List.first()

    capture_context =
      source
      |> String.split("fn lookaround_condition_capture_context", parts: 2)
      |> List.last()
      |> String.split("fn lookaround_constraint_capture_context", parts: 2)
      |> List.first()

    capture_routine =
      source
      |> String.split("fn lookaround_condition_routine", parts: 2)
      |> List.last()
      |> String.split("fn position_boundary_for_history", parts: 2)
      |> List.first()

    assert witness =~ "matched: List(Char)"
    assert witness =~ "remaining: List(Char)"
    assert witness =~ "routine: List(ExtendedInstruction)"
    assert lookbehind_witness =~ "routine: List(ExtendedInstruction)"
    assert capture_context =~ "lookahead_witness_routine"
    assert capture_context =~ "lookbehind_witness_routine"
    assert capture_routine =~ "lookahead_witness_routine"
    assert capture_routine =~ "lookbehind_witness_routine"
    refute capture_context =~ "atomic_lookaround_routine_prefix"
    refute capture_context =~ "atomic_lookaround_routine_accepts"
    refute capture_routine =~ "atomic_lookaround_routine_prefix"
    refute capture_routine =~ "atomic_lookaround_routine_accepts"
  end

  test "prefix rejection has no exact-only accepted-with-input case" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    assert Regex.match?(~r/type LookaroundPrefixPathFailure\b/, source)
    assert Regex.match?(~r/type LookaroundPrefixSearchFailure\b/, source)

    prefix_failure =
      source
      |> String.split("type LookaroundPrefixPathFailure", parts: 2)
      |> List.last()
      |> String.split("type LookaroundExhaustion", parts: 2)
      |> List.first()

    refute prefix_failure =~ "AcceptedWithInput"
    refute prefix_failure =~ "AcceptedRejected"

    assert Regex.match?(
             ~r/type LookaroundPrefixPath\([^\n]*capture_context: List\(EvidenceInstruction\)/,
             source
           )

    assert Regex.match?(
             ~r/LookaroundPrefixNextActive\s*:.*?child_destinations_equivalent: Equivalent/s,
             source
           )

    assert Regex.match?(
             ~r/fn lookaround_prefix_failure_excludes_suffix\b.*?LookaroundPrefixPathFailure.*?LookaroundPrefixPath.*?-> Empty/s,
             source
           )

    assert Regex.match?(
             ~r/fn lookaround_prefix_search_failure_excludes_path\b.*?LookaroundPrefixSearchFailure.*?LookaroundPrefixSearchPath.*?-> Empty/s,
             source
           )
  end

  test "exact and prefix search results are constructively complete" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    for theorem <- [
          "lookaround_search_path_completeness",
          "lookaround_search_refutation_completeness",
          "lookaround_prefix_search_path_completeness",
          "lookaround_prefix_search_refutation_completeness"
        ] do
      assert Regex.match?(~r/fn #{theorem}\b/, source),
             "expected the constructive completeness theorem #{theorem}"
    end

    assert Regex.match?(
             ~r/type LookaroundSearchPathCompleteness\b.*?starts: List\(MachineState\(n\)\).*?indices \(result: LookaroundSearchResult\(depth, n, machine, starts,/s,
             source
           )

    assert Regex.match?(
             ~r/type LookaroundSearchRefutationCompleteness\b.*?starts: List\(MachineState\(n\)\).*?indices \(result: LookaroundSearchResult\(depth, n, machine, starts,/s,
             source
           )

    assert Regex.match?(
             ~r/type LookaroundPrefixSearchPathCompleteness\b.*?starts: List\(MachineState\(n\)\).*?indices \(result: LookaroundPrefixSearchResult\(depth, n, machine, starts,/s,
             source
           )

    assert Regex.match?(
             ~r/type LookaroundPrefixSearchRefutationCompleteness\b.*?starts: List\(MachineState\(n\)\).*?indices \(result: LookaroundPrefixSearchResult\(depth, n, machine, starts,/s,
             source
           )

    assert length(Regex.scan(~r/@erased computed: Equivalent\(Lookaround(?:Prefix)?SearchResult/, source)) >= 4
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
             ~r/type LookaroundAcceptingPath\(depth: Nat, n: Nat, machine: PatternMachine\(n\), capture_context: List\(EvidenceInstruction\), candidates: List\(MachineState\(n\)\)\)/,
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

    assert Regex.match?(
             ~r/fn lookaround_path_failure_excludes_accepting_suffix\b.*?LookaroundPathFailure.*?MachineStateCursorSuffix/s,
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

    for constructor <- [
          "LookaroundAcceptingPathRejectedEmpty",
          "LookaroundAcceptingPathRejectedStep",
          "LookaroundAcceptingPathRejectedAcceptedStep"
        ] do
      assert Regex.match?(~r/#{constructor}\s*:.*?MachineStateCursor/s, source)
    end

    for constructor <- [
          "LookaroundPrefixPathRejectedEmpty",
          "LookaroundPrefixPathRejectedStep"
        ] do
      assert Regex.match?(~r/#{constructor}\s*:.*?MachineStateCursor/s, source)
    end
  end

  test "accepted path edges are forced to the cursor head" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")
    active = Enum.find(String.split(source, "\n"), &String.starts_with?(&1, "    LookaroundAcceptedNextActive :"))
    accepted = Enum.find(String.split(source, "\n"), &String.starts_with?(&1, "    LookaroundAcceptedNextAccepted :"))
    prefix = Enum.find(String.split(source, "\n"), &String.starts_with?(&1, "    LookaroundPrefixNextActive :"))

    prefix_accepted =
      Enum.find(String.split(source, "\n"), &String.starts_with?(&1, "    LookaroundPrefixNextAccepted :"))

    assert active =~ "members: MachineStateMembers"
    assert active =~ "candidate_equivalent: Equivalent(List(MachineState(n)), candidates, Cons(Active("
    assert active =~ ~r/edge: ListMember\(MachineState\(n\), Active\(.*?\), Cons\(Active\(/
    assert accepted =~ "candidate_equivalent: Equivalent(List(MachineState(n)), candidates, Cons(Accepted("
    assert prefix =~ "members: MachineStateMembers"
    assert prefix =~ "candidate_equivalent: Equivalent(List(MachineState(n)), candidates, Cons(Active("
    assert prefix =~ ~r/edge: ListMember\(MachineState\(n\), Active\(.*?\), Cons\(Active\(/
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

    accepting =
      Enum.find(String.split(source, "\n"), &String.starts_with?(&1, "    LookaroundAcceptingPathRejectedStep :"))

    prefix = Enum.find(String.split(source, "\n"), &String.starts_with?(&1, "    LookaroundPrefixPathRejectedStep :"))

    assert accepting =~ "MachineStateCursor(n, lookaround_machine_destinations"
    assert prefix =~ "MachineStateCursor(n, lookaround_machine_destinations"
  end

  test "cursor suffixes compose for recursive refutation" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    assert source =~ "type MachineStateCursorSuffix"
    assert source =~ "MachineStateCursorSuffixDrop"
  end

  test "destination failures retain complete child traversals" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    active =
      Enum.find(String.split(source, "\n"), &String.starts_with?(&1, "    LookaroundPathDestinationActiveRejected :"))

    accepted =
      Enum.find(String.split(source, "\n"), &String.starts_with?(&1, "    LookaroundPathDestinationAcceptedRejected :"))

    assert length(Regex.scan(~r/lookaround_machine_destinations/, active)) >= 3
    assert length(Regex.scan(~r/empty_machine_states/, accepted)) >= 2
  end

  test "accepting paths carry recursive suffix relations" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    assert source =~ "child_cursor_suffix: MachineStateCursorSuffix"
    assert source =~ "cursor_suffix: MachineStateCursorSuffix(n, current, candidates)"
  end
end
