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
        LookbehindRefuted(LookbehindAtomicSearchRejected(_, _, ['b'], [], [], _, AnyUnicodeNewline(), _, LookaroundRoutineRejected())) -> true
        _ -> false

      fn nested_decision_evidence() -> Bool =
        let inner_machine = predicate_pattern_machine(fn(char) -> char == 'a')
        let constraint = BoundaryConstraint(false, false, false, false, false, false, false, false, false, AnyUnicodeNewline(), None(), Some(LookaheadCondition(true, %[1, inner_machine])))
        match lookaround_constraints_admission(
          2,
          [constraint],
          position_boundary_for_history(subject_initial_position(), ['a'], []),
          ['a'],
          [],
          [],
          AnyUnicodeNewline()
        )
          Some(LookaroundConstraintAdmitted(_, _, [LookaheadNestedDecision(true, _)])) -> true
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

      fn atomic_prefix_shortest() -> Option(Tuple(List(Char), List(Char), List(ExtendedInstruction))) =
        let compilation = LookaroundRepeat(
          LookaroundPredicate(fn(char) -> char == 'a'),
          false
        )
        let machine = lookaround_machine(compilation)
        atomic_lookaround_routine_prefix(
          regex_assertion_depth_limit(),
          lookaround_state_count(compilation),
          machine,
          subject_initial_position(),
          ['a', 'a'],
          false,
          [],
          [],
          AnyUnicodeNewline()
        )

      fn atomic_prefix_longest() -> Option(Tuple(List(Char), List(Char), List(ExtendedInstruction))) =
        let compilation = LookaroundRepeat(
          LookaroundPredicate(fn(char) -> char == 'a'),
          false
        )
        let machine = lookaround_machine(compilation)
        atomic_lookaround_routine_prefix(
          regex_assertion_depth_limit(),
          lookaround_state_count(compilation),
          machine,
          subject_initial_position(),
          ['a', 'a'],
          true,
          [],
          [],
          AnyUnicodeNewline()
        )

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

  test "atomic prefix selection honors shortest and longest modes", %{runtime_module: module} do
    assert {:some, {[], ~c"aa", _shortest_routine}} =
             apply(module, :atomic_prefix_shortest, [])

    assert {:some, {~c"aa", [], _longest_routine}} =
             apply(module, :atomic_prefix_longest, [])
  end

  test "atomic prefix endpoint policy is implemented by the atomic authority" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")
    [body] = Regex.run(~r/fn atomic_lookaround_routine_prefix\b.*?\n\n  fn atomic_lookaround_routine_first_prefix/s, source)

    assert body =~ "atomic_lookaround_routine_first_prefix"
    assert body =~ "atomic_lookaround_routine_last_prefix"
    refute body =~ "_greedy"
  end

  test "atomic destination rejection exposes a child alignment eliminator" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    assert Regex.match?(
             ~r/fn atomic_path_destination_rejection_excludes_aligned_child\b.*?child_selection_suffix/s,
             source
           )
  end

  test "atomic candidate suffixes have an ordered alignment witness" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    assert Regex.match?(
             ~r/type LookaroundAdmittedStateCursorAlignment\b.*?LookaroundAdmittedCursorLeftToRight/s,
             source
           )

    assert Regex.match?(~r/LookaroundAdmittedCursorRightToLeft/, source)

    assert Regex.match?(
             ~r/fn lookaround_admitted_cursor_suffix_alignment\b.*?LookaroundAdmittedStateCursorAlignment/s,
           source
           )
  end

  test "atomic refutations retain their ordered candidate suffix" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    [input_exhausted] = Enum.filter(String.split(source, "\n"), &String.contains?(&1, "AtomicPathInputExhausted :"))
    [destination_rejected] = Enum.filter(String.split(source, "\n"), &String.contains?(&1, "AtomicPathDestinationRejected :"))

    assert input_exhausted =~ "LookaroundAdmittedStateCursorSuffix"
    assert destination_rejected =~ "LookaroundAdmittedStateCursorSuffix"
  end

  test "atomic child exhaustion has a suffix-indexed eliminator" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    assert Regex.match?(~r/fn atomic_path_child_input_exhaustion_excludes_trace\b.*?failure_suffix/s, source)
  end

  test "atomic exact-child exhaustion has a suffix-indexed eliminator" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    assert Regex.match?(~r/fn atomic_path_child_exact_failure_excludes_trace\b.*?failure_suffix/s, source)
  end

  test "atomic no-results publish the refutation suffix to their parent" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    [search_no] = Enum.filter(String.split(source, "\n"), &String.contains?(&1, "AtomicPathSearchNo :"))
    [members_no] = Enum.filter(String.split(source, "\n"), &String.contains?(&1, "AtomicPathMembersNo :"))

    assert search_no =~ "LookaroundAdmittedStateCursorSuffix"
    assert members_no =~ "LookaroundAdmittedStateCursorSuffix"
  end

  test "atomic refutation has a recursive child and tail eliminator" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    assert source =~ "atomic_path_destination_rejection_excludes_recursive_trace"
  end

  test "atomic rejected-child leaf consumes the published child suffix" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    assert source =~ "atomic_path_destination_rejection_excludes_stored_aligned_child"
    assert Regex.match?(~r/atomic_path_destination_rejection_excludes_aligned_child\b[^=]*child_failure_suffix/s, source)
  end

  test "atomic selected child paths retain their origin spine equivalence" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    assert source =~ "transport_lookaround_admitted_cursor_suffix_outer"
    assert source =~ "atomic_child_cursor_alignment"
    assert Regex.match?(
             ~r/AtomicSelectedTransitionActive\s*:.*?child_selected_whole_equivalence/s,
             source
           )
  end

  test "atomic no-results publish their canonical child spine" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    [search_no] = Enum.filter(String.split(source, "\n"), &String.contains?(&1, "AtomicPathSearchNo :"))

    assert search_no =~ "origin_equivalence"
  end

  test "atomic rejected destinations retain child and tail origins" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    [destination_rejected] =
      Enum.filter(String.split(source, "\n"), &String.contains?(&1, "AtomicPathDestinationRejected :"))

    assert destination_rejected =~ "child_origin_equivalence"
    assert destination_rejected =~ "tail_origin_equivalence"
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

    projection =
      source
      |> String.split("fn lookaround_admitted_machine_state", parts: 2)
      |> List.last()
      |> String.split("fn lookaround_admitted_machine_states", parts: 2)
      |> List.first()

    assert projection =~ "Active(state, append_routine(routine, assertion_markers), constraints)"
    assert projection =~ "Accepted(append_routine(routine, assertion_markers), constraints)"
    refute projection =~ "append_routine(routine, assertion_markers), Nil()"
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

    witness_replay =
      source
      |> String.split("fn lookahead_witness_routine", parts: 2)
      |> List.last()
      |> String.split("fn lookbehind_witness", parts: 2)
      |> List.first()

    lookbehind_replay =
      source
      |> String.split("fn lookbehind_witness_routine", parts: 2)
      |> List.last()
      |> String.split("fn lookaround_prefix_filtered_starts", parts: 2)
      |> List.first()

    admission =
      source
      |> String.split("fn lookaround_condition_admission", parts: 2)
      |> List.last()
      |> String.split("fn lookaround_constraint_admission", parts: 2)
      |> List.first()

    assert witness =~ "matched: List(Char)"
    assert witness =~ "remaining: List(Char)"
    assert witness =~ "routine: List(ExtendedInstruction)"
    assert lookbehind_witness =~ "routine: List(ExtendedInstruction)"
    assert admission =~ "lookahead_witness_routine"
    assert admission =~ "lookbehind_witness_routine"
    assert admission =~ "capture_slot_markers_from_extended"
    refute admission =~ "atomic_lookaround_routine_prefix"
    refute admission =~ "atomic_lookaround_routine_accepts"

    assert witness_replay =~ "selected_trace_routine"
    assert lookbehind_replay =~ "selected_trace_routine"
  end

  test "atomic assertion refutations cannot carry a successful search result" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    lookahead_refutation =
      source
      |> String.split("type LookaheadRefutation", parts: 2)
      |> List.last()
      |> String.split("type LookaheadWitness", parts: 2)
      |> List.first()

    lookbehind_refutation =
      source
      |> String.split("type LookbehindRefutation", parts: 2)
      |> List.last()
      |> String.split("type LookbehindWitness", parts: 2)
      |> List.first()

    reason =
      source
      |> String.split("type LookaroundRoutineRejectionReason", parts: 2)
      |> List.last()
      |> String.split("type AtomicDepthAtLeast", parts: 2)
      |> List.first()

    refute lookahead_refutation =~ "result: LookaroundRoutineSearchResult"
    refute lookbehind_refutation =~ "result: LookaroundRoutineSearchResult"
    assert reason =~ "LookaroundRoutineRejected"
    assert reason =~ "LookaroundRoutineCommitted(Nat)"
    refute reason =~ "LookaroundRoutineSearchYes"
  end

  test "atomic decisions never rerun the legacy indexed path search" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    prefix =
      source
      |> String.split("fn lookahead_atomic_path_decision", parts: 2)
      |> List.last()
      |> String.split("fn lookaround_prefix_search_decision", parts: 2)
      |> List.first()

    exact =
      source
      |> String.split("fn lookbehind_atomic_path_decision", parts: 2)
      |> List.last()
      |> String.split("fn lookaround_search_decision", parts: 2)
      |> List.first()

    refute prefix =~ "lookaround_prefix_search_path"
    refute exact =~ "lookaround_machine_acceptance_path"
  end

  test "the staged proof path uses the selected atomic trace authority" do
    source = File.read!("lib/std_deps/regex/regex_proof.cure")

    refute source =~ "lookaround_machine_acceptance_path"
    refute source =~ "lookaround_prefix("
    assert source =~ "atomic_lookaround_routine_initial"
  end

  test "atomic success constructs and retains the selected machine trace" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    assert source =~
             "type AtomicSelectedPathTrace(depth: Nat, n: Nat, machine: PatternMachine(n))"

    assert source =~
             "type AtomicSelectedTrace(depth: Nat, n: Nat, machine: PatternMachine(n))"

    assert source =~
             "type AtomicPathSearchResult(depth: Nat, n: Nat, machine: PatternMachine(n))"

    assert source =~
             "type LookaroundRoutineSearchResult(depth: Nat, n: Nat, machine: PatternMachine(n))"

    result_declaration =
      source
      |> String.split("LookaroundRoutineSearchYes :", parts: 2)
      |> List.last()
      |> String.split("\n", parts: 2)
      |> List.first()

    assert result_declaration =~ "matched: List(Char)"
    assert result_declaration =~ "remaining: List(Char)"
    assert result_declaration =~ "routine: List(ExtendedInstruction)"
    assert result_declaration =~ "AtomicSelectedTrace(depth, n, machine"
    assert result_declaration =~ "matched, remaining, routine)"

    lookahead_declaration =
      source
      |> String.split("LookaheadWitnessPacked :", parts: 2)
      |> List.last()
      |> String.split("\n", parts: 2)
      |> List.first()

    assert lookahead_declaration =~ "matched: List(Char)"
    assert lookahead_declaration =~ "remaining: List(Char)"
    assert lookahead_declaration =~ "routine: List(ExtendedInstruction)"
    assert lookahead_declaration =~ "AtomicSelectedTrace(depth, n, machine"
    assert lookahead_declaration =~ "matched, remaining, routine)"
    refute lookahead_declaration =~ "LookaroundPrefixSearchPath"

    lookbehind_declaration =
      source
      |> String.split("LookbehindWitnessPacked :", parts: 2)
      |> List.last()
      |> String.split("\n", parts: 2)
      |> List.first()

    assert lookbehind_declaration =~ "routine: List(ExtendedInstruction)"
    assert lookbehind_declaration =~ "AtomicSelectedTrace(depth, n, machine"
    assert lookbehind_declaration =~ "matched, remaining_input, routine)"
    refute lookbehind_declaration =~ "LookaroundSearchPath"

    assert source =~ "AtomicSelectedTransitionActive"
    assert source =~ "AtomicSelectedTransitionAccepted"
    assert source =~ "AtomicSelectedTransitionActive : (@erased source: Bounded(n))"
    assert source =~ "AtomicSelectedTransitionAccepted : (@erased source: Bounded(n))"
    assert source =~ "child_selection_suffix"
    assert source =~ "AtomicSelectedStartActive"
    assert source =~ "AtomicSelectedStartAccepted"
    assert Regex.match?(~r/AtomicSelectedStartActive\s*:[^\n]*selected_origin_equivalence/, source)
    assert Regex.match?(~r/AtomicSelectedStartAccepted\s*:[^\n]*selected_origin_equivalence/, source)
    assert source =~ "type LookaroundAdmittedStateCursor"
    assert Regex.match?(~r/AtomicSelectedTransitionActive\s*:[^\n]*LookaroundAdmittedStateCursor[^\n]*ListMember/, source)
    assert Regex.match?(~r/AtomicSelectedTransitionAccepted\s*:[^\n]*LookaroundAdmittedStateCursor[^\n]*ListMember/, source)

    assert Regex.match?(
             ~r/AtomicSelectedTransitionActive\s*:[^\n]*Equivalent[^\n]*lookaround_machine_admitted_destinations/,
             source
           )

    assert Regex.match?(
             ~r/AtomicSelectedTransitionAccepted\s*:[^\n]*Equivalent[^\n]*lookaround_machine_admitted_destinations/,
             source
           )

    assert Regex.match?(
             ~r/AtomicSelectedStartActive\s*:[^\n]*LookaroundAdmittedStateCursor[^\n]*ListMember[^\n]*Equivalent[^\n]*lookaround_admitted_starts/,
             source
           )

    assert Regex.match?(
             ~r/AtomicSelectedStartAccepted\s*:[^\n]*LookaroundAdmittedStateCursor[^\n]*ListMember[^\n]*Equivalent[^\n]*lookaround_admitted_starts/,
             source
           )
  end

  test "atomic no-path results retain an indexed refutation tree" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    assert source =~
             "type AtomicPathRefutation(depth: Nat, n: Nat, machine: PatternMachine(n))"

    assert source =~
             "type AtomicPathMembersResult(depth: Nat, n: Nat, machine: PatternMachine(n))"

    assert source =~ "AtomicPathMembersNo"

    result =
      source
      |> String.split("type AtomicPathSearchResult", parts: 2)
      |> List.last()
      |> String.split("type LookaroundRoutineSearchResult", parts: 2)
      |> List.first()

    assert result =~ "AtomicPathSearchNo"
    assert result =~ "failure: AtomicPathRefutation"
    assert result =~ "selection_suffix: LookaroundAdmittedStateCursorSuffix"
    assert result =~ "selected_whole_equivalence: Equivalent"
    assert result =~ "selected_origin_equivalence: Equivalent"
    assert source =~ "atomic_lookaround_routine_add_skipped_candidate"
    assert source =~ "AtomicPathInputExhausted"
    assert source =~ "AtomicPathDestinationRejected"
    assert source =~ "type AtomicPathRootRefutation"
    assert source =~ "AtomicPathSearchRootActiveNo"
    assert source =~ "AtomicPathSearchRootExactNo"
    assert source =~ "AtomicPathSearchRootNo"
    assert source =~ "atomic_path_members_root_to_search"
    assert source =~ "atomic_path_failure_excludes_aligned_trace"
    assert source =~ "atomic_path_root_exact_accepted_with_input_evidence"
    assert source =~ "atomic_path_root_input_exhausted_evidence"
    assert Regex.match?(~r/AtomicPathExactAcceptedWithInput\s*:[^\n]*Cons\(char, rest\)/, source)
    assert Regex.match?(~r/AtomicPathDestinationRejected\s*:[^\n]*LookaroundAdmittedStateCursor[^\n]*ListMember[^\n]*Equivalent[^\n]*lookaround_machine_admitted_destinations/, source)
    assert source =~ "AtomicStartCandidateRejected"
    start_rejection = Enum.find(String.split(source, "\n"), &String.starts_with?(&1, "    AtomicStartCandidateRejected :"))
    assert start_rejection =~ "LookaroundAdmittedState(n)"
    assert start_rejection =~ "LookaroundAdmittedStateCursor"
    assert start_rejection =~ "ListMember"
    assert source =~ "type LookaroundAdmittedStateCursorSuffix"
    assert source =~ "LookaroundAdmittedStateCursorSuffixDrop"
    assert source =~ "LookaroundAdmittedStateCursorWitness"
    assert source =~ "witness: LookaroundAdmittedStateCursorWitness"
    assert source =~ "whole: List(LookaroundAdmittedState(n)), current: List(LookaroundAdmittedState(n))"
    assert source =~ "lookaround_admitted_cursor_suffix_compose"
    assert source =~ "lookaround_admitted_cursor_suffix_from_member"
    assert source =~ "lookaround_admitted_cursor_to_suffix"
    assert source =~ "atomic_path_input_exhaustion_excludes_trace"
    assert source =~ "atomic_path_root_active_failure_excludes_trace"
    assert source =~ "atomic_path_root_exact_failure_excludes_trace"
    assert source =~ "atomic_path_failure_excludes_trace"
    assert source =~ "atomic_path_destinations_exhausted_excludes_trace"
    assert source =~ "atomic_path_active_destinations_exhausted_excludes_trace"
    assert source =~ "atomic_path_exact_failure_excludes_trace"
    assert source =~ "atomic_path_destination_rejection_excludes_trace"
    assert source =~ "atomic_path_accepted_destination_rejection_excludes_trace"
    assert source =~ "atomic_path_accepted_destination_rejection_excludes_aligned_trace"
    assert source =~ "atomic_path_tail_destinations_exhausted_excludes_aligned_trace"
    input_exhausted = Enum.find(String.split(source, "\n"), &String.starts_with?(&1, "    AtomicPathInputExhausted :"))
    destinations_exhausted = Enum.find(String.split(source, "\n"), &String.starts_with?(&1, "    AtomicPathDestinationsExhausted :"))
    assert input_exhausted =~ "ThreadActive(source)"
    assert input_exhausted =~ "machine, Nil(), after_input, ThreadActive(source)"
    assert destinations_exhausted =~ "ThreadActive(source)"
    destination_rejected = Enum.find(String.split(source, "\n"), &String.starts_with?(&1, "    AtomicPathDestinationRejected :"))
    assert destination_rejected =~ "ThreadActive(source)"

    destination_rejection =
      source
      |> String.split("fn atomic_path_destination_rejection_excludes_trace", parts: 2)
      |> List.last()
      |> String.split("\n  fn ", parts: 2)
      |> List.first()

    assert destination_rejection =~ "AtomicSelectedTransitionActive"
    assert destination_rejection =~ "atomic_path_input_exhaustion_excludes_trace"
    assert Regex.match?(~r/LookaroundRoutineSearchNo\s*:\s*\(@erased failure: AtomicStartRefutation/, source)
    assert source =~ "Option(AtomicStartRefutation"
  end

  test "constraint admission has one construction authority" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    assert source =~ "type LookaroundConstraintAdmission"
    assert source =~ "LookaroundConstraintAdmitted"

    for consumer <- [
          "lookaround_constraints_capture_context",
          "lookaround_constraints_routine",
          "lookaround_nested_decisions"
        ] do
      body =
        source
        |> String.split("fn #{consumer}", parts: 2)
        |> List.last()
        |> String.split("\n  fn ", parts: 2)
        |> List.first()

      assert body =~ "lookaround_constraints_admission",
             "#{consumer} must project the canonical constraint admission"
    end

    for consumer <- [
          "atomic_lookaround_routine_members_from",
          "atomic_lookaround_routine_initial_members"
        ] do
      body =
        source
        |> String.split("fn #{consumer}", parts: 2)
        |> List.last()
        |> String.split("\n  fn ", parts: 2)
        |> List.first()

      assert body =~ "LookaroundAdmittedState"
      refute body =~ "lookaround_constraints_admission"
    end

    for obsolete <- [
          "lookaround_condition_capture_context",
          "lookaround_constraint_capture_context",
          "lookaround_constraint_routine",
          "lookaround_condition_routine",
          "lookaround_constraint_nested_decisions"
        ] do
      refute source =~ "fn #{obsolete}", "#{obsolete} duplicates constraint evaluation"
    end
  end

  test "filtered candidates project one canonical admitted-state list" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    assert source =~ "type LookaroundAdmittedState(n: Nat)"
    assert source =~ "fn lookaround_admitted_machine_state"
    assert source =~ "fn lookaround_admitted_machine_states"
    assert source =~ "fn lookaround_admit_boundary_states"

    filter =
      source
      |> String.split("fn lookaround_filter_boundary_states", parts: 2)
      |> List.last()
      |> String.split("\n  fn ", parts: 2)
      |> List.first()

    assert filter =~ "lookaround_admitted_machine_states"
    assert filter =~ "lookaround_admit_boundary_states"
    refute filter =~ "lookaround_constraints_admission"
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

  test "atomic scope proofs use indexed construction helpers" do
    source = File.read!("lib/std_deps/regex/regex_runtime.cure")

    assert source =~ "fn atomic_lookaround_state_scope_active"
    assert source =~ "fn atomic_lookaround_state_scope_accepted"

    members =
      source
      |> String.split("fn atomic_lookaround_routine_members_from", parts: 2)
      |> List.last()
      |> String.split("\n  fn ", parts: 2)
      |> List.first()

    assert members =~ "atomic_lookaround_state_scope_active"
    assert members =~ "atomic_lookaround_state_scope_accepted"
    refute members =~ "LookaroundAdmittedStateScopeActive("
    refute members =~ "LookaroundAdmittedStateScopeAccepted("
  end
end
