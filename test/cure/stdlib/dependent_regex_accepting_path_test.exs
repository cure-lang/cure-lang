defmodule Cure.Stdlib.DependentRegexAcceptingPathTest do
  use ExUnit.Case, async: true

  alias Cure.Core.Env
  alias Cure.Elab.Program

  @source """
  mod RegexAcceptingPath
    use Std.Regex
    use Std.Regex.Proof

    fn one_next(_state: Bounded(1), char: Char) -> List(MachineState(1)) =
      [Accepted([EmitChar(char)], [])]

    fn one_machine() -> PatternMachine(1) =
      MkPatternMachine([Active(0, [], [])], one_next)

    fn start_state() -> ThreadState(1) = ThreadActive(0)

    fn one_step() -> AcceptingFrom(
      1,
      one_machine(),
      Cons('a', Nil()),
      Nil(),
      start_state(),
      Nil(),
      Nil(),
      Cons(CharacterEvidence('a'), Nil()),
      Cons(Observe('a'), Cons(Regular(EmitChar('a')), Nil()))
    ) =
      AcceptingNextAccepted(
        [EmitChar('a')],
        [],
        [CharacterEvidence('a')],
        [],
        [],
        ListMemberHere(),
        RoutineStep(
          EmitChar('a'),
          RoutineDone()
        ),
        AcceptingNow()
      )

    fn erase_path(@erased _path: AcceptingFrom(1, one_machine(), Cons('a', Nil()), Nil(), start_state(), Nil(), Nil(), Cons(CharacterEvidence('a'), Nil()), Cons(Observe('a'), Cons(Regular(EmitChar('a')), Nil())))) -> Unit = ()

    fn one_step_erased() -> Unit = erase_path(one_step())

    fn searched() -> AcceptingSearch(1, one_machine(), Cons('a', Nil()), Nil(), start_state(), Nil(), Nil()) =
      search_accepting_from(1, one_machine(), ['a'], [], start_state(), [], [])

    fn searched_machine() -> MachineAcceptingSearch(1, one_machine(), subject_initial_position(), Cons('a', Nil()), Nil()) =
      search_machine_acceptance(1, one_machine(), subject_initial_position(), ['a'], [])

    fn searched_empty() -> AcceptingSearch(1, one_machine(), Nil(), Nil(), start_state(), Nil(), Nil()) =
      search_accepting_from(1, one_machine(), [], [], start_state(), [], [])

    fn nullable_machine() -> PatternMachine(1) =
      MkPatternMachine(
        [Accepted([EmitUnit()], []), Active(0, [], [])],
        one_next
      )

    fn shortest_prefix() -> CertifiedPrefixSearch(1, nullable_machine(), subject_initial_position()) =
      search_first_machine_prefix(1, nullable_machine(), subject_initial_position(), ['a'])

    fn longest_prefix() -> CertifiedPrefixSearch(1, nullable_machine(), subject_initial_position()) =
      search_last_machine_prefix(1, nullable_machine(), subject_initial_position(), ['a'])

    fn zero_next(_state: Bounded(0), _char: Char) -> List(MachineState(0)) = []

    fn accepts_a(char: Char) -> Bool = char == 'a'
    fn accepts_b(char: Char) -> Bool = char == 'b'

    fn predicate_extended_routine_case(
      prior: List(Evidence),
      captures: List(CaptureFrame),
      {output: List(Evidence)},
      {output_captures: List(CaptureFrame)},
      execution: ExtendedEvidenceRoutineExecution(
        transition_routine('a', Cons(EmitChar('a'), Nil())),
        prior,
        captures,
        output,
        output_captures
      )
    ) -> Encodes(CharC, output, prior) =
      predicate_transition_routine_encodes('a', execution)

    fn group_character_extended_routine_case(
      prior: List(Evidence),
      captures: List(CaptureFrame),
      {output: List(Evidence)},
      {output_captures: List(CaptureFrame)},
      execution: ExtendedEvidenceRoutineExecution(
        Cons(
          Regular(BeginCapture()),
          transition_routine('a', Cons(EmitChar('a'), Cons(EndCapture(), Nil())))
        ),
        prior,
        captures,
        output,
        output_captures
      )
    ) -> Encodes(StringC, output, prior) =
      group_character_routine_encodes('a', execution)

    fn predicate_path_routine_case(
      prior: List(Evidence),
      captures: List(CaptureFrame),
      {path_evidence: List(Evidence)},
      {path_captures: List(CaptureFrame)},
      {path_final_evidence: List(Evidence)},
      {routine: List(ExtendedInstruction)},
      {output: List(Evidence)},
      {output_captures: List(CaptureFrame)},
      path: AcceptingFrom(1, predicate_pattern_machine(accepts_a), Cons('a', Nil()), Nil(), predicate_machine_thread(), path_evidence, path_captures, path_final_evidence, routine),
      execution: ExtendedEvidenceRoutineExecution(routine, prior, captures, output, output_captures)
    ) -> Encodes(CharC, output, prior) =
      predicate_path_routine_encodes(accepts_a, 'a', [], prior, captures, path, execution)

    fn empty_acceptance_case(
      prior: List(Evidence),
      captures: List(CaptureFrame),
      {final_evidence: List(Evidence)},
      {routine: List(ExtendedInstruction)},
      {output: List(Evidence)},
      {output_captures: List(CaptureFrame)},
      acceptance: MachineAcceptance(0, empty_pattern_machine(), subject_initial_position(), Nil(), Nil(), final_evidence, routine),
      execution: ExtendedEvidenceRoutineExecution(routine, prior, captures, output, output_captures)
    ) -> Encodes(UnitC, output, prior) =
      empty_machine_acceptance_encodes(subject_initial_position(), [], prior, captures, acceptance, execution)

    fn boundary_acceptance_case(
      constraint: BoundaryConstraint,
      position: InitialPosition,
      after_input: List(Char),
      @erased final_evidence: List(Evidence),
      @erased routine: List(ExtendedInstruction),
      acceptance: MachineAcceptance(0, boundary_pattern_machine(constraint), position, empty_characters(), after_input, final_evidence, routine)
    ) -> Encodes(UnitC, final_evidence, empty_evidence()) =
      boundary_machine_acceptance_encodes(constraint, position, after_input, final_evidence, routine, acceptance)

    fn predicate_acceptance_case(
      @erased final_evidence: List(Evidence),
      @erased routine: List(ExtendedInstruction),
      acceptance: MachineAcceptance(1, predicate_pattern_machine(accepts_a), subject_initial_position(), Cons('a', empty_characters()), empty_characters(), final_evidence, routine)
    ) -> Encodes(CharC, final_evidence, empty_evidence()) =
      predicate_machine_acceptance_encodes(accepts_a, 'a', empty_characters(), subject_initial_position(), final_evidence, routine, acceptance)

    fn predicate_arbitrary_input_acceptance_case(
      input: List(Char),
      after_input: List(Char),
      @erased final_evidence: List(Evidence),
      @erased routine: List(ExtendedInstruction),
      acceptance: MachineAcceptance(1, predicate_pattern_machine(accepts_a), subject_initial_position(), input, after_input, final_evidence, routine)
    ) -> Encodes(CharC, final_evidence, empty_evidence()) =
      predicate_machine_arbitrary_acceptance_encodes(
        accepts_a,
        input,
        after_input,
        subject_initial_position(),
        final_evidence,
        routine,
        acceptance
      )

    fn certified_predicate_machine_case() -> CertifiedPatternMachine =
      certify_predicate_pattern_machine(accepts_a)

    fn certified_empty_machine_case() -> CertifiedPatternMachine =
      certify_empty_pattern_machine()

    fn certified_boundary_machine_case(constraint: BoundaryConstraint) -> CertifiedPatternMachine =
      certify_boundary_pattern_machine(constraint)

    fn nested_thompson_compilation_case() -> ThompsonCompilation(PairC(UnitC(), ChoiceC(CharC(), ListC(CharC())))) =
      certify_thompson(
        PatternConcat(
          PatternEmpty(),
          PatternAlternate(
            PatternPredicate(accepts_a),
            PatternRepeat(PatternPredicate(accepts_b))
          )
        )
      )

    fn nested_thompson_compiled_case() -> Sigma(n: Nat, PatternMachine(n)) =
      thompson_compiled(nested_thompson_compilation_case())

    fn nested_alternate_machine_case() -> PatternMachine(plus(Z(), S(Z()))) =
      alternate_pattern_machine(Z(), empty_pattern_machine(), S(Z()), predicate_pattern_machine(accepts_a), false)

    fn left_alternate_state_origin_case(
      left_count: Nat,
      right_count: Nat,
      states: List(MachineState(left_count)),
      combined: MachineState(plus(left_count, right_count)),
      edge: ListMember(MachineState(plus(left_count, right_count)), combined, alternate_left_states(left_count, right_count, states, EmitLeft()))
    ) -> LeftMarkedStateOrigin(left_count, right_count, EmitLeft(), states, combined) =
      left_marked_state_origin(left_count, right_count, states, EmitLeft(), combined, edge)

    fn right_alternate_state_origin_case(
      left_count: Nat,
      right_count: Nat,
      states: List(MachineState(right_count)),
      combined: MachineState(plus(left_count, right_count)),
      edge: ListMember(MachineState(plus(left_count, right_count)), combined, alternate_right_states(left_count, right_count, states, EmitRight()))
    ) -> RightMarkedStateOrigin(left_count, right_count, EmitRight(), states, combined) =
      right_marked_state_origin(left_count, right_count, states, EmitRight(), combined, edge)

    fn appended_state_origin_case(
      n: Nat,
      left: List(MachineState(n)),
      right: List(MachineState(n)),
      value: MachineState(n),
      edge: ListMember(MachineState(n), value, append_machine_states(n, left, right))
    ) -> AppendMemberOrigin(n, left, right, value) =
      append_member_origin(n, left, right, value, edge)

    fn filtered_appended_state_origin_case(
      n: Nat,
      left: List(MachineState(n)),
      right: List(MachineState(n)),
      boundary: Boundary,
      value: MachineState(n),
      edge: ListMember(MachineState(n), value, filter_machine_states(n, append_machine_states(n, left, right), boundary))
    ) -> FilteredAppendMemberOrigin(n, filter_machine_states(n, left, boundary), filter_machine_states(n, right, boundary), value) =
      filtered_append_member_origin(n, left, right, boundary, value, edge)

    fn left_filtered_alternate_state_origin_case(
      left_count: Nat,
      right_count: Nat,
      states: List(MachineState(left_count)),
      boundary: Boundary,
      combined: MachineState(plus(left_count, right_count)),
      edge: ListMember(MachineState(plus(left_count, right_count)), combined, filter_machine_states(plus(left_count, right_count), alternate_left_states(left_count, right_count, states, EmitLeft()), boundary))
    ) -> FilteredLeftMarkedStateOrigin(left_count, right_count, EmitLeft(), filter_machine_states(left_count, states, boundary), combined) =
      filtered_left_marked_state_origin(left_count, right_count, states, EmitLeft(), boundary, combined, edge)

    fn right_filtered_alternate_state_origin_case(
      left_count: Nat,
      right_count: Nat,
      states: List(MachineState(right_count)),
      boundary: Boundary,
      combined: MachineState(plus(left_count, right_count)),
      edge: ListMember(MachineState(plus(left_count, right_count)), combined, filter_machine_states(plus(left_count, right_count), alternate_right_states(left_count, right_count, states, EmitRight()), boundary))
    ) -> FilteredRightMarkedStateOrigin(left_count, right_count, EmitRight(), filter_machine_states(right_count, states, boundary), combined) =
      filtered_right_marked_state_origin(left_count, right_count, states, EmitRight(), boundary, combined, edge)

    fn alternate_initial_origin_case(
      left_count: Nat,
      left_starts: List(MachineState(left_count)),
      right_count: Nat,
      right_starts: List(MachineState(right_count)),
      prefer_right: Bool,
      boundary: Boundary,
      combined: MachineState(plus(left_count, right_count)),
      edge: ListMember(MachineState(plus(left_count, right_count)), combined, filter_machine_states(plus(left_count, right_count), alternate_machine_starts(left_count, left_starts, right_starts, prefer_right), boundary))
    ) -> AlternateInitialOrigin(left_count, right_count, filter_machine_states(left_count, left_starts, boundary), filter_machine_states(right_count, right_starts, boundary), combined) =
      alternate_initial_origin(left_count, left_starts, right_count, right_starts, prefer_right, boundary, combined, edge)

    fn alternate_left_transition_origin_case(
      left_count: Nat,
      left_starts: List(MachineState(left_count)),
      left_next: (Bounded(left_count)) -> Char -> List(MachineState(left_count)),
      right_count: Nat,
      right_starts: List(MachineState(right_count)),
      right_next: (Bounded(right_count)) -> Char -> List(MachineState(right_count)),
      prefer_right: Bool,
      source: Bounded(left_count),
      char: Char,
      boundary: Boundary,
      combined: MachineState(plus(left_count, right_count)),
      edge: ListMember(MachineState(plus(left_count, right_count)), combined, machine_destinations(plus(left_count, right_count), alternate_pattern_machine(left_count, MkPatternMachine(left_starts, left_next), right_count, MkPatternMachine(right_starts, right_next), prefer_right), ThreadActive(inject_alternate_left(left_count, right_count, source)), char, boundary))
    ) -> FilteredLeftMarkedStateOrigin(left_count, right_count, EmitLeft(), filter_machine_states(left_count, left_next(source, char), boundary), combined) =
      alternate_left_transition_origin(left_count, left_starts, left_next, right_count, right_starts, right_next, prefer_right, source, char, boundary, combined, edge)

    fn alternate_right_transition_origin_case(
      left_count: Nat,
      left_starts: List(MachineState(left_count)),
      left_next: (Bounded(left_count)) -> Char -> List(MachineState(left_count)),
      right_count: Nat,
      right_starts: List(MachineState(right_count)),
      right_next: (Bounded(right_count)) -> Char -> List(MachineState(right_count)),
      prefer_right: Bool,
      source: Bounded(right_count),
      char: Char,
      boundary: Boundary,
      combined: MachineState(plus(left_count, right_count)),
      edge: ListMember(MachineState(plus(left_count, right_count)), combined, machine_destinations(plus(left_count, right_count), alternate_pattern_machine(left_count, MkPatternMachine(left_starts, left_next), right_count, MkPatternMachine(right_starts, right_next), prefer_right), ThreadActive(inject_alternate_right(left_count, right_count, source)), char, boundary))
    ) -> FilteredRightMarkedStateOrigin(left_count, right_count, EmitRight(), filter_machine_states(right_count, right_next(source, char), boundary), combined) =
      alternate_right_transition_origin(left_count, left_starts, left_next, right_count, right_starts, right_next, prefer_right, source, char, boundary, combined, edge)

    fn split_appended_routine_execution_case(
      left: List(EvidenceInstruction),
      right: List(EvidenceInstruction),
      input_evidence: List(Evidence),
      input_captures: List(CaptureFrame),
      {output_evidence: List(Evidence)},
      {output_captures: List(CaptureFrame)},
      execution: RoutineExecution(append_routine(left, right), input_evidence, input_captures, output_evidence, output_captures)
    ) -> AppendedRoutineExecution(left, right, input_evidence, input_captures, output_evidence, output_captures) =
      split_appended_routine_execution(left, right, input_evidence, input_captures, execution)

    fn left_marker_encodes_case(
      {left: ShapeCode},
      {right: ShapeCode},
      {branch_evidence: List(Evidence)},
      {rest: List(Evidence)},
      captures: List(CaptureFrame),
      branch: Encodes(left, branch_evidence, rest),
      execution: RoutineExecution(Cons(EmitLeft(), Nil()), branch_evidence, captures, Cons(LeftEvidence(), branch_evidence), captures)
    ) -> Encodes(ChoiceC(left, right), Cons(LeftEvidence(), branch_evidence), rest) =
      left_marker_execution_encodes(branch, execution)

    fn project_alternate_left_path_case(
      left_count: Nat,
      left_machine: PatternMachine(left_count),
      right_count: Nat,
      right_machine: PatternMachine(right_count),
      prefer_right: Bool,
      input: List(Char),
      after_input: List(Char),
      source: Bounded(left_count),
      current_evidence: List(Evidence),
      captures: List(CaptureFrame),
      {final_evidence: List(Evidence)},
      {routine: List(ExtendedInstruction)},
      path: AcceptingFrom(plus(left_count, right_count), alternate_pattern_machine(left_count, left_machine, right_count, right_machine, prefer_right), input, after_input, ThreadActive(inject_alternate_left(left_count, right_count, source)), current_evidence, captures, final_evidence, routine)
    ) -> AlternateLeftPathProjection(left_count, left_machine, input, after_input, source, current_evidence, captures, final_evidence) =
      project_alternate_left_path(left_count, left_machine, right_count, right_machine, prefer_right, input, after_input, source, current_evidence, captures, path)

    fn project_alternate_right_path_case(
      left_count: Nat,
      left_machine: PatternMachine(left_count),
      right_count: Nat,
      right_machine: PatternMachine(right_count),
      prefer_right: Bool,
      input: List(Char),
      after_input: List(Char),
      source: Bounded(right_count),
      current_evidence: List(Evidence),
      captures: List(CaptureFrame),
      {final_evidence: List(Evidence)},
      {routine: List(ExtendedInstruction)},
      path: AcceptingFrom(plus(left_count, right_count), alternate_pattern_machine(left_count, left_machine, right_count, right_machine, prefer_right), input, after_input, ThreadActive(inject_alternate_right(left_count, right_count, source)), current_evidence, captures, final_evidence, routine)
    ) -> AlternateRightPathProjection(right_count, right_machine, input, after_input, source, current_evidence, captures, final_evidence) =
      project_alternate_right_path(left_count, left_machine, right_count, right_machine, prefer_right, input, after_input, source, current_evidence, captures, path)

    fn acceptance_path_case(
      n: Nat,
      machine: PatternMachine(n),
      position: InitialPosition,
      input: List(Char),
      after_input: List(Char),
      {final_evidence: List(Evidence)},
      {routine: List(ExtendedInstruction)},
      acceptance: MachineAcceptance(n, machine, position, input, after_input, final_evidence, routine)
    ) -> AcceptancePath(n, machine, position, input, after_input, final_evidence) =
      machine_acceptance_path(n, machine, position, input, after_input, acceptance)

    fn predicate_alternate_evidence_proof(
      left: Char -> Bool,
      right: Char -> Bool,
      prefer_right: Bool
    ) -> ThompsonEvidenceProof(
      ChoiceC(CharC(), CharC()),
      ThompsonAlternate(ThompsonPredicate(left), ThompsonPredicate(right), prefer_right)
    ) =
      ThompsonEvidenceAlternate(
        ThompsonPredicate(left),
        ThompsonPredicate(right),
        prefer_right,
        ThompsonEvidencePredicate(left),
        ThompsonEvidencePredicate(right)
      )

    fn predicate_concat_evidence_proof(
      left: Char -> Bool,
      right: Char -> Bool
    ) -> ThompsonEvidenceProof(
      PairC(CharC(), CharC()),
      ThompsonConcat(ThompsonPredicate(left), ThompsonPredicate(right))
    ) =
      ThompsonEvidenceConcat(
        ThompsonPredicate(left),
        ThompsonPredicate(right),
        ThompsonEvidencePredicate(left),
        ThompsonEvidencePredicate(right)
      )

    fn grouped_predicate_evidence_proof(
      test: Char -> Bool
    ) -> ThompsonEvidenceProof(
      StringC(),
      ThompsonGroup(ThompsonPredicate(test))
    ) =
      ThompsonEvidenceGroup(
        ThompsonPredicate(test),
        ThompsonEvidencePredicate(test)
      )

    @reducible
    fn repeated_predicate_compilation(test: Char -> Bool, lazy: Bool) -> ThompsonCompilation(ListC(CharC())) =
      ThompsonRepeat(ThompsonPredicate(test), lazy)

    @reducible
    fn repeated_predicate_evidence_proof(
      test: Char -> Bool,
      lazy: Bool
    ) -> ThompsonEvidenceProof(
      ListC(CharC()),
      repeated_predicate_compilation(test, lazy)
    ) =
      ThompsonEvidenceRepeat(
        ThompsonPredicate(test),
        lazy,
        ThompsonEvidencePredicate(test)
      )

    fn enter_repeat_origin_case(
      n: Nat,
      routine: List(EvidenceInstruction),
      constraints: List(BoundaryConstraint),
      starts: List(MachineState(n)),
      entered: MachineState(n),
      edge: ListMember(
        MachineState(n),
        entered,
        enter_repeat_with_constraints(routine, constraints, starts)
      )
    ) -> EnterRepeatStateOrigin(n, routine, constraints, starts, entered) =
      enter_repeat_state_origin(n, routine, constraints, starts, entered, edge)

    fn repeat_destination_order_origin_case(
      n: Nat,
      routine: List(EvidenceInstruction),
      constraints: List(BoundaryConstraint),
      starts: List(MachineState(n)),
      lazy: Bool,
      destination: MachineState(n),
      edge: ListMember(
        MachineState(n),
        destination,
        repeat_destination_order(routine, constraints, starts, lazy)
      )
    ) -> RepeatDestinationOrderOrigin(n, routine, constraints, starts, lazy, destination) =
      repeat_destination_order_origin(n, routine, constraints, starts, lazy, destination, edge)

    fn repeat_destinations_origin_case(
      n: Nat,
      destinations: List(MachineState(n)),
      starts: List(MachineState(n)),
      lazy: Bool,
      destination: MachineState(n),
      edge: ListMember(
        MachineState(n),
        destination,
        repeat_destinations(destinations, starts, lazy)
      )
    ) -> RepeatDestinationsOrigin(n, destinations, starts, lazy, destination) =
      repeat_destinations_origin(n, destinations, starts, lazy, destination, edge)

    fn filtered_repeat_destinations_origin_case(
      n: Nat,
      destinations: List(MachineState(n)),
      starts: List(MachineState(n)),
      lazy: Bool,
      boundary: Boundary,
      filtered: MachineState(n),
      edge: ListMember(
        MachineState(n),
        filtered,
        filter_machine_states(n, repeat_destinations(destinations, starts, lazy), boundary)
      )
    ) -> FilteredRepeatDestinationsOrigin(n, destinations, starts, lazy, boundary, filtered) =
      filtered_repeat_destinations_origin(n, destinations, starts, lazy, boundary, filtered, edge)

    fn filtered_repeat_starts_origin_case(
      n: Nat,
      starts: List(MachineState(n)),
      lazy: Bool,
      boundary: Boundary,
      filtered: MachineState(n),
      edge: ListMember(
        MachineState(n),
        filtered,
        filter_machine_states(n, repeat_machine_starts(starts, lazy), boundary)
      )
    ) -> FilteredRepeatStartsOrigin(n, starts, lazy, boundary, filtered) =
      filtered_repeat_starts_origin(n, starts, lazy, boundary, filtered, edge)

    fn generic_predicate_alternate_acceptance_case(
      left: Char -> Bool,
      right: Char -> Bool,
      prefer_right: Bool,
      input: List(Char),
      after_input: List(Char),
      position: InitialPosition,
      final_evidence: List(Evidence),
      acceptance: AcceptancePath(
        plus(S(Z()), S(Z())),
        predicate_alternate_mode_machine(left, right, prefer_right),
        position,
        input,
        after_input,
        final_evidence
      )
    ) -> Encodes(ChoiceC(CharC(), CharC()), final_evidence, empty_evidence()) =
      thompson_evidence_acceptance_encodes(
        ThompsonAlternate(
          ThompsonPredicate(left),
          ThompsonPredicate(right),
          prefer_right
        ),
        predicate_alternate_evidence_proof(left, right, prefer_right),
        input,
        after_input,
        position,
        acceptance
      )

    fn generic_predicate_alternate_total_extraction(
      left: Char -> Bool,
      right: Char -> Bool,
      prefer_right: Bool,
      input: List(Char),
      after_input: List(Char),
      position: InitialPosition,
      final_evidence: List(Evidence),
      acceptance: AcceptancePath(
        plus(S(Z()), S(Z())),
        predicate_alternate_mode_machine(left, right, prefer_right),
        position,
        input,
        after_input,
        final_evidence
      )
    ) -> Sem(ChoiceC(CharC(), CharC())) =
      let compilation = ThompsonAlternate(
        ThompsonPredicate(left),
        ThompsonPredicate(right),
        prefer_right
      )
      let certificate = thompson_evidence_acceptance_encodes(
        compilation,
        predicate_alternate_evidence_proof(left, right, prefer_right),
        input,
        after_input,
        position,
        acceptance
      )
      extract_encoding(final_evidence, certificate)

    fn generic_predicate_alternate_acceptance_from_case(
      left: Char -> Bool,
      right: Char -> Bool,
      prefer_right: Bool,
      input: List(Char),
      after_input: List(Char),
      position: InitialPosition,
      input_evidence: List(Evidence),
      input_captures: List(CaptureFrame),
      {final_evidence: List(Evidence)},
      acceptance: AcceptancePathFrom(
        plus(S(Z()), S(Z())),
        predicate_alternate_mode_machine(left, right, prefer_right),
        position,
        input,
        after_input,
        input_evidence,
        input_captures,
        final_evidence
      )
    ) -> Encodes(ChoiceC(CharC(), CharC()), final_evidence, input_evidence) =
      thompson_evidence_acceptance_from_encodes(
        ThompsonAlternate(
          ThompsonPredicate(left),
          ThompsonPredicate(right),
          prefer_right
        ),
        predicate_alternate_evidence_proof(left, right, prefer_right),
        input,
        after_input,
        position,
        input_evidence,
        input_captures,
        acceptance
      )

    fn generic_empty_acceptance_case(
      input: List(Char),
      after_input: List(Char),
      position: InitialPosition,
      {final_evidence: List(Evidence)},
      acceptance: AcceptancePath(
        Z(),
        empty_pattern_machine(),
        position,
        input,
        after_input,
        final_evidence
      )
    ) -> Encodes(UnitC(), final_evidence, empty_evidence()) =
      thompson_evidence_acceptance_encodes(
        ThompsonEmpty(),
        ThompsonEvidenceEmpty(),
        input,
        after_input,
        position,
        acceptance
      )

    fn generic_boundary_acceptance_case(
      constraint: BoundaryConstraint,
      input: List(Char),
      after_input: List(Char),
      position: InitialPosition,
      {final_evidence: List(Evidence)},
      acceptance: AcceptancePath(
        Z(),
        boundary_pattern_machine(constraint),
        position,
        input,
        after_input,
        final_evidence
      )
    ) -> Encodes(UnitC(), final_evidence, empty_evidence()) =
      thompson_evidence_acceptance_encodes(
        ThompsonBoundary(constraint),
        ThompsonEvidenceBoundary(constraint),
        input,
        after_input,
        position,
        acceptance
      )

    fn generic_predicate_alternate_machine_acceptance_case(
      left: Char -> Bool,
      right: Char -> Bool,
      prefer_right: Bool,
      input: List(Char),
      after_input: List(Char),
      position: InitialPosition,
      {final_evidence: List(Evidence)},
      {routine: List(ExtendedInstruction)},
      acceptance: MachineAcceptance(
        plus(S(Z()), S(Z())),
        predicate_alternate_mode_machine(left, right, prefer_right),
        position,
        input,
        after_input,
        final_evidence,
        routine
      )
    ) -> Encodes(ChoiceC(CharC(), CharC()), final_evidence, empty_evidence()) =
      thompson_machine_acceptance_encodes(
        ThompsonAlternate(
          ThompsonPredicate(left),
          ThompsonPredicate(right),
          prefer_right
        ),
        predicate_alternate_evidence_proof(left, right, prefer_right),
        input,
        after_input,
        position,
        acceptance
      )

    fn certified_predicate_acceptance_case(
      input: List(Char),
      after_input: List(Char),
      @erased final_evidence: List(Evidence),
      @erased routine: List(ExtendedInstruction),
      acceptance: MachineAcceptance(1, predicate_pattern_machine(accepts_a), subject_initial_position(), input, after_input, final_evidence, routine)
    ) -> Encodes(CharC, final_evidence, empty_evidence()) =
      certified_pattern_acceptance_encodes(
        certify_predicate_pattern_machine(accepts_a),
        input,
        after_input,
        subject_initial_position(),
        final_evidence,
        routine,
        acceptance
      )

    fn certified_empty_acceptance_case(
      input: List(Char),
      after_input: List(Char),
      @erased final_evidence: List(Evidence),
      @erased routine: List(ExtendedInstruction),
      acceptance: MachineAcceptance(0, empty_pattern_machine(), subject_initial_position(), input, after_input, final_evidence, routine)
    ) -> Encodes(UnitC, final_evidence, empty_evidence()) =
      certified_pattern_acceptance_encodes(certify_empty_pattern_machine(), input, after_input, subject_initial_position(), final_evidence, routine, acceptance)

    fn certified_boundary_acceptance_case(
      constraint: BoundaryConstraint,
      input: List(Char),
      after_input: List(Char),
      @erased final_evidence: List(Evidence),
      @erased routine: List(ExtendedInstruction),
      acceptance: MachineAcceptance(0, boundary_pattern_machine(constraint), subject_initial_position(), input, after_input, final_evidence, routine)
    ) -> Encodes(UnitC, final_evidence, empty_evidence()) =
      certified_pattern_acceptance_encodes(certify_boundary_pattern_machine(constraint), input, after_input, subject_initial_position(), final_evidence, routine, acceptance)

    fn grouped_predicate_acceptance_case(
      @erased final_evidence: List(Evidence),
      @erased routine: List(ExtendedInstruction),
      acceptance: MachineAcceptance(
        1,
        group_pattern_machine(1, Cons(predicate_machine_start(), Nil()), predicate_machine_next(accepts_a)),
        subject_initial_position(),
        Cons('a', empty_characters()),
        empty_characters(),
        final_evidence,
        routine
      )
    ) -> Encodes(StringC, final_evidence, empty_evidence()) =
      grouped_predicate_machine_acceptance_encodes(
        accepts_a,
        'a',
        empty_characters(),
        subject_initial_position(),
        final_evidence,
        routine,
        acceptance
      )

    fn predicate_concat_acceptance_case(
      @erased final_evidence: List(Evidence),
      @erased routine: List(ExtendedInstruction),
      acceptance: MachineAcceptance(
        plus(1, 1),
        predicate_concat_machine(accepts_a, accepts_b),
        subject_initial_position(),
        Cons('a', Cons('b', empty_characters())),
        empty_characters(),
        final_evidence,
        routine
      )
    ) -> Encodes(PairC(CharC, CharC), final_evidence, empty_evidence()) =
      predicate_concat_machine_acceptance_encodes(
        accepts_a,
        accepts_b,
        'a',
        'b',
        empty_characters(),
        subject_initial_position(),
        final_evidence,
        routine,
        acceptance
      )

    fn predicate_alternate_acceptance_case(
      @erased final_evidence: List(Evidence),
      @erased routine: List(ExtendedInstruction),
      acceptance: MachineAcceptance(
        plus(1, 1),
        predicate_alternate_machine(accepts_a, accepts_b),
        subject_initial_position(),
        Cons('a', empty_characters()),
        empty_characters(),
        final_evidence,
        routine
      )
    ) -> Encodes(ChoiceC(CharC, CharC), final_evidence, empty_evidence()) =
      predicate_alternate_machine_acceptance_encodes(
        accepts_a,
        accepts_b,
        'a',
        empty_characters(),
        subject_initial_position(),
        final_evidence,
        routine,
        acceptance
      )

    fn predicate_alternate_right_acceptance_case(
      @erased final_evidence: List(Evidence),
      @erased routine: List(ExtendedInstruction),
      acceptance: MachineAcceptance(
        plus(1, 1),
        predicate_alternate_machine(accepts_a, accepts_b),
        subject_initial_position(),
        Cons('b', empty_characters()),
        empty_characters(),
        final_evidence,
        routine
      )
    ) -> Encodes(ChoiceC(CharC, CharC), final_evidence, empty_evidence()) =
      predicate_alternate_machine_acceptance_encodes(
        accepts_a,
        accepts_b,
        'b',
        empty_characters(),
        subject_initial_position(),
        final_evidence,
        routine,
        acceptance
      )

    fn predicate_alternate_mode_acceptance_case(
      prefer_right: Bool,
      @erased final_evidence: List(Evidence),
      @erased routine: List(ExtendedInstruction),
      acceptance: MachineAcceptance(
        plus(1, 1),
        predicate_alternate_mode_machine(accepts_a, accepts_a, prefer_right),
        subject_initial_position(),
        Cons('a', empty_characters()),
        empty_characters(),
        final_evidence,
        routine
      )
    ) -> Encodes(ChoiceC(CharC, CharC), final_evidence, empty_evidence()) =
      predicate_alternate_mode_machine_acceptance_encodes(
        accepts_a,
        accepts_a,
        prefer_right,
        'a',
        empty_characters(),
        subject_initial_position(),
        final_evidence,
        routine,
        acceptance
      )

    fn ambiguous_left_search() -> MachineAcceptingSearch(plus(1, 1), predicate_alternate_mode_machine(accepts_a, accepts_a, False()), subject_initial_position(), Cons('a', Nil()), Nil()) =
      search_machine_acceptance(plus(1, 1), predicate_alternate_mode_machine(accepts_a, accepts_a, False()), subject_initial_position(), ['a'], [])

    fn ambiguous_right_search() -> MachineAcceptingSearch(plus(1, 1), predicate_alternate_mode_machine(accepts_a, accepts_a, True()), subject_initial_position(), Cons('a', Nil()), Nil()) =
      search_machine_acceptance(plus(1, 1), predicate_alternate_mode_machine(accepts_a, accepts_a, True()), subject_initial_position(), ['a'], [])

    fn predicate_repeat_acceptance_case(
      input: List(Char),
      lazy: Bool,
      @erased final_evidence: List(Evidence),
      @erased routine: List(ExtendedInstruction),
      acceptance: MachineAcceptance(
        1,
        thompson_machine(repeated_predicate_compilation(accepts_a, lazy)),
        subject_initial_position(),
        input,
        empty_characters(),
        final_evidence,
        routine
      )
    ) -> Encodes(ListC(CharC), final_evidence, empty_evidence()) =
      thompson_machine_acceptance_encodes_explicit(
        ListC(CharC),
        repeated_predicate_compilation(accepts_a, lazy),
        repeated_predicate_evidence_proof(accepts_a, lazy),
        input,
        empty_characters(),
        subject_initial_position(),
        acceptance
      )

    fn predicate_repeat_total_extraction(
      input: List(Char),
      lazy: Bool,
      final_evidence: List(Evidence),
      @erased routine: List(ExtendedInstruction),
      acceptance: MachineAcceptance(
        1,
        thompson_machine(repeated_predicate_compilation(accepts_a, lazy)),
        subject_initial_position(),
        input,
        empty_characters(),
        final_evidence,
        routine
      )
    ) -> List(Char) =
      extract_encoding(
        final_evidence,
        predicate_repeat_acceptance_case(
          input,
          lazy,
          final_evidence,
          routine,
          acceptance
        )
      )

    @reducible
    fn repeated_alternate_compilation(lazy: Bool) -> ThompsonCompilation(ListC(ChoiceC(CharC(), CharC()))) =
      ThompsonRepeat(
        ThompsonAlternate(
          ThompsonPredicate(accepts_a),
          ThompsonPredicate(accepts_b),
          False()
        ),
        lazy
      )

    fn repeated_alternate_proof(lazy: Bool) -> ThompsonEvidenceProof(
      ListC(ChoiceC(CharC(), CharC())),
      repeated_alternate_compilation(lazy)
    ) =
      ThompsonEvidenceRepeat(
        ThompsonAlternate(
          ThompsonPredicate(accepts_a),
          ThompsonPredicate(accepts_b),
          False()
        ),
        lazy,
        predicate_alternate_evidence_proof(accepts_a, accepts_b, False())
      )

    fn repeated_alternate_total_extraction(
      input: List(Char),
      lazy: Bool,
      final_evidence: List(Evidence),
      @erased routine: List(ExtendedInstruction),
      acceptance: MachineAcceptance(
        2,
        thompson_machine(repeated_alternate_compilation(lazy)),
        subject_initial_position(),
        input,
        empty_characters(),
        final_evidence,
        routine
      )
    ) -> List(Choice(Char, Char)) =
      extract_encoding(
        final_evidence,
        thompson_machine_acceptance_encodes_explicit(
          ListC(ChoiceC(CharC, CharC)),
          repeated_alternate_compilation(lazy),
          repeated_alternate_proof(lazy),
          input,
          empty_characters(),
          subject_initial_position(),
          acceptance
        )
      )

    fn repeated_greedy() -> MachineAcceptingSearch(1, thompson_machine(repeated_predicate_compilation(accepts_a, False())), subject_initial_position(), Cons('a', Cons('a', Nil())), Nil()) =
      search_machine_acceptance(1, thompson_machine(repeated_predicate_compilation(accepts_a, False())), subject_initial_position(), ['a', 'a'], [])

    fn repeated_lazy() -> MachineAcceptingSearch(1, thompson_machine(repeated_predicate_compilation(accepts_a, True())), subject_initial_position(), Cons('a', Cons('a', Nil())), Nil()) =
      search_machine_acceptance(1, thompson_machine(repeated_predicate_compilation(accepts_a, True())), subject_initial_position(), ['a', 'a'], [])

    fn repeated_empty() -> MachineAcceptingSearch(1, thompson_machine(repeated_predicate_compilation(accepts_a, False())), subject_initial_position(), Nil(), Nil()) =
      search_machine_acceptance(1, thompson_machine(repeated_predicate_compilation(accepts_a, False())), subject_initial_position(), [], [])

    fn end_machine() -> PatternMachine(0) =
      MkPatternMachine([Accepted([EmitUnit()], [subject_end_constraint()])], zero_next)

    fn end_before_suffix() -> MachineAcceptingSearch(0, end_machine(), subject_initial_position(), Nil(), Cons('a', Nil())) =
      search_machine_acceptance(0, end_machine(), subject_initial_position(), [], ['a'])

    fn end_at_subject_end() -> MachineAcceptingSearch(0, end_machine(), subject_initial_position(), Nil(), Nil()) =
      search_machine_acceptance(0, end_machine(), subject_initial_position(), [], [])

    fn extended_regular() -> ExtendedExecution =
      execute_extended_routine(regular_routine([EmitUnit()]), None(), [], [])

    fn extended_capture() -> ExtendedExecution =
      match execute_extended_routine(regular_routine([BeginCapture()]), None(), [], [])
        ExtendedExecution(current, evidence, captures) ->
          execute_extended_routine(transition_routine('a', [EmitChar('a'), EndCapture()]), current, evidence, captures)

    fn erase_extended_certificate(@erased _certificate: ExtendedRoutineExecution(Cons(Regular(EmitUnit()), Nil()), None(), Nil(), Nil(), None(), Cons(UnitEvidence(), Nil()), Nil())) -> Unit = ()

    fn extended_certificate_erased() -> Unit =
      erase_extended_certificate(certify_extended_routine([Regular(EmitUnit())], None(), [], []))
  """

  test "an accepting path fixes the winning thread's evidence in its result index" do
    assert {:ok, env} = Program.elaborate(@source)

    assert Env.get_def(env, :one_step)
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :one_step))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :predicate_extended_routine_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :group_character_extended_routine_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :predicate_path_routine_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :empty_acceptance_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :boundary_acceptance_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :predicate_acceptance_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :predicate_arbitrary_input_acceptance_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :certified_predicate_machine_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :certified_predicate_acceptance_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :certified_empty_acceptance_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :certified_boundary_acceptance_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :nested_thompson_compilation_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :nested_thompson_compiled_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :nested_alternate_machine_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :left_alternate_state_origin_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :right_alternate_state_origin_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :appended_state_origin_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :filtered_appended_state_origin_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :left_filtered_alternate_state_origin_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :right_filtered_alternate_state_origin_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :alternate_initial_origin_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :alternate_left_transition_origin_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :alternate_right_transition_origin_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :split_appended_routine_execution_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :left_marker_encodes_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :project_alternate_left_path_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :project_alternate_right_path_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :acceptance_path_case))
    assert Env.get_def(env, :"Std.Regex.Proof#AcceptancePathFrom")
    assert Env.total?(env, :"Std.Regex.Proof#extend_routine_execution")
    assert Env.total?(env, :"Std.Regex.Proof#append_extended_routine_execution")
    assert Env.total?(env, :"Std.Regex.Proof#split_appended_extended_routine_execution")
    assert Env.total?(env, :"Std.Regex.Proof#left_marker_execution_captures")
    assert Env.total?(env, :"Std.Regex.Proof#right_marker_execution_captures")
    assert Env.total?(env, :"Std.Regex.Runtime#alternate_left_injection_is_widening")
    assert Env.total?(env, :"Std.Regex.Runtime#alternate_left_widening_is_injection")
    assert Env.total?(env, :"Std.Regex.Runtime#alternate_right_injection_is_inject_right")
    assert Env.get_def(env, :"Std.Regex.Proof#AlternateLeftExecutedPathProjection")
    assert Env.total?(env, :"Std.Regex.Proof#project_alternate_left_executed_path")
    assert Map.has_key?(env.ctors, :"Std.Regex.Proof#ProjectedAlternateLeftSharedExecution")
    assert Env.total?(env, :"Std.Regex.Proof#project_alternate_left_shared_execution")
    assert Env.total?(env, :"Std.Regex.Proof#shared_execution_final_captures")
    assert Env.total?(env, :"Std.Regex.Proof#alternate_left_active_path_captures")
    assert Env.total?(env, :"Std.Regex.Proof#alternate_left_active_acceptance_captures")
    assert Env.total?(env, :"Std.Regex.Proof#alternate_left_accepted_acceptance_captures")
    assert Env.get_def(env, :"Std.Regex.Proof#AlternateRightExecutedPathProjection")
    assert Env.total?(env, :"Std.Regex.Proof#project_alternate_right_executed_path")
    assert Map.has_key?(env.ctors, :"Std.Regex.Proof#ProjectedAlternateRightSharedExecution")
    assert Env.total?(env, :"Std.Regex.Proof#project_alternate_right_shared_execution")
    assert Env.total?(env, :"Std.Regex.Proof#alternate_right_active_path_captures")
    assert Env.total?(env, :"Std.Regex.Proof#alternate_right_active_acceptance_captures")
    assert Env.total?(env, :"Std.Regex.Proof#alternate_right_accepted_acceptance_captures")
    assert Map.has_key?(env.ctors, :"Std.Regex.Proof#ProjectedAlternateLeftExecutedAcceptance")
    assert Env.total?(env, :"Std.Regex.Proof#execute_alternate_left_acceptance_projection")
    assert Map.has_key?(env.ctors, :"Std.Regex.Proof#ProjectedAlternateRightExecutedAcceptance")
    assert Env.total?(env, :"Std.Regex.Proof#execute_alternate_right_acceptance_projection")
    assert Env.get_def(env, :"Std.Regex.Proof#accepting_path_execution")
    assert Env.total?(env, :"Std.Regex.Proof#accepting_path_execution")
    assert Env.get_def(env, :"Std.Regex.Proof#accepting_path_execution_exact")
    assert Env.total?(env, :"Std.Regex.Proof#accepting_path_execution_exact")
    assert Env.get_def(env, :"Std.Regex.Proof#acceptance_path_execution_exact")
    assert Env.total?(env, :"Std.Regex.Proof#acceptance_path_execution_exact")
    assert Env.get_def(env, :"Std.Regex.Proof#acceptance_with_execution_captures")
    assert Env.total?(env, :"Std.Regex.Proof#acceptance_with_execution_captures")
    assert Env.total?(env, :"Std.Regex.Proof#accepting_final_captures")
    assert Env.total?(env, :"Std.Regex.Proof#acceptance_path_final_captures")
    assert Env.total?(env, :"Std.Regex.Proof#record_capture_input")
    assert Env.total?(env, :"Std.Regex.Proof#record_capture_partition")
    assert Env.total?(env, :"Std.Regex.Proof#record_capture_frame_input")
    assert Env.total?(env, :"Std.Regex.Proof#recorded_open_capture_view")
    assert Env.total?(env, :"Std.Regex.Proof#accepted_path_final_captures")
    assert Env.total?(env, :"Std.Regex.Proof#accepted_path_input_empty")
    assert Env.total?(env, :"Std.Regex.Proof#empty_acceptance_captures")
    assert Env.total?(env, :"Std.Regex.Proof#boundary_acceptance_captures")
    assert Env.total?(env, :"Std.Regex.Proof#predicate_path_captures")
    assert Env.total?(env, :"Std.Regex.Proof#predicate_acceptance_captures")
    assert Env.get_def(env, :"Std.Regex.Proof#enter_repeat_state_origin")
    assert Env.total?(env, :"Std.Regex.Proof#enter_repeat_state_origin")
    assert Env.total?(env, :"RegexAcceptingPath#enter_repeat_origin_case")
    assert Env.get_def(env, :"Std.Regex.Proof#repeat_destination_order_origin")
    assert Env.total?(env, :"Std.Regex.Proof#repeat_destination_order_origin")
    assert Env.total?(env, :"RegexAcceptingPath#repeat_destination_order_origin_case")
    assert Env.get_def(env, :"Std.Regex.Proof#repeat_destinations_origin")
    assert Env.total?(env, :"Std.Regex.Proof#repeat_destinations_origin")
    assert Env.total?(env, :"RegexAcceptingPath#repeat_destinations_origin_case")
    assert Env.get_def(env, :"Std.Regex.Proof#filtered_repeat_destinations_origin")
    assert Env.total?(env, :"Std.Regex.Proof#filtered_repeat_destinations_origin")
    assert Env.total?(env, :"RegexAcceptingPath#filtered_repeat_destinations_origin_case")
    assert Env.get_def(env, :"Std.Regex.Proof#filtered_repeat_starts_origin")
    assert Env.total?(env, :"Std.Regex.Proof#filtered_repeat_starts_origin")
    assert Env.total?(env, :"RegexAcceptingPath#filtered_repeat_starts_origin_case")
    assert Env.get_def(env, :"Std.Regex.Proof#prepend_repeat_child_transition")
    assert Env.get_def(env, :"Std.Regex.Proof#project_repeat_closing_transition")
    assert Env.total?(env, :"Std.Regex.Proof#prepend_repeat_child_transition")
    assert Env.total?(env, :"Std.Regex.Proof#project_repeat_closing_transition")
    assert Env.get_def(env, :"Std.Regex.Proof#project_repeat_active_path")
    assert Env.get_def(env, :"Std.Regex.Proof#project_repeat_acceptance_from")
    assert Env.total?(env, :"Std.Regex.Proof#project_repeat_active_path")
    assert Env.total?(env, :"Std.Regex.Proof#project_repeat_acceptance_from")
    assert Env.total?(env, :"Std.Regex.Proof#prefix_routine_origin")
    assert Env.total?(env, :"Std.Regex.Proof#finish_capture_origin")
    assert Env.total?(env, :"Std.Regex.Proof#filtered_finish_capture_origin")
    assert Env.total?(env, :"Std.Regex.Proof#filtered_group_start_origin")
    assert Env.total?(env, :"Std.Regex.Proof#strip_begin_capture_execution")
    assert Env.total?(env, :"Std.Regex.Proof#split_end_capture_execution")
    assert Env.total?(env, :"Std.Regex.Proof#group_initial_origin")
    assert Env.total?(env, :"Std.Regex.Proof#group_transition_origin")
    assert Env.total?(env, :"Std.Regex.Proof#project_group_active_path")
    assert Env.total?(env, :"Std.Regex.Proof#project_group_acceptance_from")
    assert Env.total?(env, :"Std.Regex.Proof#routine_execution_unique")
    assert Env.total?(env, :"Std.Regex.Proof#extended_routine_execution_unique")
    assert Env.total?(env, :"Std.Regex.Proof#acceptance_extended_routine")
    assert Env.total?(env, :"Std.Regex.Proof#acceptance_path_execution")
    assert Env.total?(env, :"Std.Regex.Proof#acceptance_execution_matches")
    assert Env.total?(env, :"Std.Regex.Proof#acceptance_execution_witness")
    assert Env.total?(env, :"Std.Regex.Proof#group_child_execution_is_canonical")
    assert Env.total?(env, :"Std.Regex.Proof#acceptance_with_execution")
    assert Env.get_def(env, :"Std.Regex.Proof#empty_acceptance_path_from_encodes")
    assert Env.get_def(env, :"Std.Regex.Proof#boundary_acceptance_path_from_encodes")
    assert Env.get_def(env, :"Std.Regex.Proof#predicate_acceptance_path_from_encodes")
    assert Env.total?(env, :"Std.Regex.Proof#empty_acceptance_path_from_encodes")
    assert Env.total?(env, :"Std.Regex.Proof#boundary_acceptance_path_from_encodes")
    assert Env.total?(env, :"Std.Regex.Proof#predicate_acceptance_path_from_encodes")
    assert Env.get_def(env, :"Std.Regex.Proof#project_alternate_left_acceptance_from")
    assert Env.get_def(env, :"Std.Regex.Proof#project_alternate_right_acceptance_from")
    assert Env.get_def(env, :"Std.Regex.Proof#project_alternate_acceptance_from")
    assert Env.get_def(env, :"Std.Regex.Proof#thompson_evidence_acceptance_from_encodes")
    assert Env.get_def(env, :"Std.Regex.Proof#thompson_evidence_acceptance_captures")
    assert Env.total?(env, :"Std.Regex.Proof#project_alternate_acceptance_from")
    assert Env.total?(env, :"Std.Regex.Proof#thompson_evidence_acceptance_from_encodes")
    assert Env.total?(env, :"Std.Regex.Proof#thompson_evidence_acceptance_captures")

    thompson_reachable =
      Program.reachable_def_names(env, [
        :"Std.Regex.Proof#thompson_evidence_acceptance_from_encodes"
      ])

    # `reachable_def_names/2` is the post-erasure emission closure. This theorem
    # returns erased evidence, so its proof implementation and projection
    # dependencies are certified by totality above but do not become runtime
    # functions merely because the theorem is selected as an emission root.
    assert thompson_reachable == [
             :"Std.Regex.Proof#thompson_evidence_acceptance_from_encodes"
           ]

    assert Env.get_def(env, :"Std.Regex.Proof#concat_right_transition_origin")
    assert Env.total?(env, :"Std.Regex.Proof#concat_right_transition_origin")
    assert Env.get_def(env, :"Std.Regex.Proof#project_concat_right_path")
    assert Env.total?(env, :"Std.Regex.Proof#project_concat_right_path")
    assert Env.get_def(env, :"Std.Regex.Proof#enter_right_state_origin")
    assert Env.get_def(env, :"Std.Regex.Proof#continue_with_right_state_origin")
    assert Env.total?(env, :"Std.Regex.Proof#enter_right_state_origin")
    assert Env.total?(env, :"Std.Regex.Proof#continue_with_right_state_origin")
    assert Env.get_def(env, :"Std.Regex.Proof#filtered_state_origin")
    assert Env.total?(env, :"Std.Regex.Proof#filtered_state_origin")
    assert Env.get_def(env, :"Std.Regex.Proof#filtered_continue_with_right_state_origin")
    assert Env.total?(env, :"Std.Regex.Proof#filtered_continue_with_right_state_origin")
    assert Env.get_def(env, :"Std.Regex.Proof#concat_left_transition_origin")
    assert Env.total?(env, :"Std.Regex.Proof#concat_left_transition_origin")
    assert Env.total?(env, :"Std.Regex.Proof#appended_constraints_left_hold")
    assert Env.total?(env, :"Std.Regex.Proof#appended_constraints_right_hold")
    assert Env.total?(env, :"Std.Regex.Proof#filter_active_member")
    assert Env.total?(env, :"Std.Regex.Proof#filter_accepted_member")
    assert Env.get_def(env, :"Std.Regex.Proof#normalize_initial_active")
    assert Env.total?(env, :"Std.Regex.Proof#normalize_initial_active")
    assert Env.get_def(env, :"Std.Regex.Proof#normalize_initial_accepted")
    assert Env.total?(env, :"Std.Regex.Proof#normalize_initial_accepted")
    assert Env.get_def(env, :"Std.Regex.Proof#concat_initial_origin")
    assert Env.total?(env, :"Std.Regex.Proof#concat_initial_origin")
    assert Env.total?(env, :"Std.Regex.Runtime#advance_initial_position")
    assert Env.total?(env, :"Std.Regex.Proof#advanced_position_boundary")
    assert Env.get_def(env, :"Std.Regex.Proof#project_concat_entered_right_active_acceptance_from")
    assert Env.total?(env, :"Std.Regex.Proof#project_concat_entered_right_active_acceptance_from")
    assert Env.get_def(env, :"Std.Regex.Proof#project_concat_entered_right_accepted_acceptance_from")
    assert Env.total?(env, :"Std.Regex.Proof#project_concat_entered_right_accepted_acceptance_from")
    assert Env.get_def(env, :"Std.Regex.Proof#prepend_concat_left_projection")
    assert Env.total?(env, :"Std.Regex.Proof#prepend_concat_left_projection")
    assert Env.get_def(env, :"Std.Regex.Proof#project_concat_left_handoff_active")
    assert Env.total?(env, :"Std.Regex.Proof#project_concat_left_handoff_active")
    assert Env.get_def(env, :"Std.Regex.Proof#project_concat_left_handoff_accepted")
    assert Env.total?(env, :"Std.Regex.Proof#project_concat_left_handoff_accepted")
    assert Env.get_def(env, :"Std.Regex.Proof#project_concat_left_path")
    assert Env.total?(env, :"Std.Regex.Proof#project_concat_left_path")
    assert Env.get_def(env, :"Std.Regex.Proof#project_concat_acceptance_from")
    assert Env.total?(env, :"Std.Regex.Proof#project_concat_acceptance_from")
    assert Map.has_key?(env.ctors, :"Std.Regex.Proof#ProjectedExecutedConcatAcceptance")
    assert Env.total?(env, :"Std.Regex.Proof#execute_concat_acceptance_projection")
    assert Env.get_def(env, :"Std.Regex.Proof#project_alternate_left_acceptance")
    assert Env.total?(env, :"Std.Regex.Proof#project_alternate_left_acceptance")
    assert Env.get_def(env, :"Std.Regex.Proof#alternate_left_origin_acceptance_captures")
    assert Env.total?(env, :"Std.Regex.Proof#alternate_left_origin_acceptance_captures")
    assert Env.get_def(env, :"Std.Regex.Proof#alternate_right_origin_acceptance_captures")
    assert Env.total?(env, :"Std.Regex.Proof#alternate_right_origin_acceptance_captures")
    assert Env.get_def(env, :"Std.Regex.Proof#project_alternate_right_acceptance")
    assert Env.total?(env, :"Std.Regex.Proof#project_alternate_right_acceptance")
    assert Env.get_def(env, :"Std.Regex.Proof#project_alternate_acceptance")
    assert Env.total?(env, :"Std.Regex.Proof#project_alternate_acceptance")
    assert Env.get_def(env, :"Std.Regex.Proof#thompson_evidence_acceptance_encodes")
    assert Env.total?(env, :"Std.Regex.Proof#thompson_evidence_acceptance_encodes")
    assert Env.get_def(env, :"Std.Regex.Core#extract_encoding")
    assert Env.total?(env, :"Std.Regex.Core#extract_encoding")
    assert Env.total?(env, :generic_predicate_alternate_total_extraction)
    assert Env.total?(env, :repeated_predicate_evidence_proof)
    assert Env.total?(env, :predicate_repeat_total_extraction)
    assert Env.total?(env, :repeated_alternate_proof)
    assert Env.total?(env, :repeated_alternate_total_extraction)
    assert Env.get_def(env, :"Std.Regex.Proof#thompson_machine_acceptance_encodes")
    assert Env.total?(env, :"Std.Regex.Proof#thompson_machine_acceptance_encodes")
    assert Map.has_key?(env.ctors, :"Std.Regex.Proof#CertifiedThompson")
    assert Env.get_def(env, :"Std.Regex.Proof#certify_thompson_evidence")
    assert Env.total?(env, :"Std.Regex.Proof#certify_thompson_evidence")
    assert Env.get_def(env, :"Std.Regex.Proof#parse_pattern_full_verified")
    assert Env.total?(env, :"Std.Regex.Proof#parse_pattern_full_verified")
    assert Env.total?(env, :"Std.Regex.Proof#parse_program_full_verified")
    assert Env.total?(env, :"Std.Regex.Proof#parse_pattern_prefix_verified_at")
    assert Env.total?(env, :"Std.Regex.Proof#parse_program_prefix_chars_verified_at")
    assert Env.total?(env, :"Std.Regex.Proof#parse_program_prefix_verified_at")
    assert Map.has_key?(env.ctors, :"Std.Regex.Proof#ThompsonEvidenceBoundary")
    assert Map.has_key?(env.ctors, :"Std.Regex.Proof#ThompsonEvidenceConcat")
    assert Map.has_key?(env.ctors, :"Std.Regex.Proof#ThompsonEvidenceRepeat")
    assert Env.total?(env, :"Std.Regex.Proof#project_repeat_acceptance_from_machine")
    assert Env.total?(env, :"Std.Regex.Proof#thompson_repeat_projection_encodes_many")
    assert Env.total?(env, :"Std.Regex.Proof#thompson_repeat_projection_captures")
    assert Env.total?(env, :"Std.Regex.Proof#thompson_repeat_acceptance_from_encodes")
    assert Env.total?(env, :"Std.Regex.Proof#thompson_repeat_acceptance_captures")

    assert Env.certified?(
             env,
             Env.resolve_key(env, env.defs, :predicate_concat_evidence_proof)
           )

    assert Env.certified?(
             env,
             Env.resolve_key(env, env.defs, :generic_predicate_alternate_acceptance_case)
           )

    assert Env.certified?(
             env,
             Env.resolve_key(
               env,
               env.defs,
               :generic_predicate_alternate_acceptance_from_case
             )
           )

    assert Env.certified?(
             env,
             Env.resolve_key(env, env.defs, :generic_empty_acceptance_case)
           )

    assert Env.certified?(
             env,
             Env.resolve_key(env, env.defs, :generic_boundary_acceptance_case)
           )

    assert Env.certified?(
             env,
             Env.resolve_key(
               env,
               env.defs,
               :generic_predicate_alternate_machine_acceptance_case
             )
           )

    assert Env.certified?(env, Env.resolve_key(env, env.defs, :grouped_predicate_acceptance_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :predicate_concat_acceptance_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :predicate_alternate_acceptance_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :predicate_alternate_right_acceptance_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :predicate_repeat_acceptance_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :predicate_alternate_mode_acceptance_case))
  end

  test "the path proof is erased from the emitted runtime" do
    assert {:ok, module} = Cure.Compiler.compile_and_load(@source, emit_events: false)
    assert apply(module, :one_step_erased, []) == :unit
  end

  test "a mutated machine cannot reuse the canonical predicate certificate" do
    source = """
    mod MutatedPredicateCertificate
      use Std.Regex
      use Std.Regex.Proof

      fn accepts(_char: Char) -> Bool = true
      fn mutated_next(_state: Bounded(1), _char: Char) -> List(MachineState(1)) =
        [Accepted([EmitUnit()], [])]
      fn mutated_machine() -> PatternMachine(1) =
        MkPatternMachine([predicate_machine_start()], mutated_next)

      fn invalid(
        input: List(Char),
        after_input: List(Char),
        @erased final_evidence: List(Evidence),
        @erased routine: List(ExtendedInstruction),
        acceptance: MachineAcceptance(1, mutated_machine(), subject_initial_position(), input, after_input, final_evidence, routine)
      ) -> Encodes(CharC, final_evidence, empty_evidence()) =
        certified_pattern_acceptance_encodes(
          certify_predicate_pattern_machine(accepts),
          input,
          after_input,
          subject_initial_position(),
          final_evidence,
          routine,
          acceptance
        )
    """

    assert {:error, {:source_context, {:index_mismatch, {:cannot_unify, _, _}}, _}} =
             Program.elaborate(source)
  end

  test "published certificate constructors reduce through their machine projections" do
    source = """
    mod ProjectedPatternCertificate
      use Std.Regex
      use Std.Regex.Proof

      fn accepts(_char: Char) -> Bool = true
      fn projected_state_count() -> Equivalent(Nat, certified_pattern_state_count(certify_predicate_pattern_machine(accepts)), S(Z())) =
        reflexive(S(Z()))
      fn projected_machine() -> Equivalent(PatternMachine(S(Z())), certified_pattern_machine(certify_predicate_pattern_machine(accepts)), predicate_pattern_machine(accepts)) =
        reflexive(predicate_pattern_machine(accepts))
    """

    assert {:ok, _} = Program.elaborate(source)
  end

  test "execution produces an accepting certificate with the winning evidence" do
    assert {:ok, module} = Cure.Compiler.compile_and_load(@source, emit_events: false)

    assert apply(module, :searched_machine, []) ==
             {:MachineAcceptingPath, [{:CharacterEvidence, ?a}], [{:Observe, ?a}, {:Regular, {:EmitChar, ?a}}]}

    assert apply(module, :searched_empty, []) == :NoAcceptingPath

    assert {:MachineAcceptingPath, [:LeftEvidence, {:CharacterEvidence, ?a}], _} =
             apply(module, :ambiguous_left_search, [])

    assert {:MachineAcceptingPath, [:RightEvidence, {:CharacterEvidence, ?a}], _} =
             apply(module, :ambiguous_right_search, [])

    repeated_evidence = [:EndListEvidence, {:CharacterEvidence, ?a}, {:CharacterEvidence, ?a}, :BeginListEvidence]

    assert {:MachineAcceptingPath, ^repeated_evidence, _routine} = apply(module, :repeated_greedy, [])
    assert {:MachineAcceptingPath, ^repeated_evidence, _routine} = apply(module, :repeated_lazy, [])

    assert apply(module, :repeated_empty, []) ==
             {:MachineAcceptingPath, [:EndListEvidence, :BeginListEvidence],
              [{:Regular, :BeginList}, {:Regular, :EndList}]}
  end

  test "certified prefix search preserves shortest and longest choices" do
    assert {:ok, module} = Cure.Compiler.compile_and_load(@source, emit_events: false)

    assert apply(module, :shortest_prefix, []) ==
             {:CertifiedPrefixPath, [], [?a], [:UnitEvidence], [{:Regular, :EmitUnit}]}

    assert apply(module, :longest_prefix, []) ==
             {:CertifiedPrefixPath, [?a], [], [{:CharacterEvidence, ?a}], [{:Observe, ?a}, {:Regular, {:EmitChar, ?a}}]}
  end

  test "a prefix certificate evaluates end anchors against the trailing subject" do
    assert {:ok, module} = Cure.Compiler.compile_and_load(@source, emit_events: false)

    assert apply(module, :end_before_suffix, []) == :MachineNoAcceptingPath

    assert apply(module, :end_at_subject_end, []) ==
             {:MachineAcceptingPath, [:UnitEvidence], [{:Regular, :EmitUnit}]}
  end

  test "extended routines preserve VM chunks and observe capture input" do
    assert {:ok, module} = Cure.Compiler.compile_and_load(@source, emit_events: false)

    assert apply(module, :extended_regular, []) ==
             {:ExtendedExecution, :none, [:UnitEvidence], []}

    assert apply(module, :extended_capture, []) ==
             {:ExtendedExecution, {:some, ?a}, [{:StringEvidence, {:String, [?a]}}], []}

    assert apply(module, :extended_certificate_erased, []) == :unit
  end
end
