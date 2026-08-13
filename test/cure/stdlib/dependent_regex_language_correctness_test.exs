defmodule Cure.Stdlib.DependentRegexLanguageCorrectnessTest do
  use ExUnit.Case, async: true

  alias Cure.Core.Env
  alias Cure.Elab.Program

  @source """
  mod RegexLanguageCorrectness
    use Std.Regex
    use Std.Regex.Proof
    use Std.Regex.Language

    fn accepts_a(char: Char) -> Bool = char == 'a'
    fn accepts_b(char: Char) -> Bool = char == 'b'
    fn no_chars() -> List(Char) = Nil()

    fn predicate_soundness(
      @erased final_evidence: List(Evidence),
      @erased routine: List(ExtendedInstruction),
      acceptance: MachineAcceptance(1, predicate_pattern_machine(accepts_a), subject_initial_position(), Cons('a', no_chars()), no_chars(), final_evidence, routine)
    ) -> PatternDenotation(CharC, PatternPredicate(accepts_a), subject_initial_position(), Cons('a', no_chars()), no_chars()) = predicate_acceptance_is_sound(
      accepts_a,
      'a',
      no_chars(),
      subject_initial_position(),
      final_evidence,
      routine,
      acceptance
    )

    fn generic_predicate_path_soundness(
      test: Char -> Bool,
      input: List(Char),
      after_input: List(Char),
      position: InitialPosition,
      input_evidence: List(Evidence),
      input_captures: List(CaptureFrame),
      {final_evidence: List(Evidence)},
      acceptance: AcceptancePathFrom(
        thompson_state_count(certify_thompson(PatternPredicate(test))),
        thompson_machine(certify_thompson(PatternPredicate(test))),
        position,
        input,
        after_input,
        input_evidence,
        input_captures,
        final_evidence
      )
    ) -> PatternDenotation(CharC, PatternPredicate(test), position, input, after_input) =
      predicate_acceptance_path_is_sound(test, input, after_input, position, input_evidence, input_captures, final_evidence, acceptance)

    fn generic_predicate_path_completeness(
      test: Char -> Bool,
      char: Char,
      after_input: List(Char),
      position: InitialPosition,
      input_evidence: List(Evidence),
      input_captures: List(CaptureFrame),
      denotation: PatternDenotation(CharC, PatternPredicate(test), position, Cons(char, Nil()), after_input)
    ) -> PatternAcceptanceFrom(CharC, PatternPredicate(test), position, Cons(char, Nil()), after_input, input_evidence, input_captures) =
      predicate_denotation_is_complete_from(test, char, after_input, position, input_evidence, input_captures, denotation)

    fn alternate_left_active_edge_embedding(
      left_count: Nat,
      right_count: Nat,
      states: List(MachineState(left_count)),
      boundary: Boundary,
      state: Bounded(left_count),
      routine: List(EvidenceInstruction),
      edge: ListMember(MachineState(left_count), Active(state, routine, Nil()), filter_machine_states(left_count, states, boundary))
    ) -> ListMember(MachineState(plus(left_count, right_count)), Active(inject_alternate_left(left_count, right_count, state), routine, Nil()), filter_machine_states(plus(left_count, right_count), alternate_left_states(left_count, right_count, states, EmitLeft()), boundary)) =
      lift_filtered_left_active_member(left_count, right_count, states, EmitLeft(), boundary, state, routine, edge)

    fn alternate_left_accepted_edge_embedding(
      left_count: Nat,
      right_count: Nat,
      states: List(MachineState(left_count)),
      boundary: Boundary,
      routine: List(EvidenceInstruction),
      edge: ListMember(MachineState(left_count), Accepted(routine, Nil()), filter_machine_states(left_count, states, boundary))
    ) -> ListMember(MachineState(plus(left_count, right_count)), Accepted(append_branch_marker(routine, EmitLeft()), Nil()), filter_machine_states(plus(left_count, right_count), alternate_left_states(left_count, right_count, states, EmitLeft()), boundary)) =
      lift_filtered_left_accepted_member(left_count, right_count, states, EmitLeft(), boundary, routine, edge)

    fn alternate_right_active_edge_embedding(
      left_count: Nat,
      right_count: Nat,
      states: List(MachineState(right_count)),
      boundary: Boundary,
      state: Bounded(right_count),
      routine: List(EvidenceInstruction),
      edge: ListMember(MachineState(right_count), Active(state, routine, Nil()), filter_machine_states(right_count, states, boundary))
    ) -> ListMember(MachineState(plus(left_count, right_count)), Active(inject_alternate_right(left_count, right_count, state), routine, Nil()), filter_machine_states(plus(left_count, right_count), alternate_right_states(left_count, right_count, states, EmitRight()), boundary)) =
      lift_filtered_right_active_member(left_count, right_count, states, EmitRight(), boundary, state, routine, edge)

    fn alternate_right_accepted_edge_embedding(
      left_count: Nat,
      right_count: Nat,
      states: List(MachineState(right_count)),
      boundary: Boundary,
      routine: List(EvidenceInstruction),
      edge: ListMember(MachineState(right_count), Accepted(routine, Nil()), filter_machine_states(right_count, states, boundary))
    ) -> ListMember(MachineState(plus(left_count, right_count)), Accepted(append_branch_marker(routine, EmitRight()), Nil()), filter_machine_states(plus(left_count, right_count), alternate_right_states(left_count, right_count, states, EmitRight()), boundary)) =
      lift_filtered_right_accepted_member(left_count, right_count, states, EmitRight(), boundary, routine, edge)

    fn alternate_left_path_embedding(
      left_count: Nat,
      left_machine: PatternMachine(left_count),
      right_count: Nat,
      right_machine: PatternMachine(right_count),
      prefer_right: Bool,
      input: List(Char),
      after_input: List(Char),
      source: Bounded(left_count),
      current_evidence: List(Evidence),
      current_captures: List(CaptureFrame),
      final_evidence: List(Evidence),
      routine: List(ExtendedInstruction),
      path: AcceptingFrom(left_count, left_machine, input, after_input, ThreadActive(source), current_evidence, current_captures, final_evidence, routine)
    ) -> AlternateLeftActivePathEmbedding(left_count, left_machine, right_count, right_machine, prefer_right, input, after_input, source, current_evidence, current_captures, final_evidence) =
      lift_alternate_left_active_path(left_count, left_machine, right_count, right_machine, prefer_right, input, after_input, source, current_evidence, current_captures, final_evidence, routine, path)

    fn alternate_right_path_embedding(
      left_count: Nat,
      left_machine: PatternMachine(left_count),
      right_count: Nat,
      right_machine: PatternMachine(right_count),
      prefer_right: Bool,
      input: List(Char),
      after_input: List(Char),
      source: Bounded(right_count),
      current_evidence: List(Evidence),
      current_captures: List(CaptureFrame),
      final_evidence: List(Evidence),
      routine: List(ExtendedInstruction),
      path: AcceptingFrom(right_count, right_machine, input, after_input, ThreadActive(source), current_evidence, current_captures, final_evidence, routine)
    ) -> AlternateRightActivePathEmbedding(left_count, left_machine, right_count, right_machine, prefer_right, input, after_input, source, current_evidence, current_captures, final_evidence) =
      lift_alternate_right_active_path(left_count, left_machine, right_count, right_machine, prefer_right, input, after_input, source, current_evidence, current_captures, final_evidence, routine, path)

    fn filtered_append_left_embedding(
      n: Nat,
      left: List(MachineState(n)),
      right: List(MachineState(n)),
      boundary: Boundary,
      value: MachineState(n),
      edge: ListMember(MachineState(n), value, filter_machine_states(n, left, boundary))
    ) -> ListMember(MachineState(n), value, filter_machine_states(n, append_machine_states(n, left, right), boundary)) =
      lift_filtered_append_left_member(n, left, right, boundary, value, edge)

    fn filtered_append_right_embedding(
      n: Nat,
      left: List(MachineState(n)),
      right: List(MachineState(n)),
      boundary: Boundary,
      value: MachineState(n),
      edge: ListMember(MachineState(n), value, filter_machine_states(n, right, boundary))
    ) -> ListMember(MachineState(n), value, filter_machine_states(n, append_machine_states(n, left, right), boundary)) =
      lift_filtered_append_right_member(n, left, right, boundary, value, edge)

    fn alternate_left_acceptance_embedding(
      left_count: Nat,
      left_machine: PatternMachine(left_count),
      right_count: Nat,
      right_machine: PatternMachine(right_count),
      prefer_right: Bool,
      position: InitialPosition,
      input: List(Char),
      after_input: List(Char),
      input_evidence: List(Evidence),
      input_captures: List(CaptureFrame),
      final_evidence: List(Evidence),
      acceptance: AcceptancePathFrom(left_count, left_machine, position, input, after_input, input_evidence, input_captures, final_evidence)
    ) -> AlternateLeftAcceptanceEmbedding(left_count, left_machine, right_count, right_machine, prefer_right, position, input, after_input, input_evidence, input_captures, final_evidence) =
      lift_alternate_left_acceptance(left_count, left_machine, right_count, right_machine, prefer_right, position, input, after_input, input_evidence, input_captures, final_evidence, acceptance)

    fn alternate_right_acceptance_embedding(
      left_count: Nat,
      left_machine: PatternMachine(left_count),
      right_count: Nat,
      right_machine: PatternMachine(right_count),
      prefer_right: Bool,
      position: InitialPosition,
      input: List(Char),
      after_input: List(Char),
      input_evidence: List(Evidence),
      input_captures: List(CaptureFrame),
      final_evidence: List(Evidence),
      acceptance: AcceptancePathFrom(right_count, right_machine, position, input, after_input, input_evidence, input_captures, final_evidence)
    ) -> AlternateRightAcceptanceEmbedding(left_count, left_machine, right_count, right_machine, prefer_right, position, input, after_input, input_evidence, input_captures, final_evidence) =
      lift_alternate_right_acceptance(left_count, left_machine, right_count, right_machine, prefer_right, position, input, after_input, input_evidence, input_captures, final_evidence, acceptance)

    fn concat_right_active_path_embedding(
      left_count: Nat,
      left_machine: PatternMachine(left_count),
      right_count: Nat,
      right_machine: PatternMachine(right_count),
      input: List(Char),
      after_input: List(Char),
      source: Bounded(right_count),
      current_evidence: List(Evidence),
      current_captures: List(CaptureFrame),
      final_evidence: List(Evidence),
      routine: List(ExtendedInstruction),
      path: AcceptingFrom(right_count, right_machine, input, after_input, ThreadActive(source), current_evidence, current_captures, final_evidence, routine)
    ) -> ConcatRightActivePathEmbedding(left_count, left_machine, right_count, right_machine, input, after_input, source, current_evidence, current_captures, final_evidence) =
      lift_concat_right_active_path(left_count, left_machine, right_count, right_machine, input, after_input, source, current_evidence, current_captures, final_evidence, routine, path)

    fn concat_appended_constraints_hold(
      left: List(BoundaryConstraint),
      right: List(BoundaryConstraint),
      boundary: Boundary,
      left_holds: Equivalent(Bool, constraints_hold(left, boundary), True()),
      right_holds: Equivalent(Bool, constraints_hold(right, boundary), True())
    ) -> Equivalent(Bool, constraints_hold(append_constraints(left, right), boundary), True()) =
      appended_constraints_hold(left, right, boundary, left_holds, right_holds)

    fn concat_enter_right_active_member(
      left_count: Nat,
      right_count: Nat,
      left_routine: List(EvidenceInstruction),
      left_constraints: List(BoundaryConstraint),
      right_starts: List(MachineState(right_count)),
      state: Bounded(right_count),
      right_routine: List(EvidenceInstruction),
      right_constraints: List(BoundaryConstraint),
      edge: ListMember(MachineState(right_count), Active(state, right_routine, right_constraints), right_starts)
    ) -> ListMember(MachineState(plus(left_count, right_count)), Active(inject_alternate_right(left_count, right_count, state), append_routine(left_routine, right_routine), append_constraints(left_constraints, right_constraints)), enter_right_with_constraints(left_count, left_routine, left_constraints, right_starts)) =
      lift_enter_right_active_member(left_count, right_count, left_routine, left_constraints, right_starts, state, right_routine, right_constraints, edge)

    fn concat_enter_right_accepted_member(
      left_count: Nat,
      right_count: Nat,
      left_routine: List(EvidenceInstruction),
      left_constraints: List(BoundaryConstraint),
      right_starts: List(MachineState(right_count)),
      right_routine: List(EvidenceInstruction),
      right_constraints: List(BoundaryConstraint),
      edge: ListMember(MachineState(right_count), Accepted(right_routine, right_constraints), right_starts)
    ) -> ListMember(MachineState(plus(left_count, right_count)), Accepted(append_routine(append_routine(left_routine, right_routine), Cons(EmitPair(), Nil())), append_constraints(left_constraints, right_constraints)), enter_right_with_constraints(left_count, left_routine, left_constraints, right_starts)) =
      lift_enter_right_accepted_member(left_count, right_count, left_routine, left_constraints, right_starts, right_routine, right_constraints, edge)

    fn concat_continue_entered_right_member(
      left_count: Nat,
      right_count: Nat,
      left_starts: List(MachineState(left_count)),
      right_starts: List(MachineState(right_count)),
      left_routine: List(EvidenceInstruction),
      left_constraints: List(BoundaryConstraint),
      left_edge: ListMember(MachineState(left_count), Accepted(left_routine, left_constraints), left_starts),
      combined: MachineState(plus(left_count, right_count)),
      entered_edge: ListMember(MachineState(plus(left_count, right_count)), combined, enter_right_with_constraints(left_count, left_routine, left_constraints, right_starts))
    ) -> ListMember(MachineState(plus(left_count, right_count)), combined, continue_with_right(left_count, left_starts, right_starts)) =
      lift_continue_entered_right_member(left_count, right_count, left_starts, right_starts, left_routine, left_constraints, left_edge, combined, entered_edge)

    fn concat_nullable_left_active_right_splice(
      left_count: Nat,
      left_machine: PatternMachine(left_count),
      right_count: Nat,
      right_machine: PatternMachine(right_count),
      position: InitialPosition,
      input: List(Char),
      after_input: List(Char),
      input_evidence: List(Evidence),
      input_captures: List(CaptureFrame),
      left_regular: List(EvidenceInstruction),
      left_final_evidence: List(Evidence),
      left_final_captures: List(CaptureFrame),
      left_edge: ListMember(MachineState(left_count), Accepted(left_regular, Nil()), initial_machine_destinations(left_count, left_machine, position, empty_characters(), append_characters(input, after_input))),
      left_execution: RoutineExecution(left_regular, input_evidence, input_captures, left_final_evidence, left_final_captures),
      right_state: Bounded(right_count),
      right_regular: List(EvidenceInstruction),
      right_initial_evidence: List(Evidence),
      right_initial_captures: List(CaptureFrame),
      right_path_routine: List(ExtendedInstruction),
      right_edge: ListMember(MachineState(right_count), Active(right_state, right_regular, Nil()), initial_machine_destinations(right_count, right_machine, position, input, after_input)),
      right_execution: RoutineExecution(right_regular, left_final_evidence, left_final_captures, right_initial_evidence, right_initial_captures),
      right_final_evidence: List(Evidence),
      right_path: AcceptingFrom(right_count, right_machine, input, after_input, ThreadActive(right_state), right_initial_evidence, right_initial_captures, right_final_evidence, right_path_routine)
    ) -> NullableLeftActiveRightConcatEmbedding(left_count, left_machine, right_count, right_machine, position, input, after_input, input_evidence, input_captures, right_final_evidence) =
      splice_nullable_left_active_right(left_count, left_machine, right_count, right_machine, position, input, after_input, input_evidence, input_captures, left_regular, left_final_evidence, left_final_captures, left_edge, left_execution, right_state, right_regular, right_initial_evidence, right_initial_captures, right_path_routine, right_edge, right_execution, right_final_evidence, right_path)

    fn concat_nullable_left_accepted_right_splice(
      left_count: Nat,
      left_machine: PatternMachine(left_count),
      right_count: Nat,
      right_machine: PatternMachine(right_count),
      position: InitialPosition,
      input: List(Char),
      after_input: List(Char),
      input_evidence: List(Evidence),
      input_captures: List(CaptureFrame),
      left_regular: List(EvidenceInstruction),
      left_final_evidence: List(Evidence),
      left_final_captures: List(CaptureFrame),
      left_edge: ListMember(MachineState(left_count), Accepted(left_regular, Nil()), initial_machine_destinations(left_count, left_machine, position, empty_characters(), append_characters(input, after_input))),
      left_execution: RoutineExecution(left_regular, input_evidence, input_captures, left_final_evidence, left_final_captures),
      right_regular: List(EvidenceInstruction),
      right_initial_evidence: List(Evidence),
      right_initial_captures: List(CaptureFrame),
      right_path_routine: List(ExtendedInstruction),
      right_edge: ListMember(MachineState(right_count), Accepted(right_regular, Nil()), initial_machine_destinations(right_count, right_machine, position, input, after_input)),
      right_execution: RoutineExecution(right_regular, left_final_evidence, left_final_captures, right_initial_evidence, right_initial_captures),
      right_final_evidence: List(Evidence),
      right_path: AcceptingFrom(right_count, right_machine, input, after_input, ThreadAccepted(), right_initial_evidence, right_initial_captures, right_final_evidence, right_path_routine)
    ) -> NullableLeftAcceptedRightConcatEmbedding(left_count, left_machine, right_count, right_machine, position, input, after_input, input_evidence, input_captures, right_final_evidence) =
      splice_nullable_left_accepted_right(left_count, left_machine, right_count, right_machine, position, input, after_input, input_evidence, input_captures, left_regular, left_final_evidence, left_final_captures, left_edge, left_execution, right_regular, right_initial_evidence, right_initial_captures, right_path_routine, right_edge, right_execution, right_final_evidence, right_path)

    fn generic_concat_acceptance_composition(
      left_count: Nat,
      left_machine: PatternMachine(left_count),
      right_count: Nat,
      right_machine: PatternMachine(right_count),
      position: InitialPosition,
      left_input: List(Char),
      right_input: List(Char),
      after_input: List(Char),
      input_evidence: List(Evidence),
      input_captures: List(CaptureFrame),
      left_final_evidence: List(Evidence),
      left_acceptance: AcceptancePathFrom(left_count, left_machine, position, left_input, append_characters(right_input, after_input), input_evidence, input_captures, left_final_evidence),
      right_final_evidence: List(Evidence),
      right_acceptance: AcceptancePathFrom(right_count, right_machine, advance_initial_position(position, left_input), right_input, after_input, left_final_evidence, acceptance_path_final_captures(left_count, left_machine, position, left_input, append_characters(right_input, after_input), input_evidence, input_captures, left_final_evidence, left_acceptance), right_final_evidence)
    ) -> AcceptancePathFrom(plus(left_count, right_count), concat_pattern_machine(left_count, left_machine, right_count, right_machine), position, append_characters(left_input, right_input), after_input, input_evidence, input_captures, Cons(PairEvidence(), right_final_evidence)) =
      lift_concat_acceptances(left_count, left_machine, right_count, right_machine, position, left_input, right_input, after_input, input_evidence, input_captures, left_final_evidence, left_acceptance, right_final_evidence, right_acceptance)

    fn generic_group_acceptance_composition(
      inner_shape: ShapeCode,
      inner: Pattern(inner_shape),
      input: List(Char),
      after_input: List(Char),
      position: InitialPosition,
      input_evidence: List(Evidence),
      input_captures: List(CaptureFrame),
      completion: PatternAcceptanceFrom(
        inner_shape,
        inner,
        position,
        input,
        after_input,
        input_evidence,
        Cons(CaptureFrame(Nil(), input_evidence), input_captures)
      )
    ) -> PatternAcceptanceFrom(
      StringC,
      PatternGroup(inner),
      position,
      input,
      after_input,
      input_evidence,
      input_captures
    ) =
      complete_group_from(inner_shape, inner, input, after_input, position, input_evidence, input_captures, completion)

    fn generic_repeat_mode_empty_composition(
      inner_shape: ShapeCode,
      inner: Pattern(inner_shape),
      lazy: Bool,
      after_input: List(Char),
      position: InitialPosition,
      input_evidence: List(Evidence),
      input_captures: List(CaptureFrame)
    ) -> PatternAcceptanceFrom(
      ListC(inner_shape),
      PatternRepeatMode(inner, lazy),
      position,
      Nil(),
      after_input,
      input_evidence,
      input_captures
    ) =
      complete_repeat_mode_empty_from(inner_shape, inner, lazy, after_input, position, input_evidence, input_captures)

    fn generic_alternate_mode_left_composition(
      left_shape: ShapeCode,
      right_shape: ShapeCode,
      left: Pattern(left_shape),
      right: Pattern(right_shape),
      prefer_right: Bool,
      input: List(Char),
      after_input: List(Char),
      position: InitialPosition,
      input_evidence: List(Evidence),
      input_captures: List(CaptureFrame),
      completion: PatternAcceptanceFrom(left_shape, left, position, input, after_input, input_evidence, input_captures)
    ) -> PatternAcceptanceFrom(ChoiceC(left_shape, right_shape), PatternAlternateMode(left, right, prefer_right), position, input, after_input, input_evidence, input_captures) =
      complete_alternate_mode_left_from(left_shape, right_shape, left, right, prefer_right, input, after_input, position, input_evidence, input_captures, completion)

    fn generic_alternate_mode_right_composition(
      left_shape: ShapeCode,
      right_shape: ShapeCode,
      left: Pattern(left_shape),
      right: Pattern(right_shape),
      prefer_right: Bool,
      input: List(Char),
      after_input: List(Char),
      position: InitialPosition,
      input_evidence: List(Evidence),
      input_captures: List(CaptureFrame),
      completion: PatternAcceptanceFrom(right_shape, right, position, input, after_input, input_evidence, input_captures)
    ) -> PatternAcceptanceFrom(ChoiceC(left_shape, right_shape), PatternAlternateMode(left, right, prefer_right), position, input, after_input, input_evidence, input_captures) =
      complete_alternate_mode_right_from(left_shape, right_shape, left, right, prefer_right, input, after_input, position, input_evidence, input_captures, completion)

    fn generic_alternate_left_composition(
      left_shape: ShapeCode,
      right_shape: ShapeCode,
      left: Pattern(left_shape),
      right: Pattern(right_shape),
      input: List(Char),
      after_input: List(Char),
      position: InitialPosition,
      input_evidence: List(Evidence),
      input_captures: List(CaptureFrame),
      completion: PatternAcceptanceFrom(left_shape, left, position, input, after_input, input_evidence, input_captures)
    ) -> PatternAcceptanceFrom(ChoiceC(left_shape, right_shape), PatternAlternate(left, right), position, input, after_input, input_evidence, input_captures) =
      complete_alternate_left_from(left_shape, right_shape, left, right, input, after_input, position, input_evidence, input_captures, completion)

    fn generic_alternate_right_composition(
      left_shape: ShapeCode,
      right_shape: ShapeCode,
      left: Pattern(left_shape),
      right: Pattern(right_shape),
      input: List(Char),
      after_input: List(Char),
      position: InitialPosition,
      input_evidence: List(Evidence),
      input_captures: List(CaptureFrame),
      completion: PatternAcceptanceFrom(right_shape, right, position, input, after_input, input_evidence, input_captures)
    ) -> PatternAcceptanceFrom(ChoiceC(left_shape, right_shape), PatternAlternate(left, right), position, input, after_input, input_evidence, input_captures) =
      complete_alternate_right_from(left_shape, right_shape, left, right, input, after_input, position, input_evidence, input_captures, completion)

    fn predicate_completeness(
      denotation: PatternDenotation(CharC, PatternPredicate(accepts_a), subject_initial_position(), Cons('a', no_chars()), no_chars())
    ) -> PredicateAcceptance(accepts_a, 'a', no_chars(), subject_initial_position()) = predicate_denotation_is_complete(
      accepts_a,
      'a',
      no_chars(),
      subject_initial_position(),
      denotation
    )

    fn predicate_pattern_completeness(
      denotation: PatternDenotation(CharC, PatternPredicate(accepts_a), subject_initial_position(), Cons('a', no_chars()), no_chars())
    ) -> PatternAcceptance(CharC, PatternPredicate(accepts_a), subject_initial_position(), Cons('a', no_chars()), no_chars()) = predicate_pattern_denotation_is_complete(
      accepts_a,
      'a',
      no_chars(),
      subject_initial_position(),
      denotation
    )

    fn empty_soundness(
      @erased final_evidence: List(Evidence),
      @erased routine: List(ExtendedInstruction),
      acceptance: MachineAcceptance(0, empty_pattern_machine(), subject_initial_position(), no_chars(), no_chars(), final_evidence, routine)
    ) -> PatternDenotation(UnitC, PatternEmpty(), subject_initial_position(), no_chars(), no_chars()) = empty_acceptance_is_sound(
      no_chars(),
      subject_initial_position(),
      final_evidence,
      routine,
      acceptance
    )

    fn empty_completeness(
      denotation: PatternDenotation(UnitC, PatternEmpty(), subject_initial_position(), no_chars(), no_chars())
    ) -> EmptyAcceptance(no_chars(), subject_initial_position()) = empty_denotation_is_complete(
      no_chars(),
      subject_initial_position(),
      denotation
    )

    fn generic_empty_path_completeness(
      after_input: List(Char),
      position: InitialPosition,
      input_evidence: List(Evidence),
      input_captures: List(CaptureFrame),
      denotation: PatternDenotation(UnitC, PatternEmpty(), position, Nil(), after_input)
    ) -> PatternAcceptanceFrom(UnitC, PatternEmpty(), position, Nil(), after_input, input_evidence, input_captures) =
      empty_denotation_is_complete_from(after_input, position, input_evidence, input_captures, denotation)

    fn empty_pattern_completeness(
      denotation: PatternDenotation(UnitC, PatternEmpty(), subject_initial_position(), no_chars(), no_chars())
    ) -> PatternAcceptance(UnitC, PatternEmpty(), subject_initial_position(), no_chars(), no_chars()) = empty_pattern_denotation_is_complete(
      no_chars(),
      subject_initial_position(),
      denotation
    )

    fn boundary_soundness(
      @erased final_evidence: List(Evidence),
      @erased routine: List(ExtendedInstruction),
      acceptance: MachineAcceptance(0, boundary_pattern_machine(subject_start_constraint()), subject_initial_position(), no_chars(), no_chars(), final_evidence, routine)
    ) -> PatternDenotation(UnitC, PatternBoundary(subject_start_constraint()), subject_initial_position(), no_chars(), no_chars()) = boundary_acceptance_is_sound(
      subject_start_constraint(),
      no_chars(),
      subject_initial_position(),
      final_evidence,
      routine,
      acceptance
    )

    fn empty_path_soundness(
      input_evidence: List(Evidence),
      input_captures: List(CaptureFrame),
      {final_evidence: List(Evidence)},
      acceptance: AcceptancePathFrom(0, empty_pattern_machine(), subject_initial_position(), Nil(), Nil(), input_evidence, input_captures, final_evidence)
    ) -> PatternDenotation(UnitC, PatternEmpty(), subject_initial_position(), Nil(), Nil()) =
      empty_acceptance_path_is_sound(Nil(), Nil(), subject_initial_position(), input_evidence, input_captures, final_evidence, acceptance)

    fn boundary_path_soundness(
      input: List(Char),
      input_evidence: List(Evidence),
      input_captures: List(CaptureFrame),
      {final_evidence: List(Evidence)},
      acceptance: AcceptancePathFrom(0, boundary_pattern_machine(subject_start_constraint()), subject_initial_position(), input, Nil(), input_evidence, input_captures, final_evidence)
    ) -> PatternDenotation(UnitC, PatternBoundary(subject_start_constraint()), subject_initial_position(), input, Nil()) =
      boundary_acceptance_path_is_sound(subject_start_constraint(), input, Nil(), subject_initial_position(), input_evidence, input_captures, final_evidence, acceptance)

    fn generic_boundary_path_soundness(
      constraint: BoundaryConstraint,
      input: List(Char),
      after_input: List(Char),
      position: InitialPosition,
      input_evidence: List(Evidence),
      input_captures: List(CaptureFrame),
      {final_evidence: List(Evidence)},
      acceptance: AcceptancePathFrom(
        thompson_state_count(certify_thompson(PatternBoundary(constraint))),
        thompson_machine(certify_thompson(PatternBoundary(constraint))),
        position,
        input,
        after_input,
        input_evidence,
        input_captures,
        final_evidence
      )
    ) -> PatternDenotation(UnitC, PatternBoundary(constraint), position, input, after_input) =
      boundary_acceptance_path_is_sound(constraint, input, after_input, position, input_evidence, input_captures, final_evidence, acceptance)

    fn generic_pattern_path_soundness(
      {shape: ShapeCode},
      pattern: Pattern(shape),
      input: List(Char),
      after_input: List(Char),
      position: InitialPosition,
      input_evidence: List(Evidence),
      input_captures: List(CaptureFrame),
      {final_evidence: List(Evidence)},
      acceptance: AcceptancePathFrom(
        thompson_state_count(certify_thompson(pattern)),
        thompson_machine(certify_thompson(pattern)),
        position,
        input,
        after_input,
        input_evidence,
        input_captures,
        final_evidence
      )
    ) -> PatternDenotation(shape, pattern, position, input, after_input) =
      pattern_acceptance_path_is_sound(pattern, input, after_input, position, input_evidence, input_captures, final_evidence, acceptance)

    fn boundary_completeness(
      denotation: PatternDenotation(UnitC, PatternBoundary(subject_start_constraint()), subject_initial_position(), no_chars(), no_chars())
    ) -> BoundaryAcceptance(subject_start_constraint(), no_chars(), subject_initial_position()) = boundary_denotation_is_complete(
      subject_start_constraint(),
      no_chars(),
      subject_initial_position(),
      denotation
    )

    fn generic_boundary_path_completeness(
      constraint: BoundaryConstraint,
      after_input: List(Char),
      position: InitialPosition,
      input_evidence: List(Evidence),
      input_captures: List(CaptureFrame),
      denotation: PatternDenotation(UnitC, PatternBoundary(constraint), position, Nil(), after_input)
    ) -> PatternAcceptanceFrom(UnitC, PatternBoundary(constraint), position, Nil(), after_input, input_evidence, input_captures) =
      boundary_denotation_is_complete_from(constraint, after_input, position, input_evidence, input_captures, denotation)

    fn boundary_pattern_completeness(
      denotation: PatternDenotation(UnitC, PatternBoundary(subject_start_constraint()), subject_initial_position(), no_chars(), no_chars())
    ) -> PatternAcceptance(UnitC, PatternBoundary(subject_start_constraint()), subject_initial_position(), no_chars(), no_chars()) = boundary_pattern_denotation_is_complete(
      subject_start_constraint(),
      no_chars(),
      subject_initial_position(),
      denotation
    )

    fn grouped_predicate_denotation() -> PatternDenotation(StringC, PatternGroup(PatternPredicate(accepts_a)), subject_initial_position(), Cons('a', no_chars()), no_chars()) =
      DenotesGroup(PatternPredicate(accepts_a), DenotesPredicate(Cons('a', Nil()), 'a', IsSingleCharacter(Cons('a', Nil()), 'a', reflexive(Cons('a', Nil()))), reflexive(true)))

    fn grouped_predicate_completeness(
      denotation: PatternDenotation(CharC, PatternPredicate(accepts_a), subject_initial_position(), Cons('a', Nil()), Nil())
    ) -> PatternAcceptance(StringC, PatternGroup(PatternPredicate(accepts_a)), subject_initial_position(), Cons('a', Nil()), Nil()) =
      grouped_predicate_denotation_is_complete(accepts_a, 'a', Nil(), subject_initial_position(), denotation)

    fn grouped_predicate_soundness(
      {final_evidence: List(Evidence)},
      {routine: List(ExtendedInstruction)},
      acceptance: MachineAcceptance(1, group_pattern_machine(1, Cons(predicate_machine_start(), Nil()), predicate_machine_next(accepts_a)), subject_initial_position(), Cons('a', Nil()), Nil(), final_evidence, routine)
    ) -> PatternDenotation(StringC, PatternGroup(PatternPredicate(accepts_a)), subject_initial_position(), Cons('a', Nil()), Nil()) =
      grouped_predicate_acceptance_is_sound(accepts_a, 'a', Nil(), subject_initial_position(), final_evidence, routine, acceptance)

    fn concatenated_empty_denotation() -> PatternDenotation(PairC(UnitC, UnitC), PatternConcat(PatternEmpty(), PatternEmpty()), subject_initial_position(), no_chars(), no_chars()) =
      DenotesConcat(PatternEmpty(), PatternEmpty(), no_chars(), no_chars(), Std.Regex.Proof.input_partition_here(no_chars()), DenotesEmpty(), DenotesEmpty())

    fn concatenated_empty_completeness(
      denotation: PatternDenotation(PairC(UnitC, UnitC), PatternConcat(PatternEmpty(), PatternEmpty()), subject_initial_position(), no_chars(), no_chars())
    ) -> PatternAcceptance(PairC(UnitC, UnitC), PatternConcat(PatternEmpty(), PatternEmpty()), subject_initial_position(), no_chars(), no_chars()) =
      empty_concat_denotation_is_complete(no_chars(), subject_initial_position(), denotation)

    fn concatenated_predicate_soundness(
      {final_evidence: List(Evidence)},
      {routine: List(ExtendedInstruction)},
      acceptance: MachineAcceptance(2, concat_pattern_machine(1, predicate_pattern_machine(accepts_a), 1, predicate_pattern_machine(accepts_b)), subject_initial_position(), Cons('a', Cons('b', Nil())), Nil(), final_evidence, routine)
    ) -> PatternDenotation(PairC(CharC, CharC), PatternConcat(PatternPredicate(accepts_a), PatternPredicate(accepts_b)), subject_initial_position(), Cons('a', Cons('b', Nil())), Nil()) =
      predicate_concat_acceptance_is_sound(accepts_a, accepts_b, Cons('a', Cons('b', Nil())), Nil(), subject_initial_position(), final_evidence, routine, acceptance)

    fn concatenated_predicate_completeness(
      left_denotation: PatternDenotation(CharC, PatternPredicate(accepts_a), subject_initial_position(), Cons('a', Nil()), Cons('b', Nil())),
      right_denotation: PatternDenotation(CharC, PatternPredicate(accepts_b), advance_initial_position(subject_initial_position(), Cons('a', Nil())), Cons('b', Nil()), Nil())
    ) -> PatternAcceptance(PairC(CharC, CharC), PatternConcat(PatternPredicate(accepts_a), PatternPredicate(accepts_b)), subject_initial_position(), Cons('a', Cons('b', Nil())), Nil()) =
      predicate_concat_denotations_are_complete(accepts_a, accepts_b, 'a', 'b', Nil(), subject_initial_position(), left_denotation, right_denotation)

    fn alternate_left_denotation() -> PatternDenotation(ChoiceC(UnitC, UnitC), PatternAlternate(PatternEmpty(), PatternEmpty()), subject_initial_position(), no_chars(), no_chars()) =
      DenotesAlternateLeft(PatternEmpty(), PatternEmpty(), DenotesEmpty())

    fn alternate_mode_right_denotation() -> PatternDenotation(ChoiceC(UnitC, UnitC), PatternAlternateMode(PatternEmpty(), PatternEmpty(), True()), subject_initial_position(), Nil(), Nil()) =
      DenotesAlternateModeRight(PatternEmpty(), PatternEmpty(), True(), DenotesEmpty())

    fn alternate_predicate_left_completeness(
      denotation: PatternDenotation(CharC, PatternPredicate(accepts_a), subject_initial_position(), Cons('a', Nil()), Nil())
    ) -> PatternAcceptance(ChoiceC(CharC, CharC), PatternAlternateMode(PatternPredicate(accepts_a), PatternPredicate(accepts_b), True()), subject_initial_position(), Cons('a', Nil()), Nil()) =
      predicate_alternate_mode_left_denotation_is_complete(accepts_a, accepts_b, True(), 'a', Nil(), subject_initial_position(), denotation)

    fn alternate_predicate_right_completeness(
      denotation: PatternDenotation(CharC, PatternPredicate(accepts_b), subject_initial_position(), Cons('b', Nil()), Nil())
    ) -> PatternAcceptance(ChoiceC(CharC, CharC), PatternAlternateMode(PatternPredicate(accepts_a), PatternPredicate(accepts_b), False()), subject_initial_position(), Cons('b', Nil()), Nil()) =
      predicate_alternate_mode_right_denotation_is_complete(accepts_a, accepts_b, False(), 'b', Nil(), subject_initial_position(), denotation)

    fn alternate_predicate_default_left_completeness(
      denotation: PatternDenotation(CharC, PatternPredicate(accepts_a), subject_initial_position(), Cons('a', Nil()), Nil())
    ) -> PatternAcceptance(ChoiceC(CharC, CharC), PatternAlternate(PatternPredicate(accepts_a), PatternPredicate(accepts_b)), subject_initial_position(), Cons('a', Nil()), Nil()) =
      predicate_alternate_left_denotation_is_complete(accepts_a, accepts_b, 'a', Nil(), subject_initial_position(), denotation)

    fn alternate_predicate_default_right_completeness(
      denotation: PatternDenotation(CharC, PatternPredicate(accepts_b), subject_initial_position(), Cons('b', Nil()), Nil())
    ) -> PatternAcceptance(ChoiceC(CharC, CharC), PatternAlternate(PatternPredicate(accepts_a), PatternPredicate(accepts_b)), subject_initial_position(), Cons('b', Nil()), Nil()) =
      predicate_alternate_right_denotation_is_complete(accepts_a, accepts_b, 'b', Nil(), subject_initial_position(), denotation)

    fn alternate_predicate_soundness(
      {final_evidence: List(Evidence)},
      {routine: List(ExtendedInstruction)},
      acceptance: MachineAcceptance(2, alternate_pattern_machine(1, predicate_pattern_machine(accepts_a), 1, predicate_pattern_machine(accepts_a), True()), subject_initial_position(), Cons('a', Nil()), Nil(), final_evidence, routine)
    ) -> PatternDenotation(ChoiceC(CharC, CharC), PatternAlternateMode(PatternPredicate(accepts_a), PatternPredicate(accepts_a), True()), subject_initial_position(), Cons('a', Nil()), Nil()) =
      predicate_alternate_mode_acceptance_is_sound(accepts_a, accepts_a, True(), 'a', Nil(), subject_initial_position(), final_evidence, routine, acceptance)

    fn repeated_predicate_denotation() -> PatternDenotation(ListC(CharC), PatternRepeat(PatternPredicate(accepts_a)), subject_initial_position(), Cons('a', Nil()), Nil()) =
      DenotesRepeatMore(
        PatternPredicate(accepts_a),
        Cons('a', Nil()),
        Nil(),
        CharactersPresent('a', Nil()),
        Std.Regex.Proof.input_partition_there('a', Std.Regex.Proof.input_partition_here(Nil())),
        DenotesPredicate(Cons('a', Nil()), 'a', IsSingleCharacter(Cons('a', Nil()), 'a', reflexive(Cons('a', Nil()))), reflexive(True())),
        DenotesRepeatEmpty(PatternPredicate(accepts_a))
      )

    fn repeated_predicate_recursive_completeness(
      denotation: PatternDenotation(ListC(CharC), PatternRepeat(PatternPredicate(accepts_a)), subject_initial_position(), Cons('a', Nil()), Nil())
    ) -> PatternAcceptance(ListC(CharC), PatternRepeat(PatternPredicate(accepts_a)), subject_initial_position(), Cons('a', Nil()), Nil()) =
      predicate_repeat_denotation_is_complete(accepts_a, Cons('a', Nil()), Nil(), subject_initial_position(), denotation)

    fn repeated_mode_pair_denotation() -> PatternDenotation(ListC(CharC), PatternRepeatMode(PatternPredicate(accepts_a), True()), subject_initial_position(), Cons('a', Cons('a', Nil())), Nil()) =
      DenotesRepeatModeMore(
        PatternPredicate(accepts_a),
        True(),
        Cons('a', Nil()),
        Cons('a', Nil()),
        CharactersPresent('a', Nil()),
        Std.Regex.Proof.input_partition_there('a', Std.Regex.Proof.input_partition_here(Cons('a', Nil()))),
        DenotesPredicate(Cons('a', Nil()), 'a', IsSingleCharacter(Cons('a', Nil()), 'a', reflexive(Cons('a', Nil()))), reflexive(True())),
        DenotesRepeatModeMore(
          PatternPredicate(accepts_a),
          True(),
          Cons('a', Nil()),
          Nil(),
          CharactersPresent('a', Nil()),
          Std.Regex.Proof.input_partition_there('a', Std.Regex.Proof.input_partition_here(Nil())),
          DenotesPredicate(Cons('a', Nil()), 'a', IsSingleCharacter(Cons('a', Nil()), 'a', reflexive(Cons('a', Nil()))), reflexive(True())),
          DenotesRepeatModeEmpty(PatternPredicate(accepts_a), True())
        )
      )

    fn repeated_mode_recursive_completeness(
      denotation: PatternDenotation(ListC(CharC), PatternRepeatMode(PatternPredicate(accepts_a), True()), subject_initial_position(), Cons('a', Cons('a', Nil())), Nil())
    ) -> PatternAcceptance(ListC(CharC), PatternRepeatMode(PatternPredicate(accepts_a), True()), subject_initial_position(), Cons('a', Cons('a', Nil())), Nil()) =
      predicate_repeat_mode_denotation_is_complete(accepts_a, True(), Cons('a', Cons('a', Nil())), Nil(), subject_initial_position(), denotation)

    fn repeated_mode_empty_denotation() -> PatternDenotation(ListC(CharC), PatternRepeatMode(PatternPredicate(accepts_a), True()), subject_initial_position(), Nil(), Nil()) =
      DenotesRepeatModeEmpty(PatternPredicate(accepts_a), True())

    fn repeated_mode_empty_completeness(
      denotation: PatternDenotation(ListC(CharC), PatternRepeatMode(PatternPredicate(accepts_a), True()), subject_initial_position(), Nil(), Nil())
    ) -> PatternAcceptance(ListC(CharC), PatternRepeatMode(PatternPredicate(accepts_a), True()), subject_initial_position(), Nil(), Nil()) =
      predicate_repeat_mode_empty_denotation_is_complete(accepts_a, True(), Nil(), subject_initial_position(), denotation)

    fn repeated_default_empty_completeness(
      denotation: PatternDenotation(ListC(CharC), PatternRepeat(PatternPredicate(accepts_a)), subject_initial_position(), Nil(), Nil())
    ) -> PatternAcceptance(ListC(CharC), PatternRepeat(PatternPredicate(accepts_a)), subject_initial_position(), Nil(), Nil()) =
      predicate_repeat_empty_denotation_is_complete(accepts_a, Nil(), subject_initial_position(), denotation)

    fn repeated_nullable_inner_completeness(
      denotation: PatternDenotation(ListC(UnitC), PatternRepeat(PatternEmpty()), subject_initial_position(), Nil(), Nil())
    ) -> PatternAcceptance(ListC(UnitC), PatternRepeat(PatternEmpty()), subject_initial_position(), Nil(), Nil()) =
      repeat_empty_denotation_is_complete(UnitC, PatternEmpty(), Nil(), subject_initial_position(), denotation)

    fn repeated_nullable_inner_mode_completeness(
      denotation: PatternDenotation(ListC(UnitC), PatternRepeatMode(PatternEmpty(), True()), subject_initial_position(), Nil(), Nil())
    ) -> PatternAcceptance(ListC(UnitC), PatternRepeatMode(PatternEmpty(), True()), subject_initial_position(), Nil(), Nil()) =
      repeat_mode_empty_denotation_is_complete(UnitC, PatternEmpty(), True(), Nil(), subject_initial_position(), denotation)

    fn repeated_mode_singleton_completeness(
      item_denotation: PatternDenotation(CharC, PatternPredicate(accepts_a), subject_initial_position(), Cons('a', Nil()), Nil())
    ) -> PatternAcceptance(ListC(CharC), PatternRepeatMode(PatternPredicate(accepts_a), True()), subject_initial_position(), Cons('a', Nil()), Nil()) =
      predicate_repeat_mode_singleton_is_complete(accepts_a, True(), 'a', Nil(), subject_initial_position(), item_denotation)

    fn repeated_default_singleton_completeness(
      item_denotation: PatternDenotation(CharC, PatternPredicate(accepts_a), subject_initial_position(), Cons('a', Nil()), Nil())
    ) -> PatternAcceptance(ListC(CharC), PatternRepeat(PatternPredicate(accepts_a)), subject_initial_position(), Cons('a', Nil()), Nil()) =
      predicate_repeat_singleton_is_complete(accepts_a, 'a', Nil(), subject_initial_position(), item_denotation)

    fn repeated_mode_pair_completeness(
      first_denotation: PatternDenotation(CharC, PatternPredicate(accepts_a), subject_initial_position(), Cons('a', Nil()), Cons('a', Nil())),
      second_denotation: PatternDenotation(CharC, PatternPredicate(accepts_a), advance_initial_position(subject_initial_position(), Cons('a', Nil())), Cons('a', Nil()), Nil())
    ) -> PatternAcceptance(ListC(CharC), PatternRepeatMode(PatternPredicate(accepts_a), True()), subject_initial_position(), Cons('a', Cons('a', Nil())), Nil()) =
      predicate_repeat_mode_pair_is_complete(accepts_a, True(), 'a', 'a', Nil(), subject_initial_position(), first_denotation, second_denotation)

    fn repeated_default_pair_completeness(
      first_denotation: PatternDenotation(CharC, PatternPredicate(accepts_a), subject_initial_position(), Cons('a', Nil()), Cons('a', Nil())),
      second_denotation: PatternDenotation(CharC, PatternPredicate(accepts_a), advance_initial_position(subject_initial_position(), Cons('a', Nil())), Cons('a', Nil()), Nil())
    ) -> PatternAcceptance(ListC(CharC), PatternRepeat(PatternPredicate(accepts_a)), subject_initial_position(), Cons('a', Cons('a', Nil())), Nil()) =
      predicate_repeat_pair_is_complete(accepts_a, 'a', 'a', Nil(), subject_initial_position(), first_denotation, second_denotation)

    fn repeated_predicate_soundness(
      {final_evidence: List(Evidence)},
      {routine: List(ExtendedInstruction)},
      acceptance: MachineAcceptance(1, repeat_pattern_machine(1, predicate_pattern_machine(accepts_a), True()), subject_initial_position(), Cons('a', Nil()), Nil(), final_evidence, routine)
    ) -> PatternDenotation(ListC(CharC), PatternRepeatMode(PatternPredicate(accepts_a), True()), subject_initial_position(), Cons('a', Nil()), Nil()) =
      predicate_repeat_mode_acceptance_is_sound(accepts_a, True(), Cons('a', Nil()), Nil(), subject_initial_position(), final_evidence, routine, acceptance)

    fn repeated_predicate_default_soundness(
      {final_evidence: List(Evidence)},
      {routine: List(ExtendedInstruction)},
      acceptance: MachineAcceptance(1, repeat_pattern_machine(1, predicate_pattern_machine(accepts_a), False()), subject_initial_position(), Cons('a', Nil()), Nil(), final_evidence, routine)
    ) -> PatternDenotation(ListC(CharC), PatternRepeat(PatternPredicate(accepts_a)), subject_initial_position(), Cons('a', Nil()), Nil()) =
      predicate_repeat_acceptance_is_sound(accepts_a, Cons('a', Nil()), Nil(), subject_initial_position(), final_evidence, routine, acceptance)

  """

  test "predicate denotation is sound for certified execution" do
    assert {:ok, env} = Program.elaborate(@source)
    assert Env.total?(env, :predicate_soundness)
    assert Env.total?(env, :"Std.Regex.Language#predicate_acceptance_is_sound")
  end

  test "predicate denotation constructively produces certified execution" do
    assert {:ok, env} = Program.elaborate(@source)
    assert Env.total?(env, :predicate_completeness)
    assert Env.total?(env, :predicate_pattern_completeness)
    assert Env.total?(env, :"Std.Regex.Language#predicate_denotation_is_complete")
    assert Env.total?(env, :"Std.Regex.Language#predicate_pattern_denotation_is_complete")
  end

  test "empty and boundary denotations are sound and constructively complete" do
    assert {:ok, env} = Program.elaborate(@source)

    for name <- [
          :empty_soundness,
          :empty_completeness,
          :empty_pattern_completeness,
          :boundary_soundness,
          :boundary_completeness,
          :boundary_pattern_completeness,
          :empty_path_soundness,
          :boundary_path_soundness,
          :"Std.Regex.Language#empty_acceptance_is_sound",
          :"Std.Regex.Language#empty_denotation_is_complete",
          :"Std.Regex.Language#empty_pattern_denotation_is_complete",
          :"Std.Regex.Language#boundary_acceptance_is_sound",
          :"Std.Regex.Language#boundary_denotation_is_complete",
          :"Std.Regex.Language#boundary_pattern_denotation_is_complete",
          :"Std.Regex.Language#empty_acceptance_path_is_sound",
          :"Std.Regex.Language#boundary_acceptance_path_is_sound"
        ] do
      assert Env.total?(env, name), "expected #{inspect(name)} to be total"
    end
  end

  test "recursive denotation preserves grouped child membership" do
    assert {:ok, env} = Program.elaborate(@source)
    assert Env.total?(env, :grouped_predicate_denotation)
    assert Env.total?(env, :grouped_predicate_completeness)
    assert Env.total?(env, :"Std.Regex.Language#grouped_predicate_denotation_is_complete")
    assert Env.total?(env, :generic_group_acceptance_composition)
    assert Env.total?(env, :"Std.Regex.Language#complete_group_from")
    assert Env.total?(env, :generic_repeat_mode_empty_composition)
    assert Env.total?(env, :"Std.Regex.Language#complete_repeat_mode_empty_from")
    assert Env.total?(env, :grouped_predicate_soundness)
    assert Env.total?(env, :"Std.Regex.Language#grouped_predicate_acceptance_is_sound")
    assert Env.total?(env, :concatenated_empty_denotation)
    assert Env.total?(env, :concatenated_empty_completeness)
    assert Env.total?(env, :"Std.Regex.Language#empty_concat_denotation_is_complete")
    assert Env.total?(env, :concatenated_predicate_soundness)
    assert Env.total?(env, :concatenated_predicate_completeness)
    assert Env.total?(env, :"Std.Regex.Language#predicate_concat_denotations_are_complete")
    assert Env.total?(env, :"Std.Regex.Language#predicate_concat_acceptance_is_sound")
    assert Env.total?(env, :alternate_left_denotation)
    assert Env.total?(env, :alternate_mode_right_denotation)
    assert Env.total?(env, :alternate_predicate_left_completeness)
    assert Env.total?(env, :alternate_predicate_right_completeness)
    assert Env.total?(env, :alternate_predicate_default_left_completeness)
    assert Env.total?(env, :alternate_predicate_default_right_completeness)
    assert Env.total?(env, :"Std.Regex.Language#predicate_alternate_mode_left_denotation_is_complete")
    assert Env.total?(env, :"Std.Regex.Language#predicate_alternate_mode_right_denotation_is_complete")
    assert Env.total?(env, :"Std.Regex.Language#predicate_alternate_left_denotation_is_complete")
    assert Env.total?(env, :"Std.Regex.Language#predicate_alternate_right_denotation_is_complete")
    assert Env.total?(env, :alternate_predicate_soundness)
    assert Env.total?(env, :"Std.Regex.Language#predicate_alternate_mode_acceptance_is_sound")
    assert Env.total?(env, :repeated_predicate_denotation)
    assert Env.total?(env, :repeated_predicate_recursive_completeness)
    assert Env.total?(env, :"Std.Regex.Language#predicate_repeat_denotation_is_complete")
    assert Env.total?(env, :repeated_mode_pair_denotation)
    assert Env.total?(env, :repeated_mode_recursive_completeness)
    assert Env.total?(env, :"Std.Regex.Language#predicate_repeat_mode_denotation_is_complete")
    assert Env.total?(env, :repeated_mode_empty_denotation)
    assert Env.total?(env, :repeated_mode_empty_completeness)
    assert Env.total?(env, :repeated_default_empty_completeness)
    assert Env.total?(env, :repeated_nullable_inner_completeness)
    assert Env.total?(env, :repeated_nullable_inner_mode_completeness)
    assert Env.total?(env, :"Std.Regex.Language#repeat_empty_denotation_is_complete")
    assert Env.total?(env, :"Std.Regex.Language#repeat_mode_empty_denotation_is_complete")
    assert Env.total?(env, :repeated_mode_singleton_completeness)
    assert Env.total?(env, :repeated_default_singleton_completeness)
    assert Env.total?(env, :repeated_mode_pair_completeness)
    assert Env.total?(env, :repeated_default_pair_completeness)
    assert Env.total?(env, :"Std.Regex.Language#predicate_repeat_mode_empty_denotation_is_complete")
    assert Env.total?(env, :"Std.Regex.Language#predicate_repeat_empty_denotation_is_complete")
    assert Env.total?(env, :"Std.Regex.Language#predicate_repeat_mode_singleton_is_complete")
    assert Env.total?(env, :"Std.Regex.Language#predicate_repeat_singleton_is_complete")
    assert Env.total?(env, :"Std.Regex.Language#predicate_repeat_mode_pair_is_complete")
    assert Env.total?(env, :"Std.Regex.Language#predicate_repeat_pair_is_complete")
    assert Env.total?(env, :repeated_predicate_soundness)
    assert Env.total?(env, :"Std.Regex.Language#predicate_repeat_mode_acceptance_is_sound")
    assert Env.total?(env, :repeated_predicate_default_soundness)
    assert Env.total?(env, :"Std.Regex.Language#predicate_repeat_acceptance_is_sound")
  end
end
