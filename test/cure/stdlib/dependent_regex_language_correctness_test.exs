defmodule Cure.Stdlib.DependentRegexLanguageCorrectnessTest do
  use ExUnit.Case, async: true

  alias Cure.Core.Env
  alias Cure.Elab.Program

  @source """
  mod RegexLanguageCorrectness
    use Std.Regex
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

    fn boundary_completeness(
      denotation: PatternDenotation(UnitC, PatternBoundary(subject_start_constraint()), subject_initial_position(), no_chars(), no_chars())
    ) -> BoundaryAcceptance(subject_start_constraint(), no_chars(), subject_initial_position()) = boundary_denotation_is_complete(
      subject_start_constraint(),
      no_chars(),
      subject_initial_position(),
      denotation
    )

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

    fn grouped_predicate_soundness(
      {final_evidence: List(Evidence)},
      {routine: List(ExtendedInstruction)},
      acceptance: MachineAcceptance(1, group_pattern_machine(1, Cons(predicate_machine_start(), Nil()), predicate_machine_next(accepts_a)), subject_initial_position(), Cons('a', Nil()), Nil(), final_evidence, routine)
    ) -> PatternDenotation(StringC, PatternGroup(PatternPredicate(accepts_a)), subject_initial_position(), Cons('a', Nil()), Nil()) =
      grouped_predicate_acceptance_is_sound(accepts_a, 'a', Nil(), subject_initial_position(), final_evidence, routine, acceptance)

    fn concatenated_empty_denotation() -> PatternDenotation(PairC(UnitC, UnitC), PatternConcat(PatternEmpty(), PatternEmpty()), subject_initial_position(), no_chars(), no_chars()) =
      DenotesConcat(PatternEmpty(), PatternEmpty(), no_chars(), no_chars(), Std.Regex.Proof.input_partition_here(no_chars()), DenotesEmpty(), DenotesEmpty())

    fn concatenated_predicate_soundness(
      {final_evidence: List(Evidence)},
      {routine: List(ExtendedInstruction)},
      acceptance: MachineAcceptance(2, concat_pattern_machine(1, predicate_pattern_machine(accepts_a), 1, predicate_pattern_machine(accepts_b)), subject_initial_position(), Cons('a', Cons('b', Nil())), Nil(), final_evidence, routine)
    ) -> PatternDenotation(PairC(CharC, CharC), PatternConcat(PatternPredicate(accepts_a), PatternPredicate(accepts_b)), subject_initial_position(), Cons('a', Cons('b', Nil())), Nil()) =
      predicate_concat_acceptance_is_sound(accepts_a, accepts_b, Cons('a', Cons('b', Nil())), Nil(), subject_initial_position(), final_evidence, routine, acceptance)

    fn alternate_left_denotation() -> PatternDenotation(ChoiceC(UnitC, UnitC), PatternAlternate(PatternEmpty(), PatternEmpty()), subject_initial_position(), no_chars(), no_chars()) =
      DenotesAlternateLeft(PatternEmpty(), PatternEmpty(), DenotesEmpty())

    fn alternate_mode_right_denotation() -> PatternDenotation(ChoiceC(UnitC, UnitC), PatternAlternateMode(PatternEmpty(), PatternEmpty(), True()), subject_initial_position(), Nil(), Nil()) =
      DenotesAlternateModeRight(PatternEmpty(), PatternEmpty(), True(), DenotesEmpty())

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

    fn repeated_mode_empty_denotation() -> PatternDenotation(ListC(CharC), PatternRepeatMode(PatternPredicate(accepts_a), True()), subject_initial_position(), Nil(), Nil()) =
      DenotesRepeatModeEmpty(PatternPredicate(accepts_a), True())

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
          :"Std.Regex.Language#empty_acceptance_is_sound",
          :"Std.Regex.Language#empty_denotation_is_complete",
          :"Std.Regex.Language#empty_pattern_denotation_is_complete",
          :"Std.Regex.Language#boundary_acceptance_is_sound",
          :"Std.Regex.Language#boundary_denotation_is_complete",
          :"Std.Regex.Language#boundary_pattern_denotation_is_complete"
        ] do
      assert Env.total?(env, name), "expected #{inspect(name)} to be total"
    end
  end

  test "recursive denotation preserves grouped child membership" do
    assert {:ok, env} = Program.elaborate(@source)
    assert Env.total?(env, :grouped_predicate_denotation)
    assert Env.total?(env, :grouped_predicate_soundness)
    assert Env.total?(env, :"Std.Regex.Language#grouped_predicate_acceptance_is_sound")
    assert Env.total?(env, :concatenated_empty_denotation)
    assert Env.total?(env, :concatenated_predicate_soundness)
    assert Env.total?(env, :"Std.Regex.Language#predicate_concat_acceptance_is_sound")
    assert Env.total?(env, :alternate_left_denotation)
    assert Env.total?(env, :alternate_mode_right_denotation)
    assert Env.total?(env, :alternate_predicate_soundness)
    assert Env.total?(env, :"Std.Regex.Language#predicate_alternate_mode_acceptance_is_sound")
    assert Env.total?(env, :repeated_predicate_denotation)
    assert Env.total?(env, :repeated_mode_empty_denotation)
    assert Env.total?(env, :repeated_predicate_soundness)
    assert Env.total?(env, :"Std.Regex.Language#predicate_repeat_mode_acceptance_is_sound")
    assert Env.total?(env, :repeated_predicate_default_soundness)
    assert Env.total?(env, :"Std.Regex.Language#predicate_repeat_acceptance_is_sound")
  end
end
