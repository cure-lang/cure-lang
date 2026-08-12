defmodule Cure.Stdlib.DependentRegexLanguageCorrectnessTest do
  use ExUnit.Case, async: true

  alias Cure.Core.Env
  alias Cure.Elab.Program

  @source """
  mod RegexLanguageCorrectness
    use Std.Regex
    use Std.Regex.Language

    fn accepts_a(char: Char) -> Bool = char == 'a'
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

  """

  test "predicate denotation is sound for certified execution" do
    assert {:ok, env} = Program.elaborate(@source)
    assert Env.total?(env, :predicate_soundness)
    assert Env.total?(env, :"Std.Regex.Language#predicate_acceptance_is_sound")
  end

  test "predicate denotation constructively produces certified execution" do
    assert {:ok, env} = Program.elaborate(@source)
    assert Env.total?(env, :predicate_completeness)
    assert Env.total?(env, :"Std.Regex.Language#predicate_denotation_is_complete")
  end

  test "empty and boundary denotations are sound and constructively complete" do
    assert {:ok, env} = Program.elaborate(@source)

    for name <- [
          :empty_soundness,
          :empty_completeness,
          :boundary_soundness,
          :boundary_completeness,
          :"Std.Regex.Language#empty_acceptance_is_sound",
          :"Std.Regex.Language#empty_denotation_is_complete",
          :"Std.Regex.Language#boundary_acceptance_is_sound",
          :"Std.Regex.Language#boundary_denotation_is_complete"
        ] do
      assert Env.total?(env, name), "expected #{inspect(name)} to be total"
    end
  end
end
