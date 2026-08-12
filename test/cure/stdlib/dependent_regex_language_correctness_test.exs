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

  """

  test "predicate denotation is sound for certified execution" do
    assert {:ok, env} = Program.elaborate(@source)
    assert Env.total?(env, :predicate_soundness)
    assert Env.total?(env, :"Std.Regex.Language#predicate_acceptance_is_sound")
  end
end
