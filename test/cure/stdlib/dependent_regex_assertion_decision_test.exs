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
end
