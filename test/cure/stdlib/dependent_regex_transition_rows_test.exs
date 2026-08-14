defmodule Cure.Stdlib.DependentRegexTransitionRowsTest do
  use ExUnit.Case, async: false

  @tag timeout: 600_000
  test "compiled transition rows agree with the canonical Thompson transition function" do
    source = """
    mod RegexTransitionRows
      use Std.Regex

      fn same(expected: Char) -> Char -> Bool =
        fn(actual) -> Std.Char.same(expected, actual)

      fn atom(char: Char) -> Pattern(CharC) = PatternPredicate(same(char))
      fn pattern() -> Pattern(PairC(CharC, ChoiceC(CharC, CharC))) =
        PatternConcat(atom('a'), PatternAlternate(atom('b'), atom('c')))

      fn destination_count({n: Nat}, values: List(MachineState(n))) -> Int = match values
        [] -> 0
        [_ | rest] -> Std.Builtin.int_add(1, destination_count(rest))

      fn agrees(state: Bounded(S(S(S(Z())))), char: Char) -> Bool =
        let compilation = certify_thompson(pattern())
        let machine: PatternMachine(S(S(S(Z())))) = thompson_machine(compilation)
        let direct = pattern_machine_next(machine)(state, char)
        let rows = compile_transition_rows(S(S(S(Z()))), machine)
        destination_count(direct) == destination_count(transition_rows_next(rows, state, char))
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)

    states = [0, 1, 2]

    for state <- states, char <- ~c"abcd" do
      assert apply(module, :agrees, [state, char])
    end
  end
end
