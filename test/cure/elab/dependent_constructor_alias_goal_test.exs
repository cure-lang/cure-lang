defmodule Cure.Elab.DependentConstructorAliasGoalTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "an implicit constructor checks against a dependent alias-hidden field goal" do
    source = """
    mod DependentConstructorAliasGoal
      use Std.Nat
      type Acceptance indices ()
        Accepted : (value: Nat) -> Acceptance

      fn acceptance_value(acceptance: Acceptance) -> Nat = match acceptance
        Accepted(value) -> value

      type Execution indices (input: Nat, output: Nat)
        Done : {value: Nat} -> Execution(value, value)

      typealias HiddenExecution(input: Nat, output: Nat) = Execution(input, output)

      type Projection indices ()
        Projected : (acceptance: Acceptance) -> (execution: HiddenExecution(acceptance_value(acceptance), acceptance_value(acceptance))) -> Projection

      fn project(value: Nat) -> Projection =
        let acceptance = Accepted(value)
        Projected(acceptance, Done())
    """

    assert {:ok, _env} = Program.elaborate(source)
  end
end
