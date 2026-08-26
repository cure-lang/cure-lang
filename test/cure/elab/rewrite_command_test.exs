defmodule Cure.Elab.RewriteCommandTest do
  use ExUnit.Case, async: true

  alias Cure.Core.Grade
  alias Cure.Elab.Rewrite

  test "occurrence traversal is left-to-right and binder-aware" do
    target = {:var, 0}

    goal =
      {:pi, Grade.unrestricted(), {:int_type},
       {:data, :"Std.Equivalent#Equivalent", [{:int_type}], [{:var, 1}, {:var, 1}]}}

    occurrences = Rewrite.occurrences(goal, target)
    assert Enum.map(occurrences, & &1.number) == [1, 2]
    assert Enum.map(occurrences, & &1.traversal_path) == [[2, 2, 0], [2, 2, 1]]
    assert Enum.all?(occurrences, &match?([:normalized_goal | _], &1.source_path))
  end

  test "nested application occurrences retain stable traversal paths" do
    target = {:var, 0}
    goal = {:app, {:global, :outer}, {:app, {:global, :inner}, target}}

    assert [%Rewrite.Occurrence{number: 1, traversal_path: [1, 1]}] = Rewrite.occurrences(goal, target)
  end

  test "scoped replacement follows a target beneath dependent binders" do
    target = {:app, {:global, :f}, {:var, 0}}

    term =
      {:pi, Grade.unrestricted(), {:int_type}, {:app, {:global, :uses}, {:app, {:global, :f}, {:var, 1}}}}

    assert Rewrite.replace_term_scoped(term, target, {:var, 7}) ==
             {:pi, Grade.unrestricted(), {:int_type}, {:app, {:global, :uses}, {:var, 8}}}
  end

  test "scoped replacement follows constructor branch arity" do
    target = {:app, {:global, :f}, {:var, 0}}

    term =
      {:case, {:var, 0}, {:global, :motive},
       [{:SomeCtor, 2, {:app, {:global, :uses}, {:app, {:global, :f}, {:var, 2}}}}]}

    assert Rewrite.replace_term_scoped(term, target, {:var, 5}) ==
             {:case, {:var, 0}, {:global, :motive}, [{:SomeCtor, 2, {:app, {:global, :uses}, {:var, 7}}}]}
  end

  test "scoped occurrence detection follows constructor branch arity" do
    target = {:app, {:var, 2}, {:var, 1}}

    term =
      {:case, {:var, 0}, {:global, :motive}, [{:SomeCtor, 3, {:app, {:global, :uses}, {:app, {:var, 5}, {:var, 4}}}}]}

    refute Rewrite.contains_term?(term, target)
    assert Rewrite.contains_term_scoped?(term, target)
  end
end
