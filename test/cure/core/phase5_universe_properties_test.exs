defmodule Cure.Core.Phase5UniversePropertiesTest do
  @moduledoc """
  Independent finite-model checks over generated open maximum-plus expressions.

  No property uses normalizing equality to conceal noncanonical constructor
  output. The oracle interprets an expression tree over natural valuations and
  separately checks the returned constant/atom invariant.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Term, UniverseLevel}
  alias Cure.Core.UniverseLevel, as: L

  test "generated open constructors are directly canonical and preserve valuations" do
    for expression <- expressions() do
      level = construct(expression)
      assert_canonical(level)

      for valuation <- valuations() do
        assert evaluate_nf(level, valuation) == evaluate_expression(expression, valuation)
      end
    end
  end

  test "generated open joins obey algebra as literal canonical outputs" do
    levels = Enum.map(expressions(), &construct/1)

    for {left, index} <- Enum.with_index(levels) do
      right = Enum.at(levels, rem(index * 7 + 3, Enum.count(levels)))
      third = Enum.at(levels, rem(index * 11 + 5, Enum.count(levels)))
      joined = L.max(left, right)
      successor = L.succ(left)
      assert_canonical(joined)
      assert_canonical(successor)
      assert L.max(left, right) == L.max(right, left)
      assert L.max(L.max(left, right), third) == L.max(left, L.max(right, third))
      assert L.max(left, left) == left
      assert L.max(left, L.zero()) == left
      assert L.succ(L.max(left, right)) == L.max(L.succ(left), L.succ(right))
      assert L.max(left, L.succ(left)) == L.succ(left)
      assert L.leq?(left, successor, nil)
      refute L.leq?(successor, left, nil)
    end
  end

  test "ordering agrees with independently enumerated separating natural valuations" do
    expressions = expressions()

    for {expression, index} <- Enum.with_index(expressions) do
      other = Enum.at(expressions, rem(index * 13 + 9, Enum.count(expressions)))
      left = construct(expression)
      right = construct(other)

      oracle =
        Enum.all?(separating_valuations(), fn valuation ->
          evaluate_expression(expression, valuation) <= evaluate_expression(other, valuation)
        end)

      assert L.leq?(left, right, nil) == oracle
    end
  end

  test "known level atoms and substitution flatten offsets without keeping value wrappers" do
    for constant <- [0, 1, 37, 10 ** 40], offset <- 0..4 do
      inner = L.max(L.closed(constant), L.atom({:var, 1}))
      outer = %UniverseLevel{constant: 0, atoms: [{{:level_value, inner}, offset}]}
      expected = iterate_succ(inner, offset)
      assert L.normalize(outer) == expected
      assert L.atom({:level_value, inner}) == inner
      assert_canonical(L.normalize(outer))

      substituted = L.subst(iterate_succ(L.atom({:var, 0}), offset), 0, {:level_value, inner})
      assert substituted == expected
      assert_canonical(substituted)
    end
  end

  test "shift and substitution do not capture nested binder variables" do
    for index <- 0..4 do
      term = {:lam, :erased, {:level_type}, {:app, {:var, 0}, {:var, index + 1}}}
      level = L.atom(term)
      shifted = L.shift(level, 2)
      assert shifted.atoms == [{{:lam, :erased, {:level_type}, {:app, {:var, 0}, {:var, index + 3}}}, 0}]
      assert L.shift(shifted, -2) == level

      substituted = L.subst(level, index, {:var, 2})
      assert substituted.atoms == [{{:lam, :erased, {:level_type}, {:app, {:var, 0}, {:var, 3}}}, 0}]
      assert L.free_vars(substituted) == [2]
    end
  end

  test "free-variable traversal sees nested finite sorts and level value containers" do
    inner = L.atom({:var, 2})
    nested_value = L.atom({:app, {:global, :opaque}, {:level_value, inner}})
    nested_sort = L.atom({:app, {:global, :opaque}, {:type, {:finite, inner}}})
    assert L.free_vars(nested_value) == [2]
    assert L.free_vars(nested_sort) == [2]
  end

  @tag :u2
  test "ordinary variable substitution is retained in the new grammar" do
    assert Term.subst({:var, 0}, 0, {:int_lit, 73}) == {:int_lit, 73}
    assert Term.subst({:var, 1}, 0, {:int_lit, 73}) == {:var, 1}
    assert Term.subst({:var, 0}, 1, {:int_lit, 73}) == {:var, 0}
  end

  @tag :u2
  test "finite sort substitution flattens levels under two erased binders" do
    body = {:type, {:finite, L.succ(L.atom({:var, 2}))}}
    term = {:lam, :erased, {:level_type}, {:lam, :erased, {:level_type}, body}}

    expected =
      {:lam, :erased, {:level_type}, {:lam, :erased, {:level_type}, {:type, {:finite, L.closed(38)}}}}

    assert Term.subst(term, 0, {:level_value, L.closed(37)}) == expected
  end

  @tag :u2
  test "case branch arity protects bound atoms but substitutes escaping atoms" do
    branch_level = L.max(L.atom({:var, 0}), L.atom({:var, 2}))
    term = {:case, {:var, 0}, {:level_type}, [{:C, 2, {:level_value, branch_level}}]}
    substituted = Term.subst(term, 0, {:level_value, L.closed(37)})
    expected_level = L.max(L.atom({:var, 0}), L.closed(37))

    assert substituted ==
             {:case, {:level_value, L.closed(37)}, {:level_type}, [{:C, 2, {:level_value, expected_level}}]}
  end

  defp expressions do
    base = [{:constant, 0}, {:constant, 2}, {:constant, 7}, {:variable, 0}, {:variable, 1}, {:variable, 2}]

    base ++
      Enum.map(base, &{:successor, &1}) ++
      for left <- base, right <- base do
        {:join, {:successor, left}, right}
      end
  end

  defp valuations, do: for(a <- [0, 1, 8], b <- [0, 2, 9], c <- [0, 3, 10], do: %{0 => a, 1 => b, 2 => c})

  # Every generated offset is <= 1 and constant <= 8. Values 0..10 plus
  # isolated 100 expose each unmatched atom and every constant/offset failure.
  defp separating_valuations do
    for a <- [0, 1, 2, 7, 8, 9, 10, 100],
        b <- [0, 1, 2, 7, 8, 9, 10, 100],
        c <- [0, 1, 2, 7, 8, 9, 10, 100],
        do: %{0 => a, 1 => b, 2 => c}
  end

  defp construct({:constant, n}), do: L.closed(n)
  defp construct({:variable, n}), do: L.atom({:var, n})
  defp construct({:successor, expression}), do: L.succ(construct(expression))
  defp construct({:join, left, right}), do: L.max(construct(left), construct(right))

  defp evaluate_expression({:constant, n}, _valuation), do: n
  defp evaluate_expression({:variable, n}, valuation), do: Map.fetch!(valuation, n)
  defp evaluate_expression({:successor, expression}, valuation), do: evaluate_expression(expression, valuation) + 1

  defp evaluate_expression({:join, left, right}, valuation),
    do: Kernel.max(evaluate_expression(left, valuation), evaluate_expression(right, valuation))

  defp evaluate_nf(%UniverseLevel{constant: c, atoms: atoms}, valuation) do
    Enum.reduce(atoms, c, fn {{:var, index}, offset}, acc ->
      Kernel.max(acc, Map.fetch!(valuation, index) + offset)
    end)
  end

  defp assert_canonical(%UniverseLevel{constant: c, atoms: atoms} = level) do
    assert :ok = L.validate(level, nil)
    assert is_integer(c) and c >= 0

    keys =
      Enum.map(atoms, fn {term, offset} ->
        assert is_integer(offset) and offset >= 0
        refute match?({:level_value, _}, term)
        L.atom_order_key(term)
      end)

    assert keys == Enum.sort(Enum.uniq(keys))
    assert c == 0 or Enum.all?(atoms, fn {_term, offset} -> offset < c end)
  end

  defp iterate_succ(level, 0), do: level
  defp iterate_succ(level, count), do: iterate_succ(L.succ(level), count - 1)
end
