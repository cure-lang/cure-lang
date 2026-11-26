defmodule Cure.Core.Phase5LevelRewriteTest do
  @moduledoc """
  Rewrite-plan representation tests, not checked equality evidence.

  Expected rewritten atoms are constructed independently. Motive beta checks
  exercise the existing NbE/readback path without claiming kernel admission.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Eval, Quote, Term, UniverseLevel}
  alias Cure.Elab.Rewrite
  alias Cure.Core.UniverseLevel, as: L

  @kinds [:finite_sort, :level_value]
  @grades [:erased, :linear, :affine, :unrestricted]
  @proof {:global, :"Phase5#proof"}
  @evidence {:global, :"Phase5#evidence"}

  test "all rewrites original atom paths without an intermediate canonical merge" do
    target = a(0)
    replacement = f(target)

    for kind <- @kinds do
      original = wrap(kind, join(target, replacement))
      expected = wrap(kind, join(replacement, f(replacement)))
      assert payload(original).atoms == [{target, 0}, {replacement, 0}]

      assert {:ok, build, rewritten, [first, second]} = plan(original, target, replacement, :all)
      assert first.number == 1 and second.number == 2
      assert rewritten == expected
      assert payload(rewritten).atoms == [{replacement, 0}, {f(replacement), 0}]
      assert :ok = L.validate(payload(rewritten), nil)

      assert {:app, {:case, @proof, _, [_]}, @evidence} = build.(@evidence)
      assert count_cases(build.(@evidence)) == 1
      assert_motive_beta(build, target, replacement, original, expected)
    end
  end

  test "selected occurrences use the original portable order even when replacement merges atoms" do
    target = a(0)
    replacement = f(target)

    for kind <- @kinds do
      original = wrap(kind, join(target, replacement))
      assert {:error, {:ambiguous_occurrence, [_, _]}} = plan(original, target, replacement, nil)

      assert {:ok, first_build, first, [_, _]} = plan(original, target, replacement, 1)
      assert first == wrap(kind, L.atom(replacement))
      assert_motive_beta(first_build, target, replacement, original, first)

      assert {:ok, second_build, second, [_, _]} = plan(original, target, replacement, 2)
      assert second == wrap(kind, join(target, f(replacement)))
      assert_motive_beta(second_build, target, replacement, original, second)

      assert {:error, {:invalid_occurrence, 3, [_, _]}} = plan(original, target, replacement, 3)
    end
  end

  test "rebuilding restores portable ordering after a replacement crosses another atom" do
    target = {:global, :aaa}
    middle = {:global, :mmm}
    replacement = {:global, :zzz}

    for kind <- @kinds do
      original = wrap(kind, join(target, middle))
      assert payload(original).atoms == [{target, 0}, {middle, 0}]
      assert {:ok, build, rewritten, [_]} = plan(original, target, replacement, :all)
      assert rewritten == wrap(kind, join(middle, replacement))
      assert payload(rewritten).atoms == [{middle, 0}, {replacement, 0}]
      assert_motive_beta(build, target, replacement, original, rewritten)
    end
  end

  test "all respects Pi lambda and let depths while preserving binder grades" do
    target = a(0)
    replacement = f(target)

    for kind <- @kinds, grade <- @grades do
      body = wrap(kind, join(a(1), f(a(1))))
      rewritten_body = wrap(kind, join(f(a(1)), f(f(a(1)))))

      for {original, expected} <- [
            {{:lam, grade, {:level_type}, body}, {:lam, grade, {:level_type}, rewritten_body}},
            {{:pi, grade, {:level_type}, body}, {:pi, grade, {:level_type}, rewritten_body}},
            {{:let, grade, {:level_type}, {:level_value, L.closed(0)}, body},
             {:let, grade, {:level_type}, {:level_value, L.closed(0)}, rewritten_body}}
          ] do
        assert {:ok, build, rewritten, [_, _]} = plan(original, target, replacement, :all)
        assert rewritten == expected
        assert elem(rewritten, 1) == grade
        assert_motive_beta(build, target, replacement, original, expected)
      end
    end
  end

  test "all batches case branch paths with their distinct constructor arities" do
    target = a(0)
    replacement = f(target)

    for kind <- @kinds do
      original =
        {:case, {:global, :"Phase5#scrutinee"}, {:level_type},
         [
           {:ZeroFields, 0, wrap(kind, join(a(0), f(a(0))))},
           {:TwoFields, 2, wrap(kind, join(a(2), f(a(2))))}
         ]}

      expected =
        {:case, {:global, :"Phase5#scrutinee"}, {:level_type},
         [
           {:ZeroFields, 0, wrap(kind, join(f(a(0)), f(f(a(0)))))},
           {:TwoFields, 2, wrap(kind, join(f(a(2)), f(f(a(2)))))}
         ]}

      assert {:ok, build, rewritten, [_, _, _, _]} = plan(original, target, replacement, :all)
      assert rewritten == expected
      assert_motive_beta(build, target, replacement, original, expected)
    end
  end

  test "both directed orientations produce the same independently specified original-path rewrite" do
    target = a(0)
    replacement = f(target)

    for kind <- @kinds do
      original = wrap(kind, join(target, replacement))
      expected = wrap(kind, join(replacement, f(replacement)))

      assert {:ok, _, ^expected, [_, _]} =
               Rewrite.directed_plan(@proof, {:level_type}, target, replacement, original, :forward, :all)

      assert {:ok, _, ^expected, [_, _]} = plan(original, target, replacement, :all)
    end
  end

  test "ordinary non-level rewrite-all retains its existing transport chain" do
    left = {:int_lit, 0}
    right = {:int_lit, 1}
    original = {:ctor, :Pair, [left, left]}
    expected = {:ctor, :Pair, [right, right]}

    assert {:ok, build, ^expected, [_, _]} =
             Rewrite.directed_plan(@proof, {:int_type}, right, left, original, :backwards, :all)

    assert count_cases(build.(@evidence)) == 2
  end

  test "mixed ordinary and level occurrences share one original-path batch" do
    target = a(0)
    replacement = f(target)

    for kind <- @kinds do
      original = {:ctor, :Mixed, [target, wrap(kind, join(target, replacement))]}
      expected = {:ctor, :Mixed, [replacement, wrap(kind, join(replacement, f(replacement)))]}
      assert {:ok, build, rewritten, [_, _, _]} = plan(original, target, replacement, :all)
      assert rewritten == expected
      assert count_cases(build.(@evidence)) == 1
      assert_motive_beta(build, target, replacement, original, expected)
    end
  end

  defp plan(original, target, replacement, selector),
    do: Rewrite.directed_plan(@proof, {:level_type}, replacement, target, original, :backwards, selector)

  defp assert_motive_beta(build, target, replacement, original, rewritten) do
    assert {:app, {:case, _proof, _arrow_motive, [{_, 1, {:lam, _, {:app, shifted_motive, _}, {:var, 0}}}]}, @evidence} =
             build.(@evidence)

    motive = Term.shift(shifted_motive, -1, 0)
    assert {:lam, :erased, {:level_type}, _body} = motive
    assert normal({:app, motive, target}) == normal(original)
    assert normal({:app, motive, replacement}) == normal(rewritten)
  end

  defp normal(term), do: term |> Eval.eval(Context.neutral_env(1)) |> Quote.reify(1)
  defp a(index), do: {:app, {:global, :aaa}, {:var, index}}
  defp f(argument), do: {:app, {:global, :zzz}, argument}
  defp join(left, right), do: L.max(L.atom(left), L.atom(right))
  defp wrap(:finite_sort, level), do: {:type, {:finite, level}}
  defp wrap(:level_value, level), do: {:level_value, level}
  defp payload({:type, {:finite, level}}), do: level
  defp payload({:level_value, level}), do: level

  defp count_cases({:case, _, _, _} = node), do: 1 + count_case_children(node)
  defp count_cases(tuple) when is_tuple(tuple), do: count_case_children(tuple)
  defp count_cases(list) when is_list(list), do: list |> Enum.map(&count_cases/1) |> Enum.sum()
  defp count_cases(%UniverseLevel{atoms: atoms}), do: count_cases(atoms)
  defp count_cases(_leaf), do: 0
  defp count_case_children(tuple), do: tuple |> Tuple.to_list() |> Enum.map(&count_cases/1) |> Enum.sum()
end
