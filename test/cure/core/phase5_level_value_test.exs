defmodule Cure.Core.Phase5LevelValueTest do
  @moduledoc """
  U2 NbE representation tests, not kernel admission or typing judgments.

  The same open semantic level must read back differently at different depths;
  quoted Core indices must never be mistaken for absolute semantic levels.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Eval, LevelValue, Quote, Term, UniverseLevel, Value}
  alias Cure.Core.UniverseLevel, as: L

  test "beta and zeta evaluate level atoms in their actual environment" do
    for kind <- [:finite_sort, :level_value] do
      body = wrap(kind, L.succ(L.atom({:var, 0})))
      beta = {:app, {:lam, :erased, {:level_type}, body}, {:level_value, L.closed(36)}}
      zeta = {:let, :erased, {:level_type}, {:level_value, L.closed(36)}, body}
      assert Quote.reify(Eval.eval(beta, [])) == wrap(kind, L.closed(37))
      assert Quote.reify(Eval.eval(zeta, [])) == wrap(kind, L.closed(37))
    end
  end

  test "the same open semantic value quotes at the requested binder depth" do
    for kind <- [:finite_sort, :level_value] do
      semantic = Eval.eval(wrap(kind, L.succ(L.atom({:var, 0}))), [{:vneutral, {:nvar, 0}}])
      assert Quote.reify(semantic, 1) == wrap(kind, L.succ(L.atom({:var, 0})))
      assert Quote.reify(semantic, 2) == wrap(kind, L.succ(L.atom({:var, 1})))
      assert Quote.reify(semantic, 5) == wrap(kind, L.succ(L.atom({:var, 4})))
    end
  end

  test "nested Pi closures preserve captured closed levels in both payload forms" do
    for kind <- [:finite_sort, :level_value] do
      body = wrap(kind, L.succ(L.atom({:var, 2})))
      term = {:pi, :erased, {:level_type}, {:pi, :erased, {:level_type}, body}}
      captured = Eval.eval(term, [{:vlevel, LevelValue.closed(36)}])

      expected =
        {:pi, :erased, {:level_type}, {:pi, :erased, {:level_type}, wrap(kind, L.closed(37))}}

      assert Quote.reify(captured) == expected
    end
  end

  test "lambda readback keeps the fresh bound level distinct from captured open levels" do
    for kind <- [:finite_sort, :level_value] do
      body = wrap(kind, L.max(L.atom({:var, 0}), L.succ(L.atom({:var, 1}))))
      term = {:lam, :erased, {:level_type}, body}
      captured = Eval.eval(term, [{:vneutral, {:nvar, 0}}])
      assert Quote.reify(captured, 1) == term

      shifted_body = wrap(kind, L.max(L.atom({:var, 0}), L.succ(L.atom({:var, 2}))))
      assert Quote.reify(captured, 2) == {:lam, :erased, {:level_type}, shifted_body}
    end
  end

  test "neutral application arguments retain their evaluated captured environment" do
    atom = {:app, {:var, 0}, {:var, 1}}
    env = [{:vneutral, {:nglobal, :opaque_level}}, {:vlevel, LevelValue.closed(37)}]
    expected_atom = {:app, {:global, :opaque_level}, {:level_value, L.closed(37)}}

    for kind <- [:finite_sort, :level_value] do
      actual = Eval.eval(wrap(kind, L.atom(atom)), env)
      assert Quote.reify(actual) == wrap(kind, L.atom(expected_atom))
    end
  end

  test "non-level atom results raise rather than becoming fallback atoms" do
    malformed = %UniverseLevel{constant: 0, atoms: [{{:int_lit, 37}, 0}]}

    for kind <- [:finite_sort, :level_value] do
      assert_raise ArgumentError, fn -> Eval.eval(wrap(kind, malformed), []) end
    end
  end

  test "Core and semantic level representations are disjoint at their boundaries" do
    semantic = LevelValue.closed(37)
    core = L.closed(37)
    assert Value.value?({:vlevel, semantic})
    assert Value.value?({:vtype, {:finite, semantic}})
    refute Value.value?({:vlevel, core})
    refute Value.value?({:vtype, {:finite, core}})
    assert Term.term?({:level_value, core})
    assert Term.term?({:type, {:finite, core}})
    refute Term.term?({:level_value, semantic})
    refute Term.term?({:type, {:finite, semantic}})
    refute Term.term?({:type, 37})
    refute Term.term?({:lam, :erased, {:level_type}, {:type, 0}})
  end

  defp wrap(:finite_sort, level), do: {:type, {:finite, level}}
  defp wrap(:level_value, level), do: {:level_value, level}
end
