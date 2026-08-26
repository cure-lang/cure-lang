defmodule Cure.Elab.NatReflectionDischargeTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  defp has_hole?({:hole, _}), do: true
  defp has_hole?(t) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&has_hole?/1)
  defp has_hole?(l) when is_list(l), do: Enum.any?(l, &has_hole?/1)
  defp has_hole?(m) when is_map(m), do: m |> Map.values() |> Enum.any?(&has_hole?/1)
  defp has_hole?(_), do: false

  @src """
  mod NatReflectionDischarge
    use Std.Nat
    use Std.Proof.IntMath
    use Std.Proof.Math

    # `a`/`b` are relevant (grade-ω): the reflection lemma inducts on the operands,
    # so a proof of `IsLessThan(a, b)` genuinely needs their values — an erased
    # operand could not be discharged under QTT, and in practice the operands are
    # concrete terms at the boundary anyway.
    fn derive(a: Nat, b: Nat, e: IsTrue(natural_is_less_than(a, b))) -> IsLessThan(a, b) = ?
  end
  """

  test "an IsLessThan goal is auto-discharged from an IsTrue(<) hypothesis via the tagged reflection lemma" do
    assert {:ok, env} = Program.elaborate(@src)

    derive =
      Enum.find(Map.values(env.defs), fn d ->
        is_map(d) and to_string(Map.get(d, :name)) |> String.ends_with?("derive")
      end)

    refute has_hole?(derive.body), "reflection lemma should have filled the hole"
  end
end
