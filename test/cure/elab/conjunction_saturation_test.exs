defmodule Cure.Elab.ConjunctionSaturationTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  defp has_hole?({:hole, _}), do: true
  defp has_hole?(t) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&has_hole?/1)
  defp has_hole?(l) when is_list(l), do: Enum.any?(l, &has_hole?/1)
  defp has_hole?(m) when is_map(m), do: m |> Map.values() |> Enum.any?(&has_hole?/1)
  defp has_hole?(_), do: false

  @src """
  mod ConjunctionSaturation
    use Std.Bool
    use Std.Proof.IntMath
    use Std.Proof.BooleanReflection

    # `p`/`q` are relevant (grade-ω): the elimination lemma matches on the operand,
    # so an erased operand could not be passed to it under QTT.
    fn pick_left(p: Bool, q: Bool, both: IsTrue(`and`(p, q))) -> IsTrue(p) = ?
  end
  """

  test "an IsTrue(left) goal is discharged from an IsTrue(and(left,right)) hypothesis" do
    assert {:ok, env} = Program.elaborate(@src)

    f =
      Enum.find(Map.values(env.defs), fn d ->
        is_map(d) and to_string(Map.get(d, :name)) |> String.ends_with?("pick_left")
      end)

    refute has_hole?(f.body), "conjunction elimination should have filled the hole"
  end
end
