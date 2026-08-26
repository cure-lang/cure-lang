defmodule Cure.Elab.IfLowersToCaseTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program
  alias Cure.Core.Env

  defp body_of(env, name), do: Env.get_def(env, name).body

  defp has_bool_elim?({:bool_elim, _, _, _, _}), do: true
  defp has_bool_elim?(t) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&has_bool_elim?/1)
  defp has_bool_elim?(l) when is_list(l), do: Enum.any?(l, &has_bool_elim?/1)
  defp has_bool_elim?(_), do: false

  defp has_case?({:case, _, _, _}), do: true
  defp has_case?(t) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&has_case?/1)
  defp has_case?(l) when is_list(l), do: Enum.any?(l, &has_case?/1)
  defp has_case?(_), do: false

  test "if on a Bool lowers to a :case core term, not bool_elim" do
    src = "mod M\n  type N = Z | S(N)\n  fn f(b: Bool) -> N = if b then S(Z()) else Z()\n"
    {:ok, env} = Program.elaborate(src)
    body = body_of(env, :f)
    assert has_case?(body)
    refute has_bool_elim?(body)
  end
end
