defmodule Cure.Core.TotalityCertificatePropertyTest do
  use ExUnit.Case, async: true
  use ExUnitProperties

  alias Cure.Core.{Certificate, Env, SizeChange}
  alias Cure.Elab.TotalityGraph

  @names [:a, :b, :c, :d, :e, :f]
  @relations [:unknown, :equal, :smaller]

  property "sparse composition agrees with a dense semiring oracle" do
    check all(
            left <- list_of(member_of(@relations), length: 9),
            right <- list_of(member_of(@relations), length: 9),
            max_runs: 100
          ) do
      left = Enum.chunk_every(left, 3)
      right = Enum.chunk_every(right, 3)

      actual =
        left
        |> SizeChange.from_dense()
        |> SizeChange.compose_matrices(SizeChange.from_dense(right))
        |> SizeChange.to_dense()

      assert actual == dense_compose(left, right)
    end
  end

  property "SCC identity and witnesses are invariant under every submitted member order" do
    check all({names, order} <- cycle_and_permutation(), max_runs: 60) do
      env = cycle_env(names)
      canonical = TotalityGraph.propose_partition(env, names)
      assert TotalityGraph.propose_partition(env, order) == canonical
    end
  end

  property "fresh and cache-validated direct summaries are identical" do
    check all(depth <- integer(0..8), max_runs: 40) do
      env =
        Env.empty()
        |> Env.with_owner("Property")
        |> Env.add_def(:leaf, {:type, 0}, {:type, 0})

      body = nested_calls(depth)
      env = Env.add_def(env, :root, {:type, 0}, body)
      fresh = Certificate.direct_summary(:root, body, env)

      assert Certificate.cached_summary_valid?(fresh, :root, body, env)
      assert fresh == Certificate.direct_summary(:root, body, env)
      assert Enum.count(fresh.calls) == depth
      assert fresh.calls |> Enum.map(& &1.id) |> Enum.uniq() |> length() == depth
    end
  end

  defp cycle_and_permutation do
    bind(integer(1..length(@names)), fn count ->
      names = Enum.take(@names, count)

      integer()
      |> list_of(length: count)
      |> map(fn keys ->
        order = names |> Enum.zip(keys) |> Enum.sort_by(fn {name, key} -> {key, name} end) |> Enum.map(&elem(&1, 0))
        {names, order}
      end)
    end)
  end

  defp cycle_env(names) do
    names
    |> Enum.with_index()
    |> Enum.reduce(Env.empty(), fn {name, index}, env ->
      callee = Enum.at(names, rem(index + 1, length(names)))
      Env.add_def(env, name, {:type, 0}, {:global, callee})
    end)
    |> then(fn env ->
      Enum.reduce(names, env, fn name, acc ->
        %{body: body} = Env.get_def(acc, name)
        Env.put_direct_call_summary(acc, name, Certificate.direct_summary(name, body, acc))
      end)
    end)
  end

  defp nested_calls(0), do: {:type, 0}

  defp nested_calls(depth),
    do: {:app, {:global, :leaf}, nested_calls(depth - 1)}

  defp dense_compose(left, right) do
    for i <- 0..2 do
      for j <- 0..2 do
        Enum.reduce(0..2, :unknown, fn k, relation ->
          add(relation, multiply(Enum.at(Enum.at(left, i), k), Enum.at(Enum.at(right, k), j)))
        end)
      end
    end
  end

  defp multiply(:unknown, _), do: :unknown
  defp multiply(_, :unknown), do: :unknown
  defp multiply(:smaller, _), do: :smaller
  defp multiply(_, :smaller), do: :smaller
  defp multiply(:equal, :equal), do: :equal

  defp add(:smaller, _), do: :smaller
  defp add(_, :smaller), do: :smaller
  defp add(:equal, _), do: :equal
  defp add(_, :equal), do: :equal
  defp add(:unknown, :unknown), do: :unknown
end
