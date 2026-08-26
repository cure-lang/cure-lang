defmodule Cure.Core.MutualSizeChangeClosureTest do
  use ExUnit.Case, async: false

  alias Cure.Core.{Env, Kernel, SizeChange, TotalityCertificate}
  alias Cure.Dev.Trace
  alias Cure.Elab.TotalityGraph

  @grade Cure.Core.Grade.unrestricted()
  @type0 {:type, 0}

  test "mutual closure composes only compatible canonical edge pairs" do
    env =
      Env.empty()
      |> add_cycle_def(:f, :g)
      |> add_cycle_def(:g, :h)
      |> add_cycle_def(:h, :f)

    {:ok, env} = Kernel.prepare_direct_call_summaries(env, [:f, :g, :h])
    partition = TotalityGraph.propose_partition(env, [:f, :g, :h])
    %{members: members} = Map.fetch!(partition.components, partition.component_of.f)
    {:ok, counter} = Agent.start_link(fn -> 0 end)

    {candidate, events} =
      Trace.calls(
        SizeChange,
        :compose_edges,
        fn -> Cure.Elab.TotalityCertificate.propose(env, members) end,
        arity: 2,
        collect: false,
        format: fn _term -> :edge_pair end,
        on_call: fn _args -> Agent.update(counter, &(&1 + 1)) end
      )

    attempts = Agent.get(counter, & &1)
    Agent.stop(counter)

    assert {:ok, {:not_total, _edge}} = TotalityCertificate.verify(env, members, candidate)
    assert events == []

    # The closure has one 1x1 matrix for each of the 3x3 source/target pairs.
    # For each intermediate node there are 3 incoming × 3 outgoing compatible
    # ordered pairs: 3 × 3 × 3 = 27. More calls mean the worklist retried an
    # already-considered pair or attempted a source/target-incompatible pair.
    assert attempts <= 27
  end

  defp add_cycle_def(env, name, callee) do
    type = {:pi, @grade, @type0, @type0}
    body = {:lam, @grade, @type0, {:app, {:global, callee}, {:var, 0}}}
    Env.add_def(env, name, type, body)
  end
end
