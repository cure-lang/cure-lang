defmodule Cure.Core.MutualSizeChangeClosureTest do
  use ExUnit.Case, async: false

  alias Cure.Core.{Certificate, Env}
  alias Cure.Dev.Trace

  @grade Cure.Core.Grade.unrestricted()
  @type0 {:type, 0}

  test "mutual closure composes only compatible canonical edge pairs" do
    env =
      Env.empty()
      |> add_cycle_def(:f, :g)
      |> add_cycle_def(:g, :h)
      |> add_cycle_def(:h, :f)

    %{body: body} = Env.get_def(env, :f)
    {:ok, counter} = Agent.start_link(fn -> 0 end)

    {terminates?, events} =
      Trace.calls(
        Certificate,
        :compose_pair,
        fn -> Certificate.terminating?(:f, body, env) end,
        arity: 2,
        collect: false,
        format: fn _term -> :edge_pair end,
        on_call: fn _args -> Agent.update(counter, &(&1 + 1)) end
      )

    attempts = Agent.get(counter, & &1)
    Agent.stop(counter)

    refute terminates?
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
