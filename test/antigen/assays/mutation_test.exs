defmodule Antigen.Assays.MutationTest do
  use ExUnit.Case, async: true
  alias Antigen.Assays.Mutation, as: MA
  alias Antigen.Generators.Mutation
  alias Antigen.Backend.StreamData, as: B

  defp sample(gen, n), do: B.interp(gen) |> Enum.take(n)

  test "run/1 returns :ok when the kernel correctly rejects the mutant" do
    for c <- sample(Mutation.mutant(), 40), do: assert(MA.run(c) == :ok)
  end

  test "run/2 flags a violation when the (stubbed) kernel ACCEPTS an ill-typed term" do
    [c | _] = sample(Mutation.mutant(), 1)
    accept = fn _ctx, _term -> {:ok, {:vtype, 0}} end
    assert {:violation, {:accepted_ill_typed, term, fault}} = MA.run(c, accept)
    assert term == c.payload.term
    assert fault == c.payload.fault
  end
end
