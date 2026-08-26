defmodule Cure.Core.AbsurdLeafTest do
  @moduledoc """
  The {:absurd} leaf is DELETED from produced/final Core (K4 §H): the elaborator
  omits impossible branches, the validator release-rejects it, and Term.term?
  excludes it. What remains — and what these pins guard — is the RETAINED
  defensive handling of the grammar-excluded shape: `infer` has no catch-all, so
  its {:absurd} clause is load-bearing for kernel totality (a hand-crafted
  {:absurd} in a reachable position must return a clean {:error, _}, never crash);
  and serialize must round-trip it for decode robustness. Removing either would
  degrade robustness, not tighten — so they stay.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Context, Env, Kernel, Serialize}

  test "infer/2 rejects {:absurd} cleanly instead of raising" do
    ctx = Context.empty(Env.empty())
    assert {:error, :absurd_in_reachable_position} = Kernel.infer(ctx, {:absurd})
  end

  test "{:absurd} serializes and parses back to itself" do
    assert {:ok, {:absurd}} = Serialize.decode(Serialize.encode({:absurd}))
  end
end
