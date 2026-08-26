defmodule Cure.Elab.OverloadTest do
  use ExUnit.Case, async: false
  alias Cure.Elab.Overload

  # Register a real two-member `plus` set through the elaborator so the stored
  # telescopes (and thus the parameter domains the engine prunes against) are
  # genuine Core terms, not hand-rolled.
  setup do
    src = """
    mod OvlEngine
      type Meters = MkM(Int)
      type Grams = MkG(Int)
      fn plus(a: Meters, b: Meters) -> Meters = a
      fn plus(a: Grams, b: Grams) -> Grams = a
    end
    """

    {:ok, env} = Cure.Elab.Program.elaborate(src)
    {:ok, env: env}
  end

  # The two `plus` members owned by OvlEngine, built straight off the registry.
  # (`Resolution.overload_candidates/2` gathers these at a real call site, where
  # `module_owner` is set; the post-elaboration env resets it, so we key on the
  # owner directly here to test the prune engine in isolation.)
  defp plus_candidates(env) do
    env.defs
    |> Map.keys()
    |> Enum.filter(fn k ->
      Cure.Elab.Name.owner(k) == "OvlEngine" and Cure.Elab.Name.overload_member?(k)
    end)
  end

  # The stored parameter domains of a member ARE valid closed type terms, so
  # feeding a member's own domains back in as "argument types" must resolve to
  # exactly that member — a behavioral round-trip that needs no synthetic terms.
  defp domains(env, key) do
    %{type: pi} = Cure.Core.Env.get_def(env, key)
    walk(pi)
  end

  defp walk({:pi, _g, d, c}), do: [d | walk(c)]
  defp walk(_), do: []

  test "a member's own domains resolve to that member's discriminated key", %{env: env} do
    cands = plus_candidates(env)
    assert length(cands) == 2

    for key <- cands do
      assert {:ok, ^key} = Overload.resolve(env, :plus, domains(env, key), nil, cands)
      assert Cure.Elab.Name.overload_base(key) == "plus"
    end
  end

  test "argument types matching no member yield :no_matching_overload", %{env: env} do
    cands = plus_candidates(env)
    # Int is not Meters or Grams, so neither (Meters,Meters) nor (Grams,Grams) matches.
    int = {:data, :"Std.Nat#Nat", [], []}
    assert {:error, {:no_matching_overload, :plus, _}} = Overload.resolve(env, :plus, [int, int], nil, cands)
  end

  test "wrong arity matches no member", %{env: env} do
    cands = plus_candidates(env)
    [key | _] = cands
    [d | _] = domains(env, key)
    assert {:error, {:no_matching_overload, :plus, _}} = Overload.resolve(env, :plus, [d], nil, cands)
  end
end
