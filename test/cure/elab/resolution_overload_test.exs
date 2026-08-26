defmodule Cure.Elab.ResolutionOverloadTest do
  use ExUnit.Case, async: true
  alias Cure.Core.Env
  alias Cure.Elab.Resolution

  # A minimal env with two overload members of `plus` owned by "M" and a single
  # `solo`, plus one import "M".
  defp env_with_overloads do
    %{Env.empty() | module_owner: "M", import_modules: MapSet.new(["M"])}
    |> put_def(:"M#plus~0")
    |> put_def(:"M#plus~1")
    |> put_def(:"M#solo")
  end

  defp put_def(env, key) do
    %{env | defs: Map.put(env.defs, key, %{name: key, type: {:type, 0}, body: {:hole, "x"}, quantities: nil})}
  end

  test "overload_candidates returns every member of a set, most-specific-owner first" do
    env = env_with_overloads()
    assert Enum.sort(Resolution.overload_candidates(env, :plus)) == [:"M#plus~0", :"M#plus~1"]
  end

  test "overload_candidates returns the single provider for a non-overloaded name" do
    assert Resolution.overload_candidates(env_with_overloads(), :solo) == [:"M#solo"]
  end

  test "overload_candidates returns [] for an unknown name" do
    assert Resolution.overload_candidates(env_with_overloads(), :nope) == []
  end

  test "provider index follows immutable table versions without stale candidates" do
    env = env_with_overloads()

    assert Enum.sort(Resolution.overload_candidates(env, :plus)) == [:"M#plus~0", :"M#plus~1"]

    extended = put_def(env, :"M#plus~2")

    assert Enum.sort(Resolution.overload_candidates(extended, :plus)) == [
             :"M#plus~0",
             :"M#plus~1",
             :"M#plus~2"
           ]

    assert Enum.sort(Resolution.overload_candidates(env, :plus)) == [:"M#plus~0", :"M#plus~1"]
  end

  test "ambiguous_modules still finds an overloaded name's owner (structural recovery)" do
    # A bare unapplied reference must still surface an actionable owner list,
    # never a silent :none. (Same owner twice collapses to one entry.)
    assert Resolution.ambiguous_modules(env_with_overloads(), :plus) == ["M"]
  end
end
