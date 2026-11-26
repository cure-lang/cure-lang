defmodule Cure.Core.FamilyLevelCeilingTest do
  @moduledoc """
  Family sorts are unbounded canonical finite levels, not legacy integers.
  Removing the old ceiling must preserve predicativity of constructor fields.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive, Kernel, Sort}

  defp check(level) do
    fam = Inductive.family(:Foo, [], [], level)
    Kernel.check_family(Env.empty(), fam)
  end

  test "families at arbitrary finite levels are accepted" do
    assert :ok == check(Sort.finite_closed(37))
    assert :ok == check(Sort.finite_closed(10 ** 40))
  end

  test "legacy integer family sorts are not implicitly converted" do
    assert {:error, _} = check(2)
    assert {:error, _} = check(3)
  end

  test "a Type37 constructor field needs a family at least at level 38" do
    ctor = Inductive.ctor(:ContainsType, [{:a, {:type, Sort.finite_closed(37)}}], [])
    small = Inductive.family(:Foo, [], [], Sort.finite_closed(37))
    large = Inductive.family(:Foo, [], [], Sort.finite_closed(38))
    env = Inductive.declare(Env.empty(), small, [])

    assert :ok = Kernel.check_family(env, small)
    assert {:error, :universe_level} = Kernel.check_ctor(env, small, ctor)
    assert :ok = Kernel.check_ctor(env, large, ctor)
  end
end
