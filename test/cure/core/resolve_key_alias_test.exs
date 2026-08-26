defmodule Cure.Core.ResolveKeyAliasTest do
  use ExUnit.Case, async: true

  alias Cure.Core.Env

  # `resolve_key/3`'s fallback — find the unique owner-qualified key whose base is
  # a bare name — answers from an index cached under the table value itself.
  #
  # These tests exist to pin the cache's whole safety argument: an index must
  # never outlive the key set it describes. They pass a table directly rather
  # than going through an elaboration, so a stale answer is visible as a wrong
  # return value instead of being masked by whatever the compiler does next.

  defp env, do: %Env{}

  describe "owner-qualified alias resolution" do
    test "a bare name resolves to the unique owner-qualified key with that base" do
      table = %{:"Std.List#map" => %{}}

      assert Env.resolve_key(env(), table, :map) == :"Std.List#map"
    end

    test "an ambiguous base does not resolve" do
      table = %{:"Std.List#map" => %{}, :"Std.Map#map" => %{}}

      assert Env.resolve_key(env(), table, :map) == :map
    end

    test "a present bare key wins over any alias scan" do
      table = %{:map => %{}, :"Std.List#map" => %{}}

      assert Env.resolve_key(env(), table, :map) == :map
    end

    test "an unknown name resolves to itself" do
      assert Env.resolve_key(env(), %{:"Std.List#map" => %{}}, :nope) == :nope
    end
  end

  describe "the alias index cannot go stale" do
    test "growing a table to an ambiguous key set changes the answer" do
      one = %{:"Std.List#map" => %{}}
      two = Map.put(one, :"Std.Map#map", %{})

      assert Env.resolve_key(env(), one, :map) == :"Std.List#map"
      # Same process, same base, table now ambiguous. A retained index would
      # still answer `Std.List#map` here.
      assert Env.resolve_key(env(), two, :map) == :map
      # And the original table must still answer for its own key set.
      assert Env.resolve_key(env(), one, :map) == :"Std.List#map"
    end

    test "shrinking a table back to unambiguous changes the answer back" do
      two = %{:"Std.List#map" => %{}, :"Std.Map#map" => %{}}
      one = Map.delete(two, :"Std.Map#map")

      assert Env.resolve_key(env(), two, :map) == :map
      assert Env.resolve_key(env(), one, :map) == :"Std.List#map"
    end

    test "a same-size key-set change is not mistaken for the old table" do
      # Neither table is a subset of the other and both have one key, so any
      # cache keyed on something coarser than the key set (a count, say) would
      # serve the first index for the second table.
      first = %{:"Std.List#map" => %{}}
      second = %{:"Std.Map#map" => %{}}

      assert Env.resolve_key(env(), first, :map) == :"Std.List#map"
      assert Env.resolve_key(env(), second, :map) == :"Std.Map#map"
    end

    test "distinct tables queried in turn do not contaminate each other" do
      defs = %{:"Std.List#map" => %{}}
      ctors = %{:"Std.Map#map" => %{}}

      for _ <- 1..3 do
        assert Env.resolve_key(env(), defs, :map) == :"Std.List#map"
        assert Env.resolve_key(env(), ctors, :map) == :"Std.Map#map"
      end
    end

    test "an evicted table is rebuilt correctly rather than answered wrongly" do
      # More live tables than the cache has slots, so the first is evicted and
      # must be rebuilt on its next query.
      tables =
        for i <- 1..24 do
          {i, %{String.to_atom("M#{i}#map") => %{}}}
        end

      for {i, table} <- tables do
        assert Env.resolve_key(env(), table, :map) == String.to_atom("M#{i}#map")
      end

      for {i, table} <- tables do
        assert Env.resolve_key(env(), table, :map) == String.to_atom("M#{i}#map"),
               "table #{i} answered wrongly after eviction"
      end
    end
  end

  describe "module ownership" do
    test "the current module's own key wins over another module's alias" do
      owned = %Env{module_owner: "Std.Map"}
      table = %{:"Std.List#map" => %{}, :"Std.Map#map" => %{}}

      assert Env.resolve_key(owned, table, :map) == :"Std.Map#map"
    end

    test "a non-atom key is never an owner-qualified alias" do
      table = %{"Std.List#map" => %{}}

      assert Env.resolve_key(env(), table, :map) == :map
    end
  end
end
