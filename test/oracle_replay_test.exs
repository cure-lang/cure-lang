defmodule OracleReplayTest do
  @moduledoc """
  Offline replay of the differential oracle (design spec §7). Needs no Idris
  toolchain: it asserts Cure's *current* verdicts against the committed
  fixtures and enforces the relation contract. Fixtures are regenerated with
  `mix cure.oracle` (live mode).
  """
  use ExUnit.Case, async: true
  alias Cure.Oracle

  test "there is at least one oracle cluster to replay" do
    assert Oracle.clusters() != [], "no clusters under test/oracle/ — corpus missing"
  end

  for cluster <- Cure.Oracle.clusters() do
    describe "oracle cluster: #{cluster}" do
      @cluster cluster

      test "fixture keys match the paired files exactly" do
        fixture_keys = @cluster |> Oracle.read_fixture() |> Map.keys() |> MapSet.new()
        pair_keys = @cluster |> Oracle.pairs() |> Enum.map(& &1.name) |> MapSet.new()
        assert fixture_keys == pair_keys
      end

      test "every pair has its .idr sibling, Cure's live verdict matches the fixture, and the relation holds" do
        fixture = Oracle.read_fixture(@cluster)

        for %{name: name, cure_path: cp, idr_path: ip} <- Oracle.pairs(@cluster) do
          entry = Map.fetch!(fixture, name)
          assert File.exists?(ip), "missing paired .idr for #{@cluster}/#{name}"

          assert Atom.to_string(Oracle.cure_verdict(cp)) == entry["cure"],
                 "Cure verdict drifted for #{@cluster}/#{name} — regenerate with `mix cure.oracle #{@cluster}`"

          assert Oracle.consistent(entry) == :ok,
                 "relation contract violated for #{@cluster}/#{name}: #{inspect(entry)}"
        end
      end
    end
  end
end
