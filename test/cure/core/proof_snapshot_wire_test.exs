defmodule Cure.Core.ProofSnapshotWireTest do
  @moduledoc """
  Producer vectors and audit-boundary regressions. These are not universal
  extraction proofs; Agda independently checks the generated full bundle.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Env, Inductive, ProofSnapshotWire}
  alias Cure.Test.{ProofBundleFixture, ProofSnapshotFixture}

  @artifact Path.expand("../../..", __DIR__) <> "/proof/Fixtures/ExecutableBundle.agda"

  test "the empty registry has a fixed full-source vector without implicit empty-name interning" do
    # [18, [[], [[], []]]]: a tag wrapper and right-nested field products.
    assert {:ok, characters} = ProofSnapshotWire.encode(Env.empty(), [])
    assert characters == "(" <> String.duplicate("1", 18) <> ";(()(()())))"
  end

  test "the generated complete source and certificate artifact is reproducible" do
    assert {:ok, generated} = ProofBundleFixture.to_agda()
    assert generated == File.read!(@artifact)
  end

  test "capture exclusions are preserved rather than converted to empty metadata" do
    env = ProofSnapshotFixture.environment()

    assert {:error, %{reason: :unsupported_builtins}} =
             ProofSnapshotWire.encode(
               Inductive.register_builtin(env, :any, :"Boundary#Packed"),
               ProofBundleFixture.table()
             )

    assert {:error, %{reason: :malformed_environment}} =
             ProofSnapshotWire.encode(%{}, ProofBundleFixture.table())

    assert {:error, %{reason: :unsupported_opaque_family}} =
             ProofSnapshotWire.encode(
               Inductive.declare(env, Inductive.opaque_family(:Carrier, [], 0), []),
               ProofBundleFixture.table()
             )
  end

  test "complete malformed name tables fail even for an empty source" do
    for table <- [42, ["" | :improper], ["", 42], ["", <<255>>]] do
      assert {:error, {:malformed_table, ^table}} = ProofSnapshotWire.encode(Env.empty(), table)
    end
  end

  test "unknown declaration and telescope names cannot be omitted" do
    env = ProofSnapshotFixture.environment()
    assert {:error, {:unknown_name, "Boundary#Packed"}} = ProofSnapshotWire.encode(env, [""])

    assert {:error, {:unknown_name, "A"}} =
             ProofSnapshotWire.encode(env, ["", "Boundary#Packed"])
  end

  test "map order is canonicalized by the existing capture audit" do
    env = ProofSnapshotFixture.environment()

    reversed = %{
      env
      | defs: env.defs |> Enum.reverse() |> Map.new(),
        families: env.families |> Enum.reverse() |> Map.new(),
        ctors: env.ctors |> Enum.reverse() |> Map.new()
    }

    assert ProofSnapshotWire.encode(env, ProofBundleFixture.table()) ==
             ProofSnapshotWire.encode(reversed, ProofBundleFixture.table())
  end

  test "raw hidden bodies and separate certification flags affect the bytes" do
    env = ProofSnapshotFixture.environment()
    hidden_changed = put_in(env.defs[:"Boundary#held"][:body], {:atom_lit, :payload})
    total_only = %{env | certified: MapSet.new()}
    assert {:ok, original} = ProofSnapshotWire.encode(env, ProofBundleFixture.table())
    assert {:ok, changed} = ProofSnapshotWire.encode(hidden_changed, ProofBundleFixture.table())
    assert {:ok, flags} = ProofSnapshotWire.encode(total_only, ProofBundleFixture.table())
    refute original == changed
    refute original == flags
  end
end
