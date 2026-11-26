defmodule Cure.Core.Phase5RuntimeBaselineTest do
  @moduledoc """
  Literal emitted-backend/ABI/execution comparison against committed pre-migration
  evidence. This file is outside the ignored fixture tree intentionally.
  """
  use ExUnit.Case, async: false

  alias Cure.Test.Phase5RuntimeBaseline, as: Baseline

  setup_all do
    actual = Baseline.capture()
    frozen = Baseline.read!()
    {:ok, actual: actual, frozen: frozen}
  end

  test "ordinary emitted computational forms, exports and executions are unchanged", context do
    assert Baseline.runtime_payload(context.actual) == Baseline.runtime_payload(context.frozen)

    assert Baseline.bytes(Baseline.runtime_payload(context.actual)) ==
             Baseline.bytes(Baseline.runtime_payload(context.frozen))
  end

  test "capture is reproducible without stripping metadata or changing module names", context do
    assert Baseline.bytes(Baseline.capture()) == Baseline.bytes(context.actual)
  end

  test "literal and arity mutations are detected", context do
    assert :ok = Baseline.assert_mutation_sensitive!(context.frozen)
    assert :ok = Baseline.assert_mutation_sensitive!(context.actual)
  end

  test "frozen payload and exact fixture source identities match their manifest", context do
    manifest =
      Baseline.root()
      |> Path.join("manifest.json")
      |> File.read!()
      |> :json.decode()

    assert manifest["head"] == "722ee355665fdac39b3d954fd95e9ae7f7c4b9bd"
    assert Baseline.digest(context.frozen) == manifest["payload_sha256"]

    for {file, expected_hash} <- manifest["sources"] do
      source = File.read!(Path.join(Baseline.root(), file))
      assert Base.encode16(:crypto.hash(:sha256, source), case: :lower) == expected_hash
    end
  end
end
