defmodule Cure.Core.ProofContextTest do
  @moduledoc """
  Bounded context observation controls, not universal semantic refinement.
  The generated artifact and native coherence are checked separately by Agda.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Env, Grade, ProofContext}
  alias Cure.Test.{ProofBundleFixture, ProofContextFixture}

  @artifact Path.expand("../../..", __DIR__) <> "/proof/Fixtures/ExecutableContext.agda"

  test "the actual Context/Quote observation artifact is reproducible" do
    assert {:ok, generated} = ProofContextFixture.to_agda()
    assert generated == File.read!(@artifact)
  end

  test "dependent aliases and literal lets remain actual values after later extension" do
    {_operations, ctx} = ProofContextFixture.profile()
    assert {:ok, captured} = ProofContext.capture(ctx, ProofBundleFixture.table())
    assert captured.size == 6

    assert [
             {:neutral, 5},
             {:atom, "payload"},
             {:neutral, 3},
             {:neutral, 1},
             {:neutral, 1},
             {:neutral, 0}
           ] = captured.environment

    assert [_, _, _, _, _, _] = captured.types
    assert [_, _, _, _, _, _] = captured.grades
    refute Context.env(ctx) == Context.neutral_env(6)
  end

  test "all parallel lengths and grades must be valid before quoting" do
    {_operations, ctx} = ProofContextFixture.profile()

    for changed <- [
          %{ctx | length: -1},
          %{ctx | length: 6.0},
          %{ctx | types: []},
          %{ctx | env: []},
          %{ctx | grades: []},
          %{ctx | types: [{:vatom_type} | :improper]},
          %{ctx | grades: [:unknown, :erased, :linear, :affine, :unrestricted, :unrestricted]}
        ] do
      assert {:error, :malformed_context} = ProofContext.capture(changed, ProofBundleFixture.table())
    end
  end

  test "escaped levels never become negative indices or saturating zero" do
    assert {:error, {:escaped_level, _, 0}} = ProofContext.value({:vneutral, {:nvar, 0}}, 0)
    assert {:error, {:escaped_level, _, 1}} = ProofContext.value({:vneutral, {:nvar, 1}}, 1)
    assert {:error, {:unsupported_context_value, _}} = ProofContext.value({:vneutral, {:nvar, -1}}, 1)

    ctx = Context.extend_def(Context.empty(), {:vatom_type}, {:vneutral, {:nvar, 1}})
    assert {:error, {:escaped_level, _, 1}} = ProofContext.capture(ctx, [""])
  end

  test "closures, cases, effects and other values are excluded before evaluation" do
    for value <- [
          {:vlam, Grade.unrestricted(), {:vatom_type}, {:closure, [], {:var, 0}}},
          {:vpi, Grade.unrestricted(), {:vatom_type}, {:closure, [], {:var, 0}}},
          {:vneutral, {:napp, {:nvar, 0}, {:vatom, :payload}}},
          {:vdata, :Carrier, []},
          {:vctor, :Constructor, []},
          {:veffect_pure, {:vatom, :payload}},
          {:vfloat, 0.5}
        ] do
      assert {:error, {:unsupported_context_value, ^value}} = ProofContext.value(value, 1)
    end
  end

  test "tables and signatures are audited even for an empty context" do
    for table <- [42, ["" | :improper], ["", 42], ["", <<255>>]] do
      assert {:error, {:malformed_table, ^table}} = ProofContext.capture(Context.empty(), table)
    end

    assert {:error, :malformed_context} = ProofContext.capture(%{}, [])
    assert {:error, %{reason: :malformed_environment}} = ProofContext.capture(%Context{}, [])
    assert {:ok, %{size: 0, types: [], grades: [], environment: []}} = ProofContext.capture(Context.empty(), [])
  end

  test "missing literal names propagate as producer errors" do
    {_operations, ctx} = ProofContextFixture.profile()
    assert {:error, {:unknown_name, "payload"}} = ProofContext.capture(ctx, [""])
  end

  test "capture success does not assert coherent native typing" do
    ctx =
      Env.empty()
      |> Context.empty()
      |> Context.extend_def({:vtype, 0}, {:vatom_type})
      |> Context.extend({:vneutral, {:nvar, 0}})

    # A scoped invented neutral at a defined slot is structurally readable.
    # The corresponding Agda control passes kind construction but fails the
    # native substitution image checker.
    assert {:ok, _observations} = ProofContext.capture(ctx, [""])
  end
end
