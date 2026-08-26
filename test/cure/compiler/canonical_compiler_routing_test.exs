defmodule Cure.Compiler.CanonicalCompilerRoutingTest do
  use ExUnit.Case, async: false

  @moduletag :tmp_dir

  test "compile_files defaults one reversed universe to the canonical manifest and semantic graph", %{
    tmp_dir: dir
  } do
    provider =
      write!(dir, "z_provider.cure", "mod Routed.Provider\n  fn provided() -> Int = 41\n")

    consumer =
      write!(
        dir,
        "a_consumer.cure",
        "mod Routed.Consumer\n  use Routed.Provider\n  fn result() -> Int = provided() + 1\n"
      )

    output = Path.join(dir, "ebin")

    assert {:ok, result} =
             Cure.Compiler.compile_files([consumer, provider],
               package: "fixture",
               source_roots: [dir],
               output_dir: output,
               emit_events: false
             )

    assert result.pipeline == :canonical
    assert %Cure.Compiler.ModuleManifest{} = result.manifest
    assert %Cure.Compiler.ModulePipeline.SemanticGraph{} = result.semantic_graph

    assert Enum.map(result.compiled, &elem(&1, 1)) == [
             :"Cure.Routed.Provider",
             :"Cure.Routed.Consumer"
           ]

    provider_beam = Path.join(output, "Cure.Routed.Provider.beam")
    consumer_beam = Path.join(output, "Cure.Routed.Consumer.beam")

    assert File.regular?(provider_beam)
    assert File.regular?(consumer_beam)

    assert :ok =
             provider_beam
             |> File.read!()
             |> Cure.Compiler.Artifacts.verify_binary(:"Cure.Routed.Provider")

    assert :ok =
             consumer_beam
             |> File.read!()
             |> Cure.Compiler.Artifacts.verify_binary(:"Cure.Routed.Consumer")

    assert Cure.Compiler.ModulePipeline.semantic_edge?(
             result.canonical_result,
             "Routed.Consumer",
             "Routed.Provider",
             :lexical_use
           )
  end

  test "the canonical artifact sweep owns cold and incremental compilation", %{tmp_dir: dir} do
    source = write!(dir, "incremental.cure", "mod Routed.Incremental\n  fn value() -> Int = 1\n")
    output = Path.join(dir, "incremental-ebin")

    sweep = fn ->
      Cure.Compiler.Artifacts.sweep(
        source_paths: [source],
        source_roots: [dir],
        output_dir: output,
        kind: :project,
        compile_opts: [emit_events: false]
      )
    end

    assert {:ok, first} = sweep.()

    assert first.pipeline == :canonical
    assert Map.keys(first.rebuilt) == ["Routed.Incremental"]
    assert first.reused == []
    assert first.errors == []

    assert {:ok, warm} = sweep.()

    assert warm.pipeline == :canonical
    assert warm.rebuilt == %{}
    assert warm.reused == ["Routed.Incremental"]
  end

  test "single-source compilation inherits the active canonical source roots", %{tmp_dir: dir} do
    provider =
      write!(dir, "provider.cure", "mod Routed.ContextProvider\n  fn value() -> Int = 41\n")

    previous = Process.get(:cure_source_roots)
    Process.put(:cure_source_roots, [dir])

    try do
      assert {:ok, :"Cure.Routed.ContextProvider"} =
               Cure.Compiler.compile_and_load(File.read!(provider),
                 file: provider,
                 source_roots: [dir],
                 emit_events: false
               )

      assert {:ok, :"Cure.Routed.ContextConsumer", _warnings} =
               Cure.Compiler.compile_string(
                 "mod Routed.ContextConsumer\n  use Routed.ContextProvider\n  fn result() -> Int = value() + 1\n",
                 file: "virtual/context_consumer.cure",
                 emit_events: false
               )
    after
      if previous,
        do: Process.put(:cure_source_roots, previous),
        else: Process.delete(:cure_source_roots)
    end
  end

  defp write!(dir, name, source) do
    path = Path.join(dir, name)
    File.write!(path, source)
    path
  end
end
