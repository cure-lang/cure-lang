defmodule Cure.Compiler.CanonicalArtifactSweepTest do
  use ExUnit.Case, async: false

  @moduletag :tmp_dir

  test "artifact repair publishes a reversed universe through the canonical pipeline", %{tmp_dir: dir} do
    source_root = Path.join(dir, "src")
    output_root = Path.join(dir, "out")
    File.mkdir_p!(source_root)

    provider = Path.join(source_root, "z_provider.cure")
    consumer = Path.join(source_root, "a_consumer.cure")

    File.write!(provider, "mod Sweep.Provider\n  fn value() -> Int = 41\n")

    File.write!(
      consumer,
      "mod Sweep.Consumer\n  use Sweep.Provider\n  fn result() -> Int = value() + 1\n"
    )

    sweep = fn ->
      Cure.Compiler.Artifacts.sweep(
        module_pipeline: :canonical,
        package: "fixture",
        kind: :project,
        source_paths: [consumer, provider],
        source_roots: [source_root],
        output_dir: output_root,
        repair: true
      )
    end

    assert {:ok, result} = sweep.()

    assert result.pipeline == :canonical
    assert Map.keys(result.rebuilt) == ["Sweep.Consumer", "Sweep.Provider"]

    assert {:ok, published} = Cure.Compiler.Artifacts.open_verified_set(result.artifact_root)
    assert Map.keys(published.modules) == ["Sweep.Consumer", "Sweep.Provider"]

    assert {:ok, provider_interface} =
             Cure.Compiler.ModulePipeline.interface_path(result.artifact_root, "Sweep.Provider")

    assert File.regular?(provider_interface)

    assert {:ok, warm} = sweep.()
    assert warm.pipeline == :canonical
    assert warm.rebuilt == %{}
    assert warm.reused == ["Sweep.Consumer", "Sweep.Provider"]
    assert warm.artifact_digest == result.artifact_digest

    File.write!(provider, "mod Sweep.Provider\n  fn value() -> Int = 42\n")

    assert {:ok, body_only} = sweep.()
    assert Map.keys(body_only.rebuilt) == ["Sweep.Consumer", "Sweep.Provider"]
    assert body_only.reused == []

    {:ok, current} = Cure.Compiler.Artifacts.open_verified_set(body_only.artifact_root)
    File.write!(Path.join(current.artifact_root, "Cure.Sweep.Consumer.beam"), "corrupt")

    assert {:ok, recovered} = sweep.()
    assert Map.keys(recovered.rebuilt) == ["Sweep.Consumer", "Sweep.Provider"]
    assert recovered.reused == []
    assert {:ok, _verified} = Cure.Compiler.Artifacts.open_verified_set(recovered.artifact_root)
  end

  test "a verified dependency generation supplies canonical interfaces to a project sweep", %{tmp_dir: dir} do
    dependency_source = Path.join(dir, "dependency/src")
    dependency_output = Path.join(dir, "dependency/out")
    project_source = Path.join(dir, "project/src")
    project_output = Path.join(dir, "project/out")
    File.mkdir_p!(dependency_source)
    File.mkdir_p!(project_source)

    dependency = Path.join(dependency_source, "provider.cure")
    project = Path.join(project_source, "consumer.cure")
    File.write!(dependency, "mod Package.Provider\n  fn value() -> Int = 41\n")
    File.write!(project, "mod Package.Consumer\n  fn result() -> Int = Package.Provider.value() + 1\n")

    assert {:ok, dependency_result} =
             Cure.Compiler.Artifacts.sweep(
               module_pipeline: :canonical,
               package: "dependency",
               kind: :dependency,
               source_roots: [dependency_source],
               output_dir: dependency_output,
               repair: true
             )

    assert {:ok, dependency_set} =
             Cure.Compiler.Artifacts.open_verified_set(dependency_result.artifact_root)

    assert {:ok, project_result} =
             Cure.Compiler.Artifacts.sweep(
               module_pipeline: :canonical,
               package: "project",
               kind: :project,
               source_roots: [project_source],
               output_dir: project_output,
               repair: true,
               package_artifact_sets: [{"dependency", dependency_set}],
               package_artifact_digests: %{"dependency" => dependency_set.artifact_digest}
             )

    assert project_result.pipeline == :canonical
    assert Map.keys(project_result.rebuilt) == ["Package.Consumer"]

    assert {:ok, project_set} = Cure.Compiler.Artifacts.open_verified_set(project_result.artifact_root)
    assert Map.keys(project_set.modules) == ["Package.Consumer"]
  end

  test "canonical sweep cycles retain the closed source-hop diagnostic contract", %{tmp_dir: dir} do
    source_root = Path.join(dir, "cycle/src")
    output_root = Path.join(dir, "cycle/out")
    File.mkdir_p!(source_root)

    left = Path.join(source_root, "left.cure")
    right = Path.join(source_root, "right.cure")
    File.write!(left, "mod Cycle.Left\n  use Cycle.Right\n  fn left() -> Int = Cycle.Right.right()\n")
    File.write!(right, "mod Cycle.Right\n  use Cycle.Left\n  fn right() -> Int = 1\n")

    assert {:ok, result} =
             Cure.Compiler.Artifacts.sweep(
               module_pipeline: :canonical,
               package: "cycle",
               kind: :project,
               source_roots: [source_root],
               output_dir: output_root,
               repair: true
             )

    assert [hops] = result.cycles
    assert hd(hops).module == List.last(hops).module

    assert Enum.all?(
             hops,
             &match?(
               %{module: module, path: path, line: line}
               when is_binary(module) and is_binary(path) and is_integer(line),
               &1
             )
           )

    {diagnostic, _registry} = Cure.Compiler.Errors.to_diagnostic({:import_cycle, hops}, left, File.read!(left))
    assert diagnostic.code == "W086"
  end
end
