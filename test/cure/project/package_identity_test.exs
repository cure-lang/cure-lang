defmodule Cure.Project.PackageIdentityTest do
  use ExUnit.Case, async: true

  @moduletag :tmp_dir

  test "dependency artifacts retain the dependency package identity", %{tmp_dir: root} do
    dependency = Path.join(root, "dependency")
    consumer = Path.join(root, "consumer")
    File.mkdir_p!(Path.join(dependency, "lib"))
    File.mkdir_p!(consumer)

    File.write!(
      Path.join(dependency, "Cure.toml"),
      """
      [project]
      name = "cure_fixture_dependency"
      version = "0.1.0"
      edition = "2026"

      [exports]
      modules = ["Fixture.Provider"]
      """
    )

    File.write!(
      Path.join(dependency, "lib/provider.cure"),
      "mod Fixture.Provider\n  fn value() -> Int = 41\n"
    )

    project = %Cure.Project{
      name: "consumer",
      root: consumer,
      dependencies: [%{name: "cure_fixture_dependency", path: dependency}]
    }

    assert :ok = Cure.Project.resolve_deps(project)

    output_dir = Path.join(consumer, "_build/deps/cure_fixture_dependency")
    assert {:ok, artifacts} = Cure.Compiler.Artifacts.open_verified_set(output_dir)
    assert artifacts.context.package_exports == %{
             "cure_fixture_dependency" => ["Fixture.Provider"]
           }
    interface_path = Path.join(artifacts.artifact_root, "Fixture.Provider.cureinterface")
    assert {:ok, interface} = Cure.Compiler.ModulePipeline.Interface.read(interface_path)
    assert interface.source_metadata.package == "cure_fixture_dependency"
  end
end
