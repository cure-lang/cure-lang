defmodule Cure.Compiler.PackageExportVisibilityTest do
  use ExUnit.Case, async: false

  @moduletag :tmp_dir

  test "a consumer cannot resolve a bundled module outside the package export surface", %{tmp_dir: dir} do
    dependency_source = Path.join(dir, "dependency")
    consumer_source = Path.join(dir, "consumer")
    interface_root = Path.join(dir, "interfaces")
    File.mkdir_p!(dependency_source)
    File.mkdir_p!(consumer_source)

    public =
      write!(
        dependency_source,
        "public.cure",
        "mod Fixture.Public\n  fn value() -> Int = 41\n"
      )

    hidden =
      write!(
        dependency_source,
        "hidden.cure",
        "mod Fixture.Hidden\n  fn secret() -> Int = 42\n"
      )

    assert {:ok, dependency} =
             Cure.Compiler.ModulePipeline.check([public, hidden],
               module_pipeline: :canonical,
               package: "cure_fixture_dependency",
               source_roots: [dependency_source]
             )

    assert :ok = Cure.Compiler.ModulePipeline.write_interfaces(dependency, interface_root)

    consumer =
      write!(
        consumer_source,
        "consumer.cure",
        "mod Consumer\n  fn value() -> Int = Fixture.Hidden.secret()\n"
      )

    assert {:error, {:package_module_not_exported, %{target: {"cure_fixture_dependency", "Fixture.Hidden"}}}} =
             Cure.Compiler.ModulePipeline.check([consumer],
               module_pipeline: :canonical,
               package: "consumer",
               source_roots: [consumer_source],
               interface_roots: [interface_root],
               package_exports: %{
                 "cure_fixture_dependency" => ["Fixture.Public"]
               }
             )
  end

  defp write!(dir, name, source) do
    path = Path.join(dir, name)
    File.write!(path, source)
    path
  end
end
