defmodule Cure.Project.PackageExportsManifestTest do
  use ExUnit.Case, async: true

  @moduletag :tmp_dir

  test "a package manifest records its explicit module export surface", %{tmp_dir: dir} do
    File.write!(
      Path.join(dir, "Cure.toml"),
      """
      [project]
      name = "cure_regex"
      version = "0.1.0"
      edition = "2026"

      [exports]
      modules = ["Std.Regex"]
      """
    )

    assert {:ok, project} = Cure.Project.load(dir)
    assert project.exports == %{modules: ["Std.Regex"]}
  end
end
