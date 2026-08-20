defmodule Cure.Stdlib.PackageStageTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Artifacts

  test "the embedded regex package is staged and only its public module is exported" do
    root = Application.fetch_env!(:cure, :stdlib_beam_dir)
    assert {:ok, set} = Artifacts.open_verified_set(root, verification: :full)

    assert get_in(set, [:context, :package_exports]) == %{"cure_regex" => ["Std.Regex"]}
    assert Map.has_key?(set.modules, "Std.Regex")
    assert Map.has_key?(set.modules, "Std.Regex.Core")
    assert File.regular?(Path.join(set.artifact_root, "Std.Regex.cureinterface"))
    assert File.regular?(Path.join(set.artifact_root, "Std.Regex.Core.cureinterface"))
  end
end
