defmodule Cure.Project.CompileProjectTest do
  use ExUnit.Case, async: false

  defp setup_project(tmp, files) do
    File.mkdir_p!(Path.join(tmp, "lib"))

    Enum.each(files, fn {rel_path, contents} ->
      target = Path.join(tmp, rel_path)
      File.mkdir_p!(Path.dirname(target))
      File.write!(target, contents)
    end)
  end

  describe "[application] / [release] TOML parsing" do
    @tag :tmp_dir
    test "parses arrays of strings, booleans, ints, and nested env maps", %{tmp_dir: tmp} do
      File.write!(Path.join(tmp, "Cure.toml"), """
      [project]
      name = "demo"
      version = "0.4.2"

      [application]
      name           = "demo"
      vsn            = "0.4.2"
      applications   = ["logger", "crypto"]
      start_phases   = ["init", "warm_cache"]

      [application.env]
      port = 4000
      enabled = true

      [release]
      name         = "demo"
      vsn          = "0.4.2"
      include_erts = false
      applications = ["logger"]
      """)

      {:ok, project} = Cure.Project.load(tmp)
      assert project.application.name == "demo"
      assert project.application.applications == ["logger", "crypto"]
      assert project.application.start_phases == ["init", "warm_cache"]
      assert project.application.env["port"] == 4000
      assert project.application.env["enabled"] == true

      assert project.release.name == "demo"
      assert project.release.include_erts == false
      assert project.release.applications == ["logger"]
    end
  end

  describe "Cure.Project.detect_app/2" do
    @tag :tmp_dir
    test "returns nil when no application macro exists", %{tmp_dir: tmp} do
      setup_project(tmp, [
        {"Cure.toml", "[project]\nname = \"demo\"\nversion = \"0.1.0\"\n"},
        {"lib/lib.cure", "mod Demo\n  fn hello() -> Atom = :ok\n"}
      ])

      {:ok, project} = Cure.Project.load(tmp)
      files = Path.wildcard(Path.join(tmp, "lib/**/*.cure"))
      assert {:ok, nil} = Cure.Project.detect_app(files, project)
    end
  end

  describe "[compiler] stdlib_path parsing" do
    @tag :tmp_dir
    test "parses stdlib_path as a string value", %{tmp_dir: tmp} do
      File.write!(Path.join(tmp, "Cure.toml"), """
      [project]
      name = "demo"
      version = "0.1.0"

      [compiler]
      type_check = false
      stdlib_path = "/opt/cure/ebin"
      """)

      {:ok, project} = Cure.Project.load(tmp)
      assert Cure.Project.stdlib_path(project) == "/opt/cure/ebin"
    end

    @tag :tmp_dir
    test "stdlib_path returns nil when not set and CURE_LIB is unset", %{tmp_dir: tmp} do
      previous = System.get_env("CURE_LIB")

      try do
        System.delete_env("CURE_LIB")

        File.write!(Path.join(tmp, "Cure.toml"), """
        [project]
        name = "demo"
        version = "0.1.0"

        [compiler]
        type_check = false
        """)

        {:ok, project} = Cure.Project.load(tmp)
        assert Cure.Project.stdlib_path(project) == nil
      after
        case previous do
          nil -> System.delete_env("CURE_LIB")
          val -> System.put_env("CURE_LIB", val)
        end
      end
    end

    @tag :tmp_dir
    test "stdlib_path falls back to CURE_LIB when not set in toml", %{tmp_dir: tmp} do
      previous = System.get_env("CURE_LIB")

      try do
        System.put_env("CURE_LIB", "/fallback/ebin")

        File.write!(Path.join(tmp, "Cure.toml"), """
        [project]
        name = "demo"
        version = "0.1.0"

        [compiler]
        type_check = false
        """)

        {:ok, project} = Cure.Project.load(tmp)
        assert Cure.Project.stdlib_path(project) == "/fallback/ebin"
      after
        case previous do
          nil -> System.delete_env("CURE_LIB")
          val -> System.put_env("CURE_LIB", val)
        end
      end
    end
  end

  describe "missing stdlib module error" do
    test "use Std.Nonexistent produces :missing_stdlib_module error" do
      source = """
      mod Broken
        use Std.Nonexistent

        fn hello() -> Atom = :ok
      """

      assert {:error, {:codegen_error, {:missing_stdlib_module, :"Cure.Std.Nonexistent", _msg}}} =
               Cure.Compiler.compile_and_load(source, emit_events: false, check_types: false)
    end
  end

  describe "dependency artifact preflight" do
    @tag :tmp_dir
    test "reports an unbuilt path dependency before scanning consumer modules", %{tmp_dir: tmp} do
      dependency = Path.join(tmp, "dependency")
      consumer = Path.join(tmp, "consumer")
      File.mkdir_p!(dependency)
      File.mkdir_p!(consumer)

      File.write!(Path.join(consumer, "Cure.toml"), """
      [project]
      name = "consumer"
      version = "0.1.0"

      [dependencies]
      sample = { path = "../dependency" }
      """)

      assert {:ok, project} = Cure.Project.load(consumer)

      assert {:error, {:dependency_artifact_set_missing, {:package, "sample"}}} =
               Cure.Project.dependency_artifact_sets(project)
    end

    test "missing dependency artifacts render an actionable non-ICE diagnostic" do
      {diagnostic, _registry} =
        Cure.Diagnostic.Host.to_diagnostic(
          {:dependency_artifact_set_missing, {:package, "sample"}},
          "Cure.toml",
          ""
        )

      assert diagnostic.code == "E100"
      assert diagnostic.key == :artifact_error
      assert Cure.Diagnostic.message(diagnostic) =~ "cure deps"
      refute diagnostic.code == "E101"
    end
  end
end
