defmodule Cure.Diagnostic.MissingModuleTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Errors, ModuleManifest}
  alias Cure.Diagnostic.{Adapter, Host, Renderer, SourceRegistry}
  alias Cure.Diagnostic.Adapter.Name, as: NameAdapter

  @moduletag :tmp_dir

  # The manifest reports a dependency it cannot resolve as a bare tuple. That
  # tuple used to reach `Cure.Diagnostic.UnhandledError` and surface as
  # `E101 INTERNAL COMPILER ERROR`, although it is an ordinary authoring
  # failure: a mistyped `use`, or a sibling file left out of the compile set.

  defp missing(path, line, overrides \\ %{}) do
    {:missing_module,
     Map.merge(
       %{
         requester: {"root", "Pool.Demo"},
         target: {"root", "Pool.Core"},
         kind: :use_import,
         span: %{path: path, line: line},
         candidates: ["Pool.Demo", "Pool.Core", "Pool.WorkerFsm"]
       },
       overrides
     )}
  end

  describe "the name adapter" do
    test "reports an unknown module as E091 in the module namespace" do
      diagnostic = NameAdapter.from_error(missing("lib/demo.cure", 2, %{candidates: []}))

      assert diagnostic.code == "E091"
      assert diagnostic.key == :unknown_name
      assert diagnostic.title == "Unknown module"
      assert diagnostic.payload.namespace == :module
      assert diagnostic.payload.name == "Pool.Core"
      assert diagnostic.payload.kind == :missing_module
      assert diagnostic.payload.requester == "Pool.Demo"
      assert diagnostic.payload.dependency_kind == :use_import
    end

    test "the public adapter routes both tuple shapes instead of raising UnhandledError" do
      assert Adapter.from_error(missing("lib/demo.cure", 2)) == NameAdapter.from_error(missing("lib/demo.cure", 2))

      exported =
        {:package_module_not_exported,
         %{
           requester: {"consumer", "Consumer"},
           target: {"dep", "Dep.Hidden"},
           kind: :qualified_reference,
           span: %{path: "lib/consumer.cure", line: 2}
         }}

      assert Adapter.from_error(exported) == NameAdapter.from_error(exported)
    end

    test "words the cause by how the module was reached" do
      for {kind, phrase} <- [
            use_import: "imports `Pool.Core` with `use`",
            qualified_reference: "refers to `Pool.Core` by its qualified name",
            prelude_symbol_use: "relies on `Pool.Core` as an ambient prelude provider"
          ] do
        diagnostic = NameAdapter.from_error(missing("lib/demo.cure", 2, %{kind: kind}))
        assert Renderer.plain(diagnostic, SourceRegistry.new()) =~ phrase
      end
    end

    test "labels the module name on its own line when the origin is the registered source" do
      source = "mod Pool.Demo\n  use Pool.Core\n  fn run() -> Int = 1\n"
      registry = SourceRegistry.new() |> SourceRegistry.register("lib/demo.cure", source, "lib/demo.cure")

      diagnostic =
        NameAdapter.from_error(
          missing(Path.expand("lib/demo.cure"), 2, %{candidates: []}),
          source_registry: registry,
          source_file: "lib/demo.cure"
        )

      assert diagnostic.primary.span.start_line == 2
      assert diagnostic.primary.span.start_column == 7
      assert diagnostic.primary.span.end_column == 16

      assert Renderer.plain(diagnostic, registry, width: 100) =~ """
             at lib/demo.cure:2:7
             2 |   use Pool.Core
               |       ^^^^^^^^^ `Pool.Core` is not part of this compilation
             """
    end

    test "does not match the module as part of a longer name" do
      source = "mod Pool.Demo\n  use Pool.CoreExtra\n  use Other.Pool.Core\n  use Pool.Core.Sub\n"
      registry = SourceRegistry.new() |> SourceRegistry.register("lib/demo.cure", source, "lib/demo.cure")
      opts = [source_registry: registry, source_file: "lib/demo.cure"]
      path = Path.expand("lib/demo.cure")

      # `Pool.CoreExtra` and `Other.Pool.Core` are different names.
      for line <- [2, 3] do
        assert NameAdapter.from_error(missing(path, line, %{candidates: []}), opts).primary == nil
      end

      # `Pool.Core` is a whole qualifier of `Pool.Core.Sub`.
      assert %{span: %{start_column: 7, end_column: 16}} =
               NameAdapter.from_error(missing(path, 4, %{candidates: []}), opts).primary
    end

    test "stays locationless rather than blaming an unrelated source" do
      source = "mod Unrelated\n  fn complete() -> Int = 1\nend\n"
      registry = SourceRegistry.new() |> SourceRegistry.register("lib/unrelated.cure", source, "lib/unrelated.cure")
      opts = [source_registry: registry, source_file: "lib/unrelated.cure"]

      # Another file's dependency: a snippet of this buffer would be wrong.
      other_file = NameAdapter.from_error(missing(Path.expand("lib/demo.cure"), 2), opts)
      assert other_file.primary == nil
      assert Renderer.plain(other_file, registry) =~ "Required at lib/demo.cure:2."

      # The ambient prelude provider is attributed to line 1 without being
      # written anywhere in the source.
      ambient =
        NameAdapter.from_error(
          missing(Path.expand("lib/unrelated.cure"), 1, %{kind: :prelude_symbol_use}),
          opts
        )

      assert ambient.primary == nil

      refute Renderer.plain(ambient, registry) =~ "1 | mod Unrelated"
    end

    test "offers a never-automatic correction for a near-miss spelling" do
      source = "mod Pool.Demo\n  use Pool.Cor\n"
      registry = SourceRegistry.new() |> SourceRegistry.register("lib/demo.cure", source, "lib/demo.cure")

      diagnostic =
        NameAdapter.from_error(
          missing(Path.expand("lib/demo.cure"), 2, %{
            target: {"root", "Pool.Cor"},
            candidates: ["Pool.Demo", "Pool.Core", "Std.List"]
          }),
          source_registry: registry,
          source_file: "lib/demo.cure"
        )

      assert [suggestion] = diagnostic.suggestions
      assert suggestion.message =~ "Did you mean `Pool.Core`?"
      # A guess is not a safe rewrite: the author may mean a file not yet written.
      assert suggestion.applicability == :maybe_incorrect
      assert [%{replacement: "Pool.Core", span: span}] = suggestion.edits
      assert span.start_column == 7
    end

    test "never suggests the requester or the missing module itself" do
      diagnostic =
        NameAdapter.from_error(missing("lib/demo.cure", 2, %{candidates: ["Pool.Demo", "Pool.Core"]}))

      assert diagnostic.payload.candidates == []
    end

    test "falls back to guidance about the compile set when nothing is close" do
      diagnostic = NameAdapter.from_error(missing("lib/demo.cure", 2, %{candidates: ["Std.List", "Std.Map"]}))

      assert [suggestion] = diagnostic.suggestions
      assert suggestion.applicability == :manual
      assert suggestion.message =~ "compile the project directory"
      assert suggestion.edits == []
    end

    test "a module outside a package's export surface is private, not missing" do
      diagnostic =
        NameAdapter.from_error(
          {:package_module_not_exported,
           %{
             requester: {"consumer", "Consumer"},
             target: {"dep", "Dep.Hidden"},
             kind: :qualified_reference,
             span: %{path: "lib/consumer.cure", line: 2}
           }}
        )

      assert diagnostic.code == "E091"
      assert diagnostic.title == "Module `Dep.Hidden` is not exported by `dep`"
      assert diagnostic.payload.kind == :package_module_not_exported
      assert diagnostic.payload.package == "dep"
      assert [%{applicability: :manual}] = diagnostic.suggestions
    end
  end

  describe "through the presentation boundary" do
    test "Host.render no longer reports an internal compiler error", %{tmp_dir: dir} do
      path = Path.join(dir, "demo.cure")
      source = "mod Pool.Demo\n  use Pool.Core\n  fn run() -> Int = 1\n"
      File.write!(path, source)

      rendered = Host.render(missing(path, 2), path)

      assert rendered =~ "[E091]"
      assert rendered =~ "UNKNOWN MODULE"
      assert rendered =~ "`Pool.Demo` imports `Pool.Core` with `use`"
      assert rendered =~ "use Pool.Core"
      refute rendered =~ "INTERNAL COMPILER ERROR"
      refute rendered =~ "E101"
      refute rendered =~ "unregistered_diagnostic"
    end

    test "Errors.to_diagnostic attaches the span from the registered source", %{tmp_dir: dir} do
      path = Path.join(dir, "demo.cure")
      source = "mod Pool.Demo\n  use Pool.Core\n"
      File.write!(path, source)

      {diagnostic, _registry} = Errors.to_diagnostic(missing(path, 2), path, source)

      assert diagnostic.code == "E091"
      assert diagnostic.primary.span.start_line == 2
    end
  end

  describe "end to end from the manifest" do
    test "a missing `use` is attributed to the line that wrote it", %{tmp_dir: dir} do
      path = Path.join(dir, "demo.cure")
      File.write!(path, "mod Pool.Demo\n\n  use Pool.Core\n  fn run() -> Int = 1\n")

      assert {:error, {:missing_module, details} = error} =
               ModuleManifest.build([path], package: "root")

      # Not line 1: a `use` node carries its position as source info, and the
      # harvester used to read only a `:line` key that is never set.
      assert details.span == %{path: path, line: 3}
      assert details.kind == :use_import
      assert details.target == {"root", "Pool.Core"}
      assert "Pool.Demo" in details.candidates

      rendered = Host.render(error, path)
      assert rendered =~ "[E091]"
      assert rendered =~ "3 |   use Pool.Core"
      refute rendered =~ "INTERNAL COMPILER ERROR"
    end

    test "a mistyped `use` suggests the module that is in the compile set", %{tmp_dir: dir} do
      core = Path.join(dir, "pool_core.cure")
      demo = Path.join(dir, "demo.cure")
      File.write!(core, "mod Pool.Core\n  fn answer() -> Int = 42\n")
      File.write!(demo, "mod Pool.Demo\n  use Pool.Cor\n")

      assert {:error, {:missing_module, %{target: {"root", "Pool.Cor"}}} = error} =
               ModuleManifest.build([core, demo], package: "root")

      rendered = Host.render(error, demo)
      assert rendered =~ "Did you mean `Pool.Core`?"
      refute rendered =~ "INTERNAL COMPILER ERROR"
    end
  end
end
