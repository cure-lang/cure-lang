defmodule Cure.Elab.CheckedModuleTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler
  alias Cure.Compiler.{Artifacts, ModuleInterface}
  alias Cure.Elab.{CheckedModule, Program}

  setup do
    root = Path.join(System.tmp_dir!(), "cure_checked_module_#{System.unique_integer([:positive])}")
    File.mkdir_p!(root)
    on_exit(fn -> File.rm_rf!(root) end)
    {:ok, root: root}
  end

  test "one certified environment supplies codegen locals and the canonical interface", %{root: root} do
    path = Path.join(root, "sample.cure")

    source = """
    mod Checked.Sample
      fn answer() -> Int = 42
    """

    File.write!(path, source)
    assert {:ok, ast} = Compiler.parse_source(source, file: path)

    assert {:ok,
            %CheckedModule{
              ast: ^ast,
              env: env,
              interface: %ModuleInterface{} = interface,
              module_name: "Checked.Sample",
              source_path: source_path,
              source_hash: source_hash,
              local_defs: local_defs
            }} = Program.check_ast_artifact(ast, source: source, file: path)

    assert source_path == Path.expand(path)
    assert source_hash == :crypto.hash(:sha256, source)
    assert interface.source_hash == source_hash
    assert interface.owned_env == env
    assert interface.export_env.defs[:"Checked.Sample#answer"] == env.defs[:"Checked.Sample#answer"]
    assert :"Checked.Sample#answer" in local_defs

    assert {:ok, independently_loaded} = Program.module_interface("Checked.Sample", path)
    assert independently_loaded == interface
    assert independently_loaded.schema_version == ModuleInterface.schema_version()
  end

  test "compile_file_with_artifact checks an entry module once and reuses that artifact", %{root: root} do
    path = Path.join(root, "once.cure")
    output_dir = Path.join(root, "ebin")

    File.write!(path, """
    mod Checked.Once
      fn value() -> Int = 1
    """)

    Process.put(:cure_elaboration_observer, self())

    on_exit(fn ->
      Process.delete(:cure_elaboration_observer)
    end)

    assert {:ok, _module, [], %CheckedModule{interface: %ModuleInterface{}}} =
             Compiler.compile_file_with_artifact(path,
               output_dir: output_dir,
               emit_events: false,
               source_roots: [root]
             )

    events = drain_elaboration_events([])

    assert Enum.count(
             events,
             &match?({:checked, :entry, "Checked.Once", ^path}, &1)
           ) == 1

    refute Enum.any?(events, &match?({:checked, :interface, "Checked.Once", ^path}, &1))
  end

  test "incremental staging hashes the emitted artifact without a second elaboration", %{root: root} do
    path = Path.join(root, "incremental.cure")
    output_dir = Path.join(root, "ebin")

    File.write!(path, """
    mod Checked.Incremental
      fn value() -> Int = 1
    """)

    owner = self()
    progress = fn event -> send(owner, {:pipeline, event}) end

    assert {:ok, result} =
             Artifacts.sweep(
               source_paths: [path],
               source_roots: [root],
               output_dir: output_dir,
               kind: :project,
               progress: progress,
               compile_opts: [emit_events: false]
             )

    assert Map.keys(result.rebuilt) == ["Checked.Incremental"]
    assert result.errors == []

    assert_receive {:pipeline, {:compile_started, "Checked.Incremental", ^path}}
    refute_receive {:pipeline, {:compile_started, "Checked.Incremental", ^path}}
  end

  defp drain_elaboration_events(acc) do
    receive do
      {:cure_elaboration, event} -> drain_elaboration_events([event | acc])
    after
      0 -> Enum.reverse(acc)
    end
  end
end
