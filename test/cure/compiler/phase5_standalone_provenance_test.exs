defmodule Cure.Compiler.Phase5StandaloneProvenanceTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler
  alias Cure.Compiler.Artifacts
  alias Cure.Core.UniverseCodec

  @tag :tmp_dir
  test "standalone string and file producers emit the current universe identity", %{tmp_dir: root} do
    for entry <- [:string, :file] do
      owner = "StandaloneUniverse#{entry}"
      source = "mod #{owner}\n  fn value() -> Atom = :ok\nend\n"
      output = Path.join(root, Atom.to_string(entry))
      file = Path.join(root, "#{entry}.cure")
      opts = [file: file, output_dir: output, emit_events: false]

      result =
        case entry do
          :string ->
            Compiler.compile_string(source, opts)

          :file ->
            File.write!(file, source)
            Compiler.compile_file(file, opts)
        end

      assert {:ok, module, []} = result
      path = Path.join(output, "Cure.#{owner}.beam")
      binary = File.read!(path)
      assert :ok = Artifacts.verify_binary(binary, module)
      assert {:ok, record} = Artifacts.record(path, output)
      assert record.provenance.universe_identity == UniverseCodec.identity()
      assert record.provenance.source_hash == :crypto.hash(:sha256, source)
    end
  end

  test "in-memory compilation reaches the verified loader and executes" do
    source = "mod StandaloneUniverseLoaded\n  fn value() -> Atom = :ok\nend\n"
    assert {:ok, module} = Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :value, []) == :ok
    [provenance] = module.module_info(:attributes)[:cure_artifact]
    assert provenance.universe_identity == UniverseCodec.identity()
  end

  @tag :tmp_dir
  test "caller provenance cannot replace the producer's mandatory universe identity", %{tmp_dir: root} do
    source = "mod StandaloneUniverseOverride\n  fn value() -> Atom = :ok\nend\n"

    assert {:ok, module, []} =
             Compiler.compile_string(source,
               file: Path.join(root, "override.cure"),
               output_dir: root,
               emit_events: false,
               artifact_provenance: %{universe_identity: :fixed_ceiling}
             )

    binary = File.read!(Path.join(root, "Cure.StandaloneUniverseOverride.beam"))
    assert :ok = Artifacts.verify_binary(binary, module)
    assert {:ok, record} = Artifacts.record("Cure.StandaloneUniverseOverride.beam", root)
    assert record.provenance.universe_identity == UniverseCodec.identity()
  end
end
