defmodule Cure.Compiler.BuildManifestTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.BuildManifest, as: M

  setup do
    dir = Path.join(System.tmp_dir!(), "cure_manifest_test_#{:erlang.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    {:ok, dir: dir}
  end

  test "load/1 on an empty dir returns an empty manifest", %{dir: dir} do
    m = M.load(dir)
    assert m.version == 3
    assert m.modules == %{}
    assert m.input_snapshot == nil
  end

  test "save/1 then load/1 round-trips", %{dir: dir} do
    m = %{
      version: 3,
      workspace_key: <<1, 2, 3>>,
      input_snapshot: <<4, 5>>,
      artifact_digest: nil,
      validated_at: 10,
      kind: :stdlib,
      context: %{compiler_hash: <<1, 2, 3>>},
      dependencies: %{stdlib: nil, packages: %{}},
      expected_modules: ["Std.List"],
      modules: %{
        "Std.List" => %{
          source: %{
            path: "lib/std/list.cure",
            sha256: <<9>>,
            stat: %{device: nil, inode: 1, size: 1, mtime: 1, ctime: 1}
          },
          interface_hash: <<8>>,
          warning_count: 0,
          edges: %{compile_order: ["Std.Core"], interface: ["Std.Core"], runtime: ["Std.Core"]},
          artifacts: [
            %{
              path: "Cure.Std.List.beam",
              module: "Cure.Std.List",
              sha256: <<7>>,
              size: 1,
              stat: %{device: nil, inode: 2, size: 1, mtime: 1, ctime: 1},
              exports_hash: <<6>>,
              provenance: %{},
              provenance_hash: <<5>>,
              producer_snapshot: <<4, 5>>
            }
          ]
        }
      }
    }

    assert :ok = M.save(m, dir)
    loaded = M.load(dir)
    assert loaded == M.seal(m)
    assert M.valid_digest?(loaded)
  end

  test "version 2 is deliberately stale", %{dir: dir} do
    File.write!(
      Path.join(dir, ".cure_manifest"),
      :erlang.term_to_binary(%{version: 2, workspace_key: <<7>>, modules: %{}})
    )

    assert {:error, :manifest_version_unsupported} = M.read(dir)
    assert M.load(dir).modules == %{}
  end

  test "load/1 on a corrupt manifest returns empty, never raises", %{dir: dir} do
    File.write!(Path.join(dir, ".cure_manifest"), "not a term <<<")
    assert M.load(dir).modules == %{}
  end

  test "load/1 on a wrong-version manifest returns empty", %{dir: dir} do
    File.write!(Path.join(dir, ".cure_manifest"), :erlang.term_to_binary(%{version: 999, toolchain: "", modules: %{}}))
    assert M.load(dir).modules == %{}
  end

  test "save/1 is atomic — no .tmp file is left behind", %{dir: dir} do
    assert :ok = M.save(M.empty(<<0>>), dir)
    refute File.exists?(Path.join(dir, ".cure_manifest.tmp"))
  end

  test "toolchain_fingerprint/0 is a stable 32-byte digest" do
    a = M.toolchain_fingerprint()
    b = M.toolchain_fingerprint()
    assert byte_size(a) == 32
    assert a == b
  end

  test "toolchain fingerprint includes every application beam" do
    assert M.semantic_toolchain_beam?("/tmp/Elixir.Cure.Diagnostic.Adapter.Name.beam")
    assert M.semantic_toolchain_beam?("/tmp/Elixir.Cure.CLI.beam")
    assert M.semantic_toolchain_beam?("/tmp/Elixir.Antigen.Cover.beam")
    assert M.semantic_toolchain_beam?("/tmp/Elixir.Mix.Tasks.Cure.Compile.beam")
  end

  test "artifact fingerprint retains semantic compiler beams" do
    assert M.semantic_toolchain_beam?("/tmp/Elixir.Cure.Compiler.beam")
    assert M.semantic_toolchain_beam?("/tmp/Elixir.Cure.Core.Kernel.beam")
    assert M.semantic_toolchain_beam?("/tmp/Elixir.Cure.Elab.Program.beam")
    assert M.semantic_toolchain_beam?("/tmp/Elixir.Cure.Project.beam")
  end
end
