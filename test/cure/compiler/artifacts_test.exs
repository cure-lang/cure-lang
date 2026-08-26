defmodule Cure.Compiler.ArtifactsTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Artifacts, BuildManifest}
  alias Cure.Compiler.Artifacts.Lock

  setup do
    root = Path.join(System.tmp_dir!(), "cure_artifacts_#{System.unique_integer([:positive])}")
    File.mkdir_p!(root)
    on_exit(fn -> File.rm_rf!(root) end)
    %{root: root}
  end

  test "records and verifies BEAM bytes, identity, exports, and provenance", %{root: root} do
    write_beam!(root, :"Cure.Sample", %{producer_snapshot: <<1>>})

    assert {:ok, artifact} = Artifacts.record("Cure.Sample.beam", root)
    assert artifact.module == "Cure.Sample"
    assert artifact.provenance.producer_snapshot == <<1>>
    assert Artifacts.verify_artifact(artifact, root) == []

    assert :ok =
             Artifacts.verify_binary_against(
               File.read!(Path.join(root, "Cure.Sample.beam")),
               artifact
             )

    File.write!(Path.join(root, "Cure.Sample.beam"), "not a beam")
    assert Artifacts.verify_artifact(artifact, root) == [:beam_unreadable]
  end

  test "a same-name older BEAM is rejected by content", %{root: root} do
    write_beam!(root, :"Cure.Std.Semigroup", %{producer_snapshot: <<1>>}, [{:combine, 2}])
    {:ok, expected} = Artifacts.record("Cure.Std.Semigroup.beam", root)

    write_beam!(root, :"Cure.Std.Semigroup", %{producer_snapshot: <<0>>}, [])

    reasons = Artifacts.verify_artifact(expected, root)
    assert :artifact_hash_mismatch in reasons
    assert :exports_hash_mismatch in reasons
    assert :provenance_mismatch in reasons
  end

  test "a current BEAM paired with an older artifact record is rejected", %{root: root} do
    write_beam!(root, :"Cure.Pairing", %{producer_snapshot: <<1>>}, [{:old, 0}])
    {:ok, old_record} = Artifacts.record("Cure.Pairing.beam", root)

    write_beam!(root, :"Cure.Pairing", %{producer_snapshot: <<2>>}, [{:current, 0}])

    reasons = Artifacts.verify_artifact(old_record, root)
    assert :artifact_hash_mismatch in reasons
    assert :exports_hash_mismatch in reasons
    assert :provenance_mismatch in reasons
    assert :producer_snapshot_mismatch in reasons
  end

  test "a self-consistent manifest with false artifact metadata is rejected", %{root: root} do
    write_beam!(root, :"Cure.FalseRecord", %{producer_snapshot: <<1>>})
    {:ok, artifact} = Artifacts.record("Cure.FalseRecord.beam", root)

    false_artifact = %{artifact | sha256: <<0::256>>, size: artifact.size + 1}
    save_set!(root, :project, <<1>>, "FalseRecord", false_artifact)

    assert {:error, {:artifact_set_invalid, %{modules: %{"FalseRecord" => reasons}}}} =
             Artifacts.open_verified_set(root)

    assert :artifact_hash_mismatch in reasons
    assert :artifact_size_mismatch in reasons
  end

  test "zero-byte, random, and truncated BEAMs are rejected", %{root: root} do
    write_beam!(root, :"Cure.Corruptible", %{producer_snapshot: <<1>>})
    path = Path.join(root, "Cure.Corruptible.beam")
    original = File.read!(path)
    {:ok, expected} = Artifacts.record("Cure.Corruptible.beam", root)

    for corrupt <- [<<>>, :crypto.strong_rand_bytes(32), binary_part(original, 0, div(byte_size(original), 2))] do
      File.write!(path, corrupt)
      assert Artifacts.verify_artifact(expected, root) == [:beam_unreadable]
    end
  end

  test "same-size corruption with a restored mtime is not hidden by the sweep cache", %{root: root} do
    write_beam!(root, :"Cure.CacheProbe", %{producer_snapshot: <<1>>}, [{:old, 0}])
    path = Path.join(root, "Cure.CacheProbe.beam")
    original_mtime = File.stat!(path, time: :posix).mtime

    {:ok, expected} = Artifacts.with_cache(fn -> Artifacts.record("Cure.CacheProbe.beam", root) end)
    write_beam!(root, :"Cure.CacheProbe", %{producer_snapshot: <<2>>}, [{:new, 0}])
    assert File.stat!(path).size == expected.size
    File.touch!(path, original_mtime)

    Artifacts.with_cache(fn ->
      reasons = Artifacts.verify_artifact(expected, root)
      assert :artifact_hash_mismatch in reasons
      assert :provenance_mismatch in reasons
    end)
  end

  test "stable pre-fence stat signatures reuse hashes while full verification always reads bytes",
       %{root: root} do
    write_beam!(root, :"Cure.StatCache", %{producer_snapshot: <<1>>})
    {:ok, expected} = Artifacts.record("Cure.StatCache.beam", root, verification: :full)
    fence = max(expected.stat.mtime, expected.stat.ctime) + 1

    {cached_reasons, cached_stats} =
      Artifacts.with_cache(fn ->
        reasons =
          Artifacts.verify_artifact(expected, root,
            verification: :cached,
            validated_at: fence
          )

        {reasons, Artifacts.hash_stats()}
      end)

    assert cached_reasons == []
    assert cached_stats.reused == 1
    assert cached_stats.computed == 0

    {full_reasons, full_stats} =
      Artifacts.with_cache(fn ->
        reasons = Artifacts.verify_artifact(expected, root, verification: :full)
        {reasons, Artifacts.hash_stats()}
      end)

    assert full_reasons == []
    assert full_stats.reused == 0
    assert full_stats.computed == 1
  end

  test "a timestamp at the filesystem fence is deliberately rehashed", %{root: root} do
    write_beam!(root, :"Cure.TimestampFence", %{producer_snapshot: <<1>>})
    {:ok, expected} = Artifacts.record("Cure.TimestampFence.beam", root)
    fence = max(expected.stat.mtime, expected.stat.ctime)

    {_reasons, stats} =
      Artifacts.with_cache(fn ->
        reasons =
          Artifacts.verify_artifact(expected, root,
            verification: :cached,
            validated_at: fence
          )

        {reasons, Artifacts.hash_stats()}
      end)

    assert stats.computed == 1
    assert stats.reused == 0
  end

  test "whole-set verification rejects orphaned and multiply-owned artifacts", %{root: root} do
    write_beam!(root, :"Cure.One", %{producer_snapshot: <<1>>})
    write_beam!(root, :"Cure.Orphan", %{producer_snapshot: <<1>>})
    {:ok, artifact} = Artifacts.record("Cure.One.beam", root)

    manifest =
      manifest(root, :project, <<1>>, %{
        "One" => entry(artifact),
        "DuplicateOwner" => entry(artifact)
      })

    assert {:error, details} = Artifacts.verify_manifest(manifest, root)
    assert details.orphans == ["Cure.Orphan.beam"]
    assert details.duplicate_ownership == ["Cure.One.beam"]
  end

  test "swapped same-set BEAMs fail identity and content checks", %{root: root} do
    write_beam!(root, :"Cure.Left", %{producer_snapshot: <<1>>})
    write_beam!(root, :"Cure.Right", %{producer_snapshot: <<1>>})
    {:ok, left} = Artifacts.record("Cure.Left.beam", root)
    {:ok, right} = Artifacts.record("Cure.Right.beam", root)

    left_bytes = File.read!(Path.join(root, left.path))
    right_bytes = File.read!(Path.join(root, right.path))
    File.write!(Path.join(root, left.path), right_bytes)
    File.write!(Path.join(root, right.path), left_bytes)

    assert :beam_module_mismatch in Artifacts.verify_artifact(left, root)
    assert :artifact_hash_mismatch in Artifacts.verify_artifact(right, root)
  end

  test "path traversal and a false manifest root are rejected", %{root: root} do
    assert Artifacts.verify_artifact(%{path: "../outside.beam"}, root) ==
             [:artifact_path_invalid]

    manifest = manifest(root, :project, <<1>>, %{})

    refute BuildManifest.valid_digest?(%{manifest | kind: :stdlib})
  end

  test "a self-consistent but malformed module entry fails closed", %{root: root} do
    malformed = manifest(root, :project, <<1>>, %{"Broken" => :not_an_entry})

    BuildManifest.save(malformed, root)

    assert {:error, :manifest_invalid} = Artifacts.open_verified_set(root)
  end

  test "a manifest entry missing its recorded lifted BEAM is rejected", %{root: root} do
    write_beam!(root, :"Cure.Parent", %{producer_snapshot: <<1>>})
    {:ok, parent} = Artifacts.record("Cure.Parent.beam", root)

    missing =
      parent
      |> Map.put(:path, "Cure.Parent.Lifted.beam")
      |> Map.put(:module, "Cure.Parent.Lifted")

    manifest =
      manifest(root, :project, <<1>>, %{
        "Parent" => %{entry(parent) | artifacts: [parent, missing]}
      })

    assert {:error, %{modules: %{"Parent" => reasons}}} =
             Artifacts.verify_manifest(manifest, root)

    assert :beam_missing in reasons
  end

  test "exact in-memory verification rejects bytes from another valid artifact", %{root: root} do
    write_beam!(root, :"Cure.Expected", %{producer_snapshot: <<1>>})
    write_beam!(root, :"Cure.Other", %{producer_snapshot: <<1>>})
    {:ok, expected} = Artifacts.record("Cure.Expected.beam", root)
    other = File.read!(Path.join(root, "Cure.Other.beam"))

    assert {:error, reasons} = Artifacts.verify_binary_against(other, expected)
    assert :beam_module_mismatch in reasons
    assert :artifact_hash_mismatch in reasons
  end

  test "verified candidate selection skips an invalid first directory", %{root: root} do
    invalid = Path.join(root, "invalid")
    valid = Path.join(root, "valid")
    File.mkdir_p!(invalid)
    File.mkdir_p!(valid)
    write_beam!(invalid, :"Cure.Bad", %{producer_snapshot: <<0>>})
    write_beam!(valid, :"Cure.Good", %{producer_snapshot: <<1>>})

    {:ok, artifact} = Artifacts.record("Cure.Good.beam", valid)

    BuildManifest.save(manifest(valid, :stdlib, <<1>>, %{"Good" => entry(artifact)}), valid)

    assert {:ok, manifest} =
             Artifacts.open_verified_set(kind: :stdlib, candidates: [invalid, valid])

    assert manifest.artifact_root == Path.expand(valid)
  end

  test "two valid candidate generations select the first complete set without mixing", %{root: root} do
    first = Path.join(root, "first")
    second = Path.join(root, "second")
    File.mkdir_p!(first)
    File.mkdir_p!(second)

    write_beam!(first, :"Cure.First", %{producer_snapshot: <<1>>})
    write_beam!(second, :"Cure.Second", %{producer_snapshot: <<2>>})
    {:ok, first_artifact} = Artifacts.record("Cure.First.beam", first)
    {:ok, second_artifact} = Artifacts.record("Cure.Second.beam", second)
    save_set!(first, :stdlib, <<1>>, "First", first_artifact)
    save_set!(second, :stdlib, <<2>>, "Second", second_artifact)

    assert {:ok, manifest} =
             Artifacts.open_verified_set(kind: :stdlib, candidates: [first, second])

    assert manifest.artifact_root == Path.expand(first)
    assert Map.keys(manifest.modules) == ["First"]
  end

  test "read-only sweep validates without changing the published pointer", %{root: root} do
    source_root = Path.join(root, "src")
    output_root = Path.join(root, "out")
    File.mkdir_p!(source_root)
    File.write!(Path.join(source_root, "sample.cure"), "mod Sample\n  fn value() -> Int = 1\n")

    assert {:ok, repaired} =
             Artifacts.sweep(
               kind: :project,
               source_roots: [source_root],
               output_dir: output_root,
               repair: true
             )

    pointer = File.read!(Path.join(output_root, "current"))

    assert {:ok, checked} =
             Artifacts.sweep(
               kind: :project,
               source_roots: [source_root],
               output_dir: output_root,
               repair: false
             )

    assert checked.artifact_digest == repaired.artifact_digest
    assert File.read!(Path.join(output_root, "current")) == pointer
  end

  test "a verified stdlib generation can be copied into a flat OTP ebin", %{root: root} do
    source = Path.join(root, "source")
    destination = Path.join(root, "release/ebin")
    File.mkdir_p!(source)
    File.mkdir_p!(destination)

    write_beam!(source, :"Cure.Std.Sample", %{producer_snapshot: <<1>>})
    {:ok, artifact} = Artifacts.record("Cure.Std.Sample.beam", source)

    BuildManifest.save(
      manifest(source, :stdlib, <<1>>, %{"Std.Sample" => entry(artifact)}),
      source
    )

    # Host-application BEAMs may share the release ebin without belonging to
    # the stdlib artifact namespace.
    write_beam!(destination, :"Cure.Compiler", %{producer_snapshot: <<9>>})

    assert {:ok, copied} = Artifacts.copy_verified_flat(source, destination)
    assert copied.artifact_root == Path.expand(destination)
    assert File.regular?(Path.join(destination, "Cure.Std.Sample.beam"))
    assert {:ok, _} = Artifacts.open_verified_set(destination)
  end

  test "a corrupted flat copy is rejected after publication bytes change", %{root: root} do
    source_root = Path.join(root, "src")
    output_root = Path.join(root, "out")
    destination = Path.join(root, "bundle")
    File.mkdir_p!(source_root)
    File.write!(Path.join(source_root, "sample.cure"), "mod Sample\n  fn value() -> Int = 1\n")

    assert {:ok, built} =
             Artifacts.sweep(
               kind: :project,
               source_roots: [source_root],
               output_dir: output_root,
               repair: true
             )

    assert {:ok, _} = Artifacts.copy_verified_flat(built.artifact_root, destination)
    File.write!(Path.join(destination, "Cure.Sample.beam"), "corrupt")

    assert {:error, {:artifact_set_invalid, _}} = Artifacts.open_verified_set(destination)
  end

  test "verified project and dependency sets merge into one release set", %{root: root} do
    project = Path.join(root, "project")
    dependency = Path.join(root, "dependency")
    release = Path.join(root, "release")
    File.mkdir_p!(project)
    File.mkdir_p!(dependency)

    write_beam!(project, :"Cure.Main", %{producer_snapshot: <<1>>, compiler_hash: <<1>>})
    write_beam!(dependency, :"Cure.Dep", %{producer_snapshot: <<2>>, compiler_hash: <<2>>})
    {:ok, main} = Artifacts.record("Cure.Main.beam", project)
    {:ok, dep} = Artifacts.record("Cure.Dep.beam", dependency)
    save_set!(project, :project, <<1>>, "Main", main)
    save_set!(dependency, :dependency, <<2>>, "Dep", dep)

    assert {:ok, merged} =
             Artifacts.merge_verified_flat([project, dependency], release,
               kind: :release,
               package_artifact_digests: %{"dep" => <<2>>}
             )

    assert merged.kind == :release
    assert Enum.sort(Map.keys(merged.modules)) == ["Dep", "Main"]
    assert get_in(merged.modules, ["Main", :artifacts, Access.at(0), :provenance, :compiler_hash]) == <<1>>
    assert get_in(merged.modules, ["Dep", :artifacts, Access.at(0), :provenance, :compiler_hash]) == <<2>>
    assert File.regular?(Path.join(release, "Cure.Dep.beam"))
  end

  test "a held writer lock records its intended generation", %{root: root} do
    lock_path = Path.join(root, ".cure_artifact.lock")

    assert :ok =
             Lock.with_lock(root, fn ->
               assert :ok = Lock.set_intended_generation(<<1, 2, 3>>)
               owner = lock_path |> File.read!() |> :erlang.binary_to_term([:safe])
               assert owner.intended_generation == <<1, 2, 3>>
               assert owner.output_root == root
               :ok
             end)
  end

  test "the kernel releases an artifact lock when its BEAM owner dies", %{root: root} do
    parent = self()

    owner =
      Task.async(fn ->
        Lock.with_lock(root, fn ->
          send(parent, :artifact_lock_held)
          Process.sleep(:infinity)
        end)
      end)

    assert_receive :artifact_lock_held, 2_000
    Task.shutdown(owner, :brutal_kill)

    assert :recovered = Lock.with_lock(root, fn -> :recovered end)
  end

  @tag timeout: 20_000
  test "a contender reports the owner and waits beyond the former ten-second cutoff", %{root: root} do
    parent = self()

    owner =
      Task.async(fn ->
        Lock.with_lock(root, fn ->
          :ok = Lock.set_intended_generation(<<1, 2, 3>>)
          send(parent, :artifact_lock_held)

          receive do
            :release_artifact_lock -> :released
          end
        end)
      end)

    assert_receive :artifact_lock_held, 2_000

    log =
      ExUnit.CaptureLog.capture_log(fn ->
        contender = Task.async(fn -> Lock.with_lock(root, fn -> :acquired end) end)

        assert Task.yield(contender, 10_500) == nil
        send(owner.pid, :release_artifact_lock)
        assert Task.await(owner, 2_000) == :released
        assert Task.await(contender, 2_000) == :acquired
      end)

    assert log =~ "another Cure compiler (OS PID #{System.pid()})"
    assert log =~ "waiting for generation <<1, 2, 3>> to finish"
  end

  defp entry(artifact) do
    %{
      source: %{
        path: "sample.cure",
        sha256: <<1>>,
        stat: %{device: nil, inode: 1, size: 1, mtime: 1, ctime: 1}
      },
      warning_count: 0,
      interface_hash: <<2>>,
      edges: %{compile_order: [], interface: [], runtime: []},
      artifacts: [artifact]
    }
  end

  defp save_set!(root, kind, workspace_key, name, artifact) do
    BuildManifest.save(manifest(root, kind, workspace_key, %{name => entry(artifact)}), root)
  end

  defp manifest(root, kind, workspace_key, modules) do
    producer_snapshot =
      modules
      |> Map.values()
      |> Enum.flat_map(fn
        %{artifacts: artifacts} -> artifacts
        _ -> []
      end)
      |> List.first()
      |> then(fn
        nil -> nil
        artifact -> artifact.producer_snapshot
      end)

    compiler_hash =
      modules
      |> Map.values()
      |> Enum.flat_map(fn
        %{artifacts: artifacts} -> artifacts
        _ -> []
      end)
      |> List.first()
      |> then(fn
        nil -> <<1>>
        artifact -> artifact.provenance.compiler_hash
      end)

    BuildManifest.seal(%{
      version: 3,
      kind: kind,
      workspace_key: workspace_key,
      input_snapshot: producer_snapshot,
      artifact_digest: nil,
      validated_at: Artifacts.filesystem_timestamp(root),
      context: %{compiler_hash: compiler_hash},
      dependencies: %{stdlib: nil, packages: %{}},
      expected_modules: modules |> Map.keys() |> Enum.sort(),
      modules: modules
    })
  end

  defp write_beam!(root, module, provenance, exports \\ [{:run, 0}]) do
    provenance =
      Map.merge(
        %{
          module: Atom.to_string(module),
          source_hash: <<1>>,
          compiler_hash: <<1>>
        },
        provenance
      )

    functions =
      Enum.map(exports, fn {name, arity} ->
        arguments = for index <- 1..arity//1, do: {:var, 1, :"X#{index}"}
        {:function, 1, name, arity, [{:clause, 1, arguments, [], [{:atom, 1, :ok}]}]}
      end)

    forms = [
      {:attribute, 1, :module, module},
      {:attribute, 1, :export, exports},
      {:attribute, 1, :cure_artifact, [provenance]}
      | functions
    ]

    result = :compile.forms(forms, [:return, :binary])

    {:ok, ^module, binary} =
      case result do
        {:ok, ^module, binary, _warnings} -> {:ok, module, binary}
        {:ok, ^module, binary} -> {:ok, module, binary}
      end

    File.write!(Path.join(root, "#{module}.beam"), binary)
  end
end
