defmodule Cure.Compiler.UniverseIdentityTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Artifacts, BuildManifest, ModuleInterface}
  alias Cure.Core.{Certificate, Env, SCCCertificate, TotalityCertificate, UniverseCodec}
  alias Cure.Elab.TotalityGraph

  @module Cure.UniverseIdentityFixture

  test "interface schema and semantic identity reject old unchanged-source interfaces" do
    interface =
      ModuleInterface.new(
        module_name: "Identity",
        source_path: "/identity.cure",
        source_hash: "same"
      )

    assert 9 = ModuleInterface.schema_version()
    assert :ok = ModuleInterface.validate(interface)

    assert {:error, {:module_interface_schema_incompatible, 8, 9}} =
             ModuleInterface.validate(%{interface | schema_version: 8})

    refute ModuleInterface.semantic_hash(:same) == legacy_hash(:same)
    assert ModuleInterface.semantic_hash(:same) == UniverseCodec.semantic_hash(:same)
    assert byte_size(BuildManifest.toolchain_fingerprint()) == 32
  end

  test "warm direct summaries authenticate both universe identity and checker version" do
    body = {:atom_lit, :ok}
    env = Env.empty()
    summary = Certificate.direct_summary(:fixture, body, env)
    assert 7 = Certificate.summary_version()
    assert summary.universe_identity == UniverseCodec.identity()
    assert Certificate.cached_summary_valid?(summary, :fixture, body, env)

    refute Certificate.cached_summary_valid?(
             Map.delete(summary, :universe_identity),
             :fixture,
             body,
             env
           )

    refute Certificate.cached_summary_valid?(%{summary | version: 6}, :fixture, body, env)

    refute Certificate.cached_summary_valid?(
             %{summary | universe_identity: :obsolete},
             :fixture,
             body,
             env
           )

    refute Certificate.body_hash(body) == legacy_hash(body)
  end

  test "partition and closure verifiers refuse a mutually consistent obsolete summary identity" do
    body = {:atom_lit, :ok}
    env = Env.add_def(Env.empty(), :fixture, {:atom_type}, body)
    summary = Certificate.direct_summary(:fixture, body, env)
    env = Env.put_direct_call_summary(env, :fixture, summary)
    partition = TotalityGraph.propose_partition(env, [:fixture])
    closure = Cure.Elab.TotalityCertificate.propose(env, [:fixture])
    assert {:ok, [[:fixture]]} = SCCCertificate.verify_partition(env, partition)
    assert {:ok, :total} = TotalityCertificate.verify(env, [:fixture], closure)

    stale = Env.put_direct_call_summary(env, :fixture, Map.delete(summary, :universe_identity))
    assert {:error, {:totality_summary_stale, _}} = SCCCertificate.verify_partition(stale, partition)

    assert {:error, {:totality_derivation_invalid, %{reason: :summary_checker_mismatch}}} =
             TotalityCertificate.verify(stale, [:fixture], closure)
  end

  @tag :tmp_dir
  test "self-consistent obsolete artifacts refuse cold, warm and restarted verification", %{
    tmp_dir: root
  } do
    for {label, identity} <- [current: UniverseCodec.identity(), old: :fixed_ceiling] do
      dir = Path.join(root, Atom.to_string(label))
      File.mkdir_p!(dir)
      {binary, path} = beam(dir, identity)
      assert {:ok, record} = Artifacts.record(path, dir)
      expected = if label == :current, do: :ok, else: {:error, :universe_identity_mismatch}
      assert Artifacts.verify_binary(binary, @module) == expected

      Artifacts.with_cache(fn ->
        if label == :current do
          assert :ok = Artifacts.verify_binary_against(binary, record)
          assert [] = Artifacts.verify_artifact(record, dir)
          assert [] = Artifacts.verify_artifact(record, dir)
        else
          assert {:error, [:universe_identity_mismatch]} =
                   Artifacts.verify_binary_against(binary, record)

          assert [:universe_identity_mismatch] = Artifacts.verify_artifact(record, dir)
          assert [:universe_identity_mismatch] = Artifacts.verify_artifact(record, dir)
        end
      end)

      # A genuinely fresh OS VM re-runs the public byte/provenance verifier.
      code_paths = :code.get_path() |> Enum.flat_map(fn path -> ["-pa", List.to_string(path)] end)

      script =
        "binary = File.read!(hd(System.argv())); result = Cure.Compiler.Artifacts.verify_binary(binary, Cure.UniverseIdentityFixture); IO.inspect(result)"

      {output, 0} =
        System.cmd(System.find_executable("elixir"), code_paths ++ ["-e", script, "--", path])

      assert String.trim(output) == inspect(expected)
    end
  end

  defp beam(root, identity) do
    provenance = %{format: 1, universe_identity: identity}

    forms = [
      {:attribute, 1, :module, @module},
      {:attribute, 1, :export, [value: 0]},
      {:attribute, 1, :cure_artifact, [provenance]},
      {:function, 1, :value, 0, [{:clause, 1, [], [], [{:atom, 1, :ok}]}]}
    ]

    {:ok, @module, binary} = :compile.forms(forms, [:binary])
    path = Path.join(root, Atom.to_string(@module) <> ".beam")
    File.write!(path, binary)
    {binary, path}
  end

  defp legacy_hash(value),
    do: :crypto.hash(:sha256, :erlang.term_to_binary(value, [:deterministic]))
end
