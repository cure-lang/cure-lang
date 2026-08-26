defmodule Cure.Compiler.ModulePipeline.Emission do
  @moduledoc """
  BEAM bytecode for the modules a checked run holds.

  A checked run already owns everything emission needs: `body_envs` is the
  elaborated Core env per module, and the module's AST names which definitions
  that module OWNS. Emission is therefore a projection of a finished check, not
  a second compile — nothing here re-elaborates, re-resolves, or re-reads
  source, so a beam cannot disagree with the interface published beside it.

  Modules are emitted in a deterministic order and the first failure stops the
  run, carrying the module it belongs to. A run that cannot emit one of its own
  modules has not produced a generation, so failing here means nothing is
  published at all.
  """

  alias Cure.Compiler.{Artifacts, BeamWriter, BuildManifest, ModuleInterface, ModuleManifest}
  alias Cure.Core.Env
  alias Cure.Elab.{Emit, Program}

  @doc """
  Bytecode for every module in `asts`, keyed by the BEAM module atom.

  `body_envs` must hold a checked env for each identity in `asts`; a missing
  one is a broken run rather than a module with nothing to emit, so it is an
  error and not an empty beam.
  """
  @spec run(
          ModuleManifest.t(),
          %{term() => term()},
          %{term() => ModuleInterface.t()},
          %{term() => Env.t()},
          [Path.t()]
        ) ::
          {:ok, %{module() => binary()}} | {:error, term()}
  def run(%ModuleManifest{} = manifest, asts, interfaces, body_envs, artifact_roots)
      when is_map(asts) and is_map(interfaces) and is_map(body_envs) and is_list(artifact_roots) do
    producer_snapshot = producer_snapshot(manifest, interfaces)
    reusable_beams = reusable_beams(artifact_roots, manifest, interfaces)

    asts
    |> Enum.sort_by(fn {identity, _ast} -> identity end)
    |> Enum.reduce_while({:ok, %{}}, fn {identity, ast}, {:ok, emitted} ->
      case emit_module(identity, ast, manifest, interfaces, body_envs, reusable_beams, producer_snapshot) do
        {:ok, module, binary} -> {:cont, {:ok, Map.put(emitted, module, binary)}}
        {:error, _reason} = error -> {:halt, error}
      end
    end)
  end

  @doc false
  @spec reusable_beam_identities(
          [Path.t()],
          ModuleManifest.t(),
          %{term() => ModuleInterface.t()}
        ) :: MapSet.t(term())
  def reusable_beam_identities(artifact_roots, %ModuleManifest{} = manifest, interfaces)
      when is_list(artifact_roots) and is_map(interfaces) do
    artifact_roots
    |> reusable_beams(manifest, interfaces)
    |> Map.keys()
    |> MapSet.new()
  end

  defp emit_module(
         {_package, module_name} = identity,
         ast,
         manifest,
         interfaces,
         body_envs,
         reusable_beams,
         snapshot
       ) do
    with {:ok, entry} <- Map.fetch(manifest.entries, identity),
         {:ok, interface} <- Map.fetch(interfaces, identity) do
      case Map.fetch(body_envs, identity) do
        {:ok, env} ->
          provenance = provenance(module_name, entry, interface, snapshot)

          case emit(ast, env, provenance) do
            {:ok, _module, _binary} = ok -> ok
            {:error, reason} -> {:error, {:beam_emission_failed, module_name, reason}}
          end

        :error ->
          case Map.fetch(reusable_beams, identity) do
            {:ok, {module, binary}} -> {:ok, module, binary}
            :error -> {:error, {:beam_emission_input_missing, module_name}}
          end
      end
    else
      :error -> {:error, {:beam_emission_input_missing, module_name}}
    end
  end

  defp provenance(module_name, entry, interface, snapshot) do
    %{
      format: 1,
      module: module_name,
      source_path: entry.source_path,
      source_hash: entry.source_hash,
      interface_hash: interface.interface_hash,
      compiler_hash: BuildManifest.toolchain_fingerprint(),
      producer_snapshot: snapshot
    }
  end

  defp reusable_beams(roots, manifest, interfaces) do
    Enum.reduce(roots, %{}, fn root, reusable ->
      case Artifacts.open_verified_set(root, verification: :full) do
        {:ok, published} -> reusable_from_generation(published, manifest, interfaces, reusable)
        {:error, _reason} -> reusable
      end
    end)
  end

  defp reusable_from_generation(published, manifest, interfaces, reusable) do
    Enum.reduce(manifest.entries, reusable, fn {identity, entry}, reusable ->
      with false <- Map.has_key?(reusable, identity),
           {:ok, interface} <- Map.fetch(interfaces, identity),
           {:ok, artifact_entry} <- Map.fetch(published.modules, entry.module_name),
           true <- get_in(artifact_entry, [:source, :sha256]) == entry.source_hash,
           true <- artifact_entry.interface_hash == interface.interface_hash,
           [artifact] <- artifact_entry.artifacts,
           provenance when is_map(provenance) <- artifact.provenance,
           true <- provenance.interface_hash == interface.interface_hash,
           true <- provenance.compiler_hash == BuildManifest.toolchain_fingerprint(),
           path <- Path.join(published.artifact_root, artifact.path),
           {:ok, binary} <- File.read(path),
           module <- String.to_existing_atom("Cure." <> entry.module_name),
           :ok <- Artifacts.verify_binary(binary, module) do
        Map.put(reusable, identity, {module, binary})
      else
        _ -> reusable
      end
    end)
  end

  defp emit(ast, env, provenance) do
    module = Program.module_atom(ast)

    case Emit.compile_forms(env, module, Program.local_defs(ast, env), %{}, artifact_provenance: provenance) do
      {:ok, forms} -> assemble(module, forms)
      {:error, reason} -> {:error, reason}
    end
  end

  defp producer_snapshot(manifest, interfaces) do
    interface_hashes =
      interfaces
      |> Enum.map(fn {identity, interface} -> {identity, interface.interface_hash} end)
      |> Enum.sort()

    :crypto.hash(
      :sha256,
      :erlang.term_to_binary(
        %{
          compiler_hash: BuildManifest.toolchain_fingerprint(),
          manifest: ModuleManifest.semantic_dump(manifest),
          interface_hashes: interface_hashes
        },
        [:deterministic]
      )
    )
  end

  # `:compile.forms/2` derives the module name from the forms themselves. It
  # agreeing with the identity the manifest assigned is what makes a published
  # beam addressable by module atom, so it is checked rather than assumed.
  defp assemble(module, forms) do
    case BeamWriter.compile_forms(forms) do
      {:ok, ^module, binary, _warnings} -> {:ok, module, binary}
      {:ok, other, _binary, _warnings} -> {:error, {:beam_module_mismatch, module, other}}
      {:error, errors, warnings} -> {:error, {:beam_compilation_failed, errors, warnings}}
    end
  end
end
