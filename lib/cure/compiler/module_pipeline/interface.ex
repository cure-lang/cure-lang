defmodule Cure.Compiler.ModulePipeline.Interface do
  @moduledoc false

  alias Cure.Compiler.ModuleInterface
  alias Cure.Core.{Env, Kernel}
  alias Cure.Elab.Implementation
  alias Cure.Elab.Program

  @artifact_magic "CUREIFACE\0"
  @artifact_version 1
  @extension ".cureinterface"

  @spec path(Path.t(), String.t()) :: Path.t()
  def path(root, module_name) when is_binary(root) and is_binary(module_name),
    do: Path.join(root, module_name <> @extension)

  @spec write(ModuleInterface.t(), Path.t()) :: :ok | {:error, term()}
  def write(%ModuleInterface{} = interface, root) do
    with :ok <- ModuleInterface.validate(interface),
         :ok <- File.mkdir_p(root) do
      write_to(interface, path(root, interface.module_name))
    end
  end

  @spec read(Path.t()) :: {:ok, ModuleInterface.t()} | {:error, term()}
  def read(path) when is_binary(path) do
    with {:ok, interface} <- read_unvalidated(path),
         :ok <- ModuleInterface.validate(interface) do
      {:ok, interface}
    end
  end

  @doc """
  Replace a written interface's recorded hash with one that does not describe
  its content, leaving the file's own checksum valid.

  This exists so the *semantic* rejection path can be exercised. Flipping bytes
  cannot do it: the artifact checksum catches a damaged file long before the
  interface hash is ever recomputed, so a test that corrupts bytes proves only
  that the checksum works.
  """
  @spec corrupt(Path.t(), :dependency_hash) :: :ok | {:error, term()}
  def corrupt(path, :dependency_hash) when is_binary(path) do
    with {:ok, interface} <- read_unvalidated(path) do
      write_to(%ModuleInterface{interface | interface_hash: :crypto.hash(:sha256, "not this interface")}, path)
    end
  end

  @doc "The module a written artifact claims to describe, from its filename."
  @spec module_name(Path.t()) :: String.t()
  def module_name(path) when is_binary(path), do: Path.basename(path, @extension)

  defp write_to(%ModuleInterface{} = interface, destination) do
    payload = :erlang.term_to_binary(interface, [:deterministic, compressed: 6])
    checksum = :crypto.hash(:sha256, payload)
    File.write(destination, [@artifact_magic, <<@artifact_version>>, checksum, payload], [:binary])
  end

  defp read_unvalidated(path) do
    with {:ok, <<@artifact_magic, @artifact_version, checksum::binary-size(32), payload::binary>>} <- File.read(path),
         :ok <- verify_payload_checksum(checksum, payload),
         {:ok, interface} <- decode(payload) do
      {:ok, interface}
    else
      {:ok, <<@artifact_magic, version, _::binary>>} ->
        {:error, {:interface_artifact_version_incompatible, version, @artifact_version}}

      {:ok, _} ->
        {:error, :interface_artifact_header_invalid}

      {:error, _} = error ->
        error
    end
  end

  @spec load_roots([Path.t()]) :: {:ok, %{String.t() => ModuleInterface.t()}} | {:error, term()}
  def load_roots(roots) when is_list(roots) do
    result =
      roots
      |> Enum.flat_map(&Path.wildcard(Path.join(&1, "*" <> @extension)))
      |> Enum.uniq()
      |> Enum.sort()
      |> Enum.reduce_while({:ok, %{}}, fn artifact, {:ok, interfaces} ->
        with {:ok, interface} <- read(artifact),
             :ok <- reject_duplicate_provider(interfaces, interface, artifact) do
          {:cont, {:ok, Map.put(interfaces, interface.module_name, interface)}}
        else
          {:error, reason} -> {:halt, {:error, rejection(artifact, reason)}}
        end
      end)

    with {:ok, interfaces} <- result,
         {:ok, universe} <- environment(interfaces),
         :ok <- verify_all(interfaces, universe) do
      {:ok, interfaces}
    end
  end

  defp decode(payload) do
    try do
      # Canonical Core keys include user-authored atoms (for example
      # :"Package.Module#definition"). A clean consumer VM necessarily has not
      # interned those atoms yet, so `[:safe]` cannot decode a valid compiler
      # interface. The checksum, schema/semantic hash validation, and kernel
      # verification above and below make this a checked compiler artifact,
      # analogous to loading BEAM, rather than an untrusted wire format.
      case :erlang.binary_to_term(payload) do
        %ModuleInterface{} = interface -> {:ok, interface}
        other -> {:error, {:interface_artifact_payload_invalid, other}}
      end
    rescue
      ArgumentError -> {:error, :interface_artifact_payload_invalid}
    end
  end

  # An artifact is rejected by kind, not by the shape of whatever raised. The
  # caller has to be able to tell a damaged file from a stale one from a
  # tampered one without pattern-matching on internals.
  defp rejection(artifact, reason) do
    {:invalid_interface_artifact, %{module: module_name(artifact), path: artifact, reason: classify(reason)}}
  end

  defp classify({:module_interface_hash_mismatch, _module_name, _source_path}), do: :hash_mismatch
  defp classify(:interface_artifact_checksum_mismatch), do: :checksum_mismatch
  defp classify(:interface_artifact_header_invalid), do: :header_invalid
  defp classify(:interface_artifact_payload_invalid), do: :payload_invalid
  defp classify({:interface_artifact_payload_invalid, _payload}), do: :payload_invalid
  defp classify({:interface_artifact_version_incompatible, _written, _expected}), do: :version_incompatible
  defp classify({:module_interface_schema_incompatible, _written, _expected}), do: :schema_incompatible
  defp classify({:duplicate_interface_provider, _module_name, _first, _second}), do: :duplicate_provider
  defp classify(:enoent), do: :missing
  defp classify(reason), do: reason

  defp verify_payload_checksum(checksum, payload) do
    if :crypto.hash(:sha256, payload) == checksum,
      do: :ok,
      else: {:error, :interface_artifact_checksum_mismatch}
  end

  defp reject_duplicate_provider(interfaces, interface, artifact) do
    case Map.fetch(interfaces, interface.module_name) do
      :error ->
        :ok

      {:ok, existing} ->
        if existing.interface_hash == interface.interface_hash do
          :ok
        else
          {:error, {:duplicate_interface_provider, interface.module_name, existing.source_path, artifact}}
        end
    end
  end

  @spec from_checked_env(Env.t(), Cure.Compiler.ModuleManifest.Entry.t(), String.t(), map()) ::
          ModuleInterface.t()
  def from_checked_env(%Env{} = env, entry, package, dependency_hashes \\ %{}) do
    owner = entry.module_name
    partition = Program.canonical_owned_partition(env, owner)

    owned_def_keys = partition.declarations.defs |> Map.keys() |> MapSet.new()

    declarations =
      partition.declarations
      |> Map.update!(:defs, &published_definitions/1)
      |> Map.put(:direct_call_summaries, Map.take(env.direct_call_summaries, MapSet.to_list(owned_def_keys)))
      |> Map.put(:totality_component_of, Map.take(env.totality_component_of, MapSet.to_list(owned_def_keys)))
      |> then(fn declarations ->
        component_digests = declarations.totality_component_of |> Map.values() |> Enum.uniq()
        Map.put(declarations, :totality_components, Map.take(env.totality_components, component_digests))
      end)
      |> Map.put(
        :totality_certified,
        MapSet.intersection(env.totality_certified || MapSet.new(), owned_def_keys)
      )
      |> Map.put(
        :delta_certified,
        MapSet.intersection(env.certified || MapSet.new(), owned_def_keys)
      )

    ModuleInterface.new(%{
      module_name: owner,
      source_path: entry.source_path,
      source_hash: entry.source_hash,
      dependency_interface_hashes: dependency_hashes,
      dependency_names: entry.dependencies |> Enum.map(&elem(&1.target, 1)) |> Enum.uniq() |> Enum.sort(),
      direct_edges: Enum.map(entry.dependencies, &interface_edge/1),
      canonical_declarations: declarations,
      canonical_externs: partition.externs,
      extension_payloads: Map.put(partition.extensions, :canonical_identity, {package, owner}),
      source_metadata: %{package: package, prelude_provider?: entry.prelude_provider?},
      owned_env: nil,
      export_env: nil
    })
  end

  @spec to_env(ModuleInterface.t()) :: {:ok, Env.t()} | {:error, term()}
  def to_env(%ModuleInterface{} = interface) do
    with :ok <- ModuleInterface.validate(interface) do
      declarations = interface.canonical_declarations
      extensions = interface.extension_payloads
      empty = Env.empty()

      env =
        %Env{
          empty
          | defs: Map.get(declarations, :defs, %{}),
            direct_call_summaries: Map.get(declarations, :direct_call_summaries, %{}),
            totality_components: Map.get(declarations, :totality_components, %{}),
            totality_component_of: Map.get(declarations, :totality_component_of, %{}),
            families: Map.get(declarations, :families, %{}),
            ctors: Map.get(declarations, :ctors, %{}),
            ctor_to_family: Map.get(declarations, :ctor_to_family, %{}),
            equations: Map.get(declarations, :equations, %{}),
            interfaces: %{},
            coherence: Map.get(extensions, :coherence),
            primitives: Map.get(extensions, :primitives, %{}),
            builtins: Map.get(extensions, :builtins, %{}),
            constrained: Map.get(extensions, :constrained, %{}),
            lemmas: Map.get(extensions, :lemmas, %{}),
            certified:
              MapSet.intersection(
                Map.get(declarations, :delta_certified, MapSet.new()),
                transparent_definitions(Map.get(declarations, :defs, %{}))
              ),
            totality_certified: Map.get(declarations, :totality_certified, MapSet.new()),
            module_owner: interface.module_name
        }

      {:ok, Env.with_interfaces(env, Map.get(extensions, :interfaces, %{}))}
    end
  end

  # δ-unfolding is permitted exactly where a body survived into the interface.
  # Unfolding an opaque body would expose `__interface_opaque__`, so the two
  # decisions are one decision, made here.
  defp transparent_definitions(defs) do
    for {key, %{body: body}} <- defs,
        body != nil,
        body != {:hole, "__interface_opaque__"},
        not match?({:extern, _}, body),
        into: MapSet.new(),
        do: key
  end

  @spec verify(ModuleInterface.t(), Env.t()) :: :ok | {:error, term()}
  def verify(%ModuleInterface{} = interface, %Env{} = dependencies \\ Env.empty()) do
    with {:ok, interface_env} <- to_env(interface),
         seeded = Program.canonical_base_environment(),
         {:ok, env} <- Program.merge_canonical_environments(seeded, dependencies),
         {:ok, env} <- Program.merge_canonical_environments(env, interface_env),
         :ok <- verify_families(env, interface),
         :ok <- verify_constructors(env, interface),
         :ok <- verify_definitions(env, interface) do
      :ok
    end
  end

  @spec environment(map()) :: {:ok, Env.t()} | {:error, term()}
  def environment(interfaces) when is_map(interfaces) do
    interfaces
    |> Map.values()
    |> Enum.uniq_by(&{&1.module_name, &1.interface_hash})
    |> Enum.reduce_while({:ok, Env.empty()}, fn interface, {:ok, env} ->
      with {:ok, next} <- to_env(interface),
           {:ok, merged} <- Program.merge_canonical_environments(env, next) do
        {:cont, {:ok, merged}}
      else
        {:error, reason} -> {:halt, {:error, reason}}
      end
    end)
  end

  @spec verify_all(map(), Env.t()) :: :ok | {:error, term()}
  def verify_all(interfaces, %Env{} = universe) when is_map(interfaces) do
    interfaces
    |> Map.values()
    |> Enum.uniq_by(&{&1.module_name, &1.interface_hash})
    |> Enum.reduce_while(:ok, fn interface, :ok ->
      case verify(interface, universe) do
        :ok -> {:cont, :ok}
        {:error, reason} -> {:halt, {:error, {:invalid_checked_interface, interface.module_name, reason}}}
      end
    end)
  end

  # The interface carries a body exactly where checking a published type requires
  # reducing it. A proof of `negate(negate(x)) == x` is not checkable — by its own
  # module or by any consumer — unless `negate` unfolds, so the published type is
  # what decides, not the author. Everything a published type never reaches stays
  # opaque, which is the ordinary case for runtime code.
  defp published_definitions(defs) do
    transparent = transparency_required(defs)

    Map.new(defs, fn {key, definition} ->
      {key, if(MapSet.member?(transparent, key), do: definition, else: opaque_definition(definition))}
    end)
  end

  defp transparency_required(defs) do
    seeds =
      Enum.reduce(defs, MapSet.new(), fn {key, definition}, acc ->
        acc = if Map.get(definition, :typealias), do: MapSet.put(acc, key), else: acc

        # A literal-protocol instance is machinery the ELABORATOR runs, not code the
        # program calls: `2` at `Int` is a value only because
        # `from_integer_literal`'s body normalises to one. Hiding it publishes a
        # module whose own literals stop elaborating in every consumer, reported as
        # `:literal_initializer_not_compile_time_value` at the use site rather than
        # here. Same standing as a typealias — the body IS the interface.
        acc = if Implementation.compile_time_method?(key), do: MapSet.put(acc, key), else: acc

        # `@reducible` — the author's explicit "a consumer will need this to
        # compute". Everything above is a case the compiler can infer from the
        # module alone; this is the case it cannot, because the demand comes from
        # a module that does not exist yet when this interface is frozen. Spec §9
        # (interface-first pipeline): "A declaration whose body is needed for
        # definitional equality across the edge must be explicitly marked
        # reducible/exported." Leaving it to inference would mean either
        # publishing every body — which makes the interface hash track ordinary
        # body edits and defeats incremental rebuilds — or guessing.
        acc = if Map.get(definition, :reducible), do: MapSet.put(acc, key), else: acc

        Enum.into(mentioned_globals(definition.type), acc)
      end)

    close_transparency(defs, seeds)
  end

  # Unfolding a body exposes that body, so whatever *it* mentions must unfold too.
  defp close_transparency(defs, keys) do
    next =
      Enum.reduce(keys, keys, fn key, acc ->
        case Map.fetch(defs, key) do
          {:ok, definition} -> Enum.into(mentioned_globals(definition.body), acc)
          :error -> acc
        end
      end)

    if MapSet.equal?(next, keys), do: keys, else: close_transparency(defs, next)
  end

  defp mentioned_globals({:global, key}) when is_atom(key), do: [key]
  defp mentioned_globals(term) when is_tuple(term), do: term |> Tuple.to_list() |> mentioned_globals()
  defp mentioned_globals(terms) when is_list(terms), do: Enum.flat_map(terms, &mentioned_globals/1)

  defp mentioned_globals(%{} = term) when not is_struct(term),
    do: term |> Map.to_list() |> mentioned_globals()

  defp mentioned_globals(_term), do: []

  defp opaque_definition(%{body: {:extern, _}} = definition), do: definition
  defp opaque_definition(%{body: nil} = definition), do: definition
  # A transparent type synonym's body *is* its interface: erase it and `Letter`
  # stops being convertible with `Int` one module boundary away, which is the
  # difference between a synonym and a nominal type.
  defp opaque_definition(%{typealias: true} = definition), do: definition
  defp opaque_definition(definition), do: Map.put(definition, :body, {:hole, "__interface_opaque__"})

  defp interface_edge(dependency) do
    %{
      kind: dependency.kind,
      target: elem(dependency.target, 1),
      line: dependency.span.line
    }
  end

  defp verify_families(env, interface) do
    interface.canonical_declarations
    |> Map.get(:families, %{})
    |> Map.keys()
    |> Enum.sort()
    |> Enum.reduce_while(:ok, fn family, :ok ->
      case Kernel.check_family(env, Map.fetch!(env.families, family)) do
        :ok -> {:cont, :ok}
        {:error, reason} -> {:halt, {:error, {:invalid_interface_family, family, reason}}}
      end
    end)
  end

  defp verify_constructors(env, interface) do
    interface.canonical_declarations
    |> Map.get(:ctors, %{})
    |> Enum.sort_by(&elem(&1, 0))
    |> Enum.reduce_while(:ok, fn {constructor_name, constructor}, :ok ->
      with {:ok, family_name} <- Map.fetch(env.ctor_to_family, constructor_name),
           {:ok, family} <- Map.fetch(env.families, family_name),
           :ok <- Kernel.check_ctor(env, family, constructor) do
        {:cont, :ok}
      else
        :error ->
          {:halt, {:error, {:invalid_interface_constructor_owner, constructor_name}}}

        {:error, reason} ->
          {:halt, {:error, {:invalid_interface_constructor, constructor_name, reason}}}
      end
    end)
  end

  defp verify_definitions(env, interface) do
    interface.canonical_declarations
    |> Map.get(:defs, %{})
    |> Map.keys()
    |> Enum.sort()
    |> Enum.reduce_while(:ok, fn definition, :ok ->
      case Kernel.check_def_type(env, definition) do
        :ok -> {:cont, :ok}
        {:error, reason} -> {:halt, {:error, {:invalid_interface_definition, definition, reason}}}
      end
    end)
  end
end
