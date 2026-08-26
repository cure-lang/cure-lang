defmodule Cure.Compiler.ModuleManifest.Entry do
  @moduledoc false

  @enforce_keys [:identity, :module_name, :source_path, :source_hash]
  defstruct identity: nil,
            module_name: nil,
            source_path: nil,
            source_hash: nil,
            dependencies: [],
            fixity: [],
            prelude_provider?: false

  @type t :: %__MODULE__{}
end

defmodule Cure.Compiler.ModuleManifest do
  @moduledoc """
  Immutable canonical identity and bootstrap-dependency manifest for one
  compilation universe.

  This is the sole stored authority for mapping package/module identities to
  providers. It harvests declaration headers without elaborating bodies.
  """

  alias Cure.Compiler.ModuleManifest.Entry
  alias Cure.Compiler.Parser.{BuiltinFixity, FixityScan}

  @enforce_keys [:package]
  defstruct package: nil, entries: %{}, paths: %{}, dependencies: %{}, external_prelude_providers: []

  @type identity :: {String.t(), String.t()}
  @type dependency :: %{
          required(:kind) => :use_import | :qualified_reference | :prelude_symbol_use,
          required(:source) => identity(),
          required(:target) => identity(),
          required(:span) => map()
        }

  @type t :: %__MODULE__{
          package: String.t(),
          entries: %{identity() => Entry.t()},
          paths: %{Path.t() => identity()},
          dependencies: %{identity() => [dependency()]},
          external_prelude_providers: [identity()]
        }

  @spec build([Path.t()], keyword()) :: {:ok, t()} | {:error, term()}
  def build(paths, opts \\ []) when is_list(paths) and is_list(opts) do
    package = Keyword.get(opts, :package, "root")
    paths = paths |> Enum.map(&Path.expand/1) |> Enum.uniq() |> Enum.sort()

    with :ok <- validate_package(package),
         {:ok, entries} <- scan_entries(paths, package),
         :ok <- reject_duplicates(entries),
         entries =
           resolve_external_targets(
             entries,
             package,
             Keyword.get(opts, :known_modules, [])
           ),
         manifest = assemble(package, entries, Keyword.get(opts, :prelude_modules, [])),
         :ok <- validate_dependencies(manifest, opts) do
      {:ok, manifest}
    end
  end

  @doc """
  Add dependencies that only became visible after macro expansion.

  The header scan reads a module's own text, so it cannot see a reference that
  an imported macro's template introduces — that template lives in the
  provider's file. Expansion therefore extends the universe, and the manifest
  has to grow with it or the newly named module is never scheduled. Rebuilding
  through `assemble/2` keeps prelude ambience, ranks, and closures derived from
  one place instead of being patched in two.
  """
  @spec extend(t(), [dependency()], keyword()) :: {:ok, t()} | {:error, term()}
  def extend(%__MODULE__{} = manifest, [], _opts), do: {:ok, manifest}

  def extend(%__MODULE__{} = manifest, references, opts) when is_list(references) do
    entries =
      Enum.reduce(references, manifest.entries, fn reference, entries ->
        case Map.fetch(entries, reference.source) do
          {:ok, entry} ->
            Map.put(entries, reference.source, %{
              entry
              | dependencies: normalize_dependencies([reference | entry.dependencies])
            })

          :error ->
            entries
        end
      end)

    extended = assemble(manifest.package, Map.values(entries), manifest.external_prelude_providers)

    with :ok <- validate_dependencies(extended, opts), do: {:ok, extended}
  end

  @spec module_names(t()) :: [String.t()]
  def module_names(%__MODULE__{entries: entries}) do
    entries |> Map.keys() |> Enum.map(&elem(&1, 1)) |> Enum.sort()
  end

  @spec fetch(t(), String.t() | identity()) :: {:ok, Entry.t()} | {:error, term()}
  def fetch(%__MODULE__{package: package} = manifest, module_name) when is_binary(module_name),
    do: fetch(manifest, {package, module_name})

  def fetch(%__MODULE__{entries: entries}, identity) when is_tuple(identity) do
    case Map.fetch(entries, identity) do
      {:ok, entry} -> {:ok, entry}
      :error -> {:error, {:module_unavailable, identity}}
    end
  end

  @spec dependencies(t(), String.t() | identity()) :: [dependency()]
  def dependencies(%__MODULE__{package: package} = manifest, module_name) when is_binary(module_name),
    do: dependencies(manifest, {package, module_name})

  def dependencies(%__MODULE__{dependencies: dependencies}, identity),
    do: Map.get(dependencies, identity, [])

  @spec semantic_dump(t()) :: term()
  def semantic_dump(%__MODULE__{} = manifest) do
    manifest.entries
    |> Map.values()
    |> Enum.sort_by(& &1.identity)
    |> Enum.map(fn entry ->
      %{
        identity: entry.identity,
        source_path: entry.source_path,
        source_hash: entry.source_hash,
        prelude_provider?: entry.prelude_provider?,
        dependencies:
          Enum.map(entry.dependencies, fn dependency ->
            Map.take(dependency, [:kind, :source, :target, :span])
          end)
      }
    end)
  end

  @doc """
  A location-free projection of the manifest.

  Spans, filesystem paths, and source hashes are diagnostic provenance, not
  identity: two universes with the same canonical dump schedule and resolve
  identically, whatever order the files arrived in and however the text was
  formatted.
  """
  @spec canonical_dump(t()) :: term()
  def canonical_dump(%__MODULE__{} = manifest) do
    %{
      package: manifest.package,
      external_prelude_providers: manifest.external_prelude_providers,
      modules:
        manifest.entries
        |> Map.values()
        |> Enum.sort_by(& &1.identity)
        |> Enum.map(fn entry ->
          %{
            identity: entry.identity,
            prelude_provider?: entry.prelude_provider?,
            dependencies:
              entry.dependencies
              |> Enum.map(&{&1.kind, &1.target})
              |> Enum.uniq()
              |> Enum.sort()
          }
        end)
    }
  end

  defp validate_package(package) when is_binary(package) and package != "", do: :ok
  defp validate_package(package), do: {:error, {:invalid_package_identity, package}}

  defp scan_entries(paths, package) do
    Enum.reduce_while(paths, {:ok, []}, fn path, {:ok, entries} ->
      case scan_entry(path, package) do
        {:ok, entry} -> {:cont, {:ok, [entry | entries]}}
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  defp scan_entry(path, package) do
    with {:ok, source} <- File.read(path) do
      facts = FixityScan.harvest_source(source, path, BuiltinFixity.table())

      case facts.module do
        module_name when is_binary(module_name) ->
          identity = {package, module_name}

          dependencies =
            Enum.map(facts.uses, &dependency(:use_import, identity, package, path, &1)) ++
              Enum.map(
                facts.qualified_targets,
                &dependency(:qualified_reference, identity, package, path, &1)
              )

          {:ok,
           %Entry{
             identity: identity,
             module_name: module_name,
             source_path: path,
             source_hash: :crypto.hash(:sha256, source),
             dependencies: normalize_dependencies(dependencies),
             fixity: facts.fixity,
             prelude_provider?: facts.prelude?
           }}

        _ ->
          {:error, {:module_identity_missing, path}}
      end
    else
      {:error, reason} -> {:error, {:module_manifest_source_error, path, reason}}
    end
  end

  defp dependency(kind, source, package, path, reference) do
    %{
      kind: kind,
      source: source,
      target: {package, reference.target},
      span: %{path: path, line: reference.line}
    }
  end

  defp normalize_dependencies(dependencies) do
    dependencies
    |> Enum.uniq_by(&{&1.kind, &1.target, &1.span.line})
    |> Enum.sort_by(&{&1.target, &1.kind, &1.span.line})
  end

  defp reject_duplicates(entries) do
    entries
    |> Enum.group_by(& &1.identity)
    |> Enum.sort_by(&elem(&1, 0))
    |> Enum.find_value(:ok, fn
      {_identity, [_entry]} ->
        nil

      {identity, duplicates} ->
        providers = duplicates |> Enum.map(& &1.source_path) |> Enum.sort()
        {:error, {:duplicate_module_identity, %{identity: identity, providers: providers}}}
    end)
  end

  # A source reference is initially package-relative because the header scan
  # does not elaborate bodies and therefore has no environment to consult. Once
  # all local headers are known, resolve a non-local module against the checked
  # package identities supplied by the interface loader. Local definitions win
  # over an identically named dependency; an ambiguous dependency name is left
  # package-relative so validation can report the unresolved edge instead of
  # silently choosing one provider.
  defp resolve_external_targets(entries, package, known_modules) do
    local = MapSet.new(entries, & &1.identity)

    external_by_module =
      known_modules
      |> Enum.flat_map(fn
        {dep_package, module_name} = identity
        when is_binary(dep_package) and is_binary(module_name) and dep_package != package ->
          [{module_name, identity}]

        _ ->
          []
      end)
      |> Enum.group_by(&elem(&1, 0), &elem(&1, 1))
      |> Map.new(fn {module_name, [identity]} -> {module_name, identity} end)

    Enum.map(entries, fn entry ->
      dependencies =
        Enum.map(entry.dependencies, fn dependency ->
          case dependency.target do
            {^package, module_name} = local_target ->
              if MapSet.member?(local, local_target) do
                %{dependency | target: local_target}
              else
                case Map.fetch(external_by_module, module_name) do
                  {:ok, identity} -> %{dependency | target: identity}
                  :error -> dependency
                end
              end

            _ ->
              dependency
          end
        end)

      %{entry | dependencies: normalize_dependencies(dependencies)}
    end)
  end

  defp assemble(package, entries, external_prelude_modules) do
    entries = Map.new(entries, &{&1.identity, &1})

    external_prelude_providers =
      external_prelude_modules
      |> Enum.map(fn
        {_package, _module} = identity -> identity
        module when is_binary(module) -> {package, module}
      end)
      |> Enum.reject(&Map.has_key?(entries, &1))
      |> Enum.uniq()
      |> Enum.sort()

    prelude_providers =
      entries
      |> Enum.filter(fn {_identity, entry} -> entry.prelude_provider? end)
      |> Enum.map(&elem(&1, 0))
      |> Enum.sort()

    closures = Map.new(Map.keys(entries), &{&1, dependency_closure(entries, [&1])})

    bootstrap =
      prelude_providers
      |> Enum.map(&Map.fetch!(closures, &1))
      |> Enum.reduce(MapSet.new(), &MapSet.union/2)

    ranks = Map.new(closures, fn {identity, closure} -> {identity, {MapSet.size(closure), elem(identity, 1)}} end)

    entries =
      Map.new(entries, fn {identity, entry} ->
        ambient =
          prelude_providers
          |> Enum.filter(&ambient_provider?(bootstrap, ranks, &1, identity))
          |> Enum.map(fn provider ->
            %{
              kind: :prelude_symbol_use,
              source: identity,
              target: provider,
              span: %{path: entry.source_path, line: 1}
            }
          end)

        external_ambient =
          Enum.map(external_prelude_providers, fn provider ->
            %{
              kind: :prelude_symbol_use,
              source: identity,
              target: provider,
              span: %{path: entry.source_path, line: 1}
            }
          end)

        entry = %{entry | dependencies: normalize_dependencies(entry.dependencies ++ ambient ++ external_ambient)}
        {identity, entry}
      end)

    %__MODULE__{
      package: package,
      entries: entries,
      paths: Map.new(entries, fn {identity, entry} -> {entry.source_path, identity} end),
      dependencies: Map.new(entries, fn {identity, entry} -> {identity, entry.dependencies} end),
      external_prelude_providers: external_prelude_providers
    }
  end

  # Which prelude providers become ambient in `identity`.
  #
  # Outside the bootstrap set — the union of every provider's dependency closure
  # — a module is reachable from no provider, so handing it every provider can
  # never close a cycle. That is the ordinary case and it keeps the full prelude.
  #
  # Inside the bootstrap set the providers are being compiled too, so ambient
  # edges must run one way only. The rule this replaces gave bootstrap modules NO
  # ambient prelude at all, which is far stronger than acyclicity needs:
  # `Std.Binary` is itself a provider, so it was denied ambient `Std.Bounded`
  # even though `Std.Bounded` reaches only `Std.Nat` and could never reach back.
  # That mattered because the elaborator's own generated syntax asks for more than
  # the module authored — a contextual integer literal builds
  # `NaturalLiteral(spelling, value)`, whose spelling is a string, whose
  # characters are char literals, whose inferred type is `Bounded(0x110000)`.
  #
  # A pairwise "can the provider reach me?" test is NOT enough: `Std.Int` and
  # `Std.Equatable` reach each other through neither's authored imports, so each
  # would become ambient in the other and the two would fuse into one component.
  # Ordering by dependency-closure SIZE (name breaking ties) is a strict total
  # order that every original dependency edge already respects: A ∈ closure(B)
  # gives closure(A) ⊆ closure(B), and equal sizes would force closure(A) =
  # closure(B), i.e. a dependency cycle rejected elsewhere. Ambient edges pointing
  # strictly down that order therefore cannot create one either, and "depends on
  # less" is exactly the sense in which a module is more foundational.
  defp ambient_provider?(bootstrap, ranks, provider, identity) do
    if MapSet.member?(bootstrap, identity) do
      Map.fetch!(ranks, provider) < Map.fetch!(ranks, identity)
    else
      true
    end
  end

  defp dependency_closure(entries, roots), do: dependency_closure(entries, roots, MapSet.new())
  defp dependency_closure(_entries, [], seen), do: seen

  defp dependency_closure(entries, [identity | rest], seen) do
    if MapSet.member?(seen, identity) do
      dependency_closure(entries, rest, seen)
    else
      dependencies =
        case Map.fetch(entries, identity) do
          {:ok, entry} ->
            entry.dependencies
            |> Enum.map(& &1.target)
            |> Enum.filter(&Map.has_key?(entries, &1))

          :error ->
            []
        end

      dependency_closure(entries, dependencies ++ rest, MapSet.put(seen, identity))
    end
  end

  defp validate_dependencies(manifest, opts) do
    known =
      opts
      |> Keyword.get(:known_modules, [])
      |> Enum.map(fn
        {_package, _module} = identity -> identity
        module when is_binary(module) -> {manifest.package, module}
      end)
      |> MapSet.new()
      |> MapSet.union(MapSet.new(Map.keys(manifest.entries)))

    private =
      manifest.entries
      |> Map.keys()
      |> Enum.sort()
      |> Enum.find_value(fn identity ->
        manifest
        |> dependencies(identity)
        |> Enum.find_value(fn dependency ->
          case dependency.target do
            {package, module_name} when package != manifest.package ->
              case Keyword.get(opts, :package_exports, %{}) |> Map.fetch(package) do
                {:ok, allowed} ->
                  if module_name in List.wrap(allowed) do
                    nil
                  else
                    {:package_module_not_exported,
                     %{
                       requester: dependency.source,
                       target: dependency.target,
                       kind: dependency.kind,
                       span: dependency.span
                     }}
                  end

                _ ->
                  nil
              end

            _ ->
              nil
          end
        end)
      end)

    missing =
      manifest.entries
      |> Map.keys()
      |> Enum.sort()
      |> Enum.find_value(fn identity ->
        manifest
        |> dependencies(identity)
        |> Enum.find(&(not MapSet.member?(known, &1.target)))
      end)

    cond do
      private ->
        {:error, private}

      missing ->
        {:error,
         {:missing_module,
          %{
            requester: missing.source,
            target: missing.target,
            kind: missing.kind,
            span: missing.span
          }}}

      true ->
        :ok
    end
  end
end
