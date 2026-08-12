defmodule Cure.Compiler.ModulePipeline do
  @moduledoc """
  Canonical module compilation boundary.

  The implementation is deliberately phase-oriented: discovery creates the
  immutable manifest, header collection creates skeletons, and later phases
  add checked interfaces, bodies, closure, and artifacts to the same result.
  """

  alias Cure.Compiler.{DepGraph, ModuleInterface, ModuleManifest, Printer}

  alias Cure.Compiler.ModulePipeline.{
    BodyElaborationTrace,
    Cache,
    Closure,
    Conformance,
    Cycle,
    Diagnosis,
    Emission,
    Environment,
    Expansion,
    Interface,
    Publication,
    Request,
    Result,
    SemanticGraph
  }

  alias Cure.Core.{Builtins, Env}
  alias Cure.Elab.{MacroExpand, Name, Program}

  @spec check([Path.t()], keyword()) :: {:ok, Result.t()} | {:error, term()}
  def check(paths, opts \\ []) when is_list(paths) and is_list(opts) do
    {result, body_elaborations} = BodyElaborationTrace.run(fn -> check_traced(paths, opts) end)

    case result do
      {:ok, %Result{} = checked} ->
        {:ok, %{checked | body_elaborations: Enum.uniq(body_elaborations)}}

      other ->
        other
    end
  end

  defp check_traced(paths, opts) do
    request_opts =
      opts
      |> Keyword.put_new(:entry_point, :module_check)
      |> Keyword.put(:sources, paths)

    with {:ok, request} <- Request.new(request_opts),
         :ok <- require_canonical(request) do
      # The macro execution strategy is a property of the run, not of any one
      # expansion, so it is established once here and every expander this check
      # reaches obeys it.
      MacroExpand.with_execution(request.macro_execution, fn -> check_request(request, paths) end)
    end
  end

  defp check_request(request, paths) do
    with {:ok, external_interfaces} <-
           timed(request, :interface_load, %{roots: request.interface_roots}, fn ->
             Interface.load_roots(request.interface_roots)
           end),
         {:ok, external_envs} <- interface_environments(external_interfaces),
         manifest_options = manifest_options(request, external_interfaces),
         {:ok, manifest} <-
           timed(request, :manifest, %{source_count: length(paths)}, fn ->
             ModuleManifest.build(paths, manifest_options)
           end),
         {:ok, expansion} <-
           timed(request, :expansion, %{source_count: length(paths)}, fn ->
             Expansion.run(manifest, manifest_options)
           end),
         manifest = expansion.manifest,
         components = strongly_connected_components(manifest),
         {:ok, interfaces, checked_envs, body_envs, diagnostics, rebuilt} <-
           timed(request, :module_check, %{component_count: length(components)}, fn ->
             check_modules(
               request,
               manifest,
               expansion.skeletons,
               expansion.asts,
               expansion.sources,
               external_interfaces,
               external_envs,
               components
             )
           end),
         :ok <- reject_failed_run(diagnostics),
         {:ok, beams} <-
           timed(request, :emission, %{module_count: map_size(expansion.asts)}, fn ->
             emit_beams(request, manifest, expansion.asts, interfaces, body_envs)
           end),
         :ok <-
           timed(request, :publication, %{module_count: map_size(expansion.asts)}, fn ->
             publish(request, interfaces, beams)
           end) do
      {:ok,
       %Result{
         request: request,
         beams: beams,
         manifest: manifest,
         skeletons: expansion.skeletons,
         asts: expansion.asts,
         interfaces: interfaces,
         checked_envs: checked_envs,
         body_envs: body_envs,
         components: components,
         diagnostics: diagnostics,
         rebuilt_modules: rebuilt,
         expansion_rounds: expansion.rounds,
         semantic_graph: record_generated_references(SemanticGraph.from_manifest(manifest), expansion.generated)
       }}
    end
  end

  defp timed(request, phase, metadata, operation) when is_function(operation, 0) do
    started = System.monotonic_time(:microsecond)
    result = operation.()
    elapsed = System.monotonic_time(:microsecond) - started
    emit_event(request, {:module_pipeline_timing, phase, elapsed, metadata})
    result
  end

  defp emit_event(%Request{event_sink: sink}, event) when is_function(sink, 1) do
    sink.(event)
    :ok
  rescue
    _ -> :ok
  catch
    _, _ -> :ok
  end

  defp emit_event(_request, _event), do: :ok

  defp record_generated_references(graph, generated) do
    Enum.reduce(generated, graph, fn reference, graph ->
      SemanticGraph.put(graph, %{
        kind: :macro_generated_reference,
        source: elem(reference.source, 1),
        target: elem(reference.target, 1),
        phase: :expand,
        span: reference.span
      })
    end)
  end

  # Collected diagnostics do not make a failed run succeed: they change how the
  # failure is *reported* — every independent cause once, instead of the first
  # one and nothing else.
  defp reject_failed_run([]), do: :ok
  defp reject_failed_run(diagnostics), do: {:error, diagnostics}

  # Bytecode is a PRODUCT of a checked run, requested per run rather than always
  # produced: checking is what most entry points want, and emitting the whole
  # universe costs real time. A run that asks for beams gets them from the envs
  # the check already produced — see `Emission` — so asking cannot change what
  # was checked, only what is carried out of the run.
  defp emit_beams(%Request{products: products, artifact_roots: artifact_roots}, manifest, asts, interfaces, body_envs) do
    if :beams in List.wrap(products),
      do: Emission.run(manifest, asts, interfaces, body_envs, artifact_roots),
      else: {:ok, %{}}
  end

  # Publication is the last thing a run does. A generation that was assembled
  # from a run that then failed must never become visible, so nothing is
  # installed until the whole universe has checked — and, when beams were
  # requested, until every one of them has been emitted.
  defp publish(%Request{publication: :atomic} = request, interfaces, beams),
    do: Publication.publish(request.output, request.generation, interfaces, beams)

  defp publish(_request, _interfaces, _beams), do: :ok

  @doc """
  The generation a reader of a published output directory currently sees.
  """
  @spec open_published_generation(Path.t()) :: {:ok, map()} | {:error, term()}
  defdelegate open_published_generation(root), to: Publication, as: :open

  @doc "Whether an opened generation contains every module it claims."
  @spec generation_complete?(map()) :: boolean()
  defdelegate generation_complete?(published), to: Publication, as: :complete?

  @doc "Whether an opened generation still names a path inside a staging tree."
  @spec contains_staging_reference?(map()) :: boolean()
  defdelegate contains_staging_reference?(published), to: Publication

  @doc "The bytecode an opened generation published for `module`."
  @spec read_published_beam(map(), module()) :: {:ok, binary()} | {:error, term()}
  defdelegate read_published_beam(published, module), to: Publication, as: :read_beam

  @spec write_interfaces(Result.t(), Path.t()) :: :ok | {:error, term()}
  def write_interfaces(%Result{} = result, root) when is_binary(root) do
    result.manifest.entries
    |> Map.keys()
    |> Enum.map(&Map.fetch!(result.interfaces, &1))
    |> Enum.uniq_by(&{&1.module_name, &1.interface_hash})
    |> Enum.sort_by(& &1.module_name)
    |> Enum.reduce_while(:ok, fn interface, :ok ->
      case Interface.write(interface, root) do
        :ok -> {:cont, :ok}
        {:error, reason} -> {:halt, {:error, {:interface_write_failed, interface.module_name, reason}}}
      end
    end)
  end

  @spec interface_path(Path.t(), String.t()) :: {:ok, Path.t()} | {:error, term()}
  def interface_path(root, module_name) when is_binary(root) and is_binary(module_name) do
    path = Interface.path(root, module_name)
    if File.regular?(path), do: {:ok, path}, else: {:error, {:interface_artifact_missing, module_name, path}}
  end

  @doc """
  The modules this run actually rechecked.

  Everything else came from the cache, so this is the executable statement that
  invalidation followed the checked semantic graph and not the order the files
  were handed in.
  """
  @spec rebuilt_modules(Result.t()) :: [String.t()]
  def rebuilt_modules(%Result{rebuilt_modules: rebuilt}), do: rebuilt

  @doc """
  Make a written interface fail its own hash check, for tests of the rejection
  path.
  """
  @spec corrupt_interface_for_test(Path.t(), :dependency_hash) :: :ok | {:error, term()}
  defdelegate corrupt_interface_for_test(path, kind), to: Interface, as: :corrupt

  @spec kernel_verify_interfaces(Result.t()) :: :ok | {:error, term()}
  def kernel_verify_interfaces(%Result{} = result) do
    with {:ok, universe} <- Interface.environment(result.interfaces),
         :ok <- Interface.verify_all(result.interfaces, universe) do
      :ok
    end
  end

  @spec component_members(Result.t(), String.t()) :: [String.t()]
  def component_members(%Result{} = result, module_name) when is_binary(module_name) do
    result.components
    |> Enum.find([], fn component -> Enum.any?(component, &(elem(&1, 1) == module_name)) end)
    |> Enum.map(&elem(&1, 1))
    |> Enum.sort()
  end

  @spec component_class(Result.t(), String.t()) :: :acyclic | :runtime_cycle
  def component_class(%Result{} = result, module_name) when is_binary(module_name) do
    case component_members(result, module_name) do
      [_] -> :acyclic
      [_ | _] -> :runtime_cycle
      [] -> :acyclic
    end
  end

  @spec interfaces_frozen_together?(Result.t(), [String.t()]) :: boolean()
  def interfaces_frozen_together?(%Result{} = result, module_names) when is_list(module_names) do
    expected = Enum.sort(module_names)

    Enum.any?(result.components, fn component ->
      names = component |> Enum.map(&elem(&1, 1)) |> Enum.sort()

      names == expected and
        Enum.all?(component, &Map.has_key?(result.interfaces, &1))
    end)
  end

  @spec resolve(Result.t(), String.t(), atom(), String.t()) :: {:ok, tuple()} | {:error, term()}
  def resolve(%Result{} = result, requesting_module, namespace, written_name)
      when is_binary(requesting_module) and is_atom(namespace) and is_binary(written_name) do
    if String.contains?(written_name, ".") do
      resolve_qualified(result, namespace, written_name)
    else
      resolve_bare(result, requesting_module, namespace, written_name)
    end
  end

  @doc """
  The complete edge vocabulary of the checked semantic graph.

  This list is exhaustive by construction: an edge kind that is not here cannot
  be recorded, so no second, informal dependency notion can accumulate beside
  it. It is `SemanticGraph`'s own list rather than a copy — a second copy here
  would drift, and a kind the graph accepted but this function did not report
  would be exactly the informal vocabulary the closedness is meant to prevent.
  """
  @spec semantic_edge_kinds() :: [atom()]
  defdelegate semantic_edge_kinds(), to: SemanticGraph, as: :kinds

  @spec semantic_edge?(Result.t(), String.t(), String.t(), atom()) :: boolean()
  def semantic_edge?(%Result{} = result, source, target, kind)
      when is_binary(source) and is_binary(target) and is_atom(kind) do
    kind in SemanticGraph.kinds() and
      Enum.any?(SemanticGraph.edges(result.semantic_graph, source), fn edge ->
        edge.kind == kind and edge.target == target
      end)
  end

  @doc """
  Resolve a name across a module boundary the way a *second* consumer would.

  A module's own exports and its explicit `public use` reexports cross; an
  ordinary `use` does not.
  """
  @spec resolve_reexport(Result.t(), String.t(), atom(), String.t()) :: {:ok, tuple()} | {:error, term()}
  def resolve_reexport(%Result{} = result, module_name, namespace, name)
      when is_binary(module_name) and is_atom(namespace) and is_binary(name) do
    with {:ok, skeleton} <- fetch_skeleton(result, module_name) do
      case exported_declarations(result, skeleton, namespace, name) do
        [declaration] -> {:ok, declaration.key}
        [] -> {:error, :not_exported}
        declarations -> {:error, {:ambiguous_reexport, name, declarations |> Enum.map(& &1.key) |> Enum.sort()}}
      end
    end
  end

  @doc """
  Run the pipeline as a named compilation entry point.

  Every entry point submits the same manifest through the same boundary; the
  entry name is recorded on the request for diagnostics and product selection
  and has no say in resolution.
  """
  @spec check_entry_point(atom(), [Path.t()], keyword()) :: {:ok, Result.t()} | {:error, term()}
  def check_entry_point(entry_point, paths, opts \\ [])
      when is_atom(entry_point) and is_list(paths) and is_list(opts) do
    opts
    |> Keyword.put(:entry_point, entry_point)
    |> Keyword.put_new(:module_pipeline, :canonical)
    |> then(&check(paths, &1))
  end

  @spec interface(Result.t(), String.t()) :: {:ok, ModuleInterface.t()} | {:error, term()}
  def interface(%Result{} = result, module_name) when is_binary(module_name) do
    case Map.fetch(result.interfaces, {result.manifest.package, module_name}) do
      {:ok, interface} -> {:ok, interface}
      :error -> {:error, {:interface_unavailable, module_name}}
    end
  end

  @spec interface_hash(Result.t(), String.t()) :: binary() | nil
  def interface_hash(%Result{} = result, module_name) when is_binary(module_name) do
    case interface(result, module_name) do
      {:ok, interface} -> interface.interface_hash
      {:error, _} -> nil
    end
  end

  @spec interface_hashes(Result.t()) :: [{String.t(), binary()}]
  def interface_hashes(%Result{} = result) do
    result.interfaces
    |> Enum.map(fn {identity, interface} -> {elem(identity, 1), interface.interface_hash} end)
    |> Enum.sort()
  end

  @spec merge_interfaces([ModuleInterface.t()]) :: {:ok, Environment.t()} | {:error, term()}
  defdelegate merge_interfaces(interfaces), to: Environment, as: :merge

  @spec semantic_environment_dump(Environment.t()) :: term()
  defdelegate semantic_environment_dump(environment), to: Environment, as: :semantic_dump

  @spec canonical_identities(Environment.t()) :: [{atom(), atom()}]
  defdelegate canonical_identities(environment), to: Environment

  @spec definitionally_equal?(Environment.t(), String.t(), String.t()) :: boolean()
  defdelegate definitionally_equal?(environment, left, right), to: Environment

  @doc """
  A definition's Core, with source order and provenance already gone.

  Two universes that agree on meaning agree here; that is what makes this the
  right thing to compare an authored definition against a macro-generated one.
  """
  @spec normalized_core(Result.t(), String.t(), String.t()) :: {:ok, map()} | {:error, term()}
  def normalized_core(%Result{} = result, module_name, name)
      when is_binary(module_name) and is_binary(name) do
    with {:ok, env} <- body_environment(result, module_name) do
      Closure.normalized(env, module_name, name)
    end
  end

  @doc """
  Every global in every checked definition is an owner-qualified key the
  universe knows.
  """
  @spec all_core_globals_canonical?(Result.t()) :: boolean()
  def all_core_globals_canonical?(%Result{} = result) do
    Enum.all?(result.body_envs, fn {identity, env} ->
      Closure.all_globals_canonical?(env, owned_definition_keys(env, elem(identity, 1)))
    end)
  end

  @doc """
  The definitions the kernel certified.

  Certification is per definition, so this is the exact set the checker stands
  behind — not the set of names that happen to exist.
  """
  @spec totality_keys(Result.t()) :: [tuple()]
  def totality_keys(%Result{} = result) do
    result.body_envs
    |> Enum.flat_map(fn {identity, env} ->
      env |> owned_definition_keys(elem(identity, 1)) |> Enum.map(&definition_key(result, &1))
    end)
    |> Enum.sort()
    |> Enum.uniq()
  end

  @doc """
  The definitions reachable from what the universe exports.

  Compared against `totality_keys/1` this is the statement that nothing checked
  is unreachable and nothing reachable is unchecked.
  """
  @spec reachability_keys(Result.t()) :: [tuple()]
  def reachability_keys(%Result{} = result) do
    result.body_envs
    |> Enum.flat_map(fn {identity, env} ->
      case Closure.reachable(env, owned_definition_keys(env, elem(identity, 1))) do
        {:ok, keys} -> Enum.map(keys, &definition_key(result, &1))
        {:error, _} -> []
      end
    end)
    |> Enum.sort()
    |> Enum.uniq()
  end

  @doc "Everything emitting `module_name.name` would have to emit with it."
  @spec emission_closure(Result.t(), String.t(), String.t()) :: {:ok, [tuple()]} | {:error, term()}
  def emission_closure(%Result{} = result, module_name, name)
      when is_binary(module_name) and is_binary(name) do
    with {:ok, env} <- body_environment(result, module_name) do
      Closure.emission(env, Name.qualify(module_name, name), &definition_key(result, &1))
    end
  end

  defp body_environment(%Result{} = result, module_name) do
    case Map.fetch(result.body_envs, {result.manifest.package, module_name}) do
      {:ok, env} -> {:ok, env}
      :error -> {:error, {:module_bodies_unavailable, module_name}}
    end
  end

  defp owned_definition_keys(%Env{defs: defs}, owner),
    do: defs |> Map.keys() |> Enum.filter(&(Name.owner(&1) == owner)) |> Enum.sort()

  # A Core key names its owner but not its package; the package comes from the
  # universe that checked it, which is the manifest and nothing else.
  defp definition_key(%Result{} = result, key) do
    {owner, base} = Name.split(key)
    {package_of(result, owner), owner, :value, base}
  end

  defp package_of(%Result{} = result, owner) do
    if Map.has_key?(result.manifest.entries, {result.manifest.package, owner}),
      do: result.manifest.package,
      else: :external
  end

  @spec conformance_owner(Result.t(), String.t(), String.t()) :: String.t() | nil
  def conformance_owner(%Result{} = result, interface_name, type_name)
      when is_binary(interface_name) and is_binary(type_name),
      do: Conformance.owner(result.interfaces, interface_name, type_name)

  @spec conformance_count(Result.t(), String.t(), String.t()) :: non_neg_integer()
  def conformance_count(%Result{} = result, interface_name, type_name)
      when is_binary(interface_name) and is_binary(type_name),
      do: Conformance.count(result.interfaces, interface_name, type_name)

  @doc """
  The conformance a module selects, as canonical data.

  Selection is over what the requesting module can reach, not over everything
  the run happened to check, so a conformance that is merely present in the
  universe cannot silently become the answer.
  """
  @spec selected_conformance(Result.t(), String.t(), String.t(), String.t()) :: {:ok, map()} | {:error, term()}
  def selected_conformance(%Result{} = result, requesting_module, interface_name, type_name)
      when is_binary(requesting_module) and is_binary(interface_name) and is_binary(type_name) do
    visible =
      result.manifest
      |> reachable_modules({result.manifest.package, requesting_module})
      |> Enum.map(&elem(&1, 1))

    Conformance.selected(result.interfaces, visible, interface_name, type_name)
  end

  @spec manifest_dump(Result.t()) :: term()
  def manifest_dump(%Result{} = result), do: ModuleManifest.canonical_dump(result.manifest)

  @doc """
  How many expansion rounds this run needed before the syntax set stopped
  growing.

  One means nothing a macro produced named anything new. More than one means
  expansion extended the universe and the extension was itself resolved and
  re-scanned, which is the only evidence that the graph is the *final* one
  rather than the one the header scan guessed.
  """
  @spec expansion_rounds(Result.t()) :: pos_integer()
  def expansion_rounds(%Result{expansion_rounds: rounds}), do: rounds

  @doc """
  The expanded syntax of the whole universe, free of source positions.

  Two runs that differ only in how macro expanders were executed must agree
  here; anything else means the execution strategy is part of the language's
  meaning.
  """
  @spec expanded_syntax_dump(Result.t()) :: [{String.t(), term()}]
  def expanded_syntax_dump(%Result{} = result), do: Expansion.syntax_dump(result.asts)

  @doc "The hygienic names expansion minted, grouped by the declaration holding them."
  @spec fresh_name_sets(Result.t()) :: [{String.t(), String.t(), [String.t()]}]
  def fresh_name_sets(%Result{} = result), do: Expansion.fresh_name_groups(result.asts)

  @doc "Whether sibling expansions minted disjoint names, as hygiene requires."
  @spec sibling_expansions_disjoint?(Result.t()) :: boolean()
  def sibling_expansions_disjoint?(%Result{} = result), do: Expansion.sibling_expansions_disjoint?(result.asts)

  @doc """
  The canonical key a declaration has in its owning module.

  A declaration a macro generated is answered the same way as an authored one:
  after expansion there is no second class of definition, so nothing downstream
  needs to know which it was.
  """
  @spec canonical_definition(Result.t(), String.t(), atom(), String.t()) :: {:ok, tuple()} | {:error, term()}
  def canonical_definition(%Result{} = result, module_name, namespace, name)
      when is_binary(module_name) and is_atom(namespace) and is_binary(name) do
    identity = {result.manifest.package, module_name}

    with {:ok, skeleton} <- Map.fetch(result.skeletons, identity),
         {:ok, declaration} <- Map.fetch(skeleton.declarations, {namespace, name}) do
      {:ok, declaration.key}
    else
      :error -> {:error, {:declaration_unavailable, {elem(identity, 0), module_name, namespace, name}}}
    end
  end

  @spec checked?(Result.t(), String.t()) :: boolean()
  def checked?(%Result{} = result, module_name) when is_binary(module_name),
    do: Map.has_key?(result.interfaces, {result.manifest.package, module_name})

  @spec diagnostics(Result.t()) :: [term()]
  def diagnostics(%Result{diagnostics: diagnostics}), do: diagnostics

  @doc """
  Whether checking `source`'s bodies elaborated `target`'s bodies.

  True only for mutually recursive peers. Between two modules that are not in one
  component this is the previous pipeline's signature failure — a provider
  compiled to construct a consumer's ambient scope — and it stays observable
  here instead of being something the design merely asserts.
  """
  @spec body_elaboration_edge?(Result.t(), String.t(), String.t()) :: boolean()
  def body_elaboration_edge?(%Result{} = result, source, target)
      when is_binary(source) and is_binary(target) do
    Enum.any?(result.body_elaborations, &(&1.source == source and &1.target == target))
  end

  @doc """
  How many consumers elaborated `provider`'s bodies during `phase`.

  Counts distinct consumer/provider pairs, so a provider that is read only
  through its checked interface reports zero however many modules use it.
  """
  @spec provider_body_elaboration_count(Result.t(), String.t(), atom()) :: non_neg_integer()
  def provider_body_elaboration_count(%Result{} = result, provider, phase)
      when is_binary(provider) and is_atom(phase) do
    result.body_elaborations
    |> Enum.filter(&(&1.target == provider and &1.phase == phase))
    |> Enum.uniq_by(&{&1.source, &1.target})
    |> length()
  end

  @doc """
  How a checked module represents one of its own types.

  `:nominal` — the type is a data family, distinct from everything else even
  where the underlying shape agrees. `:transparent` — a synonym that a consumer
  may unfold. The distinction is read from the frozen interface rather than the
  source, because the interface is what a consumer actually sees: a nominal
  `String` whose interface published it as an alias for `List(Char)` would be
  nominal in name only.
  """
  @spec type_representation(Result.t(), String.t(), String.t()) :: :nominal | :transparent | :unknown
  def type_representation(%Result{} = result, module_name, type_name)
      when is_binary(module_name) and is_binary(type_name) do
    with %ModuleInterface{} = interface <- Map.get(result.interfaces, {result.manifest.package, module_name}) do
      key = Name.qualify(module_name, type_name)
      declarations = interface.canonical_declarations

      cond do
        Map.has_key?(Map.get(declarations, :families, %{}), key) -> :nominal
        Map.get(declarations, :defs, %{})[key][:typealias] -> :transparent
        true -> :unknown
      end
    else
      _ -> :unknown
    end
  end

  @doc "Diagnostics stripped of everything that is provenance rather than meaning."
  @spec normalized_diagnostics(Result.t()) :: [term()]
  def normalized_diagnostics(%Result{diagnostics: diagnostics}) do
    diagnostics
    |> Enum.map(fn diagnostic ->
      {Map.get(diagnostic, :code), Map.get(diagnostic, :severity), Map.get(diagnostic, :module)}
    end)
    |> Enum.sort()
  end

  @doc """
  Recheck the universe from printed source.

  Printing and reparsing changes every span and every byte offset. Nothing that
  survives into the manifest or an interface hash may depend on those, so this
  round trip is the executable form of "metadata is not meaning".
  """
  @spec parse_print_recheck(Result.t(), keyword()) :: {:ok, Result.t()} | {:error, term()}
  def parse_print_recheck(%Result{} = result, opts \\ []) when is_list(opts) do
    root = Path.join(System.tmp_dir!(), "cure-print-#{:erlang.unique_integer([:positive])}")

    try do
      File.mkdir_p!(root)

      paths =
        Enum.map(Enum.sort_by(result.asts, &elem(&1, 0)), fn {identity, ast} ->
          path = Path.join(root, elem(identity, 1) <> ".cure")
          File.write!(path, Printer.quoted_to_string(ast) <> "\n")
          path
        end)

      check(paths, reprint_options(result.request, root, opts))
    after
      File.rm_rf(root)
    end
  end

  defp reprint_options(%Request{} = request, root, opts) do
    [
      module_pipeline: :canonical,
      package: request.package,
      source_roots: [root],
      interface_roots: request.interface_roots,
      entry_point: request.entry_point,
      macro_execution: request.macro_execution,
      fresh_environment: Keyword.get(opts, :metadata) == :fresh
    ]
  end

  @doc """
  The stored authorities this result actually consulted.

  The design permits exactly two. A third entry here means a second answer to
  "what does this name mean" has grown back.
  """
  @spec semantic_authorities(Result.t()) :: [atom()]
  def semantic_authorities(%Result{} = result) do
    [
      {:module_manifest, match?(%ModuleManifest{}, result.manifest)},
      {:checked_interfaces, result.interfaces != %{}}
    ]
    |> Enum.filter(&elem(&1, 1))
    |> Enum.map(&elem(&1, 0))
  end

  @doc """
  How many times this run reached for a resolution path outside the manifest and
  the checked interfaces.

  Each counter names a fallback the previous pipeline used. All of them are zero
  because the code implementing them is gone, not because a check found nothing
  — what keeps them gone is the boundary suite, which reads the sources. This map
  is the other half: the channel a *reintroduced* path reports itself through, so
  one that comes back as new code is a non-zero count rather than a silent pass.
  Be clear about which of the two is doing the work before trusting either.
  """
  @spec alternate_path_counts(Result.t()) :: %{atom() => non_neg_integer()}
  def alternate_path_counts(%Result{} = result) do
    Map.merge(
      %{
        beam_export_probes: 0,
        source_jit_loads: 0,
        stamped_ast_scans: 0,
        late_bare_recoveries: 0,
        entry_point_graphs: 0,
        mutable_environment_merges: 0,
        codegen_rechecks: 0
      },
      result.alternate_paths
    )
  end

  defp require_canonical(%Request{selection: :canonical}), do: :ok
  defp require_canonical(%Request{selection: selection}), do: {:error, {:module_pipeline_not_selected, selection}}

  defp manifest_options(request, external_interfaces) do
    [
      package: request.package || "root",
      source_roots: request.source_roots,
      edition: request.edition || Cure.Edition.current(),
      known_modules: Map.keys(external_interfaces) ++ Builtins.provided_modules(),
      prelude_modules:
        external_interfaces
        |> Enum.filter(fn {_module, interface} ->
          Map.get(interface.source_metadata, :prelude_provider?, false)
        end)
        |> Enum.map(&elem(&1, 0))
        |> Enum.sort()
    ]
  end

  defp check_modules(request, manifest, skeletons, asts, sources, external_interfaces, external_envs, components) do
    cached = Cache.load(request.cache)
    reusable_products = reusable_product_identities(request, manifest, cached)

    initial =
      {:ok, external_interface_table(manifest, external_interfaces), external_env_table(manifest, external_envs), %{},
       [], []}

    result =
      Enum.reduce_while(components, initial, fn component, {:ok, interfaces, envs, bodies, diagnostics, rebuilt} ->
        timed(request, :component, %{modules: component |> Enum.map(&elem(&1, 1)) |> Enum.sort()}, fn ->
          case reuse_component(cached, component, manifest, interfaces, reusable_products) do
            {:ok, reused, reused_envs} ->
              {:cont, {:ok, Map.merge(interfaces, reused), Map.merge(envs, reused_envs), bodies, diagnostics, rebuilt}}

            :stale ->
              check_or_report(manifest, skeletons, component, asts, sources, request, {
                interfaces,
                envs,
                bodies,
                diagnostics,
                rebuilt
              })
          end
        end)
      end)

    with {:ok, interfaces, envs, bodies, diagnostics, rebuilt} <- result do
      Cache.store(request.cache, interfaces)
      {:ok, interfaces, envs, bodies, diagnostics, Enum.sort(rebuilt)}
    end
  end

  defp reusable_product_identities(
         %Request{products: products, artifact_roots: artifact_roots},
         manifest,
         cached
       ) do
    if :beams in List.wrap(products) do
      cached_by_identity =
        manifest.entries
        |> Enum.reduce(%{}, fn {identity, entry}, interfaces ->
          case Map.fetch(cached, entry.module_name) do
            {:ok, interface} -> Map.put(interfaces, identity, interface)
            :error -> interfaces
          end
        end)

      Emission.reusable_beam_identities(artifact_roots, manifest, cached_by_identity)
    else
      nil
    end
  end

  defp check_or_report(manifest, skeletons, component, asts, sources, request, state) do
    {interfaces, envs, bodies, diagnostics, rebuilt} = state

    Enum.each(component, fn identity ->
      entry = Map.fetch!(manifest.entries, identity)
      emit_event(request, {:compile_started, entry.module_name, entry.source_path})
    end)

    case check_component(request, manifest, skeletons, component, asts, sources, interfaces, envs) do
      {:ok, next_interfaces, next_envs, checked} ->
        {:cont,
         {:ok, next_interfaces, next_envs, Map.merge(bodies, checked), diagnostics,
          rebuilt ++ Enum.map(component, &elem(&1, 1))}}

      {:error, reason} when request.collect_diagnostics ->
        {:cont,
         {:ok, interfaces, envs, bodies, diagnostics ++ component_diagnostics(manifest, component, reason), rebuilt}}

      {:error, _} = error ->
        {:halt, error}
    end
  end

  defp reuse_component(cached, component, manifest, published_interfaces, reusable_products) do
    published =
      Map.new(published_interfaces, fn {identity, interface} -> {elem(identity, 1), interface.interface_hash} end)

    with {:ok, reused} <- Cache.reusable(cached, component, manifest.entries, published),
         true <- products_reusable?(component, reusable_products),
         {:ok, envs} <- reused_environments(reused) do
      {:ok, reused, envs}
    else
      _ -> :stale
    end
  end

  defp products_reusable?(_component, nil), do: true
  defp products_reusable?(component, reusable), do: Enum.all?(component, &MapSet.member?(reusable, &1))

  defp reused_environments(reused) do
    Enum.reduce_while(reused, {:ok, %{}}, fn {identity, interface}, {:ok, envs} ->
      case Interface.to_env(interface) do
        {:ok, env} -> {:cont, {:ok, Map.put(envs, identity, env)}}
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  # A component that failed publishes no interface, so every module that names it
  # fails too. Only the first failure is a cause; the rest are its shadow, and
  # `Diagnosis` is the one place that distinction is made.
  defp component_diagnostics(manifest, component, reason) do
    identity = List.first(component)
    source_path = Map.fetch!(manifest.entries, identity).source_path

    case Diagnosis.diagnostic(reason, identity, source_path) do
      nil -> []
      diagnostic -> [diagnostic]
    end
  end

  defp check_component(request, manifest, skeletons, component, asts, sources, interfaces, checked_envs) do
    members = MapSet.new(component)
    check_order = component_check_order(manifest, component)
    timing_metadata = %{modules: component |> Enum.map(&elem(&1, 1)) |> Enum.sort()}

    with :ok <- Cycle.classify(manifest, component, asts, skeletons),
         {:ok, prepared} <-
           timed(request, :component_register, timing_metadata, fn ->
             register_component(
               manifest,
               component,
               check_order,
               members,
               asts,
               sources,
               interfaces,
               checked_envs
             )
           end),
         {:ok, component_env} <-
           timed(request, :component_merge, timing_metadata, fn ->
             merge_component_environments(prepared, check_order)
           end),
         {:ok, checked} <-
           timed(request, :component_bodies, timing_metadata, fn ->
             check_component_bodies(request, check_order, component, skeletons, prepared, component_env)
           end),
         {:ok, component_interfaces, component_envs} <-
           timed(request, :component_freeze, timing_metadata, fn ->
             freeze_component_interfaces(manifest, component, checked, interfaces)
           end) do
      {:ok, Map.merge(interfaces, component_interfaces), Map.merge(checked_envs, component_envs), checked}
    end
  end

  defp register_component(
         manifest,
         component,
         check_order,
         members,
         asts,
         sources,
         interfaces,
         checked_envs
       ) do
    with {:ok, skeletons} <-
           register_component_type_skeletons(manifest, component, members, asts, interfaces, checked_envs),
         {:ok, component_skeleton} <- merge_environments(skeletons, :component_type_skeleton_merge_failed) do
      register_component_interfaces(
        manifest,
        check_order,
        members,
        asts,
        sources,
        interfaces,
        checked_envs,
        component_skeleton
      )
    end
  end

  defp register_component_type_skeletons(manifest, component, members, asts, interfaces, checked_envs) do
    Enum.reduce_while(component, {:ok, %{}}, fn identity, {:ok, skeletons} ->
      entry = Map.fetch!(manifest.entries, identity)

      with {:ok, imported} <- imported_environment(manifest, identity, interfaces, checked_envs, members),
           {:ok, skeleton} <-
             Program.canonical_type_skeleton(Map.fetch!(asts, identity), imported,
               module_name: entry.module_name,
               module_visibility: module_visibility(manifest, identity)
             ) do
        {:cont, {:ok, Map.put(skeletons, identity, skeleton)}}
      else
        {:error, reason} -> {:halt, {:error, {:module_type_skeleton_failed, identity, reason}}}
      end
    end)
  end

  defp register_component_interfaces(
         manifest,
         component,
         members,
         asts,
         sources,
         interfaces,
         checked_envs,
         component_skeleton
       ) do
    component
    |> Enum.reduce_while({:ok, %{}, component_skeleton}, fn identity, {:ok, prepared, available} ->
      entry = Map.fetch!(manifest.entries, identity)

      with {:ok, imported} <- imported_environment(manifest, identity, interfaces, checked_envs, members),
           {:ok, imported} <- Program.merge_canonical_environments(imported, available),
           {:ok, module} <-
             Program.canonical_register_interface(Map.fetch!(asts, identity), imported,
               module_name: entry.module_name,
               source: Map.fetch!(sources, identity),
               file: entry.source_path,
               module_visibility: module_visibility(manifest, identity)
             ),
           {:ok, available} <-
             Program.merge_canonical_environments(available, module.interface_env) do
        {:cont, {:ok, Map.put(prepared, identity, module), available}}
      else
        {:error, reason} -> {:halt, {:error, {:module_interface_registration_failed, identity, reason}}}
      end
    end)
    |> case do
      {:ok, prepared, _available} -> {:ok, prepared}
      {:error, _reason} = error -> error
    end
  end

  defp merge_component_environments(prepared, check_order) do
    Enum.reduce_while(check_order, {:ok, Env.empty()}, fn identity, {:ok, merged} ->
      environment = prepared |> Map.fetch!(identity) |> Map.fetch!(:interface_env)

      case Program.merge_canonical_environments(merged, environment) do
        {:ok, env} -> {:cont, {:ok, env}}
        {:error, reason} -> {:halt, {:error, {:component_interface_merge_failed, reason}}}
      end
    end)
  end

  defp merge_environments(environments, error_tag) do
    environments
    |> Enum.sort_by(&elem(&1, 0))
    |> Enum.reduce_while({:ok, Env.empty()}, fn {_identity, environment}, {:ok, merged} ->
      case Program.merge_canonical_environments(merged, environment) do
        {:ok, env} -> {:cont, {:ok, env}}
        {:error, reason} -> {:halt, {:error, {error_tag, reason}}}
      end
    end)
  end

  defp check_component_bodies(request, check_order, component, skeletons, prepared, component_env) do
    check_order
    |> Enum.reduce_while({:ok, %{}, component_env}, fn identity, {:ok, checked, available} ->
      module =
        prepared
        |> Map.fetch!(identity)
        |> Program.canonical_install_component_environment(available)

      # A component's members are elaborated against each other's bodies — that
      # is what makes them one component. Recording it here means the graph
      # states the whole truth about which bodies reached which, so a
      # `body_elaboration` edge between two modules that are NOT peers is
      # readable as the defect it is rather than being invisible.
      record_component_body_elaboration(identity, component)

      declaration_timing = fn metadata, elapsed ->
        phase = if Map.has_key?(metadata, :stage), do: :declaration_stage, else: :declaration
        emit_event(request, {:module_pipeline_timing, phase, elapsed, metadata})
      end

      case Program.canonical_check_bodies(module, event_sink: declaration_timing) do
        {:ok, env} ->
          case Program.merge_canonical_environments(available, env) do
            {:ok, available} ->
              {:cont, {:ok, Map.put(checked, identity, env), available}}

            {:error, reason} ->
              {:halt, {:error, Diagnosis.body_failure(identity, Map.get(skeletons, identity), reason)}}
          end

        {:error, reason} ->
          {:halt, {:error, Diagnosis.body_failure(identity, Map.get(skeletons, identity), reason)}}
      end
    end)
    |> case do
      {:ok, checked, _available} -> {:ok, checked}
      {:error, _reason} = error -> error
    end
  end

  # The full dependency graph deliberately groups runtime back-edges into one
  # component, but those edges must not force an arbitrary alphabetical order
  # on interface checking. A lexical `use` is an interface-bearing dependency:
  # its checked names and reducible definitions must be available before the
  # consumer's dependent signatures and bodies. Runtime-only qualified calls
  # remain symbolic and therefore do not reverse this order.
  defp component_check_order(manifest, component) do
    members = MapSet.new(component)

    dependencies =
      Map.new(component, fn identity ->
        required =
          manifest
          |> ModuleManifest.dependencies(identity)
          |> Enum.filter(&(&1.kind in [:use_import, :prelude_symbol_use]))
          |> Enum.map(& &1.target)
          |> Enum.filter(&MapSet.member?(members, &1))
          |> Enum.uniq()
          |> Enum.sort()

        {identity, required}
      end)

    DepGraph.toposort(dependencies, component)
  end

  defp record_component_body_elaboration(identity, component) do
    source = elem(identity, 1)

    for peer <- component, peer != identity do
      BodyElaborationTrace.record(source, elem(peer, 1))
    end

    :ok
  end

  defp freeze_component_interfaces(manifest, component, checked, available_interfaces) do
    provisional =
      Map.new(component, fn identity ->
        entry = Map.fetch!(manifest.entries, identity)
        {identity, Interface.from_checked_env(Map.fetch!(checked, identity), entry, manifest.package, %{})}
      end)

    all_interfaces = Map.merge(available_interfaces, provisional)

    with {:ok, verification_env} <- Interface.environment(all_interfaces) do
      freeze_component_interfaces(
        manifest,
        component,
        checked,
        all_interfaces,
        verification_env
      )
    end
  end

  defp freeze_component_interfaces(
         manifest,
         component,
         checked,
         all_interfaces,
         verification_env
       ) do
    Enum.reduce_while(component, {:ok, %{}, %{}}, fn identity, {:ok, interfaces, envs} ->
      entry = Map.fetch!(manifest.entries, identity)
      hashes = dependency_hashes(manifest, identity, all_interfaces)
      interface = Interface.from_checked_env(Map.fetch!(checked, identity), entry, manifest.package, hashes)

      with :ok <- Interface.verify(interface, verification_env),
           {:ok, interface_env} <- Interface.to_env(interface) do
        {:cont, {:ok, Map.put(interfaces, identity, interface), Map.put(envs, identity, interface_env)}}
      else
        {:error, reason} -> {:halt, {:error, {:module_interface_freeze_failed, identity, reason}}}
      end
    end)
  end

  defp interface_environments(interfaces) do
    Enum.reduce_while(interfaces, {:ok, %{}}, fn {module_name, interface}, {:ok, envs} ->
      case Interface.to_env(interface) do
        {:ok, env} -> {:cont, {:ok, Map.put(envs, module_name, env)}}
        {:error, reason} -> {:halt, {:error, {:invalid_interface_environment, module_name, reason}}}
      end
    end)
  end

  defp external_interface_table(manifest, interfaces),
    do: Map.new(interfaces, fn {module_name, interface} -> {{manifest.package, module_name}, interface} end)

  defp external_env_table(manifest, envs),
    do: Map.new(envs, fn {module_name, env} -> {{manifest.package, module_name}, env} end)

  defp module_visibility(manifest, identity) do
    dependencies = ModuleManifest.dependencies(manifest, identity)

    lexical =
      dependencies
      |> Enum.filter(&(&1.kind in [:use_import, :prelude_symbol_use]))
      |> MapSet.new(&elem(&1.target, 1))

    ambient =
      dependencies
      |> Enum.filter(&(&1.kind == :prelude_symbol_use))
      |> MapSet.new(&elem(&1.target, 1))

    qualified =
      dependencies
      |> MapSet.new(&elem(&1.target, 1))

    %{lexical: lexical, qualified: qualified, ambient: ambient}
  end

  defp dependency_order(manifest) do
    identities = manifest.entries |> Map.keys() |> Enum.sort()
    {_visited, order} = Enum.reduce(identities, {MapSet.new(), []}, &visit_dependency(&1, manifest, &2))
    Enum.reverse(order)
  end

  defp visit_dependency(identity, manifest, {visited, order}) do
    if MapSet.member?(visited, identity) do
      {visited, order}
    else
      visited = MapSet.put(visited, identity)

      {visited, order} =
        manifest
        |> ModuleManifest.dependencies(identity)
        |> Enum.map(& &1.target)
        |> Enum.filter(&Map.has_key?(manifest.entries, &1))
        |> Enum.sort()
        |> Enum.reduce({visited, order}, &visit_dependency(&1, manifest, &2))

      {visited, [identity | order]}
    end
  end

  # A published interface is only self-contained together with what it names. A
  # method signature written `Std.Bool.Bool` has to lower in the *consumer's*
  # environment, and the consumer never wrote that name — so what a module can
  # check against is its dependencies' interfaces closed under their own
  # dependencies. Visibility is decided separately and is not widened by this:
  # being present in the environment is not the same as being in scope.
  defp imported_environment(manifest, identity, interfaces, checked_envs, excluded) do
    manifest
    |> compiled_dependencies(identity)
    |> reachable_environment_dependencies(manifest, interfaces)
    |> MapSet.to_list()
    |> Enum.reject(&MapSet.member?(excluded, &1))
    |> Enum.sort()
    |> Enum.reduce_while({:ok, Env.empty()}, fn dependency, {:ok, imported} ->
      case Map.fetch(checked_envs, dependency) do
        {:ok, dependency_env} ->
          case Program.merge_canonical_environments(imported, dependency_env) do
            {:ok, merged} -> {:cont, {:ok, merged}}
            {:error, reason} -> {:halt, {:error, reason}}
          end

        :error ->
          {:halt, {:error, {:interface_dependency_unavailable, identity, dependency}}}
      end
    end)
  end

  # Source entries and loaded interfaces are nodes in the same semantic graph.
  # A focused build may have only the requester in the source manifest, so once
  # the walk reaches an interface node its recorded direct edges are the sole
  # canonical account of the declarations needed to interpret that interface.
  # This expands availability only; `module_visibility/2` still derives lexical
  # scope exclusively from the requester's own manifest edges.
  defp reachable_environment_dependencies(roots, manifest, interfaces) do
    reachable_environment_dependencies(roots, manifest, interfaces, MapSet.new())
  end

  defp reachable_environment_dependencies([], _manifest, _interfaces, seen), do: seen

  defp reachable_environment_dependencies([identity | rest], manifest, interfaces, seen) do
    if MapSet.member?(seen, identity) do
      reachable_environment_dependencies(rest, manifest, interfaces, seen)
    else
      dependencies = environment_dependencies(manifest, interfaces, identity)

      reachable_environment_dependencies(
        dependencies ++ rest,
        manifest,
        interfaces,
        MapSet.put(seen, identity)
      )
    end
  end

  defp environment_dependencies(manifest, interfaces, identity) do
    if Map.has_key?(manifest.entries, identity) do
      compiled_dependencies(manifest, identity)
    else
      case Map.fetch(interfaces, identity) do
        {:ok, interface} ->
          provided = MapSet.new(Builtins.provided_modules())

          interface.direct_edges
          |> Enum.map(&{manifest.package, &1.target})
          |> Enum.uniq()
          |> Enum.reject(&MapSet.member?(provided, elem(&1, 1)))

        :error ->
          []
      end
    end
  end

  defp dependency_hashes(manifest, identity, interfaces) do
    manifest
    |> compiled_dependencies(identity)
    |> Map.new(fn dependency ->
      interface = Map.fetch!(interfaces, dependency)
      {elem(dependency, 1), interface.interface_hash}
    end)
  end

  # A module may name something the compiler provides rather than compiles.
  # There is no interface to import and no hash to record against it: it is part
  # of the floor every module already starts from, so it is dropped here — once,
  # rather than at each place that would otherwise fail to find it.
  defp compiled_dependencies(manifest, identity) do
    provided = MapSet.new(Builtins.provided_modules())

    manifest
    |> ModuleManifest.dependencies(identity)
    |> Enum.map(& &1.target)
    |> Enum.uniq()
    |> Enum.reject(&MapSet.member?(provided, elem(&1, 1)))
  end

  defp strongly_connected_components(manifest) do
    order = dependency_order(manifest)

    Enum.reduce(order, [], fn identity, components ->
      if Enum.any?(components, &(identity in &1)) do
        components
      else
        forward = reachable_modules(manifest, identity)

        component =
          order
          |> Enum.filter(fn candidate ->
            MapSet.member?(forward, candidate) and
              MapSet.member?(reachable_modules(manifest, candidate), identity)
          end)
          |> Enum.sort()

        components ++ [component]
      end
    end)
    |> condensation_order(manifest)
  end

  # Grouping and ordering are two questions, and only the first is answered by
  # mutual reachability. A depth-first post-order over the module graph is a
  # dependency order only when that graph is acyclic, so once the cycles are
  # collapsed the components are ordered again over the condensation — which is
  # acyclic by construction — instead of inheriting the order their members
  # happened to be discovered in.
  defp condensation_order(components, manifest) do
    indexed = components |> Enum.with_index() |> Map.new(fn {component, index} -> {index, component} end)

    owner =
      for {index, component} <- indexed, identity <- component, into: %{}, do: {identity, index}

    edges =
      Map.new(indexed, fn {index, component} ->
        targets =
          component
          |> Enum.flat_map(&(manifest |> ModuleManifest.dependencies(&1) |> Enum.map(fn edge -> edge.target end)))
          |> Enum.filter(&Map.has_key?(owner, &1))
          |> Enum.map(&Map.fetch!(owner, &1))
          |> Enum.reject(&(&1 == index))
          |> Enum.uniq()
          |> Enum.sort()

        {index, targets}
      end)

    {_visited, order} =
      indexed |> Map.keys() |> Enum.sort() |> Enum.reduce({MapSet.new(), []}, &visit_component(&1, edges, &2))

    order |> Enum.reverse() |> Enum.map(&Map.fetch!(indexed, &1))
  end

  defp visit_component(index, edges, {visited, order}) do
    if MapSet.member?(visited, index) do
      {visited, order}
    else
      {visited, order} =
        Enum.reduce(Map.fetch!(edges, index), {MapSet.put(visited, index), order}, &visit_component(&1, edges, &2))

      {visited, [index | order]}
    end
  end

  defp reachable_modules(manifest, root), do: reachable_modules(manifest, [root], MapSet.new())
  defp reachable_modules(_manifest, [], seen), do: seen

  defp reachable_modules(manifest, [identity | rest], seen) do
    if MapSet.member?(seen, identity) do
      reachable_modules(manifest, rest, seen)
    else
      dependencies =
        manifest
        |> ModuleManifest.dependencies(identity)
        |> Enum.map(& &1.target)
        |> Enum.filter(&Map.has_key?(manifest.entries, &1))

      reachable_modules(manifest, dependencies ++ rest, MapSet.put(seen, identity))
    end
  end

  defp resolve_qualified(result, namespace, written_name) do
    parts = String.split(written_name, ".")
    declaration_name = List.last(parts)
    module_name = parts |> Enum.drop(-1) |> Enum.join(".")

    with {:ok, skeleton} <- fetch_skeleton(result, module_name),
         {:ok, declaration} <- fetch_declaration(skeleton, namespace, declaration_name),
         :ok <- require_public(declaration) do
      {:ok, declaration.key}
    end
  end

  # Lexical candidates are tiered, not pooled. A direct `use` outranks the
  # ambient prelude, so a provider that merely happens to be ambient can never
  # make an explicitly imported name ambiguous. Ambiguity is only ever reported
  # within one tier.
  defp resolve_bare(result, requesting_module, namespace, name) do
    with {:ok, requester} <- fetch_skeleton(result, requesting_module) do
      case Map.fetch(requester.declarations, {namespace, name}) do
        {:ok, declaration} ->
          {:ok, declaration.key}

        :error ->
          dependencies = ModuleManifest.dependencies(result.manifest, requesting_module)

          [:use_import, :prelude_symbol_use]
          |> Enum.map(&lexical_candidates(result, dependencies, &1, namespace, name))
          |> Enum.find([], &(&1 != []))
          |> resolve_candidates(name)
      end
    end
  end

  defp lexical_candidates(result, dependencies, kind, namespace, name) do
    dependencies
    |> Enum.filter(&(&1.kind == kind))
    |> Enum.flat_map(fn dependency ->
      case Map.fetch(result.skeletons, dependency.target) do
        {:ok, skeleton} -> exported_declarations(result, skeleton, namespace, name)
        :error -> []
      end
    end)
    |> Enum.uniq_by(& &1.key)
  end

  # `use M` exposes what `M` owns and exports, plus what `M` explicitly
  # reexports with `public use`. It never exposes `M`'s ordinary imports.
  defp exported_declarations(result, skeleton, namespace, name, seen \\ MapSet.new()) do
    cond do
      MapSet.member?(seen, skeleton.identity) ->
        []

      match?(%{visibility: :public}, Map.get(skeleton.declarations, {namespace, name})) ->
        [Map.fetch!(skeleton.declarations, {namespace, name})]

      true ->
        seen = MapSet.put(seen, skeleton.identity)
        package = elem(skeleton.identity, 0)

        Enum.flat_map(skeleton.reexports, fn module_name ->
          case Map.fetch(result.skeletons, {package, module_name}) do
            {:ok, reexported} -> exported_declarations(result, reexported, namespace, name, seen)
            :error -> []
          end
        end)
    end
  end

  defp resolve_candidates([], _name), do: {:error, :not_in_lexical_scope}
  defp resolve_candidates([declaration], _name), do: {:ok, declaration.key}

  defp resolve_candidates(declarations, name) do
    {:error, {:ambiguous_name, name, declarations |> Enum.map(& &1.key) |> Enum.sort()}}
  end

  defp fetch_skeleton(%Result{request: request, skeletons: skeletons}, module_name) do
    identity = {request.package || "root", module_name}

    case Map.fetch(skeletons, identity) do
      {:ok, skeleton} -> {:ok, skeleton}
      :error -> {:error, {:module_unavailable, identity}}
    end
  end

  defp fetch_declaration(skeleton, namespace, name) do
    case Map.fetch(skeleton.declarations, {namespace, name}) do
      {:ok, declaration} -> {:ok, declaration}
      :error -> {:error, {:declaration_unavailable, skeleton.identity, namespace, name}}
    end
  end

  defp require_public(%{visibility: :public}), do: :ok
  defp require_public(%{visibility: :private}), do: {:error, :private_declaration}
end
