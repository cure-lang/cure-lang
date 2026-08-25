defmodule Cure.Compiler.PortableClosure do
  @moduledoc """
  Audits the actual BEAM import closure of a packaged Cure surface.

  A source grep is not enough for portability: generated calls and imported
  helpers only become visible after emission. This module starts at the
  package's declared exports, follows the imports recorded in each verified
  BEAM, and reports forbidden host/runtime capabilities reached by that exact
  closure. It is deliberately outside the compiler TCB and is suitable for
  release gates and tests.
  """

  alias Cure.Compiler.Artifacts

  @type beam_mfa :: {atom(), atom(), non_neg_integer()}
  @type edge :: {binary(), beam_mfa()}
  @type report :: %{
          package: binary(),
          roots: [binary()],
          modules: [binary()],
          edges: [edge()],
          forbidden: [%{from: binary(), mfa: beam_mfa(), reason: atom()}],
          nifs: [binary()]
        }

  @host_regex_modules MapSet.new([
                        :re,
                        :pcre,
                        :pcres,
                        :pcres_elixir,
                        :erl_scan,
                        :erl_parse,
                        :elixir_parser,
                        :"Elixir.Regex",
                        :"Elixir.PCRE",
                        :"Elixir.PCRE2",
                        :"Elixir.Code"
                      ])

  @ets_modules MapSet.new([:ets, :dets, :persistent_term])

  @process_functions MapSet.new([
                       :apply,
                       :cancel_timer,
                       :demonitor,
                       :disconnect_node,
                       :exit,
                       :group_leader,
                       :hibernate,
                       :link,
                       :monitor,
                       :monitor_node,
                       :process_flag,
                       :put,
                       :register,
                       :registered,
                       :send,
                       :self,
                       :spawn,
                       :spawn_link,
                       :spawn_monitor,
                       :spawn_opt,
                       :unregister,
                       :whereis
                     ])

  @port_functions MapSet.new([
                    :open_port,
                    :port_command,
                    :port_close,
                    :port_connect,
                    :port_control,
                    :port_call,
                    :port_close,
                    :port_get_data,
                    :port_set_data
                  ])

  @doc "Audit the package exports in a verified artifact root."
  @spec audit(Path.t(), keyword()) :: {:ok, report()} | {:error, term()}
  def audit(root, opts \\ []) when is_binary(root) do
    with {:ok, set} <- Artifacts.open_verified_set(root, verification: :full) do
      audit_set(set, opts)
    end
  end

  @doc "Audit an already opened verified artifact set."
  @spec audit_set(map(), keyword()) :: {:ok, report()} | {:error, term()}
  def audit_set(%{modules: modules, context: context} = set, opts) when is_map(modules) do
    package = Keyword.get(opts, :package, Map.get(context, :package, "stdlib"))
    exports = Map.get(context, :package_exports, %{})

    with package when is_binary(package) <- package,
         root_names when is_list(root_names) <- Map.get(exports, package, []),
         {:ok, beam_index} <- beam_index(set),
         {:ok, roots} <- resolve_roots(root_names, beam_index) do
      {:ok, walk_closure(package, roots, beam_index)}
    else
      nil -> {:error, {:package_exports_missing, package}}
      [] -> {:error, {:package_exports_missing, package}}
      {:error, _} = error -> error
      _ -> {:error, {:package_exports_missing, package}}
    end
  end

  @doc "Whether an imported MFA is forbidden in a portable regex closure."
  @spec forbidden_mfa?(beam_mfa()) :: false | atom()
  def forbidden_mfa?({module, function, _arity}) when is_atom(module) and is_atom(function) do
    cond do
      MapSet.member?(@host_regex_modules, module) -> :host_regex_or_parser
      MapSet.member?(@ets_modules, module) -> :ets_or_process_global_state
      module == :erlang and MapSet.member?(@process_functions, function) -> :process
      module == :erlang and MapSet.member?(@port_functions, function) -> :port
      module == :erlang and function in [:nif_error, :load_nif] -> :nif
      module == :code -> :dynamic_code_loading
      true -> false
    end
  end

  defp beam_index(%{modules: modules, artifact_root: root}) do
    entries =
      Enum.map(modules, fn {source, entry} ->
        artifacts = Map.get(entry, :artifacts, [])

        case artifacts do
          [%{path: path} | _] ->
            beam_path = Path.join(root, path)

            case :beam_lib.chunks(String.to_charlist(beam_path), [:imports, :attributes]) do
              {:ok, {beam_module, chunks}} ->
                {:ok, {source, beam_module, beam_path, chunks}}

              {:error, reason} ->
                {:error, {:beam_unreadable, source, reason}}
            end

          _ ->
            {:error, {:beam_artifact_missing, source}}
        end
      end)

    case Enum.find(entries, &match?({:error, _}, &1)) do
      nil ->
        {:ok,
         entries
         |> Map.new(fn {:ok, {source, beam_module, path, chunks}} ->
           {beam_module, %{source: source, path: path, chunks: chunks}}
         end)}

      {:error, _} = error ->
        error
    end
  end

  defp resolve_roots(names, beam_index) do
    roots =
      Enum.map(names, fn source ->
        Enum.find_value(beam_index, fn
          {beam_module, %{source: ^source} = entry} ->
            Map.put(entry, :beam_module, beam_module)

          _ ->
            nil
        end) || %{source: source, beam_module: nil}
      end)

    case Enum.find(roots, &is_nil(&1.beam_module)) do
      nil -> {:ok, Enum.sort_by(roots, & &1.source)}
      %{source: source} -> {:error, {:package_export_artifact_missing, source}}
    end
  end

  defp walk_closure(package, roots, beam_index) do
    result = walk_queue(roots, %{seen: MapSet.new(), edges: [], forbidden: [], nifs: []}, beam_index)

    %{
      package: package,
      roots: Enum.map(roots, & &1.source) |> Enum.sort(),
      modules: result.seen |> Enum.map(&beam_index[&1].source) |> Enum.sort(),
      edges: result.edges |> Enum.uniq() |> Enum.sort(),
      forbidden: result.forbidden |> Enum.uniq() |> Enum.sort_by(&{&1.from, &1.mfa, &1.reason}),
      nifs: Enum.sort(Enum.uniq(result.nifs))
    }
  end

  defp walk_queue([], state, _beam_index), do: state

  defp walk_queue([%{source: source, beam_module: beam_module} = entry | rest], state, beam_index) do
    if MapSet.member?(state.seen, beam_module) do
      walk_queue(rest, state, beam_index)
    else
      state = inspect_module(source, beam_module, entry, state, beam_index)
      queue = Map.get(state, :queue, [])
      walk_queue(queue ++ rest, Map.delete(state, :queue), beam_index)
    end
  end

  defp inspect_module(source, beam_module, entry, state, beam_index) do
    chunks = entry.chunks
    imports = Keyword.get(chunks, :imports, [])
    attrs = Keyword.get(chunks, :attributes, [])
    nifs? = Keyword.get(attrs, :nifs, [])

    state = Map.put(%{state | seen: MapSet.put(state.seen, beam_module)}, :queue, [])
    state = if nifs? == [], do: state, else: %{state | nifs: [source | state.nifs]}

    Enum.reduce(imports, state, fn mfa, acc ->
      acc =
        case forbidden_mfa?(mfa) do
          false -> acc
          reason -> %{acc | forbidden: [%{from: source, mfa: mfa, reason: reason} | acc.forbidden]}
        end

      {module, _function, _arity} = mfa

      case Map.get(beam_index, module) do
        nil ->
          acc

        %{source: target_source} = target ->
          %{
            acc
            | edges: [{source, mfa} | acc.edges],
              queue:
                acc.queue ++
                  [
                    target
                    |> Map.put(:source, target_source)
                    |> Map.put(:beam_module, module)
                  ]
          }
      end
    end)
  end
end
