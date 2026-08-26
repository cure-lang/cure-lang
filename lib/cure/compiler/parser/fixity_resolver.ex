defmodule Cure.Compiler.Parser.FixityResolver do
  @moduledoc """
  Assemble `fixity(M) = base ∪ ⋃ own(X) over use_reach(M) ∪ own(M) ∪ user
  prelude providers`, resolving the `use`-closure on demand by name (no
  precomputed DepGraph). Groups are merged before operators; a same-lexeme/
  different-group or same-name/different-body clash is a hard conflict.
  Reachability uses set-union, so `use` cycles need no special handling.
  Target modules are scanned with the tolerant harvest only — never a full
  `Parser.parse` — so this never recurses into itself.
  """

  alias Cure.Compiler.Parser.{FixityTable, FixityScan}
  alias Cure.Compiler.SourceResolver
  alias Cure.Diagnostic.Span
  alias Cure.MetaAST.SourceInfo

  @spec assemble(FixityTable.t(), [tuple()], [String.t()], [String.t()], keyword()) ::
          {:ok, FixityTable.t()} | {:error, term()}
  def assemble(base, own_fixity, own_uses, prelude_providers, opts \\ []) do
    seeds = Enum.uniq(own_uses ++ prelude_providers)
    imported_fixity = Keyword.get(opts, :imported_fixity, [])

    with {:ok, reached_fixity} <- gather(seeds, MapSet.new(), [], base) do
      # own(M) is folded LAST so M's own declarations are still subject to the
      # same conflict rule against everything it imports.
      fold(base, reached_fixity ++ imported_fixity ++ own_fixity)
    end
  end

  # BFS over the use-closure, accumulating each reached module's own fixity
  # nodes. `base` seeds each target's harvest so built-in operators in the
  # target's bodies don't misparse (Component 1).
  defp gather([], _seen, acc, _base), do: {:ok, acc}

  defp gather([name | rest], seen, acc, base) do
    if MapSet.member?(seen, name) do
      gather(rest, seen, acc, base)
    else
      seen = MapSet.put(seen, name)

      case SourceResolver.module_path(name) do
        {:ok, path} ->
          case cached_harvest(path, base) do
            {:ok, scan} ->
              next = rest ++ Enum.map(scan.uses, & &1.target)
              gather(next, seen, acc ++ scan.fixity, base)

            :error ->
              gather(rest, seen, acc, base)
          end

        :not_found ->
          gather(rest, seen, acc, base)
      end
    end
  end

  # A parser process commonly checks many small sources against the same
  # imported/prelude closure (diagnostic corpora and generated properties are
  # the standing examples). The closure's source files and base fixity table are
  # immutable for that process, so harvesting every transitive module for every
  # parse is pure repeated work. Include file identity and the base table in the
  # key so edited fixtures and alternate editions cannot reuse a stale scan.
  defp cached_harvest(path, base) do
    stat =
      case File.stat(path, time: :posix) do
        {:ok, %File.Stat{size: size, mtime: mtime}} -> {size, mtime}
        _ -> :nostat
      end

    key = {__MODULE__, :harvest, path, stat, :erlang.phash2(base)}

    case Process.get(key) do
      nil ->
        result =
          case File.read(path) do
            {:ok, source} -> {:ok, FixityScan.harvest_source(source, diagnostic_source_path(path), base)}
            {:error, _} -> :error
          end

        Process.put(key, result)
        result

      cached ->
        cached
    end
  end

  # Groups first (ops reference them), then operators. Short-circuit on conflict.
  defp fold(base, nodes) do
    groups = Enum.filter(nodes, &match?({:precedencegroup, _, _}, &1))
    ops = Enum.filter(nodes, &match?({:fixity, _, _}, &1))

    initial = %{table: base, origins: %{}}

    with {:ok, state1} <- reduce_merge(initial, groups),
         {:ok, state2} <- reduce_merge(state1, ops) do
      {:ok, state2.table}
    end
  end

  defp reduce_merge(state, nodes) do
    Enum.reduce_while(nodes, {:ok, state}, fn node, {:ok, current} ->
      case merge_node(current, node) do
        {:ok, next} -> {:cont, {:ok, next}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp merge_node(%{table: table} = state, {:precedencegroup, meta, _}) when is_list(meta) do
    name = Keyword.fetch!(meta, :name)
    key = {:group, name}

    case FixityTable.merge_group(table, name,
           assoc: Keyword.get(meta, :assoc, :left),
           higher_than: Keyword.get(meta, :higher_than, []),
           lower_than: Keyword.get(meta, :lower_than, [])
         ) do
      {:ok, next} ->
        {:ok, remember_origin(state, next, key, declaration_span(meta, :name))}

      {:error, {:conflicting_precedence_group, {^name, existing, new}}} ->
        {:error,
         {:conflicting_precedence_group,
          %{
            name: name,
            existing: existing,
            new: new,
            spans: conflict_spans(state, key, declaration_span(meta, :name))
          }}}
    end
  end

  defp merge_node(%{table: table} = state, {:fixity, meta, _}) when is_list(meta) do
    lexeme = Keyword.get(meta, :operator)
    group = Keyword.get(meta, :group)
    fixity = Keyword.get(meta, :fixity)

    if is_binary(lexeme) and is_atom(group) and not is_nil(group) and
         fixity in [:infix, :prefix, :postfix] do
      key = {:operator, lexeme, fixity}

      case FixityTable.merge_op(table, lexeme, fixity, group) do
        {:ok, next} ->
          {:ok, remember_origin(state, next, key, declaration_span(meta, :operator))}

        {:error, {:conflicting_operator_fixity, {^lexeme, existing_group, ^group}}} ->
          {:error,
           {:conflicting_operator_fixity,
            %{
              operator: lexeme,
              fixity: fixity,
              existing_group: existing_group,
              new_group: group,
              spans: conflict_spans(state, key, declaration_span(meta, :operator))
            }}}
      end
    else
      {:ok, state}
    end
  end

  defp merge_node(state, _), do: {:ok, state}

  defp remember_origin(state, table, key, %Span{} = span),
    do: %{state | table: table, origins: Map.put_new(state.origins, key, span)}

  defp remember_origin(state, table, _key, _span), do: %{state | table: table}

  defp conflict_spans(state, key, incoming) do
    [Map.get(state.origins, key), incoming]
    |> Enum.filter(&match?(%Span{}, &1))
    |> Enum.uniq()
  end

  defp declaration_span(meta, role) do
    case Keyword.get(meta, :source_info) do
      %SourceInfo{} = info -> Map.get(info, role) || info.whole
      _ -> nil
    end
  end

  defp diagnostic_source_path(path) do
    expanded = Path.expand(path)

    if Enum.any?(Cure.Stdlib.Paths.source_dirs(), fn root ->
         root = Path.expand(root)
         expanded == root or String.starts_with?(expanded, root <> "/")
       end) do
      Path.join(["lib", "std", Path.basename(path)])
    else
      path
    end
  end
end
