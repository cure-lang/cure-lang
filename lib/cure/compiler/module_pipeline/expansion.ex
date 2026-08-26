defmodule Cure.Compiler.ModulePipeline.Expansion do
  @moduledoc """
  Parses the universe to a stable syntax set.

  Parsing one module is not a self-contained act when macros cross module
  boundaries. A macro's grammar has to be active for its use-sites to be
  use-sites at all, so a module that `use`s a provider must be parsed with that
  provider's rules in hand — otherwise its macro invocations are quietly parsed
  as something else and the declarations they would have produced never exist.
  And once a use-site does expand, the template can name modules the header scan
  never saw, because that text lives in the provider's file. Those references
  extend the universe, which can bring in another provider, which can expand
  again.

  So this runs rounds, exactly as the interface-first design describes (§7.3):
  parse everything with the rules known so far, collect what expansion revealed,
  fold the new references into the manifest, and go again until a round reveals
  nothing new. A universe with no cross-module macros stabilises in one round;
  one where a macro generated a reference needs at least two, and the count is
  reported rather than assumed so "expansion reached a fixpoint" is something a
  caller can check instead of trust.
  """

  alias Cure.Compiler.{Lexer, ModuleManifest, ModuleSkeleton, Parser}
  alias Cure.Compiler.Parser.FixityScan
  alias Cure.MetaAST.Metadata

  # Expansion that has not stabilised by here is not slow, it is looping: each
  # round can only add references, and a universe has finitely many modules.
  @max_rounds 16

  @type t :: %{
          manifest: ModuleManifest.t(),
          skeletons: %{ModuleManifest.identity() => ModuleSkeleton.t()},
          asts: %{ModuleManifest.identity() => term()},
          sources: %{ModuleManifest.identity() => String.t()},
          generated: [ModuleManifest.dependency()],
          rounds: pos_integer()
        }

  @spec run(ModuleManifest.t(), keyword()) :: {:ok, t()} | {:error, term()}
  def run(%ModuleManifest{} = manifest, manifest_options) do
    run(manifest, manifest_options, 1, [])
  end

  defp run(manifest, manifest_options, round, generated) do
    with {:ok, units} <- parse_units(manifest, manifest_options) do
      case discovered_references(manifest, units) do
        [] ->
          {:ok, finish(manifest, units, generated, round)}

        _discovered when round >= @max_rounds ->
          {:error, {:macro_expansion_did_not_stabilize, %{rounds: round, modules: Map.keys(units)}}}

        discovered ->
          case ModuleManifest.extend(manifest, discovered, manifest_options) do
            {:ok, extended} -> run(extended, manifest_options, round + 1, generated ++ discovered)
            {:error, _} = error -> error
          end
      end
    end
  end

  defp finish(manifest, units, generated, rounds) do
    %{
      manifest: manifest,
      skeletons: Map.new(units, fn {identity, unit} -> {identity, unit.skeleton} end),
      asts: Map.new(units, fn {identity, unit} -> {identity, unit.ast} end),
      sources: Map.new(units, fn {identity, unit} -> {identity, unit.source} end),
      generated: Enum.uniq_by(generated, &{&1.source, &1.target}),
      rounds: rounds
    }
  end

  @doc """
  The expanded syntax of every module, with source positions and provenance
  gone.

  Expansion is supposed to be a function of the source and the active grammar
  and of nothing else — not of how the expander happened to be executed. That is
  only checkable if there is one rendering both executions can be compared
  through, which is what this is.
  """
  @spec syntax_dump(%{ModuleManifest.identity() => term()}) :: [{String.t(), term()}]
  def syntax_dump(asts) when is_map(asts) do
    asts
    |> Enum.sort_by(&elem(&1, 0))
    |> Enum.map(fn {identity, ast} -> {elem(identity, 1), Metadata.strip_diagnostics(ast)} end)
  end

  @doc """
  The hygienic names expansion minted, grouped by the declaration they landed
  in.

  A gensym is `name$counter`, so the names themselves say nothing about which
  expansion produced them; the grouping is what makes hygiene measurable rather
  than merely plausible. Declarations are the grouping because a parse-time
  template carries no expansion provenance to group by, and a template that
  expands in declaration position produces exactly one declaration per use-site.
  """
  @spec fresh_name_groups(%{ModuleManifest.identity() => term()}) :: [{String.t(), String.t(), [String.t()]}]
  def fresh_name_groups(asts) when is_map(asts) do
    asts
    |> Enum.sort_by(&elem(&1, 0))
    |> Enum.flat_map(fn {identity, ast} ->
      ast
      |> top_level_declarations()
      |> Enum.map(fn {name, node} -> {elem(identity, 1), name, fresh_names(node)} end)
      |> Enum.reject(fn {_module, _name, names} -> names == [] end)
    end)
  end

  @doc """
  True when no two declarations share a minted name.

  Sibling expansions of one macro are independent instances: if two of them
  could reach the same binder, a name introduced by the template would capture
  across use-sites, which is precisely the hygiene failure freshening exists to
  prevent.
  """
  @spec sibling_expansions_disjoint?(%{ModuleManifest.identity() => term()}) :: boolean()
  def sibling_expansions_disjoint?(asts) when is_map(asts) do
    groups = fresh_name_groups(asts)
    minted = Enum.flat_map(groups, fn {_module, _name, names} -> names end)

    length(minted) == length(Enum.uniq(minted))
  end

  defp top_level_declarations({:container, _meta, children}) when is_list(children),
    do: Enum.flat_map(children, &top_level_declarations/1)

  defp top_level_declarations({:module_def, meta, children}) when is_list(children) do
    prefix = Keyword.get(meta, :name, "")

    children
    |> Enum.flat_map(&top_level_declarations/1)
    |> Enum.map(fn {name, node} -> {prefix <> "." <> name, node} end)
  end

  defp top_level_declarations({tag, meta, _children} = node) when is_atom(tag) and is_list(meta) do
    case Keyword.get(meta, :name) do
      name when is_binary(name) -> [{"#{tag}:#{name}", node}]
      _ -> []
    end
  end

  defp top_level_declarations(list) when is_list(list), do: Enum.flat_map(list, &top_level_declarations/1)
  defp top_level_declarations(_node), do: []

  defp fresh_names(node) do
    node
    |> collect_variables(MapSet.new())
    |> Enum.filter(&Regex.match?(~r/\$\d+$/, &1))
    |> Enum.sort()
  end

  defp collect_variables({:variable, _meta, name}, acc) when is_binary(name), do: MapSet.put(acc, name)

  defp collect_variables(%_{}, acc), do: acc

  defp collect_variables(node, acc) when is_map(node),
    do: Enum.reduce(node, acc, fn {_key, value}, acc -> collect_variables(value, acc) end)

  defp collect_variables(node, acc) when is_tuple(node),
    do: node |> Tuple.to_list() |> Enum.reduce(acc, &collect_variables/2)

  defp collect_variables(node, acc) when is_list(node), do: Enum.reduce(node, acc, &collect_variables/2)
  defp collect_variables(_node, acc), do: acc

  # Providers before consumers, so a module is parsed only once every macro it
  # can see has been harvested. A cycle among macro providers has no such order;
  # its members are parsed with whatever their peers published in an earlier
  # round, which is the same answer the round loop converges on anyway.
  defp parse_units(manifest, manifest_options) do
    manifest.entries
    |> Map.values()
    |> Enum.sort_by(& &1.identity)
    |> provider_order(manifest)
    |> Enum.reduce_while({:ok, %{}, %{}}, fn entry, {:ok, units, rules} ->
      imported = imported_rules(manifest, entry.identity, rules)
      imported_fixity = imported_fixity(manifest, entry.identity)

      case parse_unit(entry, imported, imported_fixity, manifest_options) do
        {:ok, unit} ->
          {:cont, {:ok, Map.put(units, entry.identity, unit), Map.put(rules, entry.identity, unit.rules)}}

        {:error, reason} ->
          {:halt, {:error, {:module_skeleton_error, entry.identity, reason}}}
      end
    end)
    |> case do
      {:ok, units, _rules} -> {:ok, units}
      {:error, _} = error -> error
    end
  end

  defp parse_unit(entry, imported, imported_fixity, manifest_options) do
    with {:ok, source} <- File.read(entry.source_path),
         {:ok, edition} <- source_edition(source, manifest_options),
         {:ok, tokens} <- Lexer.tokenize(source, file: entry.source_path, emit_events: false, edition: edition),
         {:ok, ast} <-
           Parser.parse(tokens,
             file: entry.source_path,
             emit_events: false,
             edition: edition,
             imported_macros: imported,
             imported_fixity: imported_fixity
           ) do
      {:ok,
       %{
         ast: ast,
         source: source,
         skeleton: ModuleSkeleton.collect(ast, entry.identity, entry.source_path),
         rules: Parser.macro_rules(ast, entry.source_path)
       }}
    end
  end

  defp source_edition(source, manifest_options) do
    case Cure.Edition.pragma_edition(source) do
      nil -> {:ok, Keyword.get(manifest_options, :edition, Cure.Edition.current())}
      edition -> Cure.Edition.parse(edition) |> wrap_edition_error()
    end
  end

  defp wrap_edition_error({:ok, edition}), do: {:ok, edition}
  defp wrap_edition_error({:error, reason}), do: {:error, {:edition_error, reason}}

  defp imported_fixity(manifest, identity) do
    manifest
    |> dependency_closure(identity, MapSet.new())
    |> MapSet.delete(identity)
    |> Enum.sort()
    |> Enum.flat_map(fn dependency ->
      case Map.fetch(manifest.entries, dependency) do
        {:ok, entry} -> entry.fixity
        :error -> []
      end
    end)
  end

  defp dependency_closure(manifest, identity, seen) do
    if MapSet.member?(seen, identity) do
      seen
    else
      seen = MapSet.put(seen, identity)

      manifest
      |> ModuleManifest.dependencies(identity)
      |> Enum.map(& &1.target)
      |> Enum.filter(&Map.has_key?(manifest.entries, &1))
      |> Enum.reduce(seen, &dependency_closure(manifest, &1, &2))
    end
  end

  defp imported_rules(manifest, identity, harvested) do
    manifest
    |> ModuleManifest.dependencies(identity)
    |> Enum.map(& &1.target)
    |> Enum.uniq()
    |> Enum.sort()
    |> Enum.reduce(%{}, fn target, acc ->
      Map.merge(acc, Map.get(harvested, target, %{}), fn _keyword, left, right -> Enum.uniq(left ++ right) end)
    end)
  end

  # A reference the expanded syntax names that the manifest does not record. The
  # target has to be a module of this universe: a template may mention anything,
  # and a name that resolves nowhere is a checking error to report against the
  # use-site, not a manifest entry to invent.
  defp discovered_references(manifest, units) do
    Enum.flat_map(units, fn {identity, unit} ->
      known =
        manifest
        |> ModuleManifest.dependencies(identity)
        |> MapSet.new(& &1.target)

      unit.ast
      |> FixityScan.collect_qualified_targets(FixityScan.collect_uses(unit.ast))
      |> Enum.map(fn reference ->
        %{
          kind: :qualified_reference,
          source: identity,
          target: {manifest.package, reference.target},
          span: %{path: unit.skeleton.source_path, line: reference.line}
        }
      end)
      |> Enum.reject(
        &(&1.target == identity or MapSet.member?(known, &1.target) or
            not Map.has_key?(manifest.entries, &1.target))
      )
    end)
  end

  defp provider_order(entries, manifest) do
    entries
    |> Enum.map(& &1.identity)
    |> visit(manifest, MapSet.new(), [])
    |> Enum.reverse()
    |> Enum.map(&Map.fetch!(manifest.entries, &1))
  end

  defp visit([], _manifest, _visiting, ordered), do: ordered

  defp visit([identity | rest], manifest, visiting, ordered) do
    cond do
      Enum.member?(ordered, identity) or MapSet.member?(visiting, identity) ->
        visit(rest, manifest, visiting, ordered)

      true ->
        dependencies =
          manifest
          |> ModuleManifest.dependencies(identity)
          |> Enum.map(& &1.target)
          |> Enum.filter(&Map.has_key?(manifest.entries, &1))
          |> Enum.uniq()
          |> Enum.sort()

        ordered = visit(dependencies, manifest, MapSet.put(visiting, identity), ordered)
        visit(rest, manifest, visiting, [identity | ordered])
    end
  end
end
