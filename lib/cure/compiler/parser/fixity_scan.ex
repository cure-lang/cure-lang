defmodule Cure.Compiler.Parser.FixityScan do
  @moduledoc """
  Table-independent structural extraction from Cure source. Given a module's
  source (or an already-harvested node list), reports its own fixity /
  precedence-group declarations, `use` targets, `@prelude` flag, and module
  name — WITHOUT requiring a fully successful parse of its function bodies.
  Declarations are inert (their parse never consults the fixity table), so
  `synchronize_to_statement` recovery inside the harvest pass guarantees they
  survive even when surrounding expressions misparse.
  """

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Compiler.Parser.FixityTable

  @empty %{fixity: [], uses: [], qualified_targets: [], prelude?: false, module: nil}

  @spec harvest_source(String.t(), String.t(), FixityTable.t()) :: %{
          fixity: [tuple()],
          uses: [%{target: String.t(), line: pos_integer()}],
          qualified_targets: [%{target: String.t(), line: pos_integer()}],
          prelude?: boolean(),
          module: String.t() | nil
        }
  def harvest_source(source, file, base) do
    case Lexer.tokenize(source, file: file, emit_events: false) do
      {:ok, tokens} ->
        exprs = Parser.harvest(tokens, file, base, Cure.Edition.current())
        facts = collect_module_facts(exprs)
        qualified_targets = normalize_qualified_targets(collect_qualified_targets(exprs), facts.uses)

        %{
          fixity: facts.fixity,
          uses: facts.uses,
          qualified_targets: qualified_targets,
          prelude?: prelude?(exprs),
          module: module_name(exprs)
        }

      _ ->
        @empty
    end
  end

  @spec collect_fixity(term()) :: [tuple()]
  def collect_fixity(ast),
    do:
      deep_collect(ast, fn
        {:fixity, _, _} = n -> [n]
        {:precedencegroup, _, _} = n -> [n]
        _ -> []
      end)

  @doc "Collect a harvested module's fixity declarations and imports in one walk."
  @spec collect_module_facts(term()) :: %{fixity: [tuple()], uses: [%{target: String.t(), line: pos_integer()}]}
  def collect_module_facts(ast) do
    {fixity, uses} = deep_scan(ast, [], [])
    %{fixity: Enum.reverse(fixity), uses: Enum.reverse(uses)}
  end

  @doc "Return exact authored name ranges for the selected precedence groups."
  @spec group_spans(term(), [atom()]) :: [Cure.Diagnostic.Span.t()]
  def group_spans(ast, groups) do
    wanted = MapSet.new(groups)

    ast
    |> collect_fixity()
    |> Enum.flat_map(fn
      {:precedencegroup, meta, _} when is_list(meta) ->
        with name when not is_nil(name) <- Keyword.get(meta, :name),
             true <- MapSet.member?(wanted, name),
             %Cure.MetaAST.SourceInfo{name: %Cure.Diagnostic.Span{} = span} <-
               Keyword.get(meta, :source_info) do
          [span]
        else
          _ -> []
        end

      _ ->
        []
    end)
  end

  @doc """
  Fold the `precedencegroup`/`infix`/`prefix`/`postfix` declarations found in
  `ast` into `base`, returning the extended `FixityTable`. Groups are registered
  first (so `higher_than`/`lower_than` links resolve against groups declared
  later in the same source) then operator lexemes bind to those groups.

  Table-independent: reads only the harvested declaration nodes, never the
  fixity table it is building, so it is safe to call while assembling the
  built-in table at compile time.
  """
  @spec build_table(term(), FixityTable.t()) :: FixityTable.t()
  def build_table(ast, base) do
    nodes = collect_fixity(ast)

    table =
      Enum.reduce(nodes, base, fn
        {:precedencegroup, meta, _}, acc ->
          FixityTable.add_group(acc, Keyword.fetch!(meta, :name),
            assoc: Keyword.get(meta, :assoc, :left),
            higher_than: Keyword.get(meta, :higher_than, []),
            lower_than: Keyword.get(meta, :lower_than, [])
          )

        _other, acc ->
          acc
      end)

    Enum.reduce(nodes, table, fn
      {:fixity, meta, _}, acc -> add_fixity_op(acc, meta)
      _other, acc -> acc
    end)
  end

  defp add_fixity_op(table, meta) do
    lexeme = Keyword.get(meta, :operator)
    group = Keyword.get(meta, :group)

    if is_binary(lexeme) and is_atom(group) and not is_nil(group) do
      case Keyword.get(meta, :fixity) do
        :infix -> FixityTable.add_infix(table, lexeme, group)
        :prefix -> FixityTable.add_prefix(table, lexeme, group)
        :postfix -> FixityTable.add_postfix(table, lexeme, group)
        _ -> table
      end
    else
      table
    end
  end

  @spec collect_uses(term()) :: [%{target: String.t(), line: pos_integer()}]
  def collect_uses(ast),
    do:
      deep_collect(ast, fn
        {:import, meta, _} when is_list(meta) ->
          case Keyword.get(meta, :source) do
            s when is_binary(s) -> [%{target: s, line: Keyword.get(meta, :line, 1)}]
            _ -> []
          end

        _ ->
          []
      end)

  @spec collect_use_targets(term()) :: [String.t()]
  def collect_use_targets(ast), do: ast |> collect_uses() |> Enum.map(& &1.target)

  @doc "Collect modules named by qualified function calls without opening them lexically."
  @spec collect_qualified_targets(term()) :: [%{target: String.t(), line: pos_integer()}]
  def collect_qualified_targets(ast) do
    ast
    |> collect_qualified_targets(nil, [])
    |> Enum.reverse()
    |> Enum.uniq_by(&{&1.target, &1.line})
    |> reject_qualified_prefixes()
  end

  defp collect_qualified_targets(node, inherited_line, acc) when is_tuple(node) do
    meta =
      if tuple_size(node) >= 2 and is_list(elem(node, 1)),
        do: elem(node, 1),
        else: []

    line = source_line(meta) || inherited_line

    acc =
      case node do
        # Interpolation lowers to canonical `Std.String#concat` calls during
        # elaboration. Record that compiler-authored qualified dependency at
        # the same graph-construction site as authored qualified calls, before
        # the lowering occurs.
        {:string_interpolation, _meta, _segments} ->
          [%{target: "Std.String", line: line || 1} | acc]

        {:function_call, call_meta, _args} when is_list(call_meta) ->
          case qualified_owner(Keyword.get(call_meta, :name)) do
            nil -> acc
            owner -> [%{target: owner, line: line || 1} | acc]
          end

        {:attribute_access, _access_meta, _children} = access ->
          case access |> dotted_attribute_name() |> qualified_owner() do
            owner when is_binary(owner) ->
              if module_path?(owner), do: [%{target: owner, line: line || 1} | acc], else: acc

            nil ->
              acc
          end

        _ ->
          acc
      end

    Enum.reduce(Tuple.to_list(node), acc, &collect_qualified_targets(&1, line, &2))
  end

  defp collect_qualified_targets(nodes, inherited_line, acc) when is_list(nodes),
    do: Enum.reduce(nodes, acc, &collect_qualified_targets(&1, inherited_line, &2))

  # A macro rule is a MAP, and its `template` field holds ordinary AST. A walker
  # that descends only tuples and lists therefore cannot see inside any macro
  # definition — so `macro M / syntax k becomes Other.Mod.f()` produced a module
  # with no recorded dependency on `Other.Mod`, its interface was never loaded,
  # and the expansion's qualified call resolved as a local name that does not
  # exist. The call is a real dependency the moment the rule is used, so the
  # scan has to see it; structs are skipped because they are leaves (spans,
  # source info), not AST.
  defp collect_qualified_targets(%_{}, _inherited_line, acc), do: acc

  defp collect_qualified_targets(node, inherited_line, acc) when is_map(node) do
    line = if is_integer(node[:line]), do: node[:line], else: inherited_line

    node
    |> Enum.sort_by(&elem(&1, 0))
    |> Enum.reduce(acc, fn {_key, value}, acc -> collect_qualified_targets(value, line, acc) end)
  end

  defp collect_qualified_targets(_leaf, _inherited_line, acc), do: acc

  @doc "Collect qualified targets and canonicalize applied-type owners against explicit imports."
  @spec collect_qualified_targets(term(), [%{target: String.t(), line: pos_integer()}]) ::
          [%{target: String.t(), line: pos_integer()}]
  def collect_qualified_targets(ast, uses),
    do: ast |> collect_qualified_targets() |> normalize_qualified_targets(uses)

  defp qualified_owner(name) when is_binary(name) do
    case String.split(name, ".") do
      [_bare] -> nil
      parts -> parts |> Enum.drop(-1) |> Enum.join(".")
    end
  end

  defp qualified_owner(_name), do: nil

  defp dotted_attribute_name({:variable, _meta, name}) when is_binary(name), do: name

  defp dotted_attribute_name({:attribute_access, meta, [inner]}) when is_list(meta) do
    case {dotted_attribute_name(inner), Keyword.get(meta, :attribute)} do
      {prefix, attribute} when is_binary(prefix) and is_binary(attribute) -> prefix <> "." <> attribute
      _ -> nil
    end
  end

  defp dotted_attribute_name(_node), do: nil

  defp module_path?(owner) do
    owner
    |> String.split(".")
    |> Enum.all?(&String.match?(&1, ~r/^\p{Lu}/u))
  end

  defp reject_qualified_prefixes(references) do
    Enum.reject(references, fn reference ->
      Enum.any?(references, fn other ->
        other.line == reference.line and
          other.target != reference.target and
          String.starts_with?(other.target, reference.target <> ".")
      end)
    end)
  end

  defp source_line(meta) do
    case Cure.MetaAST.Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{whole: %Cure.Diagnostic.Span{start_line: line}} -> line
      _ -> Keyword.get(meta, :line)
    end
  end

  # Applied qualified types are harvested from their nested attribute-access
  # representation. That representation's call node omits the leading segment
  # (`Std.Otp.Raw.Selector(p)` reports `Otp.Raw`), while ordinary qualified calls
  # retain it. If the shortened owner uniquely names the suffix of an explicit
  # `use`, restore that canonical module identity. This removes a false dependency
  # without guessing among unrelated modules.
  defp normalize_qualified_targets(targets, uses) do
    used_modules = Enum.map(uses, & &1.target)

    Enum.map(targets, fn reference ->
      matches =
        Enum.filter(used_modules, fn used ->
          used == reference.target or String.ends_with?(used, "." <> reference.target)
        end)

      case matches do
        [canonical] -> %{reference | target: canonical}
        _ -> reference
      end
    end)
  end

  # `@prelude` reaches the AST in three shapes, and this scan has to accept all
  # three because the MANIFEST decides prelude-provider status from it while the
  # ELABORATOR decides prelude EXPORTS from the same source text: any shape one
  # accepts and the other rejects publishes ambient names from a module nobody
  # depends on, and the name resolves in whichever modules happened to be checked
  # after it — an order-dependent `unknown_global`, not a clean error.
  #
  #   * a standalone `{:property, name: "prelude"}` — what `@prelude` becomes when
  #     ANOTHER decorator follows it, since a declaration meta holds one decorator
  #     slot (`@prelude` + `@builtin(:char)` on `Std.Char`);
  #   * an attached `{:decorator, [name: :prelude], []}` — the ordinary case, when
  #     `@prelude` is the only decorator on the declaration;
  #   * a bare `{:prelude, _}` slot, the module-level spelling.
  @spec prelude?(term()) :: boolean()
  def prelude?(ast) do
    deep_reduce(ast, false, fn
      {:property, meta, _}, false when is_list(meta) ->
        Keyword.get(meta, :name) == "prelude"

      {_t, meta, _}, false when is_list(meta) ->
        case Keyword.get(meta, :decorator) do
          {:prelude, _} -> true
          {:decorator, dm, _args} when is_list(dm) -> Keyword.get(dm, :name) == :prelude
          _ -> false
        end

      _, acc ->
        acc
    end)
  end

  # Mirrors `DepGraph.find_module/1`'s filter exactly: `:container` is also
  # emitted for non-module constructs (`:struct`, `:primitive`, `:opaque`,
  # `:enum`, `:protocol`, `:trait`), so matching on the tag alone risks
  # returning a nested type's name instead of the module's, especially on a
  # `synchronize_to_statement`-recovered harvest of malformed source where
  # node order/nesting can't be assumed well-formed.
  @module_container_types [:module, :proof]

  @spec module_name(term()) :: String.t() | nil
  def module_name(ast) do
    deep_reduce(ast, nil, fn
      {:lift_module, meta, _}, nil when is_list(meta) ->
        case Keyword.get(meta, :module) do
          name when is_binary(name) -> name
          _macro_hole_or_missing -> nil
        end

      {:container, meta, _}, nil when is_list(meta) ->
        if Keyword.get(meta, :container_type) in @module_container_types,
          do: Keyword.get(meta, :name),
          else: nil

      _, acc ->
        acc
    end)
  end

  # -- deep walkers (mirror BuiltinFixity.collect_fixity_nodes shape) --------

  defp deep_collect(node, f) do
    node
    |> deep_collect(f, [])
    |> Enum.reverse()
  end

  # Build the result backwards so a scanner never repeatedly copies the
  # already-visited prefix with `++`. The visitor is applied before children,
  # matching the old pre-order result; reversing the accumulated list restores
  # the same order at the boundary.
  defp deep_collect(node, f, acc) when is_tuple(node) do
    acc = Enum.reduce(f.(node), acc, &[&1 | &2])
    Enum.reduce(Tuple.to_list(node), acc, &deep_collect(&1, f, &2))
  end

  defp deep_collect(list, f, acc) when is_list(list),
    do: Enum.reduce(list, acc, &deep_collect(&1, f, &2))

  defp deep_collect(_other, _f, acc), do: acc

  defp deep_scan(node, fixity, uses) when is_tuple(node) do
    {fixity, uses} =
      case node do
        {:fixity, _, _} = value ->
          {[value | fixity], uses}

        {:precedencegroup, _, _} = value ->
          {[value | fixity], uses}

        {:import, meta, _} when is_list(meta) ->
          case Keyword.get(meta, :source) do
            source when is_binary(source) ->
              {fixity, [%{target: source, line: Keyword.get(meta, :line, 1)} | uses]}

            _ ->
              {fixity, uses}
          end

        _ ->
          {fixity, uses}
      end

    Enum.reduce(Tuple.to_list(node), {fixity, uses}, fn child, acc ->
      deep_scan(child, elem(acc, 0), elem(acc, 1))
    end)
  end

  defp deep_scan(list, fixity, uses) when is_list(list),
    do: Enum.reduce(list, {fixity, uses}, fn child, {f, u} -> deep_scan(child, f, u) end)

  defp deep_scan(_other, fixity, uses), do: {fixity, uses}

  defp deep_reduce(node, acc, f) when is_tuple(node) do
    acc = f.(node, acc)
    node |> Tuple.to_list() |> deep_reduce(acc, f)
  end

  defp deep_reduce(list, acc, f) when is_list(list),
    do: Enum.reduce(list, acc, fn el, a -> deep_reduce(el, a, f) end)

  defp deep_reduce(_other, acc, _f), do: acc
end
