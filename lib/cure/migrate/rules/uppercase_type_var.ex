defmodule Cure.Migrate.Rules.UppercaseTypeVar do
  @moduledoc """
  Migration rule: a *free* uppercase identifier in a type-parameter position is
  a type variable and is lowercased to the new edition's convention (spec §5.5).
  This is a `:needs_resolution` rule — an uppercase name in type position parses
  identically to a type constructor (`Int`, a declared `Foo`) and a free type
  variable (`T`); only the per-file `ctx` (built-in + declared + imported type
  names, from `Cure.Migrate.build_ctx/1`) tells them apart. A name in `ctx` is a
  real type and is left untouched; a name not in `ctx` is a type variable and is
  renamed.

  ## Where type positions live

  A function's parameter and return types are carried in the `:function_def`
  node's **meta**, not its children: `params: [{:param, [type: T], name}, …]`
  and `return_type: T`, where each `T` is a type expression — a bare
  `{:variable, [scope: :local], name}` or a `{:function_call, [name: "List"], …}`
  type application (whose constructor name is a meta string, never a variable
  node, so constructors in application position are inherently safe). The rule
  rewrites those meta entries in place.

  ## Consistent rename + collision freshening (spec §7)

  Within one signature every occurrence of a renamed variable becomes the same
  lowercased name. If the lowercased form collides with a name already used in
  that signature (another type variable, e.g. a pre-existing `t`), the binder is
  freshened with the smallest unused numeric suffix — `t` → `t1` → `t2` — checked
  against every name in the signature *and* every rename target already assigned,
  so two renamed binders never merge onto each other either.
  """

  alias Cure.Migrate.Rule

  @doc "The registry entry for this rule."
  @spec rule() :: Rule.t()
  def rule do
    %Rule{
      id: :W_uppercase_type_var,
      description: "a free uppercase type variable is lowercased",
      phase: :needs_resolution,
      tier: :review,
      since: "2026",
      detect_and_rewrite: &detect_and_rewrite/2,
      warning_template: "uppercase type variable will be lowercased"
    }
  end

  @doc false
  @spec detect_and_rewrite(Rule.ast(), Rule.ctx()) :: Rule.result()
  def detect_and_rewrite(ast, ctx) do
    {new_ast, lines} = walk(ast, ctx, %{}, [])

    case lines do
      [] -> :no_change
      _ -> {:rewrite, new_ast, Enum.reverse(lines)}
    end
  end

  # ── AST walk: rewrite every function signature, collect warning lines ──────
  #
  # `active` maps each in-scope type variable to its lowercased replacement,
  # accumulated from enclosing signatures. A variable a signature renames must
  # be renamed identically wherever it recurs in that function's body (a `let`
  # type annotation, a body type application, …); threading `active` through the
  # body walk keeps binder and reference in sync. Its keys are always uppercase
  # type-variable names, so lowercase value bindings are never touched.

  # A quasiquote is code DATA whose identifiers resolve in the generated use-site
  # scope, not in the module that constructs it. In particular, transparent
  # macros quote declarations referring to aliases they emit alongside those
  # declarations (`Message`, `State`, `Request`). Treating the quoted signature
  # as an ordinary local signature spuriously lowercases those generated type
  # names. Resolution-dependent migration must stop at this scope boundary; a
  # dedicated syntax-tree migration can transform quoted code only when it also
  # models the generated declaration environment.
  defp walk({:quoted_syntax, _meta, _children} = quoted, _ctx, _active, lines),
    do: {quoted, lines}

  defp walk({:function_def, meta, body}, ctx, active, lines) do
    # Freshening must avoid every name the BODY already uses, not just signature
    # names, or a renamed signature binder (`T` -> `t`) can land on a distinct
    # free type var the body introduces (`let y: t = …`) and silently merge two
    # variables — the very merge the rule's freshening exists to prevent.
    body_names = var_names_deep(body, [])
    # Pass `active` so a var already renamed by an enclosing binder (a proto/
    # interface/impl HEAD) REUSES that decision instead of re-freshening it here.
    # Without this, a head var freshened to `t1` (because some sibling method's
    # local `t` forced the bump) is independently re-lowercased to `t` by a method
    # that lacks that local — desyncing the method's uses from the head binder.
    {new_meta, rename_map} = rewrite_signature(meta, ctx, body_names, active)
    lines = if rename_map != %{}, do: [signature_location(meta, rename_map) | lines], else: lines
    # A nested signature's own binders shadow an outer variable of the same name.
    inner = Map.merge(active, rename_map)
    {new_body, lines} = walk(body, ctx, inner, lines)
    {{:function_def, new_meta, new_body}, lines}
  end

  defp walk({:variable, meta, name}, _ctx, active, lines) when is_binary(name) do
    {{:variable, meta, Map.get(active, name, name)}, lines}
  end

  # ── Head-bearing declarations (proto/interface, impl/implementation) ─────────
  #
  # These bind type variables in their HEAD, not in a `:function_def` signature —
  # a proto/interface's type-parameter list, an impl's for-type and where-clause
  # constraints. Their methods reference those same variables, so head and body
  # must rename in lockstep or the binder desyncs from every use (`proto Foo(T)`
  # → `interface Foo(T)` with a body `fn f(a: t)`). We compute the head's rename
  # map, apply it to the head fields, and thread it into the body walk as `active`
  # so method references follow. Both the legacy `:container` (protocol/trait) and
  # the migrated `:interface`/`:implementation` shapes are handled, since
  # `proto_to_interface` may or may not have run first within a fixpoint pass.
  defp walk({:interface, meta, body}, ctx, active, lines) do
    walk_head(:interface, meta, body, ctx, active, lines, [:params], [])
  end

  defp walk({:implementation, meta, body}, ctx, active, lines) do
    walk_head(:implementation, meta, body, ctx, active, lines, [], [:for_type, :constraints])
  end

  defp walk({:container, meta, body}, ctx, active, lines) do
    case Keyword.get(meta, :container_type) do
      :protocol ->
        walk_head(:container, meta, body, ctx, active, lines, [:type_params], [])

      :trait ->
        walk_head(:container, meta, body, ctx, active, lines, [], [:for_type, :constraints])

      _ ->
        {new_body, lines} = walk(body, ctx, active, lines)
        {{:container, rename_meta(meta, active), new_body}, lines}
    end
  end

  defp walk({k, meta, ch}, ctx, active, lines) when is_list(ch) do
    {new_ch, lines} = walk(ch, ctx, active, lines)
    {{k, rename_meta(meta, active), new_ch}, lines}
  end

  defp walk({k, meta, name, inner}, ctx, active, lines) when is_binary(name) do
    {new_inner, lines} = walk(inner, ctx, active, lines)
    {{k, rename_meta(meta, active), name, new_inner}, lines}
  end

  defp walk(l, ctx, active, lines) when is_list(l) do
    Enum.map_reduce(l, lines, fn child, acc -> walk(child, ctx, active, acc) end)
  end

  defp walk(other, _ctx, _active, lines), do: {other, lines}

  # Rename type-variable occurrences that a node carries in its META rather than
  # its children — an assignment's `:type_annotation`, a param's `:type`, etc.
  # `active`'s keys are uppercase type-variable names, so `rename_in_type` (which
  # only touches variable nodes present in the map) never disturbs value data,
  # constructor-name strings, or line/col numbers held in meta.
  defp rename_meta(meta, active) when map_size(active) == 0, do: meta

  defp rename_meta(meta, active) do
    Enum.map(meta, fn {k, v} -> {k, rename_in_type(v, active)} end)
  end

  # ── Head rewrite (proto/interface/impl) ─────────────────────────────────────
  #
  # `str_fields` name meta entries holding a plain list of type-variable NAMES
  # (`:params`, `:type_params` — bare strings); `expr_fields` name entries holding
  # type EXPRESSIONS with `{:variable, …}` nodes (`:for_type`, `:constraints`).
  # We gather every head type-var name, build one rename map (ctx-filtered, and
  # freshened against both the head's own non-renamed names and every name the
  # body uses), rewrite each head field, then thread the map into the body walk.
  defp walk_head(tag, meta, body, ctx, active, lines, str_fields, expr_fields) do
    str_names = Enum.flat_map(str_fields, &head_string_names(Keyword.get(meta, &1)))
    expr_names = Enum.flat_map(expr_fields, &type_var_names(Keyword.get(meta, &1)))
    head_names = str_names ++ expr_names

    body_names = var_names_deep(body, [])

    candidates = head_names |> Enum.filter(&rename?(&1, ctx)) |> Enum.uniq()

    reserved =
      head_names
      |> Enum.reject(&rename?(&1, ctx))
      |> Enum.concat(body_names)
      |> Enum.concat(Map.values(active))
      |> MapSet.new()

    rename_map = build_rename_map(candidates, reserved, active)

    new_meta =
      meta
      |> rewrite_str_fields(str_fields, rename_map)
      |> rewrite_expr_fields(expr_fields, rename_map)

    lines =
      if rename_map != %{},
        do: [head_location(meta, rename_map, str_fields, expr_fields) | lines],
        else: lines

    inner = Map.merge(active, rename_map)
    {new_body, lines} = walk(body, ctx, inner, lines)
    {{tag, new_meta, new_body}, lines}
  end

  defp head_string_names(list) when is_list(list), do: Enum.filter(list, &is_binary/1)
  defp head_string_names(_), do: []

  defp rewrite_str_fields(meta, fields, map) do
    Enum.reduce(fields, meta, fn f, m ->
      case Keyword.fetch(m, f) do
        {:ok, v} -> Keyword.put(m, f, rename_strings(v, map))
        :error -> m
      end
    end)
  end

  defp rewrite_expr_fields(meta, fields, map) do
    Enum.reduce(fields, meta, fn f, m ->
      case Keyword.fetch(m, f) do
        {:ok, v} -> Keyword.put(m, f, rename_in_type(v, map))
        :error -> m
      end
    end)
  end

  defp rename_strings(list, map) when is_list(list) do
    Enum.map(list, fn s -> if(is_binary(s), do: Map.get(map, s, s), else: s) end)
  end

  defp rename_strings(other, _map), do: other

  # Locate the actual authored type-variable token. The parser already carries
  # precise SourceInfo on type variables and implicit parameter names, so the
  # migration warning need not point at the entire declaration.
  defp signature_location(meta, rename_map) do
    keys = rename_map |> Map.keys() |> MapSet.new()

    Enum.find_value(Keyword.get(meta, :params, []), &rename_span(&1, keys)) ||
      rename_span(Keyword.get(meta, :return_type), keys) ||
      Rule.source_span(meta, :whole) || Rule.source_line(meta)
  end

  defp head_location(meta, rename_map, str_fields, expr_fields) do
    keys = rename_map |> Map.keys() |> MapSet.new()

    names = Enum.flat_map(str_fields, &head_string_names(Keyword.get(meta, &1)))

    spans =
      case Cure.MetaAST.Metadata.source_info(meta) do
        %Cure.MetaAST.SourceInfo{arguments: spans} -> spans
        _ -> []
      end

    string_span =
      names
      |> Enum.zip(spans)
      |> Enum.find_value(fn {name, span} ->
        if MapSet.member?(keys, name) and match?(%Cure.Diagnostic.Span{}, span), do: span
      end)

    expr_span =
      Enum.find_value(expr_fields, fn field -> rename_span(Keyword.get(meta, field), keys) end)

    string_span || expr_span || Rule.source_span(meta, :opener) ||
      Rule.source_span(meta, :whole) || Rule.source_line(meta)
  end

  defp rename_span({:variable, meta, name}, keys) when is_binary(name) do
    if MapSet.member?(keys, name), do: Rule.source_span(meta, :name)
  end

  defp rename_span({:param, meta, name}, keys) when is_binary(name) do
    if MapSet.member?(keys, name) do
      Rule.source_span(meta, :name)
    else
      rename_span(Keyword.get(meta, :type), keys)
    end
  end

  defp rename_span(tuple, keys) when is_tuple(tuple),
    do: tuple |> Tuple.to_list() |> Enum.find_value(&rename_span(&1, keys))

  defp rename_span(list, keys) when is_list(list), do: Enum.find_value(list, &rename_span(&1, keys))
  defp rename_span(_other, _keys), do: nil

  # ── Signature rewrite ──────────────────────────────────────────────────────

  # Returns {new_meta, rename_map}. `rename_map` is %{} when nothing changed;
  # otherwise it maps each renamed uppercase binder to its lowercased target so
  # the caller can propagate the same rename into the function body.
  defp rewrite_signature(meta, ctx, body_names, active) do
    params = Keyword.get(meta, :params, [])
    return_type = Keyword.get(meta, :return_type)

    types =
      (Enum.map(params, &param_type/1) ++ List.wrap(return_type)) |> Enum.reject(&is_nil/1)

    # An implicit type-parameter `{T: Type}` introduces its type variable via the
    # param NAME, not its type — collect those binder names too so the binder is
    # renamed in lockstep with its references (else the two desync).
    binder_names = Enum.flat_map(params, &implicit_binder_name/1)

    names = Enum.flat_map(types, &type_var_names/1) ++ binder_names

    # Candidates come from the SIGNATURE only — a body-only uppercase name is a
    # constructor/free var whose meaning the per-file ctx cannot settle here, so
    # the rule deliberately never renames it. But the freshening avoidance set
    # `reserved` also folds in the body's names, so a freshened target never
    # collides with a name the body already uses.
    candidates = names |> Enum.filter(&rename?(&1, ctx)) |> Enum.uniq()

    # Reserve the enclosing renames' TARGETS too, so a method-local var that is
    # NOT head-bound never freshens onto a name the head already claimed.
    reserved =
      names
      |> Enum.reject(&rename?(&1, ctx))
      |> Enum.concat(body_names)
      |> Enum.concat(Map.values(active))
      |> MapSet.new()

    rename_map = build_rename_map(candidates, reserved, active)

    if rename_map == %{} do
      {meta, %{}}
    else
      new_params = Enum.map(params, &rename_param(&1, rename_map))

      meta =
        meta
        |> Keyword.put(:params, new_params)
        |> put_return_type(return_type, rename_map)

      {meta, rename_map}
    end
  end

  # Real signatures carry param shapes beyond `{:param, [type: T], name}` (bare
  # variables, dependent binders, …). Only a proper typed `:param` contributes a
  # type expression; every other shape is transparent to this rule.
  defp param_type({:param, pmeta, _name}), do: Keyword.get(pmeta, :type)
  defp param_type(_other), do: nil

  # The binder name of an implicit type parameter (`{T: Type}` -> ["T"]); an
  # explicit param's name is a value binder, never a type variable, so it is
  # never a rename candidate.
  defp implicit_binder_name({:param, pmeta, name}) when is_binary(name) do
    if Keyword.get(pmeta, :implicit), do: [name], else: []
  end

  defp implicit_binder_name(_other), do: []

  # Rewrite the `:type` of a proper typed param, and — for an implicit type
  # parameter — its binder NAME too, so binder and references rename together.
  # Every other param shape (and typeless params) is left as-is.
  defp rename_param({:param, pmeta, pname}, map) do
    new_name =
      if Keyword.get(pmeta, :implicit), do: Map.get(map, pname, pname), else: pname

    case Keyword.fetch(pmeta, :type) do
      {:ok, _type} -> {:param, Keyword.update!(pmeta, :type, &rename_in_type(&1, map)), new_name}
      :error -> {:param, pmeta, new_name}
    end
  end

  defp rename_param(other, _map), do: other

  defp put_return_type(meta, nil, _map), do: meta

  defp put_return_type(meta, rt, map) do
    Keyword.put(meta, :return_type, rename_in_type(rt, map))
  end

  # Assign each candidate its lowercased (freshened) target, threading the
  # reserved set so later candidates avoid earlier targets too. A candidate that
  # an enclosing binder already renamed (present in `active`) REUSES that target
  # verbatim rather than freshening independently — this keeps a method's uses of
  # a head-bound type var spelled exactly as the head binder.
  defp build_rename_map(candidates, reserved, active) do
    {map, _used} =
      Enum.reduce(candidates, {%{}, reserved}, fn name, {map, used} ->
        target =
          case Map.fetch(active, name) do
            {:ok, existing} -> existing
            :error -> fresh_lower(name, used)
          end

        {Map.put(map, name, target), MapSet.put(used, target)}
      end)

    map
  end

  # `T` -> `t`; if taken, `t1`, `t2`, … — first form not in `used`.
  defp fresh_lower(name, used) do
    base = String.downcase(name)

    if MapSet.member?(used, base) do
      Stream.iterate(1, &(&1 + 1))
      |> Stream.map(&(base <> Integer.to_string(&1)))
      |> Enum.find(&(not MapSet.member?(used, &1)))
    else
      base
    end
  end

  # ── Type-expression helpers ────────────────────────────────────────────────

  # Every variable name appearing in a type expression, in order.
  # A dotted type such as `Std.Bool.Bool` is one qualified constructor name;
  # its `Std` base is a module path, never a free type variable.
  defp type_var_names({:attribute_access, _meta, [_base]}), do: []
  defp type_var_names({:variable, _meta, name}) when is_binary(name), do: [name]
  defp type_var_names({_k, _meta, ch}) when is_list(ch), do: Enum.flat_map(ch, &type_var_names/1)
  defp type_var_names(l) when is_list(l), do: Enum.flat_map(l, &type_var_names/1)
  defp type_var_names(_), do: []

  # Every variable-node name anywhere in a subtree — descending BOTH children
  # and meta-borne type expressions (a `let`'s `:type_annotation`, a param's
  # `:type`), since a body type variable frequently lives in meta rather than as
  # a child. Over-collecting value-variable names is harmless: it only pushes a
  # freshened target to a higher suffix, never causes an incorrect merge.
  defp var_names_deep({:variable, meta, name}, acc) when is_binary(name),
    do: meta |> meta_values() |> Enum.reduce([name | acc], &var_names_deep/2)

  defp var_names_deep({_k, meta, name, inner}, acc) when is_binary(name),
    do: var_names_deep(inner, meta |> meta_values() |> Enum.reduce([name | acc], &var_names_deep/2))

  defp var_names_deep({_k, meta, ch}, acc) when is_list(ch),
    do: Enum.reduce(ch, meta |> meta_values() |> Enum.reduce(acc, &var_names_deep/2), &var_names_deep/2)

  defp var_names_deep({_k, meta, inner}, acc),
    do: var_names_deep(inner, meta |> meta_values() |> Enum.reduce(acc, &var_names_deep/2))

  defp var_names_deep(l, acc) when is_list(l), do: Enum.reduce(l, acc, &var_names_deep/2)
  defp var_names_deep(_, acc), do: acc

  defp meta_values(meta) when is_list(meta), do: Enum.map(meta, fn {_k, v} -> v end)
  defp meta_values(_), do: []

  # Rewrite variable nodes whose name is a rename key; recurse into applications.
  defp rename_in_type({:attribute_access, _meta, [_base]} = qualified, _map), do: qualified

  defp rename_in_type({:variable, meta, name}, map) when is_binary(name) do
    {:variable, meta, Map.get(map, name, name)}
  end

  defp rename_in_type({k, meta, ch}, map) when is_list(ch) do
    {k, meta, Enum.map(ch, &rename_in_type(&1, map))}
  end

  defp rename_in_type(l, map) when is_list(l), do: Enum.map(l, &rename_in_type(&1, map))
  defp rename_in_type(other, _map), do: other

  # A name is renamed iff it is uppercase-initial (a type-var/constructor spelling)
  # and does NOT resolve to a known type (built-in, declared, or imported).
  #
  # A retired spelling (`Pid`, `Ref` — see `Cure.Elab.Resolution`) resolves to
  # nothing by design, so it reaches here looking exactly like a free type
  # variable. Lowercasing it would turn `-> Pid` into `-> pid`, a well-formed
  # signature over a fresh variable, and destroy the elaborator's
  # `retired_process_type` diagnostic — the only thing that tells the author to
  # write `Pid(m)`. There is no mechanical rewrite (the message type cannot be
  # synthesized), so the rule leaves the name as authored, as
  # `Rules.RemovedModule` does for a removed `use`.
  defp rename?(name, ctx) do
    uppercase_initial?(name) and not MapSet.member?(ctx, name) and
      not Cure.Elab.Resolution.retired_type_name?(name)
  end

  defp uppercase_initial?(<<c, _::binary>>) when c in ?A..?Z, do: true
  defp uppercase_initial?(_), do: false
end
