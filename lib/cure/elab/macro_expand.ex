defmodule Cure.Elab.MacroExpand do
  @moduledoc """
  Compile-time execution of Tier-3 `computed by` macro uses.

  This is frontend orchestration: it elaborates an elab reference, checks its
  application to a reflected `Std.Syntax` Core value, normalizes the result,
  and reflects the result back to surface AST. The resulting AST is still
  elaborated and kernel-checked by the ordinary declaration path.
  """

  alias Cure.Compiler.{MacroFamily, MacroSyntax, Parser}
  alias Cure.Core.{Context, Kernel, Normalise}
  alias Cure.Diagnostic.ProvenanceFrame
  alias Cure.Elab.{Elaborator, Resolve, TotalityClosure}
  alias Cure.MetaAST.{Metadata, SourceInfo}

  @normalise_fuel 10_000
  @normalise_fuel_per_node 100
  @normalise_fuel_ceiling 1_000_000
  # Termination is guaranteed by active-stack cycle detection. Production
  # expansion therefore has no arbitrary depth/size ceiling; embedders and
  # tests may still supply defensive finite limits explicitly.
  @default_limits [max_expansions: :infinity, max_nodes: :infinity]

  # Which of the two compile-time execution strategies a run may use. `:compiled`
  # is the default and prefers the already-checked BEAM implementation of a
  # stdlib expander; `:core_fallback` forbids it and evaluates every expander in
  # Core. Both must produce the same expansion — that is the whole claim — so the
  # policy exists to make the claim testable by pinning a run to one side.
  #
  # It is process-scoped rather than an argument because expansion is reached
  # from elaboration, declaration checking, reflection, and validation alike; a
  # parameter would have to be threaded through every one of them, and a strategy
  # that only some call sites honour is not a policy.
  @policy_key {__MODULE__, :execution}

  @spec with_execution(:compiled | :core_fallback | nil, (-> result)) :: result when result: term()
  def with_execution(nil, fun), do: fun.()

  def with_execution(policy, fun) when policy in [:compiled, :core_fallback] do
    previous = Process.put(@policy_key, policy)

    try do
      fun.()
    after
      if is_nil(previous), do: Process.delete(@policy_key), else: Process.put(@policy_key, previous)
    end
  end

  @spec execution_policy() :: :compiled | :core_fallback
  def execution_policy, do: Process.get(@policy_key, :compiled)

  @spec expand(term(), Cure.Core.Env.t()) :: {:ok, term()} | {:error, term()}
  def expand(ast, env), do: expand(ast, env, [])

  @doc "Expand computed syntax recursively from the inside out under explicit budgets."
  @type expansion_frame :: %{
          keyword: String.t() | nil,
          line: non_neg_integer() | nil,
          col: non_neg_integer() | nil
        }

  @spec expand(term(), Cure.Core.Env.t(), keyword()) :: {:ok, term()} | {:error, term()}
  def expand(ast, env, opts) when is_list(opts) do
    limits = Keyword.merge(@default_limits, opts)

    state = %{
      expansions: 0,
      nodes: 0,
      fresh_counter: 0,
      active: MapSet.new(),
      path: [],
      context: Keyword.get(opts, :callback_context),
      limits: limits
    }

    case expand_node(ast, env, state) do
      {:ok, expanded, _state} -> {:ok, expanded}
      {:error, _} = error -> error
    end
  end

  @doc "True when an AST contains a deferred Tier-3 use-site."
  @spec contains_computed_use?(term()) :: boolean()
  def contains_computed_use?({:computed_use, _meta, _children}), do: true
  def contains_computed_use?({:quoted_syntax, _meta, _children}), do: false

  def contains_computed_use?(term) when is_tuple(term),
    do: term |> Tuple.to_list() |> Enum.any?(&contains_computed_use?/1)

  def contains_computed_use?(term) when is_list(term), do: Enum.any?(term, &contains_computed_use?/1)

  def contains_computed_use?(term) when is_struct(term), do: false

  def contains_computed_use?(term) when is_map(term),
    do: Enum.any?(term, fn {k, v} -> contains_computed_use?(k) or contains_computed_use?(v) end)

  def contains_computed_use?(_), do: false

  defp expand_node({:computed_use, meta, [elab, input]} = node, env, state) do
    with {:ok, state} <- visit_node(state),
         {:ok, [elab, input], state} <- expand_children([elab, input], env, state),
         {:ok, state} <- begin_expansion(node, state),
         state = push_expansion(node, state),
         meta =
           meta
           |> Keyword.put(:provenance, expansion_chain(state))
           |> put_expansion_context(state.context),
         {:ok, expanded, fresh_counter} <- execute(meta, elab, input, env, state.fresh_counter),
         expanded = stamp_generated_provenance(expanded, meta),
         state = %{state | fresh_counter: fresh_counter},
         {:ok, expanded, state} <- expand_node(expanded, env, state),
         {:ok, state} <- end_expansion(node, state) do
      {:ok, expanded, state}
    end
  end

  defp expand_node({:quoted_syntax, _meta, _children} = quoted, _env, state) do
    with {:ok, state} <- visit_node(state), do: {:ok, quoted, state}
  end

  defp expand_node(term, env, state) when is_tuple(term) do
    with {:ok, values, state} <- expand_children(Tuple.to_list(term), env, state),
         {:ok, state} <- visit_node(state) do
      {:ok, List.to_tuple(values), state}
    end
  end

  defp expand_node(term, env, state) when is_list(term), do: expand_children(term, env, state)

  defp expand_node(term, _env, state) when is_struct(term) do
    with {:ok, state} <- visit_node(state), do: {:ok, term, state}
  end

  defp expand_node(term, env, state) when is_map(term) do
    with {:ok, entries, state} <- expand_children(Map.to_list(term), env, state),
         {:ok, state} <- visit_node(state) do
      {:ok, Map.new(entries), state}
    end
  end

  defp expand_node(term, _env, state) do
    with {:ok, state} <- visit_node(state), do: {:ok, term, state}
  end

  defp expand_children(items, env, state) do
    Enum.reduce_while(items, {:ok, [], state}, fn item, {:ok, acc, state} ->
      case expand_node(item, env, state) do
        {:ok, expanded, state} -> {:cont, {:ok, [expanded | acc], state}}
        {:error, _} = error -> {:halt, error}
      end
    end)
    |> case do
      {:ok, values, state} -> {:ok, Enum.reverse(values), state}
      error -> error
    end
  end

  defp visit_node(%{nodes: nodes, limits: limits} = state) do
    nodes = nodes + 1

    if over_limit?(nodes, Keyword.fetch!(limits, :max_nodes)),
      do: {:error, budget_error(:node_count, state)},
      else: {:ok, %{state | nodes: nodes}}
  end

  defp begin_expansion(node, %{expansions: expansions, active: active, limits: limits} = state) do
    key = expansion_key(node)
    frame = expansion_frame(node)

    if MapSet.member?(active, key) do
      {:error, {:macro_expansion_cycle, Enum.reverse([frame | state.path])}}
    else
      expansions = expansions + 1

      if over_limit?(expansions, Keyword.fetch!(limits, :max_expansions)) do
        {:error, {:macro_expansion_budget, :expansion_count, Enum.reverse([frame | state.path])}}
      else
        {:ok, %{state | expansions: expansions, active: MapSet.put(active, key)}}
      end
    end
  end

  defp push_expansion(node, state),
    do: %{state | path: [expansion_frame(node) | state.path]}

  defp end_expansion(node, %{active: active, path: [_frame | path]} = state),
    do: {:ok, %{state | active: MapSet.delete(active, expansion_key(node)), path: path}}

  defp end_expansion(node, %{active: active} = state),
    do: {:ok, %{state | active: MapSet.delete(active, expansion_key(node))}}

  defp budget_error(kind, state), do: {:macro_expansion_budget, kind, expansion_chain(state)}

  defp expansion_chain(%{path: path}), do: Enum.reverse(path)

  defp put_expansion_context(meta, nil), do: meta
  defp put_expansion_context(meta, context), do: Keyword.put(meta, :expansion_context, context)

  # Generated modules cross a later compilation-unit boundary. Stamp the
  # authored invocation and complete expansion chain on the unit and each of
  # its declarations now, while that information is still available.
  defp stamp_generated_provenance({:lift_module, node_meta, children}, expansion_meta) do
    source = %{
      file: Keyword.get(expansion_meta, :file),
      line: Keyword.get(expansion_meta, :line),
      col: Keyword.get(expansion_meta, :col),
      macro: Keyword.get(expansion_meta, :keyword)
    }

    chain = Keyword.get(expansion_meta, :provenance, [])

    declarations =
      node_meta
      |> Keyword.get(:declarations, [])
      |> Enum.map(&stamp_declaration_provenance(&1, source, chain))

    node_meta =
      node_meta
      |> stamp_canonical_provenance(expansion_meta, :generated_declaration)
      |> Keyword.put(:source_provenance, source)
      |> Keyword.put(:expansion_provenance, chain)
      |> Keyword.put(:declarations, declarations)

    {:lift_module, node_meta, children}
  end

  defp stamp_generated_provenance({tag, meta, children}, expansion_meta)
       when is_atom(tag) and is_list(meta) and is_list(children) do
    meta = stamp_canonical_provenance(meta, expansion_meta, :macro_expansion)
    {tag, meta, Enum.map(children, &stamp_generated_provenance(&1, expansion_meta))}
  end

  defp stamp_generated_provenance(list, expansion_meta) when is_list(list),
    do: Enum.map(list, &stamp_generated_provenance(&1, expansion_meta))

  defp stamp_generated_provenance(other, _expansion_meta), do: other

  defp stamp_declaration_provenance({tag, meta, children}, source, chain)
       when is_atom(tag) and is_list(meta) and is_list(children) do
    meta =
      meta
      |> stamp_canonical_provenance_from_chain(chain, :generated_declaration)
      |> Keyword.put(:source_provenance, source)
      |> Keyword.put(:expansion_provenance, chain)

    {tag, meta, children}
  end

  defp stamp_declaration_provenance(other, _source, _chain), do: other

  defp stamp_canonical_provenance(meta, expansion_meta, kind) when is_list(meta) do
    meta =
      stamp_canonical_provenance_from_chain(
        meta,
        Keyword.get(expansion_meta, :provenance, []),
        kind,
        Metadata.source_info(expansion_meta)
      )

    case Keyword.get(expansion_meta, :home_source) do
      home when is_binary(home) -> Keyword.put(meta, :macro_home_source, home)
      _ -> meta
    end
  end

  defp stamp_canonical_provenance_from_chain(meta, chain, kind, expansion_info \\ nil)
       when is_list(meta) and is_list(chain) do
    info = Metadata.source_info(meta) || %SourceInfo{}
    invocation = expansion_info && expansion_info.whole

    {chain_frames, _parent} =
      Enum.map_reduce(chain, nil, fn chain_frame, parent ->
        frame = %ProvenanceFrame{
          kind: :macro_expansion,
          name: Map.get(chain_frame, :keyword, "macro"),
          invocation: Map.get(chain_frame, :invocation) || invocation,
          definition: Map.get(chain_frame, :definition),
          parent: Map.get(chain_frame, :parent) || parent
        }

        {frame, provenance_parent(frame)}
      end)

    authored_frames =
      case expansion_info do
        %SourceInfo{provenance: provenance} -> provenance
        _ -> []
      end

    parent =
      case List.last(chain_frames ++ authored_frames) do
        %ProvenanceFrame{} = frame -> provenance_parent(frame)
        _ -> nil
      end

    frame = %ProvenanceFrame{
      kind: kind,
      name: Keyword.get(meta, :name, "generated"),
      invocation: invocation,
      parent: parent
    }

    provenance =
      ([frame] ++ chain_frames ++ authored_frames ++ info.provenance)
      |> Enum.uniq_by(&provenance_identity/1)

    Metadata.put_source_info(meta, %{
      info
      | provenance: provenance
    })
  end

  defp provenance_parent(%ProvenanceFrame{} = frame),
    do: %{kind: frame.kind, name: frame.name, invocation: frame.invocation}

  defp provenance_identity(%ProvenanceFrame{} = frame),
    do: {frame.kind, frame.name, frame.invocation, frame.definition, frame.generated}

  defp provenance_identity(other), do: other

  defp over_limit?(_value, :infinity), do: false
  defp over_limit?(value, limit) when is_integer(limit), do: value > limit

  defp over_limit?(_value, limit),
    do: raise(ArgumentError, "macro expansion limit must be :infinity or a non-negative integer, got #{inspect(limit)}")

  # Ignore source positions in the active key. A recursive macro that rebuilds
  # its own use-site with fresh line/column metadata is still the same expansion
  # node and must be rejected; two sibling nodes remain distinct by their input.
  defp expansion_key({:computed_use, meta, [elab, input]}) do
    {Keyword.get(meta, :keyword), MacroSyntax.to_syntax(elab), MacroSyntax.to_syntax(input)}
  end

  defp expansion_key(node), do: node

  defp expansion_frame({:computed_use, meta, _}) do
    info = Metadata.source_info(meta)
    source_frame = info && Enum.find(info.provenance, &match?(%ProvenanceFrame{kind: :macro_expansion}, &1))

    %{
      keyword: Keyword.get(meta, :keyword),
      line: Keyword.get(meta, :line),
      col: Keyword.get(meta, :col),
      invocation: (source_frame && source_frame.invocation) || (info && info.whole),
      definition: source_frame && source_frame.definition,
      parent: source_frame && source_frame.parent
    }
  end

  defp expansion_frame(_), do: %{keyword: nil, line: nil, col: nil}

  defp execute(meta, elab_ast, input_ast, env, fresh_counter) do
    with {:ok, evidence} <- check_capture_obligations(meta, env) do
      meta = Keyword.put(meta, :resolved_obligations, evidence)
      execute_after_obligations(meta, elab_ast, input_ast, env, fresh_counter)
    end
  end

  defp execute_after_obligations(meta, elab_ast, input_ast, env, fresh_counter) do
    if execution_policy() == :core_fallback do
      execute_after_obligations_core(meta, elab_ast, input_ast, env, fresh_counter)
    else
      case execute_compiled_stdlib_macro(meta, elab_ast, input_ast, fresh_counter) do
        :unavailable -> execute_after_obligations_core(meta, elab_ast, input_ast, env, fresh_counter)
        result -> result
      end
    end
  end

  defp execute_after_obligations_core(meta, elab_ast, input_ast, env, fresh_counter) do
    # Definition-site (ambient) macro hygiene, as a ZERO-OVERHEAD FALLBACK. A
    # stdlib computed/family macro's expander is a global of its HOME module. If
    # the use-site has `use Std.X` (or the macro is lexical), the expander already
    # resolves in the caller env — the common path — and we pay nothing extra.
    # Only a genuinely-bare ambient use fails to resolve the expander; that single
    # failure is retried once with the home-module env merged, so it resolves in
    # its definition scope (as Lean/Racket resolve macro helpers). The merged env
    # is local to the retry — the AST it produces is re-elaborated in the caller's
    # own env, so caller scope is unchanged.
    case execute_with_env(meta, elab_ast, input_ast, env, fresh_counter) do
      {:error, {:computed_macro_error, _meta, reason}} = err ->
        case Keyword.get(meta, :home_source) do
          nil ->
            err

          home_source ->
            if resolution_failure?(reason) do
              merged = Cure.Elab.Program.env_with_macro_home(env, home_source)
              execute_with_env(meta, elab_ast, input_ast, merged, fresh_counter)
            else
              err
            end
        end

      ok ->
        ok
    end
  end

  # A current stdlib BEAM has already passed elaboration, kernel checking,
  # totality, and code generation. Execute that checked implementation directly
  # at compile time instead of rebuilding its complete source interface in each
  # fresh compiler VM. User macros and stale/unbuilt stdlib macros retain the
  # Core evaluator path below. Expansion output still crosses the ordinary K3
  # re-elaboration firewall, and no dispatcher or interpreter enters runtime
  # program code.
  defp execute_compiled_stdlib_macro(meta, {:variable, _elab_meta, name}, input_ast, fresh_counter)
       when is_binary(name) do
    with home when is_binary(home) <- Keyword.get(meta, :home_source),
         true <- stdlib_macro_home?(home),
         {:ok, module} <- declared_runtime_module(home),
         true <- current_compiled_module?(module, home),
         function = String.to_atom(name) do
      input_repr =
        input_ast
        |> MacroSyntax.to_syntax()
        |> MacroSyntax.with_context(Keyword.get(meta, :expansion_context))

      argument_sets =
        if Keyword.get(meta, :direct_inputs, false) do
          direct =
            MacroSyntax.to_runtime_direct_inputs(
              input_repr,
              Keyword.get(meta, :syntax_fields, []),
              Keyword.get(meta, :syntax_field_types, %{})
            )

          [direct, [MacroSyntax.to_runtime(input_repr)]]
        else
          [[MacroSyntax.to_runtime(input_repr)]]
        end

      with args when is_list(args) <-
             Enum.find(argument_sets, &function_exported?(module, function, length(&1))) do
        result = apply(module, function, args)

        case MacroSyntax.from_runtime_macro_result(result) do
          {:expanded, repr} ->
            with {:ok, ast} <- validate_expansion(repr),
                 {ast, next_counter} <- Parser.freshen_generated(ast, fresh_counter) do
              {:ok, ast, next_counter}
            end

          {:rejected, diagnostics} ->
            {:error,
             {:computed_macro_error, meta, {:author_diagnostics, Enum.map(diagnostics, &MacroSyntax.from_syntax/1)}}}

          :not_macro_result ->
            case MacroSyntax.from_runtime(result) do
              {:error, _reason} ->
                :unavailable

              {:syn_failure, failure, values} ->
                {:error,
                 {:computed_macro_error, meta,
                  {:author_failure, Atom.to_string(failure), Enum.map(values, &MacroSyntax.from_syntax/1)}}}

              repr ->
                with {:ok, ast} <- validate_expansion(repr),
                     {ast, next_counter} <- Parser.freshen_generated(ast, fresh_counter) do
                  {:ok, ast, next_counter}
                end
            end
        end
      else
        nil -> :unavailable
      end
    else
      _ -> :unavailable
    end
  rescue
    error -> {:error, {:computed_macro_error, meta, {:host_exception, error.__struct__}}}
  end

  defp execute_compiled_stdlib_macro(_meta, _elab_ast, _input_ast, _fresh_counter), do: :unavailable

  defp stdlib_macro_home?(home) do
    expanded = Path.expand(home)
    stdlib = Path.expand("../../std", __DIR__)
    regex = Path.expand("../../std_deps/regex", __DIR__)

    String.starts_with?(expanded, stdlib <> "/") or
      String.starts_with?(expanded, regex <> "/")
  end

  defp declared_runtime_module(home) do
    with {:ok, source} <- File.read(home),
         [_, declared] <- Regex.run(~r/^\s*mod\s+([A-Za-z_][\w\.]*)/m, source) do
      {:ok, String.to_atom("Cure." <> declared)}
    else
      _ -> :error
    end
  end

  defp current_compiled_module?(module, source) do
    with {:file, _} <- :code.is_loaded(module),
         {:ok, source_bytes} <- File.read(source),
         attributes when is_list(attributes) <- module.module_info(:attributes),
         provenance when is_map(provenance) <- provenance_attribute(attributes) do
      provenance.source_hash == :crypto.hash(:sha256, source_bytes)
    else
      _ -> false
    end
  end

  defp provenance_attribute(attributes) do
    case Keyword.get(attributes, :cure_artifact) do
      [provenance] when is_map(provenance) -> provenance
      provenance when is_map(provenance) -> provenance
      _ -> nil
    end
  end

  defp check_capture_obligations(meta, env) do
    ctx = Context.empty(env)

    meta
    |> Keyword.get(:capture_obligations, [])
    |> Enum.reduce_while({:ok, []}, fn obligation, {:ok, evidence} ->
      iface = String.to_atom(obligation.interface)

      with {:ok, _term, type_value} <-
             Elaborator.elaborate_expr_typed(obligation.expression, [], ctx, env),
           {:ok, dictionary, dictionary_type} <-
             Resolve.dictionary_for_type_value(env, iface, type_value, ctx) do
        witness = Map.merge(obligation, %{dictionary: dictionary, dictionary_type: dictionary_type})
        {:cont, {:ok, evidence ++ [witness]}}
      else
        {:error, reason} ->
          {:halt,
           {:error,
            {:macro_capture_obligation_failed, Keyword.get(meta, :keyword), obligation.interface, obligation.capture,
             reason}}}
      end
    end)
  end

  # Only an unresolved-expander failure merits retrying in the definition-site
  # scope; any other computed-macro error is genuine and returned as-is.
  defp resolution_failure?(:unknown_global), do: true
  defp resolution_failure?({:unknown_global, _}), do: true
  defp resolution_failure?({:unknown_global, _, _details}), do: true
  defp resolution_failure?(_), do: false

  defp execute_with_env(meta, elab_ast, input_ast, env, fresh_counter) do
    context = Context.empty(env)

    # The elab sees WHERE it was invoked, not just what it was handed: the
    # callback context travels with the input, as an attribute of the generic
    # `Syntax` node and as the derived record's trailing `context` field.
    input_repr =
      input_ast
      |> MacroSyntax.to_syntax()
      |> MacroSyntax.with_context(Keyword.get(meta, :expansion_context))

    field_types = resolve_field_types(Keyword.get(meta, :syntax_field_types, %{}), env)

    input_cores =
      case Keyword.get(meta, :syntax_type) do
        nil ->
          [[MacroSyntax.to_core(input_repr)]]

        syntax_type ->
          record =
            MacroSyntax.to_core_record(
              Cure.Core.Env.resolve_key(env, env.ctors, syntax_type),
              Keyword.get(meta, :syntax_fields, []),
              Keyword.get(meta, :syntax_repeated_fields, []),
              input_repr,
              field_types
            )

          direct =
            if Keyword.get(meta, :direct_inputs, false) or primitive_field_types?(field_types),
              do: direct_input_cores(input_repr, Keyword.get(meta, :syntax_fields, []), field_types),
              else: []

          Enum.filter([direct, [record], [MacroSyntax.to_core(input_repr)]], &(&1 != []))
      end

    with {:ok, elab_core, _elab_type} <-
           Elaborator.elaborate_expr_typed(elab_ast, [], context, env),
         {:ok, eval_env} <- TotalityClosure.certify_roots(env, global_names(elab_core)),
         {:ok, result_ast} <- execute_application(Context.empty(eval_env), elab_core, input_cores),
         {result_ast, fresh_counter} <- Parser.freshen_generated(result_ast, fresh_counter) do
      {:ok, result_ast, fresh_counter}
    else
      {:error, reason} -> {:error, {:computed_macro_error, meta, reason}}
      :fuel_exhausted -> {:error, {:computed_macro_error, meta, :normalization_fuel_exhausted}}
    end
  rescue
    error -> {:error, {:computed_macro_error, meta, {:host_exception, error.__struct__}}}
  end

  defp resolve_field_types(field_types, env) when is_map(field_types) do
    Map.new(field_types, fn
      {field, {:record, name, fields}} ->
        repeated =
          fields
          |> Enum.filter(&(MacroFamily.field_cardinality(&1) in [:repeated, :one_or_more]))
          |> Enum.map(& &1.name)

        {field,
         {:record, Cure.Core.Env.resolve_key(env, env.ctors, name),
          Enum.map(fields, fn nested_field ->
            nested_field
            |> Map.put(:repeated, nested_field.name in repeated)
            |> resolve_nested_grammar(env)
          end)}}

      {field, value} ->
        {field, value}
    end)
  end

  defp resolve_field_types(_field_types, _env), do: %{}

  defp resolve_nested_grammar(%{grammar: %{name: name} = grammar} = field, env) do
    Map.put(
      field,
      :grammar,
      Map.put(grammar, :name, Cure.Core.Env.resolve_key(env, env.ctors, MacroFamily.syntax_type(name)))
    )
  end

  defp resolve_nested_grammar(field, _env), do: field

  defp primitive_field_types?(field_types) when is_map(field_types) do
    Enum.any?(field_types, fn {_field, type} -> match?({:primitive, _shape}, type) end)
  end

  defp primitive_field_types?(_field_types), do: false

  defp global_names({:global, name}), do: [name]
  defp global_names({:app, f, a}), do: global_names(f) ++ global_names(a)
  defp global_names({:lam, _grade, domain, body}), do: global_names(domain) ++ global_names(body)
  defp global_names({:pi, _grade, domain, codomain}), do: global_names(domain) ++ global_names(codomain)

  defp global_names({:case, scrutinee, motive, branches}) do
    global_names(scrutinee) ++
      global_names(motive) ++ Enum.flat_map(branches, fn {_name, _arity, body} -> global_names(body) end)
  end

  defp global_names({:let, _grade, type, value, body}),
    do: global_names(type) ++ global_names(value) ++ global_names(body)

  defp global_names({:effect_type, inner}), do: global_names(inner)
  defp global_names({:effect_pure, value}), do: global_names(value)

  defp global_names({:effect_bind, effect, continuation}),
    do: global_names(effect) ++ global_names(continuation)

  defp global_names({:ctor, _name, args}), do: Enum.flat_map(args, &global_names/1)
  defp global_names({:data, _name, params, indices}), do: Enum.flat_map(params ++ indices, &global_names/1)
  defp global_names(term) when is_list(term), do: Enum.flat_map(term, &global_names/1)

  defp global_names(term) when is_tuple(term),
    do: term |> Tuple.to_list() |> Enum.flat_map(&global_names/1)

  defp global_names(_term), do: []

  defp direct_input_cores({:syn_node, _tag, _attrs, kids}, fields, field_types) do
    fields
    |> Enum.zip(kids)
    |> Enum.map(fn {field, kid} ->
      case Map.get(field_types, field) do
        {:record, nested_name, nested_fields} ->
          repeated =
            nested_fields
            |> Enum.filter(&(MacroFamily.field_cardinality(&1) in [:repeated, :one_or_more]))
            |> Enum.map(& &1.name)

          nested_field_types = MacroSyntax.family_field_types(nested_fields)

          MacroSyntax.to_core_record_without_context(
            nested_name,
            Enum.map(nested_fields, & &1.name),
            repeated,
            kid,
            nested_field_types
          )

        {:primitive, shape} ->
          MacroSyntax.to_core_primitive_value(kid, shape)

        _ ->
          MacroSyntax.to_core(kid)
      end
    end)
  end

  defp direct_input_cores(_input_repr, _fields, _field_types), do: []

  defp execute_application(context, elab_core, [candidate | fallback]) when is_list(candidate) do
    application = Enum.reduce(candidate, elab_core, fn input_core, function -> {:app, function, input_core} end)

    case Kernel.infer(context, application) do
      {:ok, _result_type} ->
        result = Normalise.nf(context, application, fuel: normalise_fuel(application))

        case decode_result(result) do
          {:ok, _ast} = success ->
            success

          {:error, reason} when fallback != [] ->
            if fallback_decode_error?(reason),
              do: execute_application(context, elab_core, fallback),
              else: {:error, reason}

          error ->
            error
        end

      {:error, _reason} when fallback != [] ->
        execute_application(context, elab_core, fallback)

      {:error, reason} ->
        {:error, reason}
    end
  end

  defp execute_application(_context, _elab_core, []),
    do: {:error, :no_compatible_macro_input}

  # Declaration macros receive reflected records whose Core representation is
  # proportional to the authored declaration. A fixed expression-sized budget
  # made valid four-row grammars fail while two-row versions passed. Scale the
  # bounded evaluator budget with that input, retaining a hard ceiling for
  # termination and denial-of-service resistance.
  defp normalise_fuel(application) do
    min(@normalise_fuel_ceiling, @normalise_fuel + @normalise_fuel_per_node * core_nodes(application))
  end

  defp core_nodes(value) when is_tuple(value) do
    value
    |> Tuple.to_list()
    |> Enum.reduce(1, fn child, count -> count + core_nodes(child) end)
  end

  defp core_nodes(value) when is_list(value),
    do: Enum.reduce(value, 1, fn child, count -> count + core_nodes(child) end)

  defp core_nodes(_value), do: 1

  defp fallback_decode_error?({:author_failure, _name, _args}), do: false
  defp fallback_decode_error?({:author_diagnostics, _diagnostics}), do: false
  defp fallback_decode_error?({:invalid_generated_syntax, _reason}), do: false
  defp fallback_decode_error?(_reason), do: true

  defp decode_result(result) do
    if result == :fuel_exhausted do
      {:error, :normalization_fuel_exhausted}
    else
      decode_result_term(result)
    end
  end

  defp decode_result_term(result) do
    case MacroSyntax.from_core_macro_result(result) do
      {:expanded, repr} ->
        validate_expansion(repr)

      {:rejected, diagnostics} ->
        {:error, {:author_diagnostics, Enum.map(diagnostics, &MacroSyntax.from_syntax/1)}}

      {:error, reason} ->
        {:error, reason}

      :not_macro_result ->
        case MacroSyntax.from_core(result) do
          {:error, reason} ->
            {:error, reason}

          {:syn_failure, name, args} ->
            {:error, {:author_failure, Atom.to_string(name), Enum.map(args, &MacroSyntax.from_syntax/1)}}

          repr ->
            validate_expansion(repr)
        end
    end
  end

  defp validate_expansion(repr) do
    case MacroSyntax.validate_expansion(repr) do
      :ok -> {:ok, MacroSyntax.from_syntax(repr)}
      {:error, reason} -> {:error, {:invalid_generated_syntax, reason}}
    end
  end
end
