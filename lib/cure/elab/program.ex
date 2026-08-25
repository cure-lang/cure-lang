defmodule Cure.Elab.Program do
  @moduledoc """
  Whole-program elaboration (design spec §5, M9.2 wiring): lex + parse a source
  string, elaborate every declaration into the `Cure.Core` signature, then run
  the type-level totality closure so that any function reduced by the type
  checker is kernel-certified total (§7). Returns the fully-elaborated,
  totality-certified signature.
  """

  alias Cure.Compiler.{
    Artifacts,
    BuildManifest,
    Lexer,
    MacroFamily,
    MacroSyntax,
    MacroValidate,
    ModuleIndex,
    ModuleInterface,
    Parser
  }

  alias Cure.Compiler.ModulePipeline.Interface, as: PipelineInterface
  alias Cure.Compiler.Parser.FixityScan
  alias Cure.Core.{Env, Inductive, Validator}

  alias Cure.Elab.{
    AttemptCache,
    CheckedModule,
    Coherence,
    Declarations,
    Erase,
    MacroExpand,
    PreparedDeclarations,
    CallAttemptProfile,
    TotalityClosure
  }

  alias Cure.Stdlib.Paths

  @loader_state_key {__MODULE__, :module_loader_state}
  @public_reexport_cache_key {__MODULE__, :public_reexport_modules}
  @module_interface_cache_version 3
  @macro_home_cache_version 3

  @spec elaborate(String.t(), keyword()) :: {:ok, Env.t()} | {:error, term()}
  def elaborate(source, opts \\ []) when is_binary(source) and is_list(opts) do
    file = Keyword.get(opts, :file, "nofile")

    Cure.Elab.GuardLint.reset_warnings()

    with {:ok, tokens} <- Lexer.tokenize(source, file: file, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, file: file, emit_events: false) do
      check_ast(ast)
    end
  end

  @doc "Project an elaboration result's surface context away for semantic comparisons."
  @spec semantic_error(term()) :: term()
  def semantic_error({:source_context, reason, _context}), do: semantic_error(reason)
  def semantic_error({:codegen_error, reason}), do: {:codegen_error, semantic_error(reason)}

  def semantic_error({:sibling_module_collision, %{name: name, owners: owners}}),
    do: {:sibling_module_collision, name, owners}

  def semantic_error(reason), do: reason

  @doc "Project diagnostic context away from an elaboration result while preserving its verdict."
  @spec semantic_result({:ok, term()} | {:error, term()}) :: {:ok, term()} | {:error, term()}
  def semantic_result({:error, reason}), do: {:error, semantic_error(reason)}
  def semantic_result(result), do: result

  @doc """
  Elaborate + totality-certify an already-parsed module/declaration AST. Unwraps
  a `mod ... end` container to its body. This is the entry the real compiler's
  type checker calls for dependent modules.
  """
  @spec check_ast(tuple() | list()) :: {:ok, Env.t()} | {:error, term()}
  def check_ast(ast), do: AttemptCache.scope(fn -> check_ast(ast, []) end)

  @doc false
  @spec prepare_canonical_declarations(tuple() | list()) ::
          {:ok, PreparedDeclarations.t()} | {:error, term()}
  def prepare_canonical_declarations(ast) do
    with :ok <- check_declarations(ast),
         {:ok, lifted} <- Cure.Elab.Induction.lift_declarations(declarations(ast)) do
      items = lifted |> expand_where_declarations() |> annotate_overload_ordinals()

      {:ok,
       %PreparedDeclarations{
         owner: find_module_name(ast) || "Main",
         items: items,
         declaration_count: length(items)
       }}
    end
  end

  @doc """
  Validate that every author-written `use Std.X` import names a stdlib module
  that exists.

  Existing means the module has a source in the universe. It deliberately does
  NOT mean a beam for it is loaded in this VM: whether the standard library
  happens to be built is a fact about the current `_build`, not about the
  program, and letting it decide whether a name resolves is a second answer to
  what a name means. That is the loaded-BEAM resolution path the interface-first
  design removes — the checker reads the interface from source, and having the
  beam available at run time is the bundler's problem, reported as such.

  Compiler-injected ambient `@prelude` imports are exempt from the check
  entirely. They are not `order_deps` edges, so `Incremental.compile_order/1`
  cannot schedule the provider before its ambient consumers (the prelude closure
  is cyclic — no such order exists).
  """
  @spec validate_stdlib_imports(tuple() | list()) :: :ok | {:error, term()}
  def validate_stdlib_imports(ast) do
    ast
    |> import_entries()
    |> Enum.reject(fn {_sources, meta} -> Keyword.get(meta, :prelude_injected, false) end)
    |> Enum.flat_map(fn {sources, _meta} -> sources end)
    |> Enum.find_value(:ok, fn source ->
      case import_source_path(source) do
        {:ok, _module_name, _path} ->
          nil

        {:ok_user, _module_name, _path} ->
          nil

        {:error, {:missing_stdlib_source, source, _path}} ->
          missing_stdlib_error(source)

        {:error, {:missing_stdlib_source_dir, source}} ->
          missing_stdlib_error(source)

        :not_stdlib ->
          nil
      end
    end)
  end

  defp missing_stdlib_error(source) do
    module = String.to_atom("Cure." <> source)
    user_name = String.replace_prefix(source, "Cure.", "")

    {:error,
     {:missing_stdlib_module, module,
      "use #{user_name}: module '#{module}' not found. " <>
        "Set [compiler] stdlib_path in Cure.toml or export CURE_LIB."}}
  end

  @spec check_ast(tuple() | list(), keyword()) :: {:ok, Env.t()} | {:error, term()}
  def check_ast(ast, opts) do
    with {:ok, %CheckedModule{env: env}} <- check_ast_artifact(ast, opts), do: {:ok, env}
  end

  @doc false
  @spec canonical_register_interface(tuple() | list(), Env.t(), keyword()) ::
          {:ok, map()} | {:error, term()}
  def canonical_register_interface(ast, %Env{} = imported_env, opts \\ []) do
    owner = Keyword.get(opts, :module_name, find_module_name(ast) || "Main")
    source_opts = source_context_opts(Keyword.get(opts, :source), Keyword.get(opts, :file))

    with {:ok, prepared} <- prepared_declarations(ast, opts),
         seeded = Env.with_owner(seed_with_telescope_support(ast), owner),
         {:ok, merged} <- merge_env(seeded, without_incoming_owner(imported_env, owner)),
         env0 = install_canonical_module_visibility(merged, ast, opts),
         items = prepared.items,
         # Whether a module may register a `@builtin(:key)` family is a property of
         # the SOURCE, not of the pipeline compiling it: `Std.Sigma` is the
         # designated provider of `:sigma` however it is scheduled. Passing a flat
         # `false` here silently dropped every builtin binding in the canonical
         # pipeline, and the loss was invisible until a provider referred to its own
         # family through compiler-owned syntax — `Sigma(x: a, b(x))` lowers via
         # `Inductive.builtin(env, :sigma)`, whose `|| :Sigma` fallback produced a
         # bare family name that matched no constructor's real owner.
         {:ok, interface_env, function_declarations} <- register_pass(items, env0, prelude_source?(ast)),
         :ok <- check_overload_legality(interface_env) do
      {:ok,
       %{
         ast: ast,
         owner: owner,
         items: items,
         interface_env: interface_env,
         function_declarations: function_declarations,
         source_opts: source_opts,
         module_visibility: Keyword.get(opts, :module_visibility)
       }}
    end
  end

  @doc false
  @spec canonical_type_skeleton(tuple() | list(), Env.t(), keyword()) ::
          {:ok, Env.t()} | {:error, term()}
  def canonical_type_skeleton(ast, %Env{} = imported_env, opts \\ []) do
    owner = Keyword.get(opts, :module_name, find_module_name(ast) || "Main")

    with {:ok, prepared} <- prepared_declarations(ast, opts),
         seeded = Env.with_owner(seed_with_telescope_support(ast), owner),
         {:ok, merged} <- merge_env(seeded, without_incoming_owner(imported_env, owner)),
         env0 = install_canonical_module_visibility(merged, ast, opts),
         items = prepared.items,
         {:ok, skeleton} <- declare_type_headers(items, env0) do
      {:ok, skeleton}
    end
  end

  @doc false
  @spec canonical_check_bodies(map(), keyword()) :: {:ok, Env.t()} | {:error, term()}
  def canonical_check_bodies(module, opts \\ [])

  def canonical_check_bodies(
        %{
          ast: ast,
          owner: owner,
          interface_env: %Env{} = interface_env,
          function_declarations: function_declarations,
          source_opts: source_opts
        },
        opts
      ) do
    with {:ok, checked} <-
           body_pass_strict(function_declarations, interface_env, owner, Keyword.get(opts, :event_sink)),
         checked = TotalityClosure.certify_deferred(checked),
         :ok <- MacroValidate.check_program(ast, checked),
         {:ok, certified} <- certify_type_level_with_source(ast, checked, source_opts),
         {:ok, certified} <- Cure.Elab.Equation.generate_all(certified, ast) do
      {:ok, mark_inline_hints(certified, owner)}
    end
  end

  @doc false
  @spec canonical_install_component_environment(map(), Env.t()) :: map()
  def canonical_install_component_environment(
        %{interface_env: %Env{} = local} = prepared,
        %Env{} = component
      ) do
    env = %Env{
      component
      | module_owner: local.module_owner,
        import_modules: local.import_modules,
        bare_modules: local.bare_modules,
        bare_bindings: local.bare_bindings,
        qualified_modules: local.qualified_modules,
        qualified_aliases: local.qualified_aliases,
        current_def: nil
    }

    Map.put(prepared, :interface_env, %Env{env | bare_bindings: component_bare_bindings(prepared, env)})
  end

  # What a module can name without qualification is decided by the SAME rule at
  # both points it is asked; only the table it is asked about differs. A module's
  # own registration pass sees its peers as type HEADERS — families with an empty
  # constructor list — so a peer's constructors are not yet keys and cannot enter
  # the binding set. The component environment is the first place every member's
  # real declarations exist together, so the rule is applied once more there.
  # This widens nothing: `lexical`/`ambient` are the same manifest projections,
  # and a module that imported nothing gains nothing.
  defp component_bare_bindings(%{ast: ast, module_visibility: %{lexical: lexical} = visibility}, %Env{} = env),
    do:
      canonical_bare_bindings(
        env,
        ast,
        lexical,
        Map.get(visibility, :ambient, MapSet.new()),
        Map.get(visibility, :reexports, MapSet.new())
      )

  defp component_bare_bindings(_prepared, %Env{bare_bindings: bindings}), do: bindings

  @doc false
  @spec merge_canonical_environments(Env.t(), Env.t()) :: {:ok, Env.t()} | {:error, term()}
  def merge_canonical_environments(%Env{} = left, %Env{} = right), do: merge_env(left, right)

  @doc """
  Elaborate and certify `ast` once, returning every semantic projection needed
  by later compiler stages.

  When both `:source` and `:file` are supplied, the artifact includes the
  canonical `ModuleInterface` built from the same certified environment while
  the same loader generation is still live. This is the entry point for real
  compilation. AST-only callers still receive a reusable checked artifact, but
  its `interface` and source identity fields are `nil`.
  """
  @spec check_ast_artifact(tuple() | list(), keyword()) ::
          {:ok, CheckedModule.t()} | {:error, term()}
  def check_ast_artifact(ast, opts \\ []) when is_list(opts) do
    with_loader_session(fn ->
      source = Keyword.get(opts, :source)
      file = Keyword.get(opts, :file)
      module_name = Keyword.get(opts, :module_name, find_module_name(ast) || "Main")

      with :ok <-
             validate_artifact_identity(
               ast,
               module_name,
               file,
               source,
               Keyword.get(opts, :require_module_identity, false)
             ),
           :ok <- check_declarations(ast),
           {:ok, env} <-
             check_ast_elixir_core_in_session(
               ast,
               source_context_opts(source, file),
               Keyword.get(opts, :prelude_mode, :ordinary),
               Keyword.get(opts, :qualified_envs, [])
             ),
           local_defs = checked_local_defs(ast, env),
           {:ok, interface} <- checked_module_interface(ast, env, module_name, file, source) do
        emit_elaboration_event({:checked, Keyword.get(opts, :purpose, :entry), module_name, file})

        {:ok,
         %CheckedModule{
           ast: ast,
           env: env,
           interface: interface,
           module: module_atom(ast),
           module_name: module_name,
           source_hash: source_hash(source),
           source_path: expanded_source_path(file, source),
           local_defs: local_defs
         }}
      end
    end)
  end

  # A loader generation belongs to one top-level elaboration. Nested elaboration
  # (notably declaration-macro preparation) shares it; unrelated compilations,
  # temporary source roots, and changed files never observe stale interfaces.
  defp with_loader_session(fun) when is_function(fun, 0) do
    case Process.get(@loader_state_key, :no_loader_session) do
      :no_loader_session ->
        :ok = Cure.Elab.SourceMetadata.reset()
        Process.put(@loader_state_key, %{modules: %{}, paths: %{}, prelude_bootstrap: nil})

        try do
          fun.()
        after
          Process.delete(@loader_state_key)
        end

      _state ->
        fun.()
    end
  end

  # The declaration-level guards, in one place. `check_ast/2` runs them for the entry module;
  # `module_slice_env/1` and `import_source_env/2` run them for every module reached through a
  # `use` import. Those two paths used to call `elaborate_declarations/3` straight from the
  # parsed AST with no guards at all, so a duplicate inside a `Std.*` source was silently kept
  # last-wins — the exact `Map.put`-overwrite hole these checks exist to close, reachable
  # through two doors they never covered.
  @spec check_declarations(tuple() | list()) :: :ok | {:error, term()}
  defp check_declarations(ast) do
    with :ok <- check_implementation_structure(ast),
         :ok <- check_no_duplicate_defs(ast),
         :ok <- check_no_duplicate_types(ast),
         :ok <- check_no_duplicate_ctors(ast),
         :ok <- check_no_fn_ctor_collision(ast),
         :ok <- check_no_precedence_cycle(ast),
         :ok <- check_proof_shapes(ast) do
      check_no_sibling_collision(ast)
    end
  end

  defp prepared_declarations(ast, opts) do
    case Keyword.get(opts, :prepared_declarations) do
      %PreparedDeclarations{} = prepared -> {:ok, prepared}
      nil -> prepare_canonical_declarations(ast)
      other -> {:error, {:invalid_prepared_declarations, other}}
    end
  end

  # Indentation owns implementation membership. An empty implementation followed
  # by a sibling function is otherwise accepted as two top-level declarations,
  # losing the programmer's intended member relationship until a much later
  # missing-method or BEAM failure. Reject the malformed structure while both
  # authored ranges are still available.
  defp check_implementation_structure(ast) do
    ast
    |> module_decl_groups()
    |> Enum.reduce_while(:ok, fn declarations, :ok ->
      case first_invalid_implementation(declarations) do
        nil -> {:cont, :ok}
        details -> {:halt, {:error, {:implementation_scope, details}}}
      end
    end)
  end

  defp first_invalid_implementation(declarations) do
    interface_methods =
      Map.new(declarations, fn
        {:interface, meta, body} when is_list(meta) and is_list(body) ->
          methods =
            body
            |> Enum.flat_map(fn
              {:function_def, method_meta, _body} -> [Keyword.get(method_meta, :name)]
              _other -> []
            end)
            |> MapSet.new()

          defaults =
            meta
            |> Keyword.get(:defaults, %{})
            |> Map.keys()
            |> MapSet.new()

          {Keyword.get(meta, :name), %{methods: methods, defaults: defaults}}

        _other ->
          {nil, %{methods: MapSet.new(), defaults: MapSet.new()}}
      end)

    declarations
    |> Enum.with_index()
    |> Enum.find_value(fn
      {{:implementation, meta, []}, index} when is_list(meta) ->
        implementation_scope_details(meta, Enum.at(declarations, index + 1), interface_methods)

      _other ->
        nil
    end)
  end

  defp implementation_scope_details(meta, {:function_def, member_meta, _body}, interface_methods)
       when is_list(member_meta) do
    member = Keyword.get(member_meta, :name)

    interface =
      Map.get(interface_methods, Keyword.get(meta, :interface), %{methods: MapSet.new(), defaults: MapSet.new()})

    if MapSet.member?(interface.methods, member) do
      misplaced_member_details(meta, member_meta)
    else
      empty_implementation_details(meta, interface)
    end
  end

  defp implementation_scope_details(meta, _next_declaration, interface_methods) do
    interface =
      Map.get(interface_methods, Keyword.get(meta, :interface), %{methods: MapSet.new(), defaults: MapSet.new()})

    empty_implementation_details(meta, interface)
  end

  defp misplaced_member_details(meta, member_meta) do
    member_span = metadata_whole_span(member_meta)

    %{
      kind: :member_outside,
      interface: Keyword.get(meta, :interface),
      for: Keyword.get(meta, :for),
      member: Keyword.get(member_meta, :name),
      implementation_span: metadata_whole_span(meta),
      member_span: member_span,
      insertion_span: insertion_span(member_span),
      indentation: "  "
    }
  end

  defp empty_implementation_details(meta, interface) do
    if MapSet.size(interface.methods) > 0 and MapSet.subset?(interface.methods, interface.defaults) do
      nil
    else
      %{
        kind: :empty,
        interface: Keyword.get(meta, :interface),
        for: Keyword.get(meta, :for),
        implementation_span: metadata_whole_span(meta)
      }
    end
  end

  defp metadata_whole_span(meta) do
    case Cure.MetaAST.Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{whole: %Cure.Diagnostic.Span{} = span} -> span
      _ -> nil
    end
  end

  defp insertion_span(%Cure.Diagnostic.Span{} = span) do
    %{
      span
      | end_byte: span.start_byte,
        end_line: span.start_line,
        end_column: span.start_column
    }
  end

  defp insertion_span(_span), do: nil

  # A module's `precedencegroup` declarations may not describe a cyclic order —
  # two groups that each claim to bind tighter than the other (directly, through
  # the built-in tower, or through a group reached across a `use` edge) have no
  # satisfiable ranking. The Kahn sort in `FixityTable.recompute/1` linearises
  # such a cycle silently, so the diagnostic lives here: assemble the module's
  # full `fixity(M)` — built-in prelude base ∪ own decls ∪ the `use`-closure —
  # and reject if any group lies on a cycle. This is the SAME union the parser
  # builds (`FixityResolver.assemble/5`), so a cycle closed only through a used
  # module's group is caught. Elaborating `Std.Operators` itself is a no-op — its
  # groups re-add idempotently onto the identical built-in base.
  defp check_no_precedence_cycle(ast) do
    base = Cure.Compiler.Parser.BuiltinFixity.table()
    own_fixity = Cure.Compiler.Parser.FixityScan.collect_fixity(ast)
    own_uses = Cure.Compiler.Parser.FixityScan.collect_use_targets(ast)

    case Cure.Compiler.Parser.FixityResolver.assemble(base, own_fixity, own_uses, []) do
      {:ok, table} ->
        case Cure.Compiler.Parser.FixityTable.cyclic_groups(table) do
          [] ->
            :ok

          groups ->
            {:error,
             {:precedence_cycle, %{groups: groups, spans: Cure.Compiler.Parser.FixityScan.group_spans(ast, groups)}}}
        end

      # A fixity conflict is already reported at parse time (the module never
      # reaches elaboration with one). Treat a defensive conflict here as "no
      # cycle to add" rather than double-reporting a parse-stage error.
      {:error, _conflict} ->
        :ok
    end
  end

  # A top-level container the dependent pipeline elaborates as a module. Classic
  # codegen compiles a `proof` container "exactly like a regular module"; the
  # dependent pipeline now does the same, so both container types are unwrapped
  # and their declarations elaborated identically.
  defp module_like_container?(meta), do: Keyword.get(meta, :container_type) in [:module, :proof]

  # E026 proof-shape discipline: every binding inside a `proof` container must
  # inhabit a propositional-equality type (`Equivalent(T, a, b)`) — proof
  # containers are exclusively for propositions, not ordinary code. A non-proof
  # return type is rejected here, before elaboration.
  defp check_proof_shapes(ast) do
    ast
    |> proof_container_fns()
    |> Enum.find_value(:ok, fn {:function_def, meta, _body} ->
      if proof_shape_return?(Keyword.get(meta, :return_type)) do
        nil
      else
        name = Keyword.get(meta, :name)

        span =
          case Cure.MetaAST.Metadata.source_info(meta) do
            %Cure.MetaAST.SourceInfo{annotation: %Cure.Diagnostic.Span{} = annotation} -> annotation
            %Cure.MetaAST.SourceInfo{name: %Cure.Diagnostic.Span{} = name_span} -> name_span
            %Cure.MetaAST.SourceInfo{whole: %Cure.Diagnostic.Span{} = whole} -> whole
            _ -> nil
          end

        reason =
          {:proof_shape_mismatch,
           "E026: binding '#{name}' in a proof container must inhabit a " <>
             "propositional-equality type Equivalent(T, a, b)", name}

        if span do
          {:error,
           {:source_context, reason,
            %{
              span: span,
              checking: name,
              expectation_origin: :proof_container,
              expression_category: :proof_binding
            }}}
        else
          {:error, reason}
        end
      end
    end)
  end

  defp proof_container_fns({:block, _meta, items}) when is_list(items),
    do: Enum.flat_map(items, &proof_container_fns/1)

  defp proof_container_fns({:container, meta, body}) when is_list(meta) do
    if Keyword.get(meta, :container_type) == :proof do
      body |> List.wrap() |> Enum.filter(&match?({:function_def, m, _} when is_list(m), &1))
    else
      []
    end
  end

  defp proof_container_fns(_other), do: []

  # A proof return type is an application of the propositional-equality family.
  defp proof_shape_return?({:function_call, meta, _args}) when is_list(meta),
    do: Keyword.get(meta, :name) in ["Equivalent", "Eq"]

  defp proof_shape_return?(_other), do: false

  # Two sibling `mod` blocks in ONE compilation unit may not bind the same name.
  #
  # A module is a namespace, and two modules in two FILES may share a name freely: the stdlib
  # has `map` in five modules. Those are reconciled by the import rekey machinery
  # (`Resolution.rekey_module_env`, LOCKED type-shadowing Approach B), which this check does
  # not touch. But `declarations/1` flattens all SIBLING modules of one AST into a single list
  # before `elaborate_declarations/3` ever runs, and nothing rekeys them — they share one flat
  # `env.defs` / `env.families` / `env.ctor_to_family`, each a plain `Map.put`. So the later
  # sibling silently wins the bare key:
  #
  #     mod A  fn foo() -> Int = 1  end
  #     mod B  fn foo() -> Int = 2  end   # A's `foo` is GONE; A's callers δ-unfold B's body
  #
  # For types it is worse than lost — it is incoherent. `type Foo = MkA` / `type Foo = MkB`
  # leaves `MkA` registered as a constructor whose `ctor_to_family` entry names a family whose
  # constructor set contains only `MkB`. That is precisely the state `check_no_duplicate_ctors`
  # rejects within one module.
  #
  # Rejecting is the sound reading. Rekeying siblings the way imports are rekeyed would require
  # elaborating each sibling into its own slice, which would break the bare cross-sibling
  # references that flat elaboration makes work today (`mod B  fn baz() = bar()  end`, calling
  # A's `bar`). Nothing in the tree declares sibling modules in one file, so nothing loses.
  @spec check_no_sibling_collision(tuple() | list()) :: :ok | {:error, term()}
  defp check_no_sibling_collision(ast) do
    case top_modules(ast) do
      mods when length(mods) < 2 ->
        :ok

      mods ->
        # `fn` names and constructor names share one bare-atom namespace, so they collide with
        # each other across siblings exactly as `check_no_fn_ctor_collision` says they do
        # within one. Type names live in `env.families`, their own namespace.
        with :ok <- first_sibling_collision(mods, &value_bindings/1),
             do: first_sibling_collision(mods, &type_bindings/1)
    end
  end

  defp first_sibling_collision(mods, extract) do
    bindings =
      Enum.flat_map(mods, fn mod ->
        owner = module_name_atom(mod)

        mod
        |> declarations()
        |> Enum.flat_map(extract)
        |> Enum.uniq_by(&elem(&1, 0))
        |> Enum.map(fn {name, span} -> %{name: name, owner: owner, span: span} end)
      end)

    collision_name =
      Enum.find_value(bindings, fn %{name: name} ->
        owners = bindings |> Enum.filter(&(&1.name == name)) |> Enum.map(& &1.owner) |> Enum.uniq()
        if length(owners) > 1, do: name
      end)

    case collision_name do
      nil ->
        :ok

      name ->
        collisions = Enum.filter(bindings, &(&1.name == name))

        details = %{
          name: name,
          owners: collisions |> Enum.map(& &1.owner) |> Enum.uniq() |> Enum.sort(),
          spans: collisions |> Enum.map(& &1.span) |> Enum.reject(&is_nil/1)
        }

        {:error, {:sibling_module_collision, details}}
    end
  end

  defp value_bindings(decl), do: function_bindings(decl) ++ constructor_bindings(decl)

  defp function_bindings({:function_def, meta, _body} = decl) when is_list(meta) do
    case Keyword.get(meta, :name) do
      name when is_binary(name) -> [{String.to_atom(name), declaration_name_span(decl)}]
      _ -> []
    end
  end

  defp function_bindings(_decl), do: []

  defp type_bindings(decl) do
    Enum.map(type_names(decl), &{&1, declaration_name_span(decl)})
  end

  defp module_name_atom({:container, meta, _body}) when is_list(meta) do
    case Keyword.get(meta, :name) do
      n when is_binary(n) -> String.to_atom(n)
      n when is_atom(n) -> n
    end
  end

  # Each top-level module is its own namespace — it compiles to its own BEAM module
  # (`Cure.A`, `Cure.B`), so two SIBLING modules may legitimately share a type /
  # constructor / function name (the stdlib has `map` in five modules). Cross-module
  # collisions are resolved by the E-layer resolution/rekey machinery (LOCKED
  # type-shadowing Approach B), not by rejection. The duplicate checks below
  # therefore run PER MODULE: only a repeat WITHIN one module is the silent
  # `Map.put` overwrite bug. `module_decl_groups/1` returns one declaration list per
  # module (an AST with no module wrapper is a single namespace).
  defp module_decl_groups(ast) do
    case top_modules(ast) do
      [] -> [declarations(ast)]
      mods -> Enum.map(mods, &declarations/1)
    end
  end

  defp top_modules({:block, _meta, items}) when is_list(items),
    do: Enum.flat_map(items, &top_modules/1)

  defp top_modules({:container, meta, _body} = node) when is_list(meta) do
    if module_like_container?(meta), do: [node], else: []
  end

  defp top_modules(_), do: []

  # A module must not declare the same type name twice: `env.families` is a silent
  # `Map.put`, so the second would overwrite the first.
  @spec check_no_duplicate_types(tuple() | list()) :: :ok | {:error, term()}
  defp check_no_duplicate_types(ast) do
    ast
    |> module_decl_groups()
    |> Enum.reduce_while(:ok, fn decls, :ok ->
      case first_duplicate_type(decls) do
        nil -> {:cont, :ok}
        details -> {:halt, {:error, {:duplicate_type, details}}}
      end
    end)
  end

  defp first_duplicate_type(decls) do
    decls
    |> Enum.reduce_while(%{}, fn decl, seen ->
      case type_names(decl) do
        [name] ->
          span = declaration_name_span(decl)

          case Map.fetch(seen, name) do
            {:ok, first_span} ->
              {:halt, %{name: name, spans: Enum.reject([first_span, span], &is_nil/1)}}

            :error ->
              {:cont, Map.put(seen, name, span)}
          end

        _ ->
          {:cont, seen}
      end
    end)
    |> case do
      %{name: _name, spans: _spans} = details -> details
      _seen -> nil
    end
  end

  defp declaration_name_span({_tag, meta, _payload}) when is_list(meta) do
    case Cure.MetaAST.Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{name: %Cure.Diagnostic.Span{} = span} -> span
      _ -> nil
    end
  end

  # Type names a declaration binds. `:interface` belongs here: `Cure.Elab.Interface`
  # declares the interface's DICTIONARY as a record family of the same name, through the
  # same `Inductive.declare/3` (a bare `Map.put`) that `type`/`indexed type`/`rec` use.
  # Omitting it let `interface Equatable(a)` and a sibling `type Equatable = Foo | Bar`
  # both register a family named `:Equatable`: whichever elaborated second won the slot,
  # and `env.ctor_to_family` kept a dangling entry for the loser's constructor.
  defp type_names({tag, meta, _})
       when tag in [:container, :indexed_type, :type_annotation, :interface] and is_list(meta) do
    case Keyword.get(meta, :name) do
      n when is_binary(n) -> [String.to_atom(n)]
      n when is_atom(n) and not is_nil(n) -> [n]
      _ -> []
    end
  end

  defp type_names(_decl), do: []

  # A module must not bind the same constructor name twice — within one type
  # (`A | A`) or across two types in the same module (`env.ctor_to_family` maps each
  # ctor to ONE family, so a shared name silently loses one family, an unsound state
  # since Cure has no type-directed constructor disambiguation).
  @spec check_no_duplicate_ctors(tuple() | list()) :: :ok | {:error, term()}
  defp check_no_duplicate_ctors(ast) do
    ast
    |> module_decl_groups()
    |> Enum.reduce_while(:ok, fn decls, :ok ->
      case first_duplicate_constructor(decls) do
        nil -> {:cont, :ok}
        details -> {:halt, {:error, {:duplicate_constructor, details}}}
      end
    end)
  end

  defp first_duplicate_constructor(decls) do
    decls
    |> Enum.flat_map(&constructor_bindings/1)
    |> Enum.reduce_while(%{}, fn {name, span}, seen ->
      case Map.fetch(seen, name) do
        {:ok, first_span} ->
          {:halt, {:duplicate, %{name: name, spans: Enum.reject([first_span, span], &is_nil/1)}}}

        :error ->
          {:cont, Map.put(seen, name, span)}
      end
    end)
    |> case do
      {:duplicate, details} -> details
      _seen -> nil
    end
  end

  defp constructor_bindings({:container, meta, variants}) when is_list(meta) do
    case Keyword.get(meta, :container_type) do
      :enum ->
        Enum.flat_map(variants, &variant_constructor_binding/1)

      :struct ->
        [{meta |> Keyword.fetch!(:name) |> String.to_atom(), declaration_name_span({:container, meta, variants})}]

      _ ->
        []
    end
  end

  # The parser keeps a single bare RHS in the compact `:type_annotation` form
  # until elaboration decides whether it names an alias target or a nullary
  # constructor. Preserve the existing conservative rule used by `ctor_names/1`:
  # a `variant: true` RHS participates in collision checks, with its exact name
  # range, so `type Bad = Z` cannot silently erase an earlier `Z` constructor.
  defp constructor_bindings({:type_annotation, _meta, [{_tag, rmeta, _} = rhs]})
       when is_list(rmeta) do
    if Keyword.get(rmeta, :variant, false), do: variant_constructor_binding(rhs), else: []
  end

  defp constructor_bindings({:indexed_type, _meta, ctor_sigs}) when is_list(ctor_sigs),
    do: Enum.flat_map(ctor_sigs, &gadt_constructor_binding/1)

  defp constructor_bindings(_decl), do: []

  defp variant_constructor_binding({:variable, meta, name}) when is_list(meta) and is_binary(name),
    do: [{String.to_atom(name), metadata_name_span(meta)}]

  defp variant_constructor_binding({:function_def, meta, _body}) when is_list(meta),
    do: [{meta |> Keyword.fetch!(:name) |> String.to_atom(), metadata_name_span(meta)}]

  defp variant_constructor_binding(_variant), do: []

  defp gadt_constructor_binding({:gadt_ctor, meta, _body}) when is_list(meta) do
    case Keyword.get(meta, :name) do
      name when is_binary(name) -> [{String.to_atom(name), metadata_name_span(meta)}]
      name when is_atom(name) and not is_nil(name) -> [{name, metadata_name_span(meta)}]
      _ -> []
    end
  end

  defp gadt_constructor_binding(_ctor), do: []

  defp metadata_name_span(meta) do
    case Cure.MetaAST.Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{name: %Cure.Diagnostic.Span{} = span} -> span
      _ -> nil
    end
  end

  # A module must not bind one name as BOTH a constructor and a top-level function.
  # `type Foo = C` and `fn C() -> Int` both bind `C` in the same namespace; whichever
  # `Resolution` favours, the other is silently unreachable by name. Cure has no
  # type-directed disambiguation, so this must be a compile error rather than a coin
  # flip. Scoped per module, like the other duplicate checks.
  @spec check_no_fn_ctor_collision(tuple() | list()) :: :ok | {:error, term()}
  defp check_no_fn_ctor_collision(ast) do
    ast
    |> module_decl_groups()
    |> Enum.reduce_while(:ok, fn decls, :ok ->
      ctors = decls |> Enum.flat_map(&ctor_names/1) |> MapSet.new()

      decls
      |> Enum.flat_map(fn
        {:function_def, meta, _body} ->
          case Keyword.get(meta, :name) do
            name when is_binary(name) -> [String.to_atom(name)]
            _ -> []
          end

        _ ->
          []
      end)
      |> Enum.find(&MapSet.member?(ctors, &1))
      |> case do
        nil -> {:cont, :ok}
        clash -> {:halt, {:error, {:constructor_function_collision, clash}}}
      end
    end)
  end

  # Same-name top-level function defs are NO LONGER rejected here. A type-distinct
  # pair (`plus(Meters,Meters)` and `plus(Grams,Grams)`) is a legal overload set,
  # and telling a genuine duplicate from a set requires the elaborated parameter
  # telescopes, which do not exist at this pre-elaboration gate. The overwrite
  # this check used to guard is prevented instead by registering each member under
  # a discriminated key (`Mod#plus~0`/`Mod#plus~1`, see `annotate_overload_ordinals/1`
  # + `Cure.Elab.Name.overload_key/2`), and an accidental same-signature duplicate
  # is rejected precisely by `check_overload_legality/1` after the register pass.
  # (This function only ever inspected `:function_def` names, so relaxing it fully
  # is exactly "stop rejecting same-name function defs"; the `:duplicate_type` and
  # `:duplicate_constructor` gates are unaffected.)
  @spec check_no_duplicate_defs(tuple() | list()) :: :ok | {:error, term()}
  defp check_no_duplicate_defs(_ast), do: :ok

  @doc false
  @spec check_ast_elixir_core(tuple() | list()) :: {:ok, Env.t()} | {:error, term()}
  def check_ast_elixir_core(ast),
    do: with_loader_session(fn -> check_ast_elixir_core_in_session(ast, [], :ordinary) end)

  defp check_ast_elixir_core_in_session(ast, source_opts, prelude_mode, qualified_envs \\ []) do
    with {:ok, imported, _ambiguous} <- shadow_resolved_imports(ast, qualified_envs),
         {:ok, qualified} <- qualified_resolved_imports(ast, qualified_envs),
         {:ok, prelude} <- checked_prelude_env(ast, prelude_mode),
         owner = find_module_name(ast) || "Main",
         imported = without_incoming_owner(imported, owner),
         qualified = without_incoming_owner(qualified, owner),
         prelude = without_incoming_owner(prelude, owner),
         seeded = Env.with_owner(seed_with_telescope_support(ast), owner),
         {:ok, base} <- merge_env(seeded, prelude),
         {:ok, opened} <- merge_env(base, imported),
         {:ok, merged} <- merge_env(opened, qualified),
         {:ok, merged} <- merge_lifted_surfaces(merged, qualified_envs, owner),
         env0 = install_module_visibility(merged, ast),
         {:ok, env} <- elaborate_declarations(declarations(ast), env0, prelude_source?(ast)),
         :ok <- MacroValidate.check_program(ast, env),
         {:ok, certified} <- certify_type_level_with_source(ast, env, source_opts),
         {:ok, certified} <- Cure.Elab.Equation.generate_all(certified, ast) do
      # Self-compilation of a hinted module (Std.Bool/Std.Sigma) marks its own
      # defs so their intra-module uses keep inlining; any other module name
      # is a no-op here (its hinted imports were marked slice-side).
      {:ok, mark_inline_hints(certified, find_module_name(ast))}
    end
  end

  # A `fsm`/`actor`/`sup`/nested `mod` inside this unit is compiled to its own
  # BEAM module, so the members lifting synthesises (`Event`, `init/1`, ...) are
  # owned by `Demo.Machine`, not `Demo`. Qualified resolution normally reaches
  # another module by loading its interface from the module index -- keyed by
  # source path -- and a lifted module has no source file, so `Machine.Event`
  # was unreachable from the very module that declares it.
  #
  # `Cure.Compiler.codegen_modules_with_main/5` therefore checks the lifted
  # modules first and hands their certified environments in here. The edge is
  # acyclic: `LiftModule.inherit_scope/2` has already inlined whatever the
  # lifted module needs from the enclosing unit, so it never refers back by name.
  #
  # Owner-stripping matters. A lifted env carries an inlined copy of this
  # module's own declarations; merging those back would let a stale copy win the
  # right-biased `Map.merge`. Everything that survives is either the lifted
  # module's own surface or shared prelude/stdlib, identical in both envs.
  defp merge_lifted_surfaces(env, [], _owner), do: {:ok, env}

  defp merge_lifted_surfaces(env, qualified_envs, owner) do
    Enum.reduce_while(qualified_envs, {:ok, env}, fn {_module_name, lifted}, {:ok, acc} ->
      case merge_env(acc, without_incoming_owner(lifted, owner)) do
        {:ok, merged} -> {:cont, {:ok, merged}}
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  # A module cannot import its own prior interface through a transitive prelude
  # edge. In a bulk build, for example, another ambient provider can carry
  # `Std.Sigma` back into `Std.Sigma` even though direct self-injection is
  # excluded. Its old equation index then makes `Equation.generate_all/2`
  # believe the local equations already exist while local registration has
  # replaced their generated theorem definitions. Start the module from a clean
  # same-owner definition/equation namespace; dependencies owned by every other
  # module remain available for conversion and checking.
  defp without_incoming_owner(%Env{} = env, owner) when is_binary(owner) do
    defs = reject_owned(env.defs, owner)
    equations = reject_owned(env.equations, owner)
    coherence = without_owned_coherence(env.coherence, owner)

    certified =
      case env.certified do
        %MapSet{} = names -> MapSet.filter(names, &(Cure.Elab.Name.owner(&1) != owner))
        nil -> nil
      end

    totality_certified =
      case env.totality_certified do
        %MapSet{} = names -> MapSet.filter(names, &(Cure.Elab.Name.owner(&1) != owner))
        nil -> nil
      end

    direct_call_summaries = reject_owned(env.direct_call_summaries, owner)

    totality_component_of =
      Map.reject(env.totality_component_of, fn {key, _digest} ->
        Cure.Elab.Name.owner(key) == owner
      end)

    retained_digests = totality_component_of |> Map.values() |> MapSet.new()
    totality_components = Map.take(env.totality_components, MapSet.to_list(retained_digests))

    %{
      env
      | defs: defs,
        direct_call_summaries: direct_call_summaries,
        totality_components: totality_components,
        totality_component_of: totality_component_of,
        equations: equations,
        certified: certified,
        totality_certified: totality_certified,
        coherence: coherence
    }
  end

  defp reject_owned(table, owner),
    do: Map.reject(table, fn {key, _value} -> Cure.Elab.Name.owner(key) == owner end)

  defp without_owned_coherence(nil, _owner), do: nil

  defp without_owned_coherence(%Coherence{} = coherence, owner) do
    anon = Map.reject(coherence.anon, fn {_key, ref} -> instance_owned_by?(ref, owner) end)
    named = Map.reject(coherence.named, fn {_key, ref} -> instance_owned_by?(ref, owner) end)

    %Coherence{
      anon: anon,
      named: named,
      anon_origins: Map.take(coherence.anon_origins, Map.keys(anon)),
      named_origins: Map.take(coherence.named_origins, Map.keys(named))
    }
  end

  defp certify_type_level_with_source(ast, env, opts) do
    case TotalityClosure.certify_type_level_detailed(env) do
      {:ok, certified} ->
        {:ok, certified}

      {:error, {:totality_required, name, detail}} ->
        reason = {:totality_required, name}
        {:error, {:source_context, reason, totality_source_context(ast, name, detail, opts)}}

      {:error, {:compile_time_totality, name, detail} = reason} ->
        {:error, {:source_context, reason, totality_source_context(ast, name, detail, opts)}}

      {:error, reason} ->
        {:error, reason}
    end
  end

  defp totality_source_context(ast, qualified_name, detail, opts) do
    bare_name = qualified_name |> to_string() |> String.split("#") |> List.last()

    declaration =
      Enum.find(declarations(ast), fn
        {:function_def, meta, _body} when is_list(meta) -> to_string(Keyword.get(meta, :name)) == bare_name
        _ -> false
      end)

    {name_span, definition_span, recursive_call_spans} =
      case declaration do
        {:function_def, meta, body} ->
          case Cure.MetaAST.Metadata.source_info(meta) do
            %Cure.MetaAST.SourceInfo{name: name, whole: whole} ->
              {name, whole, recursive_call_spans(body, bare_name)}

            _ ->
              {nil, nil, recursive_call_spans(body, bare_name)}
          end

        _ ->
          {nil, nil, []}
      end

    context = %{
      span: name_span || definition_span,
      definition_span: definition_span,
      recursive_call_spans: recursive_call_spans,
      totality_reason: detail,
      checking: qualified_name,
      expectation_origin: :type_level_totality,
      expression_category: :function_definition
    }

    case {Keyword.get(opts, :source), Keyword.get(opts, :file)} do
      {source, file} when is_binary(source) and is_binary(file) ->
        Map.merge(context, %{source: source, file: file})

      _ ->
        context
    end
  end

  defp recursive_call_spans({:function_call, meta, arguments}, bare_name) when is_list(meta) do
    own =
      if same_surface_name?(Keyword.get(meta, :name), bare_name) do
        case Cure.MetaAST.Metadata.source_info(meta) do
          %Cure.MetaAST.SourceInfo{callee: %Cure.Diagnostic.Span{} = span} -> [span]
          %Cure.MetaAST.SourceInfo{whole: %Cure.Diagnostic.Span{} = span} -> [span]
          _ -> []
        end
      else
        []
      end

    own ++ Enum.flat_map(arguments, &recursive_call_spans(&1, bare_name))
  end

  defp recursive_call_spans({_tag, _meta, children}, bare_name),
    do: recursive_call_spans(children, bare_name)

  defp recursive_call_spans(items, bare_name) when is_list(items),
    do: Enum.flat_map(items, &recursive_call_spans(&1, bare_name))

  defp recursive_call_spans(item, bare_name) when is_tuple(item) do
    item
    |> Tuple.to_list()
    |> Enum.flat_map(&recursive_call_spans(&1, bare_name))
  end

  defp recursive_call_spans(_item, _bare_name), do: []

  defp same_surface_name?(name, bare_name) when is_atom(name) or is_binary(name) do
    name
    |> to_string()
    |> String.split(["#", "."])
    |> List.last()
    |> Kernel.==(bare_name)
  end

  defp same_surface_name?(_name, _bare_name), do: false

  @doc "Expand Tier-3 computed uses that occur in declaration position."
  @spec expand_declaration_uses(tuple() | list()) :: {:ok, term()} | {:error, term()}
  def expand_declaration_uses(ast) do
    if declaration_computed_use?(ast) do
      # Prepare the macro execution environment without checking unrelated
      # function bodies yet. A declaration macro may introduce a nominal type
      # that later functions use; checking those functions before expansion
      # would report the generated name as unknown and make the declaration
      # pass order-dependent. Computed elaborator functions themselves remain
      # in the preparation AST so local macro definitions keep working.
      prep_ast = declaration_expansion_prep(ast)

      with {:ok, env} <- check_ast_elixir_core(prep_ast),
           {:ok, expanded} <- expand_declaration_nodes(ast, env) do
        {:ok, unwrap_sole_lifted_module(expanded)}
      end
    else
      {:ok, ast}
    end
  end

  # A parse-time `becomes lift module name` template yields a bare top-level
  # `:lift_module` node, so a bare (mod-less) single-actor program has the lifted
  # module as its top-level module identity and `compile_and_load` returns the
  # actor. A computed/family expansion instead wraps its single lifted module in
  # the expander's general `:block` shape; left wrapped, the program's stripped
  # main AST is an empty block and codegen emits an empty `Cure.Main` wrapper
  # rather than the actor. Normalize that sole-lifted-module block to the bare
  # `:lift_module` so both surfaces agree downstream. Only the very top level of
  # the expansion is unwrapped; a lifted module nested inside a `mod`/container
  # is reached through the container recursion and stays wrapped, so mod-scoped
  # programs still return their own module.
  defp unwrap_sole_lifted_module({tag, _meta, [{:lift_module, _, _} = lifted]})
       when tag in [:block, :container],
       do: lifted

  defp unwrap_sole_lifted_module(other), do: other

  # Declaration expansion must not descend into function bodies. Those uses are
  # expanded by Declarations with the callback context already attached to the
  # function metadata; expanding them here would erase that lexical context.
  defp declaration_computed_use?({:computed_use, _meta, _children}), do: true
  defp declaration_computed_use?({:function_def, _meta, _body}), do: false
  defp declaration_computed_use?({:macro_def, _meta, _rules}), do: false

  defp declaration_computed_use?({tag, _meta, children})
       when tag in [:block, :container] and is_list(children),
       do: Enum.any?(children, &declaration_computed_use?/1)

  defp declaration_computed_use?(list) when is_list(list),
    do: Enum.any?(list, &declaration_computed_use?/1)

  defp declaration_computed_use?(_other), do: false

  defp declaration_expansion_prep(ast) do
    names = declaration_expansion_elab_names(ast)
    declaration_expansion_prep(ast, names)
  end

  defp declaration_expansion_elab_names(ast) do
    ast
    |> collect_declaration_expansion_elab_names([])
    |> MapSet.new()
  end

  defp collect_declaration_expansion_elab_names({:computed_use, _meta, [elab | _]}, acc) do
    case elab do
      {:variable, _meta, name} when is_binary(name) -> [String.to_atom(name) | acc]
      {:variable, _meta, name} when is_atom(name) -> [name | acc]
      _ -> acc
    end
  end

  defp collect_declaration_expansion_elab_names({tag, _meta, children}, acc)
       when is_atom(tag) and is_list(children),
       do: Enum.reduce(children, acc, &collect_declaration_expansion_elab_names/2)

  defp collect_declaration_expansion_elab_names(list, acc) when is_list(list),
    do: Enum.reduce(list, acc, &collect_declaration_expansion_elab_names/2)

  defp collect_declaration_expansion_elab_names(_other, acc), do: acc

  defp declaration_expansion_prep({:function_def, meta, _body} = node, names) when is_list(meta) do
    name = Keyword.get(meta, :name)
    name = if is_binary(name), do: String.to_atom(name), else: name
    if MapSet.member?(names, name), do: node, else: nil
  end

  defp declaration_expansion_prep({tag, meta, children}, names)
       when is_atom(tag) and is_list(meta) and is_list(children) do
    children =
      children
      |> Enum.map(&declaration_expansion_prep(&1, names))
      |> Enum.reject(&is_nil/1)

    {tag, meta, children}
  end

  defp declaration_expansion_prep(list, names) when is_list(list) do
    list
    |> Enum.map(&declaration_expansion_prep(&1, names))
    |> Enum.reject(&is_nil/1)
  end

  defp declaration_expansion_prep(other, _names), do: other

  defp expand_declaration_nodes({:computed_use, _meta, _children} = node, env) do
    MacroExpand.expand(node, env)
  end

  defp expand_declaration_nodes({:function_def, _meta, _body} = node, _env), do: {:ok, node}
  defp expand_declaration_nodes({:macro_def, _meta, _rules} = node, _env), do: {:ok, node}

  defp expand_declaration_nodes({tag, meta, children}, env)
       when tag in [:block, :container] and is_list(children) do
    with {:ok, children} <- expand_declaration_nodes(children, env) do
      {:ok, {tag, meta, children}}
    end
  end

  defp expand_declaration_nodes(list, env) when is_list(list) do
    Enum.reduce_while(list, {:ok, []}, fn node, {:ok, acc} ->
      case expand_declaration_nodes(node, env) do
        {:ok, expanded} -> {:cont, {:ok, [expanded | acc]}}
        {:error, _} = error -> {:halt, error}
      end
    end)
    |> case do
      {:ok, nodes} -> {:ok, Enum.reverse(nodes)}
      {:error, _} = error -> error
    end
  end

  defp expand_declaration_nodes(node, _env), do: {:ok, node}

  @doc false
  @spec local_def_names(tuple() | list()) :: [atom()]
  def local_def_names(ast) do
    ast
    |> declarations()
    |> Enum.flat_map(fn
      {:function_def, meta, _body} ->
        case Keyword.get(meta, :name) do
          name when is_binary(name) -> [String.to_atom(name)]
          _ -> []
        end

      _ ->
        []
    end)
  end

  # The base floor, owned by the module being elaborated.
  defp seed_with_telescope_support(ast) do
    owner = find_module_name(ast) || "Main"
    %Env{} = base = canonical_base_environment(declared_type_names(ast))
    %Env{base | module_owner: owner}
  end

  @doc """
  The floor every module is elaborated against: the kernel seed plus the
  telescope terminator `Std.Unit`.

  This is public because elaboration is not the only thing that needs it.
  Verifying a frozen interface re-checks the same terms, so it has to start from
  the same floor — a smaller one would reject a module for mentioning something
  the compiler itself provided.

  `Unit` (the empty telescope `%[]` / `Tuple()`, the terminator of the
  unit-terminated Σ chain a flat `Tuple(…)` unfolds to — spec
  2026-07-09-unified-tuple §3.4) is declared here in the E-LAYER via the ordinary
  `Inductive.declare/3` that `type`/`rec` use, NOT in the trusted
  `Core.Builtins` seed: it needs no `@builtin` schema and carries no kernel-
  judgement change, so it stays out of the TCB. A module declaring its own `Unit`
  shadows this (the local declaration overwrites the same key), same as any
  seeded builtin. `unit : Unit` is a plain nullary inductive.
  """
  @spec canonical_base_environment(MapSet.t()) :: Env.t()
  def canonical_base_environment(shadowed \\ MapSet.new()) do
    seeded = Cure.Core.Builtins.seed(Env.empty(), shadowed)

    if MapSet.member?(shadowed, :Unit) do
      seeded
    else
      unit_env = Env.with_owner(seeded, "Std.Unit")

      Inductive.declare(
        seeded,
        Inductive.family(Env.owned_name(unit_env, :Unit), [], [], 0),
        [Inductive.ctor(Env.owned_name(unit_env, :unit), [], [])]
      )
    end
  end

  # Family/type names the module declares itself. A builtin (Bool/Nat) is NOT
  # seeded into env0 when the module declares its own same-named type — the local
  # declaration is canonical, and seeding a look-alike would pollute its ctor set.
  defp declared_type_names(ast) do
    ast
    |> declarations()
    |> Enum.flat_map(&type_names/1)
    |> MapSet.new()
  end

  # Constructor names declared directly by the module. Type-name shadowing does
  # not shadow constructors; constructor-name shadowing is decided independently.
  defp declared_ctor_names(ast) do
    ast
    |> declarations()
    |> Enum.flat_map(&ctor_names/1)
    |> MapSet.new()
  end

  defp ctor_names({:container, meta, variants}) when is_list(meta) do
    case Keyword.get(meta, :container_type) do
      :enum -> Enum.flat_map(variants, &variant_ctor_names/1)
      :struct -> [meta |> Keyword.fetch!(:name) |> String.to_atom()]
      _ -> []
    end
  end

  defp ctor_names({:indexed_type, _meta, ctor_sigs}), do: Enum.flat_map(ctor_sigs, &gadt_ctor_names/1)

  # `type X = Y` with a single bare RHS is either a one-constructor enum (`type Unit =
  # MkUnit`) or an alias (`type MyNat = Nat`), decided by whether `Y` names a type — a
  # question this AST-level scan cannot answer. The parser tags both `variant: true`.
  # Counting `Y` as a constructor over-approximates: it also names the alias's target.
  # That is the safe direction (the checks it feeds reject ambiguity), and it only bites
  # a module that aliases a type AND declares a function with that type's exact,
  # capitalized name.
  defp ctor_names({:type_annotation, _meta, [{_tag, rmeta, _} = rhs]}) when is_list(rmeta) do
    if Keyword.get(rmeta, :variant, false), do: variant_ctor_names(rhs), else: []
  end

  defp ctor_names(_decl), do: []

  defp variant_ctor_names({:variable, _meta, name}) when is_binary(name), do: [String.to_atom(name)]
  defp variant_ctor_names({:function_def, meta, _body}), do: [meta |> Keyword.fetch!(:name) |> String.to_atom()]
  defp variant_ctor_names(_variant), do: []

  defp gadt_ctor_names({:gadt_ctor, meta, _body}) when is_list(meta),
    do: [meta |> Keyword.fetch!(:name) |> String.to_atom()]

  defp gadt_ctor_names(_sig), do: []

  # A source is a designated prelude source iff its own declared module name is
  # a key of the stdlib module registry. Only such sources may register a
  # `@builtin(:key)`; ordinary user code declaring the same decorator is ignored
  # (spec §1 single-registration invariant).
  defp prelude_source?(ast),
    do: Map.has_key?(Cure.Stdlib.Preload.module_groups(), module_atom(ast))

  # ── `@prelude` decorator ───────────────────────────────────────────────────
  #
  # A stdlib item marked `@prelude` (see `lib/std/string.cure`'s `String` alias)
  # joins the IMPLICIT prelude: its name resolves in every module with no `use`.
  # `@prelude` is declared at the DEFINITION site and may be item-granular — preluding `type String`
  # brings the alias without dragging `Std.String`'s whole function surface (which
  # would shadow user `length`/`reverse`/…). Discovery scans the stdlib sources for
  # the marker; the resulting slice is merged UNDER the explicit imports (so a
  # `use` still wins) and under the module's own declarations.
  defp prelude_slice_env(ast) do
    self = find_module_name(ast)
    local = declared_names(ast)

    prelude_manifest()
    |> Enum.reject(fn entry -> entry.source == self end)
    |> Enum.reduce_while({:ok, Env.empty()}, fn entry, {:ok, acc} ->
      case prelude_entry_env(entry, local) do
        {:ok, slice} ->
          case merge_env(acc, slice) do
            {:ok, merged} -> {:cont, {:ok, merged}}
            {:error, _} = err -> {:halt, err}
          end

        {:error, _} = err ->
          {:halt, err}
      end
    end)
  end

  # Elaborate one prelude-contributing module and restrict its env to the
  # `@prelude`-marked names (minus any the importer declares locally — a local
  # decl shadows the prelude). A whole-module `@prelude` keeps everything.
  defp prelude_entry_env(%{source: source, path: path, names: names}, local) do
    with {:ok, full} <- import_source_env({:ok, source, path}, MapSet.new()) do
      keep =
        case names do
          :all -> :all
          set -> MapSet.difference(set, local)
        end

      {:ok, restrict_env_to(full, keep)}
    end
  end

  # Keep only the named defs/families/constructors from an elaborated env. List /
  # Char and the other seeded builtins stay ambient via the base seed, so a
  # type-alias slice (`String := List(Char)`) needs only its def entry; a
  # `@prelude type` also keeps its family and constructors. `certified` is kept
  # whole — it is a totality whitelist, so a superset is harmless.

  # A whole-module `@prelude` (`names == :all`, e.g. `Std.Equatable`) exports its
  # OWN surface ambiently, but NOT the defs it merely `use`d: keeping them whole
  # would leak, say, `Std.String.to_int`/`length`/`reverse` into every module (via
  # `Std.Equatable`'s `use Std.String`), silently shadowing a user's own `length`
  # and making unqualified overload resolution ambiguous. Restrict the def/family/
  # ctor surface to entries this module OWNS (keyed `"<Owner>#name"`). Coherence is
  # kept WHOLE — instance resolution is the very reason a typeclass module is
  # `@prelude`, and instances are cumulative, not owned; `certified`/`primitives`
  # (seeded builtins) are harmless supersets and kept whole too.
  defp restrict_env_to(%Env{module_owner: owner} = env, :all) when is_binary(owner) do
    owned_def_keys = env.defs |> Map.keys() |> Enum.filter(&owned_by_module?(&1, owner))

    # Restrict only the FUNCTION-def surface — that is where the leak lives: keeping
    # `Std.Equatable`'s `use Std.String` whole would make `Std.String.to_int`/`length`/
    # `reverse` ambient in every module, shadowing a user's own `length` and making
    # unqualified overload resolution ambiguous. Keep entries this module OWNS *plus
    # the transitive closure of globals those owned defs reference* — a
    # `Comparable`/`Equatable` instance body for `Char` (which whnf's to `Bounded`)
    # calls `Std.Char.code_point`, owned by `Std.Char`, which no WHOLE-module
    # `@prelude` provider contributes (only its `Char` alias is item-preluded). Drop
    # it and the ambient instance body dangles — the kernel re-checks it as
    # `unknown_global`. The closure pulls in exactly the cross-module defs the kept
    # surface depends on (`code_point`, `string_lt`, …) and NOT the whole imported
    # surface: `to_int`/`length`/`reverse` are unreachable from any kept body and so
    # stay out, preserving the no-ambient-`to_int`-leak the owner scoping exists for.
    #
    # FAMILIES and CONSTRUCTORS are kept WHOLE: they are TYPES, not the function names
    # the leak concerns, and the kernel needs the full type surface to re-check the
    # kept instance bodies (e.g. `string_lt` matches on `String = List(Char)`, so the
    # `List` family and its constructors must resolve or the scrutinee is
    # `case_scrutinee_not_data`). Type shadowing (E-layer collision re-key) already
    # handles a user type that reuses an ambient type name, so a whole type surface is
    # sound. `certified` is a totality whitelist (superset harmless); coherence is the
    # very point of a typeclass prelude and stays whole too.
    # Coherence is kept WHOLE (below), so the closure must be seeded with the
    # method globals those kept instances name, not only with the owned defs. An
    # instance that reached this provider's env transitively is owned by neither
    # the provider nor anything its owned bodies call — `Std.Equatable`'s env
    # carries `ExpressibleByCharacterLiteral for Char`, whose method is owned by
    # `Std.Literal` and reached from no kept body. Seeding only `owned_def_keys`
    # drops it and leaves the ref dangling: the slice still ANSWERS instance
    # resolution with a global that is no longer a def, so a module writing
    # `c == '|'` fails far away with
    # `{:unknown_global, :"Std.Literal#__impl_…_from_character_literal"}`,
    # or — at a literal initializer — with an unsolved `{:hole, "__pending__"}` head.
    keep_keys = reachable_global_closure(env.defs, owned_def_keys ++ coherence_method_globals(env))
    kept_defs = Map.take(env.defs, keep_keys)

    # `import_modules` is the DIRECTNESS set `Resolution.prefer_direct/2` uses to
    # let an explicit `use` shadow a transitive re-export. Passing this provider's
    # OWN import list through would make ITS dependencies count as direct imports
    # of every module the slice lands in — so `Std.Equatable`'s `use Std.Option`
    # would make `Std.Option#map` a direct provider of `map` everywhere, tying
    # with `Std.List#map` under an explicit `use Std.List` and pushing a
    # previously unambiguous call onto the overload path. The prelude is merged
    # UNDER explicit imports precisely so a `use` still wins, so the slice
    # confers NO directness — not even the provider's own name, which would make
    # ambient `Std.Bounded#Next` tie with an explicitly imported `Std.Fsm#Next`.
    %Env{env | defs: kept_defs, import_modules: MapSet.new()}
  end

  defp restrict_env_to(%Env{} = env, :all), do: env

  defp restrict_env_to(%Env{} = env, %MapSet{} = names) do
    name_list = MapSet.to_list(names)
    def_names = Enum.map(name_list, &Env.resolve_key(env, env.defs, &1))
    fam_names = Enum.map(name_list, &Env.resolve_key(env, env.families, &1))
    fam_names = Enum.filter(fam_names, &Map.has_key?(env.families, &1))
    kept_ctors = for {c, f} <- env.ctor_to_family, f in fam_names, into: %{}, do: {c, f}
    kept_equations = Map.take(env.equations, def_names)
    equation_defs = kept_equations |> Map.values() |> List.flatten() |> Enum.map(& &1.theorem)

    # An item-level `@prelude` names a TYPE, and a type ambient without its
    # conformances is not usable: `"hi"` is checked by normalising
    # `from_string_literal(StringLiteral(…))`, and `a <> b` dispatches
    # `Std.Semigroup.combine` — both live in instances declared for
    # `Std.String#String`, not in the `String` declaration itself. Those
    # instances used to arrive here only by accident, through a whole-module
    # provider that transitively imported `Std.String` (`Std.Literal` reached
    # it via `Std.Char`), so removing that import silently un-ambiented every
    # string literal in a module with no `use`. The conformances of a preluded
    # head travel WITH it instead: exactly the instances for the kept families,
    # the interfaces they implement, and the transitive closure of globals
    # their method bodies name (`concat`, `characters`, …). The rest of the
    # provider's function surface stays out, which is the point of an
    # item-granular marker, and the slice still confers no bare visibility.
    coherence = restrict_coherence_to_heads(env.coherence, fam_names)
    conformance_defs = reachable_global_closure(env.defs, coherence_method_globals(%Env{env | coherence: coherence}))
    kept_interfaces = Map.take(env.interfaces, coherence_interfaces(coherence))

    %Env{
      Env.empty()
      | defs: Map.take(env.defs, def_names ++ equation_defs ++ Map.keys(kept_ctors) ++ conformance_defs),
        families: Map.take(env.families, fam_names),
        ctors: Map.take(env.ctors, Map.keys(kept_ctors)),
        ctor_to_family: kept_ctors,
        builtins: Map.filter(env.builtins, fn {_key, family} -> family in fam_names end),
        primitives: Map.take(env.primitives, name_list),
        equations: kept_equations,
        certified: env.certified,
        totality_certified: env.totality_certified,
        coherence: coherence,
        module_owner: env.module_owner
    }
    |> Env.with_interfaces(kept_interfaces)
  end

  # The instances registered for one of `heads`, anonymous and named alike. A
  # registry with no surviving entry is dropped entirely rather than kept as an
  # empty struct, so a slice that prelude-marks a plain type still merges as it
  # did before.
  defp restrict_coherence_to_heads(nil, _heads), do: nil

  defp restrict_coherence_to_heads(%Coherence{} = coherence, heads) do
    kept = MapSet.new(heads)
    keep? = fn ref -> MapSet.member?(kept, Map.get(ref, :head)) end

    anon = Map.filter(coherence.anon, fn {_key, ref} -> keep?.(ref) end)
    named = Map.filter(coherence.named, fn {_name, ref} -> keep?.(ref) end)

    if anon == %{} and named == %{} do
      nil
    else
      %Coherence{
        anon: anon,
        named: named,
        anon_origins: Map.take(coherence.anon_origins, Map.keys(anon)),
        named_origins: Map.take(coherence.named_origins, Map.keys(named))
      }
    end
  end

  # The interfaces named by a coherence registry. Method dispatch reads the
  # interface table (`Interface.for_method/2`), so an instance kept without its
  # interface answers nothing.
  defp coherence_interfaces(nil), do: []

  defp coherence_interfaces(%Coherence{} = coherence) do
    for table <- [coherence.anon, coherence.named],
        {_key, ref} <- table,
        iface = Map.get(ref, :iface),
        not is_nil(iface),
        uniq: true,
        do: iface
  end

  # Every method global named by an instance in `env`'s coherence that is a def in
  # `env`. Filtering to actual defs keeps this a seed for the closure and nothing
  # more: a ref that already dangled upstream is not conjured into existence here,
  # it stays a kernel-re-check failure at the site that uses it.
  defp coherence_method_globals(%Env{coherence: nil}), do: []

  defp coherence_method_globals(%Env{coherence: coherence, defs: defs}) do
    for table <- [coherence.anon, coherence.named],
        {_key, ref} <- table,
        {_method, global} <- Map.get(ref, :methods) || %{},
        Map.has_key?(defs, global),
        uniq: true,
        do: global
  end

  # Is `key` (an owner-qualified `"<Owner>#name"` atom) owned by module `owner`?
  # A bare/content-derived key with no `"<owner>#"` prefix is not owned.
  defp owned_by_module?(key, owner) do
    case :binary.split(Atom.to_string(key), "#") do
      [prefix, _rest] -> prefix == owner
      _ -> false
    end
  end

  # Transitive closure of `defs` keys reachable from `seed_keys` by following the
  # `{:global, g}` references in each def's `type` and `body`. Only globals that
  # resolve to a def IN `defs` are followed; unresolved names are ignored here — a
  # genuinely missing global surfaces at kernel re-check, not by silent inclusion.
  defp reachable_global_closure(defs, seed_keys) do
    seen = MapSet.new(seed_keys)
    do_reachable_closure(defs, seen, seed_keys)
  end

  defp do_reachable_closure(_defs, seen, []), do: MapSet.to_list(seen)

  defp do_reachable_closure(defs, seen, [key | rest]) do
    case Map.get(defs, key) do
      %{} = record ->
        referenced =
          MapSet.new()
          |> gather_def_globals(Map.get(record, :type))
          |> gather_def_globals(Map.get(record, :body))

        fresh =
          for g <- referenced,
              Map.has_key?(defs, g),
              not MapSet.member?(seen, g),
              do: g

        do_reachable_closure(defs, Enum.reduce(fresh, seen, &MapSet.put(&2, &1)), rest ++ fresh)

      _ ->
        do_reachable_closure(defs, seen, rest)
    end
  end

  # Collect every `{:global, g}` atom mentioned anywhere in a Core term (generic
  # tuple/list walk — Core terms are plain tuples and lists).
  defp gather_def_globals(acc, {:global, g}), do: MapSet.put(acc, g)

  defp gather_def_globals(acc, t) when is_tuple(t),
    do: t |> Tuple.to_list() |> Enum.reduce(acc, &gather_def_globals(&2, &1))

  defp gather_def_globals(acc, l) when is_list(l),
    do: Enum.reduce(l, acc, &gather_def_globals(&2, &1))

  defp gather_def_globals(acc, _), do: acc

  # `@prelude`-marked items across the stdlib tree, as a list of
  # `%{source, path, names}` (names = a `MapSet` of item names, or `:all` for a
  # whole-module mark). Discovered by scanning the stdlib sources for the marker —
  # membership lives at the definition site, not in a hand-kept list. Cached in
  # `:persistent_term`: the stdlib is fixed for a compiler build, and this runs
  # only in the HOST compiler, never on AtomVM (where `persistent_term` is absent).
  #
  # Public (but `@doc false`) so the incremental driver can observe the cached
  # set and so tests can assert its content; not part of the stable API.
  @doc false
  @spec prelude_manifest() :: [%{source: String.t(), path: String.t(), names: :all | MapSet.t()}]
  def prelude_manifest do
    case Paths.source_dir() do
      nil ->
        []

      dir ->
        key = {__MODULE__, :prelude_manifest, dir}

        case :persistent_term.get(key, :miss) do
          :miss ->
            # `persistent_term` makes hits cheap, but its get/scan/put sequence
            # is not atomic. A broad async test run used to send many elaborator
            # processes through the full stdlib parse simultaneously, saturating
            # the file server long enough for unrelated 8-second tests to time
            # out. Serialize only the cold miss and recheck after acquiring the
            # lock; steady-state reads remain one `persistent_term.get/2`.
            :global.trans({key, self()}, fn ->
              case :persistent_term.get(key, :miss) do
                :miss ->
                  manifest = scan_prelude_manifest(dir)
                  :persistent_term.put(key, manifest)
                  manifest

                cached ->
                  cached
              end
            end)

          cached ->
            cached
        end
    end
  end

  @doc """
  Evict the memoized `@prelude` manifest for the current stdlib source dir, if
  cached, so the next `prelude_manifest/0` re-scans current source content.

  `prelude_manifest/0` caches per source dir under the same "stdlib is immutable
  for the process lifetime" assumption `cached_module_interface/2` makes — and
  that incremental compilation of the stdlib likewise violates. If a stdlib
  source's `@prelude` markers change between two same-process builds, a stale
  manifest would keep elaborating later modules against the OLD ambient set. The
  incremental driver calls this once at the start of a build that recompiles any
  stdlib source, mirroring `invalidate_module_interface/1`.
  """
  @spec invalidate_prelude_manifest() :: :ok
  def invalidate_prelude_manifest do
    case Paths.source_dir() do
      nil ->
        :ok

      dir ->
        key = {__MODULE__, :prelude_manifest, dir}
        :global.trans({key, self()}, fn -> :persistent_term.erase(key) end)
    end

    :ok
  end

  defp scan_prelude_manifest(dir) do
    dir
    |> Path.join("*.cure")
    |> Path.wildcard()
    |> Enum.flat_map(fn path ->
      with {:ok, src} <- File.read(path),
           {:ok, tokens} <- Lexer.tokenize(src, emit_events: false),
           {:ok, ast} <- Parser.parse(tokens, emit_events: false),
           source when is_binary(source) <- find_module_name(ast),
           names when names != [] <- prelude_marked_names(ast) do
        [%{source: source, path: path, names: if(names == :all, do: :all, else: MapSet.new(names))}]
      else
        _ -> []
      end
    end)
  end

  # The names of `@prelude`-marked declarations in a module's AST. A `typealias`
  # (`{:type_annotation}`), `fn` (`{:function_def}`), and enum/indexed `type`
  # container all carry the decorator in their meta once the parser attached it.
  defp prelude_marked_names(ast) do
    if module_prelude_decorated?(ast) do
      :all
    else
      ast
      |> declarations()
      |> Enum.flat_map(fn decl ->
        if prelude_decorated?(decl), do: List.wrap(declaration_name(decl)), else: []
      end)
      |> Kernel.++(prelude_property_names(ast))
      |> Enum.uniq()
    end
  end

  defp module_prelude_decorated?({:block, _meta, items}) when is_list(items) do
    (Enum.any?(items, &prelude_property?/1) and
       Enum.any?(items, &match?({:container, meta, _} when is_list(meta), &1))) or
      Enum.any?(items, &module_prelude_decorated?/1)
  end

  defp module_prelude_decorated?({:container, meta, _body}) when is_list(meta),
    do: module_like_container?(meta) and match?({:prelude, _}, Keyword.get(meta, :decorator))

  defp module_prelude_decorated?(_other), do: false

  defp prelude_property_names({:container, meta, body}) when is_list(meta) and is_list(body) do
    if module_like_container?(meta), do: prelude_property_names_in(body), else: []
  end

  defp prelude_property_names({:block, _meta, items}) when is_list(items),
    do: Enum.flat_map(items, &prelude_property_names/1)

  defp prelude_property_names(_other), do: []

  defp prelude_property_names_in(items) do
    {_pending, names} =
      Enum.reduce(items, {false, []}, fn item, {pending, names} ->
        cond do
          prelude_property?(item) ->
            {true, names}

          pending ->
            {false, List.wrap(declaration_name(item)) ++ names}

          true ->
            {false, names}
        end
      end)

    Enum.reverse(names)
  end

  defp prelude_property?({:property, meta, _children}) when is_list(meta),
    do: Keyword.get(meta, :name) == "prelude"

  defp prelude_property?(_other), do: false

  defp prelude_decorated?({_tag, meta, _}) when is_list(meta),
    do: attached_decorator_name(Keyword.get(meta, :decorator)) == :prelude

  defp prelude_decorated?(_), do: false

  # The name of an attached decorator node (`{:decorator, [name: n], args}`) held
  # in a def/container meta `:decorator` slot, or `nil` if absent/non-decorator.
  defp attached_decorator_name({:decorator, m, _args}) when is_list(m), do: Keyword.get(m, :name)
  defp attached_decorator_name(_), do: nil

  defp declaration_name({:type_annotation, meta, _}) when is_list(meta),
    do: meta |> Keyword.get(:name) |> to_name_atom()

  defp declaration_name({:function_def, meta, _}) when is_list(meta),
    do: meta |> Keyword.get(:name) |> to_name_atom()

  defp declaration_name({:container, meta, _}) when is_list(meta),
    do: meta |> Keyword.get(:name) |> to_name_atom()

  defp declaration_name({:indexed_type, meta, _}) when is_list(meta),
    do: meta |> Keyword.get(:name) |> to_name_atom()

  defp declaration_name(_), do: nil

  defp to_name_atom(name) when is_binary(name), do: String.to_atom(name)
  defp to_name_atom(_), do: nil

  # Every function/type/constructor NAME a module declares locally, as a MapSet —
  # used so a `@prelude` item is not imported into a module that redefines the same
  # name (the local declaration is canonical). Reuses the existing scanners.
  defp declared_names(ast) do
    MapSet.new(local_def_names(ast))
    |> MapSet.union(declared_type_names(ast))
    |> MapSet.union(declared_ctor_names(ast))
  end

  @doc """
  Elaborate a module and return the definitions declared directly by that
  module. Imported stdlib definitions remain in the env for type checking and
  conversion, but codegen should emit only `local_defs`.
  """
  @spec check_ast_with_locals(tuple() | list()) :: {:ok, Env.t(), [atom()]} | {:error, term()}
  def check_ast_with_locals(ast) do
    with {:ok, %CheckedModule{env: env, local_defs: local_defs}} <- check_ast_artifact(ast) do
      {:ok, env, local_defs}
    end
  end

  @doc """
  The definitions `ast` owns and must therefore emit, given its checked `env`.

  `check_ast_with_locals/1` and `check_ast_artifact/2` both re-elaborate to
  compute this. A caller that has ALREADY elaborated the module — the canonical
  module pipeline holds one checked env per module — needs the answer without
  paying for a second elaboration, and the answer is a pure function of the two
  things it already has.
  """
  @spec local_defs(tuple() | list(), Env.t()) :: [atom()]
  def local_defs(ast, %Env{} = env), do: checked_local_defs(ast, env)

  defp checked_local_defs(ast, env) do
    local_defs = local_emit_names(ast)

    # `implementation` declarations synthesise mangled method globals that are
    # not in the source AST; they are still this module's locals and must be
    # emitted alongside the source-declared defs. But the coherence table also
    # carries every AMBIENT instance a `@prelude` module makes visible — and
    # `Std.Equatable`/`Std.Comparable` are whole-module `@prelude`, so their ~two
    # dozen instances are ambient in EVERY module. Emitting all of them into
    # every consumer bloats each beam with instance methods it never defines
    # (costly on the AtomVM/ESP32 target) and needlessly duplicates code that
    # already lives in the owning module's beam.
    #
    # Each mangled impl key is OWNER-QUALIFIED (`Std.Equatable#__impl_…`), so
    # emit only the instances THIS module owns. A reference to a non-owned
    # instance (a resolved `==`, a constructed dictionary) then falls through
    # `Emit.remote_target/2`'s owner branch to a REMOTE call into the owner's
    # module (`Cure.Std.Equatable`), where the instance is emitted exactly once.
    # Unqualified synthesised globals (owner = nil) have no remote home, so this
    # module must still host them.
    self_owner = ast |> module_atom() |> Atom.to_string() |> String.replace_prefix("Cure.", "")

    canonical_locals =
      Enum.map(local_defs, fn name ->
        if Cure.Elab.Name.qualified?(name),
          do: name,
          else: Cure.Elab.Name.qualify(self_owner, name)
      end)

    own_impls =
      Enum.filter(impl_def_names(env), fn key ->
        case Cure.Elab.Name.owner(key) do
          nil -> true
          ^self_owner -> true
          _ambient -> false
        end
      end)

    roots = Enum.uniq(canonical_locals ++ own_impls)

    # Local `where` functions and other lifted runtime helpers are synthesized
    # during elaboration and therefore do not appear in the authored AST scan.
    # Derive the final emission set from canonical Core edges so those helpers
    # are emitted regardless of declaration order. Qualified dependencies owned
    # by another module stay remote and are not copied into this module.
    Enum.uniq(roots ++ reachable_def_names(env, roots))
  end

  # The def keys codegen must emit, one per source `:function_def`. A member of a
  # same-name group of size >= 2 is registered under a discriminated bare name
  # (`plus~<ord>`, see `annotate_overload_ordinals/1`), so its emit key must carry
  # the SAME ordinal — otherwise both members lower to one BEAM function and
  # `erl_lint` rejects the redefinition. Ordinals are assigned in declaration
  # order, identically to the registration pass, so the emit key and the stored
  # def key agree. A size-one name is returned bare and untouched, keeping
  # non-overloaded codegen byte-identical. (`local_def_names/1` stays the surface
  # spelling for `@prelude`-shadow and import-origin bookkeeping, which key by
  # bare name.)
  defp local_emit_names(ast) do
    names = local_def_names(ast)
    overloaded = for {n, c} <- Enum.frequencies(names), c >= 2, into: MapSet.new(), do: n

    {keys, _counters} =
      Enum.map_reduce(names, %{}, fn name, counters ->
        if MapSet.member?(overloaded, name) do
          ord = Map.get(counters, name, 0)
          {Cure.Elab.Name.overload_key(name, ord), Map.put(counters, name, ord + 1)}
        else
          {name, counters}
        end
      end)

    keys
  end

  @doc """
  Map each `use`-imported function name to the BEAM module atom that DEFINES it,
  so dependent codegen can emit a REMOTE call for a cross-module reference rather
  than an (undefined) local one. Built from the module's transitive import
  closure (direct `use` + the auto-prelude), keyed by bare function name to the
  `Cure.<Module>` atom that owns it; the first owner in import-BFS order wins.
  This module's OWN local definitions are dropped from the map — a local
  definition shadows an imported one, so a call to a locally-defined name stays
  local. `Cure.Elab.Emit` consults this to route `{:global, name}` references
  (the #18 dependent-only codegen enabler). A self-contained module (no
  cross-module calls) yields an empty map and the old all-local behaviour.
  """
  @spec import_origins(tuple() | list()) :: %{atom() => module()}
  def import_origins(ast) do
    local = MapSet.new(local_def_names(ast))
    sources = imports(ast) ++ Enum.map(prelude_manifest(), & &1.source)

    transitive_import_modules(sources)
    |> Enum.reduce(%{}, fn {mod_id, path}, acc ->
      module = String.to_atom("Cure." <> mod_id)
      Enum.reduce(owned_def_names(path), acc, &Map.put_new(&2, &1, module))
    end)
    |> Map.drop(MapSet.to_list(local))
  end

  @doc """
  Names of the globals synthesised by `implementation` declarations (the mangled
  per-method impl bodies + any dictionary values). Codegen must emit these as
  module locals; `Cure.Elab.Resolve` references them by name.
  """
  @spec impl_def_names(Env.t()) :: [atom()]
  def impl_def_names(env) do
    names =
      case Env.coherence(env) do
        nil ->
          []

        %{anon: anon, named: named} ->
          refs = Map.values(anon) ++ Map.values(named)

          method_defs = Enum.flat_map(refs, &Map.values(&1.methods))
          dict_defs = Enum.flat_map(refs, fn ref -> List.wrap(Map.get(ref, :dict)) end)

          Enum.uniq(method_defs ++ dict_defs)
      end

    case env.module_owner do
      nil -> names
      owner -> Enum.filter(names, &(Cure.Elab.Name.owner(&1) in [nil, owner]))
    end
  end

  @doc """
  The transitive closure of local defs reachable from `roots` via `{:global, _}`
  references in def bodies+types.

  Emit lowers a `{:global, name}` to a *local* call within the emitted module, so
  a self-contained module must co-emit every reachable callee — a cross-module
  polymorphic call (e.g. an imported instance body delegating to `Std.List#map`)
  pulls the callee in transitively. Builtin-op defs (body-less; saturated uses
  inline to BEAM operators) are excluded — they never need a function form.
  """
  @spec reachable_def_names(Env.t(), [atom()]) :: [atom()]
  def reachable_def_names(%Env{defs: defs} = env, roots) do
    root_keys = roots |> Enum.map(&reachable_root_key(env, defs, &1)) |> Enum.reject(&is_nil/1)
    local_owners = root_keys |> Enum.map(&Cure.Elab.Name.owner/1) |> MapSet.new()

    Enum.reduce(root_keys, MapSet.new(), fn root, seen ->
      collect_reachable(env, root, local_owners, seen)
    end)
    |> MapSet.to_list()
    |> Enum.sort()
  end

  defp collect_reachable(%Env{defs: defs} = env, name, local_owners, seen) do
    cond do
      MapSet.member?(seen, name) ->
        seen

      match?(%{builtin_op: op} when not is_nil(op), Map.get(defs, name)) ->
        # Body-less builtin op: reachable but never emitted as a function form.
        seen

      match?(%{type: {:type, _}}, Map.get(defs, name)) ->
        # A TYPE-LEVEL def (a type alias like `Char = Bounded(…)`, whose type is
        # `Type`) is referenced from a value body only in a type position (a
        # lambda domain) and is never emitted as a runtime function — skip it and
        # its type-level references entirely.
        seen

      true ->
        case Map.get(defs, name) do
          nil ->
            seen

          d ->
            seen = MapSet.put(seen, name)

            d.body
            |> then(&Cure.Elab.Erase.erase(env, &1))
            |> Cure.Core.RuntimeRefs.globals()
            |> Enum.reduce(seen, fn reference, acc ->
              if Map.has_key?(defs, reference) and
                   MapSet.member?(local_owners, Cure.Elab.Name.owner(reference)),
                 do: collect_reachable(env, reference, local_owners, acc),
                 else: acc
            end)
        end
    end
  end

  # Callers may select a local root by its authored spelling at this public
  # boundary. Convert that spelling once through the current module owner.
  # Recursive closure edges are already Core identities and are never guessed.
  #
  # The owner-qualified key is tried FIRST, because the bare namespace is not
  # exclusively the caller's: `Cure.Core.Builtins.seed_ops/1` seeds every builtin
  # op under its bare spelling, and one of them — `run`, the `Effect` eliminator —
  # is an ordinary word a module may well define. Asking the bare namespace first
  # handed `[:run]` to that body-less builtin, and `collect_reachable/4` records
  # nothing for a builtin op, so the module's own `run` (and everything only it
  # reached) silently dropped out of the emission set. A local definition shadows
  # an ambient one everywhere else in the language; selecting an emission root by
  # authored spelling obeys the same rule. An already-canonical root is unaffected
  # — re-qualifying it yields `Owner#Owner#name`, which is not a key, so it falls
  # through to itself.
  defp reachable_root_key(%Env{module_owner: owner}, defs, root) when is_atom(root) do
    canonical = if is_binary(owner), do: Cure.Elab.Name.qualify(owner, root)

    cond do
      not is_nil(canonical) and Map.has_key?(defs, canonical) ->
        canonical

      Map.has_key?(defs, root) ->
        root

      true ->
        nil
    end
  end

  # Semantic dependency scans (currently type-alias ordering) need globals from
  # every Core position, unlike runtime reachability above.
  defp global_refs({:global, name}), do: [name]

  defp global_refs(term) when is_tuple(term),
    do: term |> Tuple.to_list() |> Enum.flat_map(&global_refs/1)

  defp global_refs(terms) when is_list(terms), do: Enum.flat_map(terms, &global_refs/1)
  defp global_refs(_leaf), do: []

  @doc """
  Extract the `Cure.<Name>` module atom from a parsed `mod … end` program,
  defaulting to `Cure.Main` when no module container is present.
  """
  @spec module_atom(term()) :: module()
  def module_atom(ast), do: String.to_atom("Cure." <> (find_module_name(ast) || "Main"))

  defp find_module_name({:container, meta, _body}) when is_list(meta) do
    if module_like_container?(meta), do: Keyword.get(meta, :name)
  end

  defp find_module_name({_tag, _meta, children}) when is_list(children),
    do: Enum.find_value(children, &find_module_name/1)

  defp find_module_name(list) when is_list(list), do: Enum.find_value(list, &find_module_name/1)
  defp find_module_name(_other), do: nil

  @doc """
  Hole goal reports (design spec §10/§11): for every definition whose body still
  carries a hole, report the hole's **goal type** (the definition's return type)
  and its **local context** (the parameter types in scope). This is the
  `:hole_goal` diagnostic — a hole typechecks, reports what must fill it, and
  blocks codegen until filled.
  """
  @spec hole_goals(Env.t()) :: [%{function: atom(), goal: term(), context: [term()]}]
  def hole_goals(%Env{} = env) do
    defs = program_owned_definitions(env)

    for {name, %{type: type, body: body}} <- defs, Erase.has_hole?(body) do
      {context, goal} = split_pi(type, [])
      %{function: name, goal: goal, context: context}
    end
  end

  defp split_pi({:pi, _g, dom, cod}, acc), do: split_pi(cod, [dom | acc])
  defp split_pi(goal, acc), do: {Enum.reverse(acc), goal}

  @doc """
  Codegen gate (§6 negative #5): a program with an unfilled hole typechecks but
  must not be emitted. Authored definitions return exact source metadata for the
  rejected hole; synthetic Core environments retain the legacy definition name.
  """
  @spec check_codegen_ready(Env.t()) ::
          :ok | {:error, {:unfilled_hole, atom() | %{required(:definition) => atom()}}}
  def check_codegen_ready(%Env{} = env) do
    defs = program_owned_definitions(env)

    # Route through the single Final-Core enforcement point (K3): the validator
    # descends into every node (prim args, rewrite proof/motive, eq/refl args)
    # where the hand-rolled `has_hole?` walker had gaps.
    finding =
      Enum.find_value(defs, fn {name, %{body: body}} ->
        case Validator.validate(body, Validator.release_config()) do
          {:ok, _warnings} ->
            nil

          {:error, rejections} ->
            if Enum.any?(rejections, &(&1.clause == :no_hole)), do: {name, rejections}
        end
      end)

    case finding do
      nil ->
        :ok

      {name, rejections} ->
        rejection = Enum.find(rejections, &(&1.clause == :no_hole))

        hole_id =
          case rejection do
            %{node: {:hole, id}} -> id
            _ -> nil
          end

        source_holes = defs |> Map.fetch!(name) |> Map.get(:source_holes, %{})

        case Map.get(source_holes, hole_id) do
          nil -> {:error, {:unfilled_hole, name}}
          source -> {:error, {:unfilled_hole, Map.merge(%{definition: name, hole_id: hole_id}, source)}}
        end
    end
  end

  # A checked program environment contains the semantic bodies of its imported
  # interfaces so conversion, proof search, and reachability can use them.  They
  # are dependencies, not declarations being released by this program.  Global
  # hole scans must therefore be scoped by the same canonical owner identity as
  # interface publication; emission separately validates the explicit reachable
  # closure it was asked to emit.  Ownerless synthetic environments retain the
  # historical all-definitions behavior used by kernel-level tests.
  defp program_owned_definitions(%Env{module_owner: nil, defs: defs}), do: defs

  defp program_owned_definitions(%Env{module_owner: owner, defs: defs}) do
    Map.filter(defs, fn {name, _definition} -> Cure.Elab.Name.owner(name) == owner end)
  end

  # Flatten a parsed program into a flat list of top-level declarations,
  # unwrapping `{:block, …}` groupings and `mod … end` module containers while
  # leaving ADT/GADT/function declarations intact. Stray sibling nodes the parser
  # can place next to a module container (e.g. a bare `{:variable, …}`) are
  # dropped, mirroring how codegen locates the container and ignores siblings.
  defp declarations({:block, _meta, items}) when is_list(items),
    do: Enum.flat_map(items, &declarations/1)

  defp declarations({:container, meta, body}) when is_list(meta) do
    if module_like_container?(meta) do
      body |> List.wrap() |> Enum.flat_map(&declarations/1)
    else
      [{:container, meta, body}]
    end
  end

  defp declarations({:function_def, meta, body}) when is_list(meta),
    do: [{:function_def, meta, body}]

  # A computed macro rule owns a typed record for its elab input. Keep the
  # record in the ordinary declaration stream so the existing header pass,
  # constructor registration, and projection checker remain authoritative.
  # The fields are the rule's holes plus the reserved `context` field, which
  # carries the reflected expansion context (`MacroSyntax.record_fields/1`).
  defp declarations({:macro_def, meta, rules}) when is_list(meta) and is_list(rules) do
    MacroFamily.lowered_rules(meta, rules)
    |> Enum.filter(&(&1[:kind] in [:computed, :computed_literal]))
    |> Enum.uniq_by(&Map.get(&1, :syntax_type))
    |> Enum.flat_map(fn rule ->
      MacroFamily.generated_record_declarations(meta, rule)
      |> Enum.map(&append_context_field(&1, rule))
    end)
  end

  defp declarations({tag, _meta, _body} = node) when tag in [:container, :indexed_type], do: [node]

  # Compile-time typeclass declarations (Task 21). Both are top-level
  # declarations the elaborator dispatches (`interface` → descriptor,
  # `implementation` → dictionary + coherence registration).
  defp declarations({tag, meta, _body} = node) when tag in [:interface, :implementation] and is_list(meta),
    do: [node]

  # A top-level type alias `type Name = RHS` (named, non-refinement). Inline
  # refinement/annotation `:type_annotation` nodes are not declarations.
  defp declarations({:type_annotation, meta, _} = node) when is_list(meta) do
    if Keyword.has_key?(meta, :name) and not Keyword.get(meta, :refinement, false),
      do: [node],
      else: []
  end

  defp declarations(_other), do: []

  @doc """
  Is `node` a module-level DECLARATION rather than an expression?

  This is classification, and it is a different question from `declarations/1`,
  which flattens a program into the items a pass must walk. That one answers
  "what does this contribute", which is legitimately `[]` for a `macro_def`
  carrying no computed rules — even though the node is unmistakably a
  declaration, and even though checking it as an expression is nonsense.

  Callers that must route a node to the declaration path or the expression path
  need this question. `Cure.Compiler.MacroFuzz` asks it of a macro rule's
  expansion: a `becomes` template is a single expression form, so a rule that
  generates a definition produces one bare declaration node, not a block of them.
  """
  @spec declaration?(term()) :: boolean()
  def declaration?({:function_def, meta, _body}) when is_list(meta), do: true
  def declaration?({:macro_def, meta, rules}) when is_list(meta) and is_list(rules), do: true
  def declaration?({:indexed_type, _meta, _body}), do: true

  def declaration?({tag, meta, _body}) when tag in [:interface, :implementation] and is_list(meta), do: true

  def declaration?({:container, meta, _body}) when is_list(meta), do: true

  def declaration?({:type_annotation, meta, _rhs}) when is_list(meta),
    do: Keyword.has_key?(meta, :name) and not Keyword.get(meta, :refinement, false)

  def declaration?({:block, _meta, items}) when is_list(items), do: Enum.any?(items, &declaration?/1)
  def declaration?(_other), do: false

  @doc """
  Build the canonical type-family skeleton for one source module.

  Skeletons contain only predeclared family headers. They are sufficient to
  break interface SCCs whose signatures mention a peer nominal type, but they
  expose no unchecked function body or constructor payload to consumers.
  """
  @spec module_type_skeleton(String.t(), String.t()) :: {:ok, Env.t()} | {:error, term()}
  def module_type_skeleton(module_name, path) when is_binary(module_name) and is_binary(path) do
    with {:ok, source} <- File.read(path),
         {:ok, tokens} <- Lexer.tokenize(source, file: path, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, file: path, emit_events: false),
         :ok <- validate_module_identity(ast, module_name, Path.expand(path)),
         :ok <- check_declarations(ast) do
      env = Env.with_owner(seed_with_telescope_support(ast), module_name)

      Enum.reduce_while(declarations(ast), {:ok, env}, fn declaration, {:ok, acc} ->
        case Declarations.declare_header(declaration, acc) do
          {:ok, next} -> {:cont, {:ok, next}}
          {:error, _} = error -> {:halt, error}
        end
      end)
    end
  end

  @doc false
  @spec module_signature_skeleton(String.t(), String.t(), [{String.t(), Env.t()}]) ::
          {:ok, Env.t()} | {:error, term()}
  def module_signature_skeleton(module_name, path, type_skeletons) do
    with {:ok, source} <- File.read(path),
         {:ok, tokens} <- Lexer.tokenize(source, file: path, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, file: path, emit_events: false),
         {:ok, own} <- skeleton_env(module_name, type_skeletons),
         {:ok, imported, _} <- shadow_resolved_imports(ast, type_skeletons),
         {:ok, base} <- merge_env(imported, own),
         base = Env.with_owner(base, module_name),
         base = install_module_visibility(base, ast),
         base = %{
           base
           | certified: base.certified || MapSet.new(),
             totality_certified: base.totality_certified || MapSet.new()
         },
         {:ok, with_types} <-
           Enum.reduce_while(declarations(ast), {:ok, base}, fn
             declaration, {:ok, acc}
             when elem(declaration, 0) in [:container, :indexed_type, :type_annotation] ->
               case Declarations.elaborate(declaration, acc) do
                 {:ok, next} -> {:cont, {:ok, next}}
                 {:error, _} = error -> {:halt, error}
               end

             _declaration, state ->
               {:cont, state}
           end),
         with_types = TotalityClosure.certify_deferred(with_types),
         {:ok, with_interfaces} <-
           Enum.reduce_while(declarations(ast), {:ok, with_types}, fn
             {:interface, _, _} = declaration, {:ok, acc} ->
               case Declarations.elaborate(declaration, acc) do
                 {:ok, next} -> {:cont, {:ok, next}}
                 {:error, _} = error -> {:halt, error}
               end

             _declaration, state ->
               {:cont, state}
           end),
         {:ok, complete} <-
           Enum.reduce_while(declarations(ast), {:ok, with_interfaces}, fn
             {:function_def, _, _} = declaration, {:ok, acc} ->
               case Declarations.register_signature(declaration, acc) do
                 {:ok, next} -> {:cont, {:ok, next}}
                 {:error, _} = error -> {:halt, error}
               end

             _declaration, state ->
               {:cont, state}
           end) do
      signature = owned_signature_skeleton(complete, module_name)
      # Conformance headers belong to the next SCC phase. A signature skeleton
      # can otherwise retain a same-owner instance that arrived transitively
      # through a previously loaded interface, and the conformance phase then
      # reports the authored declaration as overlapping with itself.
      {:ok, %{signature | coherence: nil}}
    end
  end

  @doc false
  @spec module_conformance_skeleton(String.t(), String.t(), [{String.t(), Env.t()}]) ::
          {:ok, Env.t()} | {:error, term()}
  def module_conformance_skeleton(module_name, path, signature_skeletons) do
    with {:ok, source} <- File.read(path),
         {:ok, tokens} <- Lexer.tokenize(source, file: path, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, file: path, emit_events: false),
         {:ok, own} <- skeleton_env(module_name, signature_skeletons),
         {:ok, imported, _} <- shadow_resolved_imports(ast, signature_skeletons),
         {:ok, base} <- merge_env(imported, own),
         base = Env.with_owner(base, module_name),
         base = install_module_visibility(base, ast),
         # A module's own instances can arrive back through its own imports: the
         # module `use`s a whole-module `@prelude` provider (`Std.Equatable`),
         # whose slice keeps coherence intact, and that provider's published
         # interface carries every instance ambient at publication — including
         # the ones THIS module owns. Re-registering the authored declaration
         # into that environment reports the module as overlapping with ITSELF,
         # which is how every warm stdlib build failed on `Std.Char`'s
         # `Equatable for Char`.
         #
         # Drop only the entries whose method globals are owner-qualified with
         # this module (`instance_owned_by?/2`); a FOREIGN instance for the same
         # head is left in place, so the authored declaration still collides with
         # it and global coherence is preserved. This is the conformance-phase
         # counterpart of `%{signature | coherence: nil}` in the signature phase
         # and `strip_shadowed_prelude_instances/2` in the body phase.
         base = Env.put_coherence(base, without_owned_coherence(Env.coherence(base), module_name)),
         {:ok, complete} <-
           Enum.reduce_while(declarations(ast), {:ok, base}, fn
             {:implementation, _, _} = declaration, {:ok, acc} ->
               case Cure.Elab.Implementation.register(declaration, acc) do
                 {:ok, next, _method_declarations, _obligations} ->
                   {:cont, {:ok, next}}

                 {:error, _} = error ->
                   {:halt, error}
               end

             _declaration, state ->
               {:cont, state}
           end) do
      {:ok, owned_signature_skeleton(complete, module_name)}
    end
  end

  defp owned_signature_skeleton(%Env{} = env, owner) do
    owned? = fn key -> Cure.Elab.Name.owner(key) == owner end
    defs = Map.filter(env.defs, fn {key, _} -> owned?.(key) end)
    families = Map.filter(env.families, fn {key, _} -> owned?.(key) end)
    ctors = Map.filter(env.ctors, fn {key, _} -> owned?.(key) end)

    ctor_to_family =
      Map.filter(env.ctor_to_family, fn {ctor, family} -> owned?.(ctor) and owned?.(family) end)

    certified =
      case env.certified do
        %MapSet{} = names -> MapSet.filter(names, owned?)
        nil -> nil
      end

    totality_certified =
      case env.totality_certified do
        %MapSet{} = names -> MapSet.filter(names, owned?)
        nil -> nil
      end

    %{
      env
      | defs: defs,
        families: families,
        ctors: ctors,
        ctor_to_family: ctor_to_family,
        certified: certified,
        totality_certified: totality_certified,
        coherence: owned_coherence(env.coherence, owner),
        import_modules: MapSet.new(),
        bare_modules: MapSet.new(),
        bare_bindings: MapSet.new()
    }
  end

  defp append_context_field({:container, meta, fields}, rule) do
    if Keyword.get(meta, :name) == Map.get(rule, :syntax_type) and
         not Enum.any?(fields, &match?({:param, _, "context"}, &1)) do
      context = {:param, [type: {:variable, [scope: :local], "Syntax"}], MacroSyntax.context_field()}
      {:container, meta, fields ++ [context]}
    else
      {:container, meta, fields}
    end
  end

  defp imports(ast), do: ast |> import_entries() |> Enum.flat_map(fn {sources, _meta} -> sources end)

  defp qualified_module_names(ast) do
    ast
    |> FixityScan.collect_qualified_targets()
    |> Enum.map(& &1.target)
    |> Enum.reject(&(&1 == find_module_name(ast)))
    |> Enum.uniq()
  end

  # Same walk as `imports/1`, but each import's sources are paired with the import
  # node's meta so a caller can tell an author-written `use` from a compiler-injected
  # ambient `@prelude` one (`Cure.Compiler.inject_prelude_uses/2` tags those
  # `prelude_injected: true`). `imports/1` discards the meta and is unchanged.
  defp import_entries({:block, _meta, items}) when is_list(items),
    do: Enum.flat_map(items, &import_entries/1)

  defp import_entries({:container, meta, body}) when is_list(meta) do
    if module_like_container?(meta) do
      body |> List.wrap() |> Enum.flat_map(&import_entries/1)
    else
      []
    end
  end

  # `use Std.{List, Core}` is grouping sugar: the brace `:items` name a set of
  # sibling modules under the `:source` namespace, each expanded to its own full
  # `source.item` import. A plain `use Std.List` (no `:items`) yields just the source.
  # (`:exposing` — the selective-name form `use M exposing (a, b)` — is a filter on
  # WHICH of the module's names come in unqualified, not a different module list, so
  # it does not affect the source expansion here.)
  defp import_entries({:import, meta, _}) when is_list(meta) do
    source = Keyword.fetch!(meta, :source)

    sources =
      case Keyword.get(meta, :items, []) do
        [] -> [source]
        items -> Enum.map(items, &(source <> "." <> to_string(&1)))
      end

    [{sources, meta}]
  end

  defp import_entries({_tag, _meta, children}) when is_list(children),
    do: Enum.flat_map(children, &import_entries/1)

  defp import_entries(list) when is_list(list), do: Enum.flat_map(list, &import_entries/1)
  defp import_entries(_other), do: []

  # Distinct {module_id, path} for every DIRECT import source, deduped by
  # module_id. Used for the merged-slice list (§3.2 re-keying/merging operates
  # only at this granularity — nested imports are pulled in automatically by
  # each direct module's own recursive `module_slice_env`).
  defp distinct_import_modules(sources) do
    sources
    |> Enum.map(&import_source_path/1)
    |> Enum.flat_map(fn
      {:ok, module_name, path} -> [{to_string(module_name), path}]
      {:ok_user, module_name, path} -> [{to_string(module_name), path}]
      _ -> []
    end)
    |> Enum.uniq_by(fn {mod_id, _path} -> mod_id end)
  end

  # Every module reachable via the import graph (direct AND transitive),
  # deduped by module_id, cycle-safe (BFS with a `seen` set). Collision
  # DETECTION (family_owners, below) must scan this closure, not just the
  # direct list: a family declared in a module reached only transitively
  # (e.g. Std.Nat, pulled in solely because `priv/std/vector.cure` itself
  # does `use Std.Nat`) still needs to be attributed to its owning module, or
  # a local declaration of the same name is never classified as a collision
  # and the disowning never happens for that family.
  defp transitive_import_modules(sources) do
    with_loader_session(fn ->
      case load_dependency_env(sources) do
        {:ok, _env} ->
          roots = dependency_module_names(sources)
          canonical_module_closure(roots, MapSet.new(), [])

        {:error, _reason} ->
          []
      end
    end)
  end

  defp canonical_module_closure([], _seen, acc), do: Enum.reverse(acc)

  defp canonical_module_closure([module_name | rest], seen, acc) do
    if MapSet.member?(seen, module_name) do
      canonical_module_closure(rest, seen, acc)
    else
      case Process.get(@loader_state_key).modules[module_name] do
        {:loaded, interface} ->
          canonical_module_closure(
            interface.dependency_names ++ rest,
            MapSet.put(seen, module_name),
            [{module_name, interface.path} | acc]
          )

        _ ->
          canonical_module_closure(rest, MapSet.put(seen, module_name), acc)
      end
    end
  end

  # Function names DECLARED in a module's own source (transitive imports
  # excluded), used to build the legacy codegen import-origin compatibility map.
  defp owned_def_names(path) do
    with {:ok, source} <- File.read(path),
         {:ok, tokens} <- Lexer.tokenize(source, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, emit_events: false) do
      MapSet.new(local_def_names(ast))
    else
      _ -> MapSet.new()
    end
  end

  # Build ONE module's flat env slice (own decls + its own imports), as today.
  @doc """
  Merge a macro's HOME-module env into a caller env for definition-site (ambient)
  expander resolution. `path` is the home file of a stdlib computed/family macro
  (stamped on the rule as `:source_path` at harvest, carried in the `:computed_use`
  meta as `:home_source`). The home slice is elaborated once and cached; the caller
  wins on any name conflict (it is the right operand of `merge_env`). Any slice
  failure degrades gracefully to the caller env, preserving prior behaviour.

  Used only to elaborate the expander itself — the AST the expander produces is
  re-elaborated in the caller's own env, so this does not widen caller scope.
  """
  @spec env_with_macro_home(Env.t(), binary()) :: Env.t()
  def env_with_macro_home(%Env{} = caller, path) when is_binary(path) do
    case cached_macro_home_env(path) do
      {:ok, %Env{} = home} ->
        case merge_env(home, caller) do
          {:ok, merged} -> merged
          {:error, _} -> caller
        end

      {:error, _} ->
        caller
    end
  end

  def env_with_macro_home(caller, _path), do: caller

  # Macro homes are ordinary module interfaces. Definition-site lookup therefore
  # observes exactly the same dependency graph and cache as a `use` import.
  defp cached_macro_home_env(path) do
    key = {__MODULE__, :macro_home_env, path}

    case :persistent_term.get(key, :missing) do
      :missing ->
        case read_macro_home_cache(path) do
          {:ok, %Env{}} = cached ->
            :persistent_term.put(key, cached)
            cached

          nil ->
            result = module_slice_env(path)

            if match?({:ok, %Env{}}, result) do
              :persistent_term.put(key, result)
              write_macro_home_cache(path, result)
            end

            result
        end

      cached ->
        cached
    end
  end

  # Path-only callers first read the declared identity, then enter the same
  # canonical loader as name-based imports. Paths are validated attributes and
  # never cache keys.
  defp module_slice_env(path) do
    with_loader_session(fn ->
      with {:ok, source} <- File.read(path),
           {:ok, tokens} <- Lexer.tokenize(source, emit_events: false),
           {:ok, ast} <- Parser.parse(tokens, emit_events: false),
           module_name when is_binary(module_name) <- find_module_name(ast) do
        load_module_interface(module_name, path)
      else
        nil -> {:error, {:module_identity_missing, path}}
        {:error, _} = error -> error
      end
    end)
  end

  defp load_module_interface(module_name, path) do
    path = Path.expand(path)
    state = Process.get(@loader_state_key)

    case Map.get(state.modules, module_name) do
      {:loaded, %{path: ^path, export_env: env}} ->
        {:ok, env}

      {:loaded, %{path: other_path}} ->
        {:error, {:duplicate_module_identity, module_name, other_path, path}}

      {:loading, _stack, ^path} ->
        # A back-edge may be an interface-only cycle. Publish the declaration
        # and signature skeleton for this edge; the outer load still checks
        # every body once the complete peer interfaces are available.
        loading_signature_skeleton(state, module_name, path)

      {:loading, _stack, other_path} ->
        {:error, {:duplicate_module_identity, module_name, other_path, path}}

      {:failed, ^path, reason} ->
        {:error, reason}

      {:failed, other_path, _reason} ->
        {:error, {:duplicate_module_identity, module_name, other_path, path}}

      nil ->
        case Map.get(state.paths, path) do
          nil -> load_new_module_interface(module_name, path)
          ^module_name -> load_new_module_interface(module_name, path)
          other_name -> {:error, {:module_path_identity_mismatch, path, other_name, module_name}}
        end
    end
  end

  defp load_new_module_interface(module_name, path) do
    state = Process.get(@loader_state_key)
    stack = loader_active_stack(state) ++ [module_name]

    put_loader_state(%{
      state
      | modules: Map.put(state.modules, module_name, {:loading, stack, path}),
        paths: Map.put(state.paths, path, module_name)
    })

    result = cached_module_interface(module_name, path)
    state = Process.get(@loader_state_key)

    case result do
      {:ok, interface} ->
        case complete_interface_environment(interface) do
          {:ok, export_env} ->
            state = Process.get(@loader_state_key)
            interface = %{interface | export_env: export_env}
            put_loader_state(%{state | modules: Map.put(state.modules, module_name, {:loaded, interface})})
            {:ok, export_env}

          {:error, reason} ->
            state = Process.get(@loader_state_key)
            put_loader_state(%{state | modules: Map.put(state.modules, module_name, {:failed, path, reason})})
            {:error, reason}
        end

      {:error, reason} ->
        put_loader_state(%{state | modules: Map.put(state.modules, module_name, {:failed, path, reason})})
        {:error, reason}
    end
  end

  # A cached interface records canonical dependency identities, but its
  # transitional `export_env` is only the view available when that module was
  # checked.  In an SCC, a back-edge is necessarily a skeleton at that moment.
  # Reconstruct the semantic dependency closure in each loader generation before
  # publishing the cached interface, otherwise module-owned registrations such
  # as `:char` can disappear permanently behind the cached skeleton.
  #
  # Dependency semantics travel; dependency visibility does not.  Clearing the
  # four name-exposure fields keeps a transitive dependency from becoming a
  # lexical `use` import of the consumer while retaining its canonical families,
  # definitions, builtin registrations, coherence, and totality evidence.
  defp complete_interface_environment(%ModuleInterface{} = interface) do
    with {:ok, owned} <- PipelineInterface.to_env(interface),
         {:ok, dependencies} <- interface_dependency_environment(interface),
         {:ok, merged} <- merge_env(dependencies, owned) do
      owned_bindings = MapSet.new(all_global_keys(owned))
      reexported_bindings = public_reexport_bindings(interface.source_path, merged)

      qualified_aliases =
        merge_qualified_reexport_aliases(
          merged,
          %{interface.module_name => public_reexport_modules(interface.source_path)}
        )

      owner_visibility = MapSet.new([interface.module_name])

      {:ok,
       %Env{
         merged
         | module_owner: interface.module_name,
           import_modules: MapSet.new(),
           bare_modules: owner_visibility,
           bare_bindings: MapSet.union(owned_bindings, reexported_bindings),
           qualified_modules: owner_visibility,
           qualified_aliases: qualified_aliases,
           current_def: nil
       }}
    end
  end

  # A verified canonical generation is already the complete interface table for
  # its source graph.  Re-entering the source loader for each dependency creates
  # a second, order-sensitive compiler and turns legal SCC back-edges into
  # provisional skeletons.  Build the transitive closure directly from the
  # published table instead.  Cold/user compilation still uses the source
  # loader until it publishes a canonical generation.
  defp interface_dependency_environment(%ModuleInterface{} = interface) do
    case canonical_published_dependency_environment(interface) do
      {:ok, %Env{} = dependencies} -> {:ok, dependencies}
      :not_published -> load_interface_dependency_environments(interface.dependency_names)
      {:error, _} = error -> error
    end
  end

  defp canonical_published_dependency_environment(%ModuleInterface{} = interface) do
    with {:ok, set} <- canonical_published_set(),
         {:ok, interfaces} <- canonical_published_interface_table(set),
         {:ok, published} <- Map.fetch(interfaces, interface.module_name),
         true <- published.interface_hash == interface.interface_hash do
      cached_published_dependency_environment(set, interfaces, interface)
    else
      false -> :not_published
      :error -> :not_published
      {:error, {:no_verified_artifact_set, _}} -> :not_published
      {:error, reason} -> {:error, reason}
    end
  end

  defp cached_published_dependency_environment(set, interfaces, interface) do
    digest = Map.get(set, :artifact_digest) || Map.get(set, :input_snapshot)
    key = {__MODULE__, :canonical_dependency_environment, set.artifact_root, digest, interface.interface_hash}

    case :persistent_term.get(key, :missing) do
      {:ok, %Env{}} = cached ->
        cached

      :missing ->
        with {:ok, names} <- interface_dependency_closure(interfaces, interface.dependency_names),
             dependency_interfaces = Map.take(interfaces, names),
             {:ok, dependencies} <- PipelineInterface.environment(dependency_interfaces) do
          result = {:ok, semantic_dependency_environment(dependencies)}
          :persistent_term.put(key, result)
          result
        end
    end
  end

  defp canonical_published_interface_table(set) do
    digest = Map.get(set, :artifact_digest) || Map.get(set, :input_snapshot)
    key = {__MODULE__, :canonical_published_interface_table, set.artifact_root, digest}

    case :persistent_term.get(key, :missing) do
      {:ok, interfaces} ->
        {:ok, interfaces}

      :missing ->
        case PipelineInterface.load_roots([set.artifact_root]) do
          {:ok, interfaces} = result ->
            :persistent_term.put(key, result)
            {:ok, interfaces}

          {:error, _} = error ->
            error
        end
    end
  end

  defp interface_dependency_closure(interfaces, roots) do
    interface_dependency_closure(interfaces, Enum.uniq(roots), MapSet.new())
  end

  defp interface_dependency_closure(_interfaces, [], seen),
    do: {:ok, MapSet.to_list(seen)}

  defp interface_dependency_closure(interfaces, [name | rest], seen) do
    cond do
      ModuleIndex.compiler_owned?(name) or MapSet.member?(seen, name) ->
        interface_dependency_closure(interfaces, rest, seen)

      true ->
        case Map.fetch(interfaces, name) do
          {:ok, dependency} ->
            interface_dependency_closure(
              interfaces,
              rest ++ dependency.dependency_names,
              MapSet.put(seen, name)
            )

          :error ->
            {:error, {:module_not_found, name}}
        end
    end
  end

  defp load_interface_dependency_environments(names) do
    Enum.reduce_while(names, {:ok, Env.empty()}, fn name, {:ok, acc} ->
      if ModuleIndex.compiler_owned?(name) do
        {:cont, {:ok, acc}}
      else
        case resolved_module_path(name) do
          nil ->
            {:halt, {:error, {:module_not_found, name}}}

          path ->
            with {:ok, dependency} <- load_module_interface(name, path),
                 dependency = semantic_dependency_environment(dependency),
                 {:ok, merged} <- merge_env(acc, dependency) do
              {:cont, {:ok, merged}}
            else
              {:error, _} = error -> {:halt, error}
            end
        end
      end
    end)
  end

  defp semantic_dependency_environment(%Env{} = env) do
    %Env{
      env
      | import_modules: MapSet.new(),
        bare_modules: MapSet.new(),
        bare_bindings: MapSet.new(),
        qualified_modules: MapSet.new(),
        qualified_aliases: %{},
        module_owner: nil,
        current_def: nil
    }
  end

  defp loading_signature_skeleton(state, module_name, path) do
    loading =
      Enum.flat_map(state.modules, fn
        {name, {:loading, _stack, loading_path}} -> [{name, loading_path}]
        _ -> []
      end)

    with {:ok, types} <-
           Enum.reduce_while(loading, {:ok, []}, fn {name, loading_path}, {:ok, acc} ->
             case module_type_skeleton(name, loading_path) do
               {:ok, env} -> {:cont, {:ok, [{name, env} | acc]}}
               {:error, _} = error -> {:halt, error}
             end
           end),
         {:ok, signatures} <-
           Enum.reduce_while(loading, {:ok, []}, fn {name, loading_path}, {:ok, acc} ->
             case module_signature_skeleton(name, loading_path, types) do
               {:ok, env} -> {:cont, {:ok, [{name, env} | acc]}}
               {:error, _} = error -> {:halt, error}
             end
           end) do
      module_conformance_skeleton(module_name, path, signatures)
    end
  end

  # Shipped stdlib sources are immutable for the lifetime of a compiler run: no
  # test writes them and nothing regenerates them mid-run, so a stdlib path is
  # guaranteed to elaborate identically every time. Their interfaces are
  # therefore memoized across loader generations, which is what collapses the
  # redundant re-elaboration every `Program.elaborate` otherwise pays — the
  # prelude modules plus explicit imports, re-sliced from source on each of the
  # hundreds of elaboration calls a test suite makes.
  #
  # Scope matters, and is the whole point: ONLY shipped stdlib paths are cached.
  # User and temp-file modules stay per-generation, so a fresh generation still
  # observes changed source and a half-written file is never memoized. Caching
  # by path regardless of provenance would reintroduce exactly that hole.
  #
  # This runs only in the HOST compiler, never on AtomVM (no `persistent_term`
  # there). Failures are NOT cached — a transient read/parse error must not
  # poison later loads once the tree is consistent.
  #
  # Bookkeeping (cycle stack, duplicate identity, path/identity agreement) lives
  # in the caller and still runs per generation on every load, hit or miss.
  @doc """
  Return the canonical module interface for `module_name` at `path`.

  The interface map carries the elaborated `:export_env` a consumer merges in
  when it imports this module, plus its `:source_hash`. This is the exact
  artifact incremental compilation hashes to decide whether a change to this
  module can affect its dependents. Semantics match the internal loader cache:
  `:persistent_term`-cached for stdlib paths, recomputed otherwise.
  """
  @spec module_interface(String.t(), String.t()) :: {:ok, ModuleInterface.t()} | {:error, term()}
  def module_interface(module_name, path) when is_binary(module_name) and is_binary(path) do
    path = Path.expand(path)

    # Runs inside a loader session so a cold, standalone call (no enclosing
    # `elaborate/1`) still has the `@loader_state_key` generation its dependency
    # loading reads. `with_loader_session/1` reuses an existing generation when
    # one is already open, so this is a no-op cost under normal elaboration.
    with_loader_session(fn -> cached_module_interface(module_name, path) end)
  end

  @doc """
  Evict `path`'s memoized interface, if one is cached, so the next
  `module_interface/2` call (and any subsequent `use`-import resolution that
  goes through the same loader) recomputes it from current source content.

  `cached_module_interface/2` assumes a shipped stdlib source is immutable for
  the lifetime of a compiler run — true for ordinary one-shot compilation, but
  violated BY DESIGN whenever the canonical artifact sweep recompiles that
  source within one long-lived process (for example, two stdlib sweeps in one
  node). Without this, a module's SECOND same-process recompile can silently
  report the FIRST run's now-stale interface, and a dependent whose actual
  interface changed is never recompiled. The incremental driver calls this
  immediately after recompiling a module, before computing its fresh
  interface hash.
  """
  @spec invalidate_module_interface(String.t()) :: :ok
  def invalidate_module_interface(path) when is_binary(path) do
    path = Path.expand(path)
    :persistent_term.erase({__MODULE__, :module_interface, path})
    :persistent_term.erase({__MODULE__, :macro_home_env, path})
    :persistent_term.erase(macro_home_cache_fingerprint_key())
    File.rm(module_interface_cache_path(path))
    File.rm(macro_home_cache_path(path))
    :ok
  end

  @doc """
  Publish the canonical interface carried by a successfully emitted checked
  module.

  Publication happens only after BEAM writing succeeds. Shipped stdlib
  interfaces retain their source-hash-keyed process and disk caches; ordinary
  user modules remain loader-generation scoped.
  """
  @spec publish_checked_interface(CheckedModule.t()) :: :ok
  def publish_checked_interface(%CheckedModule{
        interface: %ModuleInterface{} = interface,
        source_path: path,
        source_hash: source_hash
      })
      when is_binary(path) and is_binary(source_hash) do
    # Only a module whose content IS the file at `path` may speak for that path.
    # Carrying a real path is not evidence of being the module there: a file is
    # also the documentation home of every fence in its `##` comments, and
    # `mix cure.check.docs` compiles those fences with `file:` set to the
    # document they were written in, so a diagnostic anchors to the right line
    # of the right file. Such a snippet is a different module at a real
    # module's path.
    #
    # Published as canonical it erased that path's macro-home environment,
    # replaced its interface memo with an entry keyed by the SNIPPET's hash --
    # which no lookup for the real module can ever match -- and wrote the
    # snippet's interface into the real module's on-disk artifact. Nothing
    # served wrong data (every read re-checks the hash), but every stdlib
    # docstring destroyed the cache this function exists to maintain, and each
    # one also erased the global interface fingerprint, forcing a rescan of
    # every compiler BEAM and every stdlib source.
    if source_hash == current_source_hash(path) do
      :persistent_term.erase({__MODULE__, :macro_home_env, path})
      File.rm(macro_home_cache_path(path))

      if stdlib_source_path?(path) do
        cache_key = {__MODULE__, :module_interface, path}

        case :persistent_term.get(cache_key, :missing) do
          {:cached, previous_hash, _result} when previous_hash != source_hash ->
            :persistent_term.erase(macro_home_cache_fingerprint_key())

          _unchanged_or_missing ->
            :ok
        end

        result =
          case read_module_interface_cache(path, interface.module_name, source_hash) do
            {:ok, %ModuleInterface{interface_hash: hash}} = canonical
            when hash == interface.interface_hash ->
              canonical

            _missing_or_semantically_changed ->
              fresh = {:ok, interface}
              write_module_interface_cache(path, interface.module_name, source_hash, fresh)
              fresh
          end

        :persistent_term.put(cache_key, {:cached, source_hash, result})
      end
    end

    :ok
  end

  def publish_checked_interface(%CheckedModule{}), do: :ok

  # Canonical module interfaces are immutable functions of the compiler and the
  # source closure. Persisting successful interfaces avoids rebuilding the whole
  # stdlib graph in every short-lived Mix VM. The fingerprint covers compiler
  # BEAMs and every discovered stdlib source, while `source_hash` and the
  # validated identity guard the individual entry.
  defp read_module_interface_cache(path, module_name, source_hash) do
    with true <- not is_nil(source_hash),
         {:ok, binary} <- File.read(module_interface_cache_path(path)),
         {:cure_module_interface, @module_interface_cache_version, fingerprint, expanded_path, ^module_name,
          ^source_hash, {:ok, %ModuleInterface{} = interface} = result} <- :erlang.binary_to_term(binary),
         true <- fingerprint == macro_home_cache_fingerprint(),
         true <- expanded_path == Path.expand(path),
         :ok <- ModuleInterface.validate(interface) do
      result
    else
      _ -> nil
    end
  rescue
    _ -> nil
  end

  defp write_module_interface_cache(
         path,
         module_name,
         source_hash,
         {:ok, %ModuleInterface{}} = result
       )
       when not is_nil(source_hash) do
    destination = module_interface_cache_path(path)
    directory = Path.dirname(destination)
    temporary = destination <> ".#{System.unique_integer([:positive])}.tmp"

    payload =
      {:cure_module_interface, @module_interface_cache_version, macro_home_cache_fingerprint(), Path.expand(path),
       module_name, source_hash, result}
      |> :erlang.term_to_binary(compressed: 6)

    with :ok <- File.mkdir_p(directory),
         :ok <- File.chmod(directory, 0o700),
         :ok <- File.write(temporary, payload),
         :ok <- File.chmod(temporary, 0o600),
         :ok <- File.rename(temporary, destination) do
      :ok
    else
      _ ->
        File.rm(temporary)
        :ok
    end
  rescue
    _ -> :ok
  end

  defp write_module_interface_cache(_path, _module_name, _source_hash, _result), do: :ok

  defp module_interface_cache_path(path) do
    basename = :crypto.hash(:sha256, Path.expand(path)) |> Base.url_encode64(padding: false)
    Path.join([System.tmp_dir!(), "cure-module-interface-cache", basename <> ".etf"])
  end

  # A definition-site macro environment is expensive to reconstruct from a
  # cold VM (Std.Actor's closure is the largest example), while the ordinary
  # persistent_term cache only survives for one `mix` invocation. Keep a small
  # cross-process cache in the OS temporary directory. Its fingerprint covers
  # every compiler BEAM and stdlib source, so changing either invalidates every
  # entry conservatively. Only successful canonical module-interface results
  # are stored; corrupt or stale files are ignored and replaced atomically.
  defp read_macro_home_cache(path) do
    with {:ok, binary} <- File.read(macro_home_cache_path(path)),
         {:cure_macro_home, @macro_home_cache_version, fingerprint, expanded_path, {:ok, %Env{}} = result} <-
           :erlang.binary_to_term(binary),
         true <- fingerprint == macro_home_cache_fingerprint(),
         true <- expanded_path == Path.expand(path) do
      result
    else
      _ -> nil
    end
  rescue
    _ -> nil
  end

  defp write_macro_home_cache(path, {:ok, %Env{}} = result) do
    destination = macro_home_cache_path(path)
    directory = Path.dirname(destination)
    temporary = destination <> ".#{System.unique_integer([:positive])}.tmp"

    payload =
      {:cure_macro_home, @macro_home_cache_version, macro_home_cache_fingerprint(), Path.expand(path), result}
      |> :erlang.term_to_binary(compressed: 6)

    with :ok <- File.mkdir_p(directory),
         :ok <- File.chmod(directory, 0o700),
         :ok <- File.write(temporary, payload),
         :ok <- File.chmod(temporary, 0o600),
         :ok <- File.rename(temporary, destination) do
      :ok
    else
      _ ->
        File.rm(temporary)
        :ok
    end
  rescue
    _ -> :ok
  end

  defp macro_home_cache_path(path) do
    basename = :crypto.hash(:sha256, Path.expand(path)) |> Base.url_encode64(padding: false)
    Path.join([System.tmp_dir!(), "cure-macro-home-cache", basename <> ".etf"])
  end

  defp macro_home_cache_fingerprint do
    # Include the currently loaded Program BEAM identity in the process-cache
    # key. Mix can reload this module in a long-lived VM; a single static key
    # would otherwise keep the fingerprint computed by the previous compiler
    # implementation and incorrectly bless artifacts written before the reload.
    key = macro_home_cache_fingerprint_key()

    case :persistent_term.get(key, :missing) do
      :missing ->
        beam_dir = __MODULE__ |> :code.which() |> List.to_string() |> Path.dirname()

        paths =
          (Path.wildcard(Path.join(beam_dir, "*.beam")) ++
             Enum.flat_map(Paths.source_dirs(), &Path.wildcard(Path.join(&1, "*.cure"))))
          |> Enum.map(&Path.expand/1)
          |> Enum.uniq()
          |> Enum.sort()

        fingerprint =
          Enum.reduce(paths, :crypto.hash_init(:sha256), fn file, hash ->
            hash
            |> :crypto.hash_update(file)
            |> :crypto.hash_update(File.read!(file))
          end)
          |> :crypto.hash_final()

        :persistent_term.put(key, fingerprint)
        fingerprint

      fingerprint ->
        fingerprint
    end
  end

  defp macro_home_cache_fingerprint_key do
    {__MODULE__, :macro_home_cache_fingerprint, __MODULE__.module_info(:md5)}
  end

  defp cached_module_interface(module_name, path) do
    if stdlib_source_path?(path) do
      key = {__MODULE__, :module_interface, path}
      source_hash = current_source_hash(path)

      case canonical_published_interface(module_name, source_hash) do
        {:ok, %ModuleInterface{}} = canonical ->
          :persistent_term.put(key, {:cached, source_hash, canonical})
          canonical

        :error ->
          case :persistent_term.get(key, :missing) do
            {:cached, ^source_hash, {:ok, %ModuleInterface{}} = cached}
            when not is_nil(source_hash) ->
              cached

            _missing_or_stale ->
              case read_module_interface_cache(path, module_name, source_hash) do
                {:ok, %ModuleInterface{}} = cached ->
                  :persistent_term.put(key, {:cached, source_hash, cached})
                  cached

                nil ->
                  compile_and_cache_module_interface(key, source_hash, module_name, path)
              end
          end
      end
    else
      compile_module_interface(module_name, path)
    end
  end

  # Once the canonical stdlib sweep has published a generation produced by this
  # exact host compiler, that checked interface is the authority for every
  # consumer in the VM.  Re-elaborating the same source through the transitional
  # source loader created a second compiler with different SCC and inference
  # behavior.  A cold build (no generation, changed toolchain, or changed source)
  # falls through to source elaboration and publishes a fresh generation later.
  defp canonical_published_interface(module_name, source_hash) when is_binary(source_hash) do
    with {:ok, set} <- canonical_published_set(),
         {:ok, interfaces} <- canonical_published_interface_table(set),
         {:ok, interface} <- Map.fetch(interfaces, module_name),
         true <- interface.source_hash == source_hash do
      {:ok, interface}
    else
      _ -> :error
    end
  end

  defp canonical_published_interface(_module_name, _source_hash), do: :error

  defp canonical_published_set do
    # `beam_dirs/0` resolves publication pointers to immutable,
    # content-addressed generation directories.  That resolved candidate list
    # is therefore the cache identity: publishing a new generation changes the
    # path and cannot reuse this entry.  Without this cache every imported
    # interface performed a full manifest verification; one tiny Std.Syntax
    # consumer consequently rehashed 5,400 artifacts.
    candidates = Paths.beam_dirs()
    compiler_hash = BuildManifest.toolchain_fingerprint()
    key = {__MODULE__, :canonical_published_set, candidates, compiler_hash}

    case :persistent_term.get(key, :missing) do
      {:ok, set} ->
        {:ok, set}

      :missing ->
        with {:ok, set} <-
               Artifacts.open_verified_set(
                 kind: :stdlib,
                 candidates: candidates,
                 verification: :full
               ),
             true <- get_in(set, [:context, :compiler_hash]) == compiler_hash do
          result = {:ok, set}
          :persistent_term.put(key, result)
          result
        else
          false -> {:error, :canonical_artifact_toolchain_mismatch}
          {:error, _} = error -> error
        end
    end
  end

  defp compile_and_cache_module_interface(key, source_hash, module_name, path) do
    case compile_module_interface(module_name, path) do
      {:ok, %ModuleInterface{} = _interface} = ok ->
        :persistent_term.put(key, {:cached, source_hash, ok})
        write_module_interface_cache(path, module_name, source_hash, ok)
        ok

      {:error, _reason} = error ->
        error
    end
  end

  defp current_source_hash(path) do
    case File.read(path) do
      {:ok, source} -> :crypto.hash(:sha256, source)
      {:error, _} -> nil
    end
  end

  # The `:compiling` event fires only where a module is genuinely elaborated, so
  # an observer counting events never sees a cache hit reported as a compile.
  defp compile_module_interface(module_name, path) do
    emit_loader_event({:compiling, module_name, path})
    compute_module_interface(module_name, path)
  end

  defp stdlib_source_path?(path) do
    expanded = Path.expand(path)

    Paths.all_source_dirs()
    |> Enum.map(&Path.expand/1)
    |> Enum.any?(&(expanded == &1 or String.starts_with?(expanded, &1 <> "/")))
  end

  defp loader_active_stack(state) do
    state.modules
    |> Map.values()
    |> Enum.flat_map(fn
      {:loading, stack, _path} -> [stack]
      _ -> []
    end)
    |> Enum.max_by(&length/1, fn -> [] end)
  end

  defp put_loader_state(state), do: Process.put(@loader_state_key, state)

  defp emit_loader_event(event) do
    case Process.get(:cure_module_loader_observer) do
      observer when is_pid(observer) -> send(observer, {:cure_module_loader, event})
      _ -> :ok
    end
  end

  defp compute_module_interface(requested_name, path) do
    with {:ok, source} <- File.read(path),
         {:ok, tokens} <- Lexer.tokenize(source, file: path, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, file: path, emit_events: false),
         {:ok, %CheckedModule{interface: %ModuleInterface{} = interface}} <-
           check_ast_artifact(ast,
             source: source,
             file: path,
             module_name: requested_name,
             purpose: :interface,
             prelude_mode: :bootstrap_safe,
             require_module_identity: true
           ) do
      {:ok, interface}
    end
  end

  defp validate_artifact_identity(_ast, _module_name, _file, _source, false), do: :ok

  defp validate_artifact_identity(_ast, _module_name, _file, source, true)
       when not is_binary(source),
       do: :ok

  defp validate_artifact_identity(ast, module_name, file, source, true)
       when is_binary(file) and is_binary(source),
       do: validate_module_identity(ast, module_name, file)

  defp validate_artifact_identity(_ast, _module_name, _file, _source, true), do: :ok

  defp source_context_opts(source, file) when is_binary(source) and is_binary(file),
    do: [source: source, file: file]

  defp source_context_opts(_source, _file), do: []

  defp checked_module_interface(_ast, _env, _module_name, _file, source)
       when not is_binary(source),
       do: {:ok, nil}

  defp checked_module_interface(ast, env, module_name, file, source)
       when is_binary(file) and is_binary(source) do
    interface_ast = without_injected_prelude_imports(ast)
    dependencies = module_dependency_sources(ast)
    dependency_names = dependency_module_names(dependencies)

    ambient_preludes =
      Enum.uniq(injected_prelude_sources(ast) ++ prelude_sources_for(interface_ast))

    export_env = canonical_export_env(env, module_name, interface_ast, ambient_preludes)

    {:ok,
     ModuleInterface.new(%{
       module_name: module_name,
       source_path: file,
       source_hash: source_hash(source),
       dependency_interface_hashes: loaded_dependency_interface_hashes(dependency_names),
       dependency_names: dependency_names,
       direct_edges: module_interface_edges(interface_ast),
       canonical_declarations: owned_declarations(export_env, module_name),
       canonical_externs: owned_externs(export_env, module_name),
       extension_payloads: interface_extensions(export_env, module_name),
       source_metadata: %{dependency_source_hashes: dependency_source_hashes(dependency_names)},
       owned_env: env,
       export_env: export_env,
       direct_import_names: direct_import_ids(imports(interface_ast))
     })}
  end

  defp checked_module_interface(_ast, _env, _module_name, _file, _source), do: {:ok, nil}

  defp canonical_export_env(env, module_name, interface_ast, injected_preludes) do
    owned_keys =
      env.defs
      |> Map.keys()
      |> Enum.filter(&(Cure.Elab.Name.owner(&1) == module_name))

    required = env.defs |> reachable_global_closure(owned_keys) |> MapSet.new()
    injected_owners = MapSet.new(injected_preludes)

    defs =
      Map.reject(env.defs, fn {key, _definition} ->
        MapSet.member?(injected_owners, Cure.Elab.Name.owner(key)) and
          not MapSet.member?(required, key)
      end)

    canonical =
      env
      |> Map.put(:defs, defs)
      |> Map.put(:coherence, coherence_with_available_methods(env.coherence, defs))
      |> install_module_visibility(interface_ast)

    ambient = injected_owners

    canonical
    |> Map.put(:bare_modules, MapSet.union(canonical.bare_modules || MapSet.new(), ambient))
    |> Map.put(:qualified_modules, MapSet.union(canonical.qualified_modules || MapSet.new(), ambient))
  end

  defp coherence_with_available_methods(nil, _defs), do: nil

  defp coherence_with_available_methods(%Coherence{} = coherence, defs) do
    available? = fn {_key, ref} ->
      ref
      |> Map.get(:methods, %{})
      |> Map.values()
      |> Enum.all?(&Map.has_key?(defs, &1))
    end

    anon = Map.filter(coherence.anon, available?)
    named = Map.filter(coherence.named, available?)

    %Coherence{
      anon: anon,
      named: named,
      anon_origins: Map.take(coherence.anon_origins, Map.keys(anon)),
      named_origins: Map.take(coherence.named_origins, Map.keys(named))
    }
  end

  defp injected_prelude_sources(ast) do
    ast
    |> import_entries()
    |> Enum.filter(fn {_sources, meta} -> Keyword.get(meta, :prelude_injected, false) end)
    |> Enum.flat_map(&elem(&1, 0))
    |> Enum.uniq()
  end

  defp without_injected_prelude_imports({:import, meta, _children} = node) when is_list(meta) do
    if Keyword.get(meta, :prelude_injected, false), do: nil, else: node
  end

  defp without_injected_prelude_imports({tag, meta, children}) when is_list(children) do
    normalized =
      children
      |> Enum.map(&without_injected_prelude_imports/1)
      |> Enum.reject(&is_nil/1)

    {tag, meta, normalized}
  end

  defp without_injected_prelude_imports(items) when is_list(items) do
    items
    |> Enum.map(&without_injected_prelude_imports/1)
    |> Enum.reject(&is_nil/1)
  end

  defp without_injected_prelude_imports(other), do: other

  defp source_hash(source) when is_binary(source), do: :crypto.hash(:sha256, source)
  defp source_hash(_source), do: nil

  defp expanded_source_path(file, source) when is_binary(file) and is_binary(source),
    do: Path.expand(file)

  defp expanded_source_path(_file, _source), do: nil

  defp emit_elaboration_event(event) do
    case Process.get(:cure_elaboration_observer) do
      observer when is_pid(observer) -> send(observer, {:cure_elaboration, event})
      _ -> :ok
    end
  end

  defp loaded_dependency_interface_hashes(dependency_names) do
    state = Process.get(@loader_state_key)

    Map.new(dependency_names, fn name ->
      hash =
        case state.modules[name] do
          {:loaded, %ModuleInterface{interface_hash: interface_hash}} -> interface_hash
          _ -> nil
        end

      {name, hash}
    end)
  end

  defp dependency_source_hashes(dependency_names) do
    Map.new(dependency_names, fn name ->
      hash =
        case resolved_module_path(name) do
          nil ->
            nil

          path ->
            case File.read(path) do
              {:ok, source} -> :crypto.hash(:sha256, source)
              {:error, _} -> nil
            end
        end

      {name, hash}
    end)
  end

  defp module_interface_edges(ast) do
    owner = find_module_name(ast)

    imported =
      Enum.flat_map(import_entries(ast), fn {targets, meta} ->
        Enum.map(targets, fn target ->
          %{kind: :use_import, source_module: owner, target: target, line: metadata_line(meta)}
        end)
      end)

    qualified =
      ast
      |> FixityScan.collect_qualified_targets()
      |> Enum.reject(&(&1.target == owner))
      |> Enum.map(fn reference ->
        %{
          kind: :qualified_reference,
          source_module: owner,
          target: reference.target,
          line: reference.line
        }
      end)

    Enum.uniq_by(imported ++ qualified, &{&1.kind, &1.target})
  end

  defp metadata_line(meta) do
    case Cure.MetaAST.Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{whole: %Cure.Diagnostic.Span{start_line: line}} -> line
      _ -> Keyword.get(meta, :line, 1)
    end
  end

  @doc """
  Split an environment into the part `owner` declares and the extensions it
  publishes.

  Both the elaborator and `Cure.Compiler.ModulePipeline.Interface` need to know
  which half of an environment a module owns. There is one answer, and this is
  it: two spellings of "owned by" are how a declared interface silently
  disappears one module boundary away.
  """
  @spec canonical_owned_partition(Env.t(), String.t()) :: %{
          declarations: map(),
          externs: map(),
          extensions: map()
        }
  def canonical_owned_partition(%Env{} = env, owner) when is_binary(owner) do
    %{
      declarations: owned_declarations(env, owner),
      externs: owned_externs(env, owner),
      extensions: interface_extensions(env, owner)
    }
  end

  defp owned_declarations(%Env{} = env, owner) do
    defs = take_owned(env.defs, owner)
    families = take_owned(env.families, owner)
    ctors = take_owned(env.ctors, owner)

    ctor_to_family =
      Map.filter(env.ctor_to_family, fn {ctor, _family} ->
        Cure.Elab.Name.owner(ctor) == owner
      end)

    generated = MapSet.to_list(reachable_generated_keys(env, [defs, families, ctors]))

    %{
      defs: defs,
      families: Map.merge(families, Map.take(env.families, generated)),
      ctors: Map.merge(ctors, Map.take(env.ctors, generated)),
      ctor_to_family: Map.merge(ctor_to_family, Map.take(env.ctor_to_family, generated)),
      equations: take_owned(env.equations, owner)
    }
  end

  # An anonymous-ADT family (`Bool | Int`) has NO owner: its key is derived from
  # its members (`Union<Std.Bool#Bool|Std.Int#Int>`), so every module that writes
  # that type generates the identical family rather than importing someone's. That
  # is why `take_owned/2` cannot find it, and why publishing it is not a
  # duplicate-provider violation — two copies are byte-identical by construction.
  #
  # It must nonetheless travel: a published signature mentioning the union is
  # unverifiable in a consumer whose environment has never seen the family
  # (`{:unknown_family, :"Union<…>"}` at freeze time). Reachability, not "every
  # generated family in the environment": one inherited from a dependency and
  # never mentioned here is that dependency's to carry.
  defp reachable_generated_keys(%Env{} = env, roots) do
    close_generated_keys(env, collect_generated_keys(roots, MapSet.new()))
  end

  # Close under two relations:
  #
  #   * a family DRAGS ITS CONSTRUCTORS. A family record holds only its
  #     parameter/index telescope, so nothing in it mentions
  #     `Union<…>$Std.Int#Int` — yet a consumer matching on the union needs that
  #     constructor by name, and without it the match fails as
  #     `{:unknown_pattern_constructor, …}` while the type itself resolves fine.
  #     `ctor_to_family` is the only place the link is written down.
  #
  #   * an entry MENTIONS another generated key (`(Bool | Int) | String`).
  defp close_generated_keys(%Env{} = env, keys) do
    with_ctors =
      Enum.reduce(env.ctor_to_family, keys, fn {ctor, family}, acc ->
        if MapSet.member?(keys, family), do: MapSet.put(acc, ctor), else: acc
      end)

    key_list = MapSet.to_list(with_ctors)
    entries = [Map.take(env.families, key_list), Map.take(env.ctors, key_list)]
    next = collect_generated_keys(entries, with_ctors)

    if MapSet.equal?(next, keys), do: keys, else: close_generated_keys(env, next)
  end

  # Generated keys are recognised by their reserved prefix, so a single walk over
  # any Core shape finds both families (`Union<…>`) and their constructors
  # (`Union<…>$Std.Int#Int`) without knowing which node types carry them.
  defp collect_generated_keys(term, acc) when is_atom(term) do
    if Cure.Elab.Union.union_family?(term), do: MapSet.put(acc, term), else: acc
  end

  defp collect_generated_keys(term, acc) when is_tuple(term),
    do: term |> Tuple.to_list() |> collect_generated_keys(acc)

  defp collect_generated_keys(term, acc) when is_list(term),
    do: Enum.reduce(term, acc, &collect_generated_keys/2)

  defp collect_generated_keys(%_{} = term, acc),
    do: term |> Map.from_struct() |> collect_generated_keys(acc)

  defp collect_generated_keys(%{} = term, acc),
    do: term |> Map.to_list() |> collect_generated_keys(acc)

  defp collect_generated_keys(_term, acc), do: acc

  defp owned_externs(%Env{} = env, owner) do
    env.defs
    |> take_owned(owner)
    |> Map.filter(fn {_key, definition} -> match?({:extern, _}, definition.body) end)
  end

  defp interface_extensions(%Env{} = env, owner) do
    %{
      interfaces:
        Map.filter(env.interfaces, fn {name, descriptor} ->
          Map.get(descriptor, :owner) == owner or
            Map.has_key?(env.families, Cure.Elab.Name.qualify(owner, name))
        end),
      coherence: owned_coherence(env.coherence, owner),
      primitives: env.primitives,
      builtins: owned_builtins(env.builtins, owner),
      constrained: take_owned(env.constrained, owner),
      lemmas: owned_lemmas(env.lemmas, owner)
    }
  end

  # `requires Iface(a)` is part of a function's CALLING CONVENTION, not a private
  # note: the dictionary a constrained global expects is appended at each concrete
  # call site by `Cure.Elab.Resolve`, which asks `Env.constrained/2` whether the
  # callee wants one. Dropped from the interface, a consumer sees a telescope with
  # a dictionary slot it does not know to fill, and the call fails as
  # `:too_few_arguments` — `Std.Equatable`'s derived `` `!=` `` on any type whose
  # `==` is not a primitive (`a != b` on a user ADT) is the standing example.
  #
  # `lemmas` for the same reason on the proof-search side: an `@lemma` is filed
  # under its conclusion head so `Cure.Elab.ProofSearch` can find it, and the
  # entry's `name` is already owner-qualified, so the assembled `{:global, …}`
  # matches ordinary elaboration in the consumer.
  defp owned_lemmas(lemmas, owner) do
    lemmas
    |> Enum.map(fn {head, entries} ->
      {head, Enum.filter(entries, &(Cure.Elab.Name.owner(&1.name) == owner))}
    end)
    |> Enum.reject(fn {_head, entries} -> entries == [] end)
    |> Map.new()
  end

  # `@builtin(:key)` bindings are part of a module's exported meaning, not a
  # private note to itself: they are how a CONSUMER's compiler-owned syntax finds
  # the family it lowers to. `Std.Bounded` is the only module that may say which
  # family `:bounded` names, and every module elaborating a character literal has
  # to be able to ask. Dropping them from the interface left the family reachable
  # by name while the key that selects it was gone, so `Inductive.builtin/2`
  # returned `nil` in a module that could see `Std.Bounded#Bounded` perfectly well.
  #
  # Only the keys this module actually owns travel. The seeded kernel builtins are
  # re-seeded into every environment from the same source, so re-exporting them
  # would add nothing, and a family owned by someone else is that module's to
  # publish.
  defp owned_builtins(builtins, owner),
    do: Map.filter(builtins, fn {_key, family} -> Cure.Elab.Name.owner(family) == owner end)

  defp owned_coherence(nil, _owner), do: nil

  defp owned_coherence(%Coherence{} = coherence, owner) do
    anon = Map.filter(coherence.anon, fn {_key, ref} -> instance_owned_by?(ref, owner) end)
    named = Map.filter(coherence.named, fn {_key, ref} -> instance_owned_by?(ref, owner) end)

    %Coherence{
      anon: anon,
      named: named,
      anon_origins: Map.take(coherence.anon_origins, Map.keys(anon)),
      named_origins: Map.take(coherence.named_origins, Map.keys(named))
    }
  end

  defp take_owned(table, owner),
    do: Map.filter(table, fn {key, _value} -> Cure.Elab.Name.owner(key) == owner end)

  defp validate_module_identity(ast, requested_name, path) do
    case find_module_name(ast) do
      ^requested_name -> :ok
      nil -> {:error, {:module_identity_missing, path}}
      declared -> {:error, {:module_identity_mismatch, requested_name, declared, path}}
    end
  end

  defp module_dependency_sources(ast) do
    qualified =
      ast
      |> qualified_module_names()
      |> Enum.reject(&ModuleIndex.compiler_owned?/1)

    Enum.uniq(prelude_sources_for(ast) ++ imports(ast) ++ qualified)
  end

  defp module_prelude_env(ast) do
    if prelude_bootstrap?(find_module_name(ast)), do: {:ok, Env.empty()}, else: prelude_slice_env(ast)
  end

  defp checked_prelude_env(ast, :bootstrap_safe), do: module_prelude_env(ast)
  defp checked_prelude_env(ast, :ordinary), do: module_prelude_env(ast)

  defp prelude_sources_for(ast) do
    if prelude_bootstrap?(find_module_name(ast)),
      do: [],
      else: Enum.map(prelude_manifest(), & &1.source)
  end

  # Prelude providers and everything they explicitly import are the bootstrap
  # closure. Injecting a provider back into one of its own dependencies would
  # manufacture a cycle (Std.String imports Std.Char, so handing Std.String's
  # ambient slice to Std.Char would close one).
  # Derive the closure from markers and source imports so adding a new provider
  # never requires editing a compiler-owned name list.
  defp prelude_bootstrap?(module_name),
    do: MapSet.member?(prelude_bootstrap_modules(), module_name)

  defp prelude_bootstrap_modules do
    state = Process.get(@loader_state_key)

    case state && state.prelude_bootstrap do
      %MapSet{} = cached ->
        cached

      _ ->
        entries = prelude_manifest()
        paths = Map.new(entries, &{&1.source, &1.path})
        closure = prelude_bootstrap_modules(Enum.map(entries, & &1.source), paths, MapSet.new())

        if state do
          put_loader_state(%{Process.get(@loader_state_key) | prelude_bootstrap: closure})
        end

        closure
    end
  end

  defp prelude_bootstrap_modules([], _paths, seen), do: seen

  defp prelude_bootstrap_modules([module_name | rest], paths, seen) do
    if MapSet.member?(seen, module_name) do
      prelude_bootstrap_modules(rest, paths, seen)
    else
      path = Map.get(paths, module_name) || resolved_module_path(module_name)
      nested = if path, do: source_imports(path), else: []

      nested_paths =
        Enum.reduce(nested, paths, fn name, acc ->
          case import_source_path(name) do
            {kind, ^name, dependency_path} when kind in [:ok, :ok_user] ->
              Map.put_new(acc, name, dependency_path)

            _ ->
              acc
          end
        end)

      prelude_bootstrap_modules(
        nested ++ rest,
        nested_paths,
        MapSet.put(seen, module_name)
      )
    end
  end

  defp resolved_module_path(module_name) do
    case import_source_path(module_name) do
      {kind, ^module_name, path} when kind in [:ok, :ok_user] -> path
      _ -> nil
    end
  end

  defp source_imports(path) do
    with {:ok, source} <- File.read(path),
         {:ok, tokens} <- Lexer.tokenize(source, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, emit_events: false) do
      imports(ast)
    else
      _ -> []
    end
  end

  # `public use` is part of a module's exported lexical surface, not merely a
  # canonical-pipeline skeleton detail. Classic `Program.elaborate/2` still
  # loads interfaces through this source loader, so construct the same
  # re-export closure at the single interface-environment publication site.
  # The semantic dependency environment already contains every transitive
  # declaration; this helper only selects the canonical keys that may be named
  # bare through the façade. No duplicate declaration or wrapper is created.
  defp public_reexport_bindings(path, %Env{} = env) do
    owners = public_reexport_modules(path)

    env
    |> all_global_keys()
    |> Enum.filter(&(Cure.Elab.Name.owner(&1) in owners))
    |> MapSet.new()
  end

  defp public_reexport_modules(path) do
    fingerprint =
      case File.stat(path) do
        {:ok, stat} -> {stat.mtime, stat.size}
        _ -> :missing
      end

    cache = Process.get(@public_reexport_cache_key, %{})

    case Map.get(cache, path) do
      {^fingerprint, owners} ->
        owners

      _ ->
        owners =
          path
          |> public_reexport_modules_with_state(MapSet.new(), MapSet.new())
          |> elem(1)

        Process.put(@public_reexport_cache_key, Map.put(cache, path, {fingerprint, owners}))
        owners
    end
  end

  defp public_reexport_modules_with_state(path, seen, owners) do
    case File.read(path) do
      {:ok, source} ->
        with {:ok, tokens} <- Lexer.tokenize(source, emit_events: false),
             {:ok, ast} <- Parser.parse(tokens, emit_events: false) do
          public_sources =
            ast
            |> import_entries()
            |> Enum.flat_map(fn {sources, meta} ->
              if Keyword.get(meta, :public, false), do: sources, else: []
            end)

          public_sources
          |> Enum.uniq()
          |> Enum.reduce({seen, owners}, fn module_name, {seen, owners} ->
            if MapSet.member?(seen, module_name) do
              {seen, owners}
            else
              case import_source_path(module_name) do
                {kind, ^module_name, dependency_path} when kind in [:ok, :ok_user] ->
                  {seen, owners} =
                    {MapSet.put(seen, module_name), MapSet.put(owners, module_name)}

                  public_reexport_modules_with_state(dependency_path, seen, owners)

                _ ->
                  {MapSet.put(seen, module_name), owners}
              end
            end
          end)
        else
          _ -> {seen, owners}
        end

      _ ->
        {seen, owners}
    end
  end

  defp dependency_module_names(sources) do
    Enum.flat_map(sources, fn source ->
      case import_source_path(source) do
        {kind, name, _path} when kind in [:ok, :ok_user] -> [name]
        _ -> []
      end
    end)
  end

  defp load_dependency_env(sources) do
    Enum.reduce_while(sources, {:ok, Env.empty()}, fn source, {:ok, acc} ->
      case import_source_path(source) do
        {kind, name, path} when kind in [:ok, :ok_user] ->
          case load_module_interface(name, path) do
            {:ok, interface_env} ->
              case merge_env(acc, interface_env) do
                {:ok, merged} -> {:cont, {:ok, merged}}
                {:error, _} = error -> {:halt, error}
              end

            {:error, _} = error ->
              {:halt, error}
          end

        :not_stdlib ->
          {:cont, {:ok, acc}}

        {:error, _} = error ->
          {:halt, error}
      end
    end)
  end

  # Canonical imported-env builder. Module-owned families, constructors, and
  # definitions already carry their owner-qualified identities when their
  # slices are elaborated, so merging is now a pure identity-preserving map
  # operation. Ambiguity is diagnosed later by Resolution against canonical
  # suffixes and the direct-import set.
  defp shadow_resolved_imports(ast, skeletons) do
    # Prelude providers are loaded and export-filtered by `prelude_slice_env/1`.
    # Merging their full interfaces here would leak every sibling declaration
    # from an item-level marker (for example Std.String.length alongside the
    # marked String alias). This path is exclusively explicit `use` visibility.
    sources = Enum.uniq(imports(ast))

    with {:ok, modules} <- resolve_import_modules(sources),
         {:ok, merged} <-
           Enum.reduce_while(modules, {:ok, Env.empty()}, fn {module_id, path}, {:ok, acc} ->
             interface =
               case skeleton_env(module_id, skeletons) do
                 {:ok, skeleton} -> {:ok, skeleton}
                 :error -> module_slice_env(path)
               end

             case interface do
               {:ok, slice} ->
                 case merge_env(acc, slice) do
                   {:ok, merged} -> {:cont, {:ok, merged}}
                   {:error, _} = err -> {:halt, err}
                 end

               {:error, {:import_cycle, _}} = err ->
                 case skeleton_env(module_id, skeletons) do
                   {:ok, skeleton} ->
                     case merge_env(acc, skeleton) do
                       {:ok, merged} -> {:cont, {:ok, merged}}
                       {:error, _} = merge_error -> {:halt, merge_error}
                     end

                   _ ->
                     {:halt, err}
                 end

               {:error, _} = err ->
                 {:halt, err}
             end
           end) do
      direct_ids = MapSet.new(modules, fn {module_id, _path} -> module_id end)
      {:ok, %{merged | import_modules: direct_ids}, MapSet.new()}
    end
  end

  # Qualified availability is not a lexical import. We load the same canonical
  # module interface so `M.f` and an imported `f` refer to one identity, but
  # install no `import_modules` directness and therefore expose no bare names.
  defp qualified_resolved_imports(ast, skeletons) do
    names = qualified_module_names(ast)
    source_modules = Enum.reject(names, &ModuleIndex.compiler_owned?/1)
    skeleton_names = MapSet.new(skeletons, fn {name, _env} -> name end)
    loadable_modules = Enum.reject(source_modules, &MapSet.member?(skeleton_names, &1))

    with {:ok, env} <- load_dependency_env(loadable_modules),
         {:ok, env} <- merge_lifted_surfaces(env, skeletons, find_module_name(ast) || "Main") do
      {:ok,
       %{
         env
         | import_modules: MapSet.new(),
           bare_modules: MapSet.new(),
           bare_bindings: MapSet.new(),
           qualified_modules: MapSet.new(names)
       }}
    end
  end

  defp skeleton_env(module_name, skeletons) do
    case Enum.find(skeletons, fn {name, _env} -> name == module_name end) do
      {_name, %Env{} = env} -> {:ok, env}
      nil -> :error
    end
  end

  defp install_module_visibility(%Env{} = env, ast) do
    explicit = direct_import_ids(imports(ast))

    ambient =
      if prelude_bootstrap?(find_module_name(ast)),
        do: MapSet.new(),
        else: MapSet.new(prelude_manifest(), & &1.source)

    bare = MapSet.union(explicit, ambient)

    qualified =
      bare
      |> MapSet.union(MapSet.new(qualified_module_names(ast)))
      |> MapSet.union(ModuleIndex.compiler_modules())
      |> MapSet.union(
        env
        |> all_global_keys()
        |> Enum.map(&Cure.Elab.Name.owner/1)
        |> Enum.reject(&is_nil/1)
        |> MapSet.new()
      )

    env
    |> Map.put(:import_modules, explicit)
    |> Env.with_module_visibility(bare, qualified)
    |> merge_qualified_reexport_aliases(public_reexport_alias_roots(explicit))
    |> Map.put(:bare_bindings, visible_bare_bindings(env, ast, explicit))
  end

  # The canonical pipeline has already classified every dependency edge while
  # constructing its immutable manifest.  Consume that classification here;
  # do not turn an authored `use` back into a source-path lookup merely to
  # rediscover the same module identity.
  defp install_canonical_module_visibility(%Env{} = env, ast, opts) do
    case Keyword.fetch(opts, :module_visibility) do
      :error ->
        install_module_visibility(env, ast)

      {:ok, %{lexical: lexical, qualified: qualified} = visibility}
      when is_struct(lexical, MapSet) and is_struct(qualified, MapSet) ->
        ambient = Map.get(visibility, :ambient, MapSet.new())
        reexports = Map.get(visibility, :reexports, MapSet.new())

        bare = lexical

        env
        |> Map.put(:import_modules, lexical)
        |> Env.with_module_visibility(bare, qualified)
        |> merge_qualified_reexport_aliases(Map.get(visibility, :reexport_roots, %{}))
        |> Map.put(
          :bare_bindings,
          canonical_bare_bindings(env, ast, lexical, ambient, reexports)
        )

      {:ok, visibility} ->
        raise ArgumentError,
              "expected :module_visibility to contain MapSet :lexical and :qualified projections, got: #{inspect(visibility)}"
    end
  end

  defp canonical_bare_bindings(env, ast, lexical, ambient, reexports) do
    bindings = visible_bare_bindings(env, ast, MapSet.union(lexical, reexports), false)
    owner = find_module_name(ast)
    explicit = canonical_explicit_modules(ast, MapSet.union(lexical, reexports), ambient)
    preferred = preferred_bases_by_namespace(env, owner, explicit)

    MapSet.reject(bindings, fn key ->
      MapSet.member?(ambient, Cure.Elab.Name.owner(key)) and shadowed?(env, preferred, key)
    end)
  end

  # A module that *authored* `use Std.String` has imported it explicitly, even
  # though `Std.String` is also a prelude provider and therefore reaches every
  # module ambiently.  Deriving "explicit" as `lexical - ambient` alone silently
  # demotes such an import to ambient standing, so its names lose to any
  # same-base name the module happens to own.  Take the authored `use` list as
  # what it says it is, and keep the manifest-derived difference for the
  # re-exported modules that reach this module through an explicit import chain
  # without being named here.
  defp canonical_explicit_modules(ast, lexical, ambient) do
    ast
    |> imports()
    |> direct_import_ids()
    |> MapSet.intersection(lexical)
    |> MapSet.union(MapSet.difference(lexical, ambient))
  end

  # The tables a bare name can resolve through.  `Env.resolve_key/3` is asked
  # for ONE of them at a time — a type position looks in `families`, a pattern
  # in `ctors` — so shadowing is a per-table question too.
  @global_namespaces [:defs, :families, :ctors]

  # base -> the owners that provide it, per table.  Owners are kept rather than
  # collapsed to a set of bases because an explicitly imported module that is
  # ALSO a prelude provider would otherwise make its own names preferred and
  # then shadow them with that preference — `use Std.Nat` evicting `Nat`.
  defp preferred_bases_by_namespace(%Env{} = env, owner, explicit) do
    Map.new(@global_namespaces, fn table ->
      owners_by_base =
        env
        |> Map.fetch!(table)
        |> Map.keys()
        |> Enum.filter(fn key ->
          key_owner = Cure.Elab.Name.owner(key)
          key_owner == owner or MapSet.member?(explicit, key_owner)
        end)
        |> Enum.group_by(&Cure.Elab.Name.base/1, &Cure.Elab.Name.owner/1)
        |> Map.new(fn {base, owners} -> {base, MapSet.new(owners)} end)

      {table, owners_by_base}
    end)
  end

  # Whether a locally-owned or explicitly-imported name shadows this ambient one.
  #
  # Shadowing is judged per table, and an ambient key is dropped only when EVERY
  # table it occupies is shadowed.  A module that declares `type V = … |
  # String(…)` owns a *constructor* named `String`; that must not evict the
  # ambient *type* `Std.String#String`, because a type position asks `families`
  # and finds nothing local competing there.  A namespace-blind rule drops the
  # binding outright, `Env.bare_key_available?/2` then reports the type as
  # invisible, and `resolve_index_name/2` falls through to the constructor
  # branch — a *type* annotation resolving to a *value* constructor, surfaced as
  # a downstream `{:cannot_unify, {:data, …}, {:ctor, …}}` far from its cause.
  #
  # `Std.String#String` occupies `families` AND `ctors`, so keeping it leaves
  # the bare constructor `String` genuinely ambiguous — and that is fine:
  # `Env.resolve_key/3` tries `Owner#name` before any bare binding, so the
  # module's own constructor still wins.  This set is the fallback that decides
  # what an *unowned* bare name may reach, not the resolution order itself.
  defp shadowed?(%Env{} = env, preferred, key) do
    base = Cure.Elab.Name.base(key)
    key_owner = Cure.Elab.Name.owner(key)

    occupied = Enum.filter(@global_namespaces, &Map.has_key?(Map.fetch!(env, &1), key))

    occupied != [] and
      Enum.all?(occupied, fn table ->
        preferred
        |> Map.fetch!(table)
        |> Map.get(base, MapSet.new())
        |> MapSet.delete(key_owner)
        |> Enum.any?()
      end)
  end

  defp public_reexport_modules_for(explicit_modules) do
    Enum.reduce(explicit_modules, MapSet.new(), fn module_name, acc ->
      case import_source_path(module_name) do
        {kind, ^module_name, path} when kind in [:ok, :ok_user] ->
          MapSet.union(acc, public_reexport_modules(path))

        _ ->
          acc
      end
    end)
  end

  # Qualified compatibility spellings are rooted at the module the author
  # imported, not at the importing module.  For `use Std.Regex`, a generated
  # `Std.Regex.configured` must therefore be mapped to the single canonical
  # `Std.Regex.Runtime#configured` key.  Keeping this root-to-closure map
  # explicit also prevents a transitive `use` from accidentally publishing its
  # names under the consumer's module name.
  defp public_reexport_alias_roots(explicit_modules) do
    Map.new(explicit_modules, fn module_name ->
      modules =
        case import_source_path(module_name) do
          {kind, ^module_name, path} when kind in [:ok, :ok_user] ->
            public_reexport_modules(path)

          _ ->
            MapSet.new()
        end

      {module_name, modules}
    end)
  end

  # Preserve old qualified façade spellings without copying declarations into
  # the façade's environment. Each alias points at the single canonical key
  # owned by the public reexport; ambiguous values are deliberately omitted so
  # the normal qualified resolver can report the conflict instead of guessing.
  defp merge_qualified_reexport_aliases(%Env{} = env, roots) when is_map(roots) do
    aliases = qualified_reexport_aliases(env, roots)
    Env.with_qualified_aliases(env, Map.merge(env.qualified_aliases, aliases))
  end

  defp qualified_reexport_aliases(%Env{} = env, roots) when is_map(roots) do
    namespaces = [
      {:type, Map.keys(env.families)},
      {:value, Map.keys(env.defs) ++ Map.keys(env.ctors)}
    ]

    for {root, reexport_modules} <- roots,
        {namespace, keys} <- namespaces,
        {base, owners} <-
          keys
          |> Enum.filter(fn key -> Cure.Elab.Name.owner(key) in reexport_modules end)
          |> Enum.group_by(&(Cure.Elab.Name.base(&1) |> String.to_atom()), & &1)
          |> Enum.map(fn {base, candidates} -> {base, Enum.uniq(candidates)} end),
        [key] <- [owners],
        into: %{} do
      {{root, base, namespace}, key}
    end
  end

  defp visible_bare_bindings(%Env{} = env, ast, explicit_modules, include_reexports? \\ true) do
    owner = find_module_name(ast)

    # A direct `use` imports the façade's public surface as well as its own
    # declarations. Keep this expansion at the shared visibility construction
    # site so classic and canonical loaders agree; ordinary (non-public)
    # transitive imports remain qualified-only.
    reexported_modules = if include_reexports?, do: public_reexport_modules_for(explicit_modules), else: MapSet.new()

    explicit_modules = MapSet.union(explicit_modules, reexported_modules)

    local_and_explicit =
      all_global_keys(env)
      |> Enum.filter(fn key ->
        key_owner = Cure.Elab.Name.owner(key)
        key_owner == owner or MapSet.member?(explicit_modules, key_owner)
      end)

    builtin_families =
      env.builtins
      |> Map.values()
      |> MapSet.new()
      |> MapSet.put(:"Std.Unit#Unit")

    builtin_surface =
      MapSet.to_list(builtin_families) ++
        for(
          {ctor, family} <- env.ctor_to_family,
          MapSet.member?(builtin_families, family),
          do: ctor
        ) ++
        Enum.filter(Map.keys(env.defs), &(Cure.Elab.Name.owner(&1) == "Std.Builtin"))

    prelude_surface =
      Enum.flat_map(prelude_manifest(), fn
        %{source: source, names: :all} ->
          Enum.filter(all_global_keys(env), &(Cure.Elab.Name.owner(&1) == source))

        %{source: source, names: names} ->
          selected_families =
            env.families
            |> Map.keys()
            |> Enum.filter(fn key ->
              Cure.Elab.Name.owner(key) == source and MapSet.member?(names, bare_name_atom(key))
            end)
            |> MapSet.new()

          selected_values =
            [env.defs, env.families]
            |> Enum.flat_map(&Map.keys/1)
            |> Enum.filter(fn key ->
              Cure.Elab.Name.owner(key) == source and MapSet.member?(names, bare_name_atom(key))
            end)

          selected_values ++
            for {ctor, family} <- env.ctor_to_family,
                MapSet.member?(selected_families, family),
                do: ctor
      end)

    MapSet.new(local_and_explicit ++ builtin_surface ++ prelude_surface)
  end

  defp all_global_keys(%Env{} = env),
    do: Enum.uniq(Map.keys(env.defs) ++ Map.keys(env.families) ++ Map.keys(env.ctors))

  defp bare_name_atom(key), do: key |> Cure.Elab.Name.base() |> String.to_atom()

  defp resolve_import_modules(sources) do
    Enum.reduce_while(sources, {:ok, []}, fn source, {:ok, acc} ->
      case import_source_path(source) do
        {kind, module_name, path} when kind in [:ok, :ok_user] ->
          entry = {to_string(module_name), path}
          {:cont, {:ok, if(Enum.any?(acc, &(elem(&1, 0) == elem(entry, 0))), do: acc, else: acc ++ [entry])}}

        :not_stdlib ->
          {:cont, {:ok, acc}}

        {:error, _} = error ->
          {:halt, error}
      end
    end)
  end

  defp import_source_env({kind, module_name, path}, _seen) when kind in [:ok, :ok_user],
    do: with_loader_session(fn -> load_module_interface(module_name, path) end)

  defp direct_import_ids(sources) do
    sources
    |> distinct_import_modules()
    |> MapSet.new(fn {module_id, _path} -> module_id end)
  end

  # Emit-inline markers for the prelude defs whose saturated applications lower
  # to native BEAM forms (connectives → boolean ops, Sigma projections →
  # element/2). Set HERE, on the import path keyed by source module identity —
  # never by bare global atom — so a local def shadowing `eq`/`sigma_first`/…
  # owns an unmarked record and is emitted as an ordinary call (R1 discipline;
  # see `Env.register_inline_hint/3`).
  @inline_hints %{
    "Std.Bool" => [and: :and, or: :or, not: :not, eq: :eq, ne: :ne],
    "Std.Sigma" => [
      sigma_first: :sigma_first,
      sigma_second: :sigma_second,
      tproj2: :tproj2,
      tproj3: :tproj3,
      tproj4: :tproj4,
      tproj5: :tproj5,
      tproj6: :tproj6,
      tproj7: :tproj7,
      tproj8: :tproj8
    ]
  }

  defp mark_inline_hints(env, module_name) do
    case Map.get(@inline_hints, module_name) do
      nil ->
        env

      hints ->
        # Skip a hinted name the module doesn't actually define (a user module
        # merely NAMED Std.Bool must not crash marking).
        Enum.reduce(hints, env, fn {name, key}, e ->
          if Env.get_def(e, name), do: Env.register_inline_hint(e, name, key), else: e
        end)
    end
  end

  defp import_source_path(source) do
    case String.split(source, ".") do
      ["Std" | segments] when segments != [] ->
        dirs = Paths.all_source_dirs()

        case dirs do
          [] ->
            case user_source_path(source) do
              {:ok, path} -> {:ok_user, source, path}
              {:duplicate, paths} -> {:error, {:duplicate_module_identity, source, paths}}
              :not_found -> {:error, {:missing_stdlib_source_dir, source}}
            end

          dirs ->
            # The file convention snake_cases each module-name segment
            # (`Std.Json.Decoder` -> `json_decoder.cure`), so a compound CamelCase
            # segment gets its underscores. The old all-downcase join
            # (`otp_inferencelaws`) missed them, leaving every multi-word module
            # (`Json.Decoder`, `Http.Client`, …) unresolvable on `use` (E3). Try the
            # snake_cased path first, then the legacy join as a fallback for any file that
            # predates the convention.
            candidates =
              [
                Enum.map_join(segments, "_", &Macro.underscore/1),
                String.downcase(Enum.join(segments, "_"))
              ]
              |> Enum.uniq()
              |> Enum.flat_map(fn stem -> Enum.map(dirs, &Path.join(&1, stem <> ".cure")) end)

            case Enum.find(candidates, &File.exists?/1) do
              nil ->
                case user_source_path(source) do
                  {:ok, user_path} -> {:ok_user, source, user_path}
                  {:duplicate, paths} -> {:error, {:duplicate_module_identity, source, paths}}
                  :not_found -> {:error, {:missing_stdlib_source, source, hd(candidates)}}
                end

              path ->
                {:ok, source, path}
            end
        end

      _ ->
        case user_source_path(source) do
          {:ok, path} -> {:ok_user, source, path}
          {:duplicate, paths} -> {:error, {:duplicate_module_identity, source, paths}}
          :not_found -> :not_stdlib
        end
    end
  end

  # Project modules are source imports too. The dependent pipeline searches
  # the configured source roots by declared module name rather than filename,
  # so descriptive filenames such as `zz_lib.cure` remain valid imports.
  defp user_source_path(source) do
    matches =
      Process.get(:cure_source_roots, [])
      |> Enum.flat_map(fn root -> Path.wildcard(Path.join(root, "**/*.cure")) end)
      |> Enum.uniq()
      |> Enum.filter(fn path ->
        case File.read(path) do
          {:ok, contents} ->
            with {:ok, tokens} <- Lexer.tokenize(contents, emit_events: false),
                 {:ok, ast} <- Parser.parse(tokens, emit_events: false),
                 ^source <- find_module_name(ast) do
              true
            else
              _ -> false
            end

          {:error, _} ->
            false
        end
      end)

    case matches do
      [] -> :not_found
      [path] -> {:ok, path}
      paths -> {:duplicate, Enum.sort(paths)}
    end
  end

  # Every `Env` field this function knows how to combine. `merge_env/2` builds a
  # FRESH `%Env{}`, so any field omitted here silently reverts to the struct default
  # — that is how `interfaces`/`coherence`/`constrained` were lost across module
  # boundaries, making an imported interface's instances invisible to the importer
  # and quietly breaking global coherence. The assertion below turns the next such
  # omission into a compile error rather than a runtime mystery.
  @merged_env_keys ~w(families ctors ctor_to_family defs direct_call_summaries totality_components totality_component_of certified totality_certified builtins
                      primitives interfaces interface_methods coherence constrained import_modules bare_modules bare_bindings
                      qualified_modules qualified_aliases lemmas equations module_owner current_def)a

  @env_keys Map.keys(Map.from_struct(%Env{}))
  missing = @env_keys -- @merged_env_keys

  if missing != [] do
    raise CompileError,
      description:
        "Cure.Elab.Program.merge_env/2 does not merge Env field(s) #{inspect(missing)}. " <>
          "Add them to the merge (and to @merged_env_keys) or they will be dropped " <>
          "when an imported module's env is combined with the importing module's."
  end

  defp merge_env(%Env{} = left, %Env{} = right) do
    with {:ok, coherence} <- merge_coherence(left.coherence, right.coherence),
         {:ok, merged_interfaces} <- Cure.Elab.Interface.merge_tables(left.interfaces, right.interfaces) do
      merged =
        %Env{
          families: Map.merge(left.families, right.families),
          ctors: Map.merge(left.ctors, right.ctors),
          ctor_to_family: Map.merge(left.ctor_to_family, right.ctor_to_family),
          defs: merge_defs(left.defs, right.defs),
          # Summaries are self-authenticating through their body/checker hashes.
          # A conflicting entry may be stale after `merge_defs/2` chooses the
          # non-pending body; the kernel's summary gate rejects/rebuilds it before
          # use. Right bias makes repeated import of the same interface idempotent.
          direct_call_summaries: Map.merge(left.direct_call_summaries, right.direct_call_summaries),
          totality_components: Map.merge(left.totality_components, right.totality_components),
          totality_component_of: Map.merge(left.totality_component_of, right.totality_component_of),
          certified: MapSet.union(left.certified || MapSet.new(), right.certified || MapSet.new()),
          totality_certified:
            MapSet.union(
              left.totality_certified || MapSet.new(),
              right.totality_certified || MapSet.new()
            ),
          builtins: Map.merge(left.builtins, right.builtins),
          primitives: Map.merge(left.primitives, right.primitives),
          interfaces: merged_interfaces,
          interface_methods: %{},
          coherence: coherence,
          constrained: Map.merge(left.constrained, right.constrained),
          import_modules: MapSet.union(left.import_modules, right.import_modules),
          bare_modules: merge_module_visibility(left.bare_modules, right.bare_modules),
          bare_bindings: merge_module_visibility(left.bare_bindings, right.bare_bindings),
          qualified_modules: merge_module_visibility(left.qualified_modules, right.qualified_modules),
          qualified_aliases: Map.merge(left.qualified_aliases, right.qualified_aliases),
          lemmas: Map.merge(left.lemmas, right.lemmas, fn _head, ls, rs -> Enum.uniq(ls ++ rs) end),
          equations: Map.merge(left.equations, right.equations, fn _owner, ls, rs -> Enum.uniq(ls ++ rs) end),
          module_owner: left.module_owner || right.module_owner,
          # Transient (set only for the duration of one def's body elaboration in
          # `Declarations.elaborate_real_body/3`, never part of a stored/merged
          # env in practice); mirrors `module_owner`'s merge for consistency.
          current_def: left.current_def || right.current_def
        }

      {:ok, Env.with_interfaces(merged, merged_interfaces)}
    end
  end

  # Right normally wins — the importer's own view of a name is the later, more
  # specific one. The exception is the `{:hole, "__pending__"}` body that
  # `Declarations` forward-declares a signature with: it means "not elaborated
  # yet", so it is strictly LESS information than an elaborated body for the same
  # key and must never displace one. A module's published env can carry that
  # placeholder for a def it does not own (`Std.String` holds a pending record for
  # `Std.Literal`'s `ExpressibleByCharacterLiteral` method), and letting it win
  # deleted a body the ambient prelude had already supplied. Nothing observes that
  # at merge time; it surfaces at the next site that must REDUCE the body, as a
  # literal initializer that will not normalise.
  defp merge_defs(left, right) do
    Map.merge(left, right, fn _key, left_record, right_record ->
      if pending_body?(right_record) and not pending_body?(left_record),
        do: left_record,
        else: right_record
    end)
  end

  defp pending_body?(%{body: {:hole, "__pending__"}}), do: true
  defp pending_body?(_record), do: false

  defp merge_module_visibility(nil, nil), do: nil
  defp merge_module_visibility(nil, %MapSet{} = right), do: right
  defp merge_module_visibility(%MapSet{} = left, nil), do: left
  defp merge_module_visibility(%MapSet{} = left, %MapSet{} = right), do: MapSet.union(left, right)

  defp merge_coherence(nil, right), do: {:ok, right}
  defp merge_coherence(left, nil), do: {:ok, left}

  defp merge_coherence(%Coherence{} = left, %Coherence{} = right) do
    # Global coherence must survive the merge: two modules may not each supply an
    # anonymous instance for the same `(interface, head)`. Identical entries are
    # fine — a diamond import re-delivers the same instance descriptor by two paths,
    # and `import_env/2` accumulates left-to-right — so only a genuine DISAGREEMENT
    # is an overlap. Named instances are exempt from uniqueness by design but their
    # names must still not collide with a different instance.
    with {:ok, anon, anon_origins} <- merge_anon_instances(left, right),
         {:ok, named, named_origins} <- merge_named_instances(left, right) do
      {:ok,
       %Coherence{
         anon: anon,
         named: named,
         anon_origins: anon_origins,
         named_origins: named_origins
       }}
    end
  end

  defp merge_anon_instances(%Coherence{} = left, %Coherence{} = right) do
    Enum.reduce_while(right.anon, {:ok, left.anon, left.anon_origins}, fn {key = {iface, head}, ref},
                                                                          {:ok, anon, origins} ->
      case Map.fetch(anon, key) do
        {:ok, other} ->
          if same_instance_ref?(other, ref) do
            origin = Map.get(origins, key) || Map.get(right.anon_origins, key, %{})
            {:cont, {:ok, anon, Map.put(origins, key, origin)}}
          else
            stored_first = Map.get(origins, key, %{})
            stored_second = Map.get(right.anon_origins, key, %{})
            {first, second} = merged_instance_origins(:anonymous, key, stored_first, stored_second)

            {:halt,
             {:error,
              {:overlapping_instance,
               %{
                 interface: iface,
                 head: head,
                 first_span: Map.get(first, :span),
                 second_span: Map.get(second, :span),
                 first_for: Map.get(first, :for),
                 second_for: Map.get(second, :for)
               }}}}
          end

        :error ->
          {:cont, {:ok, Map.put(anon, key, ref), Map.put(origins, key, Map.get(right.anon_origins, key, %{}))}}
      end
    end)
  end

  # Interface skeletons and full interfaces describe the same conformance with
  # ASTs parsed in different source trees (`lib/std` versus the staged build
  # copy). Source spelling and spans are provenance, not definition identity.
  # The interface/head and owned method globals are the canonical identity; two
  # genuinely distinct implementations cannot own the same canonical methods.
  defp same_instance_ref?(left, right) do
    Map.take(left, [:iface, :head, :methods, :as]) == Map.take(right, [:iface, :head, :methods, :as])
  end

  defp merge_named_instances(%Coherence{} = left, %Coherence{} = right) do
    Enum.reduce_while(right.named, {:ok, left.named, left.named_origins}, fn {name, ref}, {:ok, named, origins} ->
      case Map.fetch(named, name) do
        {:ok, ^ref} ->
          origin = Map.get(origins, name) || Map.get(right.named_origins, name, %{})
          {:cont, {:ok, named, Map.put(origins, name, origin)}}

        {:ok, _other} ->
          stored_first = Map.get(origins, name, %{})
          stored_second = Map.get(right.named_origins, name, %{})
          {first, second} = merged_instance_origins(:named, name, stored_first, stored_second)

          {:halt,
           {:error,
            {:overlapping_named_instance,
             %{
               name: name,
               interface: Map.get(ref, :iface),
               head: Map.get(ref, :head),
               first_interface: Map.get(first, :interface),
               first_head: Map.get(first, :head),
               first_span: Map.get(first, :span),
               second_span: Map.get(second, :span),
               first_for: Map.get(first, :for),
               second_for: Map.get(second, :for)
             }}}}

        :error ->
          {:cont, {:ok, Map.put(named, name, ref), Map.put(origins, name, Map.get(right.named_origins, name, %{}))}}
      end
    end)
  end

  defp merged_instance_origins(kind, key, stored_first, stored_second) do
    case Cure.Elab.SourceMetadata.instance_origins(kind, key) do
      [first | _] = origins ->
        {Map.merge(stored_first, first), Map.merge(stored_second, List.last(origins))}

      [] ->
        {stored_first, stored_second}
    end
  end

  # Two passes so that forward references and mutual recursion resolve: first
  # every type/record is elaborated and every function *signature* is registered;
  # then every function *body* is elaborated against the fully-populated
  # environment. Non-function declarations are elaborated in source order in pass
  # one (a function signature may reference any type declared before it).
  defp elaborate_declarations(items, env, prelude?) do
    with {:ok, items} <- Cure.Elab.Induction.lift_declarations(items) do
      elaborate_lifted_declarations(expand_where_declarations(items), env, prelude?)
    end
  end

  defp elaborate_lifted_declarations(items, env, prelude?) do
    items = annotate_overload_ordinals(items)

    result =
      with {:ok, env1, fn_decls} <- register_pass(items, env, prelude?),
           :ok <- check_overload_legality(env1),
           {:ok, alias_order} <- typealias_order(items, env1),
           {:ok, env_completed} <- complete_typealiases(alias_order, items, env1),
           # Alias bodies are all present after the register pass. Certify their
           # forward chains now so an earlier function body can use conversion
           # through `A -> B -> RHS`; the final sweep below still handles
           # functions whose bodies are only installed by `body_pass/2`.
           env_aliases = TotalityClosure.certify_deferred(env_completed),
           {:ok, env2} <- body_pass(fn_decls, env_aliases) do
        # Every body is now present. Re-certify defs whose totality was DEFERRED
        # in declaration order (a total function calling a helper declared below
        # it — `reverse` → `reverse_acc`), which the in-order per-def certify left
        # uncertified and no later pass revisits. Sound: the kernel re-derives each
        # certificate; genuinely partial defs are rejected exactly as before.
        {:ok, TotalityClosure.certify_deferred(env2)}
      end

    contextualize_trusted_declaration_error(result, items)
  end

  # A context raised by the expression elaborator already names the exact
  # subexpression that failed, and nothing here improves on it. The one exception
  # is `contextualize_body_pass_error/2`'s declaration-boundary FLOOR: it fires
  # for any reason that escapes a body without context, which includes every
  # trusted-declaration failure below — `usage_violation`, `effect_binder_erased`,
  # `extern_arity_mismatch` — whose whole purpose is to name the authored binder
  # and point at its span. Marking the declaration is a last resort, not a claim
  # on the reason, so look for something more precise and restore the floor when
  # there is none.
  defp contextualize_trusted_declaration_error(
         {:error, {:source_context, reason, %{elaboration_stage: :body_pass}}} = error,
         items
       ) do
    case contextualize_trusted_declaration_error({:error, reason}, items) do
      {:error, ^reason} -> error
      refined -> refined
    end
  end

  defp contextualize_trusted_declaration_error({:error, {:source_context, _, _}} = error, _items), do: error

  defp contextualize_trusted_declaration_error({:error, reason} = error, items) do
    case trusted_declaration_span(reason, items) do
      %{span: %Cure.Diagnostic.Span{}} = context ->
        {:error,
         {:source_context, reason,
          Map.merge(
            %{
              expectation_origin: :trusted_declaration_check
            },
            context
          )}}

      {%Cure.Diagnostic.Span{} = span, checking, category} ->
        {:error,
         {:source_context, reason,
          %{
            span: span,
            checking: checking,
            expectation_origin: :trusted_declaration_check,
            expression_category: category
          }}}

      _ ->
        error
    end
  end

  defp contextualize_trusted_declaration_error(result, _items), do: result

  defp trusted_declaration_span({:unknown_erasure_class, name, _class}, items),
    do: erasure_source_context(items, name)

  defp trusted_declaration_span({:erases_on_non_opaque, name}, items),
    do: erasure_source_context(items, name)

  defp trusted_declaration_span({:effect_binder_erased, %{def: name, binder: binder}}, items),
    do: effect_binder_source_context(items, name, binder)

  defp trusted_declaration_span({:non_strictly_positive, constructor}, items),
    do: positivity_source_context(items, constructor)

  defp trusted_declaration_span(
         {:erased_used_relevantly, %{def: name, binder: binder}},
         items
       ) do
    relevance_source_context(items, name, binder)
  end

  defp trusted_declaration_span(
         {:usage_violation, %{def: name, binder: binder, kind: :param} = details},
         items
       ) do
    usage_source_context(items, name, binder, details) ||
      declaration_role_span(items, name, :body, :relevance_check)
  end

  defp trusted_declaration_span({:usage_violation, %{def: name}}, items),
    do: declaration_role_span(items, name, :body, :relevance_check)

  defp trusted_declaration_span(_reason, _items), do: nil

  # Relevance checking intentionally runs over span-free Core. At this boundary the
  # reported de Bruijn level is still the declaration-order parameter index, so we
  # can recover the authored binder without contaminating Core with presentation
  # metadata. We only claim an exact use range when the surface body has one
  # unambiguous occurrence of that name; shadowing or repeated uses fall back to the
  # honest body range instead of pointing at a possibly unrelated token.
  defp relevance_source_context(items, qualified_name, binder) do
    bare_name = qualified_name |> to_string() |> String.split("#") |> List.last()

    Enum.find_value(items, fn
      {:function_def, meta, [body]} when is_list(meta) ->
        if to_string(Keyword.get(meta, :name)) == bare_name do
          params = Keyword.get(meta, :params, [])
          param = Enum.at(params, binder)
          binder_name = if param, do: param_name(param)
          binder_span = ast_role_span(param, :name)
          body_span = ast_role_span(body, :whole) || ast_role_span({:function_def, meta, [body]}, :body)

          use_span =
            body
            |> surface_variable_spans(binder_name)
            |> case do
              [span] -> span
              _ -> body_span
            end

          if use_span do
            %{
              span: use_span,
              binder_span: binder_span,
              binder_name: binder_name,
              checking: qualified_name,
              expression_category: :relevance_check
            }
          end
        end

      _ ->
        nil
    end)
  end

  defp usage_source_context(items, qualified_name, binder, details) do
    bare_name = qualified_name |> to_string() |> String.split("#") |> List.last()

    Enum.find_value(items, fn
      {:function_def, meta, [body]} when is_list(meta) ->
        if to_string(Keyword.get(meta, :name)) == bare_name do
          param = meta |> Keyword.get(:params, []) |> Enum.at(binder)
          binder_name = if param, do: param_name(param)
          binder_span = ast_role_span(param, :name)
          grade_span = ast_role_span(param, :annotation)
          use_spans = surface_variable_spans(body, binder_name)
          body_span = ast_role_span(body, :whole) || ast_role_span({:function_def, meta, [body]}, :body)

          primary_span =
            case Map.get(details, :used) do
              :erased -> binder_span || grade_span || body_span
              _ -> List.last(use_spans) || body_span || binder_span
            end

          if primary_span do
            %{
              span: primary_span,
              binder_span: binder_span,
              grade_span: grade_span,
              binder_name: binder_name,
              use_spans: use_spans,
              checking: qualified_name,
              expression_category: :resource_usage
            }
          end
        end

      _ ->
        nil
    end)
  end

  defp surface_variable_spans(_ast, nil), do: []

  defp surface_variable_spans({:variable, meta, name}, name) when is_list(meta) do
    case ast_role_span({:variable, meta, name}, :name) do
      %Cure.Diagnostic.Span{} = span -> [span]
      _ -> []
    end
  end

  defp surface_variable_spans({tag, _meta, children}, name) when is_atom(tag) do
    surface_variable_spans(children, name)
  end

  defp surface_variable_spans(list, name) when is_list(list),
    do: Enum.flat_map(list, &surface_variable_spans(&1, name))

  defp surface_variable_spans(tuple, name) when is_tuple(tuple) do
    tuple
    |> Tuple.to_list()
    |> Enum.flat_map(&surface_variable_spans(&1, name))
  end

  defp surface_variable_spans(_other, _name), do: []

  defp ast_role_span({_tag, meta, _children}, role) when is_list(meta) do
    meta
    |> Cure.MetaAST.Metadata.source_info()
    |> source_role_span(role)
  end

  defp ast_role_span(_ast, _role), do: nil

  defp positivity_source_context(items, qualified_constructor) do
    constructor = qualified_constructor |> to_string() |> String.split("#") |> List.last()

    Enum.find_value(items, fn
      {:container, container_meta, variants} when is_list(container_meta) and is_list(variants) ->
        family = container_meta |> Keyword.get(:name) |> to_string()

        Enum.find_value(variants, fn
          {:function_def, ctor_meta, _body} when is_list(ctor_meta) ->
            if to_string(Keyword.get(ctor_meta, :name)) == constructor do
              constructor_span = ast_role_span({:function_def, ctor_meta, []}, :name)

              negative_spans =
                ctor_meta
                |> Keyword.get(:params, [])
                |> Enum.flat_map(&negative_recursive_spans(&1, family))
                |> Enum.uniq()

              {span, precise?} =
                case negative_spans do
                  [span] -> {span, true}
                  _ -> {constructor_span, false}
                end

              if span do
                %{
                  span: span,
                  constructor_span: constructor_span,
                  family_name: family,
                  checking: qualified_constructor,
                  expression_category: :constructor_declaration,
                  precise_occurrence: precise?
                }
              end
            end

          _ ->
            nil
        end)

      _ ->
        nil
    end)
  end

  # Cure's strict-positivity rule rejects every recursive occurrence in a
  # function domain, including occurrences nested further inside that domain.
  # Continue through the codomain because it may itself contain another arrow.
  # Other surface type constructors are covariant here, so search their children
  # for nested arrows without marking ordinary recursive arguments as negative.
  defp negative_recursive_spans(
         {:function_call, meta, args},
         family
       )
       when is_list(meta) and is_list(args) do
    if Keyword.get(meta, :function_type, false) do
      {domains, codomain} = Enum.split(args, max(length(args) - 1, 0))

      Enum.flat_map(domains, &recursive_type_spans(&1, family)) ++
        Enum.flat_map(codomain, &negative_recursive_spans(&1, family))
    else
      Enum.flat_map(args, &negative_recursive_spans(&1, family))
    end
  end

  defp negative_recursive_spans({_tag, _meta, children}, family),
    do: negative_recursive_spans(children, family)

  defp negative_recursive_spans(list, family) when is_list(list),
    do: Enum.flat_map(list, &negative_recursive_spans(&1, family))

  defp negative_recursive_spans(tuple, family) when is_tuple(tuple) do
    tuple
    |> Tuple.to_list()
    |> Enum.flat_map(&negative_recursive_spans(&1, family))
  end

  defp negative_recursive_spans(_other, _family), do: []

  defp recursive_type_spans({:variable, meta, family}, family) when is_list(meta) do
    case ast_role_span({:variable, meta, family}, :name) do
      %Cure.Diagnostic.Span{} = span -> [span]
      _ -> []
    end
  end

  defp recursive_type_spans({_tag, _meta, children}, family),
    do: recursive_type_spans(children, family)

  defp recursive_type_spans(list, family) when is_list(list),
    do: Enum.flat_map(list, &recursive_type_spans(&1, family))

  defp recursive_type_spans(tuple, family) when is_tuple(tuple) do
    tuple
    |> Tuple.to_list()
    |> Enum.flat_map(&recursive_type_spans(&1, family))
  end

  defp recursive_type_spans(_other, _family), do: []

  defp declaration_role_span(items, qualified_name, role, category) do
    bare_name = qualified_name |> to_string() |> String.split("#") |> List.last()

    Enum.find_value(items, fn
      {tag, meta, _body} when tag in [:function_def, :container, :indexed_type] and is_list(meta) ->
        if to_string(Keyword.get(meta, :name)) == bare_name do
          info = Cure.MetaAST.Metadata.source_info(meta)
          span = source_role_span(info, role) || source_role_span(info, :name) || source_role_span(info, :whole)
          if span, do: {span, qualified_name, category}
        end

      _ ->
        nil
    end)
  end

  defp erasure_source_context(items, qualified_name) do
    bare_name = qualified_name |> to_string() |> String.split("#") |> List.last()

    Enum.find_value(items, fn
      {tag, meta, _body} when tag in [:container, :indexed_type] and is_list(meta) ->
        if to_string(Keyword.get(meta, :name)) == bare_name do
          info = Cure.MetaAST.Metadata.source_info(meta)
          decorator = info && Map.get(info.decorators, "erases")
          decorator_span = decorator && decorator.whole

          if decorator_span do
            %{
              span: decorator_span,
              decorator_span: decorator_span,
              argument_spans: decorator.arguments,
              name_span: info.name,
              declaration_span: info.whole,
              checking: qualified_name,
              expression_category: :erasure_annotation
            }
          end
        end

      _ ->
        nil
    end)
  end

  defp effect_binder_source_context(items, qualified_name, binder) do
    bare_name = qualified_name |> to_string() |> String.split("#") |> List.last()

    Enum.find_value(items, fn
      {:function_def, meta, _body} when is_list(meta) ->
        if to_string(Keyword.get(meta, :name)) == bare_name do
          parameter = meta |> Keyword.get(:params, []) |> Enum.at(binder)
          info = parameter && parameter |> elem(1) |> Cure.MetaAST.Metadata.source_info()

          if info do
            %{
              span: info.annotation || info.whole,
              parameter_span: info.whole,
              binder_span: info.name,
              opener_span: info.opener,
              closer_span: info.closer,
              binder_name: parameter && param_name(parameter),
              checking: qualified_name,
              expression_category: :effect_binder
            }
          end
        end

      _ ->
        nil
    end)
  end

  defp source_role_span(%Cure.MetaAST.SourceInfo{decorators: decorators}, :erases_decorator) do
    case Map.get(decorators, "erases") do
      %{whole: %Cure.Diagnostic.Span{} = span} -> span
      %{name: %Cure.Diagnostic.Span{} = span} -> span
      _ -> nil
    end
  end

  defp source_role_span(%Cure.MetaAST.SourceInfo{} = info, role) when role in [:name, :whole, :body],
    do: Map.get(info, role)

  defp source_role_span(_info, _role), do: nil

  defp expand_where_declarations(items) when is_list(items) do
    {expanded, _counter} =
      Enum.map_reduce(items, 0, fn
        {:function_def, meta, [body]}, counter when is_list(meta) ->
          case Keyword.get(meta, :where, []) do
            [] ->
              {{:function_def, meta, [body]}, counter}

            bindings ->
              parent = Keyword.fetch!(meta, :name)
              params = Keyword.get(meta, :params, [])
              param_names = Enum.map(params, &param_name/1)
              param_map = Map.new(params, fn p -> {param_name(p), p} end)

              {helpers, helper_names, counter} =
                Enum.reduce(bindings, {[], %{}, counter}, fn
                  {:function_def, hmeta, hbody}, {acc, names, n} ->
                    hname = Keyword.fetch!(hmeta, :name)
                    helper_param_names = hmeta |> Keyword.get(:params, []) |> Enum.map(&param_name/1)

                    captures =
                      param_names
                      |> Enum.reject(&(&1 in helper_param_names))
                      |> Enum.filter(fn name ->
                        surface_occurs?(hbody, name) or surface_occurs?(hmeta, name)
                      end)

                    present_captures =
                      Enum.reject(captures, fn name ->
                        name
                        |> then(&Map.fetch!(param_map, &1))
                        |> implicit_param?()
                      end)

                    fresh = "#{parent}$#{hname}$#{n}"
                    lifted_params = Enum.map(captures, &Map.fetch!(param_map, &1)) ++ Keyword.get(hmeta, :params, [])

                    hmeta =
                      hmeta
                      |> Keyword.put(:name, fresh)
                      |> Keyword.put(:visibility, :private)
                      |> Keyword.put(:params, lifted_params)
                      |> Keyword.put(:arity, length(lifted_params))
                      |> prepend_where_capture_patterns(present_captures)
                      |> Keyword.delete(:where)

                    {body0, _} = List.pop_at(hbody, 0)
                    helper = {:function_def, hmeta, [body0]}
                    {[helper | acc], Map.put(names, hname, {fresh, present_captures}), n + 1}

                  {:where_value, _vmeta, _expr}, acc ->
                    acc
                end)

              helpers = Enum.reverse(helpers)
              # A second pass sees the complete helper table, allowing mutual
              # recursion and calls between helpers.
              helpers =
                Enum.map(helpers, fn {:function_def, hm, [hb]} ->
                  {:function_def, hm, [rewrite_where_calls(hb, helper_names)]}
                end)

              body =
                bindings
                |> Enum.reverse()
                |> Enum.reduce(body, fn
                  {:where_value, vmeta, expr}, acc ->
                    {:block, [line: Keyword.get(vmeta, :line, 0)],
                     [
                       {:assignment, [let: true, line: Keyword.get(vmeta, :line, 0)],
                        [{:variable, [scope: :local], Keyword.fetch!(vmeta, :name)}, expr]},
                       acc
                     ]}

                  _, acc ->
                    acc
                end)

              parent_meta = Keyword.delete(meta, :where)
              parent_decl = {:function_def, parent_meta, [rewrite_where_calls(body, helper_names)]}
              {helpers ++ [parent_decl], counter}
          end

        other, counter ->
          {other, counter}
      end)

    List.flatten(expanded)
  end

  defp expand_where_declarations(items), do: items

  # Clause syntax stores its refutable parameter patterns separately from the
  # declared parameter telescope. Lambda-lifting a captured outer parameter must
  # extend both in lockstep; extending only `params:` shifts every clause column
  # and leaves references to the capture unresolved in the branch body.
  defp prepend_where_capture_patterns(meta, []), do: meta

  defp prepend_where_capture_patterns(meta, captures) do
    capture_patterns = Enum.map(captures, &{:variable, [scope: :local], &1})

    Keyword.update(meta, :clauses, [], fn clauses ->
      Enum.map(clauses, fn clause ->
        Map.update!(clause, :params, &(capture_patterns ++ &1))
      end)
    end)
  end

  defp param_name({:param, _meta, name}), do: name
  defp param_name({name, _type}), do: name

  defp implicit_param?({:param, meta, _name}), do: Keyword.get(meta, :implicit, false)
  defp implicit_param?({_name, _type}), do: false

  defp surface_occurs?(term, name) do
    case term do
      {:variable, _meta, ^name} -> true
      {tag, _meta, children} when is_atom(tag) and is_list(children) -> Enum.any?(children, &surface_occurs?(&1, name))
      {_key, value} -> surface_occurs?(value, name)
      map when is_map(map) -> Enum.any?(Map.values(map), &surface_occurs?(&1, name))
      list when is_list(list) -> Enum.any?(list, &surface_occurs?(&1, name))
      _ -> false
    end
  end

  defp rewrite_where_calls(term, names) do
    case term do
      {:function_call, meta, args} ->
        name = Keyword.get(meta, :name)
        args = Enum.map(args, &rewrite_where_calls(&1, names))

        case Map.get(names, name) do
          {fresh, caps} ->
            cap_args = Enum.map(caps, &{:variable, [scope: :local], &1})
            {:function_call, Keyword.put(meta, :name, fresh), cap_args ++ args}

          nil ->
            {:function_call, meta, args}
        end

      {tag, meta, children} when is_atom(tag) and is_list(children) ->
        {tag, meta, Enum.map(children, &rewrite_where_calls(&1, names))}

      list when is_list(list) ->
        Enum.map(list, &rewrite_where_calls(&1, names))

      other ->
        other
    end
  end

  # Tag each `:function_def` that shares its bare name with a sibling (same-name
  # group of size >= 2) with its declaration-order ordinal within that group, so
  # `function_signature/2` registers it under a discriminated key. Size-one names
  # are left untouched, keeping non-overloaded code byte-identical.
  #
  # Grouping purely by bare `:name` is sound here because `items` can never hold
  # two DIFFERENT sibling modules that share a function name: `check_no_sibling_collision/1`
  # (run inside `check_declarations/1`, ahead of every path that reaches
  # `elaborate_declarations/3`) rejects that combination first. Do not call this
  # from a new entry point that bypasses that precondition.
  defp annotate_overload_ordinals(items) when is_list(items) do
    names =
      Enum.flat_map(items, fn
        {:function_def, meta, _} when is_list(meta) -> [Keyword.fetch!(meta, :name)]
        _ -> []
      end)

    overloaded = for {n, c} <- Enum.frequencies(names), c >= 2, into: MapSet.new(), do: n

    {tagged, _counters} =
      Enum.map_reduce(items, %{}, fn
        {:function_def, meta, body} = decl, counters when is_list(meta) ->
          name = Keyword.fetch!(meta, :name)

          if MapSet.member?(overloaded, name) do
            ord = Map.get(counters, name, 0)

            {{:function_def, Keyword.put(meta, :overload_ordinal, ord), body}, Map.put(counters, name, ord + 1)}
          else
            {decl, counters}
          end

        other, counters ->
          {other, counters}
      end)

    tagged
  end

  defp annotate_overload_ordinals(items), do: items

  # Reject an overload set holding two members that no call site could ever tell
  # apart: same owner, same base name, same arity, and position-wise convertible
  # parameter types. Such a pair is the successor of the old
  # `duplicate_definition` collision — under discriminated keys both members
  # register, so this check is what preserves the "a signature can't be defined
  # twice" guarantee. Runs after `register_pass/3`, once telescopes exist.
  defp check_overload_legality(env) do
    env.defs
    |> Enum.filter(fn {k, _} -> is_atom(k) and Cure.Elab.Name.overload_member?(k) end)
    |> Enum.group_by(fn {k, _} ->
      {Cure.Elab.Name.owner(k), Cure.Elab.Name.overload_base(k)}
    end)
    |> Enum.reduce_while(:ok, fn {{_owner, base}, members}, :ok ->
      case first_overlapping_pair(env, members) do
        nil ->
          {:cont, :ok}

        overlap ->
          {:halt,
           {:error,
            {:overlapping_overload,
             Map.merge(overlap, %{
               name: String.to_atom(base),
               arity: length(overlap.first.parameters)
             })}}}
      end
    end)
  end

  # The arity of the first indistinguishable pair among `members`, or nil. Two
  # members overlap iff their parameter telescopes have equal length, every
  # position is definitionally convertible, AND their argument labels agree at
  # every position (Ph2). A call site discriminates by both the inferred argument
  # types and the written labels, so two members with identical types but distinct
  # labels — `move(to dest: Point)` vs `move(from src: Point)` — ARE tellable
  # apart and legally co-register; only a pair matching on both is a true overlap.
  defp first_overlapping_pair(env, members) do
    typed =
      for {key, def} <- members do
        ptypes = param_types(def.type)

        %{
          id: key,
          parameters: ptypes,
          labels: member_labels(def, length(ptypes)),
          span: Cure.Elab.SourceMetadata.declaration_span(key)
        }
      end
      |> Enum.sort_by(fn
        %{span: %Cure.Diagnostic.Span{start_byte: byte}, id: id} -> {0, byte, id}
        %{id: id} -> {1, 0, id}
      end)

    Enum.find_value(pairs(typed), fn {first, second} ->
      if length(first.parameters) == length(second.parameters) and first.labels == second.labels and
           Enum.all?(Enum.zip(first.parameters, second.parameters), fn {p, q} ->
             Cure.Elab.TypeConv.convertible?(env, p, q)
           end) do
        %{first: first, second: second}
      end
    end)
  end

  # A member's telescope-aligned MANDATORY-label vector: each stored descriptor
  # projected to its external label if writing it is required (`{:required, l}` →
  # `l`), else `nil`. Only mandatory labels distinguish overload members — an
  # OPTIONAL (single-name) label can always be omitted, so a set separable only by
  # optional labels is still ambiguous at a bare call and must stay an overlap.
  # A label-free / no-vector def defaults to an all-`nil` vector so the
  # position-wise comparison is total.
  defp member_labels(def, arity) do
    case Map.get(def, :labels) do
      nil ->
        List.duplicate(nil, arity)

      labels ->
        Enum.map(labels, fn
          {:required, l} -> l
          _optional -> nil
        end)
    end
  end

  # Every parameter domain of a stored def type, in order. Walks the Pi spine
  # collecting each domain unconditionally (value- and type-domains alike) —
  # NOT the `typealias_parameter_count` shape, which only counts `{:type, _}`
  # domains and would silently drop value-typed parameters here.
  defp param_types({:pi, _grade, domain, codomain}), do: [domain | param_types(codomain)]
  defp param_types(_), do: []

  # All unordered pairs of a list, as {earlier, later} tuples.
  defp pairs(list) do
    list
    |> Enum.with_index()
    |> then(fn indexed ->
      for {a, i} <- indexed, {b, j} <- indexed, i < j, do: {a, b}
    end)
  end

  # Transparent aliases are ordinary Core definitions, so a forward chain is
  # harmless once every body is present. A cycle is different: it can never be
  # certified for delta-reduction and would leave apparently declared types
  # permanently opaque. Reject it explicitly instead of accepting a synonym
  # that normalization cannot unfold.
  defp typealias_order(items, env) do
    alias_items =
      items
      |> Enum.flat_map(fn
        {:type_annotation, meta, [_rhs]} = decl when is_list(meta) ->
          if Keyword.get(meta, :typealias, false) do
            name = Env.owned_name(env, meta |> Keyword.fetch!(:name) |> String.to_atom())
            [{name, decl}]
          else
            []
          end

        _ ->
          []
      end)
      |> Map.new()

    aliases = alias_items |> Map.keys() |> MapSet.new()

    graph =
      Map.new(aliases, fn name ->
        deps =
          case Env.get_def(env, name) do
            %{body: body} -> body |> global_refs() |> Enum.filter(&MapSet.member?(aliases, &1)) |> Enum.uniq()
            _ -> []
          end

        {name, deps}
      end)

    kahn_typealiases(graph, [])
  end

  defp kahn_typealiases(graph, order) when map_size(graph) == 0,
    do: {:ok, Enum.reverse(order)}

  defp kahn_typealiases(graph, order) do
    ready =
      graph
      |> Enum.filter(fn {_name, deps} -> deps == [] end)
      |> Enum.map(&elem(&1, 0))
      |> Enum.sort()

    case ready do
      [] ->
        remaining = graph |> Map.keys() |> Enum.sort()
        {:error, {:cyclic_typealiases, remaining ++ [hd(remaining)]}}

      _ ->
        ready_set = MapSet.new(ready)

        graph2 =
          graph
          |> Map.drop(ready)
          |> Map.new(fn {name, deps} -> {name, Enum.reject(deps, &MapSet.member?(ready_set, &1))} end)

        kahn_typealiases(graph2, Enum.reverse(ready) ++ order)
    end
  end

  defp typealias?({:type_annotation, meta, [_rhs]}) when is_list(meta),
    do: Keyword.get(meta, :typealias, false)

  defp typealias?(_), do: false

  # `on_error: :halt` is the authoritative mode: the first alias that fails to
  # elaborate stops the pass and reports. `:skip` is the *provisional* mode used
  # by `register_pass/3` — see the ordering note there.
  defp complete_typealiases(order, items, env, on_error \\ :halt) do
    declarations =
      Map.new(items, fn
        {:type_annotation, meta, [_rhs]} = decl when is_list(meta) ->
          {Env.owned_name(env, meta |> Keyword.fetch!(:name) |> String.to_atom()), decl}

        other ->
          {make_ref(), other}
      end)

    Enum.reduce_while(order, {:ok, env}, fn name, {:ok, acc} ->
      case {Declarations.elaborate(Map.fetch!(declarations, name), acc), on_error} do
        {{:ok, acc2}, _} -> {:cont, {:ok, acc2}}
        {{:error, _}, :skip} -> {:cont, {:ok, acc}}
        {{:error, _} = error, :halt} -> {:halt, error}
      end
    end)
  end

  # A module is ONE mutually-recursive block: an alias body may name a
  # module-level function, and a function signature may name an alias. Concretely
  # `Std.Otp.DepActorServer(m, q, rep)` takes its reply family as a value
  # (`rep : (q) -> Type`), so every query-bearing `actor` expands to
  #
  #     fn ReplyOf(request: ActorRequest) -> Type = …
  #     typealias Handle = Std.Otp.DepActorServer(Message, Request, ReplyOf)
  #
  # Aliases must still be completed BEFORE `body_register_pass/3`, because a
  # function signature routinely mentions one. So this pass is provisional
  # (`:skip`): an alias whose body names a function not yet registered is left
  # for later rather than failing the module. The authoritative pass runs in
  # `elaborate_lifted_declarations/3` against the fully-populated environment and
  # is the one that reports a genuinely unknown name.
  defp register_pass(items, env, prelude?) do
    with {:ok, env_h} <- declare_type_headers(items, env),
         {:ok, alias_order} <- typealias_order(items, env_h),
         {:ok, env_with_aliases} <- complete_typealiases(alias_order, items, env_h, :skip),
         {:ok, env_with_constructors} <- pre_register_constructor_declarations(items, env_with_aliases),
         {:ok, env_with_signatures} <- pre_register_function_signatures(items, env_with_constructors) do
      body_register_pass(items, env_with_signatures, prelude?)
    end
  end

  # Canonical module SCC staging is types → signatures → conformances → bodies.
  # `declare_type_headers/2` establishes family identities, but a dependent
  # function signature may also contain constructor VALUES in an index
  # (`choose(value, On())`, `bind(m, fn(x) -> Pure(x))`). Register the checked
  # constructor payloads before the signature work-list so those values resolve
  # through the same canonical table as they do during body elaboration.
  #
  # This pass has no separate authority: `body_register_pass/3` revisits the same
  # declarations for deriving/builtin side effects, and `Inductive.declare/3` is
  # idempotent for an identical checked family. Type declarations whose payload
  # genuinely depends on a local function remain for the ordinary source pass;
  # only that later pass reports their error.
  defp pre_register_constructor_declarations(items, env) do
    local_functions =
      items
      |> Enum.flat_map(&function_bindings/1)
      |> MapSet.new(fn {name, _meta} -> Atom.to_string(name) end)

    items
    |> Enum.filter(fn
      {:container, meta, _variants} = declaration when is_list(meta) ->
        constructor_bindings(declaration) != []

      _indexed_or_non_constructor ->
        false
    end)
    |> Enum.reduce_while({:ok, env}, fn declaration, {:ok, acc} ->
      case Declarations.elaborate(declaration, acc) do
        {:ok, next} ->
          {:cont, {:ok, next}}

        {:error, reason} = error ->
          if sibling_signature_dependency?(reason, local_functions),
            do: {:cont, {:ok, acc}},
            else: {:halt, error}
      end
    end)
  end

  # A module is one mutually-recursive declaration block, but the old
  # `body_register_pass/3` elaborated function signatures in source order.  An
  # earlier signature that mentioned a later local function therefore saw no
  # canonical def entry and lowered the reference as a bare global.  Re-running
  # the same signature after the later declaration existed produced the proper
  # `Owner#name` key, leaving two definitionally different Core types in one
  # environment.
  #
  # Register every signature that is currently checkable, retrying only an
  # unknown global whose base name is another function in this block.  This is a
  # dependency work-list, not error swallowing: once no declaration makes
  # progress, the first real elaboration error is returned unchanged.  The
  # ordinary registration pass remains authoritative for implementations,
  # labels, overload legality, and declaration ordering; re-registering an
  # already-known ordinary signature is intentionally idempotent.
  defp pre_register_function_signatures(items, env) do
    declarations = Enum.filter(items, &match?({:function_def, _, _}, &1))

    local_names =
      declarations
      |> Enum.map(fn {:function_def, meta, _body} ->
        meta |> Keyword.fetch!(:name) |> to_string()
      end)
      |> MapSet.new()

    pre_register_function_signatures(declarations, env, local_names)
  end

  defp pre_register_function_signatures([], env, _local_names), do: {:ok, env}

  defp pre_register_function_signatures(declarations, env, local_names) do
    {env, deferred, first_error, progress?} =
      Enum.reduce(declarations, {env, [], nil, false}, fn declaration, {acc, pending, first_error, progress?} ->
        case Declarations.register_signature(declaration, acc) do
          {:ok, next} ->
            {next, pending, first_error, true}

          {:error, reason} = error ->
            if sibling_signature_dependency?(reason, local_names) do
              {acc, [declaration | pending], first_error || error, progress?}
            else
              {acc, pending, error, progress?}
            end
        end
      end)

    cond do
      first_error != nil and deferred == [] -> first_error
      deferred == [] -> {:ok, env}
      progress? -> pre_register_function_signatures(Enum.reverse(deferred), env, local_names)
      true -> first_error
    end
  end

  defp sibling_signature_dependency?({:source_context, reason, _context}, local_names),
    do: sibling_signature_dependency?(reason, local_names)

  defp sibling_signature_dependency?({:unknown_global, name}, local_names) when is_atom(name) do
    base = Cure.Elab.Name.base(name) || Atom.to_string(name)
    MapSet.member?(local_names, base)
  end

  defp sibling_signature_dependency?({:unknown_global, name, _details}, local_names) when is_atom(name),
    do: sibling_signature_dependency?({:unknown_global, name}, local_names)

  defp sibling_signature_dependency?(_reason, _local_names), do: false

  # Header pre-pass: register every ctor-bearing type family's HEADER (name +
  # telescopes, empty ctors) before any constructor body is elaborated, so a
  # field type may forward-reference a sibling declared later or a
  # mutually-recursive partner (standard `data`-block scoping). `declare_header`
  # is a no-op for non-type decls and for `@builtin` containers.
  defp declare_type_headers(items, env) do
    Enum.reduce_while(items, {:ok, env}, fn decl, {:ok, acc} ->
      case Declarations.declare_header(decl, acc) do
        {:ok, acc2} -> {:cont, {:ok, acc2}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp body_register_pass(items, env, prelude?) do
    # A module's OWN anonymous `implementation` shadows an ambient one for the same
    # `(interface, head)` reaching it through the `@prelude` slice or an `import`.
    # Concretely: `Std.Comparable` `use`s `Std.Equatable`, and both are `@prelude`,
    # so the whole-module prelude slice re-exports `Std.Equatable`'s own
    # `Equatable for Int` back INTO `Std.Equatable`, where it would collide with the
    # local declaration. Drop those heads from the incoming coherence before the
    # register pass so the local declaration registers cleanly. Two LOCAL
    # declarations for one head still collide with each other (they are re-added into
    # the now-stripped table in source order), so genuine duplicate-instance errors
    # are unaffected.
    env = strip_shadowed_prelude_instances(items, env)
    # The fold threads a fourth accumulator, `pending`: the list of
    # `{iface, super_interface, head}` superinterface obligations recorded by each
    # `implementation`/`deriving` registration. Checking them inline would only
    # see implementations registered EARLIER in source order; instead we drain
    # them against the FINAL coherence table after the fold, so a `requires`
    # obligation is order-independent (see `drain_superinterface_checks/2`).
    Enum.reduce_while(items, {:ok, env, [], []}, fn decl, {:ok, acc, fns, pending} ->
      case decl do
        {:function_def, _meta, _body} ->
          case Declarations.register_signature(decl, acc) do
            {:ok, acc2} -> {:cont, {:ok, acc2, fns ++ [decl], pending}}
            {:error, _} = err -> {:halt, err}
          end

        # An implementation lowers each method to a mangled global; register its
        # signatures + the coherence entry now, and thread the mangled defs into
        # `fns` so their bodies elaborate in the second pass like any function.
        # Its superinterface obligations join `pending` for the post-fold drain.
        {:implementation, _meta, _body} ->
          case Cure.Elab.Implementation.register(decl, acc) do
            {:ok, acc2, mangled_fns, obligations} ->
              {:cont, {:ok, acc2, fns ++ mangled_fns, pending ++ obligations}}

            {:error, _} = err ->
              {:halt, err}
          end

        # A `type … deriving Iface` container elaborates normally, then each named
        # interface is derived structurally: `Cure.Elab.Deriving` synthesises an
        # implementation whose mangled method bodies join `fns` for the second
        # pass, exactly like a hand-written instance.
        {:container, meta, _body} = decl when is_list(meta) ->
          with {:ok, acc2} <- Declarations.elaborate(decl, acc),
               {:ok, acc3} <- maybe_register_builtin(decl, acc2, prelude?),
               {:ok, acc4, derived_fns, derived_obligations} <-
                 register_derived(Keyword.get(meta, :deriving, []), decl, acc3) do
            {:cont, {:ok, acc4, fns ++ derived_fns, pending ++ derived_obligations}}
          else
            {:error, _} = err -> {:halt, err}
          end

        _ ->
          case Declarations.elaborate(decl, acc) do
            {:ok, acc2} ->
              # `maybe_register_builtin` is total ({:ok, _} always), so there is no
              # error branch to thread here.
              case maybe_register_builtin(decl, acc2, prelude?) do
                {:ok, acc3} -> {:cont, {:ok, acc3, fns, pending}}
              end

            # A `typealias` reaching this catch-all is being elaborated for the
            # THIRD time (provisional pass in `register_pass/3`, here, then the
            # authoritative pass in `elaborate_lifted_declarations/3`). Here it is
            # walked in SOURCE order, so an alias written above the function its
            # body names — a module is one mutually-recursive block — would halt
            # the whole module on a name that is registered a few items later.
            # Alias completion has one owner, `complete_typealiases/4`; defer to
            # it rather than reporting from a pass that cannot see the whole
            # module yet.
            {:error, _} = err ->
              if typealias?(decl), do: {:cont, {:ok, acc, fns, pending}}, else: {:halt, err}
          end
      end
    end)
    |> case do
      {:ok, env_final, fns, pending} ->
        # Post-pass over the FINAL env (mirroring `drain_superinterface_checks`):
        # auto-derive a structural `Equatable` for every ADT with no hand-written
        # instance, THEN drain superinterface obligations against the now-complete
        # coherence table — so a hand-written `Comparable for T` may rely on the
        # auto-derived `Equatable for T` to satisfy its `requires Equatable(t)`.
        with {:ok, env2, equatable_fns} <- auto_derive_equatable(items, env_final),
             :ok <- drain_superinterface_checks(env2, pending) do
          {:ok, env2, fns ++ equatable_fns}
        else
          {:error, _} = err -> err
        end

      {:error, _} = err ->
        err
    end
  end

  # Auto-derive a structural `Equatable` instance for every variant-bearing ADT
  # declared in this module that has no hand-written (or explicitly-`deriving`d)
  # instance. This makes the `Equatable` typeclass cover exactly what
  # `build_binop`'s deleted `:error`-branch `struct_eq` covered — ADT `==` now
  # routes to a coherence-registered instance whose body is the same `struct_eq`
  # spine, so it evaluates identically while a user's hand-written instance still
  # supersedes it (override).
  #
  # Runs only when the `Equatable` interface is in scope: a bootstrap-closure
  # module elaborated with `Env.empty()` (Bool, Int, …, and `Std.Equatable`
  # itself before it is ambient) has no interface to instantiate, and its ADTs
  # never route `==` through the typeclass — so there is nothing to derive.
  #
  # A type that already carries an anonymous instance is detected by
  # `Implementation.register/2`'s own `{:overlapping_instance, …}` signal (which
  # uses the exact same head normalisation the coherence table is keyed on), so no
  # separate head recomputation can drift from it.
  # Remove from `env`'s coherence every `(iface, head)` this module declares its own
  # anonymous `implementation` for AND whose ambient instance this very module OWNS —
  # i.e. an instance that reached `env` by re-importing THIS module's own methods
  # through the `@prelude` slice (the `Std.Equatable`/`Std.Comparable` cycle). The
  # ambient `ref`'s method globals are mangled with their owning module's name
  # (`Std.Equatable#__impl_Equatable_Int_==`); if that owner is the module now being
  # elaborated, the "collision" is the module against itself, so the local
  # declaration re-registers cleanly. A FOREIGN redefinition (a user module
  # declaring `implementation Equatable for Int`) leaves the ambient ref in place, so
  # its registration still raises `{:overlapping_instance, …}` — global coherence for
  # stdlib instances is preserved. Named instances (`… as name`) live in a separate
  # name-keyed table and never collide, so they are ignored. A head that fails to
  # resolve is left in place (the local registration will surface the same error).
  defp strip_shadowed_prelude_instances(items, env) do
    coherence = Env.coherence(env) || Coherence.new()
    owner = Env.owner(env)

    # (1) Self-cycle re-imports: an ambient `(iface, head)` this module declares
    # its own `implementation` for AND whose ambient ref this module OWNS (it
    # reached `env` by re-importing this module's own methods through the
    # `@prelude` slice). Stripping lets the local declaration re-register cleanly;
    # a FOREIGN duplicate is left in place so its registration still collides.
    self_heads =
      for {:implementation, meta, _body} <- items,
          is_nil(Keyword.get(meta, :as)),
          iface = meta |> Keyword.fetch!(:interface) |> String.to_atom(),
          for_type = Keyword.fetch!(meta, :for_type),
          {:ok, head} <- [Cure.Elab.Implementation.head_of(env, for_type)],
          ref = Map.get(coherence.anon, {iface, head}),
          not is_nil(ref),
          instance_owned_by?(ref, owner) or Cure.Elab.Name.owner(head) == owner,
          do: {iface, head}

    # Auto-derived instances can also arrive back through a module's own stale
    # prelude/interface slice during an incremental stdlib repair.  They have no
    # authored `implementation` node for the comprehension above to find.  If
    # this module is declaring the head locally and the ambient method globals
    # are owned by this same module, discard that self-import so the post-pass
    # derives and registers a fresh definition body in the current environment.
    local_heads =
      items
      |> Enum.flat_map(fn
        {:container, meta, _body} when is_list(meta) -> [Keyword.get(meta, :name)]
        {:indexed_type, meta, _body} when is_list(meta) -> [Keyword.get(meta, :name)]
        _ -> []
      end)
      |> Enum.reject(&is_nil/1)
      |> Enum.map(fn name ->
        name = if is_atom(name), do: name, else: String.to_atom(name)
        if owner, do: Cure.Elab.Name.qualify(owner, name), else: name
      end)
      |> MapSet.new()

    self_derived_heads =
      for {{_iface, head} = key, ref} <- coherence.anon,
          MapSet.member?(local_heads, head),
          instance_owned_by?(ref, owner),
          do: key

    # (2) Interface shadowing: a module that REDECLARES an `interface I` defines a
    # fresh, locally-scoped typeclass that merely shares the name `I` with the
    # ambient prelude interface (per the E-layer bare-atom shadowing decision).
    # The prelude's ambient instances implement the PRELUDE's `I` (a different
    # method surface — e.g. `Equatable`'s `==` vs. a local `eq`), so none of them
    # belong to the local `I`. Drop EVERY ambient anon entry for a redeclared
    # interface so the local interface + its own implementations register against a
    # clean slate. Genuinely-shared (non-redeclared) interfaces are untouched, so
    # global coherence for stdlib interfaces is preserved.
    redeclared =
      for {:interface, meta, _body} <- items, into: MapSet.new() do
        meta |> Keyword.fetch!(:name) |> String.to_atom()
      end

    keys_to_drop =
      self_heads ++
        self_derived_heads ++
        for {{iface, _head} = key, _ref} <- coherence.anon,
            MapSet.member?(redeclared, iface),
            do: key

    case keys_to_drop do
      [] ->
        env

      _ ->
        Env.put_coherence(env, %{
          coherence
          | anon: Map.drop(coherence.anon, keys_to_drop),
            anon_origins: Map.drop(coherence.anon_origins, keys_to_drop)
        })
    end
  end

  # Is every method global of `ref` mangled with `owner` as its module prefix? A
  # `nil` owner (top-level, un-owned elaboration) owns nothing. The mangled name is
  # `"<Owner>#__impl_<Iface>_<Head>_<method>"`; the owner is the segment before `#`.
  defp instance_owned_by?(_ref, nil), do: false

  defp instance_owned_by?(%{methods: methods}, owner) when is_map(methods) do
    owner_str = to_string(owner)

    methods != %{} and
      Enum.all?(methods, fn {_m, global} ->
        case String.split(Atom.to_string(global), "#", parts: 2) do
          [prefix, _rest] -> prefix == owner_str
          _ -> false
        end
      end)
  end

  defp instance_owned_by?(_ref, _owner), do: false

  defp auto_derive_equatable(items, env) do
    case equatable_method_name(Env.get_interface(env, :Equatable)) do
      # No `Equatable` interface in scope, or it is not the canonical single
      # structural-equality method shape — nothing to auto-derive against.
      nil ->
        {:ok, env, []}

      method_name ->
        auto_derive_equatable(items, env, method_name)
    end
  end

  # The sole method name of a canonical `Equatable` interface (`"=="` for
  # `Std.Equatable`). A multi-method interface named `Equatable` is not the
  # structural-equality shape this generator targets — return `nil` to skip.
  defp equatable_method_name(nil), do: nil

  defp equatable_method_name(%{method_order: [m]}), do: Atom.to_string(m)
  defp equatable_method_name(%{method_order: _}), do: nil
  defp equatable_method_name(_), do: nil

  defp auto_derive_equatable(items, env, method_name) do
    Enum.reduce_while(items, {:ok, env, []}, fn decl, {:ok, acc, fns} ->
      case Cure.Elab.Deriving.struct_eq_instance(decl, method_name, acc) do
        :skip ->
          {:cont, {:ok, acc, fns}}

        {:ok, impl_ast} ->
          case Cure.Elab.Implementation.register(impl_ast, acc) do
            {:ok, acc2, mangled_fns, _obligations} ->
              {:cont, {:ok, acc2, fns ++ mangled_fns}}

            # A hand-written / explicitly-derived instance already covers this type.
            # `register/2` reports the overlap (its coherence key is head-based, so a
            # derived instance whose head matches a hand-written one is rejected
            # BEFORE `register_signatures` runs — the hand-written method body is
            # never overwritten). Leave it authoritative, derive nothing.
            {:error, {:overlapping_instance, %{interface: :Equatable}}} ->
              {:cont, {:ok, acc, fns}}

            {:error, _} = err ->
              {:halt, err}
          end
      end
    end)
  end

  # Verify every recorded superinterface obligation against the
  # FINAL coherence table, now that all implementations in the module are
  # registered. Each `interface Big(t) requires Small(t)` obliges every
  # `implementation Big for T` to have an `implementation Small for T` present —
  # in EITHER source order. On the first unmet obligation, report
  # structured `:missing_superinterface` diagnostic with its implementation source.
  defp drain_superinterface_checks(env, pending) do
    coherence = Env.coherence(env) || Coherence.new()

    Enum.reduce_while(pending, :ok, fn obligation, :ok ->
      %{superinterface: super_interface, head: head} = obligation

      case Coherence.lookup_anon(coherence, super_interface, head) do
        {:ok, _ref} ->
          {:cont, :ok}

        {:error, _} ->
          {:halt, {:error, {:missing_superinterface, obligation}}}
      end
    end)
  end

  # In a designated prelude source, a `@builtin(:key) type Name = ...` container
  # registers the canonical builtin family (schema-validated). Non-prelude
  # sources (or non-`@builtin` decls) pass through unchanged.
  #
  # A `@builtin(:tag) primitive Name` container is NOT an inductive family: its
  # marker is consumed by Declarations.elaborate's :primitive path (which binds
  # the floor), so it must skip the inductive-family schema validation here.
  defp maybe_register_builtin({:container, meta, _body}, env, true) do
    if Keyword.get(meta, :container_type) == :primitive do
      {:ok, env}
    else
      register_builtin_from_meta(meta, env)
    end
  end

  # A `@builtin(:key) type Name indices (...)` GADT family (e.g. Bounded)
  # elaborates to an {:indexed_type} rather than a {:container}; register it
  # identically off its :decorator meta.
  defp maybe_register_builtin({:indexed_type, meta, _ctors}, env, true),
    do: register_builtin_from_meta(meta, env)

  defp maybe_register_builtin(_decl, env, _prelude?), do: {:ok, env}

  # Derive an instance of each named interface for a `deriving` container. Each
  # generated implementation is registered like a hand-written one; its mangled
  # method defs are threaded back so the second pass elaborates their bodies, and
  # its superinterface obligations are threaded back for the post-fold drain.
  defp register_derived([], _decl, env), do: {:ok, env, [], []}

  defp register_derived(names, decl, env) do
    Enum.reduce_while(names, {:ok, env, [], []}, fn name, {:ok, acc, fns, obligations} ->
      iface = String.to_atom(name)

      with {:ok, impl_ast} <- Cure.Elab.Deriving.generate(iface, decl, acc),
           {:ok, acc2, mangled_fns, new_obligations} <-
             Cure.Elab.Implementation.register(impl_ast, acc) do
        {:cont, {:ok, acc2, fns ++ mangled_fns, obligations ++ new_obligations}}
      else
        {:error, {:source_context, _reason, _context}} = err ->
          {:halt, err}

        {:error, reason} ->
          {:halt, {:error, {:source_context, reason, deriving_source_context(decl, name)}}}
      end
    end)
  end

  defp deriving_source_context({:container, meta, _body}, interface) do
    info = Cure.MetaAST.Metadata.source_info(meta) || %Cure.MetaAST.SourceInfo{}
    declaration_name = Keyword.get(meta, :name)

    %{
      span: Map.get(info.fields, {:deriving_interface, interface}) || Map.get(info.fields, :deriving) || info.whole,
      deriving_span: Map.get(info.fields, {:deriving_interface, interface}) || Map.get(info.fields, :deriving),
      declaration_span: info.whole,
      declaration_name_span: info.name,
      checking: declaration_name,
      interface: interface,
      expectation_origin: :deriving,
      expression_category: :deriving_clause
    }
  end

  defp deriving_source_context(_decl, interface),
    do: %{interface: interface, expectation_origin: :deriving, expression_category: :deriving_clause}

  defp register_builtin_from_meta(meta, env) do
    dec = Keyword.get(meta, :decorator)

    if attached_decorator_name(dec) == :builtin do
      {:decorator, _dm, args} = dec
      key = builtin_key(args)

      # The declaration meta still carries the AUTHORED name; `Declarations.elaborate`
      # has just registered the family under its canonical `Owner#Name` key. Bind the
      # builtin key to that canonical id, not to the bare spelling: everything that
      # later asks `Inductive.builtin(env, key)` compares the answer against a real
      # family id — a ctor's owner, a `{:vdata, fid, _}` head — and a bare name
      # matches none of them, so the key would resolve to a family that does not
      # exist while the module's own type checked out fine.
      fid = Env.resolve_key(env, env.families, meta |> Keyword.fetch!(:name) |> String.to_atom())

      :ok = Cure.Core.Builtins.validate!(env, key, fid)
      {:ok, Cure.Core.Inductive.register_builtin(env, key, fid)}
    else
      {:ok, env}
    end
  end

  defp builtin_key([{:literal, _meta, key}]) when is_atom(key), do: key
  defp builtin_key([key]) when is_atom(key), do: key

  defp body_pass(fn_decls, env) do
    Enum.reduce_while(body_pass_order(fn_decls), {:ok, env}, fn decl, {:ok, acc} ->
      case elaborate_body_with_canonical_modules(decl, acc) do
        {:ok, acc2} ->
          {:cont, {:ok, acc2}}

        {:error, _reason} = err ->
          {:halt, contextualize_body_pass_error(err, decl)}
      end
    end)
  end

  # Canonical module compilation receives its complete checked interface table
  # from the phase planner. A missing qualified global is therefore a real
  # resolver error: it must never invoke the source loader and retry.
  defp body_pass_strict(fn_decls, env, owner, event_sink) do
    Enum.reduce_while(body_pass_order(fn_decls), {:ok, env}, fn decl, {:ok, acc} ->
      started = System.monotonic_time(:microsecond)
      metadata = body_timing_metadata(owner, decl)
      call_metrics_before = CallAttemptProfile.metrics()

      stage_sink = fn stage, elapsed ->
        emit_body_timing(event_sink, Map.put(metadata, :stage, stage), elapsed)
      end

      result = Declarations.elaborate_function_body(decl, acc, event_sink: stage_sink)
      elapsed = System.monotonic_time(:microsecond) - started

      emit_body_timing(
        event_sink,
        Map.put(metadata, :call_metrics, CallAttemptProfile.delta(call_metrics_before)),
        elapsed
      )

      case result do
        {:ok, checked} -> {:cont, {:ok, checked}}
        {:error, _} = error -> {:halt, contextualize_body_pass_error(error, decl)}
      end
    end)
  end

  # Reducible bodies are part of the module's definitional interface, not merely
  # runtime implementations. If an earlier body references a later reducible,
  # publish that helper immediately before its first caller so dependent
  # conversion is independent of source order. This is deliberately a stable,
  # dependency-directed move rather than a blanket "all reducibles first": an
  # already-ordered reducible may itself rely on opaque helpers above it. Keep
  # computed-macro users in their later phase because macro expansion has a
  # separate staging dependency.
  defp body_pass_order(fn_decls) do
    {plain, computed} = Enum.split_with(fn_decls, &(not MacroExpand.contains_computed_use?(&1)))
    order_forward_reducibles(plain) ++ order_forward_reducibles(computed)
  end

  defp order_forward_reducibles(declarations) do
    reducible_names =
      declarations
      |> Enum.filter(&reducible_function_declaration?/1)
      |> Enum.map(&function_declaration_name/1)

    Enum.reduce(reducible_names, declarations, fn name, ordered ->
      helper_index = Enum.find_index(ordered, &(function_declaration_name(&1) == name))

      caller_index =
        ordered
        |> Enum.take(helper_index)
        |> Enum.find_index(&MapSet.member?(surface_function_calls(&1), name))

      if is_nil(caller_index) do
        ordered
      else
        {helper, without_helper} = List.pop_at(ordered, helper_index)
        List.insert_at(without_helper, caller_index, helper)
      end
    end)
  end

  defp function_declaration_name({:function_def, meta, _body}) when is_list(meta),
    do: meta |> Keyword.fetch!(:name) |> to_string()

  defp function_declaration_name(_declaration), do: nil

  defp surface_function_calls({:function_call, meta, arguments}) when is_list(meta) do
    called = meta |> Keyword.get(:name) |> to_string()
    Enum.reduce(arguments, MapSet.new([called]), &MapSet.union(surface_function_calls(&1), &2))
  end

  defp surface_function_calls({_tag, meta, children}) when is_list(meta) and is_list(children) do
    MapSet.union(surface_function_calls(meta), surface_function_calls(children))
  end

  defp surface_function_calls({_key, value}), do: surface_function_calls(value)

  defp surface_function_calls(map) when is_map(map),
    do: Enum.reduce(Map.values(map), MapSet.new(), &MapSet.union(surface_function_calls(&1), &2))

  defp surface_function_calls(list) when is_list(list),
    do: Enum.reduce(list, MapSet.new(), &MapSet.union(surface_function_calls(&1), &2))

  defp surface_function_calls(_leaf), do: MapSet.new()

  defp reducible_function_declaration?({:function_def, meta, _body}) when is_list(meta) do
    case Keyword.get(meta, :decorator) do
      {:decorator, decorator_meta, _args} when is_list(decorator_meta) ->
        Keyword.get(decorator_meta, :name) == :reducible

      _ ->
        false
    end
  end

  defp reducible_function_declaration?(_declaration), do: false

  defp body_timing_metadata(owner, {:function_def, meta, _body}) when is_list(meta) do
    source_info = Cure.MetaAST.Metadata.source_info(meta)
    name = Keyword.get(meta, :name)
    params = Keyword.get(meta, :params, [])
    declaration_key = "#{owner}##{name}"

    fingerprint =
      {:function_def, Cure.MetaAST.Metadata.semantic_key(meta), Cure.MetaAST.Metadata.semantic_key(params)}
      |> :erlang.term_to_binary([:deterministic])
      |> then(&:crypto.hash(:sha256, &1))
      |> Base.encode16(case: :lower)

    %{
      module: owner,
      declaration: name,
      canonical_owner: owner,
      canonical_declaration: declaration_key,
      arity: length(params),
      fingerprint: fingerprint,
      span: if(source_info, do: source_info.whole)
    }
  end

  defp emit_body_timing(event_sink, metadata, elapsed) when is_function(event_sink, 2) do
    event_sink.(metadata, elapsed)
    :ok
  rescue
    _ -> :ok
  catch
    _, _ -> :ok
  end

  defp emit_body_timing(_event_sink, _metadata, _elapsed), do: :ok

  # Body elaboration normally attaches expression-level source context itself.
  # Kernel invariant failures such as `:ctor_arity`, however, used to escape as
  # an anonymous atom. Preserve the declaration boundary so an internal failure
  # at least identifies the function and authored span that produced the Core.
  defp contextualize_body_pass_error(
         {:error, {:source_context, _reason, _context}} = error,
         _decl
       ),
       do: error

  # The declaration boundary is a floor, so it applies only when nothing else
  # locates the failure. A reason that already carries an authored span — an
  # `extern_arity_mismatch` points at the target-arity literal inside the
  # decorator — is strictly more precise than the `fn` line containing it, and
  # wrapping it would demote that literal to a secondary.
  defp contextualize_body_pass_error({:error, reason} = error, decl) do
    if located_reason?(reason), do: error, else: contextualize_declaration_boundary(error, decl)
  end

  defp located_reason?(%Cure.Diagnostic.Span{}), do: true
  defp located_reason?(%{span: %Cure.Diagnostic.Span{}}), do: true

  defp located_reason?(reason) when is_tuple(reason),
    do: reason |> Tuple.to_list() |> Enum.any?(&located_reason?/1)

  defp located_reason?(_reason), do: false

  defp contextualize_declaration_boundary({:error, reason}, {:function_def, meta, _body})
       when is_list(meta) do
    source_info = Cure.MetaAST.Metadata.source_info(meta)

    {:error,
     {:source_context, reason,
      %{
        span: if(source_info, do: source_info.whole),
        checking: Keyword.get(meta, :name),
        expression_category: :function_definition,
        elaboration_stage: :body_pass
      }}}
  end

  defp contextualize_declaration_boundary(error, _decl), do: error

  # A computed macro can construct `M.f(...)` even when that spelling was not
  # present in the authored AST. Resolve that failure exactly once through the
  # canonical compile-universe index, merge M's checked interface as qualified
  # (never lexical) availability, and retry the ordinary body elaborator. This
  # is demand-driven module resolution, not a generated-AST dependency scan.
  defp elaborate_body_with_canonical_modules(decl, env) do
    case Declarations.elaborate_function_body(decl, env) do
      {:error, reason} = error ->
        with {:ok, module_name} <- missing_qualified_module(reason),
             {:ok, enriched} <- load_indexed_qualified_module(env, module_name) do
          elaborate_body_with_canonical_modules(decl, enriched)
        else
          _ -> error
        end

      success ->
        success
    end
  end

  defp missing_qualified_module({:source_context, reason, _context}),
    do: missing_qualified_module(reason)

  defp missing_qualified_module({:unknown_global, name}),
    do: module_owner_from_dotted(name)

  defp missing_qualified_module({:unknown_global, name, _details}),
    do: module_owner_from_dotted(name)

  defp missing_qualified_module(_reason), do: :error

  defp module_owner_from_dotted(name) when is_atom(name) or is_binary(name) do
    parts = name |> to_string() |> String.split(".")

    case Enum.split(parts, length(parts) - 1) do
      {[_ | _] = owner, [_name]} -> {:ok, Enum.join(owner, ".")}
      _ -> :error
    end
  end

  defp module_owner_from_dotted(_name), do: :error

  defp load_indexed_qualified_module(env, module_name) do
    with {:ok, source_path} <- canonical_module_path(module_name),
         false <- qualified_module_recorded?(env, module_name),
         {:ok, interface_env} <- load_module_interface(module_name, source_path),
         {:ok, merged} <- merge_env(env, qualified_surface(interface_env)) do
      qualified =
        merge_module_visibility(
          env.qualified_modules,
          MapSet.new([module_name])
        )

      {:ok,
       %{
         merged
         | import_modules: env.import_modules,
           bare_modules: env.bare_modules,
           bare_bindings: env.bare_bindings,
           qualified_modules: qualified
       }}
    else
      _ -> :error
    end
  end

  defp qualified_module_recorded?(%Env{qualified_modules: %MapSet{} = modules}, module_name),
    do: MapSet.member?(modules, module_name)

  defp qualified_module_recorded?(%Env{}, _module_name), do: false

  defp canonical_module_path(module_name) do
    case Process.get(:cure_module_index) do
      %ModuleIndex{} = index ->
        case ModuleIndex.fetch(index, module_name) do
          {:ok, entry} -> {:ok, entry.source_path}
          {:error, _} -> Cure.Compiler.SourceResolver.module_path(module_name)
        end

      _ ->
        Cure.Compiler.SourceResolver.module_path(module_name)
    end
  end

  defp qualified_surface(%Env{} = env) do
    %{
      env
      | coherence: nil,
        import_modules: MapSet.new(),
        bare_modules: MapSet.new(),
        bare_bindings: MapSet.new()
    }
  end
end
