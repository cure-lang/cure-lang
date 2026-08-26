defmodule Cure.Elab.Emit do
  @moduledoc """
  BEAM emission for the erased Core (design spec §8, M9.3).

  The final leg of the pipeline: an elaborated, totality-certified definition is
  erased (its `:erased` index arguments dropped, M9.1) and lowered to Erlang
  abstract forms, which `:compile.forms/2` turns into real bytecode.

  The supported runtime fragment is the non-dependent residue of a checked
  program — exactly what survives erasure:

    * a nullary constructor becomes its atom (`Causal` → `:Causal`, `prim` → `:prim`);
    * an n-ary constructor becomes a tagged tuple of its *present* fields
      (`seq(l, r)` → `{:seq, L, R}`);
    * a dependent `case` becomes an Erlang `case` whose patterns bind only the
      present fields; erased fields carry no runtime slot;
    * a Sigma pair becomes a 2-tuple, `fst`/`snd` become `element/2`.

  A definition whose erased body still contains a hole is refused (§6 negative #5):
  it typechecks but must not be emitted.
  """

  alias Cure.Compiler.BeamWriter
  alias Cure.Core.{Grade, Env, Inductive, RuntimeRefs, Validator}
  alias Cure.Elab.{Erase, Name}

  @line 1

  @doc """
  Emit `functions` from `env` as a module named `module`, compile, and load it.

  Returns `{:ok, module}` on success, `{:error, {:unfilled_hole, name}}` when a
  requested function still contains a hole, or `{:error, reason}` if the Erlang
  compiler rejects the forms.
  """
  @spec compile_and_load(Env.t(), keyword()) :: {:ok, module()} | {:error, term()}
  def compile_and_load(%Env{} = env, opts) do
    module = Keyword.fetch!(opts, :module)
    names = opts |> Keyword.fetch!(:functions) |> Enum.map(&emission_root_key(env, &1))
    origins = Keyword.get(opts, :origins, %{})

    emit_opts =
      opts
      |> Keyword.take([:prefix, :local_owners])
      |> Keyword.put_new_lazy(:artifact_provenance, fn ->
        ephemeral_provenance(module, env)
      end)

    with :ok <- validate_emission_closure(env, names),
         :ok <- reject_holes(env, names) do
      BeamWriter.compile_and_load(module_forms(env, module, names, origins, emit_opts))
    end
  end

  @doc """
  Erlang abstract forms for *every* definition in `env`, as module `module`.

  This is the codegen entry the real compiler pipeline calls for a dependent
  module. Refuses the whole module if any definition still contains a hole
  (§6 negative #5) and reports a definition the runtime fragment cannot express
  rather than crashing the pipeline.
  """
  @spec compile_forms(Env.t(), module()) :: {:ok, [tuple()]} | {:error, term()}
  def compile_forms(%Env{defs: defs} = env, module) do
    # Builtin-op defs are body-less (K2): nothing to emit — saturated uses
    # inline to BEAM operators and first-class uses become local wrappers.
    # (`function_form` would crash on the nil body.) The live pipeline calls
    # /3 with local_defs, so this all-defs entry filters defensively.
    names = for {name, d} <- defs, is_nil(Map.get(d, :builtin_op)), do: name

    compile_forms(env, module, names)
  end

  @doc """
  Erlang abstract forms for a selected set of definitions in `env`.

  Imported definitions may be present in the Core env so conversion can unfold
  them, but an importing module should emit only its own local definitions.
  """
  @spec compile_forms(Env.t(), module(), [atom()]) :: {:ok, [tuple()]} | {:error, term()}
  def compile_forms(%Env{} = env, module, names), do: compile_forms(env, module, names, %{})

  @doc """
  Compatibility form of `compile_forms/3`. The `origins` argument is ignored:
  qualified Core identities are the sole authority for remote-call routing.
  """
  @spec compile_forms(Env.t(), module(), [atom()], map()) :: {:ok, [tuple()]} | {:error, term()}
  def compile_forms(%Env{} = env, module, names, origins),
    do: compile_forms(env, module, names, origins, [])

  @doc "As `compile_forms/4`, with `emit_opts` (`:prefix`/`:local_owners`, see `module_forms/5`)."
  @spec compile_forms(Env.t(), module(), [atom()], map(), keyword()) ::
          {:ok, [tuple()]} | {:error, term()}
  def compile_forms(%Env{} = env, module, names, origins, emit_opts) do
    # Type-level definitions — those whose type ends in a universe (`… -> Type`) —
    # are type synonyms / type-level computations (a large-elim kind selector, a
    # `Lens(s, a) = Optic(LensKind, s, a)` alias). They are computationally
    # irrelevant: their body is a type value (`{:data, LensOptic, …}`) with no BEAM
    # representation, so lowering one crashes emission. Erase them wholesale — no
    # BEAM function, no export — exactly as Idris/Agda/Lean drop type-level
    # definitions. Ordinary value functions that merely MENTION those types in
    # their signatures are unaffected (their codomain is a data type, not `Type`).
    # Hole-check the FULL name set first — an unfilled obligation in a type-level
    # def is still refused (#102 firewall) — then drop the type-level defs from the
    # set that actually reaches emission.
    names = Enum.map(names, &emission_root_key(env, &1))

    with :ok <- validate_emission_closure(env, names),
         :ok <- reject_holes(env, names) do
      emit_names = Enum.reject(names, &type_level_def?(env, &1))

      try do
        {:ok, module_forms(env, module, emit_names, origins, emit_opts)}
      rescue
        e in ArgumentError -> {:error, {:cannot_emit, Exception.message(e)}}
      end
    end
  end

  @doc """
  Validate that every selected definition and every Core global reachable from
  it resolves to a real definition, compiler primitive, or extern boundary.

  This runs before Erlang lowering so a malformed closure is a structured
  compiler diagnostic rather than an `ArgumentError` from `function_form/2`.
  """
  @spec validate_emission_closure(Env.t(), [atom()]) :: :ok | {:error, term()}
  def validate_emission_closure(%Env{} = env, names) do
    selected =
      names
      |> Enum.map(&emission_root_key(env, &1))
      |> MapSet.new()

    selected_owners =
      selected
      |> Enum.map(&Name.owner/1)
      |> Enum.reject(&is_nil/1)
      |> MapSet.new()

    Enum.reduce_while(selected, :ok, fn key, :ok ->
      case validate_selected_definition(env, key, selected, selected_owners) do
        :ok -> {:cont, :ok}
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  defp validate_selected_definition(env, key, selected, selected_owners) do
    definition = Map.get(env.defs, key)

    cond do
      is_nil(definition) ->
        closure_error(:emission_closure_missing, env, key, nil)

      is_map(definition) and type_level_def?(env, key) ->
        :ok

      true ->
        case definition do
          %{body: nil, builtin_op: builtin_op} when not is_nil(builtin_op) ->
            :ok

          %{body: {:extern, {_module, _function, arity}}} when is_integer(arity) and arity >= 0 ->
            :ok

          %{body: body} ->
            body
            |> then(&Erase.erase(env, &1))
            |> RuntimeRefs.globals()
            |> MapSet.new()
            |> Enum.reduce_while(:ok, fn reference, :ok ->
              case validate_emission_reference(env, reference, key, selected, selected_owners) do
                :ok -> {:cont, :ok}
                {:error, _} = error -> {:halt, error}
              end
            end)

          invalid ->
            closure_error(:emission_closure_invalid, env, key, nil, value: invalid)
        end
    end
  end

  defp validate_emission_reference(env, reference, referenced_by, selected, selected_owners) do
    case Map.get(env.defs, reference) do
      nil ->
        if not is_nil(Env.builtin_op(env, reference)) or
             not is_nil(Env.inline_hint(env, reference)) do
          :ok
        else
          closure_error(:emission_closure_missing, env, reference, referenced_by)
        end

      %{body: nil, builtin_op: builtin_op} when not is_nil(builtin_op) ->
        :ok

      %{body: {:extern, {_module, _function, arity}}} when is_integer(arity) and arity >= 0 ->
        :ok

      %{body: _body} ->
        owner = Name.owner(reference)

        if owner == env.module_owner and MapSet.member?(selected_owners, owner) and
             not MapSet.member?(selected, reference) do
          closure_error(:emission_closure_incomplete, env, reference, referenced_by)
        else
          :ok
        end

      definition ->
        closure_error(:emission_closure_invalid, env, reference, referenced_by, value: definition)
    end
  end

  defp closure_error(kind, env, definition, referenced_by, extra \\ []) do
    details =
      extra
      |> Map.new()
      |> Map.merge(%{
        definition: definition,
        referenced_by: referenced_by,
        module: env.module_owner,
        closure_path: [referenced_by, definition] |> Enum.reject(&is_nil/1)
      })

    {:error, {kind, details}}
  end

  # A definition is TYPE-LEVEL when its type's ultimate codomain (after peeling the
  # parameter Π telescope) is a universe `{:type, _}` — i.e. it RETURNS a type. A
  # value function returns a value, so its codomain is a data type / Π / primitive,
  # never a universe.
  defp type_level_def?(env, name) do
    case Map.get(env.defs, name) do
      %{type: type} -> universe_codomain?(type)
      _ -> false
    end
  end

  defp universe_codomain?({:pi, _g, _dom, cod}), do: universe_codomain?(cod)
  defp universe_codomain?({:type, _}), do: true
  defp universe_codomain?(_), do: false

  @doc "The Erlang abstract forms for `functions` in `env`, as module `module`."
  @spec module_forms(Env.t(), module(), [atom()]) :: [tuple()]
  def module_forms(%Env{} = env, module, names), do: module_forms(env, module, names, %{})

  @doc "Compatibility form of `module_forms/3`; `origins` is ignored."
  @spec module_forms(Env.t(), module(), [atom()], map()) :: [tuple()]
  def module_forms(%Env{} = env, module, names, origins),
    do: module_forms(env, module, names, origins, [])

  @doc """
  As `module_forms/4`, with `emit_opts`:

    * `:prefix` — module-name prefix for the emitted group (default `""`).
    * `:local_owners` — owner strings emitted together in this call, whose
      intra-group calls should target the prefixed module. `nil` (default) means
      "derive from `names`"; only consulted when `:prefix` is non-empty.

  With `prefix: ""` the forms are byte-for-byte identical to `module_forms/4`.
  """
  @spec module_forms(Env.t(), module(), [atom()], map(), keyword()) :: [tuple()]
  def module_forms(%Env{} = env, module, names, origins, emit_opts) do
    # Callers commonly select every definition owned by a module. Type formers
    # and interface method signatures are real Core definitions, but neither has
    # a runtime body to turn into an Erlang function.
    names = names |> Enum.map(&emission_root_key(env, &1)) |> Enum.filter(&runtime_definition?(env, &1))
    prefix = Keyword.get(emit_opts, :prefix, "")

    local_owners =
      case Keyword.get(emit_opts, :local_owners) do
        nil -> names |> Enum.map(&Name.owner/1) |> Enum.reject(&is_nil/1) |> MapSet.new()
        list -> MapSet.new(list)
      end

    # Prefix/local-owners route intra-group cross-owner calls to a prefixed
    # target under a non-empty prefix (C2). `origins` remains only as a
    # compatibility argument and cannot participate in identity recovery.
    _ = origins
    Process.put(:cure_emit_prefix, prefix)
    Process.put(:cure_emit_local_owners, local_owners)
    Process.put(:cure_emit_fresh_counter, 0)

    aliases =
      Enum.flat_map(names, fn name ->
        emitted = emit_name_for_key(name)
        [{name, emitted}]
      end)

    Process.put(:cure_emit_aliases, Map.new(aliases))

    try do
      fn_forms = Enum.map(names, &function_form(env, &1))

      exports =
        fn_forms
        |> Enum.reject(fn {:function, _line, name, _arity, _clauses} ->
          String.match?(Atom.to_string(name), ~r/\$[^$]+\$\d+$/)
        end)
        |> Enum.map(fn {:function, _l, name, arity, _cls} -> {name, arity} end)

      [
        {:attribute, @line, :module, module},
        {:attribute, @line, :export, exports}
        | artifact_provenance_attrs(emit_opts) ++ no_auto_import_attr(exports) ++ fn_forms
      ]
    after
      Process.delete(:cure_emit_prefix)
      Process.delete(:cure_emit_local_owners)
      Process.delete(:cure_emit_aliases)
      Process.delete(:cure_emit_fresh_counter)
    end
  end

  defp runtime_definition?(env, name) do
    case Map.get(env.defs, name) do
      %{body: nil} -> false
      %{body: _body} -> not type_level_def?(env, name)
      _ -> false
    end
  end

  # A module that defines a function whose `{name, arity}` matches an Erlang
  # auto-imported BIF (e.g. `size/1`, `byte_size/1`, `length/1` — common `@extern`
  # wrapper or stdlib helper names) shadows that BIF. An unqualified call to it
  # then trips `erl_lint`'s `call_to_redefined_bif` warning. Emit an explicit
  # `-compile({no_auto_import, […]}).` so the local definition unambiguously wins
  # and the warning is silenced — exactly how a hand-written Erlang module handles
  # a BIF-named export. Safe here because every such wrapper's body is a *qualified*
  # remote call (`:erlang.byte_size/1`, `:maps.size/1`), never an unqualified
  # self-call, so re-binding the bare name to the local def cannot loop.
  defp no_auto_import_attr(exports) do
    case Enum.filter(exports, fn {name, arity} -> :erl_internal.bif(name, arity) end) do
      [] -> []
      bifs -> [{:attribute, @line, :compile, {:no_auto_import, bifs}}]
    end
  end

  defp artifact_provenance_attrs(opts) do
    case Keyword.get(opts, :artifact_provenance) do
      provenance when is_map(provenance) ->
        [{:attribute, @line, :cure_artifact, [provenance]}]

      _ ->
        []
    end
  end

  defp ephemeral_provenance(module, env) do
    compiler_hash = Cure.Compiler.BuildManifest.toolchain_fingerprint()
    source_hash = :crypto.hash(:sha256, :erlang.term_to_binary(env, [:deterministic]))

    %{
      format: 1,
      module: module |> Atom.to_string() |> String.replace_prefix("Cure.", ""),
      source_path: "nofile",
      source_hash: source_hash,
      interface_hash: nil,
      compiler_hash: compiler_hash,
      producer_snapshot:
        :crypto.hash(
          :sha256,
          :erlang.term_to_binary(
            %{compiler_hash: compiler_hash, source_hash: source_hash},
            [:deterministic]
          )
        )
    }
  end

  # The module-name prefix for the group currently being emitted (`""` outside an
  # emit or for the default un-prefixed path).
  defp emit_prefix, do: Process.get(:cure_emit_prefix, "")

  # The owner strings emitted together in this call (empty set outside an emit).
  defp emit_local_owners, do: Process.get(:cure_emit_local_owners, MapSet.new())

  defp emit_aliases, do: Process.get(:cure_emit_aliases, %{})

  defp emit_name_for_key(name) do
    case Cure.Elab.Name.base(name) do
      nil -> name
      base -> String.to_atom(base)
    end
  end

  defp emitted_name(name), do: Map.get(emit_aliases(), name, emit_name_for_key(name))

  # Resolve a source `{:global, name}` to a REMOTE `{module, fun}` target or
  # `:local`. Every ordinary global is owner-qualified during elaboration.
  # Local keys are recorded in `emit_aliases`; any remaining qualified key is a
  # remote call. The compatibility emitter arities still accept an `origins`
  # map, but identity is no longer recovered from it: Core is the authority.
  defp remote_target(name) do
    cond do
      Map.has_key?(emit_aliases(), name) ->
        :local

      (owner = Name.owner(name)) != nil ->
        base = String.to_atom(Name.base(name))
        prefix = emit_prefix()

        if prefix != "" and MapSet.member?(emit_local_owners(), owner) do
          {String.to_atom(prefix <> "Cure." <> owner), base}
        else
          {String.to_atom("Cure." <> owner), base}
        end

      true ->
        :local
    end
  end

  # -- functions --------------------------------------------------------------

  # The single trusted enforcement point for "no unfilled obligation ships" (K3).
  # Validates the *pre-erase* Core body against the strict release config: the
  # validator descends into erased subterms (rewrite proof/motive, eq/refl args)
  # that `Erase.erase` drops, so a hole hidden in an erased position is caught
  # here rather than shipped silently (#102). A `no_hole` rejection maps to the
  # public E014 reason (with exact authored metadata when available); any other
  # release-clause rejection surfaces as a `{:final_core_violation, name, _}`
  # rather than crashing codegen.
  defp reject_holes(env, names) do
    Enum.reduce_while(names, :ok, fn name, :ok ->
      with {:ok, body} <- def_body(env, name) do
        case Validator.validate(body, Validator.release_config()) do
          {:ok, _warnings} ->
            {:cont, :ok}

          {:error, rejections} ->
            case Enum.find(rejections, &(&1.clause == :no_hole)) do
              nil -> {:halt, {:error, {:final_core_violation, name, rejections}}}
              rejection -> {:halt, {:error, unfilled_hole_error(env, name, rejection)}}
            end
        end
      else
        {:error, reason} -> {:halt, {:error, reason}}
      end
    end)
  end

  defp unfilled_hole_error(env, name, %{node: {:hole, hole_id}}) do
    source = env.defs |> Map.get(name) |> then(&if(&1, do: Map.get(&1, :source_holes, %{}), else: %{}))

    case Map.get(source, hole_id) do
      nil -> {:unfilled_hole, name}
      details -> {:unfilled_hole, Map.merge(%{definition: name, hole_id: hole_id}, details)}
    end
  end

  defp def_body(env, name) do
    case Map.get(env.defs, name) do
      %{body: body} -> {:ok, body}
      nil -> closure_error(:emission_closure_missing, env, name, nil)
    end
  end

  defp function_form(env, name) do
    case Map.get(env.defs, name) do
      %{body: {:extern, {mod, fun, _arity}}} = def ->
        extern_form(
          emitted_name(name),
          {mod, fun},
          present_arity(env, name),
          extern_union_members(env, def),
          env
        )

      def ->
        real_function_form(emitted_name(name), def, env)
    end
  end

  # Emission accepts an authored bare spelling only as a root of the current
  # module. Recursive edges are already canonical Core identities. Never route
  # this boundary through `Env.resolve_key/3`: its lexical unique-provider
  # fallback is correct during elaboration but would let a missing local root be
  # guessed from an unrelated imported definition with the same suffix.
  defp emission_root_key(%Env{module_owner: owner, defs: defs}, name) when is_atom(name) do
    local = if is_binary(owner), do: Name.qualify(owner, name)

    cond do
      not is_nil(local) and Map.has_key?(defs, local) -> local
      Map.has_key?(defs, name) -> name
      Name.qualified?(name) -> name
      not is_nil(local) -> local
      true -> name
    end
  end

  # The members of an `@extern`'s union return type, tagged with their constructor names,
  # or nil when it does not return a union. Drives the discriminating wrapper below.
  defp extern_union_members(env, %{type: pi, quantities: quantities}) do
    codomain =
      pi
      |> codomain_of(length(quantities || []))
      |> Cure.Elab.Declarations.strip_effect()

    case codomain do
      {:data, ukey, [], []} ->
        if Cure.Elab.Union.union_family?(ukey) do
          env
          |> Cure.Elab.Union.members_of(ukey)
          |> Enum.map(&Map.put(&1, :ctor, Cure.Elab.Union.ctor_key(ukey, &1)))
        end

      _ ->
        nil
    end
  end

  defp codomain_of(type, 0), do: type
  defp codomain_of({:pi, _g, _dom, cod}, n), do: codomain_of(cod, n - 1)
  defp codomain_of(type, _n), do: type

  # Wave-3: emit a direct Erlang remote call, mirroring codegen.ex:691-705 (NOT
  # calling it). Params are synthesized from the arity — a bodyless extern has no
  # {:lam, Cure.Core.Grade.unrestricted(),…} chain to peel, so peel_params/4 would yield zero params for arity>0.
  # `0..(arity-1)//1` yields `[]` at arity 0 → `mod:fun()`, correct.
  #
  # The arity is the def's PRESENT count, as in `real_function_form/3` and at every call site
  # (`present_arity/2`), never the raw literal from `@extern(…)` — an erased parameter never
  # reaches the BEAM. `Declarations.check_extern_arity/2` rejects a literal that disagrees, so
  # the two agree by construction; reading the quantities here keeps that true by construction
  # rather than by convention.
  defp extern_form(fn_atom, {mod, fun}, arity, union_members, env) do
    param_forms = for i <- 0..(arity - 1)//1, do: {:var, @line, :"V#{i}"}
    remote = {:call, @line, {:remote, @line, {:atom, @line, mod}, {:atom, @line, fun}}, param_forms}

    body =
      case union_members do
        nil -> remote
        members -> union_dispatch(remote, members, env)
      end

    {:function, @line, fn_atom, arity, [{:clause, @line, param_forms, [], [body]}]}
  end

  # An `@extern` whose return type is an anonymous union: Erlang hands back an UNTAGGED
  # value, so the boundary re-tags it. Guard on the raw result and inject the matching
  # constructor, turning the FFI value into a real tagged union the moment it enters Cure.
  #
  # `Declarations.check_extern_not_union/2` has already established that the members are
  # pairwise distinguishable, so exactly one clause can match. There is deliberately NO
  # catch-all: if Erlang returns a shape outside the declared union, the extern's type was
  # a lie, and a `CaseClauseError` naming the offending value is the honest outcome.
  #
  # Literal members are matched by EXACT VALUE and come first — they are strictly more
  # specific than a type member's guard.
  defp union_dispatch(remote, members, env) do
    clauses =
      members
      |> Cure.Elab.Union.discrimination_order(env)
      |> Enum.map(fn
        %{payload: nil} = lit -> literal_clause(lit)
        type -> type_clause(type, env)
      end)

    {:case, @line, remote, clauses}
  end

  # `R when R =:= <lit> -> :'Union<…>$<key>'` — a literal member is a NULLARY ctor, so it
  # erases to the bare constructor atom with no payload.
  defp literal_clause(%{key: key, ctor: ctor}) do
    {:ok, _kind, value} = Cure.Elab.Union.literal_value(key)

    guard = {:op, @line, :"=:=", {:var, @line, :R}, literal_form(value)}
    {:clause, @line, [{:var, @line, :R}], [[guard]], [{:atom, @line, ctor}]}
  end

  # `R when is_integer(R) -> {:'Union<…>$Int', R}` — a type member is a 1-ary ctor, so it
  # erases to a tagged 2-tuple carrying the raw value.
  defp type_clause(%{ctor: ctor} = member, env) do
    body = {:tuple, @line, [{:atom, @line, ctor}, {:var, @line, :R}]}

    # The guard sequence is a CONJUNCTION. A class test alone is not always enough: it must
    # never be WIDER than the member's value set, or the wrapper fabricates a value the
    # author never asserted. `Nat` erases to a plain integer, but `is_integer` also accepts
    # negatives — a raw -7 was being tagged Nat(-7). `Bounded(n)` (hence `Char`) is an
    # integer confined to 0..n-1.
    guards =
      [class_test(member, env) | bound_tests(Cure.Elab.Union.value_bounds(member))]

    {:clause, @line, [{:var, @line, :R}], [guards], [body]}
  end

  defp class_test(member, env) do
    test = class_guard(Cure.Elab.Union.runtime_class(env, member))
    {:call, @line, {:atom, @line, test}, [{:var, @line, :R}]}
  end

  defp bound_tests(nil), do: []

  defp bound_tests({min, :infinity}),
    do: [{:op, @line, :>=, {:var, @line, :R}, {:integer, @line, min}}]

  defp bound_tests({min, max}),
    do: [
      {:op, @line, :>=, {:var, @line, :R}, {:integer, @line, min}},
      {:op, @line, :<, {:var, @line, :R}, {:integer, @line, max}}
    ]

  # `is_boolean` strictly refines `is_atom`, and `Union.discrimination_order/1` puts it
  # first — so `true`/`false` take the Bool clause and every other atom falls through to
  # Atom. That is why `Bool | Atom` is admissible rather than a collision.
  defp class_guard(:boolean), do: :is_boolean
  defp class_guard(:atom), do: :is_atom
  defp class_guard(:integer), do: :is_integer
  defp class_guard(:float), do: :is_float
  defp class_guard(:binary), do: :is_binary
  defp class_guard(:list), do: :is_list
  defp class_guard(:pid), do: :is_pid
  defp class_guard(:reference), do: :is_reference

  defp literal_form(v) when is_integer(v), do: {:integer, @line, v}
  defp literal_form(v) when is_float(v), do: {:float, @line, v}
  defp literal_form(v) when is_atom(v), do: {:atom, @line, v}
  defp literal_form(v) when is_binary(v), do: {:string, @line, String.to_charlist(v)}

  defp real_function_form(name, %{body: body, quantities: quantities}, env) do
    qs = quantities || []
    {param_names, inner} = peel_params(Erase.erase(env, body), qs, 0, [])

    ctx = Enum.reverse(param_names)
    body_form = lower(env, inner, ctx)

    params =
      for {n, q} <- Enum.zip(param_names, qs),
          Grade.present?(q),
          do: underscore_if_unused({:var, @line, n}, body_form)

    clause = {:clause, @line, params, [], [body_form]}
    {:function, @line, name, length(params), [clause]}
  end

  # Peel one binder per declared parameter, naming present binders `V<pos>` (bound
  # as Erlang params) and erased binders `_e<pos>` (dead after erasure).
  defp peel_params(term, [], _pos, acc), do: {Enum.reverse(acc), term}

  defp peel_params({:lam, _g, _dom, body}, [q | qs], pos, acc) do
    name = if Grade.present?(q), do: :"V#{pos}", else: :"_e#{pos}"
    peel_params(body, qs, pos + 1, [name | acc])
  end

  defp peel_params(term, _qs, _pos, acc), do: {Enum.reverse(acc), term}

  # -- expressions ------------------------------------------------------------

  # `ctx` lists the in-scope Erlang variable atoms with de Bruijn index 0 first.
  defp lower(_env, {:var, k}, ctx) do
    case Enum.at(ctx, k) do
      nil -> raise ArgumentError, "de Bruijn index #{k} out of range"
      name -> {:var, @line, name}
    end
  end

  defp lower(env, {:ctor, name, args}, ctx) do
    cond do
      args == [] and bool_ctor?(env, name) ->
        {:atom, @line, bool_atom(name)}

      nat_ctor?(env, name) ->
        case args do
          [] -> {:integer, @line, 0}
          [n] -> {:op, @line, :+, lower(env, n, ctx), {:integer, @line, 1}}
        end

      # Bounded erases exactly like Nat — `First` → 0, `Next(pred)` → pred+1 — so a
      # codepoint is a native integer at runtime (matches `{:bounded_lit, _}`). But
      # Bounded is INDEXED: each ctor app also carries an erased implicit index `m`,
      # so drop the erased args and keep only the present predecessor (if any).
      bounded_ctor?(env, name) ->
        case bounded_present_args(env, name, args) do
          [] -> {:integer, @line, 0}
          [n] -> {:op, @line, :+, lower(env, n, ctx), {:integer, @line, 1}}
        end

      sigma_ctor?(env, name) ->
        # A UNIT-TERMINATED `mk_pair` spine `mk_pair(e1, … mk_pair(en, unit))` is a
        # flat telescope `Tuple(T1,…,Tn)` — lower it to ONE flat BEAM tuple
        # `{e1,…,en}`, dropping the `unit`. Each car is lowered independently, so an
        # inner telescope car flattens on its own (opt-in nesting: `%[1,%[2,3]]` →
        # `{1,{2,3}}`). A NON-unit-terminated pair (a bare `Sigma(x:T,U)`) keeps the
        # structural nested 2-tuple emit. The `unit` marker is thus consumed here and
        # never appears at runtime.
        case telescope_cars(env, {:ctor, name, args}) do
          {:telescope, cars} -> {:tuple, @line, Enum.map(cars, &lower(env, &1, ctx))}
          :not_telescope -> {:tuple, @line, Enum.map(args, &lower(env, &1, ctx))}
        end

      list_ctor?(env, name) ->
        case {base_name(name), args} do
          {:Nil, []} -> {nil, @line}
          {:Cons, [h, t]} -> {:cons, @line, lower(env, h, ctx), lower(env, t, ctx)}
        end

      # case-on-Int construction: both ctors are 1-ary, so dispatch by NAME.
      #   FromNat(n)           -> n            (identity — NO +1, unlike Nat's S)
      #   NegativeSuccessor(n) -> -(n + 1) = 0 - n - 1
      # A closed application already folds to {:int_lit,_} before emit (Task 2), so
      # this path fires only on OPEN constructor terms.
      int_ctor?(env, name) ->
        [n] = args

        case base_name(name) do
          :FromNat ->
            lower(env, n, ctx)

          :NegativeSuccessor ->
            {:op, @line, :-, {:op, @line, :-, {:integer, @line, 0}, lower(env, n, ctx)}, {:integer, @line, 1}}
        end

      true ->
        case Enum.map(args, &lower(env, &1, ctx)) do
          [] -> {:atom, @line, otp_tag(name)}
          forms -> {:tuple, @line, [{:atom, @line, otp_tag(name)} | forms]}
        end
    end
  end

  defp lower(env, {:case, scrut, _motive, branches}, ctx) do
    scrut_form = lower(env, scrut, ctx)
    clauses = Enum.map(branches, &branch_clause(env, &1, ctx))
    irrefutable_projection(scrut_form, clauses) || {:case, @line, scrut_form, clauses}
  end

  defp lower(_env, {:int_lit, n}, _ctx), do: {:integer, @line, n}
  # A compact Nat literal emits as a raw BEAM integer — identical to the existing
  # Nat-ctor erasure (`Z` → 0, `S(n)` → n+1), so `{:nat_lit, 2}` and `S(S(Z))`
  # compile to the same value `2` and interoperate with nat `case` clauses.
  defp lower(_env, {:nat_lit, n}, _ctx), do: {:integer, @line, n}
  # A compact Bounded literal erases to its raw codepoint integer — identical to
  # the `First` → 0 / `Next(n)` → n+1 constructor erasure, so `{:bounded_lit, 97}`
  # and `Next(...First)` compile to the same value 97.
  defp lower(_env, {:bounded_lit, n}, _ctx), do: {:integer, @line, n}
  defp lower(_env, {:float_lit, f}, _ctx), do: {:float, @line, f}
  # An atom literal is its own BEAM value.
  defp lower(_env, {:atom_lit, a}, _ctx), do: {:atom, @line, a}

  # A first-class lambda erases to a curried 1-argument BEAM fun; its parameter
  # takes de Bruijn index 0 in the body's frame.
  defp lower(env, {:lam, _g, _dom, body}, ctx) do
    var = fresh_var("Fn")
    body_form = lower(env, body, [var | ctx])
    clause = {:clause, @line, [{:var, @line, unused_underscore(var, body_form)}], [], [body_form]}
    {:fun, @line, {:clauses, [clause]}}
  end

  # `let x := v in body`  ⟶  `begin Lk = <v>, <body> end`. This is the whole
  # payoff of the `:let` binder: `v` is emitted ONCE and bound to a BEAM variable,
  # where surface substitution emitted it at every use site (and not at all at
  # zero uses). Its parameter takes de Bruijn index 0 in the body's frame.
  defp lower(env, {:let, _g, _ty, val, body}, ctx) do
    var = fresh_var("L")
    body_form = lower(env, body, [var | ctx])
    bind = {:match, @line, {:var, @line, unused_underscore(var, body_form)}, lower(env, val, ctx)}
    {:block, @line, [bind, body_form]}
  end

  defp lower(env, {:app, _, _} = app, ctx) do
    {head, args} = spine(app, [])

    case builtin_op_form(head, args, env, ctx) do
      {:ok, form} ->
        form

      :no ->
        case connective_inline(head, args, env, ctx) do
          {:ok, form} ->
            form

          :no ->
            lower_app_spine(env, head, args, ctx)
        end
    end
  end

  # A bare global: a nullary definition is called (`name()`); a definition with
  # present parameters used as a *value* (passed to a higher-order function)
  # becomes a function reference `fun name/arity`. A BUILTIN-OP global has no
  # compiled top-level function to reference (body-less; present_arity would
  # read its nil quantities as 0 and emit a bogus `name()` call) — it becomes a
  # local curried fun wrapper computing the op (K2 §1.5b).
  defp lower(env, {:global, name}, _ctx) do
    case Env.builtin_op(env, name) do
      nil ->
        case present_arity(env, name) do
          0 ->
            case remote_target(name) do
              :local -> {:call, @line, {:atom, @line, emitted_name(name)}, []}
              {mod, fun} -> {:call, @line, {:remote, @line, {:atom, @line, mod}, {:atom, @line, fun}}, []}
            end

          n ->
            callee =
              case remote_target(name) do
                :local -> {:atom, @line, emitted_name(name)}
                {mod, fun} -> {:remote, @line, {:atom, @line, mod}, {:atom, @line, fun}}
              end

            curried_global_wrapper(callee, n)
        end

      op ->
        builtin_op_wrapper(op)
    end
  end

  # {:absurd} is deleted from produced Core (K4 §H: the elaborator omits impossible
  # branches; the validator release-rejects it; Term.term? excludes it). Retained
  # only as a defensive stub — a hand-crafted {:absurd} reaching emit lowers to a
  # crash rather than the raising catch-all. Not produced in practice.
  defp lower(_env, {:absurd}, _ctx),
    do: {:call, @line, {:atom, @line, :error}, [{:atom, @line, :absurd}]}

  # `bind(e, λx. body)` lowers DIRECT-STYLE (design §6): on the strict BEAM `e`
  # performs its effect the moment it is evaluated, so this is exactly the `:let`
  # block — `begin Ek = <e>, <body> end`. The elaborator always emits a literal-λ
  # continuation (slice c: `let x = e ⏎ rest`), the dominant "effect consumed
  # where produced" case; the emitted shape is byte-for-byte the bespoke path's.
  defp lower(env, {:effect_bind, e, {:lam, _g, _dom, body}}, ctx) do
    var = fresh_var("E")
    body_form = lower(env, body, [var | ctx])
    bind = {:match, @line, {:var, @line, unused_underscore(var, body_form)}, lower(env, e, ctx)}
    {:block, @line, [bind, body_form]}
  end

  # `pure(a)` in direct (tail) position is just `a` — no effect to perform.
  defp lower(env, {:effect_pure, a}, ctx), do: lower(env, a, ctx)

  defp lower(_env, term, _ctx), do: raise(ArgumentError, "cannot emit #{inspect(term)}")

  # A single-clause `case` whose one clause is a tuple pattern and whose body is
  # exactly a variable bound by that pattern is an irrefutable field projection —
  # e.g. the dictionary-method extraction the typeclass elaborator emits
  # (`case Dict of {Comparable, Compare} -> Compare end`). Lowered as a `case`, the
  # bound variable is "exported" from the case, and when that case sits inside an
  # operator subexpression (`compare(x, y) == LessThan`, from `min`/`max`/`clamp`)
  # `erl_lint` raises `export_var_subexpr`. Emit `erlang:element(Idx, Scrut)`
  # instead: a pure call that binds nothing — same value, no warning, no needless
  # case. Semantics-preserving because the match is irrefutable (single, total
  # clause over a well-typed value).
  defp irrefutable_projection(scrut_form, [
         {:clause, _, [{:tuple, _, elems}], [], [{:var, _, v}]}
       ]) do
    case Enum.find_index(elems, &match?({:var, _, ^v}, &1)) do
      nil ->
        nil

      idx ->
        {:call, @line, {:remote, @line, {:atom, @line, :erlang}, {:atom, @line, :element}},
         [{:integer, @line, idx + 1}, scrut_form]}
    end
  end

  defp irrefutable_projection(_scrut_form, _clauses), do: nil

  # An emit-generated binder (lambda param `Fn<n>` / let binder `L<n>`) that never
  # appears in its lowered body — e.g. a catch-all `match` branch whose join-point
  # ignores the scrutinee — must be spelled `_Fn<n>` so `erl_lint` does not flag it
  # as an unused variable (which the stdlib gate treats as a failure). Renaming is
  # sound precisely because the var is absent from the body: no reference to rewrite.
  defp unused_underscore(var, body_form) do
    if var_in_form?(body_form, var), do: var, else: :"_#{var}"
  end

  defp var_in_form?({:var, _, v}, v), do: true
  defp var_in_form?(t, v) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&var_in_form?(&1, v))
  defp var_in_form?(l, v) when is_list(l), do: Enum.any?(l, &var_in_form?(&1, v))
  defp var_in_form?(_, _), do: false

  # Builtin-op global spines (K2 spec 2026-07-09 §1.5 + A1 §1-A), keyed via the
  # def-record registry (`Env.builtin_op/2`) — a user def named int_add carries
  # no marker and takes the ordinary global path. Saturated → the SAME BEAM
  # operator as the retired prim lowering (struct ops DROP the type argument).
  # Partial (0 < n < arity) must NOT reach `lower_app_spine`'s generic global
  # branch (present_arity reads nil quantities as 0 and would emit a call to a
  # nonexistent `int_add()`): route as wrapper + curried applications, same as
  # the closure branch. The function-value ABI is curried 1-arg funs (lambdas
  # lower so; closures apply one arg at a time), so wrappers nest 1-arg funs.
  defp builtin_op_form({:global, g}, args, env, ctx) do
    case Env.builtin_op(env, g) do
      nil -> :no
      op -> {:ok, lower_builtin_op(op, args, env, ctx)}
    end
  end

  defp builtin_op_form(_head, _args, _env, _ctx), do: :no

  defp lower_builtin_op(op, args, env, ctx) when op in [:struct_eq, :struct_ne] do
    # The type argument is erased, so a saturated call reaches emit as the two
    # value operands `[l, r]`; the `[_ty, l, r]` form is kept only for a term that
    # bypassed erasure (defensive). Anything else is a partial application.
    erl = if op == :struct_eq, do: :==, else: :"/="

    case args do
      [l, r] -> {:op, @line, erl, lower(env, l, ctx), lower(env, r, ctx)}
      [_ty, l, r] -> {:op, @line, erl, lower(env, l, ctx), lower(env, r, ctx)}
      _ -> curry_apply(builtin_op_wrapper(op), args, env, ctx)
    end
  end

  defp lower_builtin_op(:neg, args, env, ctx) do
    case args do
      [a] -> {:op, @line, :-, lower(env, a, ctx)}
      _ -> curry_apply(builtin_op_wrapper(:neg), args, env, ctx)
    end
  end

  defp lower_builtin_op(:bnot, args, env, ctx) do
    case args do
      [a] -> {:op, @line, :bnot, lower(env, a, ctx)}
      _ -> curry_apply(builtin_op_wrapper(:bnot), args, env, ctx)
    end
  end

  # `Effect(T)` is direct-style, so `run` has no runtime wrapper. The erased
  # type argument is already absent here.
  defp lower_builtin_op(:effect_run, [value], env, ctx), do: lower(env, value, ctx)
  defp lower_builtin_op(:effect_run, args, env, ctx), do: curry_apply(builtin_op_wrapper(:effect_run), args, env, ctx)

  defp lower_builtin_op(op, args, env, ctx) do
    case args do
      [a, b] -> {:op, @line, erl_binop(op), lower(env, a, ctx), lower(env, b, ctx)}
      _ -> curry_apply(builtin_op_wrapper(op), args, env, ctx)
    end
  end

  defp curry_apply(base, args, env, ctx),
    do: Enum.reduce(args, base, fn arg, acc -> {:call, @line, acc, [lower(env, arg, ctx)]} end)

  # A first-class/partial builtin-op use: a local curried fun computing the op.
  # Param names use a dedicated prefix (ctx vars are V<pos>/Fn<n>/_e<pos>), so
  # no shadowing. The struct wrapper takes the two value operands — the erased
  # type argument is dropped before emit, so it never reaches the wrapper.
  defp builtin_op_wrapper(op) when op in [:struct_eq, :struct_ne] do
    erl = if op == :struct_eq, do: :==, else: :"/="
    body = {:op, @line, erl, {:var, @line, :BopL}, {:var, @line, :BopR}}

    fun1(:BopL, fun1(:BopR, body))
  end

  defp builtin_op_wrapper(:neg),
    do: fun1(:BopA, {:op, @line, :-, {:var, @line, :BopA}})

  defp builtin_op_wrapper(:bnot),
    do: fun1(:BopA, {:op, @line, :bnot, {:var, @line, :BopA}})

  defp builtin_op_wrapper(:effect_run),
    do: fun1(:BopA, {:var, @line, :BopA})

  defp builtin_op_wrapper(op) do
    body = {:op, @line, erl_binop(op), {:var, @line, :BopL}, {:var, @line, :BopR}}
    fun1(:BopL, fun1(:BopR, body))
  end

  defp fun1(param, body),
    do: {:fun, @line, {:clauses, [{:clause, @line, [{:var, @line, param}], [], [body]}]}}

  # A SATURATED application of a `Std.Bool` connective def inlines to the native
  # BEAM boolean op — byte-for-byte the retired primitive's codegen (strict
  # `:and`/`:or`/`:not`; `:==`/`:"/="` for Bool equality) — and a saturated
  # Sigma projection `sigma_first(p)`/`sigma_second(p)` (a single-argument
  # spine after implicit erasure) inlines to `element(1|2, P)`, keeping
  # `.1`/`.2` zero-cost on the bare-2-tuple ABI (spec §1.5 / §2.3). An
  # UNSATURATED use (wrong arg count, or the bare global passed as a value)
  # returns `:no` and falls through to an ordinary call/reference. Recognised
  # via the `inline_hint` marker on the def RECORD (set only by the
  # `Std.Bool`/`Std.Sigma` import path), never by bare global atom — a user
  # def shadowing `eq`/`sigma_first`/… carries no marker and is never inlined
  # (R1 discipline, same as the builtin-op registry).
  defp connective_inline({:global, name}, args, env, ctx) do
    case Env.inline_hint(env, name) do
      nil -> :no
      hint -> inline_hint_form(hint, args, env, ctx)
    end
  end

  defp connective_inline(_head, _args, _env, _ctx), do: :no

  defp inline_hint_form(hint, [a, b], env, ctx) when hint in [:and, :or, :eq, :ne],
    do: {:ok, {:op, @line, connective_binop(hint), lower(env, a, ctx), lower(env, b, ctx)}}

  defp inline_hint_form(:not, [a], env, ctx),
    do: {:ok, {:op, @line, :not, lower(env, a, ctx)}}

  defp inline_hint_form(:sigma_first, [p], env, ctx),
    do: {:ok, element(1, lower(env, p, ctx))}

  defp inline_hint_form(:sigma_second, [p], env, ctx),
    do: {:ok, element(2, lower(env, p, ctx))}

  # Flat-telescope positional projections `tproj_i(p)` inline to `element(i, P)`
  # — the i-th slot of the flat BEAM tuple. The final `[p]` spine (one explicit
  # argument after the erased type/tail implicits) is what reaches here.
  defp inline_hint_form(:tproj2, [p], env, ctx), do: {:ok, element(2, lower(env, p, ctx))}
  defp inline_hint_form(:tproj3, [p], env, ctx), do: {:ok, element(3, lower(env, p, ctx))}
  defp inline_hint_form(:tproj4, [p], env, ctx), do: {:ok, element(4, lower(env, p, ctx))}
  defp inline_hint_form(:tproj5, [p], env, ctx), do: {:ok, element(5, lower(env, p, ctx))}
  defp inline_hint_form(:tproj6, [p], env, ctx), do: {:ok, element(6, lower(env, p, ctx))}
  defp inline_hint_form(:tproj7, [p], env, ctx), do: {:ok, element(7, lower(env, p, ctx))}
  defp inline_hint_form(:tproj8, [p], env, ctx), do: {:ok, element(8, lower(env, p, ctx))}

  defp inline_hint_form(_hint, _args, _env, _ctx), do: :no

  defp connective_binop(:and), do: :and
  defp connective_binop(:or), do: :or
  defp connective_binop(:eq), do: :==
  defp connective_binop(:ne), do: :"/="

  defp lower_app_spine(env, head, args, ctx) do
    case head do
      # A named function takes its declared arity in one BEAM call; any further
      # arguments apply (curried) to the function it returns — `mk()(z)`.
      {:global, name} ->
        arity = present_arity(env, name)

        callee =
          case remote_target(name) do
            :local -> {:atom, @line, emitted_name(name)}
            {mod, fun} -> {:remote, @line, {:atom, @line, mod}, {:atom, @line, fun}}
          end

        if length(args) < arity do
          # UNDER-saturated (partial application): the value has a function type, so eta-expand
          # the missing explicit parameters into the curried 1-arg-fun ABI — `add(Z)` at arity 2
          # becomes `fun(V) -> add(Z, V) end`. Without this, `Enum.split` would emit a call at
          # the SUPPLIED arity (`add/1`), which does not exist (E4). The kernel already typed the
          # partial application (currying); this only lowers it faithfully.
          eta = for _ <- 1..(arity - length(args)), do: fresh_var("Pa")
          supplied = Enum.map(args, &lower(env, &1, ctx))
          saturated = {:call, @line, callee, supplied ++ Enum.map(eta, &{:var, @line, &1})}

          Enum.reduce(Enum.reverse(eta), saturated, fn v, body ->
            {:fun, @line, {:clauses, [{:clause, @line, [{:var, @line, v}], [], [body]}]}}
          end)
        else
          {direct, extra} = Enum.split(args, arity)
          base = {:call, @line, callee, Enum.map(direct, &lower(env, &1, ctx))}
          Enum.reduce(extra, base, fn arg, acc -> {:call, @line, acc, [lower(env, arg, ctx)]} end)
        end

      # Applying a closure value (a lambda or a function-typed binder) is curried:
      # apply one argument at a time to the BEAM fun.
      _ ->
        Enum.reduce(args, lower(env, head, ctx), fn arg, acc ->
          {:call, @line, acc, [lower(env, arg, ctx)]}
        end)
    end
  end

  # Core functions are curried, and first-class lambdas lower to nested unary
  # BEAM closures. A named N-ary definition used as a value must obey that same
  # ABI: `add` becomes `fn(a) -> fn(b) -> add(a, b) end end`, not `fun add/2`.
  # Direct named calls remain native N-ary calls in `lower_app_spine/4`; only the
  # first-class value representation is wrapped.
  defp curried_global_wrapper(callee, arity) when arity > 0 do
    vars = for _ <- 1..arity, do: fresh_var("Gf")
    call = {:call, @line, callee, Enum.map(vars, &{:var, @line, &1})}

    Enum.reduce(Enum.reverse(vars), call, fn var, body ->
      {:fun, @line, {:clauses, [{:clause, @line, [{:var, @line, var}], [], [body]}]}}
    end)
  end

  defp present_arity(env, name) do
    case Map.get(env.defs, name) do
      %{quantities: qs} when is_list(qs) -> Enum.count(qs, &Grade.present?/1)
      _ -> 0
    end
  end

  defp erl_binop(:add), do: :+
  defp erl_binop(:sub), do: :-
  defp erl_binop(:mul), do: :*
  # `div` is Erlang INTEGER division; `/` is float division. `Builtins` gives
  # float_div the distinct op key `:fdiv` precisely so this mapping can tell them
  # apart — do not collapse them.
  defp erl_binop(:div), do: :div
  defp erl_binop(:fdiv), do: :/
  defp erl_binop(:rem), do: :rem
  defp erl_binop(:band), do: :band
  defp erl_binop(:bor), do: :bor
  defp erl_binop(:bxor), do: :bxor
  defp erl_binop(:bsl), do: :bsl
  defp erl_binop(:bsr), do: :bsr
  defp erl_binop(:eq), do: :==
  defp erl_binop(:ne), do: :"/="
  defp erl_binop(:lt), do: :<
  defp erl_binop(:le), do: :"=<"
  defp erl_binop(:gt), do: :>
  defp erl_binop(:ge), do: :>=
  defp erl_binop(:and), do: :and
  defp erl_binop(:or), do: :or

  defp element(n, tuple_form) do
    {:call, @line, {:atom, @line, :element}, [{:integer, @line, n}, tuple_form]}
  end

  # Classify a Core term as a UNIT-TERMINATED Σ-telescope spine, returning its car
  # list `[e1, …, en]` (the flat components, `unit` dropped) — or `:not_telescope`
  # for a bare `Sigma(x:T,U)` pair (whose tail is an ordinary value, not `unit`).
  # This is the emit-time reader of the `unit` marker: it decides flat-vs-nested for
  # BOTH values (here) and telescope patterns (`telescope_pattern_cars/2`).
  defp telescope_cars(_env, {:ctor, name, []}) when is_atom(name) do
    if base_name(name) == :unit, do: {:telescope, []}, else: :not_telescope
  end

  defp telescope_cars(env, {:ctor, name, [car, cdr]}) do
    if sigma_ctor?(env, name) do
      case telescope_cars(env, cdr) do
        {:telescope, rest} -> {:telescope, [car | rest]}
        :not_telescope -> :not_telescope
      end
    else
      :not_telescope
    end
  end

  defp telescope_cars(_env, _other), do: :not_telescope

  defp spine({:app, f, x}, acc), do: spine(f, [x | acc])
  defp spine(head, acc), do: {head, acc}

  # A dependent-`case` branch. The scrutinee at runtime is the *erased* value, so
  # the pattern binds only present fields; the body's de Bruijn frame still counts
  # every field (index 0 = last field), so erased fields keep a (dead) context slot.
  defp branch_clause(env, {cname, arity, body}, ctx) do
    cond do
      nat_ctor?(env, cname) -> nat_branch_clause(env, {cname, arity, body}, ctx)
      int_ctor?(env, cname) -> int_branch_clause(env, {cname, arity, body}, ctx)
      bounded_ctor?(env, cname) -> bounded_branch_clause(env, {cname, arity, body}, ctx)
      sigma_ctor?(env, cname) -> sigma_branch_clause(env, {cname, arity, body}, ctx)
      list_ctor?(env, cname) -> list_branch_clause(env, {cname, arity, body}, ctx)
      true -> generic_branch_clause(env, {cname, arity, body}, ctx)
    end
  end

  # case-on-Sigma (spec §2.3): `mk_pair(x, y)` matches a bare 2-tuple `{X, Y}` (both
  # fields present), binding both into the de Bruijn frame exactly as the generic
  # tagged form would — but without the leading ctor-name atom, so the value stays
  # the untagged 2-tuple the ABI requires.
  defp sigma_branch_clause(env, {_mk_pair, 2, body}, ctx) do
    vx = fresh_var("V")
    vy = fresh_var("V")
    body_form = lower(env, body, [vy, vx | ctx])
    px = underscore_if_unused({:var, @line, vx}, body_form)
    py = underscore_if_unused({:var, @line, vy}, body_form)
    {:clause, @line, [{:tuple, @line, [px, py]}], [], [body_form]}
  end

  # case-on-List: Nil matches [], Cons(h,t) matches [H|T], binding both fields
  # into the de Bruijn frame exactly as the generic tagged form would (index 0 =
  # last field, so `[tail, head | ctx]`). A nested list pattern is lowered by the
  # elaborator's matrix compiler into a chain of these single-level Cons/Nil
  # branches, so native cons cells select correctly at every level.
  defp list_branch_clause(env, {cname, 0, body}, ctx) do
    if base_name(cname) == :Nil,
      do: {:clause, @line, [{nil, @line}], [], [lower(env, body, ctx)]},
      else: generic_branch_clause(env, {cname, 0, body}, ctx)
  end

  defp list_branch_clause(env, {cname, 2, body}, ctx) do
    if base_name(cname) == :Cons do
      vh = fresh_var("V")
      vt = fresh_var("V")
      body_form = lower(env, body, [vt, vh | ctx])
      ph = underscore_if_unused({:var, @line, vh}, body_form)
      pt = underscore_if_unused({:var, @line, vt}, body_form)
      {:clause, @line, [{:cons, @line, ph, pt}], [], [body_form]}
    else
      generic_branch_clause(env, {cname, 2, body}, ctx)
    end
  end

  # case-on-Nat (spec §2.2): the zero ctor's branch matches literal 0; the succ
  # ctor's branch matches a fresh N with guard `N > 0` (belt-and-braces: a rep
  # bug crashes loudly instead of binding k = -1) and binds the predecessor as
  # the body's first statement — Erlang patterns/guards cannot compute-and-bind,
  # so `K = N - 1` must open the body, making it a two-form list. The body's
  # de Bruijn frame still counts the field (index 0 = predecessor), exactly as
  # the tuple form would have bound it.
  defp nat_branch_clause(env, {_zero, 0, body}, ctx) do
    {:clause, @line, [{:integer, @line, 0}], [], [lower(env, body, ctx)]}
  end

  defp nat_branch_clause(env, {_succ, 1, body}, ctx) do
    k = fresh_var("V")
    n = fresh_var("N")
    body_form = lower(env, body, [k | ctx])
    k_var = underscore_if_unused({:var, @line, k}, body_form)
    bind = {:match, @line, k_var, {:op, @line, :-, {:var, @line, n}, {:integer, @line, 1}}}
    guard = [[{:op, @line, :>, {:var, @line, n}, {:integer, @line, 0}}]]
    {:clause, @line, [{:var, @line, n}], guard, [bind, body_form]}
  end

  # case-on-Int (spec 2026-07-18-inductive-int §3.4): the runtime scrutinee is a
  # native BEAM integer. FromNat(n) matches any N with guard `N >= 0`, binding the
  # field n = N (identity — no `-1`, unlike Nat's S). NegativeSuccessor(n) matches
  # any N with guard `N < 0`, binding the field n = -N - 1 (since
  # NegativeSuccessor(n) = -(n + 1)). Both ctors are 1-ary, so dispatch is by
  # constructor NAME + sign guard, not arity. Erlang patterns/guards cannot
  # compute-and-bind, so the field binding opens the body as its first form; the
  # body's de Bruijn frame counts the single field (index 0), exactly as the tuple
  # form would have. The guards are mutually exclusive and exhaustive over ℤ, so
  # clause order follows source-arm order.
  defp int_branch_clause(env, {name, 1, body}, ctx) do
    n = fresh_var("N")
    field = fresh_var("V")
    body_form = lower(env, body, [field | ctx])
    field_pat = underscore_if_unused({:var, @line, field}, body_form)

    {guard_cmp, field_expr} =
      case base_name(name) do
        :FromNat ->
          {:>=, {:var, @line, n}}

        :NegativeSuccessor ->
          # field = -N - 1 = 0 - N - 1
          {:<, {:op, @line, :-, {:op, @line, :-, {:integer, @line, 0}, {:var, @line, n}}, {:integer, @line, 1}}}
      end

    guard = [[{:op, @line, guard_cmp, {:var, @line, n}, {:integer, @line, 0}}]]
    bind = {:match, @line, field_pat, field_expr}
    {:clause, @line, [{:var, @line, n}], guard, [bind, body_form]}
  end

  # case-on-Bounded: erases to native integers like Nat (`First`≙`Z`,
  # `Next`≙`S`), but — unlike Nat — Bounded is an INDEXED family: each ctor also
  # binds an erased implicit index `{m : Nat}`, so the Core branch arity is 1
  # (First: {m}) / 2 (Next: {m}, pred), not 0 / 1. The erased binders keep a dead
  # de Bruijn slot but are never matched at runtime; the single PRESENT field
  # (Next's predecessor) is the one that carries data. So: no present field ->
  # `First`, matching literal 0; one present field -> `Next`, matching a fresh N
  # with guard `N > 0` and binding the predecessor `pred = N - 1`.
  defp bounded_branch_clause(env, {name, arity, body}, ctx) do
    quantities = Inductive.ctor_quantities(env, name) || List.duplicate(:unrestricted, arity)
    field_names = for _i <- indices(arity), do: fresh_var("V")
    new_ctx = Enum.reverse(field_names) ++ ctx
    body_form = lower(env, body, new_ctx)

    case Enum.find_index(quantities, &Grade.present?/1) do
      nil ->
        # `First`: only the erased index -> matches literal 0.
        {:clause, @line, [{:integer, @line, 0}], [], [body_form]}

      present_idx ->
        # `Next`: the present field is the predecessor = N - 1.
        n = fresh_var("N")
        pred_name = Enum.at(field_names, present_idx)
        pred_var = underscore_if_unused({:var, @line, pred_name}, body_form)
        bind = {:match, @line, pred_var, {:op, @line, :-, {:var, @line, n}, {:integer, @line, 1}}}
        guard = [[{:op, @line, :>, {:var, @line, n}, {:integer, @line, 0}}]]
        {:clause, @line, [{:var, @line, n}], guard, [bind, body_form]}
    end
  end

  defp generic_branch_clause(env, {cname, arity, body}, ctx) do
    quantities = Inductive.ctor_quantities(env, cname) || List.duplicate(:unrestricted, arity)

    fields =
      for i <- indices(arity) do
        q = Enum.at(quantities, i, :unrestricted)

        if Grade.present?(q),
          do: {:present, fresh_var("V")},
          else: {:erased, fresh_var("_f")}
      end

    field_names = Enum.map(fields, fn {_q, n} -> n end)
    new_ctx = Enum.reverse(field_names) ++ ctx
    body_form = lower(env, body, new_ctx)

    present =
      for {:present, n} <- fields,
          do: underscore_if_unused({:var, @line, n}, body_form)

    pattern =
      case present do
        [] -> {:atom, @line, otp_tag(bool_atom_or_self(env, cname))}
        _ -> {:tuple, @line, [{:atom, @line, otp_tag(cname)} | present]}
      end

    {:clause, @line, [pattern], [], [body_form]}
  end

  # A synthetic BEAM variable name, unique across one emitted module (not just
  # within one lexical nesting chain). Binder names used to be derived
  # from `length(ctx)` (de-Bruijn context depth): sound along a single ancestor
  # chain, but two SIBLING subterms lowered from the same `ctx` (e.g. independent
  # arguments to a ctor/call, or independent elements of a list literal) could
  # legitimately reach the same depth and so mint the *same* name for two
  # unrelated binders. Erlang's `expr_list`/pattern-list hygiene checks then
  # either warn (`match_underscore_var_pat`, sibling case-exports reusing a
  # name) or — worse — silently REBIND: a nested case whose fresh field name
  # happens to equal an already-bound ancestor variable stops introducing a new
  # binding and instead matches against the ancestor's *value*, corrupting the
  # program. A module-scoped monotonic counter sidesteps both: every call reserves
  # one fresh id, so no two synthetic binders in the module can ever collide,
  # siblings or not. Resetting it at `module_forms/5` also makes BEAM output
  # independent of what compiled earlier in the VM. (Each field of a multi-field
  # clause must call this once per field —
  # never derive further names by adding an offset to one reserved id, since
  # that reintroduces the exact same collision class against other reserved ids.)
  #
  # The `_` between prefix and id is load-bearing, not decoration. Positional
  # parameter binders use a SEPARATE scheme — `V<pos>` / `_e<pos>` (see
  # `peel_params/4`, ~line 455), where `<pos>` is a small de Bruijn index — and
  # are NOT minted here. The counter can return a small value like `1`, so a bare
  # `:"V#{1}"` would alias the parameter `V1`. In Erlang an already-bound
  # `V1` in `[V1|V2]` is an equality match, not a fresh bind, corrupting the clause
  # (a non-deterministic `CaseClauseError`). The separator makes the fresh
  # namespace `<prefix>_<digits>` provably disjoint from the positional
  # `<prefix><digits>` shape — no fresh binder can ever spell a positional name.
  defp fresh_var(prefix) do
    id = Process.get(:cure_emit_fresh_counter, 0) + 1
    Process.put(:cure_emit_fresh_counter, id)
    :"#{prefix}_#{id}"
  end

  # `erl_lint` flags a bound-but-unused variable (`unused_var`). An erased proof
  # discards its parameters — an equality proof erases to the runtime-irrelevant
  # `:refl`, so a *present* function parameter or matched ctor field can go
  # unreferenced. Rename such a binder to a `_`-prefixed name: still a real,
  # referenceable variable, but exempt from the warning. Binder names are
  # globally unique (`fresh_var/1`), so a plain occurrence check over the
  # lowered body is a sound "is it used?" test (no shadowing to confuse it).
  defp underscore_if_unused({:var, l, name} = v, body_form) do
    if used_var?(name, body_form), do: v, else: {:var, l, :"_#{name}"}
  end

  defp used_var?(name, {:var, _, name}), do: true

  defp used_var?(name, form) when is_tuple(form),
    do: Enum.any?(Tuple.to_list(form), &used_var?(name, &1))

  defp used_var?(name, form) when is_list(form),
    do: Enum.any?(form, &used_var?(name, &1))

  defp used_var?(_name, _other), do: false

  defp indices(0), do: []
  defp indices(arity), do: Enum.to_list(0..(arity - 1))

  # The canonical Bool inductive erases to native BEAM booleans: its nullary
  # constructors `True`/`False` lower to the atoms `true`/`false` (matching what
  # `{:prim}` comparisons already return at runtime), and a `:case` on Bool tests
  # those same lowercase atoms.
  defp bool_ctor?(env, name), do: Inductive.builtin(env, :bool) == Inductive.ctor_family(env, name)

  # The canonical Std.Nat family (registry-keyed, nominal): its values are BEAM
  # machine integers (spec 2026-07-08-nat-int-erasure). A locally-redeclared
  # structural twin has a different family-id and keeps tuples.
  defp nat_ctor?(env, name) do
    fam = Inductive.builtin(env, :nat)
    fam != nil and Inductive.ctor_family(env, name) == fam
  end

  # The canonical Std.Int family (registry-keyed, nominal): its values are native
  # BEAM machine integers (spec 2026-07-18-inductive-int). Both constructors are
  # 1-ary, so — unlike Nat's Z/S — the erasure MUST key off the constructor NAME:
  #   FromNat(n)           -> n            (identity, no +1)
  #   NegativeSuccessor(n) -> -(n + 1)
  # A locally-redeclared structural twin has a different family-id and keeps tuples.
  defp int_ctor?(env, name) do
    fam = Inductive.builtin(env, :int)
    fam != nil and Inductive.ctor_family(env, name) == fam
  end

  # The canonical Std.Bounded family (registry-keyed, nominal): its `First`/`Next`
  # values erase to native BEAM integers (Fin-as-int), like Nat's Z/S.
  defp bounded_ctor?(env, name) do
    fam = Inductive.builtin(env, :bounded)
    fam != nil and Inductive.ctor_family(env, name) == fam
  end

  # Keep only the runtime-present args of a Bounded ctor app, dropping the erased
  # implicit index `m`. If erasure already stripped the args (their count matches
  # the present-quantity count) they are already the present ones; otherwise
  # filter the full arg list against the ctor's declared quantities.
  defp bounded_present_args(env, name, args) do
    case Inductive.ctor_quantities(env, name) do
      qs when is_list(qs) and length(qs) == length(args) ->
        for {arg, quantity} <- Enum.zip(args, qs),
            Grade.present?(quantity),
            do: arg

      _ ->
        args
    end
  end

  # The canonical Sigma family (registry-keyed, nominal): its values are the bare
  # BEAM 2-tuples the primitive pair always compiled to (spec 2026-07-09 D2 §1.5) —
  # Std.Pair's element/2 interop and AtomVM depend on the untagged shape.
  defp sigma_ctor?(env, name) do
    fam = Inductive.builtin(env, :sigma)
    fam != nil and Inductive.ctor_family(env, name) == fam
  end

  # The canonical Std.List family (registry-keyed, nominal): its values are native
  # BEAM lists — Nil is [], Cons(h,t) is [H|T] — so Erlang/AtomVM list NIFs interop.
  defp list_ctor?(env, name) do
    fam = Inductive.builtin(env, :list)
    fam != nil and Inductive.ctor_family(env, name) == fam
  end

  defp bool_atom(name) do
    case base_name(name) do
      :True -> true
      :False -> false
      other -> other
    end
  end

  defp bool_atom_or_self(env, name) do
    if bool_ctor?(env, name), do: bool_atom(name), else: name
  end

  # The OTP-conventional constructors erase to their lowercase BEAM atoms so a
  # Cure `Result`/`Option` value is a native `{:ok, _}` / `{:error, _}` /
  # `{:some, _}` / `:none` term — the shape Erlang, Elixir, and (critically)
  # AtomVM FFI expect. `lib/std/core.cure` documents exactly this representation
  # (`Ok(value) -> {:ok, value}`, `None() -> :none`). Applied at BOTH the
  # construction and the pattern site so the tags agree. Every other constructor
  # keeps its declared (PascalCase) tag; records stay tagged tuples `{:Point,…}`.
  defp otp_tag(name) do
    case base_name(name) do
      :Ok -> :ok
      :Error -> :error
      :Some -> :some
      :None -> :none
      other -> other
    end
  end

  defp base_name(name), do: name |> Cure.Elab.Name.base() |> String.to_atom()
end
