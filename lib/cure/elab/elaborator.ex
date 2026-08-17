defmodule Cure.Elab.Elaborator do
  @moduledoc """
  Elaborate the surface expression fragment into explicit `Cure.Core` terms
  (design spec §5; mirrors Idris `TTImp/Elab/Check.idr`).

  Untrusted: it resolves names to de Bruijn indices and builds Core terms that
  the kernel then re-checks. This task covers the basic fragment — `Type`,
  function definitions (→ λ / Π), variables, and application. Implicit inference
  (M8.2), erasure marking (M8.3), and dependent pattern compilation (M8.4) build
  on it.

  A *scope* is the list of in-scope binder names, most-recently-bound first, so a
  name resolves to its de Bruijn index by position.
  """

  alias Cure.Core.{Context, Conv, Env, Eval, Grade, Inductive, Kernel, Normalise, Quote, Term}
  alias Cure.Elab.{AttemptCache, CallAttemptProfile, GuardLint, MetaCtx, Rewrite, Subst, Unify}
  alias Cure.Elab.Subst.{Frame, Prefix}

  import Cure.Elab.Rewrite,
    only: [
      abstract_term: 3,
      contains_term_scoped?: 2,
      mk_eq: 3,
      mk_refl: 1,
      replace_term: 3,
      replace_term_scoped: 3,
      transport_case: 4
    ]

  # Placeholder body for a `:case` branch the join point will fill (see
  # `join_point?/5`, `elaborate_join/6`, `wrap_join/2`). Never reaches the kernel:
  # `wrap_join/2` replaces every marker before the term escapes `elaborate_match`.
  @join_marker :"$join_point"

  # Internal request used by motive-generalized matches when an authored
  # `Ctor(...) -> impossible` branch is reachable by the outer scrutinee but its
  # refined dependent context contains an uninhabited indexed value. It is
  # consumed before expression elaboration and never reaches Core.
  @contextual_impossible_body {:__cure_contextual_impossible__, [], []}

  # A blocked field without discoverable metavariable dependencies gets a
  # bounded conservative retry queue rather than a catch-all sweep.
  @constructor_fallback_retry_limit 8

  @doc """
  Elaborate a top-level function definition into `{:ok, core_lambda, type_value}`
  — the λ over the parameters and the Π type it inhabits.
  """
  @spec elaborate(tuple(), Env.t()) :: {:ok, Cure.Core.Term.t(), Cure.Core.Value.t()} | {:error, term()}
  def elaborate({:function_def, meta, body}, env) do
    params = Keyword.get(meta, :params, [])
    return_expr = Keyword.fetch!(meta, :return_type)

    with {:ok, param_tele} <- elaborate_params(params, [], env),
         scope = param_tele |> Enum.map(&elem(&1, 0)) |> Enum.reverse(),
         {:ok, body_core} <- elaborate_expr(single_body(body), scope, env),
         {:ok, return_core} <- elaborate_type(return_expr, scope, env) do
      lambda = wrap(:lam, param_tele, body_core)
      pi = wrap(:pi, param_tele, return_core)
      {:ok, lambda, Eval.eval(pi, [])}
    end
  end

  def elaborate(other, _env), do: {:error, {:unsupported_expression, other}}

  # Desugar record construction `Point{x: .., y: ..}` (a `record: true` call whose
  # arguments are `field: value` pairs) into the positional constructor application
  # `Point(.., ..)`, ordering the values by the record constructor's field telescope
  # (the constructor's argument names ARE the field names). Missing or extra fields
  # are rejected.
  defp desugar_record_construction(meta, field_pairs, env) do
    name = Keyword.fetch!(meta, :name)
    atom = String.to_atom(name)

    case Inductive.get_ctor(env, atom) do
      nil ->
        {:error, {:unknown_record, atom}}

      ctor ->
        with :ok <- reject_duplicate_record_fields(field_pairs, atom, :construction) do
          order = Enum.map(ctor.args, fn {n, _t} -> n end)
          defaults = Map.get(ctor, :field_defaults, %{})
          provided = Map.new(field_pairs, fn {:pair, _m, [{:literal, _s, f}, val]} -> {f, val} end)

          cond do
            # A named field is not a field of this record.
            not Enum.all?(Map.keys(provided), &(&1 in order)) ->
              {:error, record_field_mismatch(atom, order, defaults, Map.keys(provided))}

            # Every field must be supplied by the caller or carry a declared default
            # (`name: String = "Anonymous"`); an omitted field with no default is a
            # genuine mismatch.
            not Enum.all?(order, &(Map.has_key?(provided, &1) or Map.has_key?(defaults, &1))) ->
              {:error, record_field_mismatch(atom, order, defaults, Map.keys(provided))}

            true ->
              values =
                Enum.map(order, fn f ->
                  case Map.fetch(provided, f) do
                    {:ok, val} -> val
                    :error -> Map.fetch!(defaults, f)
                  end
                end)

              {:ok, {:function_call, [name: name], values}}
          end
        end
    end
  end

  # Desugar record update `Point{base | x: .., …}` into the positional constructor
  # `Point(.., ..)`: each overridden field takes its new value, every other field is
  # projected from the base (`base.field`), reusing construction and projection. An
  # override that names a non-field is rejected.
  defp desugar_record_update(meta, [base | field_pairs], env) do
    name = Keyword.fetch!(meta, :name)
    atom = String.to_atom(name)

    case Inductive.get_ctor(env, atom) do
      nil ->
        {:error, {:unknown_record, atom}}

      ctor ->
        with :ok <- reject_duplicate_record_fields(field_pairs, atom, :update) do
          order = Enum.map(ctor.args, fn {n, _t} -> n end)
          overrides = Map.new(field_pairs, fn {:pair, _m, [{:literal, _s, f}, val]} -> {f, val} end)

          if Enum.all?(Map.keys(overrides), &(&1 in order)) do
            values =
              Enum.map(order, fn f ->
                case Map.fetch(overrides, f) do
                  {:ok, val} -> val
                  :error -> {:attribute_access, [attribute: Atom.to_string(f)], [base]}
                end
              end)

            {:ok, {:function_call, [name: name], values}}
          else
            {:error, record_field_mismatch(atom, order, Map.new(order, &{&1, :from_base}), Map.keys(overrides))}
          end
        end
    end
  end

  defp record_field_mismatch(record, declared, defaults, provided) do
    %{
      record: record,
      declared: declared,
      provided: provided,
      unknown: Enum.reject(provided, &(&1 in declared)),
      missing: Enum.reject(declared, &(Enum.member?(provided, &1) or Map.has_key?(defaults, &1)))
    }
    |> then(&{:record_field_mismatch, &1})
  end

  defp reject_duplicate_record_fields(field_pairs, record, operation) do
    occurrences =
      Enum.map(field_pairs, fn {:pair, meta, [{:literal, _symbol_meta, field}, _value]} ->
        source_info = Cure.MetaAST.Metadata.source_info(meta)
        {field, source_info && source_info.name}
      end)

    case Enum.find(occurrences, fn {field, _span} -> Enum.count(occurrences, &(elem(&1, 0) == field)) > 1 end) do
      nil ->
        :ok

      {duplicate, _span} ->
        spans = for {^duplicate, %Cure.Diagnostic.Span{} = span} <- occurrences, do: span

        {:error, {:duplicate_field, %{name: duplicate, record: record, operation: operation, spans: spans}}}
    end
  end

  defp validate_record_update_base(meta, [base | _fields], names, ctx, env) do
    record = meta |> Keyword.fetch!(:name) |> String.to_atom()
    expected = Inductive.ctor_family(env, record)

    with {:ok, _term, type} <- elaborate_expr_typed(base, names, ctx, env) do
      actual = Quote.reify(type, Context.length(ctx))

      case actual do
        {:data, ^expected, _parameters, _indices} ->
          :ok

        {:data, actual_record, _parameters, _indices} ->
          {:error, {:record_update_base_mismatch, %{record: expected || record, actual: actual_record}}}

        other ->
          {:error, {:record_update_base_mismatch, %{record: expected || record, actual: other}}}
      end
    end
  end

  defp available_record_names(%Env{} = env) do
    env.ctors
    |> Map.keys()
    |> Enum.filter(&(Map.get(env.ctor_to_family, &1) == &1))
    |> Enum.sort_by(&Atom.to_string/1)
  end

  # Normalize a constructor atom to a registry key via the resolution layer:
  # a flattened dotted path (`:"Std.Nat.Z"`) via qualified resolution; a bare atom
  # that is absent from the registry but present under exactly one re-keyed
  # `:"Mod#Z"` variant (a shadowed-but-present import, spec §3.3) to that variant.
  # A bare atom still present under its bare key (local winner / unshadowed import)
  # is returned unchanged — so a redeclared ctor keeps winning (R1).
  defp resolve_ctor_key(env, cname) do
    s = Atom.to_string(cname)

    cond do
      String.contains?(s, ".") ->
        case Cure.Elab.Resolution.resolve_qualified(env, s, :value) do
          {:ok, key} -> key
          :error -> cname
        end

      Inductive.get_ctor(env, cname) != nil ->
        Env.resolve_key(env, env.ctors, cname)

      true ->
        case Cure.Elab.Resolution.resolve_bare(env, cname) do
          {:ok, key} -> key
          _ -> cname
        end
    end
  end

  # Rewrite a constructor pattern's surface `:name` to the resolved registry key
  # so downstream re-derivation (`constructor_pattern/1` in `elaborate_matched_branch`
  # / `elaborate_rematch_branch`) yields the resolved atom, not the stale dotted
  # one. Only ever called on a `constructor_pattern`-validated arm, which is always
  # a `{:function_call, …}` node (bare nullary ctors included, with empty args).
  defp rekey_pattern_name({:function_call, pmeta, pargs}, cname),
    do: {:function_call, Keyword.put(pmeta, :name, Atom.to_string(cname)), pargs}

  # A constructor pattern whose (resolved) ctor belongs to a different family than
  # the scrutinee. If the ORIGINAL bare name was shadowed off the registry (now
  # only reachable as a re-keyed `:"Mod#name"` variant, which uniform resolution
  # just bound `cname` to), report the targeted R5 `:shadowed_ctor` with a
  # qualified-escape-hatch hint; otherwise it is a genuine cross-family
  # `:foreign_ctor`.
  #
  # "Shadowed off the registry" is not the same question as "reached through an
  # import": the latter is true of every imported constructor, so asking it alone
  # reported an ordinary wrong-family pattern as shadowing and hinted at a
  # qualified spelling that does not type-check either. The R5 story needs BOTH —
  # the bare name resolves only through an import, AND the local family the
  # pattern is checked against carries the same bare name as the constructor's
  # own family. That name collision is what pushed the imported constructors out
  # of bare reach, and is what makes `Mod.Ctor` the fix.
  defp shadowed_or_foreign_ctor(env, sig, cname0, cname, dname) do
    case shadowed_ctor_origin(env, sig, cname, dname, cname0) do
      {:ok, mod_id} ->
        {:error,
         {:shadowed_ctor,
          [
            ctor: cname0,
            shadowed_module: mod_id,
            local_family: dname,
            local_ctors: Enum.map(Inductive.ctors_of(sig, dname), & &1.name),
            hint: mod_id <> "." <> Atom.to_string(cname0)
          ]}}

      :error ->
        {:error,
         {:source_context, {:foreign_ctor, cname},
          %{
            constructor: cname,
            actual_family: Inductive.ctor_family(sig, cname),
            expected_family: dname,
            expected_constructors: Enum.map(Inductive.ctors_of(sig, dname), & &1.name),
            expectation_origin: :pattern_constructor,
            expression_category: :constructor_pattern
          }}}
    end
  end

  # The module whose type name the scrutinee's family shadows, when that is why
  # `cname0` could not be written bare. `nil` bare names (a family with no owner,
  # or a ctor the signature does not know) never count as a collision.
  defp shadowed_ctor_origin(env, sig, cname, dname, cname0) do
    with {:ok, mod_id, _key} <- Cure.Elab.Resolution.shadowed_origin(env, cname0),
         ctor_family when not is_nil(ctor_family) <- Inductive.ctor_family(sig, cname),
         local_base when not is_nil(local_base) <- Cure.Elab.Name.base(dname),
         ^local_base <- Cure.Elab.Name.base(ctor_family) do
      {:ok, mod_id}
    else
      _ -> :error
    end
  end

  # In a Type-returning expression body the parser represents `Tuple(A, B)` as
  # an ordinary call rather than the annotation-only `:tuple_type` node. Lower
  # it through the canonical tuple-type path and synthesize `Type`, just as we
  # already do for first-class primitive and inductive types.
  defp elaborate_named_call([{:name, "Tuple"} | _], args, names, ctx, env) do
    tuple_ast =
      {:tuple_type, [arity: length(args), binders: List.duplicate("_", length(args))], args}

    with {:ok, term} <- elaborate_type(tuple_ast, names, env),
         {:ok, type} <- Kernel.infer(ctx, term) do
      {:ok, term, type}
    end
  end

  defp elaborate_named_call(meta, args, names, ctx, env) do
    elaborate_named_call_regular(meta, args, names, ctx, env)
  end

  defp elaborate_named_call_regular(meta, args, names, ctx, env) do
    profile_named_call(meta, :inference, env, fn ->
      elaborate_named_call_regular_profiled(meta, args, names, ctx, env)
    end)
  end

  defp elaborate_named_call_regular_profiled(meta, args, names, ctx, env) do
    name = Keyword.fetch!(meta, :name)
    atom = String.to_atom(name)

    resolved =
      cond do
        String.contains?(name, ".") ->
          case Cure.Elab.Resolution.resolve_qualified(env, name, :value) do
            {:ok, key} -> key
            :error -> atom
          end

        Inductive.get_ctor(env, atom) != nil ->
          Env.resolve_key(env, env.ctors, atom)

        true ->
          case Cure.Elab.Resolution.resolve_bare(env, atom) do
            {:ok, key} -> key
            _ -> atom
          end
      end

    {meta, args} = normalize_constructor_named_args(meta, args, Inductive.get_ctor(env, resolved))

    # Ph2 label enforcement for a SINGLE call target. An overloaded name (≥2
    # candidates) is handled by the pruner clause below, which tie-breaks on
    # exact label agreement; a lone target instead only enforces its declared
    # labels here (mandatory two-name labels must be written, optional single-name
    # ones are free). Inert for every pre-Ph2 call: a target with no mandatory
    # label called without labels checks `:ok`.
    overloaded? =
      not String.contains?(name, ".") and
        length(Cure.Elab.Resolution.overload_candidates(env, atom)) >= 2

    alignment =
      if overloaded? do
        {:ok, args}
      else
        if ctor = Inductive.get_ctor(env, resolved) do
          align_constructor_args(resolved, ctor, meta, args)
        else
          if Cure.Elab.Resolve.method?(env, atom) do
            descriptor = Cure.Elab.Interface.for_method(env, atom)
            method = Map.fetch!(descriptor.methods, atom)

            labels =
              Enum.map(method.params, fn {:param, parameter_meta, internal} ->
                case Keyword.get(parameter_meta, :label) do
                  nil -> {:optional, to_string(internal)}
                  external -> {:required, to_string(external)}
                end
              end)

            Cure.Elab.Overload.align_labels(atom, labels, args, Keyword.get(meta, :arg_labels), call_label_opts(meta))
          else
            Cure.Elab.Overload.align(
              env,
              resolved,
              args,
              Keyword.get(meta, :arg_labels),
              call_label_opts(meta)
            )
          end
        end
      end

    case alignment do
      {:error, _} = err -> err
      {:ok, aligned_args} -> elaborate_named_call_resolved(meta, name, atom, aligned_args, names, resolved, ctx, env)
    end
  end

  defp normalize_constructor_named_args(meta, args, nil), do: {meta, args}

  defp normalize_constructor_named_args(meta, args, _ctor) do
    converted =
      Enum.map(args, fn
        {:typed_pattern, pattern_meta, [name, value]} ->
          span =
            case Cure.MetaAST.Metadata.source_info(pattern_meta) do
              %Cure.MetaAST.SourceInfo{whole: whole} -> whole
              _ -> nil
            end

          {value, to_string(name), span}

        value ->
          {value, nil, nil}
      end)

    if Enum.any?(converted, fn {_value, label, _span} -> not is_nil(label) end) do
      values = Enum.map(converted, &elem(&1, 0))
      labels = Enum.map(converted, &elem(&1, 1))
      spans = Enum.map(converted, &elem(&1, 2))

      meta = Keyword.put(meta, :arg_labels, labels)

      meta =
        case Cure.MetaAST.Metadata.source_info(meta) do
          %Cure.MetaAST.SourceInfo{} = info ->
            Cure.MetaAST.Metadata.put_source_info(meta, %{info | argument_labels: spans})

          _ ->
            meta
        end

      {meta, values}
    else
      {meta, args}
    end
  end

  defp align_constructor_args(key, ctor, meta, args) do
    labels =
      Enum.zip(ctor.args, Inductive.plicities_of(ctor))
      |> Enum.flat_map(fn
        {{parameter_name, _type}, :explicit} -> [{:optional, to_string(parameter_name)}]
        _ -> []
      end)

    Cure.Elab.Overload.align_labels(key, labels, args, Keyword.get(meta, :arg_labels), call_label_opts(meta))
  end

  defp call_label_opts(meta) do
    info = Cure.MetaAST.Metadata.source_info(meta)

    [
      argument_spans: if(info, do: info.arguments, else: []),
      label_spans: if(info, do: info.argument_labels, else: [])
    ]
  end

  defp profile_named_call(meta, expected_type, env, fun) do
    if CallAttemptProfile.active?() do
      source_info = Cure.MetaAST.Metadata.source_info(meta)

      CallAttemptProfile.with_call(
        %{
          declaration: profile_declaration(env),
          span: if(source_info, do: source_info.whole),
          callee: Keyword.fetch!(meta, :name),
          expected_type: expected_type
        },
        fun
      )
    else
      fun.()
    end
  end

  defp profile_attempt(candidate, strategy, fun),
    do: CallAttemptProfile.attempt(candidate, strategy, fun)

  defp profile_attempt_at(meta, expected_type, env, candidate, strategy, fun) do
    profile_named_call(meta, expected_type, env, fn -> profile_attempt(candidate, strategy, fun) end)
  end

  defp profile_declaration(env) do
    case {Env.current_def(env), Env.owner(env)} do
      {nil, _owner} -> nil
      {name, nil} -> name
      {name, owner} -> if(Cure.Elab.Name.qualified?(name), do: name, else: Cure.Elab.Name.qualify(owner, name))
    end
  end

  defp elaborate_named_call_resolved(meta, name, atom, args, names, resolved, ctx, env) do
    case require_unsafe_call(meta, name, resolved, env) do
      :ok -> elaborate_named_call_resolved_unchecked(meta, name, atom, args, names, resolved, ctx, env)
      {:error, _} = error -> error
    end
  end

  defp elaborate_named_call_resolved_unchecked(meta, name, atom, args, names, resolved, ctx, env) do
    cond do
      # An interface-method call (`eqs(x, y)`) resolves to a concrete instance
      # from the head-positioned argument's type — inlined at a concrete head,
      # projected off the dictionary parameter at a rigid one. Checked before the
      # constructor/global paths so a method name never falls through to an
      # unresolved global.
      Cure.Elab.Resolve.method?(env, atom) ->
        Cure.Elab.Resolve.method_call(env, atom, args, names, ctx)

      # A call to a `where`-constrained global resolves and appends the dictionary
      # the callee expects before the ordinary application machinery runs, so the
      # dictionary parameter is supplied at every concrete call site.
      #
      # The `constrained` index is keyed by BARE spelling, so this fast path must
      # also confirm the bare name still names one definition. When two modules
      # provide it — an ambient `Std.Comparable#max` and an explicitly imported
      # `Std.Math#max` — `resolve_key` reports the spelling unresolved and
      # `Env.get_def` is nil; taking the fast path anyway would hand that
      # unresolvable bare atom to the applicator, which assumes a def. Falling
      # through instead reaches the overload path, where local-then-direct
      # precedence lets the explicit `use` win.
      Cure.Elab.Resolve.constrained?(env, atom) and Env.get_def(env, atom) != nil ->
        Cure.Elab.Resolve.constrained_call(env, atom, args, names, ctx)

      name == "reflexive" and length(args) == 1 ->
        [arg] = args

        # Surface `reflexive(x)` supplies the (erased, forced) witness explicitly;
        # build the inductive ctor `reflexive : {w:a} -> Equivalent(a,w,w)` with `x`
        # in the erased slot (dropped at runtime by erasure). Matching is the
        # ordinary `reflexive()` ctor pattern. Retires the primitive `{:refl, x}`
        # (spec 2026-07-04).
        #
        # A bare data ctor has no inference rule (`:ctor_requires_checking_mode`),
        # so we synthesize reflexive's ONLY possible type — `Equivalent(a, x, x)`
        # over the witness's type/value — and have the kernel `check` the ctor
        # against it (validating that `x` inhabits `a` and the indices unify).
        with {:ok, arg_term, arg_type} <- elaborate_expr_typed(arg, names, ctx, env),
             reflexive = resolve_ctor_key(env, :reflexive),
             equivalent = Inductive.ctor_family(env, reflexive),
             term = {:ctor, reflexive, [arg_term]},
             arg_val = Eval.eval(arg_term, Context.env(ctx)),
             type = {:vdata, equivalent, [arg_type, arg_val, arg_val]},
             :ok <- Kernel.check(ctx, term, type) do
          {:ok, term, type}
        end

      Inductive.get_ctor(env, resolved) ->
        with_constructor_retry_cache(fn ->
          result =
            profile_attempt(resolved, :constructor_infer, fn ->
              with :ok <- validate_constructor_arity(env, resolved, args, name),
                   {:ok, present} <- map_present_args(args, names, ctx, env) do
                elaborate_ctor_app(env, resolved, present, ctx)
              end
            end)

          # A nested underdetermined constructor in *inference* position —
          # `Cons(Z(), Nil())` as a bare argument, whose inner `Nil()` cannot be
          # inferred — fails up-front inference. Retry left-to-right: solve the
          # constructor's parameters from the arguments that do infer (`Z() : Nat`
          # fixes `a`), then *check* the rest (`Nil()` against `Lst(Nat)`). Additive:
          # reached only after inference already failed, original error surfaced
          # otherwise. The retry cache records blocked nested constructors so
          # this second strategy does not elaborate the same surface call again;
          # it waits for the sibling field to make its expected type concrete.
          case result do
            {:ok, _, _} = ok ->
              ok

            {:error, _} = orig ->
              remember_blocked_constructor(resolved, args, orig)

              case profile_attempt(resolved, :constructor_bidirectional, fn ->
                     elaborate_ctor_app_infer_bidirectional(env, resolved, args, names, ctx)
                   end) do
                {:ok, _, _} = ok -> ok
                {:error, _} -> orig
              end
          end
        end)

      # A saturated call to a registered builtin primitive op — `Std.Builtin.int_add`,
      # `struct_eq`, … — spelled by its qualified name. These globals are body-less:
      # the arithmetic/comparison ops carry `quantities: nil`, so the general
      # `elaborate_global_app` path crashes on `length(quantities)`, and `struct_eq`'s
      # leading ERASED type param makes that path auto-solve the type as a metavar
      # instead of consuming the explicitly-passed one (an index mismatch). Emit the
      # raw left-nested app spine directly and let the kernel infer the whole term;
      # `struct_eq`'s type argument sits in an erased slot the kernel accepts by fiat
      # (builtins.ex `seed_struct_ops`). Guarded on the `builtin_op` marker (set only
      # by `Builtins.seed_ops`), so it fires for no user-defined global. Restricted to
      # the QUALIFIED spelling (`name` carries a `.`): a bare `struct_eq(x, y)` still
      # routes through the general path, which auto-solves the leading erased type
      # param as a metavar rather than expecting it as an explicit positional arg.
      # Placed before the general global-application arm, which would otherwise
      # intercept the qualified name.
      String.contains?(name, ".") and
          match?(%{builtin_op: op} when not is_nil(op), Env.get_def(env, resolved)) ->
        with {:ok, arg_terms} <- elaborate_all_args(args, names, ctx, env),
             term = build_app_spine({:global, resolved}, arg_terms),
             {:ok, type} <- Kernel.infer(ctx, term) do
          {:ok, term, type}
        end

      # A QUALIFIED call to a plain (non-ctor) global def: `A.foo(x)`. The
      # qualified branch above mapped the dotted `name` to the def's registry key
      # (`resolved`, bare or re-keyed `Mod#foo`) via `resolve_qualified/3`; without
      # a clause acting on it the call falls through to the catch-all, which
      # re-elaborates from the raw dotted name and can never find a `.`-spelled
      # key. `elaborate_global_app/4` (as the `implicit_def?` clause uses it) reaches
      # both plain and implicit defs. Guarded on the dot so bare def calls keep
      # their existing paths.
      String.contains?(name, ".") and Map.has_key?(env.defs, resolved) ->
        if Enum.any?(args, &(match?({:lambda, _m, _b}, &1) or call_placeholder?(&1))) do
          # A lambda argument needs a checking-mode expected type, so the bidirectional
          # elaborator is the ONLY path here. It used to be run, and then — on failure —
          # run a second time with identical arguments, which can only reproduce the same
          # error. One attempt, one verdict.
          profile_attempt(resolved, :qualified_bidirectional, fn ->
            elaborate_implicit_app_bidirectional(env, resolved, args, names, ctx)
          end)
        else
          result =
            profile_attempt(resolved, :qualified_infer, fn ->
              with {:ok, present} <- map_present_args(args, names, ctx, env) do
                elaborate_global_app(env, resolved, present, ctx)
              end
            end)

          case result do
            {:ok, _, _} = ok ->
              ok

            {:error, _} = orig ->
              # This retry IS load-bearing: the attempt above used a different algorithm
              # (direct application of already-elaborated args), so the bidirectional
              # elaborator can still succeed where it failed — e.g. when an implicit
              # argument only becomes solvable in checking mode.
              case profile_attempt(resolved, :qualified_bidirectional, fn ->
                     elaborate_implicit_app_bidirectional(env, resolved, args, names, ctx)
                   end) do
                {:ok, _, _} = ok -> ok
                {:error, _} -> orig
              end
          end
        end

      # An applied call to a bare overloaded name — a set of ≥2 members sharing
      # one bare spelling: same-module discriminated members, or cross-module
      # providers with no unique winner. `overload_candidates/2` already applies
      # local-then-direct precedence, so a name with a single local/direct winner
      # (a local `map` shadowing imports) collapses to one candidate and never
      # reaches here — only a genuine set of ≥2 does. Align the authored
      # arguments against each candidate, bidirectionally elaborate each aligned
      # call, and dispatch the unique survivor.
      # Placed after the ctor/method/constrained/qualified special cases and
      # before the generic ambiguity/def paths; the `not String.contains?` guard
      # keeps it disjoint from the dotted-qualified clause.
      not String.contains?(name, ".") and
          length(Cure.Elab.Resolution.overload_candidates(env, atom)) >= 2 ->
        cands = Cure.Elab.Resolution.overload_candidates(env, atom)

        case elaborate_overloaded_app(
               env,
               atom,
               args,
               Keyword.get(meta, :arg_labels),
               names,
               ctx,
               cands,
               call_label_opts(meta)
             ) do
          {:error, reason} ->
            {:error, attach_expectation_context(reason, {:function_call, meta, args}, :overload, atom, nil)}

          result ->
            result
        end

      # A bare name provided by ≥2 distinct re-keyed imports with no local/
      # unshadowed winner: unqualified use is ambiguous (R7). Checked before the
      # generic paths so an ambiguous name surfaces `:ambiguous_name`, not a
      # confusing downstream "not found". (`resolved == atom` here: an ambiguous
      # name has no dot and no unique variant.)
      length(Cure.Elab.Resolution.ambiguous_modules(env, atom)) >= 2 ->
        {:error, {:ambiguous_name, atom, Cure.Elab.Resolution.ambiguous_modules(env, atom)}}

      # `_` is meaningful only to the goal-directed application solver: the
      # ordinary scoped path necessarily interprets every variable-shaped AST as
      # a name and reports `:unknown_global` before a later dependent argument can
      # constrain it. Route placeholder-bearing calls directly through the same
      # Π-telescope solver used for implicit and lambda-bearing applications.
      # Local definitions retain the ordinary local-over-import precedence.
      Enum.any?(args, &call_placeholder?/1) and
          (Env.get_def(env, atom) != nil or Env.get_def(env, resolved) != nil) ->
        key = if Env.get_def(env, atom), do: Env.resolve_key(env, env.defs, atom), else: resolved

        profile_attempt(key, :placeholder_bidirectional, fn ->
          elaborate_implicit_app_bidirectional(env, key, args, names, ctx)
        end)

      # A global whose telescope carries erased (implicit) parameters: insert
      # fresh metavariables for them and solve from the present arguments, the
      # same way constructor indices are inferred (§5.2). Without this, the
      # explicit args would be bound to the implicit positions.
      #
      # Key on the raw `atom` whenever it names a LOCAL def (which must shadow any
      # same-named import), otherwise on `resolved`. An IMPORTED implicit def is
      # registered under a re-keyed import key (`Std.List#map`), so
      # `implicit_def?(env, :map)` is false and the raw atom is not a def; without
      # resolving, a bare `map(xs, fn(x) -> ...)` skips implicit insertion, falls to
      # the lambda clause below, and mis-binds `xs : List(Int)` against the erased
      # `{t} : Type` slot (a `:conversion_failure`). Preferring `atom` when it is a
      # local def keeps a module's own `map`/`filter` bound to itself;
      # `resolve_bare` (which feeds `resolved`) resolves toward imports and
      # would otherwise redirect a recursive self-call to a same-named import.
      implicit_def?(env, if(Env.get_def(env, atom), do: atom, else: resolved)) ->
        key = if Env.get_def(env, atom), do: Env.resolve_key(env, env.defs, atom), else: resolved

        result =
          profile_attempt(key, :implicit_infer, fn ->
            with {:ok, present} <- map_present_args(args, names, ctx, env) do
              elaborate_global_app(env, key, present, ctx)
            end
          end)

        # When up-front inference of the arguments fails — an argument that is
        # underdetermined until an implicit parameter is solved (`map(s, Cons(Z(),
        # Nil()))`) — retry with left-to-right bidirectional application. Additive:
        # reached only after the inference path errored, and its own failure
        # surfaces the original error, so a working call is untouched.
        case result do
          {:ok, _, _} = ok ->
            ok

          {:error, _} = orig ->
            case profile_attempt(key, :implicit_bidirectional, fn ->
                   elaborate_implicit_app_bidirectional(env, key, args, names, ctx)
                 end) do
              {:ok, _, _} = ok -> ok
              {:error, _} -> orig
            end
        end

      # A call carrying a lambda argument needs the callee's parameter types to
      # reach the (untyped-in-surface) lambda: elaborate bidirectionally, checking
      # each argument against its Π domain. Restricted to lambda-bearing calls so
      # every other application keeps its exact existing inference path.
      Enum.any?(args, &match?({:lambda, _m, _b}, &1)) ->
        profile_attempt(resolved, :lambda_bidirectional, fn ->
          elaborate_bidirectional_app(name, args, names, ctx, env)
        end)

      true ->
        # Non-constructor application: elaborate to a term, then let the kernel type it.
        result =
          profile_attempt(resolved, :scoped_infer, fn ->
            with {:ok, term} <- elaborate_expr({:function_call, [name: name], args}, names, env),
                 {:ok, type} <- Kernel.infer(ctx, term) do
              {:ok, term, type}
            end
          end)

        # The scoped path binds arguments positionally and does not insert
        # metavariables for a *nested* implicit call, so an argument like
        # `len(mklist())` / `map(s, xs)` — an implicit-parameter call — is
        # mis-bound (`Lst(Nat)` checked against the `{a} : Type` slot). When that
        # fails, retry checking each argument against the callee's Π domain, which
        # elaborates a nested implicit call in checking mode. Additive: reached only
        # after the scoped path errored, original error surfaced otherwise.
        case result do
          {:ok, _, _} = ok ->
            ok

          {:error, _} = orig ->
            case profile_attempt(resolved, :scoped_bidirectional, fn ->
                   elaborate_bidirectional_app(name, args, names, ctx, env)
                 end) do
              {:ok, _, _} = ok ->
                ok

              {:error, retry_reason} ->
                case orig do
                  {:error, :ctor_arity} -> {:error, retry_reason}
                  _ -> orig
                end
            end
        end
    end
  end

  # Saturated application checked argument-by-argument against the callee's Π
  # telescope, so a lambda argument is elaborated in checking mode (its parameter
  # types come from the domain). The codomain is instantiated at each argument's
  # value, so a dependent parameter type is honoured too.
  defp elaborate_bidirectional_app(name, args, names, ctx, env) do
    with {:ok, head} <- elaborate_expr({:variable, [], name}, names, env),
         {:ok, head_type} <- Kernel.infer(ctx, head) do
      check_app_args(head, head_type, args, names, ctx, env)
    end
  end

  @doc """
  Apply an already-elaborated `term` of value-type `type` to surface `args`,
  checking each argument against the callee's Π domain (so a lambda argument
  elaborates in checking mode). Used by `Cure.Elab.Resolve` to apply a method
  projected off a dictionary at an abstract call site.
  """
  @spec apply_checked_args(term(), term(), [term()], [String.t()], Context.t(), Env.t()) ::
          {:ok, term(), term()} | {:error, term()}
  def apply_checked_args(term, type, args, names, ctx, env),
    do: check_app_args(term, type, args, names, ctx, env)

  defp check_app_args(term, type, args, names, ctx, env),
    do: check_app_args(term, type, args, names, ctx, env, 0)

  defp check_app_args(term, type, [], _names, _ctx, _env, _index), do: {:ok, term, type}

  defp check_app_args(term, type, [arg | rest], names, ctx, env, index) do
    case type do
      {:vpi, _g, dom_value, cod_closure} ->
        dom_term = resplit_data(Quote.reify(dom_value, Context.length(ctx)), env)

        case elaborate_expr_checked(arg, dom_term, names, ctx, env) do
          {:ok, arg_term} ->
            arg_value = Eval.eval(arg_term, Context.env(ctx))
            next_type = Eval.apply_closure(cod_closure, arg_value)
            check_app_args({:app, term, arg_term}, next_type, rest, names, ctx, env, index + 1)

          {:error, reason} ->
            {:error, attach_call_argument_context(reason, arg, index, term)}
        end

      _ ->
        {:error, {:applied_non_function, %{actual: Quote.reify(type, Context.length(ctx)), argument_index: index}}}
    end
  end

  defp attach_call_argument_context({:source_context, reason, context}, arg, index, term)
       when is_map(context) do
    {:source_context, reason, Map.merge(context, call_argument_context(arg, index, term))}
  end

  defp attach_call_argument_context(reason, arg, index, term) do
    {:source_context, reason, call_argument_context(arg, index, term)}
  end

  defp call_argument_context(arg, index, term) do
    span = surface_expression_span(arg)

    %{
      line: span && span.start_line,
      column: span && span.start_column,
      length: span && max(1, span.end_byte - span.start_byte),
      span: span,
      expectation_span: span,
      checking: call_owner(term),
      expression_category: expression_category(arg),
      expectation_origin: :call_argument,
      argument_index: index
    }
  end

  defp surface_expression_span({:union_type, _meta, children}) when is_list(children) do
    spans = children |> Enum.map(&surface_expression_span/1) |> Enum.reject(&is_nil/1)

    case spans do
      [%Cure.Diagnostic.Span{} = first | _] ->
        last = List.last(spans)

        %Cure.Diagnostic.Span{
          first
          | end_byte: last.end_byte,
            end_line: last.end_line,
            end_column: last.end_column
        }

      [] ->
        nil
    end
  end

  defp surface_expression_span({_kind, meta, _children}) when is_list(meta) do
    case Cure.MetaAST.Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{whole: span} -> span
      _ -> nil
    end
  end

  defp surface_expression_span({_kind, meta, _left, _right}) when is_list(meta) do
    case Cure.MetaAST.Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{whole: span} -> span
      _ -> nil
    end
  end

  defp surface_expression_span(_expression), do: nil

  defp expression_category({kind, _meta, _children}) when is_atom(kind), do: kind
  defp expression_category({kind, _meta, _left, _right}) when is_atom(kind), do: kind
  defp expression_category(_expression), do: :expression

  defp call_owner({:global, name}), do: name
  defp call_owner({:app, head, _argument}), do: call_owner(head)
  defp call_owner(_term), do: nil

  @doc """
  Context-aware expression elaboration: elaborate `expr` to `{term, type_value}`
  in a kernel typing `ctx` (whose variables are named, most-recently-bound first,
  by `names`). Constructor applications route through `elaborate_ctor_app/3` so
  their erased indices are inferred; other forms reuse the untyped elaborator and
  the kernel's `infer/2` for their type.
  """
  @spec elaborate_expr_typed(term(), [String.t()], Context.t(), Env.t()) ::
          {:ok, term(), Cure.Core.Value.t()} | {:error, term()}
  def elaborate_expr_typed({:variable, _meta, "Type"}, _names, _ctx, _env),
    do: {:ok, {:type, 0}, {:vtype, 1}}

  def elaborate_expr_typed({:variable, meta, name}, names, ctx, env) do
    case Enum.find_index(names, &(&1 == name)) do
      nil ->
        case resolve_free(name, env) do
          {:ok, term} ->
            with {:ok, type} <- Kernel.infer(ctx, term) do
              {:ok, term, type}
            end

          {:error, reason} ->
            {:error, attach_variable_context(reason, meta, name)}
        end

      index ->
        term = {:var, index}

        with {:ok, type} <- Kernel.infer(ctx, term) do
          {:ok, term, type}
        end
    end
  end

  # A synthetic dictionary argument `{:dict_value, iface, head}`, inserted by
  # `Cure.Elab.Resolve` at a concrete call to a constrained function: build the
  # instance's dictionary record value (its type is `iface(head)`).
  def elaborate_expr_typed({:dict_value, iface, head, type_value}, names, ctx, env),
    do: Cure.Elab.Resolve.dict_value(env, iface, head, type_value, names, ctx)

  # A forced (dot) pattern `{:forced_pattern, …}` is only meaningful in a
  # constructor-argument PATTERN position (handled by the pattern path in a later
  # task). Reaching ordinary expression elaboration means a dot was used outside
  # a pattern (a `let` RHS, a function argument/body, …) — reject it. Placed
  # before the catch-all so this precise error, not `{:unsupported_expression,…}`,
  # is reported.
  def elaborate_expr_typed({:forced_pattern, meta, _children}, _names, _ctx, _env),
    do: {:error, {:source_context, {:forced_pattern_not_in_pattern, meta}, pattern_only_context(meta, :forced_pattern)}}

  # A named-implicit dot pattern `{ name = <expr> }` is only meaningful as a
  # constructor-argument PATTERN position (annotating an erased index by name).
  # Reaching ordinary expression elaboration means it was used outside a pattern
  # — reject it with a precise error (mirrors the forced-pattern guard above).
  def elaborate_expr_typed({:named_implicit_pat, meta, _children}, _names, _ctx, _env),
    do:
      {:error,
       {:source_context, {:named_implicit_not_in_pattern, meta}, pattern_only_context(meta, :named_implicit_pattern)}}

  def elaborate_expr_typed({:function_call, meta, args}, names, ctx, env) do
    cond do
      equation_named_call?(meta, env) ->
        elaborate_equation_named_call(meta, args, names, ctx, env)

      # `element(t, i)` — dependent n-ary telescope/tuple projection. ONE surface
      # for the i-th component, typed at the true `Ti` (not a numbered `tproj_i`),
      # with a COMPILE-TIME bounds check: an `i` beyond the arity is rejected at
      # elaboration, never a runtime crash. `t.i` is sugar for this (both share
      # `positional_projection`). `i` must be a static positive integer literal —
      # the bounds check is only meaningful for a statically-known index.
      Keyword.get(meta, :name) == "element" and
        is_nil(Env.get_def(env, :element)) and
          element_projection?(args) ->
        [t_arg, {:literal, _, i} = index_arg] = args

        positional_projection(i, t_arg, names, ctx, env)
        |> attach_element_projection_context(meta, t_arg, index_arg)

      # Record construction `Point{x: .., y: ..}` desugars to the positional
      # constructor `Point(.., ..)` (fields ordered by the record's telescope).
      Keyword.get(meta, :record) ->
        case desugar_record_construction(meta, args, env) do
          {:ok, positional} ->
            elaborate_expr_typed(positional, names, ctx, env)
            |> attach_record_field_context(meta, args, env)
            |> attach_record_context(meta, args, env)

          {:error, reason} ->
            attach_record_context({:error, reason}, meta, args, env)
        end

      # `f(x)(y)` parses with the inner call preserved as `:callee` (and `name`
      # left "unknown"): elaborate the callee expression, then apply the outer
      # arguments to its (function-typed) result.
      callee = Keyword.get(meta, :callee) ->
        result =
          with {:ok, head, head_type} <- elaborate_expr_typed(callee, names, ctx, env) do
            check_app_args(head, head_type, args, names, ctx, env)
          end

        attach_application_context(result, meta, callee, args)

      true ->
        case elaborate_named_call(meta, args, names, ctx, env) do
          {:error, {:applied_non_function, _details}} = error ->
            attach_application_context(error, meta, nil, args)

          {:error, reason} when is_tuple(reason) ->
            if unresolved_call_reason?(reason) do
              {:error, attach_unresolved_call_context(reason, {:function_call, meta, args}, env)}
            else
              {:error, reason}
            end

          result ->
            result
        end
    end
  end

  def elaborate_expr_typed({:record_update, meta, children}, names, ctx, env) do
    with {:ok, positional} <- desugar_record_update(meta, children, env),
         :ok <- validate_record_update_base(meta, children, names, ctx, env) do
      elaborate_expr_typed(positional, names, ctx, env)
      |> attach_record_update_context(meta, children, env)
    else
      {:error, reason} ->
        attach_record_update_context({:error, reason}, meta, children, env)
    end
  end

  # Projection of a literal pair reduces by the Σ β-rule (`fst %[a,b] = a`,
  # `snd %[a,b] = b`), so we take the component directly — no `{:pair, …}` is built
  # and the kernel is never asked to infer a bare pair. This is what makes a
  # let-bound pair work: `let p = %[a, b]` is substitution-based, so `p.1`/`p.2`
  # become `%[a, b].1`/`.2` after inlining.
  def elaborate_expr_typed({:attribute_access, meta, [{:tuple, _tm, [a, b]} = pair]}, names, ctx, env) do
    field = Keyword.fetch!(meta, :attribute)

    result =
      case field do
        "1" ->
          elaborate_expr_typed(a, names, ctx, env)

        "2" ->
          elaborate_expr_typed(b, names, ctx, env)

        _ ->
          case parse_positional_index(field) do
            {:ok, index} -> {:error, {:telescope_index_out_of_bounds, index, 2}}
            :error -> record_projection(pair, field, names, ctx, env)
          end
      end

    attach_projection_context(result, meta, pair, field)
  end

  def elaborate_expr_typed({:attribute_access, meta, [inner]} = expr, names, ctx, env) do
    attr = Keyword.fetch!(meta, :attribute)

    case equation_member(inner, attr, surface_expression_span(expr), ctx, env) do
      {:ok, _term, _type} = equation ->
        equation

      :not_equation ->
        result =
          case parse_positional_index(attr) do
            {:ok, i} -> positional_projection(i, inner, names, ctx, env)
            :error -> record_projection(inner, attr, names, ctx, env)
          end

        attach_projection_context(result, meta, inner, attr)

      {:error, _} = error ->
        error
    end
  end

  def elaborate_expr_typed({:rewrite_expr, meta, [proof_ast, body_ast]}, _names, _ctx, _env) do
    {:error, {:source_context, :rewrite_requires_expected_type, rewrite_source_context(meta, proof_ast, body_ast)}}
  end

  def elaborate_expr_typed({:proof_chain, _meta, _children} = chain, names, ctx, env),
    do: Cure.Elab.ProofChain.elaborate(chain, names, ctx, env)

  def elaborate_expr_typed({:simplify_command, meta, _rules}, _names, _ctx, _env),
    do: simplify_outside_justification(meta)

  # `assert_type expr : T` — a compile-time ascription. Lower `T`, then elaborate
  # `expr` in CHECKING mode against it (so the assertion can also steer inference).
  # The wrapper carries no runtime content: the result IS the checked term at type
  # `T`, so emit sees only `expr`. Mirrors the classic codegen, which strips it.
  def elaborate_expr_typed({:assert_type, _meta, [expr, type_ast]}, names, ctx, env) do
    with {:ok, expected_core} <- elaborate_type(type_ast, names, env, ctx),
         {:ok, term} <- elaborate_expr_checked(expr, expected_core, names, ctx, env) do
      {:ok, term, Eval.eval(expected_core, Context.env(ctx))}
    end
  end

  def elaborate_expr_typed({:literal, meta, value} = expr, names, ctx, env) do
    case Keyword.get(meta, :subtype) do
      :boolean when is_boolean(value) ->
        ctor = resolve_ctor_key(env, if(value, do: :True, else: :False))
        {:ok, {:ctor, ctor, []}, Kernel.bool_type_value(Context.signature(ctx))}

      :integer when is_integer(value) ->
        # The compact `{:int_lit, value}` Core node stays canonical, but its TYPE
        # is the inductive `Int` family value (post-2026-07-18 surface flip),
        # exactly as the bool arm above types its ctor at `bool_type_value`. Handing
        # back the retired facade `{:vint_type}` here made every elaborated literal
        # fail conversion against a family-typed context (`{:data, Std.Int#Int}` vs
        # `{:int_type}`).
        {:ok, {:int_lit, value}, Kernel.int_type_value(Context.signature(ctx))}

      :float when is_float(value) ->
        {:ok, {:float_lit, value}, {:vfloat_type}}

      :char when is_integer(value) and value >= 0 and value <= 0x10FFFF ->
        case char_type_value(Context.signature(ctx)) do
          {:ok, ty} -> {:ok, {:bounded_lit, value}, ty}
          :no_bounded -> {:error, {:char_literal_needs_bounded, value}}
        end

      :char when is_integer(value) ->
        {:error, {:char_literal_out_of_range, value}}

      # A bare string literal constructs the nominal prelude `String`. Its
      # descriptor still carries `List(Char)` so user literal implementations
      # receive decoded code points without depending on String's storage.
      :string when is_binary(value) ->
        elaborate_expr_typed(desugar_string(value, meta), names, ctx, env)

      # A byte binary literal `<<1, 2, 3>>` desugars to `Std.Binary.of_bytes/1`.
      :bytes when is_list(value) ->
        with {:ok, surface} <- desugar_bytes(value, Keyword.get(meta, :line, 0)) do
          elaborate_expr_typed(surface, names, ctx, env)
        end

      # A symbol literal `:ok` is a value of the Int-tier primitive `Atom` base
      # type — a BEAM atom is its own canonical value (Core `{:atom_lit, a}`).
      :symbol when is_atom(value) ->
        {:ok, {:atom_lit, value}, {:vatom_type}}

      _ ->
        {:error, {:unsupported_expression, expr}}
    end
  end

  # `if c then t else e` — lowered to a `:case` on the inductive `Bool`. In
  # inference mode we infer the `then` branch's type T, check `else` against T,
  # and use the constant motive `λ_:Bool. T` (both branches share the type T).
  def elaborate_expr_typed({:conditional, _meta, [c, t, e]}, names, ctx, env) do
    case elaborate_expr_checked(c, bool_type_term(Context.signature(ctx)), names, ctx, env) do
      {:error, reason} ->
        {:error, attach_expectation_context(reason, c, :condition, :if, nil)}

      {:ok, c_core} ->
        case elaborate_expr_typed(t, names, ctx, env) do
          {:error, reason} ->
            {:error, attach_expectation_context(reason, t, :branch, :if, 0)}

          {:ok, t_core, t_type} ->
            t_type_core = Quote.reify(t_type, Context.length(ctx))

            case elaborate_expr_checked(e, t_type_core, names, ctx, env) do
              {:error, reason} ->
                {:error, normalize_branch_check_error(reason, e, t_type_core, names, ctx, env, :if, 1)}

              {:ok, e_core} ->
                {:ok, bool_case(c_core, t_type_core, t_core, e_core, ctx), t_type}
            end
        end
    end
  end

  # A `let … ⏎ body` block in INFERENCE position — the counterpart to the
  # check-mode `{:block}` clause (`elaborate_let_block/5`). Enables annotation-free
  # function bodies (`fn f() = let a = 1 ⏎ a + 1`) and any inference-position block.
  # There is no `:let` desugaring to guess a type for: build the `:let` Core chain
  # by inferring each binding's rhs, then let the kernel infer the whole term's type
  # (which sidesteps hand-managing the de Bruijn depth of the body's type).
  def elaborate_expr_typed({:block, meta, stmts} = block, names, ctx, env) do
    if Keyword.get(meta, :do, false) do
      infer_do_block(block, stmts, names, ctx, env)
    else
      with {:ok, term} <- infer_block_term(stmts, names, ctx, env),
           {:ok, type} <- Kernel.infer(ctx, term) do
        {:ok, term, type}
      end
    end
  end

  # A surface unary operator. Prefix `-` DESUGARS to a call on `negate` (the
  # `Std.Arithmetic` `Additive` method) so a user type with an `Additive`
  # instance gets prefix negation for free, exactly as an infix overloadable
  # operator desugars to a `:function_call` (Task 3.3). The desugar fires only
  # when `negate` has a meaning in scope (`operator_meaning?/2`); otherwise it
  # falls back to the built-in type-directed lowering, so a unary expression that
  # compiles today with no `use Std.Arithmetic` (bare `-(5)`) is UNCHANGED.
  #
  # `not` is NOT desugared to a call: it is `Std.Bool.\`not\``, a plain function
  # (not an overloadable interface method), so a `:function_call` gives no user
  # benefit and would change its Core lowering (breaking the parity with the
  # `and`/`or` connectives, which stay `{:global, :and/:or}`). It keeps its direct
  # application of the `Std.Bool` prelude def, unchanged.
  def elaborate_expr_typed({:unary_op, meta, [operand]}, names, ctx, env) do
    case Keyword.fetch!(meta, :operator) do
      :not ->
        result =
          with {:ok, o_core, _ot} <- elaborate_expr_typed(operand, names, ctx, env),
               term = {:app, {:global, Cure.Elab.Name.qualify("Std.Bool", :not)}, o_core},
               {:ok, type} <- Kernel.infer(ctx, term) do
            {:ok, term, type}
          end

        attach_unary_operand_context(result, operand, :not)

      # Int-only bitwise complement. `int_bnot : Int -> Int`, so the kernel
      # infer both types the operand against Int and rejects a non-Int operand.
      :bnot ->
        result =
          with {:ok, o_core, _ot} <- elaborate_expr_typed(operand, names, ctx, env),
               term = {:app, {:global, builtin_op_global(:int_bnot)}, o_core},
               {:ok, type} <- Kernel.infer(ctx, term) do
            {:ok, term, type}
          end

        attach_unary_operand_context(result, operand, :bnot)

      # Numeric negation. Desugars to `negate` ONLY when it is a genuine
      # overloadable interface method (`Std.Arithmetic`'s `Additive.negate`) in
      # scope — mirroring the binary-operator path, which routes through
      # `Resolve.method?` (see `elaborate_named_call_resolved`). Otherwise it is
      # type-directed like binary arithmetic: infer the operand's primitive kind,
      # then lower to `int_neg`/`float_neg` (both return their operand type).
      #
      # The trigger MUST be the interface-method check, not the broad
      # `operator_meaning?`: the latter also matches an ordinary function named
      # `negate` (e.g. the ambient `Std.Int.negate`, prelude-visible because
      # `type Int` is `@prelude`). Routing `-x` to that monomorphic `Int -> Int`
      # function hijacked negation for EVERY operand kind, so `-(f : Float)`
      # lowered to an `Int` result and failed conversion against `Float`. Keying
      # on `method?` lets a real `Additive` instance dispatch per operand type
      # while a plain `negate` function falls through to the built-in lowering.
      :- ->
        if Cure.Elab.Resolve.method?(env, :negate) do
          elaborate_expr_typed({:function_call, [name: "negate"], [operand]}, names, ctx, env)
        else
          result =
            with {:ok, o_core, o_type} <- elaborate_expr_typed(operand, names, ctx, env),
                 {:ok, g} <- neg_global(o_type, ctx),
                 term = {:app, {:global, builtin_op_global(g)}, o_core},
                 {:ok, type} <- Kernel.infer(ctx, term) do
              {:ok, term, type}
            end

          attach_unary_operand_context(result, operand, :-)
        end

      op ->
        elaborate_expr_typed(
          {:function_call, [name: Atom.to_string(op)], [operand]},
          names,
          ctx,
          env
        )
    end
  end

  # A surface binary operator (K2 phase 2 + Amendment A1). Arithmetic and
  # comparisons lower to registry-keyed builtin-op GLOBAL spines, type-directed
  # by the left operand: Int → int_*, Float → float_*. The Boolean CONNECTIVES
  # `and`/`or` lower to the `Std.Bool` prelude defs. `==`/`!=` dispatch 4-way:
  # Bool → `eq`/`ne` defs; Int/Float → `int_eq`/`float_eq` twins; any OTHER
  # operand type (ADT, neutral, type variable) → the polymorphic structural
  # `struct_eq`/`struct_ne` global applied to the READBACK of the operand type
  # (A1 §1-A — today's runtime-structural semantics, verbatim). We elaborate
  # both operands in inference mode, assemble the term, and let the kernel
  # infer the result type.
  # Concatenation is an operator overload resolved through the `Std.Semigroup`
  # interface, not a bespoke `build_binop` case: `x <> y` desugars to the
  # `combine` method, which coherence dispatches by the operand's type (the
  # `List` instance delegates to the reducing library `Std.List.append`). A
  # non-numeric `+` is the same overload (Swift-style) — numeric `+`/`-`/`<`/…
  # keep their primitive meaning and only route here when `build_binop` reports
  # the operand type has no primitive op.
  def elaborate_expr_typed({:binary_op, meta, [l, r]} = expr, names, ctx, env) do
    op = Keyword.fetch!(meta, :operator)

    cond do
      # A user-declared overloadable operator (parser tagged it `:overloaded`):
      # desugar to a call on the function named by its lexeme, exactly as the
      # built-in overloads route (`<>`→combine, non-primitive `==`/`<`→method).
      Keyword.get(meta, :category) == :overloaded ->
        overloaded_op_call(op, l, r, expr, names, ctx, env)

      op == :<> ->
        combine_call(l, r, expr, names, ctx, env)

      true ->
        elaborate_binop(op, l, r, expr, names, ctx, env)
    end
  end

  # A `match` in INFERENCE position (no expected type) — reached when a match
  # must have its type SYNTHESISED rather than checked: as the scrutinee of an
  # outer match, or (via `let`'s surface substitution, `elaborate_let_block`)
  # `let b = match n … ⏎ match b …`, which inlines the inner match into the outer
  # scrutinee slot. NON-DEPENDENT synthesis, faithful to Idris' case-function
  # lift: infer the scrutinee's data family, synthesise a candidate result type
  # `T` from the FIRST constructor arm's body (inferred in that arm's branch
  # context), verify `T` does NOT mention the arm's constructor-bound variables
  # (else the match is genuinely dependent and — exactly as in Idris — needs an
  # annotation, so we reject with `:cannot_infer_dependent_match`), strengthen it
  # out of the branch frame, then hand `T` to the CHECKED path (`elaborate_match`)
  # so every arm is checked against the one synthesised type. That reuses all the
  # coverage/motive/index machinery and, since `T` is non-scrutinee-dependent, the
  # motive it builds is effectively constant — correct for inference position.
  def elaborate_expr_typed({:pattern_match, meta, [scrut | arms]} = expr, names, ctx, env)
      when is_list(meta) do
    arms = arms |> desugar_list_patterns() |> desugar_typed_constructor_args()

    if special_match_arms?(arms) do
      with {:ok, desugared} <- desugar_special_match(scrut, arms, Keyword.get(meta, :line, 0)) do
        elaborate_expr_typed(desugared, names, ctx, env)
      end
    else
      with {:ok, _scrut_term, {:vdata, dname, combined_vals}} <-
             elaborate_expr_typed(scrut, names, ctx, env),
           {:ok, {cname, pattern_vars, body_expr}} <- first_constructor_arm(arms, env),
           %{args: telescope, quantities: quantities, plicities: plicities} <-
             Inductive.get_ctor(env, cname),
           arity = length(telescope),
           pc = Inductive.param_count(env, dname),
           {param_vals, _idx_vals} = Enum.split(combined_vals, pc),
           branch_names = branch_scope(telescope, quantities, plicities, pattern_vars) ++ names,
           branch_ctx = extend_context(ctx, telescope, param_vals),
           {:ok, _b_term, t_branch_val} <-
             elaborate_expr_typed(body_expr, branch_names, branch_ctx, env),
           t_branch = Quote.reify(t_branch_val, Context.length(branch_ctx)),
           {:ok, result_type_term} <- strengthen_inferred_type(t_branch, arity),
           {:ok, term} <- elaborate_match(scrut, arms, result_type_term, names, ctx, env),
           result_type_val = Eval.eval(result_type_term, Context.env(ctx)),
           :ok <- Kernel.check(ctx, term, result_type_val) do
        {:ok, term, result_type_val}
      else
        {:ok, _term, _non_data_type} ->
          {:error, cannot_infer_match_type(expr, arms, :scrutinee_not_data)}

        {:error, {:cannot_infer_match_type, :no_constructor_arm}} ->
          {:error, cannot_infer_match_type(expr, arms, :no_constructor_arm)}

        {:error, _} = err ->
          err
      end
    end
  end

  # List literals have one canonical elaborator. Once the first element fixes
  # the homogeneous element type, check the remaining spine directly and build
  # the same `Cons`/`Nil` Core. Falling back retains the blocked-head behaviour
  # where a later element is needed to infer the type.
  # `()` — the unit value (Swift-style), the sole inhabitant of `Unit`. It is the
  # nullary `unit` constructor of the seeded `Unit` family; the same node emit
  # already understands as the empty-telescope terminator.
  def elaborate_expr_typed({:unit_value, _meta}, _names, _ctx, env) do
    {:ok, {:ctor, unit_ctor_name(env), []}, {:vdata, unit_family_name(env), []}}
  end

  def elaborate_expr_typed({:list, meta, elements} = node, names, ctx, env) do
    case infer_list_literal(meta, elements, names, ctx, env) do
      :fallback -> elaborate_expr_typed(desugar_list(node), names, ctx, env)
      {:error, reason} -> {:error, attach_collection_context(reason, elements)}
      result -> result
    end
  end

  # `return e` — in tail position it IS the value of the enclosing function or
  # branch, so it elaborates as the identity on `e`. The classic throw/catch
  # unwind is dropped (a total language has no such escape); the STRUCTURED
  # tail-position meaning is all that survives.
  def elaborate_expr_typed({:early_return, _meta, [e]}, names, ctx, env),
    do: elaborate_expr_typed(e, names, ctx, env)

  # Integer range `a..b` (exclusive) / `a..=b` (inclusive). Desugars to a call to
  # the total structurally-recursive helper `Std.Nat.range_upto{,_incl}` (auto-
  # prelude, so no `use` is needed) — the honest analog of Idris's `enumFromTo`.
  # The list construction is genuine recursion; only the `Int -> Nat` count cast
  # (`Std.Nat.of_int`) is a trusted primitive boundary.
  def elaborate_expr_typed({:range, meta, [from_ast, to_ast]}, names, ctx, env) do
    fname = if Keyword.get(meta, :inclusive, false), do: "range_upto_incl", else: "range_upto"
    line = Keyword.get(meta, :line, 0)
    call = {:function_call, [name: fname, line: line], [from_ast, to_ast]}
    elaborate_expr_typed(call, names, ctx, env)
  end

  # List comprehension `[e for x <- xs, cond, y <- ys]`. Desugars (before Core) to
  # the textbook Wadler translation over already-supported constructs — nothing new
  # reaches the kernel:
  #   * no qualifiers left        -> `[e]`               (singleton list)
  #   * generator `x <- src`      -> `flat_map(src, fn(x) -> <rest>)`
  #   * filter `cond`             -> `if cond then <rest> else []`
  # The sole library dependency is `flat_map` (Std.List; `use`d or, at #18, the
  # dependent-compiled stdlib). Generator patterns must currently be a plain
  # variable — a destructuring generator is rejected rather than silently mistyped.
  def elaborate_expr_typed({:comprehension, meta, [body | quals]}, names, ctx, env) do
    case desugar_comprehension(quals, body, Keyword.get(meta, :line, 0)) do
      {:ok, desugared} -> elaborate_expr_typed(desugared, names, ctx, env)
      {:error, _} = err -> err
    end
  end

  # String interpolation `"a#{e}b"` desugars to a right fold of
  # `Std.String.concat` over the segments (see `desugar_interpolation`).
  # String-valued holes only; a non-string hole fails as an ordinary type error
  # against `concat`'s `String` parameter.
  def elaborate_expr_typed({:string_interpolation, meta, segments}, names, ctx, env) do
    elaborate_expr_typed(
      desugar_interpolation(segments, Keyword.get(meta, :line, 0)),
      names,
      ctx,
      env
    )
  end

  # Map literal `%{k: v, …}`. Desugars (before Core) to nested `Std.Map.put`
  # calls over `Std.Map.new()` — the same shape a hand-written builder has, so
  # nothing new reaches the kernel. `Std.Map` is a thin `@extern` wrapper over
  # Erlang `:maps`, so this is seam-free (the runtime value is always a raw map);
  # the caller must have `use Std.Map` in scope for `put`/`new` to resolve.
  def elaborate_expr_typed({:map, meta, pairs}, names, ctx, env) do
    elaborate_expr_typed(desugar_map(pairs, Keyword.get(meta, :line, 0)), names, ctx, env)
  end

  # Pair introduction `%[a, b]` in typed-synthesis position (a ctor argument, a
  # `let` rhs, any sub-term the checked tuple clause at line ~1137 doesn't reach).
  # Synthesizes the non-dependent Σ `Sigma(A, λ_:A. B)` from the inferred component
  # types — the honest surface `Tuple(A, B)`. Mirrors the scope-based builder
  # (`elaborate_expr/3`, ~5129) and the checked clause; a *genuinely dependent* pair
  # still needs a checking position (its expected type supplies the codomain family).
  # The codomain `B` is closed w.r.t. the fresh Σ binder, so it is shifted +1 to keep
  # its free de Bruijn indices pointing at the same context entries under the `λ`.
  def elaborate_expr_typed({:tuple, _meta, [_, _ | _] = elems}, names, ctx, env) do
    with {:ok, parts} <- elaborate_tuple_parts(elems, names, ctx, env) do
      {value, type_term} = build_telescope_value(parts, ctx, env)
      {:ok, value, Eval.eval(type_term, Context.env(ctx))}
    end
  end

  # Quasiquotation (SP5.1) in checked position: lower `quote` to its builder
  # expression and check that against the expected type (`Syntax`).
  def elaborate_expr_typed({:quoted_syntax, _meta, [inner]}, names, ctx, env),
    do: elaborate_expr_typed(Cure.Compiler.MacroSyntax.lower_quote(inner), names, ctx, env)

  def elaborate_expr_typed({:async_operation, meta, _children}, _names, _ctx, _env),
    do: {:error, unsupported_async_error(meta)}

  def elaborate_expr_typed({tag, meta, _}, _names, _ctx, _env) when tag in [:splice, :splice_group],
    do: {:error, splice_outside_quote_error(tag, meta)}

  # `pickup` predicate dispatch (value-surface Wave 1). Pure syntactic
  # desugaring to a right-nested `:conditional` chain; reuses the conditional
  # path's Bool-guard and branch-join checks verbatim. No kernel change.
  # See docs/superpowers/specs/2026-07-09-wave1-pickup-design.md.
  def elaborate_expr_typed({:pickup, _meta, clauses}, names, ctx, env) do
    with {:ok, desugared} <- desugar_pickup(clauses) do
      elaborate_expr_typed(desugared, names, ctx, env)
    end
  end

  def elaborate_expr_typed(other, _names, _ctx, _env) do
    {:error, {:unsupported_expression, other}}
  end

  # A do block is commonly supplied as an argument to `run`, where ordinary
  # application elaboration initially asks for an inferred argument type. Its
  # effectful first bind gives us the payload type needed to switch to the
  # checking path; that path then constructs the complete bind chain and keeps
  # the Effect wrapper visible until the call to `run`.
  defp infer_do_block({:block, _meta, _stmts} = block, [first | _], names, ctx, env) do
    with {:assignment, _assignment_meta, [_pattern, rhs]} <- first,
         {:ok, _rhs_core, {:veffect_type, result_type}} <- elaborate_expr_typed(rhs, names, ctx, env),
         result_core = Quote.reify(result_type, Context.length(ctx), Context.signature(ctx)),
         expected = {:effect_type, result_core},
         {:ok, term} <- elaborate_expr_checked(block, expected, names, ctx, env),
         {:ok, type} <- Kernel.infer(ctx, term) do
      {:ok, term, type}
    else
      _ -> {:error, {:do_requires_effectful_bind, first}}
    end
  end

  defp infer_do_block(_block, _stmts, _names, _ctx, _env),
    do: {:error, {:do_requires_effectful_bind, :empty}}

  defp require_unsafe_call(meta, name, resolved, env) do
    required? =
      case Env.get_def(env, resolved) do
        %{unsafe: true} -> true
        _ -> false
      end

    if required? and not Keyword.get(meta, :unsafe, false) do
      {:error,
       {:unsafe_call_required,
        %{callee: name, resolved: resolved, span: surface_expression_span({:function_call, meta, []})}}}
    else
      :ok
    end
  end

  defp pattern_only_context(meta, category) do
    source_info = Cure.MetaAST.Metadata.source_info(meta)

    %{
      span: source_info && source_info.whole,
      opener_span: source_info && source_info.opener,
      name_span: source_info && source_info.name,
      body_span: source_info && source_info.body,
      expectation_origin: :pattern,
      expression_category: category
    }
  end

  defp attach_application_context(
         {:error, {:applied_non_function, details} = reason},
         meta,
         callee,
         args
       ) do
    source_info = Cure.MetaAST.Metadata.source_info(meta)
    index = Map.get(details, :argument_index, 0)
    callee_span = if(callee, do: surface_expression_span(callee), else: source_info && source_info.callee)
    argument_span = args |> Enum.at(index) |> surface_expression_span()

    {:error,
     {:source_context, reason,
      %{
        span: if(index == 0, do: callee_span || argument_span, else: argument_span || callee_span),
        application_span: source_info && source_info.whole,
        callee_span: callee_span,
        callee_name: Keyword.get(meta, :name),
        argument_span: argument_span,
        argument_index: index,
        expectation_origin: :application,
        expression_category: :function_call
      }}}
  end

  defp attach_application_context(result, _meta, _callee, _args), do: result

  defp attach_projection_context({:error, {:source_context, reason, context}}, meta, inner, field) do
    {:error, {:source_context, reason, Map.merge(projection_context(meta, inner, field), context)}}
  end

  defp attach_projection_context({:error, reason}, meta, inner, field) do
    {:error, {:source_context, reason, projection_context(meta, inner, field)}}
  end

  defp attach_projection_context(result, _meta, _inner, _field), do: result

  defp attach_element_projection_context({:error, reason}, meta, receiver, index) do
    info = Cure.MetaAST.Metadata.source_info(meta)

    {:error,
     {:source_context, reason,
      %{
        span: info && info.whole,
        receiver_span: surface_expression_span(receiver),
        index_span: surface_expression_span(index),
        callee_span: info && info.callee,
        expression_category: :function_call,
        expectation_origin: :projection,
        projection_syntax: :element
      }}}
  end

  defp attach_element_projection_context(result, _meta, _receiver, _index), do: result

  defp projection_context(meta, inner, field) do
    source_info = Cure.MetaAST.Metadata.source_info(meta)

    %{
      span: source_info && source_info.whole,
      receiver_span: surface_expression_span(inner),
      field_span: source_info && source_info.name,
      field: field,
      expression_category: :attribute_access,
      expectation_origin: :projection
    }
  end

  defp equation_member(inner, member_name, use_span, ctx, env) do
    with {:ok, function_name, members} <- equation_reference(inner, member_name) do
      resolve_equation_member(env, function_name, members, use_span, ctx)
    else
      :error -> :not_equation
    end
  end

  # `f.Ctor` without arguments is attribute access, but `f.Ctor(args...)` is
  # flattened by the parser into a named call literally called `"f.Ctor"`.
  # Resolve that representation to the certified theorem before global lookup.
  defp equation_named_call?(meta, env) do
    case equation_call_parts(Keyword.get(meta, :name)) do
      {:ok, function_name, members} ->
        Cure.Elab.Equation.resolve_path(env, function_name, members) != :not_equation

      :error ->
        false
    end
  end

  defp elaborate_equation_named_call(meta, args, names, ctx, env) do
    {:ok, function_name, members} = equation_call_parts(Keyword.fetch!(meta, :name))
    info = Cure.MetaAST.Metadata.source_info(meta)
    span = info && info.whole

    case Cure.Elab.Equation.resolve_path(env, function_name, members) do
      {:ok, descriptor} ->
        apply_equation_descriptor(descriptor, args, names, ctx, env)

      _ ->
        with {:ok, term, type} <- resolve_equation_member(env, function_name, members, span, ctx),
             {:ok, applied, result_type} <- check_app_args(term, type, args, names, ctx, env) do
          {:ok, applied, result_type}
        end
    end
  end

  defp apply_equation_descriptor(descriptor, args, names, ctx, env) do
    parameter_count = Map.get(descriptor, :application_parameter_count, 0)
    field_count = Map.get(descriptor, :application_field_count, 0)
    replacements = Map.get(descriptor, :application_replacements, %{})
    unaffected_count = parameter_count - map_size(replacements)

    if length(args) == field_count + unaffected_count do
      with {:ok, surface_terms} <- map_typed_terms(args, names, ctx, env) do
        {field_terms, unaffected_terms} = Enum.split(surface_terms, field_count)

        {original_terms, []} =
          Enum.map_reduce(0..(parameter_count - 1)//1, unaffected_terms, fn position, remaining ->
            original_index = parameter_count - 1 - position

            case Map.fetch(replacements, original_index) do
              {:ok, template} ->
                {replace_equation_field_vars(template, field_terms), remaining}

              :error ->
                [term | rest] = remaining
                {term, rest}
            end
          end)

        copy_terms =
          descriptor
          |> Map.get(:application_copy_map, %{})
          |> Enum.sort_by(fn {_original, copy_index} -> -copy_index end)
          |> Enum.map(fn {original_index, _copy_index} ->
            Enum.at(original_terms, parameter_count - 1 - original_index)
          end)

        applied =
          Enum.reduce(original_terms ++ field_terms ++ copy_terms, {:global, descriptor.theorem}, fn argument, call ->
            {:app, call, argument}
          end)

        case Kernel.infer(ctx, applied) do
          {:ok, result_type} -> {:ok, applied, result_type}
          {:error, _} = error -> error
        end
      end
    else
      {:error,
       {:arity_mismatch, %{function: descriptor.theorem, expected: field_count + unaffected_count, got: length(args)}}}
    end
  end

  defp map_typed_terms(args, names, ctx, env) do
    Enum.reduce_while(args, {:ok, []}, fn arg, {:ok, terms} ->
      case elaborate_expr_typed(arg, names, ctx, env) do
        {:ok, term, _type} -> {:cont, {:ok, terms ++ [term]}}
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  defp replace_equation_field_vars({:var, index}, field_terms) when is_integer(index) do
    Enum.at(field_terms, length(field_terms) - 1 - index)
  end

  defp replace_equation_field_vars(tuple, field_terms) when is_tuple(tuple) do
    tuple
    |> Tuple.to_list()
    |> Enum.map(&replace_equation_field_vars(&1, field_terms))
    |> List.to_tuple()
  end

  defp replace_equation_field_vars(list, field_terms) when is_list(list),
    do: Enum.map(list, &replace_equation_field_vars(&1, field_terms))

  defp replace_equation_field_vars(other, _field_terms), do: other

  defp equation_call_parts(name) when is_binary(name) do
    case String.split(name, ".", trim: true) do
      [function_name, member | rest] -> {:ok, function_name, [member | rest]}
      _ -> :error
    end
  end

  defp equation_call_parts(_), do: :error

  defp resolve_equation_member(env, function_name, members, use_span, ctx) do
    case Cure.Elab.Equation.resolve_path(env, function_name, members) do
      {:ok, descriptor} ->
        term = {:global, descriptor.theorem}

        case Kernel.infer(ctx, term) do
          {:ok, type} -> {:ok, term, type}
          {:error, _} = error -> error
        end

      {:error, {:defining_equation_unavailable, kind, _function, _member, details}} ->
        {:error,
         {:defining_equation_unavailable,
          %Cure.Diagnostic.DefiningEquationProblem{
            kind: kind,
            equation_use: use_span,
            function_definition: equation_definition_span(env, function_name),
            candidate_equations: equation_candidate_spans(details),
            owner: function_name,
            member: Enum.join(members, ".")
          }}}

      :not_equation ->
        :not_equation
    end
  end

  defp equation_reference({:variable, _meta, function_name}, member_name),
    do: {:ok, function_name, [member_name]}

  defp equation_reference({:attribute_access, meta, [inner]}, member_name) do
    with {:ok, function_name, members} <- equation_reference(inner, Keyword.fetch!(meta, :attribute)) do
      {:ok, function_name, members ++ [member_name]}
    end
  end

  defp equation_reference(_inner, _member_name), do: :error

  defp equation_definition_span(env, function_name) do
    env.equations
    |> Enum.find_value(fn {owner, descriptors} ->
      if Cure.Elab.Name.overload_base(owner) == function_name do
        descriptors
        |> List.first()
        |> then(&(&1 && Cure.Elab.Equation.source_metadata(&1)[:definition_span]))
      end
    end)
  end

  defp equation_candidate_spans(details) when is_list(details) do
    Enum.flat_map(details, fn
      %{definition_span: %Cure.Diagnostic.Span{} = span} -> [span]
      _ -> []
    end)
  end

  defp equation_candidate_spans(_details), do: []

  # Synthesise each element of a tuple literal to `{core, type_term}` (the inferred
  # type reified to a Core term at the current depth).
  defp elaborate_tuple_parts(elems, names, ctx, env) do
    len = Context.length(ctx)

    Enum.reduce_while(elems, {:ok, []}, fn e, {:ok, acc} ->
      case elaborate_expr_typed(e, names, ctx, env) do
        {:ok, core, type} -> {:cont, {:ok, acc ++ [{core, Quote.reify(type, len)}]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  # Build the unit-terminated telescope value + type from synthesised parts:
  # `%[e1, …, en]` (no expected type) is a flat `Tuple(T1, …, Tn)` —
  # `mk_pair(e1, … mk_pair(en, unit))` at type `Sigma(T1, λ. … Sigma(Tn, λ. Unit))`.
  # A genuinely DEPENDENT pair still needs a checking position (its expected type
  # supplies the codomain family); synthesis is the non-dependent product, which
  # is exactly a Tuple. Folds from the right so each accumulated type shifts +1
  # under the fresh Σ binder (non-dependent, so the binder is unused).
  defp build_telescope_value(parts, _ctx, env) do
    mk_pair = sigma_ctor_name(env)
    fam = Inductive.builtin(env, :sigma)
    unit_ctor = unit_ctor_name(env)
    unit_family = unit_family_name(env)

    Enum.reduce(Enum.reverse(parts), {{:ctor, unit_ctor, []}, {:data, unit_family, [], []}}, fn
      {core, type_term}, {val_acc, type_acc} ->
        value = {:ctor, mk_pair, [core, val_acc]}
        cod = {:lam, Cure.Core.Grade.unrestricted(), type_term, Cure.Core.Term.shift(type_acc, 1)}
        type = {:data, fam, [type_term, cod], []}
        {value, type}
    end)
  end

  # Desugar a concatenation operator to the `Std.Semigroup.combine` method call,
  # letting the interface-dispatch machinery pick the instance by operand type.
  defp combine_call(l, r, expr, names, ctx, env) do
    if operator_meaning?(env, :combine) do
      elaborate_expr_typed({:function_call, [name: "combine"], [l, r]}, names, ctx, env)
    else
      details = %{operator: :<>, method: :combine, provider: "Std.Semigroup"}
      context = operator_expression_context(expr, l, r, :<>, [], ctx)
      {:error, {:source_context, {:operator_provider_not_in_scope, details}, context}}
    end
  end

  # Desugar an operator on a NON-primitive operand to the bare-name method call
  # for its lexeme — the SOLE route to `==`/`!=`/`<`/`<=`/`>`/`>=` for any type
  # `build_binop` does not lower to a primitive. `Comparable` now exposes `` `<` ``
  # directly (and the derived `` `<=` ``/`` `>` ``/`` `>=` `` are top-level
  # `where Comparable(t)` functions), and `Equatable` exposes `` `==` `` (with the
  # derived `` `!=` `` a top-level `where Equatable(t)` function). So each operator
  # maps to a function-call on its own lexeme:
  #
  #     a <  b  ~>  `<`(a, b)      a == b  ~>  `==`(a, b)
  #     a <= b  ~>  `<=`(a, b)     a != b  ~>  `!=`(a, b)
  #     a >  b  ~>  `>`(a, b)
  #     a >= b  ~>  `>=`(a, b)
  #
  # `` `==` ``/`` `<` `` resolve through the interface (`Resolve.method_call`),
  # dispatching by coherence to the operand's `Equatable`/`Comparable` instance;
  # the derived `` `!=` ``/`` `<=` ``/`` `>` ``/`` `>=` `` resolve as ordinary
  # `where`-constrained globals (`Resolve.constrained_call`). Reached only when
  # `build_binop` reports the operand type has no primitive lowering (Int/Float —
  # and, for equality, Bool/Bounded — keep their primitive meaning as an
  # optimisation of this single route). `Std.Equatable`/`Std.Comparable` are
  # `@prelude`-ambient, so these names resolve with no explicit `use`.
  defp op_method_call(op, l, r, names, ctx, env),
    do: elaborate_expr_typed({:function_call, [name: Atom.to_string(op)], [l, r]}, names, ctx, env)

  # The built-in binary-operator path (arithmetic/comparison/equality/bitwise):
  # elaborate both operands, assemble the primitive term, and let the kernel
  # infer its type; on `{:unsupported_operand_type, _}` fall back to the
  # typeclass method desugar (Phase 2). Extracted verbatim from the former
  # `{:binary_op}` body so the `:overloaded` and `<>` routes sit beside it.
  defp elaborate_binop(op, l, r, expr, names, ctx, env) do
    case elaborate_binop_operands(l, r, names, ctx, env) do
      {:error, index, reason} ->
        operand = if index == 0, do: l, else: r
        {:error, attach_operator_operand_context(reason, operand, index, op)}

      {:ok, l_core, l_type, r_core} ->
        with {:ok, term} <- build_binop(op, l_core, r_core, l_type, ctx),
             {:ok, type} <- Kernel.infer(ctx, term) do
          {:ok, term, type}
        else
          {:error, {:unsupported_operand_type, :+}} ->
            combine_call(l, r, expr, names, ctx, env)

          {:error, {:unsupported_operand_type, cmp}}
          when cmp in [:<, :>, :<=, :>=] ->
            op_method_call(cmp, l, r, names, ctx, env)

          # `==`/`!=` on a non-primitive operand (String, ADT, abstract/rigid type
          # variable) — `build_binop`'s `{:==,:!=}` clause reports the operand has no
          # primitive twin, and the SOLE route is the `Equatable` method desugar. A
          # rigid type variable with no in-scope dictionary rejects here as
          # `{:no_instance, :Equatable, {:rigid, _}}`, the intended sole-route error.
          {:error, {:unsupported_operand_type, eq}}
          when eq in [:==, :!=] ->
            op_method_call(eq, l, r, names, ctx, env)

          :unsupported_op ->
            overloaded_op_call(op, l, r, expr, names, ctx, env)

          {:error, {:unsupported_operand_type, failed_op} = reason} ->
            {:error,
             {:source_context, reason, operator_expression_context(expr, l, r, failed_op, [l_type, l_type], ctx)}}

          {:error, reason} ->
            {:error, attach_operator_operand_context(reason, r, 1, op)}

          other ->
            other
        end
    end
  end

  # Binary operators are homogeneous. Infer one operand, then CHECK the other at
  # that type so contextual literal protocols participate (`char == 12`). If the
  # left operand is itself an integer spelling and the right is not, infer from
  # the right instead (`12 == char`); two bare numerals retain the Int default.
  defp elaborate_binop_operands(l, r, names, ctx, env) do
    if integer_literal_ast?(l) and not integer_literal_ast?(r) do
      case elaborate_expr_typed(r, names, ctx, env) do
        {:ok, r_core, r_type} ->
          expected = r_type |> Quote.reify(Context.length(ctx)) |> resplit_data(env)

          case elaborate_expr_checked(l, expected, names, ctx, env) do
            {:ok, l_core} -> {:ok, l_core, r_type, r_core}
            {:error, reason} -> {:error, 0, reason}
          end

        {:error, reason} ->
          {:error, 1, reason}
      end
    else
      case elaborate_expr_typed(l, names, ctx, env) do
        {:ok, l_core, l_type} ->
          expected = l_type |> Quote.reify(Context.length(ctx)) |> resplit_data(env)

          case elaborate_expr_checked(r, expected, names, ctx, env) do
            {:ok, r_core} -> {:ok, l_core, l_type, r_core}
            {:error, reason} -> {:error, 1, reason}
          end

        {:error, reason} ->
          {:error, 0, reason}
      end
    end
  end

  defp integer_literal_ast?({:literal, meta, value}),
    do: Keyword.get(meta, :subtype) == :integer and is_integer(value)

  defp integer_literal_ast?(_), do: false

  defp attach_operator_operand_context({:source_context, reason, context}, operand, index, op)
       when is_map(context) do
    {:source_context, reason, Map.merge(context, operator_operand_context(operand, index, op))}
  end

  # Nested operators use these values as internal dispatch signals. Preserve
  # them so the enclosing operator can still lower to its method-call route.
  defp attach_operator_operand_context({:unsupported_operand_type, operator}, _operand, _index, _op),
    do: {:unsupported_operand_type, operator}

  defp attach_operator_operand_context(:unsupported_op, _operand, _index, _op), do: :unsupported_op

  defp attach_operator_operand_context(reason, operand, index, op) do
    {:source_context, reason, operator_operand_context(operand, index, op)}
  end

  defp operator_operand_context(operand, index, op) do
    span = surface_expression_span(operand)

    %{
      line: span && span.start_line,
      column: span && span.start_column,
      length: span && max(1, span.end_byte - span.start_byte),
      span: span,
      expectation_span: span,
      checking: op,
      expression_category: expression_category(operand),
      expectation_origin: :operator_operand,
      argument_index: index
    }
  end

  # A user-declared overloadable operator (`x <?> y`) is sugar for a call on the
  # function named by its lexeme (`` `<?>`(x, y) ``). If no function/method/ctor
  # of that name is in scope, the operator has a fixity but no meaning — reject
  # with `{:no_operator_meaning, op}` rather than letting it dissolve into a
  # generic `:unknown_global`. Otherwise route through the ordinary
  # function-call path, so real type errors in the operands still surface.
  defp overloaded_op_call(op, l, r, expr, names, ctx, env) do
    if operator_meaning?(env, op) do
      elaborate_expr_typed({:function_call, [name: Atom.to_string(op)], [l, r]}, names, ctx, env)
    else
      {:error, {:source_context, {:no_operator_meaning, op}, operator_expression_context(expr, l, r, op, [], ctx)}}
    end
  end

  defp operator_expression_context({:binary_op, meta, _children}, left, right, op, types, ctx)
       when is_list(meta) do
    source_info = Cure.MetaAST.Metadata.source_info(meta)
    operator_span = source_info && source_info.operator
    operand_spans = if source_info, do: source_info.operands, else: []

    operand_spans =
      if operand_spans == [], do: [surface_expression_span(left), surface_expression_span(right)], else: operand_spans

    %{
      line: operator_span && operator_span.start_line,
      column: operator_span && operator_span.start_column,
      length: operator_span && max(1, operator_span.end_byte - operator_span.start_byte),
      span: operator_span,
      operator_span: operator_span,
      operand_spans: Enum.reject(operand_spans, &is_nil/1),
      operand_types: Enum.map(types, &Quote.reify(&1, Context.length(ctx), Context.signature(ctx))),
      checking: op,
      expression_category: :binary_operator,
      expectation_origin: :operator
    }
  end

  # True when `atom` names anything callable: a top-level definition, an
  # interface method, a `where`-constrained global, a constructor, or a bare
  # name resolvable through a single re-keyed import.
  defp operator_meaning?(env, atom) do
    Env.get_def(env, atom) != nil or
      Cure.Elab.Resolve.method?(env, atom) or
      Cure.Elab.Resolve.constrained?(env, atom) or
      Inductive.get_ctor(env, atom) != nil or
      match?({:ok, _}, Cure.Elab.Resolution.resolve_bare(env, atom))
  end

  # Fold a `pickup` clause list into a right-nested `:conditional` chain.
  # The LAST clause is the terminator (its body is the seed); every earlier
  # clause is a guard wrapper `{:conditional, [], [guard, body, acc]}`.
  # Three terminator shapes (matching codegen.ex's pickup lowering exactly):
  #   {:pickup_else, _, [e]}                         -> seed e
  #   {:pickup_clause, _, [{:literal, _, true}, e]}  -> seed e (guard discarded)
  #   anything else in last position                 -> defensive error
  # A single-clause pickup (only the terminator) collapses to the seed body
  # with no wrapping conditional (PICKUP §11: `pickup else -> e ≡ e`).
  # The empty/terminatorless shapes are impossible post-parse (the parser's
  # validate_pickup_clauses enforces them); the error arms are belt-and-suspenders.
  defp desugar_pickup([]), do: {:error, {:pickup_missing_else, []}}

  defp desugar_pickup(clauses) do
    {wrappers, [last]} = Enum.split(clauses, length(clauses) - 1)

    with {:ok, seed} <- pickup_seed(last) do
      fold_pickup_wrappers(wrappers, seed)
    end
  end

  defp fold_pickup_wrappers(wrappers, seed) do
    Enum.reduce_while(Enum.reverse(wrappers), {:ok, seed}, fn
      {:pickup_clause, _cm, [g, b]}, {:ok, acc} ->
        {:cont, {:ok, {:conditional, [], [g, b, acc]}}}

      other, {:ok, _acc} ->
        {:halt, {:error, {:pickup_missing_else, other}}}
    end)
  end

  defp pickup_seed({:pickup_else, _m, [e]}), do: {:ok, e}
  defp pickup_seed({:pickup_clause, _m, [{:literal, _, true}, e]}), do: {:ok, e}
  defp pickup_seed(other), do: {:error, {:pickup_missing_else, other}}

  # The first arm whose pattern is a constructor application, as
  # `{resolved_ctor, pattern_vars, body}` — the arm used to synthesise an
  # inference-position match's result type. Variable/wildcard (default) arms are
  # skipped; if no constructor arm exists the match cannot be synthesised here.
  defp first_constructor_arm(arms, env) do
    Enum.reduce_while(arms, {:error, {:cannot_infer_match_type, :no_constructor_arm}}, fn
      {:match_arm, arm_meta, body}, acc ->
        pattern = Keyword.fetch!(arm_meta, :pattern)

        case constructor_pattern(pattern) do
          {:ok, {cname0, pattern_vars}} ->
            cname = resolve_ctor_key(env, cname0)

            case Inductive.get_ctor(env, cname) do
              nil ->
                {:cont, acc}

              ctor ->
                case validate_constructor_pattern_arity(pattern, ctor, cname, pattern_vars) do
                  :ok -> {:halt, {:ok, {cname, pattern_vars, single_body(body)}}}
                  {:error, _} = error -> {:halt, error}
                end
            end

          {:error, _} ->
            {:cont, acc}
        end

      _other, acc ->
        {:cont, acc}
    end)
  end

  defp cannot_infer_match_type(expr, arms, reason) do
    %{
      reason: reason,
      span: surface_expression_span(expr),
      scrutinee_span: match_scrutinee_span(expr),
      branch_spans: Enum.map(arms, &match_arm_pattern_span/1) |> Enum.reject(&is_nil/1),
      expression_category: :pattern_match
    }
    |> then(&{:cannot_infer_match_type, &1})
  end

  defp match_scrutinee_span({:pattern_match, _meta, [scrutinee | _arms]}),
    do: surface_expression_span(scrutinee)

  defp match_scrutinee_span(_expression), do: nil

  defp match_arm_pattern_span({:match_arm, arm_meta, _body}) when is_list(arm_meta) do
    arm_meta
    |> Keyword.get(:pattern)
    |> surface_expression_span()
  end

  defp match_arm_pattern_span(_arm), do: nil

  # Strengthen a branch-body type out of the constructor's `arity` bound vars (de
  # Bruijn 0..arity-1, most-recently bound). If any of those occur the type is
  # genuinely dependent — reject (needs an annotation); otherwise shift the free
  # outer variables down by `arity` (the inverse of `Subst.shift(_, arity, 0)`).
  defp strengthen_inferred_type(t_branch, 0), do: {:ok, t_branch}

  defp strengthen_inferred_type(t_branch, arity) do
    if occurs_below?(t_branch, arity, 0),
      do: {:error, {:cannot_infer_dependent_match, t_branch}},
      else: {:ok, Subst.shift(t_branch, -arity, 0)}
  end

  # Does any de Bruijn variable in the window `[depth, depth + arity)` occur in
  # `term`? Binder cutoffs are tracked EXACTLY as `Subst.shift` does (pi/lam/sigma
  # add one, each `:case` branch adds its own arity), so a positive answer means
  # strengthening by `-arity` at cutoff 0 would capture/underflow — i.e. the type
  # depends on the constructor-bound variables.
  defp occurs_below?({:var, k}, arity, depth), do: k >= depth and k < depth + arity

  defp occurs_below?({:pi, _g, d, c}, arity, depth),
    do: occurs_below?(d, arity, depth) or occurs_below?(c, arity, depth + 1)

  defp occurs_below?({:lam, _g, d, b}, arity, depth),
    do: occurs_below?(d, arity, depth) or occurs_below?(b, arity, depth + 1)

  defp occurs_below?({:case, s, m, brs}, arity, depth) do
    occurs_below?(s, arity, depth) or occurs_below?(m, arity, depth) or
      Enum.any?(brs, fn {_cn, ar, b} -> occurs_below?(b, arity, depth + ar) end)
  end

  defp occurs_below?(t, arity, depth) when is_tuple(t),
    do: t |> Tuple.to_list() |> Enum.any?(&occurs_below?(&1, arity, depth))

  defp occurs_below?(l, arity, depth) when is_list(l),
    do: Enum.any?(l, &occurs_below?(&1, arity, depth))

  defp occurs_below?(_other, _arity, _depth), do: false

  # Authored operator names to the builtin-op key the type-directed dispatch
  # maps onto a monomorphic global
  # (K2). Only the ops with registered globals are mapped; `<>` (string
  # concat), `..`, and the like are left unsupported here.
  defp prim_op(:+), do: {:ok, :add}
  defp prim_op(:-), do: {:ok, :sub}
  defp prim_op(:*), do: {:ok, :mul}
  defp prim_op(:/), do: {:ok, :div}
  defp prim_op(:rem), do: {:ok, :rem}
  defp prim_op(:<), do: {:ok, :lt}
  defp prim_op(:>), do: {:ok, :gt}
  defp prim_op(:<=), do: {:ok, :le}
  defp prim_op(:>=), do: {:ok, :ge}
  # Int-only bitwise (no float twin — an @float_binop_globals miss rejects).
  defp prim_op(:band), do: {:ok, :band}
  defp prim_op(:bor), do: {:ok, :bor}
  defp prim_op(:bxor), do: {:ok, :bxor}
  defp prim_op(:bsl), do: {:ok, :bsl}
  defp prim_op(:bsr), do: {:ok, :bsr}
  defp prim_op(_), do: :error

  # Assemble the Core term for a surface binary operator (K2 phase 2 + A1).
  # The connectives and Bool-operand equality become applications of the
  # Std.Bool prelude defs; arithmetic/comparisons become type-directed
  # builtin-op global spines (int_*/float_*); non-primitive-typed `==`/`!=`
  # becomes the polymorphic structural `struct_eq`/`struct_ne` global applied
  # to the quoted operand type. Maps are explicit literals (no dynamic atom
  # construction). The float map has NO `rem` entry — `rem` on Float is
  # `{:error, {:unsupported_operand_type, :rem}}` (enumerated R5 churn; today
  # it dies as kernel `{:prim_type, :rem}`).
  @int_binop_globals %{
    add: :int_add,
    sub: :int_sub,
    mul: :int_mul,
    div: :int_div,
    rem: :int_rem,
    lt: :int_lt,
    le: :int_le,
    gt: :int_gt,
    ge: :int_ge,
    band: :int_band,
    bor: :int_bor,
    bxor: :int_bxor,
    bsl: :int_bsl,
    bsr: :int_bsr
  }
  @float_binop_globals %{
    add: :float_add,
    sub: :float_sub,
    mul: :float_mul,
    div: :float_div,
    lt: :float_lt,
    le: :float_le,
    gt: :float_gt,
    ge: :float_ge
  }

  defp build_binop(:and, l, r, _l_type, _ctx),
    do: {:ok, app2(Cure.Elab.Name.qualify("Std.Bool", :and), l, r)}

  defp build_binop(:or, l, r, _l_type, _ctx),
    do: {:ok, app2(Cure.Elab.Name.qualify("Std.Bool", :or), l, r)}

  defp build_binop(op_sym, l, r, l_type, ctx) when op_sym in [:==, :!=] do
    case primitive_scrut_kind(l_type, Context.signature(ctx)) do
      {:ok, :bool} ->
        name = if(op_sym == :==, do: :eq, else: :ne)
        {:ok, app2(Cure.Elab.Name.qualify("Std.Bool", name), l, r)}

      {:ok, :int} ->
        {:ok, app2(builtin_op_global(if(op_sym == :==, do: :int_eq, else: :int_ne)), l, r)}

      {:ok, :float} ->
        {:ok, app2(builtin_op_global(if(op_sym == :==, do: :float_eq, else: :float_ne)), l, r)}

      # An indexed family (Bounded — Char) erases to a native int but is not a
      # monomorphic twin, so it takes the polymorphic struct_eq path directly. This
      # is a concrete-type primitive fast path (Bounded erases to a BEAM int, so
      # struct_eq IS its native equality), lowering to the identical spine
      # the `Equatable for Char` (keyed `:Bounded`) instance would — kept as an
      # optimisation of the single route. It is NOT routed to the method because
      # that instance is index-specialised to Char's `Bounded(1114112)` and would
      # reject a differently-indexed `Bounded(n)`.
      {:ok, :bounded} ->
        struct_eq_binop(op_sym, l, r, l_type, ctx)

      # `Atom` is a sealed Int-tier primitive base type (`{:vatom_type}`): a BEAM
      # atom is its own canonical value, so `:ok == :ok` is native primitive
      # equality, no more a typeclass obligation than `1 == 1`. This concrete fast
      # path lowers to the identical `struct_eq(Atom, ·, ·)` spine the
      # `Equatable for Atom` instance emits — an optimisation of the single route,
      # never reached for an abstract/rigid/ADT operand (those fall to `:error`).
      # It is required for the bootstrap-closure OTP/syntax modules, which compare
      # atoms yet elaborate with no ambient `Equatable` dictionary.
      {:ok, :atom} ->
        struct_eq_binop(op_sym, l, r, l_type, ctx)

      # Any OTHER operand type — String, an ADT, a neutral, or an abstract/rigid
      # type variable — has no primitive equality. The SOLE route is the
      # `Equatable` method desugar: report "no primitive operand" so the
      # `{:binary_op, …}` caller re-elaborates `` `==`(l, r) ``/`` `!=`(l, r) ``.
      # A concrete type reaches its (hand-written or auto-derived) instance; a
      # rigid variable with no in-scope dictionary rejects with
      # `{:no_instance, :Equatable, {:rigid, _}}`. The universal constraint-free
      # `struct_eq` last-resort for abstract types is retired here.
      :error ->
        {:error, {:unsupported_operand_type, op_sym}}
    end
  end

  defp build_binop(op_sym, l, r, l_type, ctx) do
    case prim_op(op_sym) do
      {:ok, op} ->
        case primitive_scrut_kind(l_type, Context.signature(ctx)) do
          {:ok, :int} ->
            case Map.fetch(@int_binop_globals, op) do
              {:ok, g} -> {:ok, app2(builtin_op_global(g), l, r)}
              :error -> {:error, {:unsupported_operand_type, op_sym}}
            end

          {:ok, :float} ->
            case Map.fetch(@float_binop_globals, op) do
              {:ok, g} -> {:ok, app2(builtin_op_global(g), l, r)}
              :error -> {:error, {:unsupported_operand_type, op_sym}}
            end

          # No Bool arithmetic; non-numeric operand types reject here
          # (enumerated R5 churn — today these die as kernel {:prim_type, op}).
          _ ->
            {:error, {:unsupported_operand_type, op_sym}}
        end

      :error ->
        :unsupported_op
    end
  end

  # A1 §1-A: structural equality — struct_eq/struct_ne applied to the readback of
  # the operand type. The readback is signature-aware: an applied INDEXED family
  # (e.g. `Bounded(n)`, Char's underlying type) must keep its param/index split,
  # because this `ty` flows into `Kernel.infer` (the caller), which arity-checks
  # params and indices separately — a sig-less readback flattens the index into
  # the param slot and the kernel rejects it with `:arg_arity`. A meta-containing
  # readback must never reach the kernel (R8b): reject defensively (corpus
  # predicts none).
  defp struct_eq_binop(op_sym, l, r, l_type, ctx) do
    ty = Quote.reify(l_type, Context.length(ctx), Context.signature(ctx))

    if Unify.has_meta?(ty) do
      {:error, {:unsupported_operand_type, op_sym}}
    else
      g = builtin_op_global(if op_sym == :==, do: :struct_eq, else: :struct_ne)
      {:ok, {:app, app2(g, ty, l), r}}
    end
  end

  # Pick the type-directed negation builtin from the operand's primitive kind,
  # mirroring `build_binop`'s Int→int_*/Float→float_* dispatch for unary `-x`.
  defp neg_global(o_type, ctx) do
    case primitive_scrut_kind(o_type, Context.signature(ctx)) do
      {:ok, :int} -> {:ok, :int_neg}
      {:ok, :float} -> {:ok, :float_neg}
      _ -> {:error, {:unsupported_operand_type, :-}}
    end
  end

  # A saturated `f(a)(b)` application of a global by name, most-recently-applied
  # argument outermost — the shape the kernel + emit expect for a curried def.
  defp app2(name, l, r), do: {:app, {:app, {:global, name}, l}, r}

  # Left-nested application of a head term to a list of argument terms, in order:
  # `[a, b, c]` becomes `{:app, {:app, {:app, head, a}, b}, c}` — the curried spine
  # the kernel and emit expect.
  defp build_app_spine(head, arg_terms), do: Enum.reduce(arg_terms, head, &{:app, &2, &1})

  # Elaborate every surface argument to its Core term (discarding the inferred
  # types), short-circuiting on the first failure. Returns `{:ok, terms}` in call
  # order or the first `{:error, _}`.
  defp elaborate_all_args(args, names, ctx, env) do
    Enum.reduce_while(args, {:ok, []}, fn a, {:ok, acc} ->
      case elaborate_expr_typed(a, names, ctx, env) do
        {:ok, term, _ty} -> {:cont, {:ok, acc ++ [term]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  # The canonical global identity of a kernel builtin op. `Builtins.seed/2`
  # registers these under `Std.Builtin#<op>` (see `builtin_op_name/1` there), so a
  # reference must name the same owner — otherwise it only resolves through
  # `Env.resolve_key`'s base-scan fallback and a raw `env.defs` walk (the trust
  # ledger's) sees the def as unresolved.
  defp builtin_op_global(op), do: Cure.Elab.Name.qualify("Std.Builtin", op)

  # `.1`/`.2` lower to an application of the Std.Sigma projection global
  # (`sigma_first`/`sigma_second`), with the erased implicits `{a}`/`{b}` solved
  # from `inner`'s inferred `Sigma(a, b)` type by the implicit-insertion machinery.
  # `inner` is the SURFACE AST (not the already-lowered term) so the wrapper infers
  # it in the caller's context. Same `{:ok, term, result_type}` contract as before.
  defp sigma_projection(which, inner, names, ctx, env) do
    gname = if which == :fst, do: :sigma_first, else: :sigma_second
    elaborate_implicit_global_app(env, gname, [inner], names, ctx)
  end

  # `element(t, i)` is the dependent n-ary projection form iff called with exactly
  # two arguments and a STATIC positive-integer literal index — the only shape for
  # which the compile-time bounds check is meaningful. Any other `element(…)`
  # call falls through to ordinary name resolution. A visible definition named
  # `element` also wins, preserving ordinary local/import shadowing.
  defp element_projection?([_t_arg, {:literal, _meta, i}]) when is_integer(i) and i >= 1, do: true
  defp element_projection?(_), do: false

  # A `.N` attribute where `N` is a positive integer is a POSITIONAL projection
  # (`.1`, `.2`, …); anything else is a record field name.
  defp parse_positional_index(attr) do
    case Integer.parse(attr) do
      {i, ""} when i >= 1 -> {:ok, i}
      _ -> :error
    end
  end

  # Positional projection `base.i`. When `base` is a flat unit-terminated
  # telescope of arity `n` (a `Tuple(T1,…,Tn)` value, lowered to a flat BEAM
  # tuple), `.i` for `i ≥ 2` lowers to the `Std.Sigma` positional-projection
  # global `tproj_i` — typed at the true i-th component `Ti` and inlined to
  # `element(i, base)` (see sigma.cure). `.1` is `sigma_first` (correct for any
  # telescope). For a bare dependent pair (`Sigma(a, b)`, tail not `Unit`) or any
  # non-telescope, `.1`/`.2` keep their `sigma_first`/`sigma_second` meaning and
  # a higher index falls to the record path — exactly the pre-telescope behavior.
  # The classification is a heuristic over `base`'s inferred type; the kernel
  # re-checks the chosen `tproj_i` application against its real signature, so a
  # misclassification can only surface as a clean rejection, never unsoundness.
  defp positional_projection(i, inner, names, ctx, env) do
    case telescope_arity_of(inner, names, ctx, env) do
      {:telescope, n} when i <= n and i >= 2 ->
        elaborate_telescope_projection(i, inner, names, ctx, env)

      {:telescope, n} when i <= n ->
        sigma_projection(:fst, inner, names, ctx, env)

      # The arity is statically known and `i` is out of `[1, n]` — reject at
      # elaboration. A telescope carries its arity in its type, so an
      # out-of-bounds positional access (`t.9` / `element(t, 9)` on a 3-tuple)
      # is a compile-time error, never a runtime `element/2` crash.
      {:telescope, n} ->
        {:error, {:telescope_index_out_of_bounds, i, n}}

      _ ->
        case i do
          1 -> sigma_projection(:fst, inner, names, ctx, env)
          2 -> sigma_projection(:snd, inner, names, ctx, env)
          _ -> record_projection(inner, Integer.to_string(i), names, ctx, env)
        end
    end
  end

  # The `tprojN` result is inferable from the tuple's telescope, but ordinary
  # implicit insertion sees its erased component types only through a nested
  # Sigma codomain. In synthesis mode that used to leave the trailing `r`
  # metavariable unsolved, making `let x = tuple.2` spuriously check-only.
  # Read the already-inferred telescope once and supply the erased arguments
  # explicitly. These are ordinary canonical `Std.Sigma.tprojN` applications;
  # no projection or tuple type is special-cased in the kernel.
  defp elaborate_telescope_projection(i, inner, names, ctx, env) do
    sigma_fam = Inductive.builtin(env, :sigma)
    unit_ctor = unit_ctor_name(env)

    with {:ok, inner_term, type_value} <- elaborate_expr_typed(inner, names, ctx, env),
         type_term =
           type_value
           |> Quote.reify(Context.length(ctx), Context.signature(ctx))
           |> resplit_data(env),
         {:ok, components, tail} <-
           telescope_prefix(type_term, i, ctx, sigma_fam, unit_ctor, []) do
      name = Env.resolve_key(env, env.defs, :"tproj#{i}")
      args = components ++ [tail, inner_term]
      term = Enum.reduce(args, {:global, name}, fn argument, application -> {:app, application, argument} end)
      result_type = Enum.at(components, i - 1) |> Eval.eval(Context.env(ctx))
      {:ok, term, result_type}
    end
  end

  defp telescope_prefix(type, 0, _ctx, _sigma_fam, _unit_ctor, components),
    do: {:ok, Enum.reverse(components), type}

  defp telescope_prefix(type, remaining, ctx, sigma_fam, unit_ctor, components)
       when remaining > 0 do
    case Kernel.normalize(ctx, type) do
      {:data, ^sigma_fam, [domain, codomain], []} ->
        tail = Kernel.normalize(ctx, {:app, codomain, {:ctor, unit_ctor, []}})
        telescope_prefix(tail, remaining - 1, ctx, sigma_fam, unit_ctor, [domain | components])

      _ ->
        {:error, {:not_a_telescope_projection, remaining}}
    end
  end

  # `{:telescope, n}` when `inner`'s inferred type is a unit-terminated Σ
  # telescope of arity `n` (`Sigma(T1, … Sigma(Tn, Unit))`), else `:not_telescope`.
  defp telescope_arity_of(inner, names, ctx, env) do
    case elaborate_expr_typed(inner, names, ctx, env) do
      {:ok, _term, type_value} ->
        case Inductive.builtin(env, :sigma) do
          nil ->
            :not_telescope

          sigma_fam ->
            # `type_value` is a semantic VALUE (as returned by elaboration); read it
            # back to a Core term (family param/index split recovered via the sig)
            # before walking the Σ spine.
            type_term = Quote.reify(type_value, Context.length(ctx), Context.signature(ctx))
            count_tele(type_term, ctx, sigma_fam, unit_family_name(env), unit_ctor_name(env), 0)
        end

      _ ->
        :not_telescope
    end
  end

  # Walk the Σ spine, instantiating each codomain (non-dependent for a telescope,
  # so the applied argument is discarded) until a `Unit` terminator is reached.
  defp count_tele(type, ctx, sigma_fam, unit_fam, unit_ctor, n) do
    case Kernel.normalize(ctx, type) do
      {:data, ^sigma_fam, [_dom, cod], []} ->
        tail = Kernel.normalize(ctx, {:app, cod, {:ctor, unit_ctor, []}})
        count_tele(tail, ctx, sigma_fam, unit_fam, unit_ctor, n + 1)

      {:data, ^unit_fam, [], []} when n >= 1 ->
        {:telescope, n}

      _ ->
        :not_telescope
    end
  end

  # Record field projection `obj.field`. The object's type identifies its record
  # family; the field name is looked up in the (single) constructor's telescope —
  # whose argument names ARE the field names — and the projection is elaborated as a
  # one-branch `match obj | Rec(f0, …, fn) -> f_i` in checking mode, the field's own
  # type as the goal. The field type lives in the constructor frame `params ++
  # fields`; its parameter references are instantiated with the record value's
  # actual arguments (so `val : a` in `Box(Nat)` becomes `Nat`). A field type that
  # references an EARLIER FIELD (filled with the sentinel index below) is rejected —
  # a genuinely dependent record field, which projection does not yet support. A
  # field type that merely mentions the record PARAMETER at an abstract argument
  # (`eqs : a -> a -> Bool` on a dictionary `Eqs(a)` over a rigid `a`) is fine: it
  # is a legitimate context-open type, and the kernel re-checks the built `:case`.
  @proj_field_sentinel 1_000_000

  @doc """
  Public entry to project field `field` from the record-typed surface expression
  `inner`. Used by `Cure.Elab.Resolve` to pull an interface method off the
  in-scope dictionary parameter at an abstract (rigid-head) call site.
  """
  @spec project_record_field(term(), String.t(), [String.t()], Context.t(), Env.t()) ::
          {:ok, term(), term()} | {:error, term()}
  def project_record_field(inner, field, names, ctx, env),
    do: record_projection(inner, field, names, ctx, env)

  defp record_projection(inner, field, names, ctx, env) do
    with {:ok, _obj_term, obj_type} <- elaborate_expr_typed(inner, names, ctx, env) do
      case Quote.reify(obj_type, Context.length(ctx)) do
        {:data, rec, params, _indices} ->
          ctor = Inductive.get_ctor(env, rec)

          cond do
            is_nil(ctor) or ctor.name != rec ->
              {:error, {:projection_not_a_record, rec}}

            true ->
              fields = ctor.args
              idx = Enum.find_index(fields, fn {n, _t} -> Atom.to_string(n) == field end)

              # Instantiate the field's type in `params ++ fields`: the parameters
              # get the record's actual arguments, earlier-field slots get a
              # sentinel var (so a field-dependent field type is caught below).
              ftype =
                idx &&
                  Subst.instantiate(
                    elem(Enum.at(fields, idx), 1),
                    params ++ List.duplicate({:var, @proj_field_sentinel}, idx)
                  )

              cond do
                is_nil(idx) ->
                  {:error, {:unknown_field, rec, field, Enum.map(fields, &elem(&1, 0))}}

                mentions_prior_field?(ftype) ->
                  dependencies = dependent_record_field_names(fields, idx)
                  field_sites = Cure.Elab.SourceMetadata.record_field_sites(rec)

                  {:error,
                   {:source_context, {:dependent_record_projection, rec, field},
                    %{
                      record: rec,
                      projected_field: field,
                      dependent_fields: dependencies,
                      projected_field_declaration: Map.get(field_sites, field),
                      dependent_field_declarations: Map.take(field_sites, dependencies)
                    }}}

                true ->
                  binders = for i <- 0..(length(fields) - 1), do: {:variable, [scope: :local], "$proj#{i}"}

                  arm =
                    {:match_arm, [pattern: {:function_call, [name: Atom.to_string(rec)], binders}],
                     [Enum.at(binders, idx)]}

                  with {:ok, term} <- elaborate_match(inner, [arm], ftype, names, ctx, env) do
                    {:ok, term, Eval.eval(ftype, Context.env(ctx))}
                  end
              end
          end

        _ ->
          {:error, {:projection_non_record, field}}
      end
    end
  end

  # Does the term reference the prior-field sentinel index (`@proj_field_sentinel`,
  # substituted into earlier-field slots)? A `{:var, k}` at binder depth `d` is the
  # sentinel iff `k - d >= @proj_field_sentinel` — the sentinel is lifted by one per
  # binder crossed, so its distance from the current frame stays constant, while a
  # genuine context/parameter reference stays far below the threshold.
  defp mentions_prior_field?(term), do: mentions_prior_field?(term, 0)

  defp mentions_prior_field?({:var, k}, depth), do: k - depth >= @proj_field_sentinel

  defp mentions_prior_field?({:lam, _g, d, b}, depth),
    do: mentions_prior_field?(d, depth) or mentions_prior_field?(b, depth + 1)

  defp mentions_prior_field?({:pi, _g, d, c}, depth),
    do: mentions_prior_field?(d, depth) or mentions_prior_field?(c, depth + 1)

  defp mentions_prior_field?(tuple, depth) when is_tuple(tuple),
    do: tuple |> Tuple.to_list() |> Enum.any?(&mentions_prior_field?(&1, depth))

  defp mentions_prior_field?(list, depth) when is_list(list), do: Enum.any?(list, &mentions_prior_field?(&1, depth))
  defp mentions_prior_field?(_other, _depth), do: false

  defp dependent_record_field_names(fields, index) do
    previous = fields |> Enum.take(index) |> Enum.map(&elem(&1, 0)) |> Enum.reverse()
    {_name, type} = Enum.at(fields, index)

    type
    |> free_indices(0)
    |> Enum.filter(&(&1 < index))
    |> Enum.sort()
    |> Enum.map(&Enum.at(previous, &1))
    |> Enum.reject(&is_nil/1)
    |> Enum.map(&Atom.to_string/1)
  end

  defp attach_unary_operand_context({:error, reason}, operand, operator),
    do: {:error, attach_operator_operand_context(reason, operand, 0, operator)}

  defp attach_unary_operand_context(result, _operand, _operator), do: result

  @doc """
  Checking-mode elaboration for proof forms whose Core term depends on the
  expected type. Ordinary expressions fall back to infer-then-check.
  """
  @spec elaborate_expr_checked(term(), term(), [String.t()], Context.t(), Env.t()) ::
          {:ok, term()} | {:error, term()}
  def elaborate_expr_checked(
        {:unary_op, meta, [{:literal, literal_meta, value}]},
        expected_core,
        names,
        ctx,
        env
      )
      when is_integer(value) and value >= 0 do
    if Keyword.get(meta, :operator) == :- and Keyword.get(literal_meta, :subtype) == :integer and
         literal_protocol_available?(env) do
      spelling = "-" <> normalized_integer_spelling(Keyword.get(literal_meta, :exact_integer), value)
      elaborate_contextual_integer_literal(-value, spelling, expected_core, names, ctx, env)
    else
      elaborate_expr_checked_fallback(
        {:unary_op, meta, [{:literal, literal_meta, value}]},
        expected_core,
        names,
        ctx,
        env
      )
    end
  end

  def elaborate_expr_checked(
        {:unary_op, meta, [{:literal, literal_meta, value}]} = expression,
        expected_core,
        names,
        ctx,
        env
      )
      when is_float(value) do
    exact = Keyword.get(literal_meta, :exact_decimal)

    cond do
      Keyword.get(meta, :operator) == :- and float_expected?(expected_core, ctx) ->
        {:ok, {:float_lit, -abs(value)}}

      Keyword.get(meta, :operator) == :- and is_binary(exact) ->
        elaborate_contextual_decimal_literal(
          "-" <> String.trim_leading(exact, "-"),
          expected_core,
          names,
          ctx,
          env
        )

      true ->
        elaborate_expr_checked_fallback(expression, expected_core, names, ctx, env)
    end
  end

  def elaborate_expr_checked({:record_update, meta, children}, expected_core, names, ctx, env) do
    with {:ok, positional} <- desugar_record_update(meta, children, env),
         :ok <- validate_record_update_base(meta, children, names, ctx, env) do
      elaborate_expr_checked(positional, expected_core, names, ctx, env)
      |> attach_record_update_context(meta, children, env)
    else
      {:error, reason} ->
        attach_record_update_context({:error, reason}, meta, children, env)
    end
  end

  def elaborate_expr_checked({:function_call, meta, args}, expected_core, names, ctx, env) do
    name = Keyword.fetch!(meta, :name)
    atom = String.to_atom(name)
    # Resolve a qualified (`Std.Nat.S`) or bare-shadowed (`S` under a local `Nat`
    # shadow, present only as `:"Std.Nat#S"`) constructor to its registry key
    # (spec §3.3); a non-dotted, registry-present name maps to itself.
    cres = resolve_ctor_key(env, atom)
    ctor = Inductive.get_ctor(env, cres)
    {meta, args} = normalize_constructor_named_args(meta, args, ctor)
    expr = {:function_call, meta, args}

    cond do
      equation_named_call?(meta, env) ->
        with {:ok, term, _type} <- elaborate_equation_named_call(meta, args, names, ctx, env),
             :ok <- Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
          {:ok, term}
        end

      Keyword.get(meta, :record) ->
        case desugar_record_construction(meta, args, env) do
          {:ok, positional} ->
            elaborate_expr_checked(positional, expected_core, names, ctx, env)
            |> attach_record_field_context(meta, args, env)
            |> attach_record_context(meta, args, env)

          {:error, reason} ->
            attach_record_context({:error, reason}, meta, args, env)
        end

      name == "reflexive" and length(args) == 1 ->
        [arg] = args

        # Checking-mode `reflexive(x)` — see the infer-mode note above. Build the
        # inductive ctor and let the kernel check it against the expected type.
        with {:ok, arg_term, _type} <- elaborate_expr_typed(arg, names, ctx, env),
             reflexive = resolve_ctor_key(env, :reflexive),
             term = {:ctor, reflexive, [arg_term]},
             :ok <- Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
          {:ok, term}
        end

      Cure.Elab.Resolve.result_dispatched_method?(env, atom) ->
        Cure.Elab.Resolve.method_call_checked(env, atom, args, expected_core, names, ctx)

      Cure.Elab.Resolve.constrained?(env, atom) ->
        Cure.Elab.Resolve.constrained_call_checked(env, atom, args, expected_core, names, ctx)

      ctor ->
        # Checking-mode constructor: pin erased indices from the expected type (a
        # reconstructed dependent-match branch body like `prim()`/`seq(l,r)` whose
        # indices no present argument determines), then let the kernel re-check the
        # assembled constructor against the goal.
        #
        # Checking is goal-first: solve the constructor parameters from the
        # expected result, then check each present argument against its instantiated
        # field type. This is required even when standalone argument inference would
        # succeed with a DIFFERENT type — a numeral in `List(Bounded(3))` otherwise
        # defaults to `Int`, and the useful element goal is lost. If the result goal
        # cannot seed this constructor, retain the ordinary inference path as the
        # compatibility fallback. Either way the kernel re-checks below.
        result =
          case align_constructor_args(cres, ctor, meta, args) do
            {:error, _} = error ->
              error

            {:ok, aligned_args} ->
              bidirectional =
                profile_attempt_at(meta, expected_core, env, cres, :constructor_checked_bidirectional, fn ->
                  elaborate_ctor_app_bidirectional(env, cres, aligned_args, names, ctx, expected_core)
                end)

              case bidirectional do
                {:ok, _} = ok ->
                  ok

                {:error, _} = bidirectional_error ->
                  inferred =
                    profile_attempt_at(meta, expected_core, env, cres, :constructor_checked_infer, fn ->
                      with :ok <- validate_constructor_arity(env, cres, aligned_args, name),
                           {:ok, present} <- map_present_args(aligned_args, names, ctx, env),
                           {:ok, term, _type} <- elaborate_ctor_app(env, cres, present, ctx, expected_core) do
                        {:ok, term}
                      end
                    end)

                  case {inferred, bidirectional_error} do
                    {{:ok, _} = ok, _} ->
                      ok

                    {{:error, _} = orig, {:error, {:constructor_result_mismatch, details}}} ->
                      attach_constructor_result_mismatch(orig, details, meta, args)

                    {{:error, _} = orig, _} ->
                      attach_nested_constructor_context(orig, aligned_args, cres)
                  end
              end
          end

        case result do
          {:ok, term} ->
            case Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
              :ok -> {:ok, term}
              {:error, _} = err -> ctor_refinement_fallback(expr, expected_core, names, ctx, env, err)
            end

          {:error, _} = err ->
            ctor_refinement_fallback(expr, expected_core, names, ctx, env, err)
        end

      true ->
        # Non-constructor call in checking mode. Try the ordinary path first (infer
        # then re-check against the goal). When that fails specifically because a
        # call's implicit stayed unsolved AND we have a concrete expected type,
        # retry the application threading the expected return type in, so an
        # implicit determined by NEITHER argument — only by the return type — gets
        # solved (`mk : {a} -> {b} -> a -> Const(a, b)` at `-> Const(Nat, Bool)`
        # solves `b` from the goal). Additive: reached only after the ordinary path
        # errored with `:unsolved_metavariables`, and the retry surfaces that
        # original error if it too fails, so inference-position behaviour (no
        # expected type) is byte-for-byte unchanged.
        #
        # ONE goal-first pre-pass. This was three (`implicit_first`, `lambda_first`,
        # `union_first`) with byte-identical bodies and different guards, tried in
        # sequence — so a call satisfying two guards ran the same elaboration twice and
        # discarded the first result. Three guesses in a row is not a solving strategy;
        # they are a single rule, and the guard is their disjunction: when the goal can
        # inform solving, thread it in FROM THE START instead of inferring and re-checking.
        #
        # Each disjunct earns its place:
        #   * a concrete goal + an implicit def — an implicit determined by NEITHER
        #     argument, only by the return type (`mk : {a} -> {b} -> a -> Const(a, b)`
        #     at `-> Const(Nat, Bool)` solves `b` from the goal);
        #   * a lambda argument, whose domain the goal may fix.
        #
        # The former anonymous-union disjunct is GONE, not merged: an implicit def at a
        # concrete goal already covers it (a union goal that reaches here is a container
        # implicit — `Std.Map.put`'s `v` — so the first disjunct fires). It mattered only
        # because inferring a union-goal call SUCCEEDS but wrongly (solving `v := Int`
        # from the value argument), and a wrong-but-solved implicit is not
        # `:unsolved_metavariables`, so the retry below never fired. Threading the goal
        # first is what fixes that — and that is now the rule, not an exception to it.
        # Union INJECTION is untouched: it is a check-position coercion, not an ordering.
        #
        # Additive: falls back to the ordinary infer-then-check path on any failure, so
        # inference-position behaviour (no expected type) is unchanged.
        resolved = resolve_def_key(env, name, atom)

        # Partial application of an implicit-carrying def against a function-type
        # goal: eta-expand the missing explicit parameters into lambda binders —
        # `konst(7)` at `(Int) -> Int` becomes `fn(x) -> konst(7, x)`. The residual
        # binder domains come from the expected Π, reducing an under-saturated call
        # (which the saturating implicit paths reject with `:too_few_arguments`, or
        # mis-align the first explicit arg onto the leading implicit slot) to the
        # ordinary saturated path. Idris elaborates an under-applied function
        # checked against a function type exactly this way; the kernel re-checks the
        # synthesized lambda, so only eta-equivalent well-typed terms are accepted.
        overloaded? =
          not String.contains?(name, ".") and
            length(Cure.Elab.Resolution.overload_candidates(env, atom)) >= 2

        alignment =
          if overloaded?,
            do: {:ok, args},
            else: Cure.Elab.Overload.align(env, resolved, args, Keyword.get(meta, :arg_labels), call_label_opts(meta))

        case alignment do
          {:error, _} = error ->
            error

          {:ok, aligned_args} ->
            aligned_expr = {:function_call, meta, aligned_args}
            residual = residual_explicit_arity(env, resolved, length(aligned_args))

            if residual > 0 and match?({:pi, _, _, _}, Kernel.normalize(ctx, expected_core)) do
              elaborate_expr_checked(
                eta_expand_call(meta, aligned_args, residual),
                expected_core,
                names,
                ctx,
                env
              )
            else
              case elaborate_checked_call_saturated(
                     aligned_expr,
                     resolved,
                     expected_core,
                     aligned_args,
                     names,
                     ctx,
                     env
                   ) do
                {:error, reason} when is_tuple(reason) ->
                  if unresolved_call_reason?(reason),
                    do: {:error, attach_unresolved_call_context(reason, aligned_expr, env)},
                    else: {:error, reason}

                result ->
                  result
              end
            end
        end
    end
  end

  # A synthetic dictionary argument in checking position (the constrained-call
  # applicator's dictionary slot): build the instance's dictionary record value
  # and let the kernel check it against the expected `iface(head)` type.
  def elaborate_expr_checked({:dict_value, iface, head, type_value}, expected_core, names, ctx, env) do
    with {:ok, term, _type} <- Cure.Elab.Resolve.dict_value(env, iface, head, type_value, names, ctx),
         :ok <- Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
      {:ok, term}
    end
  end

  def elaborate_expr_checked({:rewrite_expr, meta, [proof_ast, body_ast]}, expected_core, names, ctx, env) do
    depth = Context.length(ctx)

    result =
      with {:ok, proof_term, proof_type} <- elaborate_expr_typed(proof_ast, names, ctx, env),
           {:ok, ty_value, a_value, b_value} <- Rewrite.eq_parts(proof_type, Context.signature(ctx)),
           ty = Kernel.normalize(ctx, Quote.reify(ty_value, depth)),
           a = Kernel.normalize(ctx, Quote.reify(a_value, depth)),
           b = Kernel.normalize(ctx, Quote.reify(b_value, depth)),
           normalized_expected = Kernel.normalize(ctx, expected_core),
           {:ok, build, body_expected} <- Rewrite.legacy_plan(proof_term, ty, a, b, normalized_expected),
           {:ok, body_term} <- elaborate_expr_checked(body_ast, body_expected, names, ctx, env),
           term = build.(body_term),
           :ok <- Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
        {:ok, term}
      end

    attach_rewrite_context(result, meta, proof_ast, body_ast)
  end

  def elaborate_expr_checked({:proof_chain, _meta, _children} = chain, expected_core, names, ctx, env) do
    with {:ok, term, _type} <- Cure.Elab.ProofChain.elaborate(chain, names, ctx, env),
         :ok <- Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
      {:ok, term}
    end
  end

  def elaborate_expr_checked({:simplify_command, meta, _rules}, _expected_core, _names, _ctx, _env),
    do: simplify_outside_justification(meta)

  # A `match` in nested expression position, in checking mode: the expected type
  # IS the result type its motive needs, so hand it straight to `elaborate_match`
  # (which builds the motive, refines indices per branch, and enforces coverage),
  # then let the kernel re-check the assembled `:case` — mirroring `:rewrite_expr`
  # above. Reached from `rewrite … in match …` (line ~151) and from nested arm
  # bodies (`elaborate_branch_body`). `let`-blocks are now handled in checking
  # mode (the `{:block, …}` clause below); inference-position inline match (no
  # expected type) stays unimplemented (a separate aux-function lift).
  def elaborate_expr_checked({:pattern_match, meta, [scrut | arms]}, expected_core, names, ctx, env)
      when is_list(meta) do
    if special_match_arms?(arms) do
      with {:ok, desugared} <- desugar_special_match(scrut, arms, Keyword.get(meta, :line, 0)) do
        elaborate_expr_checked(desugared, expected_core, names, ctx, env)
      end
    else
      case elaborate_match(scrut, arms, expected_core, names, ctx, env) do
        {:ok, term} ->
          case Kernel.check_with_branch_details(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
            :ok -> {:ok, term}
            {:error, _reason} = error -> error
          end

        {:error, _reason} = error ->
          if Keyword.get(meta, :induction) do
            Cure.Elab.Induction.wrap_match_error(error, meta, arms)
          else
            error
          end
      end
    end
  end

  # A `with <expr>` in checking-mode expression position — a nested with-clause
  # appearing as another with/match arm body. Mirrors the top-level with-body
  # (`declarations.ex` `elaborate_body`): `expected_core` is this position's
  # (already-refined) goal, so each nested level refines on top of the enclosing
  # branch's goal and with-abstractions compose. No original params are threaded
  # (LHS re-match is a top-level-only form), so `original_params` is empty.
  def elaborate_expr_checked({:with_abs, meta, [scrut | arms]}, expected_core, names, ctx, env) do
    proof = Keyword.get(meta, :proof)
    elaborate_with(scrut, arms, proof, expected_core, names, ctx, env, [])
  end

  # A semantic macro failure is a typed `Std.Syntax.Failure` value. The
  # computed-macro expansion pass recognizes this constructor after
  # normalization and turns it into the author-facing Diagnosis error.
  def elaborate_expr_checked({:macro_fail, meta, args}, expected_core, names, ctx, env) do
    with {:ok, term} <- elaborate_macro_failure(meta, args, names, ctx, env),
         :ok <- Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
      {:ok, term}
    end
  end

  # A `let x = e ⏎ body` block, in checking mode. There is no `:let` in Core, so
  # each binding is eliminated by *surface substitution* (`elaborate_let_block`):
  # every free `x` in the remaining statements is replaced by the rhs expression
  # `e`, then the substituted body is checked against the expected type. NOTE:
  # this INLINES `e` at each use (it does not build a `(λ x:T. body) e` redex), so
  # it does not bind-once — a caller wanting to avoid duplicating/re-evaluating a
  # complex `e` (e.g. a guarded match's scrutinee) cannot get that by routing
  # through here; it would need a real Core binder built directly. A rebinding of
  # `x` in a later statement is refused (would capture).
  def elaborate_expr_checked({:block, _meta, stmts}, expected_core, names, ctx, env) do
    elaborate_let_block(stmts, expected_core, names, ctx, env)
  end

  # `return e` in a checking position (e.g. an `if`/`match` branch tail): the
  # identity on `e`, checked against the expected type. See the inference clause.
  def elaborate_expr_checked({:early_return, _meta, [e]}, expected_core, names, ctx, env),
    do: elaborate_expr_checked(e, expected_core, names, ctx, env)

  # Dependent-pair introduction `%[a, b]` in checking mode. The expected type must
  # be the builtin inductive Sigma; elaborate `a` against its domain, then `b`
  # against the codomain APPLIED to `a` (the second Σ param `b_fn` is an arbitrary
  # term — lambda, global, or neutral — so the instantiated codomain is the
  # application `b_fn(a)` handed to the normalizer, NOT a binder-body substitution;
  # spec §2.2). Lowers to the ctor `mk_pair`; the kernel re-checks it. With no Sigma
  # family registered (a raw-`Env.empty()` elaboration), falls through to the
  # inference fallback, which builds the same `{:ctor, :mk_pair, …}`.
  # A tuple literal `%[e1, …, en]` (n ≥ 2) checked against a Σ-shaped goal. ONE
  # recursion (`check_tuple_against/5`) elaborates both the bare dependent pair
  # (`Sigma(x:T, U)` — the last element is the whole second component) AND the
  # unit-terminated telescope (`Tuple(T1,…,Tn)` = `Sigma(T1, … Sigma(Tn, Unit))` —
  # each element gets its own `mk_pair` cell, bottoming at `unit`). Which one is
  # produced is driven ENTIRELY by the goal's structure: whether a Σ layer's tail
  # bottoms at `Unit` (telescope) or at an ordinary type (bare). A non-Σ goal falls
  # through to the fallback exactly as the former arity-2 clause did.
  def elaborate_expr_checked({:tuple, _meta, elems} = expr, expected_core, names, ctx, env)
      when is_list(elems) and length(elems) >= 2 do
    sigma_fam = Inductive.builtin(env, :sigma)

    case Kernel.normalize(ctx, expected_core) do
      {:data, fam, [_dom, _b_fn], []} when fam == sigma_fam and not is_nil(sigma_fam) ->
        with {:ok, term} <- check_tuple_against(elems, expected_core, names, ctx, env),
             :ok <- Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
          {:ok, term}
        end

      _ ->
        elaborate_expr_checked_fallback(expr, expected_core, names, ctx, env)
    end
  end

  # Lambda in checking mode: the expected type supplies the parameter types the
  # surface leaves untyped. `fn(a, b) -> body` against `Π a. Π b. C` curries to
  # `λa. λb. body` — each parameter is bound at the corresponding domain and the
  # body checked against the final codomain. A lambda needs a known Π (Idris
  # likewise only *checks*, never *infers*, an unannotated lambda); one in an
  # inference position (e.g. a bare higher-order argument) still needs the
  # expected type routed to it, which is a separate bidirectional-application step.
  def elaborate_expr_checked({:lambda, meta, [body_expr]}, expected_core, names, ctx, env) do
    with {:ok, term} <-
           elaborate_lambda(Keyword.fetch!(meta, :params), body_expr, expected_core, names, ctx, env),
         :ok <- Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
      {:ok, term}
    end
  end

  # `if c then t else e` checked against the expected type: both branches are
  # checked at `expected_core` under a constant motive `λ_:Bool. expected_core`
  # (shifted past the fresh Bool binder). The kernel re-checks the assembled
  # `:case`, so nothing here is trusted.
  def elaborate_expr_checked({:conditional, _meta, [c, t, e]}, expected_core, names, ctx, env) do
    branch = fn expr ->
      if effect_goal?(expected_core, ctx),
        do: elaborate_effect_branch(expr, expected_core, names, ctx, env),
        else: elaborate_expr_checked(expr, expected_core, names, ctx, env)
    end

    case elaborate_expr_checked(c, bool_type_term(Context.signature(ctx)), names, ctx, env) do
      {:error, reason} ->
        {:error, attach_expectation_context(reason, c, :condition, :if, nil)}

      {:ok, c_core} ->
        case branch.(t) do
          {:error, reason} ->
            {:error, normalize_branch_check_error(reason, t, expected_core, names, ctx, env, :if, 0)}

          {:ok, t_core} ->
            case branch.(e) do
              {:error, reason} ->
                {:error, normalize_branch_check_error(reason, e, expected_core, names, ctx, env, :if, 1)}

              {:ok, e_core} ->
                {:ok, bool_case(c_core, expected_core, t_core, e_core, ctx)}
            end
        end
    end
  end

  # `pickup` in checked position: desugar to the nested conditional and check
  # it against the expected type (each branch body is checked at `expected_core`).
  def elaborate_expr_checked({:pickup, _meta, clauses}, expected_core, names, ctx, env) do
    with {:ok, desugared} <- desugar_pickup(clauses) do
      elaborate_expr_checked(desugared, expected_core, names, ctx, env)
    end
  end

  # A known `List(a)` goal makes every literal cell deterministic. Build the Core
  # spine directly instead of routing each generated `Cons`/`Nil` through global
  # name resolution, label alignment, constructor inference, and fallback.
  def elaborate_expr_checked({:list, meta, elements} = node, expected_core, names, ctx, env) do
    result =
      case Kernel.normalize(ctx, expected_core) do
        {:data, family, [element_type], []} ->
          if family == Inductive.builtin(env, :list) do
            check_list_literal(meta, elements, expected_core, element_type, names, ctx, env)
          else
            elaborate_expr_checked(desugar_list(node), expected_core, names, ctx, env)
          end

        _ ->
          elaborate_expr_checked(desugar_list(node), expected_core, names, ctx, env)
      end

    case result do
      {:error, reason} -> {:error, attach_collection_context(reason, elements)}
      other -> other
    end
  end

  # Map literal in checked position: desugar to the `put`/`new` chain and re-check
  # against the expected type. This is what lets an empty `%{}` (a bare `new()`
  # with nothing to pin its key/value metavariables in synthesis) solve them from
  # an expected `Map(k, v)`.
  def elaborate_expr_checked({:map, meta, pairs}, expected_core, names, ctx, env),
    do:
      elaborate_expr_checked(
        desugar_map(pairs, Keyword.get(meta, :line, 0)),
        expected_core,
        names,
        ctx,
        env
      )

  def elaborate_expr_checked({:string_interpolation, meta, segments}, expected_core, names, ctx, env),
    do:
      elaborate_expr_checked(
        desugar_interpolation(segments, Keyword.get(meta, :line, 0)),
        expected_core,
        names,
        ctx,
        env
      )

  # Type-directed compact-Nat literal: a non-negative integer literal checked
  # against the `Nat` family lowers to a compact `{:nat_lit, n}` — the surface
  # payoff of the compact-Nat kernel path, so a numeric literal at `Nat` (and
  # hence a `Bounded`/`Char` index) is one machine integer, not an `S`-tower. A
  # bare literal still defaults to `Int` in inference mode; only a `Nat`-checked
  # one becomes compact. Every other case defers to the ordinary checked path.
  def elaborate_expr_checked({:literal, meta, value} = expr, expected_core, names, ctx, env) do
    int? = Keyword.get(meta, :subtype) == :integer and is_integer(value) and value >= 0
    signed_int? = Keyword.get(meta, :subtype) == :integer and is_integer(value)
    literal_protocol = Keyword.get(meta, :literal_protocol)
    exact_integer = Keyword.get(meta, :exact_integer)
    string? = Keyword.get(meta, :subtype) == :string and is_binary(value)
    character? = Keyword.get(meta, :subtype) == :char and is_integer(value)
    atom? = Keyword.get(meta, :subtype) == :symbol and is_atom(value)
    bytes? = Keyword.get(meta, :subtype) == :bytes and is_list(value)
    exact_decimal = Keyword.get(meta, :exact_decimal)
    union_ctor = union_literal_ctor(meta, value, expected_core, ctx, env)

    cond do
      # A literal checked against a union that has that literal as a MEMBER is the
      # member's NULLARY constructor: the value is fully determined by the ctor, so
      # there is nothing to store.
      #
      # This must precede the `string?` branch — otherwise a `"north"` member would
      # be desugared to its List(Char) spine and never reach the injection.
      union_ctor != nil ->
        {:ok, {:ctor, union_ctor, []}}

      # A literal whose TYPE is a union member is an ordinary union injection,
      # not an attempt to invoke the literal protocol on the union itself. Infer
      # the literal's normal type first, then let the shared checked fallback
      # inject it. Exact literal members were handled by the nullary case above.
      union_goal?(expected_core) ->
        elaborate_expr_checked_fallback(expr, expected_core, names, ctx, env)

      # A string literal checks as its `List(Char)` desugaring (see the typed
      # clause), so the expected `List(Char)`/`String` type drives each char.
      string? and literal_protocol == :string_argument ->
        elaborate_expr_checked(desugar_string_characters(value, meta), expected_core, names, ctx, env)

      string? and scalar_literal_protocol_available?(env, :from_string_literal) ->
        elaborate_scalar_literal_protocol(
          :from_string_literal,
          "StringLiteral",
          literal_spelling(value),
          value,
          expected_core,
          names,
          ctx,
          env
        )

      string? ->
        elaborate_expr_checked(desugar_string(value, meta), expected_core, names, ctx, env)

      character? and literal_protocol == :character_argument ->
        elaborate_expr_checked_fallback(expr, expected_core, names, ctx, env)

      character? and scalar_literal_protocol_available?(env, :from_character_literal) ->
        elaborate_scalar_literal_protocol(
          :from_character_literal,
          "CharacterLiteral",
          {:literal, [subtype: :char, literal_protocol: :character_argument], value},
          value,
          expected_core,
          names,
          ctx,
          env
        )

      atom? and literal_protocol == :atom_argument ->
        elaborate_expr_checked_fallback(expr, expected_core, names, ctx, env)

      atom? and scalar_literal_protocol_available?(env, :from_atom_literal) ->
        elaborate_scalar_literal_protocol(
          :from_atom_literal,
          "AtomLiteral",
          {:literal, [subtype: :symbol, literal_protocol: :atom_argument], value},
          value,
          expected_core,
          names,
          ctx,
          env
        )

      # A byte binary literal checks as its `Std.Binary.of_bytes/1` desugaring.
      bytes? ->
        with {:ok, surface} <- desugar_bytes(value, Keyword.get(meta, :line, 0)) do
          elaborate_expr_checked(surface, expected_core, names, ctx, env)
        end

      signed_int? and refinement_return?(expected_core, ctx, env) ->
        elaborate_expr_checked_fallback(expr, expected_core, names, ctx, env)

      literal_protocol == :natural_argument and int? and nat_expected?(expected_core, ctx) ->
        {:ok, {:nat_lit, value}}

      literal_protocol == :integer_argument and signed_int? and int_expected?(expected_core, ctx) ->
        {:ok, {:int_lit, value}}

      not literal_protocol_available?(env) and int? and nat_expected?(expected_core, ctx) ->
        {:ok, {:nat_lit, value}}

      not literal_protocol_available?(env) and signed_int? and int_expected?(expected_core, ctx) ->
        {:ok, {:int_lit, value}}

      signed_int? and float_expected?(expected_core, ctx) ->
        {:ok, {:float_lit, value * 1.0}}

      # Contextual numerals are language-level conversions. A non-negative
      # spelling first asks `ExpressibleByNaturalLiteral`; if that expected type
      # has no natural implementation, it falls back to
      # `ExpressibleByIntegerLiteral`. Negative spellings use only the signed
      # interface. The selected total initializer returns `LiteralResult(t)`;
      # normalization must expose `LiteralValue(value)` or `InvalidLiteral` at
      # compile time, so no dictionary or conversion wrapper reaches emitted
      # runtime code.
      signed_int? and literal_protocol_available?(env) ->
        elaborate_contextual_integer_literal(
          value,
          exact_integer,
          expected_core,
          names,
          ctx,
          env
        )

      is_float(value) and float_expected?(expected_core, ctx) ->
        {:ok, {:float_lit, value}}

      is_float(value) and is_binary(exact_decimal) and decimal_literal_protocol_available?(env) ->
        elaborate_contextual_decimal_literal(exact_decimal, expected_core, names, ctx, env)

      true ->
        elaborate_expr_checked_fallback(expr, expected_core, names, ctx, env)
    end
  end

  # A proof-position hole: attempt auto-resolution. `expected_core` is the Core
  # goal at this slot. Soundness: ProofSearch only builds a term; the kernel
  # re-checks it. On `:none` (no candidate discharges the goal) the hole SURVIVES
  # as a first-class `{:hole, id}` — since holes are stuck neutrals (first-class
  # holes, Slice 1), the enclosing application evals to a stuck spine and
  # type-checks (the kernel accepts a hole at any goal), so the declined proof
  # becomes an inspectable hole that blocks codegen, exactly like a body-level
  # hole (declarations.ex hole clause), rather than a hard elaboration error.
  # The id is minted by the shared `Declarations.hole_id/2` scheme.
  def elaborate_expr_checked({:hole, meta, _}, expected_core, _names, ctx, env) do
    case Cure.Elab.ProofSearch.resolve(expected_core, ctx, env) do
      {:ok, term} -> {:ok, term}
      :none -> {:ok, {:hole, Cure.Elab.Declarations.hole_id(env, meta)}}
      {:error, _} = err -> err
    end
  end

  def elaborate_expr_checked({:variable, meta, name} = expr, expected_core, names, ctx, env) do
    case Keyword.get(meta, :induction_hypothesis) do
      %{recursive_fields: recursive_fields} ->
        with {:ok, term, available} <- elaborate_expr_typed(expr, names, ctx, env) do
          case Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
            :ok ->
              {:ok, term}

            {:error, cause} ->
              span =
                case Cure.MetaAST.Metadata.source_info(meta) do
                  %{whole: whole} -> whole
                  _ -> nil
                end

              {:error,
               {:induction_failed,
                %Cure.Diagnostic.InductionProblem{
                  kind: :mistyped_hypothesis,
                  hypothesis: name,
                  hypothesis_range: span,
                  recursive_fields: recursive_fields,
                  required: expected_core,
                  available: Quote.reify(available, Context.length(ctx), Context.signature(ctx)),
                  cause: cause
                }}}
          end
        end

      _ ->
        expected = Eval.eval(expected_core, Context.env(ctx))
        atom = String.to_atom(name)
        resolved = resolve_def_key(env, name, atom)
        residual = residual_explicit_arity(env, resolved, 0)
        implicit_global? = implicit_def?(env, resolved)

        case {name in names, expected} do
          # A bare reference to an implicit-carrying definition is a partial
          # application too.  Give it the same goal-directed eta expansion as
          # an authored under-saturated call: `no_next` at
          # `(Bounded(n)) -> List(State(n))` becomes
          # `fn(state) -> no_next(state)`, allowing the call elaborator to solve
          # the hidden `n` from the expected function type.  Inferring the bare
          # global first leaves its leading `{n : Nat}` in the Pi telescope and
          # the kernel then compares that domain with `Bounded(n)`, producing the
          # misleading `Expected Nat, Found Bounded(n)` seen by Std.Regex.
          # Locals still shadow globals, and the synthesized term is kernel
          # checked through the ordinary lambda/call paths.
          {false, {:vpi, _, _, _}} when residual > 0 and implicit_global? ->
            call_meta = Keyword.put(meta, :name, name)

            elaborate_expr_checked(
              eta_expand_call(call_meta, [], residual),
              expected_core,
              names,
              ctx,
              env
            )

          {false, {:vtype, _level}} ->
            case resolve_type_free(name, env) do
              {:ok, term} ->
                case Kernel.check(ctx, term, expected) do
                  :ok -> {:ok, term}
                  {:error, _} -> elaborate_expr_checked_fallback(expr, expected_core, names, ctx, env)
                end

              :error ->
                elaborate_expr_checked_fallback(expr, expected_core, names, ctx, env)
            end

          _ ->
            elaborate_expr_checked_fallback(expr, expected_core, names, ctx, env)
        end
    end
  end

  def elaborate_expr_checked(expr, expected_core, names, ctx, env),
    do: elaborate_expr_checked_fallback(expr, expected_core, names, ctx, env)

  defp attach_rewrite_context({:error, {:source_context, _, _}} = error, _meta, _proof, _body), do: error

  defp attach_rewrite_context({:error, reason}, meta, proof_ast, body_ast)
       when reason == :rewrite_proof_not_equality or
              (is_tuple(reason) and elem(reason, 0) == :rewrite_no_match) do
    {:error, {:source_context, reason, rewrite_source_context(meta, proof_ast, body_ast)}}
  end

  defp attach_rewrite_context(result, _meta, _proof, _body), do: result

  defp rewrite_source_context(meta, proof_ast, body_ast) do
    source_info = Cure.MetaAST.Metadata.source_info(meta)
    opener_span = if(source_info, do: source_info.opener || source_info.whole)
    body_span = surface_expression_span(body_ast)

    %{
      span: rewrite_span(opener_span, body_span),
      opener_span: opener_span,
      proof_span: surface_expression_span(proof_ast),
      body_span: body_span,
      expectation_origin: :rewrite,
      expression_category: :rewrite_expr
    }
  end

  defp rewrite_span(%Cure.Diagnostic.Span{} = opener, %Cure.Diagnostic.Span{} = body) do
    %Cure.Diagnostic.Span{
      opener
      | end_byte: body.end_byte,
        end_line: body.end_line,
        end_column: body.end_column
    }
  end

  defp rewrite_span(opener, _body), do: opener

  defp attach_expectation_context({:source_context, reason, context}, expression, origin, owner, index)
       when is_map(context) do
    {:source_context, reason, Map.merge(context, expectation_context(expression, origin, owner, index))}
  end

  defp attach_expectation_context(reason, expression, origin, owner, index) do
    {:source_context, reason, expectation_context(expression, origin, owner, index)}
  end

  # A conditional checks each branch against one shared result type. Constructor
  # syntax can make a perfectly valid branch fail that check at a low level as
  # `:foreign_ctor` (notably String, which elaborates to the List constructors
  # Nil/Cons). At this boundary that is a branch-type mismatch, not a name error.
  #
  # Infer the branch independently after the failed check. If it is valid on its
  # own, report its actual type against the branch goal through the contextual
  # E093 route. If independent inference also fails, preserve that authored
  # branch error instead of hiding it behind a synthetic mismatch.
  defp normalize_branch_check_error(reason, expression, expected_core, names, ctx, env, owner, index) do
    normalized_reason =
      case elaborate_expr_typed(expression, names, ctx, env) do
        {:ok, _term, actual_type} ->
          actual_core = Quote.reify(actual_type, Context.length(ctx), Context.signature(ctx))
          actual_diagnostic = diagnostic_type_alias(expression, actual_core, ctx, env)
          expected_diagnostic = diagnostic_type_alias(nil, expected_core, ctx, env)
          {:cannot_unify, actual_diagnostic, expected_diagnostic}

        {:error, _independent_reason} ->
          reason
      end

    attach_expectation_context(normalized_reason, expression, :branch, owner, index)
  end

  defp diagnostic_type_alias(expression, core, ctx, env) do
    alias_name =
      case expression do
        {:literal, _meta, value} when is_binary(value) -> resolve_typealias_name(env, :String)
        _ -> typealias_head(core, env)
      end

    case alias_name && Env.get_def(env, alias_name) do
      %{typealias: true, body: body} ->
        original = Cure.Core.Normalise.nf(ctx, body)
        {:diagnostic_alias, Cure.Elab.Name.base(alias_name), original}

      _ ->
        core
    end
  end

  defp typealias_head({:global, name}, env) do
    case Env.get_def(env, name) do
      %{typealias: true} -> name
      _ -> nil
    end
  end

  defp typealias_head(_core, _env), do: nil

  defp resolve_typealias_name(env, name) do
    case Env.get_def(env, name) do
      %{typealias: true, name: resolved} -> resolved
      _ -> nil
    end
  end

  defp expectation_context(expression, origin, owner, index) do
    span = surface_expression_span(expression)

    %{
      line: span && span.start_line,
      column: span && span.start_column,
      length: span && max(1, span.end_byte - span.start_byte),
      span: span,
      expectation_span: span,
      checking: owner,
      expression_category: expression_category(expression),
      expectation_origin: origin,
      argument_index: index
    }
  end

  defp attach_variable_context(reason, meta, name),
    do: {:source_context, reason, variable_context(meta, name)}

  defp variable_context(meta, name) do
    expression = {:variable, meta, name}
    expectation_context(expression, :annotation, name, nil)
  end

  defp attach_collection_context({:source_context, reason, context}, elements)
       when is_map(context) do
    case collection_offender(reason, elements) do
      {element, index} ->
        {:source_context, reason, Map.merge(context, expectation_context(element, :collection, :list, index))}

      nil ->
        {:source_context, reason, context}
    end
  end

  defp attach_collection_context(reason, elements) do
    case collection_offender(reason, elements) do
      {element, index} -> {:source_context, reason, expectation_context(element, :collection, :list, index)}
      nil -> reason
    end
  end

  defp collection_offender({:source_context, reason, _context}, elements),
    do: collection_offender(reason, elements)

  defp collection_offender({:index_mismatch, {:cannot_unify, actual, expected}}, elements) do
    collection_type_offender(elements, actual, expected)
  end

  defp collection_offender({:cannot_unify, actual, expected}, elements) do
    collection_type_offender(elements, actual, expected)
  end

  defp collection_offender(_reason, _elements), do: nil

  defp collection_type_offender(elements, actual, expected) do
    elements
    |> Enum.with_index()
    |> Enum.reverse()
    |> Enum.find(fn {element, _index} ->
      literal_matches_type?(element, actual) or literal_matches_type?(element, expected)
    end)
  end

  defp literal_matches_type?({:literal, _meta, value}, type) when is_boolean(value),
    do: type_family?(type, "Bool")

  defp literal_matches_type?({:literal, _meta, value}, type) when is_integer(value),
    do: type_family?(type, "Int") or type_family?(type, "Nat")

  defp literal_matches_type?({:literal, _meta, value}, type) when is_float(value),
    do: type_family?(type, "Float")

  defp literal_matches_type?(_element, _type), do: false

  defp type_family?({:data, name, _params, _indices}, suffix),
    do: String.ends_with?(Atom.to_string(name), "##{suffix}")

  defp type_family?(_type, _suffix), do: false

  defp attach_record_field_context({:error, reason}, meta, field_pairs, env),
    do: {:error, attach_record_field_reason(reason, meta, field_pairs, env)}

  defp attach_record_field_context(result, _meta, _field_pairs, _env), do: result

  # A record literal is a semantic shape boundary. Keep a more precise field
  # or constructor-argument producer when one was identified, but give a
  # whole-record failure the authored record expression and its declared name.
  defp attach_record_context(
         {:error, {:source_context, _reason, %{expectation_origin: origin} = _context}} = result,
         _meta,
         _args,
         _env
       )
       when origin in [:record_field, :constructor_argument],
       do: result

  defp attach_record_context({:error, {:source_context, reason, context}}, meta, args, env)
       when is_map(context),
       do: {:error, {:source_context, reason, Map.merge(record_context(meta, args, env), context)}}

  defp attach_record_context({:error, reason}, meta, args, env),
    do: {:error, {:source_context, reason, record_context(meta, args, env)}}

  defp attach_record_context(result, _meta, _args, _env), do: result

  defp record_context(meta, args, env) do
    expression = {:function_call, meta, args}

    expectation_context(expression, :record, Keyword.get(meta, :name, :record), nil)
    |> Map.put(:field_spans, record_field_spans(meta))
    |> Map.put(:available_records, available_record_names(env))
    |> Map.merge(record_delimiter_context(meta))
  end

  defp record_field_spans(meta) do
    case Cure.MetaAST.Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{fields: fields} when is_map(fields) -> fields
      _ -> %{}
    end
  end

  defp attach_record_update_context({:error, {:source_context, reason, context}}, meta, children, env)
       when is_map(context) do
    field_result = attach_record_field_context({:error, {:source_context, reason, context}}, meta, tl(children), env)

    case field_result do
      {:error, {:source_context, _reason, %{expectation_origin: :record_field} = _field_context}} ->
        field_result

      {:error, {:source_context, _reason, field_context}} ->
        {:error,
         {:source_context, reason, Map.merge(field_context, record_update_context(meta, children, context, env))}}
    end
  end

  defp attach_record_update_context({:error, reason}, meta, children, env),
    do: {:error, {:source_context, reason, record_update_context(meta, children, %{}, env)}}

  defp attach_record_update_context(result, _meta, _children, _env), do: result

  defp record_update_context(meta, children, context, env) do
    expression = {:record_update, meta, children}

    Map.merge(context, expectation_context(expression, :record_update, Keyword.get(meta, :name, :record_update), nil))
    |> Map.put(:field_spans, record_field_spans(meta))
    |> Map.put(:available_records, available_record_names(env))
    |> Map.merge(record_delimiter_context(meta))
    |> Map.put(:base_span, children |> List.first() |> surface_expression_span())
  end

  defp record_delimiter_context(meta) do
    case Cure.MetaAST.Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{} = info ->
        %{record_name_span: info.name, opener_span: info.opener, closer_span: info.closer}

      _ ->
        %{}
    end
  end

  defp attach_record_field_reason({:source_context, reason, context}, meta, field_pairs, env)
       when is_map(context) do
    case record_field_context(meta, field_pairs, context, env) do
      nil -> {:source_context, reason, context}
      details -> {:source_context, reason, Map.merge(context, details)}
    end
  end

  defp attach_record_field_reason(reason, meta, field_pairs, env) do
    case record_field_context(meta, field_pairs, %{}, env) do
      nil -> reason
      details -> {:source_context, reason, details}
    end
  end

  defp record_field_context(meta, field_pairs, context, env) do
    index = Map.get(context, :argument_index) || singleton_record_field_index(field_pairs)
    name = Keyword.get(meta, :name)
    ctor = name && Inductive.get_ctor(env, String.to_atom(name))

    with index when is_integer(index) <- index,
         %{args: fields} <- ctor,
         {field, _type} <- Enum.at(fields, index),
         {:ok, value} <- fetch_record_field_value(field_pairs, field),
         %Cure.Diagnostic.Span{} = span <- surface_expression_span(value) do
      %{
        line: span.start_line,
        column: span.start_column,
        length: max(1, span.end_byte - span.start_byte),
        span: span,
        expectation_span: span,
        checking: field,
        expectation_origin: :record_field,
        argument_index: index
      }
    else
      _ -> nil
    end
  end

  defp fetch_record_field_value(field_pairs, field) do
    Enum.find_value(field_pairs, :error, fn
      {:pair, _meta, [{:literal, _label_meta, value_field}, value]}
      when value_field == field ->
        {:ok, value}

      _ ->
        false
    end)
  end

  defp singleton_record_field_index([{:pair, _meta, [_label, _value]}]), do: 0
  defp singleton_record_field_index(_field_pairs), do: nil

  # The saturated (or non-function-goal) checking-mode path for a non-constructor
  # call: try the goal-first pre-pass when the goal can inform implicit solving,
  # otherwise infer-then-recheck. Split out of the `true ->` branch of
  # `elaborate_expr_checked({:function_call,...})` so the eta-expansion path can
  # share `resolved` without duplicating this block. Defined here (after the
  # `elaborate_expr_checked/5` clause group) so those clauses stay grouped.
  defp elaborate_checked_call_saturated(
         {:function_call, meta, _} = expr,
         resolved,
         expected_core,
         args,
         names,
         ctx,
         env
       ) do
    profile_named_call(meta, expected_core, env, fn ->
      elaborate_checked_call_saturated_profiled(expr, resolved, expected_core, args, names, ctx, env)
    end)
  end

  defp elaborate_checked_call_saturated_profiled(expr, resolved, expected_core, args, names, ctx, env) do
    concrete_goal? = not Unify.has_meta?(expected_core)

    goal_first? =
      (concrete_goal? and implicit_def?(env, resolved)) or
        (concrete_goal? and Enum.any?(args, &call_placeholder?/1) and Map.has_key?(env.defs, resolved)) or
        (Enum.any?(args, &match?({:lambda, _m, _b}, &1)) and Map.has_key?(env.defs, resolved))

    goal_first =
      if goal_first? do
        case elaborate_global_app_expected(env, resolved, args, names, ctx, expected_core) do
          {:ok, term, _type} ->
            case Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
              :ok -> {:ok, term}
              {:error, _} -> nil
            end

          {:error, _} ->
            nil
        end
      end

    # No post-hoc retry. There used to be one here, firing on
    # `:unsolved_metavariables` under the guard `implicit_def?(resolved) and not
    # has_meta?(expected_core)` — which is EXACTLY the first disjunct of
    # `goal_first?` above. Whenever it fired, the identical
    # `elaborate_global_app_expected` had therefore already run and failed, so it
    # could only fail again. It was dead the moment the goal-first pre-pass was
    # introduced, and stayed in the file because each new attempt was bolted on in
    # front of the previous one instead of replacing it. Solving happens once, up
    # front, where the goal is known.
    goal_first || elaborate_expr_checked_fallback(expr, expected_core, names, ctx, env)
  end

  # Recursively elaborate a run of surface tuple elements against a Σ-shaped goal,
  # peeling ONE Σ layer per element. Distinguishes two terminations:
  #
  #   * telescope terminator — the current Σ's tail bottoms at `Unit`
  #     (`telescope_terminator?/3`): the element inhabits the Σ's *domain* and a
  #     trailing `unit` closes the spine, so `%[…,e]` against `Sigma(D, λ_.Unit)`
  #     becomes `mk_pair(check(e,D), unit)`. This is how `Tuple(T1,…,Tn)` builds a
  #     flat, unit-terminated HList that emit later flattens to a BEAM tuple.
  #
  #   * bare dependent pair — the tail is an ordinary type: the LAST element is the
  #     whole second component, so `%[a,b]` against `Sigma(D, Cod)` checks `b` at
  #     `Cod[a]` directly (no `unit`). Preserves the landed `Sigma(x:T,U)` ABI.
  #
  # An empty run against `Unit` yields `unit` (the telescope terminator itself).
  defp check_tuple_against([], expected_core, _names, ctx, env) do
    unit_family = unit_family_name(env)

    case Kernel.normalize(ctx, expected_core) do
      {:data, ^unit_family, [], []} -> {:ok, {:ctor, unit_ctor_name(env), []}}
      other -> {:error, {:tuple_arity_mismatch, :expected_more, other}}
    end
  end

  defp check_tuple_against(elements, expected_core, names, ctx, env),
    do: check_tuple_against(elements, expected_core, names, ctx, env, 0)

  defp check_tuple_against([], expected_core, _names, ctx, env, _index),
    do: check_tuple_against([], expected_core, [], ctx, env)

  defp check_tuple_against([e | rest], expected_core, names, ctx, env, index) do
    sigma_fam = Inductive.builtin(env, :sigma)

    case Kernel.normalize(ctx, expected_core) do
      {:data, fam, [dom, b_fn], []} when fam == sigma_fam and not is_nil(sigma_fam) ->
        if rest == [] and not telescope_terminator?(b_fn, ctx, env) do
          # Last element, tail is an ordinary type → e IS the whole second
          # component (a bare pair, possibly itself a nested tuple).
          case elaborate_expr_checked(e, expected_core, names, ctx, env) do
            {:error, reason} ->
              {:error, attach_expectation_context(reason, e, :element, :tuple, index)}

            ok ->
              ok
          end
        else
          [%{name: mk_pair} | _] = Inductive.ctors_of(env, sigma_fam)

          case elaborate_expr_checked(e, dom, names, ctx, env) do
            {:error, reason} ->
              {:error, attach_expectation_context(reason, e, :element, :tuple, index)}

            {:ok, e_term} ->
              cod_inst = Kernel.normalize(ctx, {:app, b_fn, e_term})

              case check_tuple_against(rest, cod_inst, names, ctx, env, index + 1) do
                {:ok, rest_term} -> {:ok, {:ctor, mk_pair, [e_term, rest_term]}}
                error -> error
              end
          end
        end

      other ->
        # Goal is not a Σ: only a single remaining element can inhabit it directly
        # (the bare final component of a 2-tuple). More than one is an arity error.
        if rest == [] do
          case elaborate_expr_checked(e, expected_core, names, ctx, env) do
            {:error, reason} ->
              {:error, attach_expectation_context(reason, e, :element, :tuple, index)}

            ok ->
              ok
          end
        else
          {:error, {:tuple_arity_mismatch, :too_many, other}}
        end
    end
  end

  # Does this Σ's second parameter (a `λ`) bottom at `Unit`? Applying it to a
  # closed probe term and normalizing β-reduces a non-dependent tail to its body;
  # a dependent tail that mentions its argument won't reduce to `Unit` anyway. This
  # is the sole signal separating a telescope layer from a bare dependent pair.
  defp telescope_terminator?(b_fn, ctx, env) do
    unit_family = unit_family_name(env)

    case Kernel.normalize(ctx, {:app, b_fn, {:ctor, unit_ctor_name(env), []}}) do
      {:data, ^unit_family, [], []} -> true
      _ -> false
    end
  end

  # True iff the (meta-free) expected type evaluates to the canonical `Nat` family.
  defp elaborate_contextual_integer_literal(value, spelling, expected_core, names, ctx, env)
       when value >= 0 do
    argument = {:natural_argument, normalized_integer_spelling(spelling, value)}

    case elaborate_literal_protocol(:from_natural_literal, argument, value, expected_core, names, ctx, env) do
      {:error, {:no_instance, :ExpressibleByNaturalLiteral, _}} ->
        integer_argument = {:integer_argument, normalized_integer_spelling(spelling, value)}

        case elaborate_literal_protocol(
               :from_integer_literal,
               integer_argument,
               value,
               expected_core,
               names,
               ctx,
               env
             ) do
          {:error, {:no_instance, :ExpressibleByIntegerLiteral, _}} ->
            elaborate_bounded_literal_fallback(value, expected_core, ctx, env)

          result ->
            result
        end

      result ->
        result
    end
  end

  defp elaborate_contextual_integer_literal(value, spelling, expected_core, names, ctx, env),
    do:
      elaborate_literal_protocol(
        :from_integer_literal,
        {:integer_argument, normalized_integer_spelling(spelling, value)},
        value,
        expected_core,
        names,
        ctx,
        env
      )

  # One rule, shared with example-pin comparison — see
  # `Cure.MetaAST.Metadata.integer_spelling/2` for why a spelling-less literal's
  # canonical digits are the decimal rendering of its value.
  defp normalized_integer_spelling(spelling, value),
    do: Cure.MetaAST.Metadata.integer_spelling(spelling, value)

  # Prelude bootstrap modules are elaborated before the literal interfaces can
  # be ambiently imported. Preserve the ordinary infer-and-convert path there;
  # once the provider is in scope every contextual numeral routes through the
  # language-level protocols below.
  defp literal_protocol_available?(env) do
    result_family = Env.resolve_key(env, env.families, :LiteralResult)

    Map.has_key?(env.families, result_family) and
      Cure.Elab.Resolve.method?(env, :from_integer_literal) and
      Cure.Elab.Resolve.method?(env, :from_natural_literal)
  end

  defp decimal_literal_protocol_available?(env),
    do: Cure.Elab.Resolve.method?(env, :from_decimal_literal)

  defp scalar_literal_protocol_available?(env, method),
    do: Cure.Elab.Resolve.method?(env, method)

  defp elaborate_contextual_decimal_literal(exact, expected_core, names, ctx, env) do
    descriptor = {:function_call, [name: "DecimalLiteral"], [literal_spelling(exact)]}

    elaborate_literal_protocol(
      :from_decimal_literal,
      {:decimal_argument, descriptor},
      exact,
      expected_core,
      names,
      ctx,
      env
    )
  end

  defp elaborate_scalar_literal_protocol(
         method,
         constructor,
         value_ast,
         display,
         expected_core,
         names,
         ctx,
         env
       ) do
    descriptor = {:function_call, [name: constructor], [value_ast]}

    elaborate_literal_protocol(
      method,
      {:descriptor_argument, descriptor},
      display,
      expected_core,
      names,
      ctx,
      env
    )
  end

  # Compatibility for indexed `Bounded(n)` until coherence keys retain indices
  # (today every `Bounded(n)` implementation shares the `Bounded` head).
  # Arbitrary bounds keep the existing compact representation and delegate their
  # range proof to the kernel instead of materializing a constructor tower.
  #
  # `Char` lands here too, and deliberately. It is a constructor-less nominal
  # carrier whose SOLE introduction form is the kernel's compact-literal rule
  # (`Kernel.check/3` on `{:bounded_lit, k}`, which re-derives the Unicode scalar
  # ceiling itself). A user-space `ExpressibleByNaturalLiteral for Char` cannot
  # stand in for that rule: any such instance has to turn an `Int` into a `Char`,
  # and every route from `Int` to `Char` is an `@extern` postulate with no body,
  # so the initializer never reduces to a compile-time value — `fn c() -> Char =
  # 12` failed with `literal_initializer_not_compile_time_value` rather than
  # producing a character. Introducing builtin scalars from the elaborator's own
  # rule (as Idris and Lean do for `Char`) instead of from a protocol instance is
  # what makes the literal work at all, and it keeps the ceiling in the one place
  # the kernel already enforces it.
  defp elaborate_bounded_literal_fallback(value, expected_core, ctx, _env) do
    expected = Eval.eval(expected_core, Context.env(ctx))

    case Kernel.check(ctx, {:bounded_lit, value}, expected) do
      :ok ->
        {:ok, {:bounded_lit, value}}

      {:error, {:bounded_lit_out_of_range, _value, _bound}} = error ->
        error

      {:error, {:char_literal_out_of_range, _value}} = error ->
        error

      {:error, {:bounded_bound_not_concrete, _bound}} = error ->
        error

      {:error, _not_a_bounded_or_char_domain} ->
        case Kernel.check(ctx, {:int_lit, value}, expected) do
          :ok -> {:ok, {:int_lit, value}}
          {:error, reason} -> {:error, reason}
        end
    end
  end

  defp elaborate_literal_protocol(method, argument_kind, value, expected_core, names, ctx, env) do
    result_family = Env.resolve_key(env, env.families, :LiteralResult)
    literal_ctx = literal_normalization_context(ctx, env)

    if Map.has_key?(env.families, result_family) and Cure.Elab.Resolve.method?(env, method) do
      result_type = {:data, result_family, [expected_core], []}
      argument = literal_protocol_argument(argument_kind, value)
      value_ctor = resolve_ctor_key(env, :LiteralValue)
      invalid_ctor = resolve_ctor_key(env, :InvalidLiteral)

      with {:ok, conversion} <-
             Cure.Elab.Resolve.method_call_checked(
               env,
               method,
               [argument],
               result_type,
               names,
               literal_ctx
             ) do
        case Normalise.nf(literal_ctx, conversion, delta: :certified, fuel: 5_000_000) do
          {:ctor, ^value_ctor, [literal]} ->
            case Kernel.check(
                   literal_ctx,
                   literal,
                   Eval.eval(expected_core, Context.env(literal_ctx))
                 ) do
              :ok -> {:ok, literal}
              {:error, reason} -> {:error, {:invalid_literal_implementation, method, reason}}
            end

          {:ctor, ^invalid_ctor, []} ->
            {:error, {:literal_out_of_range, method, value, expected_core}}

          other ->
            {:error, {:literal_initializer_not_compile_time_value, method, other}}
        end
      end
    else
      iface =
        case method do
          :from_natural_literal -> :ExpressibleByNaturalLiteral
          :from_integer_literal -> :ExpressibleByIntegerLiteral
          :from_decimal_literal -> :ExpressibleByDecimalLiteral
          :from_string_literal -> :ExpressibleByStringLiteral
          :from_character_literal -> :ExpressibleByCharacterLiteral
          :from_atom_literal -> :ExpressibleByAtomLiteral
        end

      {:error, {:no_instance, iface, expected_core}}
    end
  end

  # Temporary 0.34 bridge. Name resolution already used `env`; literal
  # normalization must see that same canonical world rather than the older
  # snapshot retained by `ctx.signature`. The module-system follow-up replaces
  # both with one CompilationWorld and removes this helper.
  defp literal_normalization_context(ctx, env), do: %{ctx | signature: env}

  defp literal_protocol_argument({:decimal_argument, descriptor}, _value), do: descriptor

  defp literal_protocol_argument({:descriptor_argument, descriptor}, _value), do: descriptor

  defp literal_protocol_argument({:natural_argument, spelling}, value) do
    {:function_call, [name: "NaturalLiteral"],
     [
       literal_spelling(spelling),
       {:literal, [subtype: :integer, literal_protocol: :natural_argument], value}
     ]}
  end

  defp literal_protocol_argument({:integer_argument, spelling}, value) do
    {:function_call, [name: "IntegerLiteral"],
     [
       literal_spelling(spelling),
       {:literal, [subtype: :integer, literal_protocol: :integer_argument], value}
     ]}
  end

  defp literal_protocol_argument(argument_kind, value),
    do: {:literal, [subtype: :integer, literal_protocol: argument_kind], value}

  # The `spelling`/`value` text a literal descriptor carries is declared `List(Char)`
  # — the decoded code points, deliberately independent of however `Std.String`
  # stores its characters, so a user's `from_natural_literal` can read digits
  # without depending on that record. Emit the character list itself rather than a
  # string literal: a bare string literal constructs the nominal `String`, and it
  # did so here whenever the descriptor's field was elaborated in inference mode,
  # which is a `String` where a `List(Char)` was declared. These are already-decoded
  # descriptor characters rather than fresh authored literals, so tag them for the
  # canonical `Char` introduction path instead of recursively invoking
  # `ExpressibleByCharacterLiteral` once per code point.
  defp literal_spelling(text) when is_binary(text),
    do: desugar_string_characters(text, [], literal_protocol: :character_argument)

  defp nat_expected?(expected_core, ctx) do
    sig = Context.signature(ctx)
    nat_fid = Cure.Core.Inductive.builtin(sig, :nat)

    not is_nil(nat_fid) and not Unify.has_meta?(expected_core) and
      match?({:vdata, ^nat_fid, []}, Eval.eval(expected_core, Context.env(ctx)))
  end

  defp int_expected?(expected_core, ctx) do
    sig = Context.signature(ctx)
    int_fid = Cure.Core.Inductive.builtin(sig, :int)

    not is_nil(int_fid) and not Unify.has_meta?(expected_core) and
      match?({:vdata, ^int_fid, []}, Eval.eval(expected_core, Context.env(ctx)))
  end

  defp float_expected?(expected_core, ctx) do
    not Unify.has_meta?(expected_core) and
      match?({:vfloat_type}, Eval.eval(expected_core, Context.env(ctx)))
  end

  # The type of every character literal. `Std.Char` declares `Char` as a nominal
  # carrier — no longer a `Bounded(0x110000)` synonym — so where that module is in
  # scope a character literal IS a `Char` and nothing else; an arbitrary bounded
  # value can no longer pass for one. The kernel admits the same compact
  # `{:bounded_lit, k}` value at either family, so this only decides which type the
  # literal announces, not how it is represented.
  #
  # `Bounded(0x110000)` remains the fallback for a universe compiled without
  # `Std.Char` (the bound 0x110000 = 1_114_112 is intrinsic to a code point, not
  # read from context). `:no_bounded` when neither family is registered, so the
  # caller reports a fix-naming error rather than crashing.
  defp char_type_value(sig) do
    case Inductive.builtin(sig, :char) do
      nil ->
        case Inductive.builtin(sig, :bounded) do
          nil -> :no_bounded
          fid -> {:ok, {:vdata, fid, [{:vnat, 0x110000}]}}
        end

      fid ->
        {:ok, {:vdata, fid, []}}
    end
  end

  defp elaborate_lambda([], body_expr, expected_core, names, ctx, env),
    do: elaborate_expr_checked(body_expr, expected_core, names, ctx, env)

  defp elaborate_lambda(params, body_expr, expected_core, names, ctx, env),
    do: elaborate_lambda(params, body_expr, expected_core, names, ctx, env, 0)

  defp elaborate_lambda([], body_expr, expected_core, names, ctx, env, _index),
    do: elaborate_expr_checked(body_expr, expected_core, names, ctx, env)

  defp elaborate_lambda(
         [{:param, param_meta, pname} | rest],
         body_expr,
         expected_core,
         names,
         ctx,
         env,
         index
       ) do
    case Kernel.normalize(ctx, expected_core) do
      {:pi, _g, dom_term, cod_term} ->
        dom_value = Eval.eval(dom_term, Context.env(ctx))
        ctx1 = Context.extend(ctx, dom_value)

        with {:ok, body_term} <-
               elaborate_lambda(rest, body_expr, cod_term, [pname | names], ctx1, env, index + 1) do
          {:ok, {:lam, Cure.Core.Grade.unrestricted(), dom_term, body_term}}
        end

      _ ->
        {:error,
         {:lambda_expected_pi,
          %{
            expected: expected_core,
            parameter_index: index,
            parameter_span: surface_expression_span({:param, param_meta, []})
          }}}
    end
  end

  defp elaborate_expr_checked_fallback(expr, expected_core, names, ctx, env) do
    # An unsolved metavariable in the expected type (e.g. a higher-order implicit
    # `{P : Nat -> Type}` that first-order unification could not solve) must not be
    # handed to the trusted `Eval.eval` — it has no `{:meta, _}` clause and would
    # crash the kernel. Reject cleanly instead; higher-order pattern unification
    # (ledger #10) is what would let it be solved rather than rejected.
    if Unify.has_meta?(expected_core) do
      {:error, {:unsolved_metavariable_in_type, expected_core}}
    else
      case try_discharge_refinement(expr, expected_core, names, ctx, env) do
        {:ok, term} ->
          {:ok, term}

        :no ->
          with {:ok, term, type} <- elaborate_expr_typed(expr, names, ctx, env) do
            term = maybe_inject_union(term, type, expected_core, ctx, env)
            term = maybe_coerce_refined_to_base(term, type, expected_core, ctx, env)

            case Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
              :ok ->
                {:ok, term}

              {:error, reason} ->
                {:error, attach_call_result_context(reason, expr, env)}
            end
          end
      end
    end
  end

  defp attach_call_result_context(
         {:source_context, reason, context},
         {:function_call, meta, _args} = expression,
         env
       )
       when is_map(context) do
    reason = contextualize_call_arity(reason, expression, env)

    if Map.get(context, :expectation_origin) in [:call_argument, :operator_operand] do
      {:source_context, reason, context}
    else
      origin_context =
        if extern_call_mismatch?(reason, meta, env),
          do: ffi_result_context(expression),
          else: call_result_context(expression)

      {:source_context, reason, Map.merge(context, origin_context)}
    end
  end

  defp attach_call_result_context(reason, {:function_call, meta, _args} = expression, env) do
    reason = contextualize_call_arity(reason, expression, env)

    context =
      if extern_call_mismatch?(reason, meta, env),
        do: ffi_result_context(expression),
        else: call_result_context(expression)

    {:source_context, reason, context}
  end

  defp attach_call_result_context(reason, _expression, _env), do: reason

  @doc false
  def contextualize_call_arity({:source_context, reason, context}, expression, env) when is_map(context) do
    {:source_context, contextualize_call_arity(reason, expression, env), context}
  end

  def contextualize_call_arity(reason, {:function_call, meta, args}, env) do
    name = Keyword.get(meta, :name)

    with name when is_binary(name) <- name,
         key <- resolve_def_key(env, name, String.to_atom(name)),
         %{type: type, quantities: quantities} when is_list(quantities) <- Env.get_def(env, key),
         expected when is_integer(expected) <- callable_surface_arity(type, quantities),
         actual = length(args),
         true <- call_arity_reason?(reason, expected, actual) do
      {:call_arity_mismatch,
       %{
         name: name,
         expected: expected,
         actual: actual,
         direction: if(actual < expected, do: :too_few, else: :too_many)
       }}
    else
      _ -> reason
    end
  end

  def contextualize_call_arity(reason, _expression, _env), do: reason

  defp callable_surface_arity(type, quantities) do
    {_declared_domains, codomain} = peel_pi(type, length(quantities))
    Enum.count(quantities, &Grade.present?/1) + residual_pi_arity(codomain)
  end

  defp residual_pi_arity({:pi, _grade, _domain, codomain}), do: 1 + residual_pi_arity(codomain)
  defp residual_pi_arity(_type), do: 0

  defp call_arity_reason?(_reason, expected, actual) when expected == actual, do: false
  defp call_arity_reason?(:not_a_function, expected, actual), do: actual > expected
  defp call_arity_reason?(:too_many_arguments, expected, actual), do: actual > expected
  defp call_arity_reason?(:too_few_arguments, expected, actual), do: actual < expected

  defp call_arity_reason?({:conversion_failure, {:pi, _, _, _}, _expected}, expected, actual),
    do: actual < expected

  defp call_arity_reason?(_reason, _expected, _actual), do: false

  defp unresolved_call_reason?({:unknown_global, _}), do: true
  defp unresolved_call_reason?({:unknown_global, _, _}), do: true
  defp unresolved_call_reason?({:unknown_name, _}), do: true
  defp unresolved_call_reason?({:unknown_name, _, _}), do: true
  defp unresolved_call_reason?({:unknown_ctor, _}), do: true
  defp unresolved_call_reason?({:ambiguous_name, _, _}), do: true
  defp unresolved_call_reason?(_reason), do: false

  defp attach_unresolved_call_context(reason, {:function_call, meta, args} = expression, env) do
    {:source_context, _nested_reason, context} = attach_call_result_context(reason, expression, env)

    {:source_context, reason,
     Map.merge(context, %{
       name_candidates: name_candidates(env, Keyword.get(meta, :name)),
       name_arity: length(args),
       checking: Keyword.get(meta, :name)
     })}
  end

  defp name_candidates(
         %Cure.Core.Env{defs: defs, module_owner: module_owner, import_modules: import_modules},
         spelling
       ) do
    spelling = to_string(spelling)

    defs
    |> Enum.map(fn {key, _definition} ->
      {owner, name} = Cure.Elab.Name.split(key)

      {owner, name,
       %{
         id: key,
         name: name,
         namespace: :value,
         owner: owner,
         imported: owner == module_owner or is_nil(owner),
         candidate_id: key
       }}
    end)
    |> Enum.filter(fn {owner, _name, _candidate} ->
      owner == module_owner or is_nil(owner) or MapSet.member?(import_modules, owner)
    end)
    |> Enum.map(&elem(&1, 2))
    |> Enum.filter(fn %{name: name} -> abs(String.length(name) - String.length(spelling)) <= 2 end)
    |> Enum.sort_by(fn %{name: name, owner: owner} ->
      {owner != module_owner, not String.starts_with?(String.downcase(name), String.downcase(spelling)), name}
    end)
    |> Enum.take(128)
  end

  defp name_candidates(_env, _spelling), do: []

  defp extern_call_mismatch?(reason, meta, env) do
    name = Keyword.get(meta, :name)
    key = if is_binary(name), do: String.to_atom(name), else: name

    ffi_type_mismatch?(reason) and
      match?(%{body: {:extern, _}}, Env.get_def(env, key))
  end

  defp ffi_type_mismatch?({:source_context, reason, _context}), do: ffi_type_mismatch?(reason)
  defp ffi_type_mismatch?({:cannot_unify, _actual, _expected}), do: true
  defp ffi_type_mismatch?({:index_mismatch, {:cannot_unify, _actual, _expected}}), do: true
  defp ffi_type_mismatch?({:conversion_failure, _actual, _expected}), do: true
  defp ffi_type_mismatch?(_reason), do: false

  defp ffi_result_context({:function_call, meta, _args} = expression) when is_list(meta) do
    Map.merge(call_result_context(expression), %{
      checking: Keyword.get(meta, :name),
      expectation_origin: :ffi
    })
  end

  defp call_result_context({:function_call, meta, _args}) when is_list(meta) do
    span = surface_expression_span({:function_call, meta, []})

    {origin, owner} =
      if Keyword.has_key?(meta, :callee) do
        {:application, :application}
      else
        {:call_result, Keyword.get(meta, :name)}
      end

    %{
      line: span && span.start_line,
      column: span && span.start_column,
      length: span && max(1, span.end_byte - span.start_byte),
      span: span,
      expectation_span: span,
      checking: owner,
      expression_category: :function_call,
      expectation_origin: origin
    }
  end

  # A checking-mode constructor whose direct check against the expected type failed
  # may still inhabit the BASE of a refinement `{x: T | φ}` = `Sigma(T, λx. φ)` —
  # e.g. `S(k)` at `-> {n: Nat | IsPositive(n)}`, where `S` is a `Nat` (not `Sigma`)
  # constructor, so the direct check reports `:foreign_ctor`. When the expected type
  # is such a refinement, route to the refinement-discharge fallback, which checks
  # the constructor against the base domain `T` and searches for a proof of the
  # obligation `φ[x := S(k)]`. Additive: reached only after the direct constructor
  # check already failed, and the original error is surfaced when the expected type
  # is not a dischargeable refinement or no proof is found — so every
  # currently-accepted or -rejected constructor body is unchanged.
  defp ctor_refinement_fallback(expr, expected_core, names, ctx, env, orig_err) do
    if refinement_return?(expected_core, ctx, env) do
      case elaborate_expr_checked_fallback(expr, expected_core, names, ctx, env) do
        {:ok, _} = ok -> ok
        _ -> orig_err
      end
    else
      orig_err
    end
  end

  # Auto-discharge a CLOSED refinement obligation (§3a level 2). When a value is
  # checked against a refinement type `{x: T | φ}` — the dependent pair
  # `Sigma(T, λx. φ)` — and `φ[x := value]` reduces to an inhabited reflection
  # proposition (`IsTrue(True())`), fill the proof slot with that proposition's
  # nullary constructor (`Confirmed()`) and build the pair. The author writes just
  # the value; no `refine`, no explicit proof.
  #
  # Soundness: the elaborator only PROPOSES `mk_pair(value, proof)`; the proof it
  # supplies is itself kernel-checked against the obligation before use (by
  # `reflection_proof` via `Kernel.check`, or — for an open obligation — by every
  # candidate `ProofSearch.resolve` returns), and `value` is checked against the
  # base component at elaboration. The Σ-intro rule then makes the pair well-typed
  # by construction; the elaborator never trusts its own reduction. A CLOSED
  # obligation with no inhabiting nullary constructor (`IsTrue(False())`), or an
  # OPEN one with no derivable proof, yields `nil`, so this returns `:no` and the
  # value falls through to ordinary checking — the proof is required, never
  # invented.
  defp try_discharge_refinement(expr, expected_core, names, ctx, env) do
    sigma_fam = Inductive.builtin(env, :sigma)

    with false <- is_nil(sigma_fam),
         {:data, ^sigma_fam, [dom, cod], []} <- Kernel.normalize(ctx, expected_core),
         # Exclude a flat tuple / bare nested-pair Σ (`Tuple(T1,…,Tn)` lowers to a
         # unit-terminated Σ telescope that shares this shape). Its instantiated
         # second component is itself a Σ, which `ProofSearch` would happily "prove"
         # by fabricating a pair — silently accepting a program that has no
         # refinement obligation at all (and mis-elaborating its value). Only a
         # genuine refinement `{x: T | φ}`, whose predicate is a proposition, may
         # reach discharge.
         false <- tuple_telescope_type?(expected_core, sigma_fam, ctx, env) do
      # A Sigma is also the representation of user-authored dependent records
      # such as Regex's `AcceptancePathFrom`.  Some of those telescope tails end
      # in a proposition, so shape inspection alone cannot distinguish them from
      # refinement sugar.  Preserve an expression that ALREADY inhabits the
      # requested Sigma before attempting base-value + proof synthesis.  Running
      # discharge first projected the head and proof-searched the tail, eta-
      # reconstructing an opaque local as `mk_pair(fst(x), snd(x))`; Cure has no
      # pair eta, so a later dependent argument indexed by the original `x`
      # correctly rejected the reconstruction.  The kernel is the sole authority
      # here: only its ordinary check can select this identity-preserving path.
      case elaborate_expr_typed(expr, names, ctx, env) do
        {:ok, term, _type} ->
          case Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
            :ok -> {:ok, term}
            {:error, _} -> synthesize_refinement(expr, dom, cod, names, ctx, env)
          end

        {:error, _} ->
          synthesize_refinement(expr, dom, cod, names, ctx, env)
      end
    else
      _ -> :no
    end
  end

  defp synthesize_refinement(expr, dom, cod, names, ctx, env) do
    with {:ok, value} <- elaborate_expr_checked(expr, dom, names, ctx, env),
         {:data, _fam_key, _p, _i} = obligation <- Kernel.normalize(ctx, {:app, cod, value}),
         proof when not is_nil(proof) <- discharge_obligation(obligation, ctx, env) do
      {:ok, {:ctor, sigma_ctor_name(env), [value, proof]}}
    else
      _ -> :no
    end
  end

  # Find a proof of a refinement obligation, or nil. A CLOSED obligation
  # (`IsTrue(True())`) is discharged by its family's nullary constructor via
  # `reflection_proof`. An OPEN obligation — one whose truth rests on a free
  # binder, e.g. `IsTrue(int_gt(x, 0))` for a parameter `x` — has no nullary
  # inhabitant, so it falls through to the auto-lemma proof search, which derives
  # the proof from in-scope hypotheses (a matching `evidence : IsTrue(x > 0)`
  # binder), `@lemma`-tagged theorems, or the sign-directed positivity procedure.
  # Every term `ProofSearch` returns is kernel-checked against this obligation
  # inside the search, so an open obligation is discharged only when a genuine
  # proof exists; an unprovable one returns `:none` here (→ nil → `:no` upstream)
  # and the value is rejected exactly as before.
  defp discharge_obligation(obligation, ctx, env) do
    case reflection_proof(obligation, ctx, env) do
      nil ->
        case Cure.Elab.ProofSearch.resolve(obligation, ctx, env) do
          {:ok, proof} -> proof
          _ -> nil
        end

      proof ->
        proof
    end
  end

  # The nullary constructor of the obligation's reflection family that the kernel
  # accepts as a proof of the (already-reduced) obligation, or nil if none does.
  # Trying each nullary constructor and letting `Kernel.check` decide keeps this
  # general over any `So`-style reflection type and never trusts the elaborator's
  # own view of inhabitation.
  defp reflection_proof({:data, fam_key, _p, _i} = obligation, ctx, env) do
    obligation_value = Eval.eval(obligation, Context.env(ctx))

    Inductive.ctors_of(env, fam_key)
    |> Enum.filter(fn ctor -> ctor.args == [] end)
    |> Enum.find_value(fn ctor ->
      candidate = {:ctor, ctor.name, []}

      case Kernel.check(ctx, candidate, obligation_value) do
        :ok -> candidate
        _ -> nil
      end
    end)
  end

  # If `term`'s inferred `type` WHNFs to the Sigma refinement family and the
  # expected base type is convertible to the Sigma's first-component type, coerce
  # by inserting the first projection (`sigma_first`, or `Std.Refine.refined_value`
  # when that idiomatic accessor is in scope) — the reverse of the base->refined
  # injection. This is the ONLY new behavior; if the shapes don't match, return
  # `term` unchanged so ordinary checking (and its error) stands.
  #
  # `type` is a semantic VALUE here (not a Core term — see the call site), so it is
  # inspected with `Normalise.whnf_value/2` (mirror `sigma_params/3` in
  # proof_search.ex), never `Kernel.normalize/2` (which expects a Core term and
  # matches `:data`, not `:vdata`). The inserted projection is independently
  # re-verified by the fallback's `Kernel.check`, so a wrong coercion is caught.
  defp maybe_coerce_refined_to_base(term, type, expected_core, ctx, env) do
    sigma_fam = Inductive.builtin(env, :sigma)
    depth = Context.length(ctx)
    sig = Context.signature(ctx)

    with false <- is_nil(sigma_fam),
         {:vdata, ^sigma_fam, [dom_value, predicate_value]} <- Normalise.whnf_value(type, sig),
         # Do not coerce when the expected type is itself that Sigma (no coercion
         # needed) — only when expected is the base component type.
         false <- sigma_typed?(expected_core, sigma_fam, ctx),
         dom_term <- Quote.reify(dom_value, depth, sig),
         true <- convertible?(dom_term, expected_core, ctx, env) do
      predicate_term = Quote.reify(predicate_value, depth, sig)
      build_app({:global, first_projection_head(env)}, [dom_term, predicate_term, term])
    else
      _ -> term
    end
  end

  # The global to head the first projection with: `Std.Refine.refined_value` when
  # the refinement API is in scope (the idiomatic accessor a human writes,
  # mirroring `refinement_proof`), else the kernel builtin `sigma_first`. Mirror
  # `second_projection_head/1` in `proof_search.ex`: nil-check via `Env.get_def`
  # FIRST, because `Env.resolve_key/3` falls back to the bare input atom (never
  # nil) and would otherwise hand back a nonexistent global.
  defp first_projection_head(env) do
    case Env.get_def(env, "refined_value") do
      nil -> :sigma_first
      _def -> Env.resolve_key(env, env.defs, "refined_value")
    end
  end

  # True when the expected Core type normalises to the Sigma family itself (so no
  # coercion is needed — the refined value is already at the expected type).
  defp sigma_typed?(expected_core, sigma_fam, ctx) do
    match?({:data, ^sigma_fam, _, []}, Kernel.normalize(ctx, expected_core))
  end

  # Up-to-conversion equality of two Core types, mirroring proof_search.ex:317.
  # `Conv.conv?/5` takes Core terms and evaluates them itself.
  defp convertible?(a_term, b_term, ctx, env) do
    Conv.conv?(a_term, b_term, Context.env(ctx), Context.length(ctx), env)
  end

  defp build_app(head, args), do: Enum.reduce(args, head, fn a, f -> {:app, f, a} end)

  # The nullary constructor for a LITERAL member of the expected union, or nil if the
  # expected type is not a union or the literal is not one of its members.
  #
  # The key comes from `Union.literal_key/2` — the same single source of truth the
  # canonicaliser uses when it builds the family. Duplicating the key format here
  # instead would let the two drift and silently produce a ctor name that does not
  # exist, turning the injection into a no-op conversion failure.
  defp union_literal_ctor(meta, value, expected_core, ctx, env) do
    with {:data, ukey, [], []} <- Kernel.normalize(ctx, expected_core),
         true <- Cure.Elab.Union.union_family?(ukey),
         {:ok, key} <- Cure.Elab.Union.literal_key(Keyword.get(meta, :subtype), value),
         cname <- Cure.Elab.Union.ctor_key(ukey, %{key: key}),
         true <- Inductive.get_ctor(env, cname) != nil do
      cname
    else
      _ -> nil
    end
  end

  @doc """
  Coerce an already-inferred term into an expected anonymous-union type.

  A STRICT no-op unless `expected_core` normalises to a generated union family, so it
  is safe to apply anywhere a term has been inferred but the expected type is known.
  `Declarations.elaborate_body/6`'s catch-all needs it: that clause elaborates in
  INFER mode and discards the declared return type, so a body like `fn f(n: Int) ->
  Int | Bool = n` never reaches check-position and would never be injected.
  """
  @spec coerce_union(term(), Cure.Core.Value.t(), term(), Context.t(), Env.t()) :: term()
  def coerce_union(term, type, expected_core, ctx, env),
    do: maybe_inject_union(term, type, expected_core, ctx, env)

  @doc """
  Coerce an already-inferred refinement value to its base type.

  A STRICT no-op unless the inferred `type` WHNFs to the Sigma refinement family and
  `expected_core` is convertible to the Sigma's first-component type, so it is safe to
  apply anywhere a term has been inferred but the expected base type is known.
  `Declarations.elaborate_body/6`'s catch-all needs it for the same reason it needs
  `coerce_union/5`: that clause elaborates in INFER mode, so a body like
  `fn underlying(p: PositiveNatural) -> Nat = p` never reaches the check-mode fallback.
  """
  @spec coerce_refined_to_base(term(), Cure.Core.Value.t(), term(), Context.t(), Env.t()) ::
          term()
  def coerce_refined_to_base(term, type, expected_core, ctx, env),
    do: maybe_coerce_refined_to_base(term, type, expected_core, ctx, env)

  @doc """
  True when the declared return type is the refinement / dependent-pair Sigma
  family.

  `Declarations.elaborate_body/6`'s catch-all uses it to route such returns
  through CHECK mode, so an OPEN refinement obligation (`{n: T | φ}` whose truth
  depends on a binder) reaches `try_discharge_refinement` and can be discharged by
  proof search — mirroring how `union_goal?/1` routes union returns through check
  mode. A metavariable-bearing return type is excluded (it must not be handed to
  the kernel's `Kernel.normalize`), matching `elaborate_expr_checked_fallback/5`'s
  own guard; such a body keeps the historical infer path.
  """
  @spec refinement_return?(term(), Context.t(), Env.t()) :: boolean()
  def refinement_return?(expected_core, ctx, env) do
    sigma_fam = Inductive.builtin(env, :sigma)

    not is_nil(sigma_fam) and not Unify.has_meta?(expected_core) and
      sigma_typed?(expected_core, sigma_fam, ctx) and
      not tuple_telescope_type?(expected_core, sigma_fam, ctx, env)
  end

  @doc """
  True when an *inferred* body already sits at the refinement / dependent-pair
  Sigma family — i.e. it is a complete refinement value (`refine(v, pf)`) rather
  than a bare base value that still owes a refinement obligation.

  `Declarations.elaborate_refinement_return_body/6` uses it to decide whether a
  body at a refinement return needs the goal threaded in (a base value like
  `multiply(a, b)` at `{n | IsPositive(n)}`, whose obligation must reach
  `try_discharge_refinement`) or is already complete and must be kept verbatim (so
  its projection accessors are not re-derived by a redundant checked pass).

  `type` is a semantic VALUE (the third element of `elaborate_expr_typed/4`, see
  `coerce_refined_to_base/5`), so it is inspected with `Normalise.whnf_value/2` —
  never `Kernel.normalize/2`, which expects a Core term and would crash on a value.
  """
  @spec inferred_refinement_value?(Cure.Core.Value.t(), Context.t(), Env.t()) :: boolean()
  def inferred_refinement_value?(type, ctx, env) do
    sigma_fam = Inductive.builtin(env, :sigma)
    sig = Context.signature(ctx)

    not is_nil(sigma_fam) and
      match?({:vdata, ^sigma_fam, [_dom, _pred]}, Normalise.whnf_value(type, sig))
  end

  # A refinement / bare dependent-pair Σ and a flat tuple Σ share ONE Core shape
  # (`{:data, Sigma, [dom, λ], []}`) — the unified-tuple encoding lowers
  # `Tuple(T1,…,Tn)` to the unit-terminated telescope
  # `Sigma(T1, λ_. … Sigma(Tn, λ_. Unit))`. Only the SPINE TERMINATOR separates
  # them: a tuple bottoms at `Unit`, a refinement's predicate is a proposition.
  # Routing a tuple return through the refinement check-first path changes how its
  # body elaborates (a still-well-typed but different Core term, e.g. an off-by-one
  # in a nested optic rebuild), so tuples MUST be excluded here.
  #
  # This is the transitive closure of `telescope_terminator?/3`'s probe technique:
  # apply each Σ's predicate to a closed `unit` probe, normalize (β-reducing a
  # non-dependent tail to its body), and recurse on the tail. A car list that ends
  # in `Unit` is a tuple; anything else (a proposition, or a bare pair whose tail is
  # an ordinary type) is not. Mirrors emit's value-level `telescope_cars/2`.
  defp tuple_telescope_type?(expected_core, sigma_fam, ctx, env) do
    unit_family = unit_family_name(env)

    case Kernel.normalize(ctx, expected_core) do
      {:data, ^unit_family, [], []} ->
        true

      {:data, ^sigma_fam, [_dom, b_fn], []} ->
        tail = {:app, b_fn, {:ctor, unit_ctor_name(env), []}}
        tuple_telescope_type?(tail, sigma_fam, ctx, env)

      _ ->
        false
    end
  end

  # Anonymous-union subsumption: a coercion inserted by the ELABORATOR in check mode
  # only — never a kernel rule. If the expected type is a generated union family and
  # the term's inferred type is one of its members, inject that member's constructor.
  #
  # Otherwise the term passes through untouched and the kernel rejects it with an
  # ordinary conversion failure. Note the injected `{:ctor, …}` is independently
  # re-verified by `Kernel.check/3`, so the elaborator stays untrusted: a wrong
  # injection is caught, not silently accepted.
  defp maybe_inject_union(term, type, expected_core, ctx, env) do
    with {:data, ukey, [], []} <- Kernel.normalize(ctx, expected_core),
         true <- Cure.Elab.Union.union_family?(ukey) do
      member_term = Quote.reify(type, Context.length(ctx), Context.signature(ctx))

      cond do
        # (a) The term's type is ITSELF a narrower union — widen it.
        match?({:data, _, [], []}, member_term) and
            Cure.Elab.Union.union_family?(elem(member_term, 1)) ->
          widen_union(term, elem(member_term, 1), ukey, expected_core, ctx, env)

        # (b) The term's type is a plain member — inject it.
        true ->
          cname =
            Cure.Elab.Union.ctor_key(ukey, %{key: Cure.Elab.Union.member_key(member_term)})

          if Inductive.get_ctor(env, cname), do: {:ctor, cname, [term]}, else: term
      end
    else
      _ -> term
    end
  end

  # Widen a narrower union into a wider one by remapping each of its constructors to
  # the counterpart with the same member key in the target family. This is a REAL
  # function — a Core `:case` — not a cast: the two families are genuinely distinct
  # types, so there is nothing to reinterpret.
  #
  # If any source member is absent from the target, the term is returned untouched
  # and the kernel rejects it with an ordinary conversion failure.
  defp widen_union(term, from_key, to_key, to_core, _ctx, env) do
    from_prefix = Atom.to_string(from_key) <> "$"

    branches =
      env
      |> Inductive.ctors_of(from_key)
      |> Enum.map(fn ctor ->
        suffix = ctor.name |> Atom.to_string() |> String.replace_prefix(from_prefix, "")
        target = String.to_atom(Atom.to_string(to_key) <> "$" <> suffix)

        cond do
          Inductive.get_ctor(env, target) == nil -> :missing
          ctor.args == [] -> {ctor.name, 0, {:ctor, target, []}}
          true -> {ctor.name, 1, {:ctor, target, [{:var, 0}]}}
        end
      end)

    if Enum.any?(branches, &(&1 == :missing)) do
      term
    else
      # The source family is parameterless and index-free, so its motive is a single
      # lambda over the scrutinee. `to_core` is a closed `{:data, key, [], []}`, so it
      # needs no weakening under that binder.
      motive =
        {:lam, Cure.Core.Grade.unrestricted(), {:data, from_key, [], []}, to_core}

      {:case, term, motive, branches}
    end
  end

  # Elaborate a saturated global call in checking mode, threading the expected
  # return type into the application so a return-type-only implicit can be solved.
  # Checking mode is goal-directed: solve hidden arguments from `expected` before
  # inferring explicit arguments, then retain eager inference as a compatibility
  # fallback. This ordering matters when eager inference can produce a complete but
  # wrong hidden family (for example the predicate of a refinement constructor).
  # The caller re-checks the assembled term against the goal in either path.
  defp elaborate_global_app_expected(env, atom, args, names, ctx, expected) do
    if Enum.any?(args, &call_placeholder?/1) do
      profile_attempt(atom, :goal_placeholder_bidirectional, fn ->
        elaborate_implicit_app_bidirectional(env, atom, args, names, ctx, expected)
      end)
    else
      elaborate_global_app_expected_eager(env, atom, args, names, ctx, expected)
    end
  end

  defp elaborate_global_app_expected_eager(env, atom, args, names, ctx, expected) do
    case profile_attempt(atom, :goal_bidirectional, fn ->
           elaborate_implicit_app_bidirectional(env, atom, args, names, ctx, expected)
         end) do
      {:ok, _, _} = ok ->
        ok

      {:error, _} = goal_error ->
        case map_present_args(args, names, ctx, env) do
          {:ok, present} ->
            case profile_attempt(atom, :goal_eager, fn ->
                   elaborate_global_app(env, atom, present, ctx, expected)
                 end) do
              {:ok, _, _} = ok -> ok
              {:error, _} -> goal_error
            end

          {:error, _} ->
            goal_error
        end
    end
  end

  defp call_placeholder?({:variable, _meta, "_"}), do: true
  defp call_placeholder?(_arg), do: false

  defp children(term) when is_tuple(term), do: term |> Tuple.to_list() |> tl()

  # Free de Bruijn indices in `term`, counted from `depth` binders in (binder-
  # aware for Π/λ/Σ/case, mirroring abstract_term). Used to check convoy sibling
  # independence.
  defp free_indices({:var, i}, depth) when i >= depth, do: MapSet.new([i - depth])
  defp free_indices({:var, _}, _depth), do: MapSet.new()

  defp free_indices({:pi, _g, d, c}, depth),
    do: MapSet.union(free_indices(d, depth), free_indices(c, depth + 1))

  defp free_indices({:lam, _g, d, b}, depth),
    do: MapSet.union(free_indices(d, depth), free_indices(b, depth + 1))

  defp free_indices({:case, s, m, brs}, depth) do
    base = MapSet.union(free_indices(s, depth), free_indices(m, depth))
    Enum.reduce(brs, base, fn {_c, ar, b}, acc -> MapSet.union(acc, free_indices(b, depth + ar)) end)
  end

  defp free_indices(term, depth) when is_tuple(term),
    do: term |> children() |> Enum.reduce(MapSet.new(), &MapSet.union(&2, free_indices(&1, depth)))

  defp free_indices(term, depth) when is_list(term),
    do: Enum.reduce(term, MapSet.new(), &MapSet.union(&2, free_indices(&1, depth)))

  defp free_indices(_term, _depth), do: MapSet.new()

  # Largest free de Bruijn index occurring anywhere in `terms` (−1 if none). Used
  # to pick sentinel variables for computed-index abstraction that are guaranteed
  # not to alias any existing variable.
  defp max_free_ref(terms) do
    terms
    |> Enum.reduce(MapSet.new(), fn t, acc -> MapSet.union(acc, free_indices(t, 0)) end)
    |> MapSet.to_list()
    |> Enum.max(fn -> -1 end)
  end

  # `Quote.reify` collapses a `{:vdata, name, params ++ indices}` value into
  # `{:data, name, all_args, []}` (the value rep does not track the param/index
  # split). Restore the split for every data application in `term` using the
  # family's declared param count, so the kernel's `:data` rule — which checks
  # params and indices against separate telescopes — accepts reified sibling and
  # transport types.
  defp resplit_data({:data, name, params, indices}, env) do
    combined = Enum.map(params ++ indices, &resplit_data(&1, env))
    {ps, is} = Enum.split(combined, Inductive.param_count(env, name))
    {:data, name, ps, is}
  end

  defp resplit_data(term, env) when is_tuple(term),
    do: rebuild(term, Enum.map(children(term), &resplit_data(&1, env)))

  defp resplit_data(term, env) when is_list(term),
    do: Enum.map(term, &resplit_data(&1, env))

  defp resplit_data(term, _env), do: term

  defp rebuild(term, children) when is_tuple(term) do
    [elem(term, 0) | children] |> List.to_tuple()
  end

  defp implicit_def?(env, atom) do
    case Env.get_def(env, atom) do
      %{plicities: p, quantities: q} when is_list(p) and is_list(q) -> :implicit in p or :erased in q
      %{plicities: p} when is_list(p) -> :implicit in p
      %{quantities: q} when is_list(q) -> :erased in q
      _ -> false
    end
  end

  # Residual explicit-parameter count for a partial application in checking mode:
  # the def's explicit (non-erased) arity minus the number of supplied arguments.
  # Positive means the call is under-saturated. Only defs with recorded
  # per-parameter quantities participate (every implicit-carrying def has them);
  # a def without quantities returns 0 so its existing partial-application
  # behaviour — non-implicit currying, which the kernel already types — is left
  # exactly as-is.
  defp residual_explicit_arity(env, key, supplied) do
    case Env.get_def(env, key) do
      %{quantities: q} when is_list(q) -> Enum.count(q, &(&1 != :erased)) - supplied
      _ -> 0
    end
  end

  # Eta-expand an under-saturated call by `k` explicit binders: `f(a1..an)`
  # becomes `fn($eta0 .. $eta{k-1}) -> f(a1..an, $eta0 .. $eta{k-1})`. The
  # `$`-prefixed binder names are synthetic and cannot collide with a source
  # identifier. Reuses the original call `meta` (carrying `:name`) for the now-
  # saturated inner application.
  defp eta_expand_call(meta, args, k) do
    vars = for i <- 0..(k - 1), do: {:variable, [], "$eta#{i}"}
    params = for i <- 0..(k - 1), do: {:param, [], "$eta#{i}"}
    {:lambda, [params: params], [{:function_call, meta, args ++ vars}]}
  end

  # Map a surface call name to its def-registry key: a qualified (`Std.Map.keys`)
  # name resolves through the value namespace, a bare name through bare-shadowing;
  # either falls back to the raw atom. Mirrors the `resolved` computation at the
  # top of `elaborate_named_call_scoped` so the checked-mode retry looks up the
  # same def the inference path does.
  defp resolve_def_key(env, name, atom) do
    if String.contains?(name, ".") do
      case Cure.Elab.Resolution.resolve_qualified(env, name, :value) do
        {:ok, key} -> key
        :error -> atom
      end
    else
      case Cure.Elab.Resolution.resolve_bare(env, atom) do
        {:ok, key} -> key
        _ -> atom
      end
    end
  end

  @doc """
  Resolve and elaborate an applied call to a bare OVERLOADED name (a set of ≥2
  members sharing one spelling — same-module discriminated members, or
  cross-module providers with no unique winner). Arguments are first aligned to
  each candidate's telescope, then the aligned calls are elaborated
  bidirectionally and the unique survivor is dispatched.

  Shared verbatim by TERM-position elaboration (`elaborate_named_call_resolved`)
  and dependent-INDEX-position lowering (`declarations.ex:lower_applied_type`) so
  both disambiguate identically — index position previously ran the pre-overload
  resolver and either mis-picked an ambient same-name provider (crashing in ι) or
  reported `:ambiguous_name`. Returns the standard `{:ok, term, type}` on a unique
  survivor, or a structured named-argument/overload error. `candidates` is the
  caller's already-computed `overload_candidates/2` (≥2).
  """
  @spec elaborate_overloaded_app(
          Env.t(),
          atom(),
          [tuple()],
          [String.t()] | nil,
          [String.t()],
          Context.t(),
          [atom()],
          keyword()
        ) :: {:ok, term(), term()} | {:error, term()}
  def elaborate_overloaded_app(env, atom, args, arg_labels, names, ctx, candidates, opts \\ []) do
    case Cure.Elab.Overload.align_candidates(env, candidates, args, arg_labels, opts) do
      {:error, _} = error ->
        error

      aligned ->
        survivors =
          Enum.flat_map(aligned, fn {key, reordered} ->
            case profile_attempt(key, :overload_bidirectional, fn ->
                   elaborate_implicit_app_bidirectional(env, key, reordered, names, ctx)
                 end) do
              {:ok, term, type} ->
                [{key, term, type}]

              {:error, _} ->
                []
            end
          end)

        case survivors do
          [{_winner, term, type}] ->
            {:ok, term, type}

          [] ->
            argument_types = infer_overload_argument_types(args, names, ctx, env)

            {:error,
             {:no_matching_overload,
              %{
                name: atom,
                arguments: argument_types,
                candidates: Cure.Elab.Overload.candidate_signatures(env, candidates)
              }}}

          many ->
            keys = Enum.map(many, &elem(&1, 0))

            if is_list(arg_labels) do
              {:error,
               {:named_argument_mismatch, :ambiguous_label,
                %{
                  key: atom,
                  label: nil,
                  written: arg_labels,
                  candidates: keys,
                  owners: Cure.Elab.Overload.candidate_owners(keys),
                  argument_spans: Keyword.get(opts, :argument_spans, []),
                  label_spans: Keyword.get(opts, :label_spans, []),
                  parameter_spans:
                    Enum.flat_map(keys, fn key ->
                      Cure.Elab.SourceMetadata.parameter_spans(key) |> Enum.reject(&is_nil/1)
                    end)
                }}}
            else
              {:error, {:ambiguous_overload, atom, Cure.Elab.Overload.candidate_owners(keys)}}
            end
        end
    end
  end

  defp infer_overload_argument_types(args, names, ctx, env) do
    Enum.map(args, fn argument ->
      case elaborate_expr_typed(argument, names, ctx, env) do
        {:ok, _term, type} -> Quote.reify(type, Context.length(ctx))
        {:error, _reason} -> nil
      end
    end)
  end

  defp map_present_args(args, names, ctx, env) do
    depth = Context.length(ctx)

    Enum.reduce_while(args, {:ok, []}, fn arg, {:ok, acc} ->
      case elaborate_expr_typed(arg, names, ctx, env) do
        # Reify at the caller's depth AND with the inductive signature. Semantic
        # data values flatten parameters and indices; a signature-free readback
        # would turn `IsPositive(n)` (zero parameters, one index) into a bogus
        # one-parameter family before it is unified with a dependent call slot.
        {:ok, term, type} ->
          {:cont, {:ok, acc ++ [{term, Quote.reify(type, depth, env)}]}}

        {:error, _} = error ->
          {:halt, error}
      end
    end)
  end

  @doc """
  Elaborate a surface `match scrut | C(pat…) -> body …` into a Core `:case`
  (design spec §5, M8.4). `result_type_term` is the expected result type (Core
  term in the current frame); the motive is built as a constant type family over
  the scrutinee family's indices and value (dependent motives — a result that
  varies with the matched indices — are a follow-up). Branch bodies are
  elaborated under the constructor's full telescope (erased indices + present
  args); surface pattern variables name the present positions. Coverage and
  per-branch index refinement are then enforced by the kernel.
  """
  @spec elaborate_match(term(), [tuple()], term(), [String.t()], Context.t(), Env.t()) ::
          {:ok, term()} | {:error, term()}
  def elaborate_match(scrut_expr, arms0, result_type_term, names, ctx, env) do
    with :ok <- validate_positional_forced_patterns(arms0) do
      elaborate_validated_match(scrut_expr, arms0, result_type_term, names, ctx, env)
    end
  end

  defp elaborate_validated_match(scrut_expr, arms0, result_type_term, names, ctx, env) do
    authored_arms = arms0

    # A tuple SCRUTINEE (`match %[xs, ys] | %[C(…), D(…)] -> …`) is lowered to a
    # nested single-scrutinee match (`match xs | C(…) -> match ys | D(…) -> …`),
    # so the existing dependent single-scrutinee machinery handles it — absurd
    # cross-constructor cases (a `Vector`'s shared index rules them out) fall out
    # of the inner index-refined match's coverage, exactly as the hand-written
    # nested form already does. Non-tuple scrutinees are returned unchanged.
    # Wave-2 List sugar in pattern position: rewrite each arm's `[]`/`[h|t]`
    # `:pattern` meta to Nil/Cons ctor-call form BEFORE any downstream pass, so
    # rekey/refine/constructor_pattern all see the uniform function_call shape and
    # no `:list` node survives. Nested list patterns continue through the general
    # constructor-pattern matrix.
    arms0 =
      arms0
      |> desugar_negative_patterns()
      |> desugar_record_patterns(env)
      |> desugar_list_patterns()
      |> desugar_typed_constructor_args()

    {scrut_expr, arms0} = desugar_single_refutable_tuple_column(scrut_expr, arms0)
    {scrut_expr, arms0} = desugar_tuple_scrutinee(scrut_expr, arms0)

    result =
      if hoist_named_default?(scrut_expr, arms0) do
        hoist_named_default_scrutinee(scrut_expr, arms0, result_type_term, names, ctx, env)
      else
        elaborate_match_dispatch(scrut_expr, arms0, result_type_term, names, ctx, env)
      end

    contextualize_authored_tuple_pattern_result(result, authored_arms, env)
  end

  # Unary minus is an expression node in the parser, including in pattern
  # position. Normalize it to the corresponding signed integer literal before
  # shape dispatch so a chain containing `-1` remains a literal-pattern chain
  # instead of falling through to constructor matching.
  defp desugar_negative_patterns(arms) do
    Enum.map(arms, fn
      {:match_arm, meta, body} ->
        {:match_arm, Keyword.update!(meta, :pattern, &desugar_negative_pattern/1), body}

      arm ->
        arm
    end)
  end

  defp desugar_negative_pattern({:unary_op, meta, [{:literal, literal_meta, value}]})
       when is_integer(value) and value >= 0 do
    if Keyword.get(meta, :operator) == :- and Keyword.get(literal_meta, :subtype) == :integer do
      {:literal, Keyword.merge(literal_meta, Keyword.take(meta, [:line, :col])), -value}
    else
      {:unary_op, meta, [{:literal, literal_meta, value}]}
    end
  end

  defp desugar_negative_pattern({:literal, meta, value}) when is_binary(value),
    do: desugar_string(value, meta)

  defp desugar_negative_pattern({tag, meta, children}) when is_list(children),
    do: {tag, meta, Enum.map(children, &desugar_negative_pattern/1)}

  defp desugar_negative_pattern(pattern), do: pattern

  # Record patterns are open and name-directed. Convert
  # `Person{age: a}` to the ordinary positional constructor pattern
  # `Person(_, a)` using the registered field telescope; omitted fields become
  # wildcards. Nested records recurse through the same conversion.
  defp desugar_record_patterns(arms, env) do
    Enum.map(arms, fn
      {:match_arm, meta, body} ->
        {:match_arm, Keyword.update!(meta, :pattern, &desugar_record_pattern(&1, env)), body}

      arm ->
        arm
    end)
  end

  defp desugar_record_pattern({:function_call, meta, field_pairs}, env) do
    if Keyword.get(meta, :record, false) do
      name = Keyword.fetch!(meta, :name)

      case Inductive.get_ctor(env, String.to_atom(name)) do
        %{args: fields} ->
          provided =
            Map.new(field_pairs, fn
              {:pair, _pair_meta, [{:literal, _field_meta, field}, value]} ->
                {field, value}
            end)

          positional =
            Enum.map(fields, fn {field, _type} ->
              provided
              |> Map.get(field, {:variable, generated_meta(meta), "_"})
              |> desugar_record_pattern(env)
            end)

          {:function_call, Keyword.delete(meta, :record), positional}

        nil ->
          {:function_call, meta, Enum.map(field_pairs, &desugar_record_pattern(&1, env))}
      end
    else
      {:function_call, meta, Enum.map(field_pairs, &desugar_record_pattern(&1, env))}
    end
  end

  defp desugar_record_pattern({tag, meta, children}, env) when is_list(children),
    do: {tag, meta, Enum.map(children, &desugar_record_pattern(&1, env))}

  defp desugar_record_pattern(pattern, _env), do: pattern

  defp validate_positional_forced_patterns(arms) do
    Enum.reduce_while(arms, :ok, fn
      {:match_arm, meta, _body}, :ok ->
        case positional_forced_pattern(Keyword.get(meta, :pattern)) do
          nil ->
            {:cont, :ok}

          {forced_meta, constructor_meta, argument_index} ->
            forced_info = Cure.MetaAST.Metadata.source_info(forced_meta)
            constructor_info = Cure.MetaAST.Metadata.source_info(constructor_meta)
            span = forced_info && forced_info.whole

            {:halt,
             {:error,
              {:source_context, {:forced_pattern_not_in_pattern, forced_meta},
               %{
                 line: span && span.start_line,
                 column: span && span.start_column,
                 length: span && max(1, span.end_column - span.start_column),
                 span: span,
                 constructor: Keyword.get(constructor_meta, :name),
                 constructor_span: constructor_info && (constructor_info.callee || constructor_info.name),
                 argument_index: argument_index,
                 expectation_origin: :pattern,
                 expression_category: :forced_pattern,
                 forced_pattern_position: :positional_constructor_argument
               }}}}
        end

      _arm, :ok ->
        {:cont, :ok}
    end)
  end

  defp positional_forced_pattern({:function_call, meta, args}) do
    args
    |> Enum.with_index()
    |> Enum.find_value(fn
      {{:forced_pattern, forced_meta, _children}, index} ->
        {forced_meta, meta, index}

      {{:named_implicit_pat, _named_meta, _children}, _index} ->
        nil

      {argument, _index} ->
        positional_forced_pattern(argument)
    end)
  end

  defp positional_forced_pattern({_tag, _meta, children}) when is_list(children),
    do: Enum.find_value(children, &positional_forced_pattern/1)

  defp positional_forced_pattern(children) when is_list(children),
    do: Enum.find_value(children, &positional_forced_pattern/1)

  defp positional_forced_pattern(_pattern), do: nil

  # A *named* default (`… | other -> body`) binds the WHOLE scrutinee value, but
  # `desugar_with_default` can only do so when the scrutinee is already a
  # variable. A complex scrutinee (`match S(n) | S(Z()) -> … | other -> …`) has
  # nothing to bind `other` to and would otherwise reject as
  # `:catchall_with_nesting`. Hoist it into a fresh `let $s = scrut in match $s
  # | …` so the whole variable-scrutinee machinery applies and `$s` is evaluated
  # exactly once (Idris' `case … of other =>` binds once likewise). Engaged only
  # when nesting forces the default path AND the scrutinee is not already a
  # variable, so the common cases are untouched.
  defp hoist_named_default?(scrut_expr, arms) do
    not match?({:variable, _m, _n}, scrut_expr) and
      Enum.any?(arms, &named_default_arm?/1) and
      Enum.any?(arms, &(arm_has_nested?(&1) or guarded_arm?(&1)))
  end

  defp named_default_arm?({:match_arm, meta, _body}) do
    case Keyword.fetch!(meta, :pattern) do
      {:variable, _m, name} -> name != "_"
      _ -> false
    end
  end

  defp hoist_named_default_scrutinee(scrut_expr, arms, result_type_term, names, ctx, env) do
    sname = "$scrut" <> fresh_tag()
    svar = {:variable, [], sname}
    assign = {:assignment, [let: true], [svar, scrut_expr]}
    inner_match = {:pattern_match, [], [svar | arms]}
    elaborate_let_block([assign, inner_match], result_type_term, names, ctx, env)
  end

  defp elaborate_match_dispatch(scrut_expr, arms0, result_type_term, names, ctx, env) do
    with {:ok, arms1} <- desugar_as_patterns(arms0),
         {:ok, arms1b} <- desugar_tuple_args(arms1),
         # A guard on a *nested* constructor pattern is threaded through the
         # pattern-matrix compiler here: rows carry their guard, and each matrix
         # leaf folds the reached rows into a `:case`-on-Bool `if`-chain whose tail is
         # the next row (the Wadler/Augustsson `match … default` continuation,
         # à la Idris' `CaseBuilder` errorCase — but over surface names, so no
         # de-Bruijn weakening is needed).
         {:ok, arms1c} <- desugar_nested_arms(arms1b, scrut_expr),
         # A guard on a *single-level* constructor pattern (which never reaches the
         # matrix) is folded into a guardless arm whose body is a `:case`-on-Bool
         # `if`-chain over the constructor group's rows (same-constructor
         # fall-through), so it flows through the ordinary `:vdata` path below. A
         # guard on a *variable/catch-all* pattern is left for `try_guard_match`.
         {:ok, arms} <- desugar_ctor_guards(arms1c, scrut_expr),
         # A `when` guard is orthogonal to the pattern's shape, so it is resolved
         # before the shape-dispatching paths (each of which would silently drop
         # the guard). Claims EVERY guarded match: handles the tractable subset,
         # errors on the rest — so no path below ever ignores a guard.
         :not_applicable <- try_tuple_match(scrut_expr, arms, result_type_term, names, ctx, env),
         :not_applicable <-
           try_guard_match(scrut_expr, arms, result_type_term, names, ctx, env),
         {:ok, scrut_term, scrut_type} <- elaborate_expr_typed(scrut_expr, names, ctx, env),
         :ok <- validate_typed_pattern_annotations(arms, scrut_type, names, ctx, env),
         :not_applicable <-
           try_trivial_match(scrut_expr, arms, result_type_term, names, ctx, env),
         :not_applicable <-
           try_literal_match(
             scrut_expr,
             arms,
             scrut_term,
             scrut_type,
             result_type_term,
             names,
             ctx,
             env
           ) do
      # Parameters can retain a transparent applied alias at their head (for
      # example `List(String)`, where `String = List(Char)`). Match dispatch
      # needs the weak-head-normal form so the outer data family is visible;
      # conversion still preserves the authored alias for diagnostics.
      case Normalise.whnf_value(scrut_type, Context.signature(ctx)) do
        {:vdata, dname, combined_vals} ->
          family = Inductive.get_family(env, dname)
          # A computed scrutinee can occur in the goal only behind one or more
          # published reducible definitions. Expose that dependency before both
          # motive construction and per-branch goal refinement; otherwise
          # `replace_term` cannot abstract the discriminant and every branch is
          # checked against the original, unrefined result index.
          result_type_term =
            case scrut_term do
              {:var, _} ->
                result_type_term

              computed ->
                result_type_term
                |> expose_reducible_dependency(computed, ctx, env)
                |> expose_sibling_result_indices(computed, ctx, env)
            end

          # The scrutinee's args are parameters ++ indices; split off the leading
          # parameters. Only the indices are abstracted by the motive and refined
          # per branch — parameters are uniform (never matched).
          pc = Inductive.param_count(env, dname)
          {param_vals, idx_vals} = Enum.split(combined_vals, pc)
          param_terms = Enum.map(param_vals, &Quote.reify(&1, Context.length(ctx)))
          idx_terms = Enum.map(idx_vals, &Quote.reify(&1, Context.length(ctx)))

          motive0 =
            build_motive(dname, family.indices, param_terms, idx_terms, scrut_term, result_type_term)

          # Step 3b: a *sibling* whose type mentions the scrutinee's stuck computed
          # index (`w : F(app(p,q))`) is not refined by 3a's motive (that only
          # generalizes the scrutinee's own goal). Carry `Eq(T, app(p,q), jₚₒₛ)`
          # into the motive and transport each such sibling in the branch body —
          # the same kernel-checked Eq-arrow + `rewrite` vehicle as capability B,
          # lifted from the scrutinee VALUE to its computed INDEX term.
          carried = detect_carried_index(family.indices, idx_terms, scrut_term, names, ctx, env)

          carried_goal_dependent? =
            carried != nil and
              Enum.any?(carried.siblings, fn %{index: index} ->
                contains_term_scoped?(result_type_term, {:var, index})
              end)

          k = length(family.indices)
          motive = if carried, do: wrap_motive_carried_eq(motive0, k, carried), else: motive0

          # Anonymous-union elimination. Runs LATE — unlike the other desugarings,
          # which fire before the scrutinee is even elaborated — because it needs the
          # scrutinee's family key, which is only known here. Typed-pattern arms
          # (`n: Int`) become ordinary ctor-pattern arms, so coverage, exhaustiveness
          # and totality all come from the existing machinery below.
          with {:ok, arms} <- desugar_union_arms(arms, dname, names, env) do
            standard =
              if carried_goal_dependent? do
                elaborate_index_motivegen_case(
                  scrut_term,
                  dname,
                  family.indices,
                  param_terms,
                  idx_terms,
                  param_vals,
                  carried.siblings,
                  arms,
                  result_type_term,
                  names,
                  ctx,
                  env
                )
              else
                with {:ok, branches, join} <-
                       elaborate_branches(
                         arms,
                         names,
                         ctx,
                         env,
                         dname,
                         idx_vals,
                         idx_terms,
                         param_vals,
                         scrut_term,
                         result_type_term,
                         carried,
                         motive
                       ) do
                  case_term = wrap_join({:case, scrut_term, motive, branches}, join)
                  {:ok, if(carried, do: {:app, case_term, mk_refl(carried.idx_term)}, else: case_term)}
                end
              end

            # The standard motive refines the return per branch but not the types of
            # scrutinee-dependent siblings (`w : ReplyOf(r)`). Collect the exact
            # dependent context telescope here. Non-indexed matches generalize that
            # telescope directly; indexed matches retry through indexed motive
            # generalization so constructor indices and sibling values are refined by
            # one canonical dependent elimination path.
            siblings =
              with {:var, _i} <- scrut_term,
                   {:ok, s} <- collect_with_siblings(scrut_term, names, ctx, env) do
                s
              else
                {:error, _reason} -> []
                _ -> []
              end

            index_siblings =
              if family.indices != [] do
                case collect_index_motive_siblings(scrut_term, idx_terms, names, ctx, env) do
                  {:ok, s} -> s
                  {:error, _} -> []
                end
              else
                []
              end

            retry_value_siblings = fn ->
              if family.indices == [] do
                elaborate_motivegen_case(
                  scrut_term,
                  scrut_type,
                  dname,
                  combined_vals,
                  siblings,
                  arms,
                  result_type_term,
                  names,
                  ctx,
                  env
                )
              else
                elaborate_index_motivegen_case(
                  scrut_term,
                  dname,
                  family.indices,
                  param_terms,
                  idx_terms,
                  param_vals,
                  siblings,
                  arms,
                  result_type_term,
                  names,
                  ctx,
                  env
                )
              end
            end

            retry_index_siblings = fn ->
              elaborate_index_motivegen_case(
                scrut_term,
                dname,
                family.indices,
                param_terms,
                idx_terms,
                param_vals,
                index_siblings,
                arms,
                result_type_term,
                names,
                ctx,
                env
              )
            end

            cond do
              siblings != [] and match?({:error, _}, standard) ->
                retry_value_siblings.()

              siblings != [] and match_term_kernel_rejects?(elem(standard, 1), result_type_term, ctx) ->
                retry_value_siblings.()

              index_siblings != [] and match?({:error, _}, standard) ->
                retry_index_siblings.()

              index_siblings != [] and
                  match_term_kernel_rejects?(elem(standard, 1), result_type_term, ctx) ->
                retry_index_siblings.()

              true ->
                standard
            end
          end

        _ ->
          {:error,
           {:source_context, :match_scrutinee_not_data,
            %{
              span: surface_expression_span(scrut_expr),
              scrutinee_span: surface_expression_span(scrut_expr),
              actual_type: scrut_type
            }}}
      end
    end
  end

  # ── Anonymous-union elimination ────────────────────────────────────────────

  # Rewrite typed-pattern and literal arms into ordinary constructor-pattern arms
  # against the union family `dname`, so everything downstream — `partition_arms/4`,
  # coverage, exhaustiveness, totality — works unchanged.
  #
  # A no-op when the scrutinee is not a generated union, so an ordinary `match` over
  # a user ADT is untouched.
  defp desugar_union_arms(arms, dname, names, env) do
    if Cure.Elab.Union.union_family?(dname) do
      Enum.reduce_while(arms, {:ok, []}, fn arm, {:ok, acc} ->
        case expand_union_arm(arm, dname, names, env) do
          {:ok, expanded} -> {:cont, {:ok, acc ++ expanded}}
          {:error, _} = err -> {:halt, err}
        end
      end)
    else
      {:ok, arms}
    end
  end

  defp expand_union_arm({:match_arm, meta, body} = arm, dname, names, env) do
    case Keyword.get(meta, :pattern) do
      # `n: Int` — a type member, or `rest: Bool | Atom` — a SUB-UNION, which expands
      # into one arm per member of the sub-union.
      {:typed_pattern, pm, [name, type_ast]} ->
        with {:ok, members} <- Cure.Elab.Union.canonicalise([type_ast], names, env) do
          sub_union? = length(members) > 1

          Enum.reduce_while(members, {:ok, []}, fn m, {:ok, acc} ->
            cname = Cure.Elab.Union.ctor_key(dname, m)

            case expand_member_arm(meta, pm, name, type_ast, cname, m, sub_union?, body) do
              {:ok, arm} -> {:cont, {:ok, [arm | acc]}}
              {:error, _} = err -> {:halt, err}
            end
          end)
          |> case do
            {:ok, arms} -> {:ok, Enum.reverse(arms)}
            {:error, _} = err -> err
          end
        end

      # `:north` — a literal member, matched bare, binding nothing.
      {:literal, lm, value} ->
        case Cure.Elab.Union.literal_key(Keyword.get(lm, :subtype), value) do
          {:ok, key} ->
            cname = Cure.Elab.Union.ctor_key(dname, %{key: key})
            pattern = {:function_call, [name: Atom.to_string(cname)], []}
            {:ok, [{:match_arm, Keyword.put(meta, :pattern, pattern), body}]}

          :error ->
            {:ok, [arm]}
        end

      _ ->
        {:ok, [arm]}
    end
  end

  # A single member of a typed-pattern arm.
  #
  # For a plain member the bound name IS the payload, so the ctor pattern binds it
  # directly.
  #
  # For a SUB-UNION member (`rest: Bool | Atom`) the bound name must carry the
  # SUB-UNION's type, not this one member's payload type. So the ctor pattern binds a
  # FRESH name, and every occurrence of the surface name in the body is replaced by
  # `assert_type <fresh> : <sub-union>` — an ascription, which elaborates the fresh
  # payload in CHECK position against the sub-union and therefore re-injects it via
  # the ordinary union coercion. (A `let`-block cannot be used here: `:block` has no
  # infer-mode clause, and branch bodies are elaborated in infer mode.)
  #
  # `subst_surface_var/3` is a blind textual walk with no notion of scope, so it must
  # not run if `body` contains a NESTED binder that rebinds `name` — a nested `match`
  # arm whose own pattern is also `name`, or a lambda parameter named `name`. Left
  # unguarded, the inner (correctly narrower-typed) occurrence would be silently
  # overwritten by the outer sub-union ascription. `binds_any?/2` is the same
  # capture-avoidance guard `elaborate_let_block` and friends use for the identical
  # class of problem; when it fires here, refuse rather than attempt a smarter
  # rewrite, matching that established idiom.
  defp expand_member_arm(meta, pm, name, type_ast, cname, m, sub_union?, body) do
    cond do
      # A LITERAL member binds no payload — the value IS the constructor. But the arm still
      # gave it a NAME (`n: 3`, or the literal arm of `rest: Bool | 3`), and the body may
      # use it. Passing `body` through untouched leaves that name resolving to whatever it
      # means in the ENCLOSING scope — it typechecks, compiles, and returns the wrong
      # value. So substitute the name with the literal itself, ascribed to the arm's type,
      # exactly as the sub-union branch substitutes its fresh payload binder. And run the
      # SAME capture guard: this branch was skipping it entirely.
      m.payload == nil and binds_any?(body, [name]) ->
        pattern_info = Cure.MetaAST.Metadata.source_info(pm)

        {:error,
         {:unsupported_pattern,
          %{
            reason: :shadowed_literal_member,
            name: name,
            member: m.key,
            span: pattern_info && (pattern_info.name || pattern_info.whole),
            type_span: (pattern_info && pattern_info.annotation) || surface_expression_span(type_ast),
            shadow_span: first_binding_span(body, name)
          }}}

      m.payload == nil ->
        pattern = {:function_call, [name: Atom.to_string(cname)], []}

        rebound =
          case Cure.Elab.Union.literal_surface(m.key) do
            {:ok, lit} ->
              ascription = {:assert_type, pm, [lit, type_ast]}
              Enum.map(body, &subst_surface_var(&1, name, ascription))

            :error ->
              body
          end

        {:ok, {:match_arm, Keyword.put(meta, :pattern, pattern), rebound}}

      sub_union? and binds_any?(body, [name]) ->
        pattern_info = Cure.MetaAST.Metadata.source_info(pm)

        {:error,
         {:unsupported_pattern,
          %{
            reason: :shadowed_sub_union,
            name: name,
            span: pattern_info && (pattern_info.name || pattern_info.whole),
            type_span: (pattern_info && pattern_info.annotation) || surface_expression_span(type_ast),
            shadow_span: first_binding_span(body, name)
          }}}

      sub_union? ->
        fresh = "__u" <> Integer.to_string(:erlang.phash2({name, m.key}))
        pattern = {:function_call, [name: Atom.to_string(cname)], [{:variable, pm, fresh}]}

        ascription = {:assert_type, pm, [{:variable, pm, fresh}, type_ast]}
        rebound = Enum.map(body, &subst_surface_var(&1, name, ascription))

        {:ok, {:match_arm, Keyword.put(meta, :pattern, pattern), rebound}}

      true ->
        pattern = {:function_call, [name: Atom.to_string(cname)], [{:variable, pm, name}]}
        {:ok, {:match_arm, Keyword.put(meta, :pattern, pattern), body}}
    end
  end

  @doc """
  Elaborate a surface `with <scrut> [proof <name>] | C(pat…) -> body …` into a
  Core `:case`. Unlike `elaborate_match`, the motive is *value-abstracting*: the
  scrutinee EXPRESSION is abstracted out of the goal (`motive_for`-style), so
  each branch's expected type is the goal with the scrutinee replaced by that
  branch's constructor value — goal refinement that plain `match` cannot do (its
  `build_motive` only generalizes type INDICES).

  Capabilities A (goal refinement), B (`proof <name>`), and sibling/other-
  argument refinement share ONE Eq-arrow mechanism. Let `e : T`, goal `G`, and
  the SIBLINGS be the in-scope parameters `h_j : H_j` whose type mentions `e`.
  When either a proof clause or a sibling is present, the motive carries the
  scrutinee equation:

      motive = λ(w:T). Eq(T, e, w) -> G[e↦w]
      term   = (case e of … branches …) (refl e)   : G

  and each branch receives `prf : Eq(T, e, pat)` (the user's proof name, or an
  internal one). Siblings are refined **by transport in the branch body**, NOT
  by generalizing their type into the motive. (When this was written, a
  `Π(SNat(w))…` motive domain tripped `Quote.reify`'s `{:vdata}` param/index
  collapse. The no-proof sibling case now DOES generalize into the motive —
  `elaborate_motivegen_case` — and index-bearing families work there because
  `collect_with_siblings` applies `resplit_data`, recovering the split; see
  `linear_sibling_refinement_test.exs`. This proof-clause path keeps transport.)
  For each sibling:

      h_j' = rewrite prf (λx. H_j[e↦x]) h_j   : H_j[e↦pat]

  bound in the arm body via `(λ h_j'. body) h_j'`, so the ORIGINAL name resolves
  to the refined `h_j'`. The indexed-data type only ever appears as a `:rewrite`
  motive RESULT (which the kernel `Eval.apply`s, never reifies) — sound, no TCB.
  Capability A is the no-equation special case (bare value-abstracting motive).
  Restricted to a non-indexed scrutinee family; this slice generalizes only
  siblings that form an independent set (see `collect_with_siblings`).
  """
  @spec elaborate_with(term(), [tuple()], String.t() | nil, term(), [String.t()], Context.t(), Env.t(), [tuple()]) ::
          {:ok, term()} | {:error, term()}
  def elaborate_with(scrut_expr, arms, proof_name, result_type_term, names, ctx, env, original_params \\ []) do
    cond do
      Enum.any?(arms, &with_rematch_arm?/1) ->
        if Enum.all?(arms, &with_rematch_arm?/1) do
          elaborate_with_rematch(scrut_expr, arms, original_params, result_type_term, names, ctx, env)
        else
          {:error,
           {:source_context, :with_mixed_rematch_arms,
            %{
              span: mixed_with_primary_span(arms),
              with_arms: Enum.map(arms, &with_arm_context/1)
            }}}
        end

      true ->
        elaborate_with_value(scrut_expr, arms, proof_name, result_type_term, names, ctx, env)
    end
  end

  defp with_rematch_arm?({:with_rematch_arm, _, _}), do: true
  defp with_rematch_arm?(_), do: false

  defp with_arm_context({:with_rematch_arm, meta, _children}) do
    %{style: :rematch, span: surface_expression_span({:with_rematch_arm, meta, []})}
  end

  defp with_arm_context({:match_arm, meta, _children}) do
    pattern = Keyword.get(meta, :pattern)

    %{
      style: :ordinary,
      span: surface_expression_span({:match_arm, meta, []}),
      pattern_span: surface_expression_span(pattern),
      pattern_kind: if(match?({:variable, _, _}, pattern), do: :catch_all, else: :constructor)
    }
  end

  defp with_arm_context(arm), do: %{style: :unknown, span: surface_expression_span(arm)}

  defp mixed_with_primary_span(arms) do
    contexts = Enum.map(arms, &with_arm_context/1)
    frequencies = Enum.frequencies_by(contexts, & &1.style)

    outlier =
      Enum.find(contexts, fn context ->
        Map.get(frequencies, context.style) == 1 and map_size(frequencies) > 1 and
          Enum.any?(frequencies, fn {style, count} -> style != context.style and count > 1 end)
      end)

    Map.get(outlier || List.first(contexts) || %{}, :span)
  end

  # Capability A/B (no LHS re-match): value-abstracting motive + eq-arrow sibling
  # transport, restricted to a NON-indexed scrutinee family. This is the original
  # `elaborate_with` body, unchanged.
  defp elaborate_with_value(scrut_expr, arms, proof_name, result_type_term, names, ctx, env) do
    with {:ok, scrut_term, scrut_type} <- elaborate_expr_typed(scrut_expr, names, ctx, env) do
      case scrut_type do
        {:vdata, dname, combined_vals} ->
          family = Inductive.get_family(env, dname)

          with {:ok, siblings} <- collect_with_siblings(scrut_term, names, ctx, env) do
            # An Eq-arrow is needed when the user asked for a proof OR when a
            # sibling must be transported (both consume `prf : Eq(T,e,pat)`).
            need_eq = proof_name != nil or siblings != []

            cond do
              # Capability A (bare value-abstraction) is SUBSUMED by the unified
              # match front-end: since Phase 2½ plain `match` value-refines the
              # goal per branch (the same refinement A's `{:lam, Cure.Core.Grade.unrestricted(), T, g_abs}` motive
              # provided), so `with <e>` with no proof and no sibling is exactly a
              # plain `match <e>`. (Task 3.2; the arms are already `{:match_arm}`.)
              # elaborate_match handles indexed AND non-indexed families, so the
              # no-eq path is index-agnostic — a bare `with` over an indexed-family
              # scrutinee (`with v` for `v : NVv(n)`) refines the same as `match v`.
              not need_eq ->
                elaborate_match(scrut_expr, arms, result_type_term, names, ctx, env)

              # Sibling refinement WITHOUT a user proof, single sibling: use
              # MOTIVE-GENERALIZATION rather than Eq-transport. The sibling becomes a
              # Π domain in the case motive and a real λ binder per branch, so a LINEAR
              # sibling STAYS linear — the Eq-transport `transport_case(prf) cap`
              # encoding is a collapsible case that erases to identity but which the
              # relevance checker ω-scaled pre-erasure (over-counting a dup, masking a
              # drop). Here `cap` is a direct convoy argument `(case e …) cap` whose
              # per-branch λ binder `check_binder` polices; the relevance convoy rule
              # counts it once. The branch-λ grade is ω — the sibling's REAL grade is
              # enforced at its own binding site (the def's `:linear cap`) via the
              # convoy. Restricted to ONE sibling; the proof form and multi-sibling keep
              # the Eq-arrow path below.
              family.indices == [] and proof_name == nil and siblings != [] ->
                elaborate_motivegen_case(
                  scrut_term,
                  scrut_type,
                  dname,
                  combined_vals,
                  siblings,
                  arms,
                  result_type_term,
                  names,
                  ctx,
                  env
                )

              # Capability B (proof / sibling transport) — the Eq-arrow motive.
              # This slice's eq-arrow motive is built for a NON-indexed scrutinee
              # family; an indexed scrutinee that also needs transport must use the
              # multi-column LHS-rematch form (`elaborate_with_rematch`) instead.
              family.indices == [] ->
                pc = Inductive.param_count(env, dname)
                {param_vals, _idx_vals} = Enum.split(combined_vals, pc)
                scrut_type_term = resplit_data(Quote.reify(scrut_type, Context.length(ctx)), env)
                g_abs = abstract_term(result_type_term, scrut_term, 0)
                motive = eq_arrow_motive(scrut_type_term, scrut_term, g_abs)

                cfg = %{
                  names: names,
                  ctx: ctx,
                  env: env,
                  dname: dname,
                  param_vals: param_vals,
                  motive: motive,
                  need_eq: true,
                  siblings: siblings,
                  prf_name: proof_name || "$with_prf",
                  scrut_term: scrut_term,
                  scrut_type_term: scrut_type_term
                }

                with {:ok, branches} <- elaborate_with_branches(arms, cfg) do
                  case_term = {:case, scrut_term, motive, branches}
                  {:ok, {:app, case_term, mk_refl(scrut_term)}}
                end

              true ->
                {:error, {:with_indexed_scrutinee_unsupported, dname}}
            end
          end

        _ ->
          with_scrutinee_not_data(scrut_expr, scrut_type, arms)
      end
    end
  end

  # -- LHS re-match over an indexed view (Idris-parity indexed views) ----------
  #
  # A with-clause that restates the parent LHS (`{:with_rematch_arm}`) is
  # elaborated like an indexed `match` — NOT the value-abstracting capability-A
  # path. The scrutinee (e.g. `view n : NV n`) is genuinely indexed; the goal is
  # generalized over its index variables by `build_motive`, and each branch is
  # refined by the kernel's index inversion (`branch_unify` yields `n := S(m)`).
  # That SAME substitution refines the branch goal AND every index-mentioning
  # sibling (e.g. `w : SNat n` ↦ `SNat (S m)`) via `specialize_branch_context`.
  # The kernel independently re-checks the assembled `{:case,…}`, so the
  # refinement is sound with no TCB change (the index equation comes from the
  # case eliminator, not from an index-injectivity assumption). `match_parent_lhs`
  # validates each restated LHS is constructor-refined (rejecting forced/
  # arithmetic patterns — the deferred #5 case) before the arm is admitted.
  defp elaborate_with_rematch(scrut_expr, arms, original_params, result_type_term, names, ctx, env) do
    with {:ok, scrut_term, scrut_type} <- elaborate_expr_typed(scrut_expr, names, ctx, env) do
      case scrut_type do
        {:vdata, dname, combined_vals} ->
          family = Inductive.get_family(env, dname)
          pc = Inductive.param_count(env, dname)
          {param_vals, idx_vals} = Enum.split(combined_vals, pc)
          depth = Context.length(ctx)
          param_terms = Enum.map(param_vals, &Quote.reify(&1, depth))
          idx_terms = Enum.map(idx_vals, &Quote.reify(&1, depth))

          motive =
            build_motive(dname, family.indices, param_terms, idx_terms, scrut_term, result_type_term)

          with {:ok, arm_map} <- partition_rematch_arms(arms, original_params, ctx, env, dname),
               {:ok, branches} <-
                 elaborate_rematch_branches(
                   arm_map,
                   names,
                   ctx,
                   env,
                   dname,
                   idx_vals,
                   idx_terms,
                   param_vals,
                   scrut_term,
                   result_type_term,
                   motive
                 ) do
            {:ok, {:case, scrut_term, motive, branches}}
          end

        _ ->
          with_scrutinee_not_data(scrut_expr, scrut_type, arms)
      end
    end
  end

  defp with_scrutinee_not_data(scrutinee, actual_type, arms) do
    arm_contexts = Enum.map(arms, &with_arm_context/1)

    {:error,
     {:source_context, :with_scrutinee_not_data,
      %{
        span: surface_expression_span(scrutinee),
        scrutinee_span: surface_expression_span(scrutinee),
        actual_type: actual_type,
        with_form: if(Enum.any?(arms, &with_rematch_arm?/1), do: :rematch, else: :ordinary),
        with_arms: arm_contexts
      }}}
  end

  # Build `cname => {:matched, with_pattern, body} | {:impossible_marked, ...}`,
  # validating (a) the with-pattern names one of dname's OWN constructors (reused
  # from `partition_arms` semantics), and (b) the restated parent patterns are a
  # legal LHS re-match of `original_params` (`match_parent_lhs`) — the point at
  # which a forced/arithmetic restated pattern (`k+k`) is rejected.
  defp partition_rematch_arms(arms, original_params, ctx, env, dname) do
    sig = Context.signature(ctx)

    Enum.reduce_while(arms, {:ok, %{}}, fn {:with_rematch_arm, arm_meta, body}, {:ok, acc} ->
      with_pattern = Keyword.fetch!(arm_meta, :pattern)
      parent_patterns = Keyword.fetch!(arm_meta, :parent_patterns)

      with {:ok, {cname0, _vars}} <- constructor_pattern(with_pattern),
           {:ok, _subst} <- match_parent_lhs_at_arm(original_params, parent_patterns, arm_meta) do
        cname = resolve_ctor_key(env, cname0)
        with_pattern = rekey_pattern_name(with_pattern, cname)

        cond do
          Inductive.get_ctor(env, cname) == nil ->
            {:halt, unknown_pattern_constructor_error(with_pattern, cname, env, dname)}

          Inductive.ctor_family(sig, cname) != dname ->
            {:halt, shadowed_or_foreign_ctor(env, sig, cname0, cname, dname)}

          Map.has_key?(acc, cname) ->
            {:halt, {:error, {:duplicate_branch, cname}}}

          true ->
            {:cont, {:ok, Map.put(acc, cname, {:matched, with_pattern, single_body(body)})}}
        end
      else
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp match_parent_lhs_at_arm(originals, restated, arm_meta) do
    case match_parent_lhs(originals, restated) do
      {:ok, _subst} = ok ->
        ok

      {:error, reason} ->
        info = Cure.MetaAST.Metadata.source_info(arm_meta)
        original_spans = Enum.map(originals, &surface_expression_span/1)
        restated_spans = Enum.map(restated, &surface_expression_span/1)

        context = %{
          span: rematch_lhs_failure_span(reason, originals, restated, info),
          rematch_arm_span: info && info.whole,
          rematch_separator_span: info && Map.get(info.fields, :rematch_separator),
          with_pattern_span: info && info.pattern,
          original_pattern_spans: original_spans,
          restated_pattern_spans: restated_spans,
          original_patterns_span: rematch_spans_through(original_spans),
          restated_patterns_span: rematch_spans_through(restated_spans),
          original_pattern_count: length(originals),
          restated_pattern_count: length(restated)
        }

        {:error, {:source_context, reason, context}}
    end
  end

  defp rematch_lhs_failure_span({:with_rematch_non_constructor_pattern, _}, _originals, restated, info) do
    restated
    |> Enum.find_value(&first_invalid_restated_pattern/1)
    |> surface_expression_span()
    |> rematch_span_or(info && info.whole)
  end

  defp rematch_lhs_failure_span({:with_rematch_ctor_mismatch, _, _}, originals, restated, info) do
    case first_rematch_difference(originals, restated) do
      {_original, authored} -> surface_expression_span(authored) || (info && info.whole)
      nil -> info && info.whole
    end
  end

  defp rematch_lhs_failure_span({:with_rematch_inconsistent_binding, name}, originals, restated, info) do
    originals
    |> Enum.zip(restated)
    |> Enum.find_value(fn {original, authored} ->
      if pattern_binds_name?(original, name), do: surface_expression_span(authored)
    end)
    |> rematch_span_or(info && info.whole)
  end

  defp rematch_lhs_failure_span(_reason, _originals, restated, info) do
    restated
    |> Enum.map(&surface_expression_span/1)
    |> rematch_spans_through()
    |> rematch_span_or(info && info.whole)
  end

  defp rematch_span_or(nil, fallback), do: fallback
  defp rematch_span_or(span, _fallback), do: span

  defp rematch_spans_through(spans) do
    spans = Enum.reject(spans, &is_nil/1)

    case {List.first(spans), List.last(spans)} do
      {nil, nil} ->
        nil

      {first, last} ->
        case Cure.Compiler.Parser.Range.through(first, last) do
          {:ok, span} -> span
          _ -> last || first
        end
    end
  end

  defp first_invalid_restated_pattern({:variable, _, _}), do: nil

  defp first_invalid_restated_pattern({:function_call, _meta, args}),
    do: Enum.find_value(args, &first_invalid_restated_pattern/1)

  defp first_invalid_restated_pattern(pattern), do: pattern

  defp first_rematch_difference(originals, restated) when is_list(originals) and is_list(restated) do
    originals
    |> Enum.zip(restated)
    |> Enum.find_value(fn {original, authored} -> first_rematch_difference(original, authored) end)
  end

  defp first_rematch_difference(
         {:function_call, original_meta, original_args} = original,
         {
           :function_call,
           authored_meta,
           authored_args
         } = authored
       ) do
    if Keyword.get(original_meta, :name) != Keyword.get(authored_meta, :name) or
         length(original_args) != length(authored_args) do
      {original, authored}
    else
      first_rematch_difference(original_args, authored_args)
    end
  end

  defp first_rematch_difference(_original, _authored), do: nil

  defp pattern_binds_name?({:variable, _, name}, name), do: true
  defp pattern_binds_name?({:param, _, name}, name), do: true

  defp pattern_binds_name?({:function_call, _meta, args}, name),
    do: Enum.any?(args, &pattern_binds_name?(&1, name))

  defp pattern_binds_name?(_pattern, _name), do: false

  # One Core branch per declared constructor (coverage), mirroring
  # `elaborate_branches`: an omitted/impossible constructor is discharged with
  # `{:absurd}`; a matched constructor's body is elaborated under the kernel's
  # index-refinement substitution.
  defp elaborate_rematch_branches(
         arm_map,
         names,
         ctx,
         env,
         dname,
         idx_vals,
         idx_terms,
         param_vals,
         scrut_term,
         result_type_term,
         motive
       ) do
    sig = Context.signature(ctx)

    sig
    |> Inductive.ctors_of(dname)
    |> Enum.map(& &1.name)
    |> Enum.reduce_while({:ok, []}, fn cname, {:ok, acc} ->
      verdict = Kernel.branch_unify(ctx, dname, cname, idx_vals, param_vals)

      case Map.get(arm_map, cname) do
        {:matched, with_pattern, body_expr} ->
          case elaborate_rematch_branch(
                 verdict,
                 cname,
                 with_pattern,
                 body_expr,
                 names,
                 ctx,
                 env,
                 param_vals,
                 idx_terms,
                 scrut_term,
                 result_type_term,
                 motive
               ) do
            :omit -> {:cont, {:ok, acc}}
            {:ok, branch} -> {:cont, {:ok, acc ++ [branch]}}
            {:error, _} = err -> {:halt, err}
          end

        nil ->
          if verdict == :impossible do
            # impossible constructor ⇒ OMIT it (K4 §H); the kernel's partial
            # coverage accepts the omission. No {:absurd} placeholder body.
            {:cont, {:ok, acc}}
          else
            {:halt, {:error, {:missing_branch, cname}}}
          end
      end
    end)
  end

  defp elaborate_rematch_branch(
         verdict,
         cname,
         with_pattern,
         body_expr,
         names,
         ctx,
         env,
         param_vals,
         _idx_terms,
         scrut_term,
         _result_type_term,
         motive
       ) do
    with_pattern = internalize_branch_wildcards(with_pattern)
    {:ok, {^cname, pattern_vars}} = constructor_pattern(with_pattern)

    %{args: telescope, quantities: quantities, plicities: plicities, result_indices: result_indices} =
      Inductive.get_ctor(env, cname)

    arity = length(telescope)

    instantiated_result_indices =
      Kernel.instantiate_branch_result_indices(
        result_indices,
        arity,
        param_vals,
        Context.length(ctx)
      )

    branch_names = branch_scope(telescope, quantities, plicities, pattern_vars) ++ names

    case verdict do
      :impossible ->
        # impossible ⇒ signal omission to the caller (K4 §H); no {:absurd} body.
        :omit

      _solved_or_trivial ->
        subst =
          case verdict do
            {:solved, s} -> s
            :trivial -> %{}
          end

        # The index inversion (`n := S(m)`) refines the branch goal AND every
        # index-mentioning sibling in the context.
        branch_ctx =
          ctx
          |> extend_context(telescope, param_vals)
          |> specialize_branch_context_subst(subst)

        # Compose (1b) value-refinement with (1a) index inversion via the shared
        # `refine_branch_goal` (Task 3.4) — the SAME refinement plain match uses.
        # The rematch path abstracts the computed scrutinee in the MOTIVE (shared
        # `build_motive`); this refines the branch goal to the constructor too.
        branch_expected =
          instantiate_branch_motive(
            motive,
            instantiated_result_indices,
            cname,
            arity,
            subst,
            branch_ctx
          )

        body_expr = refine_scrutinee_in_body(body_expr, scrut_term, with_pattern, pattern_vars, names)

        with {:ok, body_term} <-
               elaborate_branch_body(body_expr, branch_expected, branch_names, branch_ctx, env) do
          {:ok, {cname, arity, body_term}}
        end
    end
  end

  # Refine every context type by a branch substitution (kernel-frame de Bruijn
  # keys), mirroring the kernel's `specialize_branch_context`: reify → replace →
  # re-eval (the reify/eval round-trip repairs the flat-`{:vdata}` split).
  defp specialize_branch_context_subst(ctx, subst) when map_size(subst) == 0, do: ctx

  defp specialize_branch_context_subst(ctx, subst), do: Kernel.specialize_branch_context(ctx, subst)

  # Eq-arrow motive `λ(w:T). Eq(T, e, w) -> G[e↦w]`. Under the `w`-binder, `e`/`T`
  # shift by +1; `g_abs` (= `G[e↦w]`, already under one binder) shifts +1 more to
  # clear the extra Eq-arrow (proof) binder.
  defp eq_arrow_motive(scrut_type_term, scrut_term, g_abs) do
    eq_ty_w =
      mk_eq(Subst.shift(scrut_type_term, 1, 0), Subst.shift(scrut_term, 1, 0), {:var, 0})

    {:lam, Cure.Core.Grade.unrestricted(), scrut_type_term,
     {:pi, Cure.Core.Grade.unrestricted(), eq_ty_w, Subst.shift(g_abs, 1, 0)}}
  end

  # In-scope parameters whose (reified) type mentions the scrutinee term, in
  # scope order (outermost binder first). STOPs (rather than mis-building) when a
  # generalized sibling's type mentions another generalized sibling, or a kept
  # parameter depends on a generalized one — this slice handles only an
  # independent set.
  defp collect_with_siblings(scrut_term, names, ctx, env) do
    depth = Context.length(ctx)

    gen =
      names
      |> visible_named_context_indices()
      |> Enum.flat_map(fn {name, i} ->
        if is_binary(name) do
          type_term = resplit_data(Quote.reify(Context.lookup(ctx, i), depth), env)
          type_term = expose_reducible_dependency(type_term, scrut_term, ctx, env)
          type_term = expose_local_definition_dependency(type_term, scrut_term, ctx, env)

          # `type_term` may expose the dependency beneath Π/Σ binders (for
          # example `AcceptancePathFrom`, a nested Sigma).  The scrutinee's
          # de Bruijn index shifts at every such binder; the binder-blind check
          # silently missed that sibling and left its type unrefined.
          if contains_term_scoped?(type_term, scrut_term),
            do: [%{name: name, index: i, type_term: type_term, grade: Context.grade(ctx, i) || Grade.unrestricted()}],
            else: []
        else
          []
        end
      end)
      |> Enum.sort_by(& &1.index, :desc)

    # The motive builder below now constructs a genuinely dependent telescope,
    # so carry the transitive closure too: if `captures` depends on a selected
    # `acceptance`, both must move into the convoy. The older independent-set
    # rejection predates `generalize_sibling_telescope/2` and discarded exactly
    # this ordinary dependent-context shape.
    gen = close_sibling_dependency_set(gen, names, ctx, env, depth, MapSet.new())
    gen_set = gen |> Enum.map(& &1.index) |> MapSet.new()

    case sibling_dependency(gen, gen_set, names, ctx, env, depth) do
      nil ->
        {:ok, gen}

      details ->
        {:error,
         {:source_context, {:with_sibling_dependency_unsupported, details.reason}, Map.delete(details, :reason)}}
    end
  end

  # A transparent local `let` is represented by a variable in Core syntax but
  # by its value in `Context.env/1`. Older siblings therefore mention the let's
  # defining expression rather than the fresh variable itself:
  #
  #     let machine = thompson_machine(compilation)
  #     match machine
  #       MkPatternMachine(starts, next) -> ... child_acceptance ...
  #
  # `child_acceptance` depends on `thompson_machine(compilation)`, so the value
  # convoy must recognize that as a dependency on `machine`. Reify the local
  # definition and replace that exact, definitionally-equal occurrence with the
  # scrutinee variable before the existing motive generalization runs. Opaque
  # binders reify to themselves and are unchanged. The generated case/motive is
  # still checked by the kernel; this only exposes the dependency already stored
  # at the canonical local-definition binding site.
  defp expose_local_definition_dependency(type_term, {:var, index} = target, ctx, env) do
    depth = Context.length(ctx)

    case Enum.at(Context.env(ctx), index) do
      nil ->
        type_term

      value ->
        definition = resplit_data(Quote.reify(value, depth, Context.signature(ctx)), env)

        if definition != target and contains_term_scoped?(type_term, definition),
          do: replace_term_scoped(type_term, definition, target),
          else: type_term
    end
  end

  defp expose_local_definition_dependency(type_term, _target, _ctx, _env), do: type_term

  defp collect_index_motive_siblings(scrut_term, idx_terms, names, ctx, env) do
    depth = Context.length(ctx)

    expanded_targets =
      idx_terms
      |> Enum.flat_map(fn target -> [target, expose_reducible_layer(target, ctx, env)] end)
      |> Enum.uniq()

    # A computed scrutinee commonly has a structured index such as
    # `Active(destination, routine, constraints)`. Matching an origin view for
    # that value refines the variables *inside* the index, so a later execution
    # or accepting path whose type mentions `routine` must travel in the motive
    # even though its type does not contain the whole `Active(...)` term.
    # Variable scrutinees already take the value-convoy path above; this expands
    # only the indexed motive's dependency targets.
    targets =
      expanded_targets
      |> Enum.flat_map(fn target -> [target | structured_index_var_targets(target, env)] end)
      |> Enum.uniq()

    scrut_idx =
      case scrut_term do
        {:var, i} -> i
        _ -> -1
      end

    # An index variable is already abstracted by the motive's own index
    # telescope. Generalizing it again as a carried sibling duplicates that
    # binder and can rebind a later dependent sibling against the wrong value
    # (for example `shape : ShapeCode`, `compilation : Compilation(shape)`).
    # Carry only other context entries whose *types* depend on an index.
    index_var_indices =
      idx_terms
      |> Enum.flat_map(fn
        {:var, i} -> [i]
        _ -> []
      end)
      |> MapSet.new()

    gen =
      names
      |> visible_named_context_indices()
      |> Enum.flat_map(fn {name, i} ->
        if is_binary(name) and i != scrut_idx and not MapSet.member?(index_var_indices, i) do
          type_term = resplit_data(Quote.reify(Context.lookup(ctx, i), depth), env)

          direct_dependency? = Enum.any?(expanded_targets, &contains_term_scoped?(type_term, &1))
          structured_dependency? = Enum.any?(targets, &contains_term_scoped?(type_term, &1))

          if structured_dependency? do
            [
              %{
                name: name,
                index: i,
                type_term: type_term,
                transport_branch_subst?: not direct_dependency?
              }
            ]
          else
            []
          end
        else
          []
        end
      end)
      |> Enum.sort_by(& &1.index, :desc)

    excluded = MapSet.put(index_var_indices, scrut_idx)
    gen = close_sibling_dependency_set(gen, names, ctx, env, depth, excluded)
    gen_set = gen |> Enum.map(& &1.index) |> MapSet.new()

    case sibling_dependency(gen, gen_set, names, ctx, env, depth) do
      nil -> {:ok, gen}
      details -> {:error, details}
    end
  end

  defp visible_named_context_indices(names) do
    names
    |> Enum.with_index()
    |> Enum.reduce({[], MapSet.new()}, fn
      {name, index}, {visible, seen} when is_binary(name) ->
        if MapSet.member?(seen, name),
          do: {visible, seen},
          else: {[{name, index} | visible], MapSet.put(seen, name)}

      {_name, _index}, acc ->
        acc
    end)
    |> elem(0)
    |> Enum.reverse()
  end

  # The carried-sibling lowerer below constructs a genuinely dependent Sigma
  # telescope, so selection must be closed under dependencies. If `path` depends
  # on a selected `source`, carrying only `source` leaves the old `path` in the
  # branch context and loses the constructor refinement. Add every visible named
  # dependent transitively; `sibling_dependency/6` then only has to reject an
  # uncarryable kept binder (for example an anonymous compiler binder).
  defp close_sibling_dependency_set(gen, names, ctx, env, depth, excluded) do
    selected = gen |> Enum.map(& &1.index) |> MapSet.new()

    additions =
      names
      |> visible_named_context_indices()
      |> Enum.flat_map(fn {name, index} ->
        cond do
          not is_binary(name) or MapSet.member?(selected, index) or MapSet.member?(excluded, index) ->
            []

          true ->
            type_term = resplit_data(Quote.reify(Context.lookup(ctx, index), depth), env)
            dependencies = MapSet.intersection(free_indices(type_term, 0), selected)

            if MapSet.size(dependencies) > 0 do
              transport_branch_subst? =
                Enum.any?(gen, fn sibling ->
                  MapSet.member?(dependencies, sibling.index) and
                    Map.get(sibling, :transport_branch_subst?, false)
                end)

              [
                %{
                  name: name,
                  index: index,
                  type_term: type_term,
                  transport_branch_subst?: transport_branch_subst?
                }
              ]
            else
              []
            end
        end
      end)

    case additions do
      [] -> Enum.sort_by(gen, & &1.index, :desc)
      _ -> close_sibling_dependency_set(gen ++ additions, names, ctx, env, depth, excluded)
    end
  end

  defp structured_index_var_targets({:ctor, constructor, args}, env) do
    value_fields =
      case Inductive.get_ctor(env, constructor) do
        nil ->
          args

        ctor ->
          args
          |> Enum.zip(Inductive.plicities_of(ctor))
          |> Enum.flat_map(fn
            {argument, :explicit} -> [argument]
            {_argument, _implicit} -> []
          end)
      end

    value_fields
    |> Enum.flat_map(fn term ->
      term
      |> free_context_var_indices(0, MapSet.new())
      |> Enum.map(&{:var, &1})
    end)
  end

  defp structured_index_var_targets(_term, _env), do: []

  defp free_context_var_indices({:var, index}, depth, acc) when index >= depth,
    do: MapSet.put(acc, index - depth)

  defp free_context_var_indices({:var, _bound}, _depth, acc), do: acc

  defp free_context_var_indices({:lam, _grade, domain, body}, depth, acc) do
    acc = free_context_var_indices(domain, depth, acc)
    free_context_var_indices(body, depth + 1, acc)
  end

  defp free_context_var_indices({:pi, _grade, domain, codomain}, depth, acc) do
    acc = free_context_var_indices(domain, depth, acc)
    free_context_var_indices(codomain, depth + 1, acc)
  end

  defp free_context_var_indices({:let, _grade, type, value, body}, depth, acc) do
    acc = free_context_var_indices(type, depth, acc)
    acc = free_context_var_indices(value, depth, acc)
    free_context_var_indices(body, depth + 1, acc)
  end

  defp free_context_var_indices({:case, scrutinee, motive, branches}, depth, acc) do
    acc = free_context_var_indices(scrutinee, depth, acc)
    acc = free_context_var_indices(motive, depth, acc)

    Enum.reduce(branches, acc, fn {_constructor, arity, body}, inner_acc ->
      free_context_var_indices(body, depth + arity, inner_acc)
    end)
  end

  defp free_context_var_indices(term, depth, acc) when is_tuple(term) do
    term
    |> Tuple.to_list()
    |> Enum.reduce(acc, &free_context_var_indices(&1, depth, &2))
  end

  defp free_context_var_indices(terms, depth, acc) when is_list(terms),
    do: Enum.reduce(terms, acc, &free_context_var_indices(&1, depth, &2))

  defp free_context_var_indices(_leaf, _depth, acc), do: acc

  # Normalisation deliberately keeps a certified global folded when unfolding it
  # would merely expose a case stuck on a neutral (Core.Normalise's A6 rule). That
  # is the right canonical-form policy, but it can hide a convoy dependency from
  # the elaborator: a sibling type such as `View(f(x))` may reach `x` only through
  # one or more explicitly published `@reducible` definitions.
  #
  # Dependency discovery is untrusted elaboration, so it may inspect those bodies
  # more aggressively without changing conversion. Expand only certified, closed,
  # author-published bodies, at most once per expansion path, then beta/iota-normalise
  # with delta reduction disabled. Repeated sibling occurrences are independent:
  # unfolding a definition in one case arm must not suppress it in another. If
  # this exposes the scrutinee, the ordinary convoy
  # machinery uses the exposed (definitionally equal) type and the kernel checks
  # the resulting term. Opaque, uncertified, open, and recursive occurrences stay
  # folded. The global budget bounds hostile or unusually deep interface graphs.
  defp expose_reducible_dependency(type_term, target, ctx, env) do
    if contains_term_scoped?(type_term, target) do
      type_term
    else
      raw = raw_expose_reducible_dependency(type_term, target, ctx, env, MapSet.new(), 32)

      if contains_term_scoped?(raw, target) do
        raw
      else
        allowed = reducible_globals_in(type_term, env)
        do_expose_reducible_dependency(type_term, type_term, target, ctx, env, allowed, 8)
      end
    end
  rescue
    _ -> type_term
  catch
    _, _ -> type_term
  end

  defp do_expose_reducible_dependency(original, _term, _target, _ctx, _env, _allowed, 0),
    do: original

  defp do_expose_reducible_dependency(original, term, target, ctx, env, allowed, fuel) do
    if MapSet.size(allowed) == 0 do
      original
    else
      case Normalise.whnf(ctx, term,
             delta: :reducible,
             delta_allow: allowed,
             stuck_cases: :expose,
             fuel: 512
           ) do
        :fuel_exhausted ->
          original

        exposed ->
          exposed = resplit_data(exposed, env)

          if contains_term_scoped?(exposed, target) do
            exposed
          else
            expanded_allowed = MapSet.union(allowed, reducible_globals_in(exposed, env))

            if MapSet.size(expanded_allowed) == MapSet.size(allowed),
              do: original,
              else:
                do_expose_reducible_dependency(
                  original,
                  exposed,
                  target,
                  ctx,
                  env,
                  expanded_allowed,
                  fuel - 1
                )
          end
      end
    end
  end

  defp reducible_globals_in({:global, name}, env) do
    key = Env.resolve_key(env, env.defs, name)

    case Env.get_def(env, key) do
      %{reducible: true} -> MapSet.new([key])
      _ -> MapSet.new()
    end
  end

  defp reducible_globals_in(term, env) when is_tuple(term) do
    term
    |> children()
    |> Enum.reduce(MapSet.new(), &MapSet.union(reducible_globals_in(&1, env), &2))
  end

  defp reducible_globals_in(term, env) when is_list(term),
    do: Enum.reduce(term, MapSet.new(), &MapSet.union(reducible_globals_in(&1, env), &2))

  defp reducible_globals_in(_term, _env), do: MapSet.new()

  defp expose_reducible_layer(term, ctx, env) do
    allowed = reducible_globals_in(term, env)

    case Normalise.whnf(ctx, term,
           delta: :reducible,
           delta_allow: allowed,
           stuck_cases: :expose,
           fuel: 512
         ) do
      :fuel_exhausted -> term
      exposed -> resplit_data(exposed, env)
    end
  rescue
    _ -> term
  catch
    _, _ -> term
  end

  defp raw_expose_reducible_dependency(term, _target, _ctx, _env, _seen, 0), do: term

  defp raw_expose_reducible_dependency(term, target, ctx, env, seen, fuel) do
    if contains_term_scoped?(term, target) do
      term
    else
      {expanded, newly_seen} = expand_published_reducibles(term, env, seen)

      if MapSet.size(newly_seen) == MapSet.size(seen) do
        term
      else
        case dependency_exposure_nf(ctx, expanded) do
          normalized when normalized not in [:unsafe_to_expose, :fuel_exhausted] ->
            raw_expose_reducible_dependency(
              resplit_data(normalized, env),
              target,
              ctx,
              env,
              newly_seen,
              fuel - 1
            )

          _ ->
            term
        end
      end
    end
  end

  defp dependency_exposure_nf(ctx, term) do
    Normalise.nf(ctx, term, delta: :none, fuel: 2_048)
  rescue
    _ -> :unsafe_to_expose
  catch
    _, _ -> :unsafe_to_expose
  end

  defp expand_published_reducibles({:global, name} = global, env, seen) do
    key = Env.resolve_key(env, env.defs, name)

    case Env.get_def(env, key) do
      %{body: body, reducible: true} when not is_nil(body) ->
        if not MapSet.member?(seen, key) and Env.certified?(env, key) and Term.closed?(body),
          do: {body, MapSet.put(seen, key)},
          else: {global, seen}

      _ ->
        {global, seen}
    end
  end

  defp expand_published_reducibles(term, env, seen) when is_tuple(term) do
    {children, seen_sets} =
      term
      |> children()
      |> Enum.map(&expand_published_reducibles(&1, env, seen))
      |> Enum.unzip()

    {rebuild(term, children), Enum.reduce(seen_sets, seen, &MapSet.union/2)}
  end

  defp expand_published_reducibles(term, env, seen) when is_list(term) do
    {children, seen_sets} =
      term
      |> Enum.map(&expand_published_reducibles(&1, env, seen))
      |> Enum.unzip()

    {children, Enum.reduce(seen_sets, seen, &MapSet.union/2)}
  end

  defp expand_published_reducibles(term, _env, seen), do: {term, seen}

  defp expose_sibling_result_indices({:data, name, params, indices} = result, target, ctx, env) do
    if Enum.any?(indices, &contains_term_scoped?(&1, target)) do
      indices =
        Enum.map(indices, fn index ->
          if contains_term_scoped?(index, target) do
            index
          else
            exposed = expose_reducible_dependency(index, target, ctx, env)
            if contains_term_scoped?(exposed, target), do: exposed, else: index
          end
        end)

      {:data, name, params, indices}
    else
      result
    end
  end

  defp expose_sibling_result_indices(result, _target, _ctx, _env), do: result

  defp sibling_dependency(gen, gen_set, names, ctx, env, depth) do
    Enum.find_value(0..(depth - 1)//1, fn index ->
      dependencies =
        ctx
        |> Context.lookup(index)
        |> Quote.reify(depth)
        |> resplit_data(env)
        |> free_indices(0)
        |> MapSet.intersection(gen_set)

      if not MapSet.member?(gen_set, index) and MapSet.size(dependencies) > 0 do
        dependency = Enum.find(gen, &MapSet.member?(dependencies, &1.index))

        %{
          reason: :kept_references_sibling,
          dependent: Enum.at(names, index),
          dependency: dependency && dependency.name
        }
      end
    end)
  end

  # Emit one Core branch per surface arm. Reuses partition_arms (same validation
  # as match: own-family ctors, no duplicates). A `-> impossible` arm becomes an
  # `{:absurd}` branch; coverage is enforced by the kernel's check_coverage.
  defp elaborate_with_branches(arms, %{ctx: ctx, env: env, dname: dname} = cfg) do
    with {:ok, {arm_map, default}} <- partition_arms(arms, ctx, env, dname),
         :ok <- reject_with_default(default) do
      arm_map
      |> Enum.reduce_while({:ok, []}, fn
        {_cname, {:impossible_marked, _pattern}}, {:ok, acc} ->
          # explicit `-> impossible` ⇒ OMIT (K4 §H); kernel coverage re-verifies.
          {:cont, {:ok, acc}}

        {cname, {:matched, pattern, body_expr}}, {:ok, acc} ->
          case elaborate_with_branch(cname, pattern, body_expr, cfg) do
            {:ok, branch} -> {:cont, {:ok, acc ++ [branch]}}
            {:error, _} = err -> {:halt, err}
          end
      end)
    end
  end

  defp reject_with_default(nil), do: :ok

  defp reject_with_default({name, _body}),
    do: {:error, {:unsupported_pattern, %{reason: :default_in_with, name: name}}}

  defp elaborate_with_branch(cname, pattern, body_expr, cfg) do
    %{
      names: names,
      ctx: ctx,
      env: env,
      param_vals: param_vals,
      motive: motive,
      need_eq: need_eq
    } = cfg

    pattern = internalize_branch_wildcards(pattern)
    {:ok, {^cname, pattern_vars}} = constructor_pattern(pattern)
    %{args: telescope, quantities: quantities, plicities: plicities} = Inductive.get_ctor(env, cname)
    arity = length(telescope)
    branch_names0 = branch_scope(telescope, quantities, plicities, pattern_vars) ++ names
    branch_ctx0 = extend_context(ctx, telescope, param_vals)

    ctor_term = branch_constructor_term(cname, arity)
    motive_shifted = Subst.shift(motive, arity, 0)
    applied = Kernel.normalize(branch_ctx0, {:app, motive_shifted, ctor_term})

    if need_eq do
      elaborate_with_eq_branch(cname, arity, ctor_term, applied, branch_ctx0, branch_names0, body_expr, cfg)
    else
      with {:ok, body_term} <-
             elaborate_branch_body(body_expr, applied, branch_names0, branch_ctx0, env) do
        {:ok, {cname, arity, body_term}}
      end
    end
  end

  # The Eq-arrow branch: bind `prf : Eq(T,e,pat)`, transport each `e`-mentioning
  # sibling to its refined type, check the arm body under the refined names, and
  # wrap as `λprf. (λh_1. … (λh_m. body) t_m …) t_1`.
  defp elaborate_with_eq_branch(cname, arity, ctor_term, applied, branch_ctx0, branch_names0, body_expr, cfg) do
    %{env: env, siblings: siblings, prf_name: prf_name, scrut_term: scrut_term, scrut_type_term: scrut_type_term} = cfg

    # `applied` = Π(prf : Eq(T,e,pat)). G[e↦pat]. Bind prf → the branch_ctx1 frame.
    {:pi, _g, eq_dom_term, cod_b1} = applied
    eq_dom_value = Eval.eval(eq_dom_term, Context.env(branch_ctx0))
    branch_ctx1 = Context.extend(branch_ctx0, eq_dom_value)
    branch_names1 = [prf_name | branch_names0]

    # Constants in the branch_ctx1 frame (ctx + ctor telescope + prf).
    sc = arity + 1
    e_b1 = Subst.shift(scrut_term, sc, 0)
    t_b1 = Subst.shift(scrut_type_term, sc, 0)
    pat_b1 = Subst.shift(ctor_term, 1, 0)

    # Per-sibling transport (`prf = {:var,0}`; original `h_j` = {:var, idx+sc}).
    sib_data =
      Enum.map(siblings, fn %{index: idx, name: sname, type_term: h_ctx} = sibling ->
        h_b1 = Subst.shift(h_ctx, sc, 0)
        motive_j = {:lam, Cure.Core.Grade.unrestricted(), t_b1, abstract_term(h_b1, e_b1, 0)}
        # J/subst transport (Phase B): prf {:var,0} : Eq(T, e, pat); the case's
        # type is (M_j@e) -> (M_j@pat), applied to the original sibling h_j.
        # Annotation-safety (transport_case doc): M_j abstracts e out of an
        # OUTER-frame sibling type, so it mentions neither `pat` nor the ctor
        # telescope vars pair-2 of the reflexive unify could bind.
        transport =
          {:app, transport_case({:var, 0}, t_b1, motive_j, e_b1), {:var, idx + sc}}

        %{
          name: sname,
          grade: Map.get(sibling, :grade, Grade.unrestricted()),
          dom: replace_term_scoped(h_b1, e_b1, pat_b1),
          transport: transport
        }
      end)

    m = length(sib_data)

    branch_ctx_full =
      Enum.reduce(sib_data, branch_ctx1, fn %{dom: d, grade: grade}, c ->
        Context.extend(c, Eval.eval(d, Context.env(branch_ctx1)), grade)
      end)

    body_names = Enum.reduce(sib_data, branch_names1, fn %{name: s}, acc -> [s | acc] end)
    cod_expected = Kernel.normalize(branch_ctx_full, Subst.shift(cod_b1, m, 0))

    with {:ok, inner} <-
           elaborate_branch_body(body_expr, cod_expected, body_names, branch_ctx_full, env) do
      wrapped =
        sib_data
        |> Enum.with_index()
        |> Enum.reverse()
        |> Enum.reduce(inner, fn {%{dom: d, transport: t, grade: grade}, i}, acc ->
          {:app, {:lam, grade, Subst.shift(d, i, 0), acc}, Subst.shift(t, i, 0)}
        end)

      {:ok, {cname, arity, {:lam, Cure.Core.Grade.unrestricted(), eq_dom_term, wrapped}}}
    end
  end

  # Does the assembled `match` term fail the kernel against its expected type? Used
  # by the item-C fallback: a plain `match` whose body reads a scrutinee-dependent
  # sibling at its unrefined type builds a term `elaborate_branches` accepts but the
  # kernel later rejects (`:branch_type`). A crash in the check is treated as a
  # rejection (retry motive-gen). Only ever called when a sibling is in scope.
  defp match_term_kernel_rejects?(term, result_type_term, ctx) do
    expected = Eval.eval(result_type_term, Context.env(ctx))
    match?({:error, _}, Kernel.check(ctx, term, expected))
  rescue
    _ -> true
  catch
    _, _ -> true
  end

  # Motive-generalization elimination (shared by `with` and plain `match`): refine
  # `m` scrutinee-dependent siblings by generalizing them into the case motive and
  # binding a fresh refined λ per branch, then apply the case to the ORIGINAL
  # siblings. `motive = λw. Π(s₁: H₁[e↦w]) … Π(sₘ: Hₘ[e↦w]). G[e↦w]` (independent
  # siblings, so domain j shifts +(j-1) and G shifts +m). Non-indexed family, variable
  # scrutinee. A linear sibling stays linear (see the relevance convoy rule).
  defp elaborate_motivegen_case(
         scrut_term,
         scrut_type,
         dname,
         combined_vals,
         siblings,
         arms,
         result_type_term,
         names,
         ctx,
         env
       ) do
    scrut_type_term = resplit_data(Quote.reify(scrut_type, Context.length(ctx)), env)
    # Build the sibling telescope through the same binder-aware authority as the
    # indexed convoy path. Merely shifting the result under fresh Π binders leaves
    # references pointing at the original ambient siblings (`final(old_path)`)
    # instead of rebinding them to the refined branch arguments
    # (`final(refined_path)`). Abstracting the scrutinee after telescope
    # generalization refines both every sibling domain and the dependent result.
    motive_body =
      siblings
      |> generalize_sibling_telescope(result_type_term)
      |> abstract_term(scrut_term, 0)

    motive = {:lam, Cure.Core.Grade.unrestricted(), scrut_type_term, motive_body}
    pc = Inductive.param_count(env, dname)
    {param_vals, _idx_vals} = Enum.split(combined_vals, pc)

    cfg = %{
      names: names,
      ctx: ctx,
      env: env,
      dname: dname,
      scrut_term: scrut_term,
      param_vals: param_vals,
      motive: motive,
      result_type_term: result_type_term,
      siblings: siblings,
      sibling_names: Enum.map(siblings, & &1.name)
    }

    with {:ok, branches} <- elaborate_with_motivegen_branches(arms, cfg) do
      case_term = {:case, scrut_term, motive, branches}

      applied =
        Enum.reduce(siblings, case_term, fn %{index: idx}, acc ->
          {:app, acc, {:var, idx}}
        end)

      {:ok, applied}
    end
  end

  defp elaborate_index_motivegen_case(
         scrut_term,
         dname,
         index_tele,
         param_terms,
         idx_terms,
         param_vals,
         siblings,
         arms,
         result_type_term,
         names,
         ctx,
         env
       ) do
    generalized_result = generalize_sibling_telescope(siblings, result_type_term)

    motive = build_motive(dname, index_tele, param_terms, idx_terms, scrut_term, generalized_result)

    cfg = %{
      names: names,
      ctx: ctx,
      env: env,
      dname: dname,
      scrut_term: scrut_term,
      param_vals: param_vals,
      idx_vals: Enum.map(idx_terms, &Eval.eval(&1, Context.env(ctx))),
      motive: motive,
      result_type_term: result_type_term,
      siblings: siblings,
      sibling_names: Enum.map(siblings, & &1.name),
      indexed_motive?: true
    }

    with {:ok, branches} <- elaborate_with_motivegen_branches(arms, cfg) do
      case_term = {:case, scrut_term, motive, branches}
      applied = Enum.reduce(siblings, case_term, fn %{index: idx}, acc -> {:app, acc, {:var, idx}} end)
      {:ok, applied}
    end
  end

  # Move a selected slice of the ambient context into a dependent Π telescope.
  # `siblings` is outermost-first (descending ambient de Bruijn index). A later
  # sibling may therefore mention an earlier one; each domain is generalized
  # only over the binders already introduced, while the result is generalized
  # over the whole slice. The former implementation merely shifted the codomain
  # once per sibling and copied every domain unchanged, which was valid only for
  # an independent set and left computed convoy occurrences in sibling domains
  # in the outer frame. Once motive abstraction crossed those Πs, evaluation
  # could reify the stale references as negative indices.
  defp generalize_sibling_telescope(siblings, result_type_term) do
    m = length(siblings)

    result_rebind =
      siblings
      |> Enum.with_index()
      |> Map.new(fn {%{index: original}, position} -> {original, m - 1 - position} end)

    body = generalize(result_type_term, result_rebind, m, 0)

    domains =
      siblings
      |> Enum.with_index()
      |> Enum.map(fn {%{type_term: domain}, position} ->
        preceding_rebind =
          siblings
          |> Enum.take(position)
          |> Enum.with_index()
          |> Map.new(fn {%{index: original}, prior_position} ->
            {original, position - 1 - prior_position}
          end)

        generalize(domain, preceding_rebind, position, 0)
      end)

    domains
    |> Enum.zip(Enum.map(siblings, &Map.get(&1, :grade, Grade.unrestricted())))
    |> Enum.reverse()
    |> Enum.reduce(body, fn {domain, grade}, codomain ->
      {:pi, grade, domain, codomain}
    end)
  end

  # Motive-generalization branches (single sibling, no proof). Each branch binds the
  # REFINED sibling as a fresh λ, at the type `motive @ ctor` computes, and rebinds
  # the sibling's ORIGINAL name to it so the body sees the refined type. No Eq, no
  # transport — the linear sibling stays a real linear resource threaded through the
  # convoy `(case e …) cap`.
  defp elaborate_with_motivegen_branches(arms, %{ctx: ctx, env: env, dname: dname} = cfg) do
    with {:ok, {arm_map, default}} <- partition_arms(arms, ctx, env, dname),
         :ok <- reject_with_default(default) do
      arm_map
      |> Enum.reduce_while({:ok, []}, fn
        {cname, {:impossible_marked, pattern}}, {:ok, acc} ->
          # An indexed constructor that cannot unify with the scrutinee is
          # discharged by the same kernel authority as an ordinary dependent
          # match.  Previously the motive-generalized convoy path still built a
          # synthetic constructor context and asked `contextual_absurd/3` to
          # rediscover the contradiction from a carried sibling.  That context
          # contains the constructor at its own result indices, so the original
          # rigid index clash (for example `Cons _ _ = Nil`) has already been
          # erased and a valid `-> impossible` was rejected as reachable.
          #
          # Keep contextual ex-falso for the distinct case it was designed for:
          # the matched constructor is reachable at its own indices, but a
          # transported sibling in the convoy is empty.
          direct_verdict = motivegen_branch_verdict(cfg, cname)

          case direct_verdict do
            :impossible ->
              {:cont, {:ok, acc}}

            _reachable ->
              case elaborate_with_motivegen_branch(
                     cname,
                     pattern,
                     @contextual_impossible_body,
                     cfg
                   ) do
                {:ok, branch} -> {:cont, {:ok, acc ++ [branch]}}
                {:error, _} = err -> {:halt, err}
              end
          end

        {cname, {:matched, pattern, body_expr}}, {:ok, acc} ->
          case motivegen_branch_verdict(cfg, cname) do
            :impossible ->
              {:cont, {:ok, acc}}

            _reachable ->
              case elaborate_with_motivegen_branch(cname, pattern, body_expr, cfg) do
                {:ok, branch} -> {:cont, {:ok, acc ++ [branch]}}
                {:error, _} = err -> {:halt, err}
              end
          end
      end)
    end
  end

  defp motivegen_branch_verdict(%{idx_vals: idx_vals, ctx: ctx, dname: dname, param_vals: param_vals}, cname),
    do: Kernel.branch_unify(ctx, dname, cname, idx_vals, param_vals)

  defp motivegen_branch_verdict(_cfg, _cname), do: :trivial

  defp elaborate_with_motivegen_branch(cname, pattern, body_expr, cfg) do
    %{
      names: names,
      ctx: ctx,
      env: env,
      param_vals: param_vals,
      motive: motive,
      siblings: siblings
    } = cfg

    pattern = internalize_branch_wildcards(pattern)
    {:ok, {^cname, pattern_vars}} = constructor_pattern(pattern)

    %{args: telescope, quantities: quantities, plicities: plicities, result_indices: result_indices} =
      Inductive.get_ctor(env, cname)

    arity = length(telescope)

    {branch_ctx0, branch_subst} =
      if Map.get(cfg, :indexed_motive?, false) do
        subst =
          case Kernel.branch_unify(ctx, cfg.dname, cname, cfg.idx_vals, param_vals) do
            {:solved, s} -> s
            _ -> %{}
          end

        {ctx |> extend_context(telescope, param_vals) |> specialize_branch_context_subst(subst), subst}
      else
        {extend_context(ctx, telescope, param_vals), %{}}
      end

    # Named implicit binders are part of the branch scope in every dependent
    # match path, including the motive-generated convoy path. Previously this
    # path retained the synthetic `$erased_*` names, so a pattern with multiple
    # erased fields (`C({a = a}, {b = b}, ...)`) silently resolved `a`/`b` to
    # later positional fields in the surrounding scope. That shifted every
    # dependent recursive call by one slot. Use the same single authority as
    # ordinary constructor matching for both binding and forced-value checks.
    {named_bindings, named_checks} =
      split_named_implicits(pattern, branch_subst, arity, telescope, quantities)

    tele_names =
      Enum.reduce(
        named_bindings,
        branch_scope(telescope, quantities, plicities, pattern_vars),
        fn {name, {:variable, _, variable_name}, _named_meta, _constructor_meta}, acc ->
          position = Enum.find_index(telescope, fn {tele_name, _type} -> tele_name == String.to_atom(name) end)
          List.replace_at(acc, arity - 1 - position, to_string(variable_name))
        end
      )

    branch_names0 = tele_names ++ names

    ctor_term = branch_constructor_term(cname, arity)
    motive_shifted = Subst.shift(motive, arity, 0)
    # applied = Π(s₁: H₁[e↦pat]) … Π(sₘ: Hₘ[e↦pat]). G[e↦pat]
    motive_arguments =
      if Map.get(cfg, :indexed_motive?, false) do
        # Constructor result indices live in `params(outer) ++ args(inner)`.
        # Applying them raw as motive arguments lets a uniform parameter slot
        # numerically alias an unrelated outer binder in this branch frame (the
        # Regex marker `EmitLeft` became the later `path` sibling). Instantiate
        # those slots with the scrutinee's actual parameters through the same
        # kernel authority used by branch unification before applying the motive.
        Kernel.instantiate_branch_result_indices(
          result_indices,
          arity,
          param_vals,
          Context.length(ctx)
        ) ++ [ctor_term]
      else
        [ctor_term]
      end

    # Motives constructed above are explicit λ-spines. Instantiate that spine
    # structurally instead of evaluating and reifying the whole application.
    # Reification under the still-unintroduced sibling Πs changes levels back to
    # indices in the wrong frame; with several siblings that used to manufacture
    # negative indices. Binder-aware substitution performs the same β-step while
    # preserving the frame in which every sibling domain was authored.
    {_motive_domains, motive_body} = peel_lams(motive_shifted, length(motive_arguments), [])
    applied = Subst.instantiate(motive_body, motive_arguments)

    motive_subst =
      if Map.get(cfg, :indexed_motive?, false),
        do: emission_branch_subst(branch_subst, quantities),
        else: %{}

    # Peel one Π per sibling, extending the branch context and rebinding each
    # refined sibling under its original name (so the arm body reads the refined
    # type; the outer unrefined binder is shadowed). Collect the (grade, domain)
    # pairs to wrap the body in the matching λ-nest.
    {branch_ctx, branch_names, cod, doms_rev} =
      siblings
      |> Enum.with_index()
      |> Enum.reduce({branch_ctx0, branch_names0, applied, []}, fn {sibling, position}, {c, ns, ty, acc} ->
        # `applied` is the structurally instantiated body of the motive we built,
        # so these Πs are already exposed. Evaluating the whole Π just to inspect
        # its head reifies its codomain before this binder has been added to `c`,
        # changing neutral levels into negative indices. Peel it syntactically.
        {:pi, g, raw_dom_term, cod_ty} = ty

        transported_domain? =
          Map.get(cfg, :indexed_motive?, false) and
            Map.get(sibling, :transport_branch_subst?, false) and
            map_size(motive_subst) > 0

        dom_term =
          if transported_domain? do
            transport_structured_sibling_domain(
              sibling.type_term,
              siblings,
              position,
              arity,
              motive_subst
            )
          else
            Kernel.normalize(c, raw_dom_term)
          end

        dom_value = Eval.eval(dom_term, Context.env(c))

        {Context.extend(c, dom_value, g), [sibling.name | ns], cod_ty, [{g, dom_term} | acc]}
      end)

    # For an indexed convoy, reconstruct the branch goal from the original
    # result in the SAME authoritative branch frame used by ordinary matches.
    # Reading back `cod` through a specialized context can choose an old outer
    # variable as the neutral representative, losing an equation nested inside a
    # structured index (`regular` remained outer while `execution` had already
    # become `Execution(child_regular, ...)`).  Numeric post-hoc rewriting is not
    # sound here: sibling generalization and motive-index binders have already
    # changed the frame.
    #
    # `refine_branch_goal/6` applies the kernel's branch substitution before any
    # normalization.  Then rebind the original sibling occurrences to the fresh
    # convoy binders, exactly as their transported domains are rebound above.
    cod_expected =
      if Map.get(cfg, :indexed_motive?, false) do
        indexed_branch_codomain(
          cfg.result_type_term,
          Map.fetch!(cfg, :scrut_term),
          cname,
          arity,
          motive_subst,
          siblings,
          branch_ctx
        )
      else
        Kernel.normalize(branch_ctx, cod)
      end

    contextual_impossible? = body_expr == @contextual_impossible_body

    refined_body_expr =
      refine_scrutinee_in_body(
        body_expr,
        Map.fetch!(cfg, :scrut_term),
        pattern,
        pattern_vars,
        names
      )

    branch_body_result =
      if contextual_impossible? do
        contextual_absurd(branch_ctx, cod_expected, env)
      else
        explicit_constructor? = length(plicities) == arity and Enum.all?(plicities, &(&1 == :explicit))

        if explicit_constructor? do
          elaborate_branch_body(refined_body_expr, cod_expected, branch_names, branch_ctx, env)
        else
          # Hidden constructor indices often infer from the explicit fields
          # (`mk(l,r)` recovers `as`/`bs` from `l : F(as)`, `r : F(bs)`). Keep
          # the original spelling as the compatibility-first attempt, then use
          # the complete branch refinement when a dependent consumer requires
          # the scrutinee VALUE rather than merely its family index.
          case elaborate_branch_body(body_expr, cod_expected, branch_names, branch_ctx, env) do
            {:ok, _} = ok ->
              ok

            {:error, _} = original ->
              case elaborate_branch_body(refined_body_expr, cod_expected, branch_names, branch_ctx, env) do
                {:ok, _} = ok -> ok
                {:error, _} -> original
              end
          end
        end
      end

    with :ok <-
           check_named_implicits(
             named_checks,
             branch_subst,
             arity,
             telescope,
             branch_ctx,
             branch_names,
             env
           ),
         {:ok, inner} <- branch_body_result do
      # doms_rev is innermost-first; folding wraps λs₁'. … λsₘ'. inner (s₁ outermost).
      wrapped =
        Enum.reduce(doms_rev, inner, fn {g, dom_term}, acc -> {:lam, g, dom_term, acc} end)

      {:ok, {cname, arity, wrapped}}
    end
  end

  # Build ex-falso from an indexed value already present in the refined branch
  # context. This is the contextual counterpart of omitting an impossible
  # constructor of the *matched* family: all constructors of the sibling family
  # must receive the kernel's certain `:impossible` verdict at its actual
  # indices. The produced empty Core case is then independently checked by the
  # kernel, so an elaborator mistake cannot manufacture an inhabitant.
  defp contextual_absurd(ctx, expected, env) do
    depth = Context.length(ctx)

    0..(depth - 1)//1
    |> Enum.find_value(fn index ->
      case Normalise.whnf_value(Context.lookup(ctx, index), Context.signature(ctx)) do
        {:vdata, dname, args} ->
          family = Inductive.get_family(env, dname)

          if family != nil and not Inductive.opaque_family?(family) do
            pc = Inductive.param_count(env, dname)
            {params, indices} = Enum.split(args, pc)

            impossible? =
              env
              |> Inductive.ctors_of(dname)
              |> Enum.all?(fn ctor ->
                Kernel.branch_unify(ctx, dname, ctor.name, indices, params) == :impossible
              end)

            if impossible? do
              param_terms = Enum.map(params, &Quote.reify(&1, depth))
              index_terms = Enum.map(indices, &Quote.reify(&1, depth))
              scrutinee = {:var, index}
              motive = build_motive(dname, family.indices, param_terms, index_terms, scrutinee, expected)
              {:ok, {:case, scrutinee, motive, []}}
            end
          end

        _ ->
          nil
      end
    end)
    |> case do
      nil -> {:error, {:reachable_impossible, :context_inhabited}}
      result -> result
    end
  end

  defp transport_structured_sibling_domain(type_term, siblings, position, arity, subst) do
    type_term
    |> Subst.shift(arity, 0)
    |> replace_branch_vars(subst)
    |> rebind_carried_sibling_term(siblings, position, arity)
  end

  defp indexed_branch_codomain(result_type, scrutinee, cname, arity, subst, siblings, branch_ctx) do
    result_type
    |> refine_branch_goal_term(scrutinee, cname, arity, subst)
    |> rebind_carried_sibling_term(siblings, length(siblings), arity)
    |> then(&Kernel.normalize(branch_ctx, &1))
  end

  defp emission_branch_subst(subst, quantities) do
    arity = length(quantities)

    erased_fields =
      quantities
      |> Enum.with_index()
      |> Enum.filter(fn {quantity, _position} -> Grade.erased?(quantity) end)
      |> MapSet.new(fn {_quantity, position} -> arity - 1 - position end)

    # Only a direct `constructor field := outer variable` equation has a
    # computational meaning. Other branch-unifier entries are type/index
    # refinements and may relate variables reified in different nested frames;
    # composing those into executable Core corrupts otherwise checked terms.
    Enum.reduce(subst, %{}, fn
      {field, {:var, outer}}, acc when field < arity and outer >= arity ->
        if MapSet.member?(erased_fields, field),
          do: acc,
          else: Map.put(acc, outer, {:var, field})

      _, acc ->
        acc
    end)
  end

  # motive = λ(j₀:T₀)…λ(jₙ:Tₙ).λ(x : D j̄). ResultType[scrutinee-indices ↦ j̄]
  #
  # The result type is *generalized* over the scrutinee's index arguments: where
  # the scrutinee is `x : D ā` with each aₖ a variable, every occurrence of aₖ in
  # ResultType is rebound to the motive's k-th index binder. Each branch is then
  # checked with that index specialized to the constructor's computed index —
  # this is what refines `m` to `Z`/`S k` in `match (xs : Vec a m)` so a result
  # like `Vec a (plus m n)` typechecks per branch. When ResultType doesn't
  # mention an index variable the generalization is a no-op, degrading to the
  # constant motive.
  defp build_motive(dname, index_tele, param_terms, idx_terms, scrut_term, result_type_term) do
    k = length(index_tele)
    index_types = Enum.map(index_tele, &elem(&1, 1))
    # The scrutinee-binder type `D params̄ j̄` sits under the k index binders j̄;
    # the parameters were reified in the outer frame, so shift them past the k
    # binders. Parameters are uniform, so they are constant across branches (no
    # generalization) — only the indices become the fresh binders `(k-1)..0`.
    param_terms_shifted = Enum.map(param_terms, &Subst.shift(&1, k, 0))
    scrut_type = {:data, dname, param_terms_shifted, Enum.map((k - 1)..0//-1, &{:var, &1})}

    # Map each scrutinee index to the de Bruijn index of its motive binder jₖ
    # (which sits at depth k-pos above the body). A *variable* index position
    # rebinds directly by its de Bruijn name. A *computed* index position — e.g.
    # `app(p, q)`, whose result index is not a single variable — cannot be named
    # that way, so we abstract the whole index *term* out of the result type:
    # every occurrence of that computed index is replaced by a fresh sentinel
    # variable that then rebinds to the position's motive binder. This is the
    # standard casesOn/kabstract motive extended to computed result indices
    # (Lean `inductive.cpp:643-646` reads each ctor's result-index *terms* — which
    # may be arbitrary computed terms — and applies the motive to them): each
    # branch's goal refines to the constructor's own index (`F(app as bs)`,
    # `F(SNil)`), sound with no carried equation because the kernel checks every
    # branch at `motive @ ctor_indices` while the use site recovers the original
    # goal via `motive @ scrutinee_indices`. Sentinels are chosen above every free
    # de Bruijn index in play so they cannot alias a real variable or each other.
    sentinel_base = 1 + max_free_ref([result_type_term, scrut_term | idx_terms])

    {result_type_term, rebind} =
      idx_terms
      |> Enum.with_index()
      |> Enum.reduce({result_type_term, %{}}, fn
        {{:var, orig}, pos}, {rt, acc} ->
          {rt, Map.put(acc, orig, k - pos)}

        {computed, pos}, {rt, acc} ->
          sentinel = sentinel_base + pos
          {replace_term_scoped(rt, computed, {:var, sentinel}), Map.put(acc, sentinel, k - pos)}
      end)

    # The scrutinee VALUE rebinds to the motive's last binder `x`. A variable
    # scrutinee rebinds by name; a *computed* scrutinee (e.g. `view(n)`) is
    # abstracted out of the result type the same sentinel way as a computed
    # index — this is Lean's `kabstract result.matchType discr`
    # (`Elab/Match.lean:137`), which abstracts occurrences of the discriminant
    # TERM whether or not it is a variable. Without it a goal like
    # `Eq(NV(n), view(n), view(n))` keeps `view(n)` opaque per branch, and
    # `vs(toS(m)) ≢ vs(s)` — no amount of index refinement can recover it.
    {result_type_term, rebind} =
      case scrut_term do
        {:var, orig} ->
          {result_type_term, Map.put(rebind, orig, 0)}

        computed ->
          sentinel = sentinel_base + k
          {replace_term_scoped(result_type_term, computed, {:var, sentinel}), Map.put(rebind, sentinel, 0)}
      end

    body = generalize(result_type_term, rebind, k + 1, 0)

    (index_types ++ [scrut_type])
    |> Enum.reverse()
    |> Enum.reduce(body, fn type, acc -> {:lam, Cure.Core.Grade.unrestricted(), type, acc} end)
  end

  # Step 3b detection. Return `nil` unless the scrutinee has exactly one MAXIMAL
  # computed index position whose term is mentioned by a sibling. A sibling can
  # mention both `boundary(x)` and the enclosing `destinations(..., boundary(x))`;
  # the outer equation subsumes the inner one, so those are one dependency rather
  # than two unrelated equations. In the singleton maximal case return
  # `%{pos, idx_term, idx_type_term, siblings}` describing the equation to carry.
  # Restricted to a single computed index with a closed index type (SList, Dec —
  # the FRP carriers); anything else falls back to the plain 3a motive (the kernel
  # then rejects an un-transportable sibling, never mis-accepts it).
  defp detect_carried_index(index_tele, idx_terms, scrut_term, names, ctx, env) do
    candidates =
      idx_terms
      |> Enum.with_index()
      |> Enum.reject(fn {t, _pos} -> invertible_index?(t) end)
      |> Enum.flat_map(fn {idx_term, pos} ->
        {_name, idx_type_term} = Enum.at(index_tele, pos)
        siblings = collect_index_siblings(scrut_term, idx_term, idx_type_term, names, ctx, env)

        if MapSet.size(free_indices(idx_type_term, 0)) == 0 and siblings != [] do
          [%{pos: pos, idx_term: idx_term, idx_type_term: idx_type_term, siblings: siblings}]
        else
          []
        end
      end)

    maximal =
      Enum.reject(candidates, fn candidate ->
        Enum.any?(candidates, fn other ->
          other.pos != candidate.pos and
            contains_term_scoped?(other.idx_term, candidate.idx_term)
        end)
      end)

    with [carried] <- maximal do
      carried
    else
      _ -> nil
    end
  end

  # A computed index whose HEAD is a constructor (`S(m)`, `Cons(h, t)`, and also
  # `Node(p, twist(q))` where an argument carries a computed subterm) is INVERTIBLE
  # by ordinary index refinement — matching unifies the scrutinee's constructor
  # index with each branch constructor's index directly (Idris's `yr : Vect m a` in
  # the `(::)` branch), and structural unification descends THROUGH the ctor head,
  # binding any computed argument subterm to the ctor's own argument binder. So the
  # test is on the HEAD only, not the argument shapes: it needs no carried equation.
  # Forcing the carried-eq transport onto a sibling with a constructor index (e.g.
  # `S(n')` for a bound tail length) spuriously fails `:branch_type` even when the
  # branch body never uses that sibling; and recursing into ctor args used to
  # misclassify `Node(p, twist(q))` as non-invertible merely because `twist(q)` is a
  # function application, dropping the branch-unify subst (E8, `:rewrite_no_match`).
  # Only a NON-constructor head — a defined-function application like `app(p, q)`,
  # which cannot be inverted structurally — genuinely needs the carried equation
  # (see `carried_index_sibling_test` and the E8 antibody). A bare variable is
  # trivially invertible (and was already excluded before).
  defp invertible_index?({:ctor, _name, _args}), do: true
  defp invertible_index?({:var, _}), do: true
  defp invertible_index?(_), do: false

  # Siblings whose (reified) type mentions the computed index term `idx_term`,
  # EXCLUDING the scrutinee itself (its own type mentions the index but it is the
  # thing being eliminated, not transported). Innermost-first, like
  # `collect_with_siblings`. Interdependent siblings are not pre-screened here; a
  # transport that would be ill-typed is caught by the kernel's re-check.
  defp collect_index_siblings(scrut_term, idx_term, idx_type_term, names, ctx, env) do
    depth = Context.length(ctx)
    idx_type_value = Eval.eval(idx_type_term, Context.env(ctx))

    scrut_idx =
      case scrut_term do
        {:var, i} -> i
        _ -> -1
      end

    names
    |> Enum.with_index()
    |> Enum.flat_map(fn {name, i} ->
      if transportable_sibling_name?(name) and i != scrut_idx do
        original_type_term = resplit_data(Quote.reify(Context.lookup(ctx, i), depth), env)

        {type_term, found?} =
          canonicalize_convoy_occurrence(original_type_term, idx_term, idx_type_value, ctx)

        if found?,
          do: [%{name: name, index: i, type_term: type_term}],
          else: []
      else
        []
      end
    end)
    |> Enum.sort_by(& &1.index, :desc)
  end

  defp transportable_sibling_name?(name) when is_binary(name),
    do: name != "_" and name != carried_prf_name() and not String.starts_with?(name, "$carried_idx_prf")

  defp transportable_sibling_name?(_name), do: false

  # A sibling and a scrutinee index can use different but definitionally equal
  # spellings (`ThreadActive(0)` versus a reducible `initial_thread()`). Convoy
  # abstraction is syntactic, so orient convertible occurrences in the sibling
  # toward the scrutinee's ORIGINAL folded index term before `abstract_term` runs.
  # This changes no kernel equality: the final motive and transports are checked.
  # Binder bodies are left alone because their de Bruijn frame differs from `ctx`;
  # the dependent sibling types handled here are ordinary data/application spines.
  defp canonicalize_convoy_occurrence(term, target, _target_type, _ctx) when term == target,
    do: {target, true}

  defp canonicalize_convoy_occurrence({tag, _g, _d, _body} = term, _target, _target_type, _ctx)
       when tag in [:pi, :lam],
       do: {term, false}

  defp canonicalize_convoy_occurrence({:case, _s, _m, _branches} = term, _target, _target_type, _ctx),
    do: {term, false}

  defp canonicalize_convoy_occurrence(term, target, target_type, ctx) when is_tuple(term) do
    if convertible_convoy_occurrence?(term, target, target_type, ctx) do
      {target, true}
    else
      {children, found?} =
        Enum.map_reduce(children(term), false, fn child, found ->
          {child, child_found?} = canonicalize_convoy_occurrence(child, target, target_type, ctx)
          {child, found or child_found?}
        end)

      {rebuild(term, children), found?}
    end
  end

  defp canonicalize_convoy_occurrence(term, target, target_type, ctx) when is_list(term) do
    Enum.map_reduce(term, false, fn child, found ->
      {child, child_found?} = canonicalize_convoy_occurrence(child, target, target_type, ctx)
      {child, found or child_found?}
    end)
  end

  defp canonicalize_convoy_occurrence(term, _target, _target_type, _ctx), do: {term, false}

  defp convertible_convoy_occurrence?(term, target, target_type, ctx) do
    inferred = Kernel.infer(ctx, term)

    type_compatible? =
      case inferred do
        {:ok, term_type} ->
          Conv.conv_values?(
            term_type,
            target_type,
            Context.length(ctx),
            Context.signature(ctx)
          )

        {:error, _} ->
          case Kernel.infer_application_result_shape(ctx, term) do
            {:ok, term_type} ->
              Conv.conv_values?(
                term_type,
                target_type,
                Context.length(ctx),
                Context.signature(ctx)
              )

            :unknown ->
              # Bidirectional constructors such as `Nil()` deliberately do not
              # infer their element parameter. The computed index's declared
              # type supplies exactly that missing expectation.
              Kernel.check(ctx, term, target_type) == :ok
          end
      end

    convertible? =
      Term.term?(term) and
        Conv.conv?(
          term,
          target,
          Context.env(ctx),
          Context.length(ctx),
          Context.signature(ctx)
        )

    with true <- type_compatible? do
      convertible?
    else
      _ -> false
    end
  rescue
    _ -> false
  catch
    _, _ -> false
  end

  # Inject the carried index equation into a 3a motive `λj̄. λx. G'`, yielding
  # `λj̄. λx. Eq(T, idx, jₚₒₛ) -> G'`.
  defp wrap_motive_carried_eq(motive, k, %{pos: pos, idx_term: idx_term, idx_type_term: idx_type_term}) do
    {binder_types, body} = peel_lams(motive, k + 1, [])

    eq_dom =
      mk_eq(Subst.shift(idx_type_term, k + 1, 0), Subst.shift(idx_term, k + 1, 0), {:var, k - pos})

    new_body = {:pi, Cure.Core.Grade.unrestricted(), eq_dom, Subst.shift(body, 1, 0)}

    binder_types
    |> Enum.reverse()
    |> Enum.reduce(new_body, fn type, acc -> {:lam, Cure.Core.Grade.unrestricted(), type, acc} end)
  end

  # Peel `n` leading `{:lam, Cure.Core.Grade.unrestricted(), dom, body}` binders, returning `{doms_outermost_first,
  # inner_body}`.
  defp peel_lams(body, 0, acc), do: {Enum.reverse(acc), body}
  defp peel_lams({:lam, _g, dom, body}, n, acc), do: peel_lams(body, n - 1, [dom | acc])

  # Rewrite the free variables of `term` for placement under the motive's k+1
  # binders (`depth` counts binders entered *within* term): a free variable that
  # names a scrutinee index becomes its motive binder (`rebind`); every other
  # free variable is shifted past the new binders (`shift`).
  defp generalize({:var, i}, _rebind, _shift, depth) when i < depth, do: {:var, i}

  defp generalize({:var, i}, rebind, shift, depth) do
    orig = i - depth

    case Map.fetch(rebind, orig) do
      {:ok, binder} -> {:var, binder + depth}
      :error -> {:var, orig + shift + depth}
    end
  end

  defp generalize({:pi, _g, d, c}, rb, s, depth),
    do: {:pi, Cure.Core.Grade.unrestricted(), generalize(d, rb, s, depth), generalize(c, rb, s, depth + 1)}

  defp generalize({:lam, _g, d, b}, rb, s, depth),
    do: {:lam, Cure.Core.Grade.unrestricted(), generalize(d, rb, s, depth), generalize(b, rb, s, depth + 1)}

  defp generalize({:app, f, a}, rb, s, depth),
    do: {:app, generalize(f, rb, s, depth), generalize(a, rb, s, depth)}

  defp generalize({:data, n, ps, is}, rb, s, depth),
    do: {:data, n, Enum.map(ps, &generalize(&1, rb, s, depth)), Enum.map(is, &generalize(&1, rb, s, depth))}

  defp generalize({:ctor, n, args}, rb, s, depth),
    do: {:ctor, n, Enum.map(args, &generalize(&1, rb, s, depth))}

  defp generalize({:case, scr, m, brs}, rb, s, depth),
    do:
      {:case, generalize(scr, rb, s, depth), generalize(m, rb, s, depth),
       Enum.map(brs, fn {c, ar, b} -> {c, ar, generalize(b, rb, s, depth + ar)} end)}

  defp generalize(leaf, _rb, _s, _depth), do: leaf

  # Coverage/discharge pass (spec §5). Partition the surface arms, then emit a
  # branch for EVERY declared constructor of `dname` — matched arms elaborate
  # their bodies; omitted or explicit-impossible constructors are discharged
  # (verdict :impossible ⇒ {:absurd} placeholder body) or rejected. The kernel
  # then re-checks and re-discharges the assembled {:case,…} independently.
  # `idx_vals` are the scrutinee's index VALUES (for branch_unify); each
  # branch's expected type comes from the kernel's branch_unify verdict subst
  # plus the scrutinee-value refinement (see elaborate_matched_branch).
  #
  # Returns `{:ok, branches, join}`. `join` is `nil`, or `{join_ty, join_val}` —
  # the JOIN POINT (plan slice 4c): the catch-all body, elaborated ONCE, which
  # `wrap_join/2` binds around the assembled `:case`. Branches that would have
  # re-elaborated it carry the `@join_marker` body until then.
  defp elaborate_branches(
         arms,
         names,
         ctx,
         env,
         dname,
         idx_vals,
         idx_terms,
         param_vals,
         scrut_term,
         result_type_term,
         carried,
         motive
       ) do
    with {:ok, {arm_map, default}} <- partition_arms(arms, ctx, env, dname) do
      sig = Context.signature(ctx)
      cnames = sig |> Inductive.ctors_of(dname) |> Enum.map(& &1.name)

      known_value =
        case Eval.eval(scrut_term, Context.env(ctx)) do
          {:vctor, _cname, _args} = value -> value
          _ -> nil
        end

      verdicts =
        Map.new(cnames, fn cname ->
          verdict = Kernel.branch_unify(ctx, dname, cname, idx_vals, param_vals)

          verdict =
            case known_value do
              {:vctor, known_ctor, _args} when cname != known_ctor -> :impossible
              {:vctor, ^cname, args} -> merge_known_ctor_args(verdict, args, Context.length(ctx))
              _ -> verdict
            end

          {cname, verdict}
        end)

      uncovered =
        Enum.filter(cnames, fn c ->
          not Map.has_key?(arm_map, c) and Map.get(verdicts, c) != :impossible
        end)

      join? = join_point?(default, uncovered, carried, idx_vals, motive)

      branches =
        cnames
        |> Enum.reduce_while({:ok, []}, fn cname, {:ok, acc} ->
          verdict = Map.fetch!(verdicts, cname)

          case Map.get(arm_map, cname) do
            {:matched, pattern, body_expr} ->
              case elaborate_matched_branch(
                     verdict,
                     pattern,
                     body_expr,
                     names,
                     ctx,
                     env,
                     param_vals,
                     idx_terms,
                     scrut_term,
                     result_type_term,
                     carried,
                     motive
                   ) do
                {:ok, branch} -> {:cont, {:ok, acc ++ [branch]}}
                {:error, _} = err -> {:halt, err}
              end

            {:impossible_marked, _pattern} ->
              if verdict == :impossible do
                # omit (K4 §H)
                {:cont, {:ok, acc}}
              else
                {:halt, {:error, {:reachable_impossible, cname}}}
              end

            nil ->
              # omitted constructor — discharge if impossible, else covered by a
              # variable/wildcard catch-all (`x -> …`), else a genuine gap.
              cond do
                verdict == :impossible ->
                  # omit (K4 §H)
                  {:cont, {:ok, acc}}

                # The join point covers this constructor: leave a marker whose body
                # `wrap_join/2` fills with `{:app, j, scrut}` once it knows the
                # let-binder's depth. The catch-all body is elaborated exactly once,
                # below, instead of once per uncovered constructor.
                join? ->
                  arity = length(Inductive.get_ctor(env, cname).args)
                  {:cont, {:ok, acc ++ [{cname, arity, @join_marker}]}}

                default != nil ->
                  case elaborate_default_branch(
                         verdict,
                         cname,
                         default,
                         names,
                         ctx,
                         env,
                         param_vals,
                         idx_terms,
                         scrut_term,
                         result_type_term,
                         carried,
                         motive
                       ) do
                    {:ok, branch} -> {:cont, {:ok, acc ++ [branch]}}
                    {:error, _} = err -> {:halt, err}
                  end

                true ->
                  {:halt, {:error, {:missing_branch, cname}}}
              end
          end
        end)

      with {:ok, brs} <- branches,
           {:ok, join} <- elaborate_join(join?, default, names, ctx, env, motive) do
        {:ok, brs, join}
      end
    end
  end

  defp merge_known_ctor_args(:impossible, _args, _depth), do: :impossible

  defp merge_known_ctor_args(verdict, args, depth) do
    arity = length(args)

    value_subst =
      args
      |> Enum.with_index()
      |> Map.new(fn {value, p} ->
        ctor_key = arity - 1 - p
        shifted = value |> Quote.reify(depth) |> Cure.Core.Term.shift(arity, 0)

        case shifted do
          {:var, outer_key} -> {outer_key, {:var, ctor_key}}
          closed -> {ctor_key, closed}
        end
      end)

    index_subst =
      case verdict do
        {:solved, subst} -> subst
        :trivial -> %{}
      end

    {:solved, Map.merge(index_subst, value_subst)}
  end

  # --- as-pattern desugaring (parity #4) -------------------------------------
  #
  # `name @ <pattern>` binds the whole matched value to `name` as well as
  # destructuring it. Inline `{:as_pattern, _, [name, sub]}` nodes may sit at the
  # arm's top level OR nested inside constructor arguments (`Cons(h, t @ …)`).
  # Strip them out of the pattern tree and, since a pattern and its
  # value-reconstruction share the same surface shape, substitute each `name` by
  # its (cleaned) sub-pattern in the body — the cleaned pattern then flows through
  # nested-pattern lowering unchanged.
  defp desugar_as_patterns(arms) do
    Enum.reduce_while(arms, {:ok, []}, fn {:match_arm, meta, body} = arm, {:ok, acc} ->
      pattern = Keyword.fetch!(meta, :pattern)
      {clean, subs} = strip_as_patterns(pattern)

      shadowed =
        Enum.find(subs, fn {name, _reconstruction} ->
          binds_any?(single_body(body), [name])
        end)

      cond do
        subs == [] ->
          {:cont, {:ok, acc ++ [arm]}}

        shadowed != nil ->
          {name, reconstruction} = shadowed

          {:halt,
           {:error,
            {:unsupported_pattern,
             %{
               reason: :shadowed_as,
               name: name,
               span: as_pattern_binding_span(pattern, name),
               type_span: surface_expression_span(reconstruction),
               shadow_span: first_binding_span(body, name)
             }}}}

        true ->
          b2 =
            Enum.reduce(subs, single_body(body), fn {name, recon}, b ->
              subst_surface_var(b, name, recon)
            end)

          {:cont, {:ok, acc ++ [{:match_arm, Keyword.put(meta, :pattern, clean), b2}]}}
      end
    end)
  end

  defp as_pattern_binding_span({:as_pattern, meta, [name, _subpattern]}, name) do
    case Cure.MetaAST.Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{name: %Cure.Diagnostic.Span{} = span} -> span
      %Cure.MetaAST.SourceInfo{whole: %Cure.Diagnostic.Span{} = span} -> span
      _ -> nil
    end
  end

  defp as_pattern_binding_span({_tag, _meta, children}, name) when is_list(children),
    do: Enum.find_value(children, &as_pattern_binding_span(&1, name))

  defp as_pattern_binding_span(list, name) when is_list(list),
    do: Enum.find_value(list, &as_pattern_binding_span(&1, name))

  defp as_pattern_binding_span(_other, _name), do: nil

  # Strip inline as-patterns from a pattern tree → `{cleaned_pattern, [{name,
  # reconstruction}]}`. The reconstruction is the cleaned sub-pattern (valid as an
  # expression). Handles nesting: `w @ S(t @ Z())` yields `w ↦ S(Z())`, `t ↦ Z()`.
  defp strip_as_patterns({:as_pattern, _m, [name, sub]}) do
    {clean_sub, subs} = strip_as_patterns(sub)
    {clean_sub, [{name, strip_named_implicits(clean_sub)} | subs]}
  end

  defp strip_as_patterns({:function_call, m, args}) do
    {clean_args, subs} =
      Enum.map_reduce(args, [], fn a, acc ->
        {ca, s} = strip_as_patterns(a)
        {ca, acc ++ s}
      end)

    {{:function_call, m, clean_args}, subs}
  end

  defp strip_as_patterns(other), do: {other, []}

  # --- tuple sub-patterns inside a constructor argument (parity #4) -----------
  #
  # `A(%[x, y]) -> body` destructures a Σ-typed field. Replace each tuple
  # constructor-argument with a fresh `$tup_i` binder (the `$` prefix cannot clash
  # with a user identifier) and substitute the tuple's variables by projections of
  # that binder in the body — so `A(%[x, y]) -> body` becomes
  # `A($tup_0) -> body[x ↦ $tup_0.1, y ↦ $tup_0.2]`, which then flows through the
  # ordinary all-variable constructor path. Only direct constructor arguments are
  # rewritten; a top-level tuple pattern is left for `try_tuple_match`, and a tuple
  # nested inside a *nested* constructor falls through to that path's clean error.
  defp desugar_tuple_args(arms) do
    arms
    |> desugar_refutable_tuple_arg_groups()
    |> case do
      {:ok, grouped} -> desugar_irrefutable_tuple_args(grouped)
      {:error, _reason} = error -> error
    end
  end

  defp desugar_irrefutable_tuple_args(arms) do
    Enum.reduce_while(arms, {:ok, []}, fn {:match_arm, meta, body} = arm, {:ok, acc} ->
      case strip_tuple_args_in_ctor(Keyword.fetch!(meta, :pattern)) do
        {:ok, _clean, []} ->
          {:cont, {:ok, acc ++ [arm]}}

        {:ok, clean, subs} ->
          b = single_body(body)

          case Enum.find(subs, fn {name, _projection} -> binds_any?(b, [name]) end) do
            {name, _projection} ->
              pattern = Keyword.fetch!(meta, :pattern)

              {:halt,
               {:error,
                {:unsupported_pattern,
                 %{
                   reason: :shadowed_tuple_arg,
                   name: name,
                   span: pattern_binder_span(pattern, name),
                   type_span: tuple_pattern_span_for_name(pattern, name),
                   shadow_span: first_binding_span(body, name)
                 }}}}

            nil ->
              b2 = Enum.reduce(subs, b, fn {n, r}, acc_b -> subst_surface_var(acc_b, n, r) end)
              {:cont, {:ok, acc ++ [{:match_arm, Keyword.put(meta, :pattern, clean), b2}]}}
          end

        {:error, :refutable_tuple_element} ->
          # A refutable tuple combined with another nested constructor column is
          # left intact for the general pattern matrix, which expands tuple
          # columns into projection scrutinees.
          {:cont, {:ok, acc ++ [arm]}}

        {:error, _reason} = error ->
          {:halt, error}
      end
    end)
  end

  defp desugar_refutable_tuple_arg_groups(arms) do
    order =
      arms
      |> Enum.map(fn arm ->
        case arm_pattern(arm) do
          {:function_call, meta, _arguments} -> {:constructor, Keyword.fetch!(meta, :name)}
          pattern -> {:other, pattern}
        end
      end)
      |> Enum.uniq()

    grouped =
      Enum.group_by(arms, fn arm ->
        case arm_pattern(arm) do
          {:function_call, meta, _arguments} -> {:constructor, Keyword.fetch!(meta, :name)}
          pattern -> {:other, pattern}
        end
      end)

    Enum.reduce_while(order, {:ok, []}, fn key, {:ok, accumulated} ->
      group = Map.fetch!(grouped, key)

      case desugar_refutable_tuple_arg_group(group) do
        {:ok, rewritten} -> {:cont, {:ok, accumulated ++ rewritten}}
        {:error, _reason} = error -> {:halt, error}
      end
    end)
  end

  defp desugar_refutable_tuple_arg_group([{:match_arm, meta, _body} | _rest] = arms) do
    case Keyword.fetch!(meta, :pattern) do
      {:function_call, function_meta, arguments} ->
        case refutable_tuple_argument_index(arms) do
          nil ->
            {:ok, arms}

          tuple_index ->
            if refutable_tuple_group_supported?(arms, tuple_index) do
              lower_refutable_tuple_argument_group(arms, function_meta, arguments, tuple_index)
            else
              {:ok, arms}
            end
        end

      _other ->
        {:ok, arms}
    end
  end

  defp refutable_tuple_argument_index(arms) do
    Enum.find_value(arms, fn arm ->
      case arm_pattern(arm) do
        {:function_call, _meta, arguments} ->
          Enum.find_index(arguments, fn
            {:tuple, _tuple_meta, elements} ->
              match?(
                {:error, :refutable_tuple_element},
                tuple_subs(elements, {:variable, [], "$p"})
              )

            _other ->
              false
          end)

        _other ->
          nil
      end
    end)
  end

  defp refutable_tuple_group_supported?(arms, tuple_index) do
    Enum.all?(arms, fn arm ->
      case arm_pattern(arm) do
        {:function_call, _meta, arguments} ->
          match?({:tuple, _tuple_meta, _elements}, Enum.at(arguments, tuple_index)) and
            arguments
            |> List.delete_at(tuple_index)
            |> Enum.all?(fn
              {:variable, _meta, _name} -> true
              {:named_implicit_pat, _meta, _children} -> true
              _other -> false
            end)

        _other ->
          false
      end
    end)
  end

  defp lower_refutable_tuple_argument_group(arms, function_meta, arguments, tuple_index) do
    tag = fresh_tag()

    fresh_arguments =
      arguments
      |> Enum.with_index()
      |> Enum.map(fn
        {{:named_implicit_pat, _meta, _children} = pattern, _index} -> pattern
        {_argument, index} -> {:variable, [], "$tuple_arg_" <> tag <> Integer.to_string(index)}
      end)

    inner_arms =
      Enum.reduce_while(arms, {:ok, []}, fn {:match_arm, meta, body}, {:ok, accumulated} ->
        {:function_call, _call_meta, row_arguments} = Keyword.fetch!(meta, :pattern)

        substitutions =
          row_arguments
          |> Enum.with_index()
          |> Enum.flat_map(fn
            {{:variable, _variable_meta, "_"}, _index} ->
              []

            {{:variable, _variable_meta, name}, index} when index != tuple_index ->
              [{name, Enum.at(fresh_arguments, index)}]

            _other ->
              []
          end)

        expressions = [single_body(body) | List.wrap(Keyword.get(meta, :guard))]

        case Enum.find(substitutions, fn {name, _replacement} ->
               Enum.any?(expressions, &binds_any?(&1, [name]))
             end) do
          {name, _replacement} ->
            pattern = Keyword.fetch!(meta, :pattern)

            {:halt,
             {:error,
              {:unsupported_pattern,
               %{
                 reason: :shadowed_nested,
                 name: name,
                 span: pattern_binder_span(pattern, name),
                 type_span: surface_expression_span(pattern),
                 shadow_span: first_binding_span(expressions, name)
               }}}}

          nil ->
            rewrite = fn expression ->
              Enum.reduce(substitutions, expression, fn {name, replacement}, rewritten ->
                subst_surface_var(rewritten, name, replacement)
              end)
            end

            inner_meta =
              meta
              |> Keyword.put(:pattern, Enum.at(row_arguments, tuple_index))
              |> then(fn inner_meta ->
                case Keyword.fetch(inner_meta, :guard) do
                  {:ok, guard} -> Keyword.put(inner_meta, :guard, rewrite.(guard))
                  :error -> inner_meta
                end
              end)

            inner_arm = {:match_arm, inner_meta, [rewrite.(single_body(body))]}
            {:cont, {:ok, accumulated ++ [inner_arm]}}
        end
      end)

    with {:ok, inner_arms} <- inner_arms do
      tuple_scrutinee = Enum.at(fresh_arguments, tuple_index)
      inner_match = {:pattern_match, [], [tuple_scrutinee | inner_arms]}
      outer_pattern = {:function_call, function_meta, fresh_arguments}
      {:ok, [{:match_arm, [pattern: outer_pattern], [inner_match]}]}
    end
  end

  defp tuple_pattern_span_for_name({:tuple, _meta, children} = tuple, name) do
    if name in pattern_binders(children), do: surface_expression_span(tuple), else: nil
  end

  defp tuple_pattern_span_for_name({_tag, _meta, children}, name) when is_list(children),
    do: Enum.find_value(children, &tuple_pattern_span_for_name(&1, name))

  defp tuple_pattern_span_for_name(list, name) when is_list(list),
    do: Enum.find_value(list, &tuple_pattern_span_for_name(&1, name))

  defp tuple_pattern_span_for_name(_other, _name), do: nil

  defp strip_tuple_args_in_ctor({:function_call, m, args}) do
    args
    |> Enum.with_index()
    |> Enum.reduce_while({:ok, [], []}, fn {arg, i}, {:ok, cargs, subs} ->
      case arg do
        {:tuple, _tm, [_, _ | _] = elems} ->
          fresh_var = {:variable, [], "$tup_" <> Integer.to_string(i)}

          case tuple_subs(elems, fresh_var) do
            {:ok, s} -> {:cont, {:ok, cargs ++ [fresh_var], subs ++ s}}
            {:error, _} = err -> {:halt, err}
          end

        _ ->
          {:cont, {:ok, cargs ++ [arg], subs}}
      end
    end)
    |> case do
      {:ok, cargs, subs} -> {:ok, {:function_call, m, cargs}, subs}
      {:error, _} = err -> err
    end
  end

  defp strip_tuple_args_in_ctor(other), do: {:ok, other, []}

  # --- tuple-scrutinee matching (parity #6) ----------------------------------
  # Multi-parameter function clauses are represented as a match over a flat
  # tuple of arguments. When exactly one parameter column contains structural
  # patterns, project that column and turn the rows into an ordinary
  # single-scrutinee match. The other columns are irrefutable variables or
  # wildcards; substitute their tuple projections into each body. This preserves
  # source-order fallthrough and lets the existing List/constructor/literal
  # match machinery handle the selected column without teaching tuple matching
  # every data family.
  defp desugar_single_refutable_tuple_column(
         {:variable, _meta, _name} = scrut,
         [{:match_arm, _, _} | _] = arms
       ) do
    with {:ok, rows, arity} <- flat_tuple_rows(arms),
         [column] <- refutable_tuple_columns(rows, arity),
         projections = Enum.map(1..arity, &tuple_proj(scrut, Integer.to_string(&1))),
         {:ok, projected_arms} <- project_tuple_column_rows(rows, projections, column) do
      {tuple_proj(scrut, Integer.to_string(column + 1)), desugar_list_patterns(projected_arms)}
    else
      _ -> {scrut, arms}
    end
  end

  defp desugar_single_refutable_tuple_column(
         {:tuple, _meta, elems} = scrut,
         [{:match_arm, _, _} | _] = arms
       )
       when length(elems) >= 2 do
    with {:ok, rows, arity} <- flat_tuple_rows(arms),
         true <- arity == length(elems),
         true <- Enum.all?(elems, &match?({:variable, _, _}, &1)),
         [column] <- refutable_tuple_columns(rows, arity),
         {:ok, projected_arms} <- project_tuple_column_rows(rows, elems, column) do
      {Enum.at(elems, column), desugar_list_patterns(projected_arms)}
    else
      _ -> {scrut, arms}
    end
  end

  defp desugar_single_refutable_tuple_column(scrut, arms), do: {scrut, arms}

  defp flat_tuple_rows(arms) do
    Enum.reduce_while(arms, {:ok, [], nil}, fn
      {:match_arm, meta, body}, {:ok, rows, arity} ->
        case Keyword.fetch!(meta, :pattern) do
          {:tuple, _tm, pats} when length(pats) >= 2 and (is_nil(arity) or length(pats) == arity) ->
            {:cont, {:ok, rows ++ [{pats, meta, body}], length(pats)}}

          _ ->
            {:halt, :not_applicable}
        end

      _other, _acc ->
        {:halt, :not_applicable}
    end)
  end

  # Columns carrying structural patterns, excluding those whose pattern is
  # itself a tuple. Projecting such a column would hand a tuple pattern to
  # single-scrutinee matching, which cannot destructure one — that is
  # `desugar_tuple_scrutinee`'s job, and it needs the tuple still in place.
  defp refutable_tuple_columns(rows, arity) do
    Enum.filter(0..(arity - 1), fn column ->
      patterns = Enum.map(rows, fn {pats, _meta, _body} -> Enum.at(pats, column) end)

      Enum.any?(patterns, &(not catchall_pat?(&1))) and
        not Enum.any?(patterns, &match?({:tuple, _meta, _elems}, &1))
    end)
  end

  defp project_tuple_column_rows(rows, projections, selected) do
    Enum.reduce_while(rows, {:ok, []}, fn {pats, meta, body}, {:ok, acc} ->
      other_refutable? =
        pats
        |> Enum.with_index()
        |> Enum.any?(fn {pat, column} -> column != selected and not catchall_pat?(pat) end)

      if other_refutable? do
        {:halt, :not_applicable}
      else
        subs =
          pats
          |> Enum.with_index(1)
          |> Enum.flat_map(fn
            {{:variable, _m, "_"}, _column} -> []
            {{:variable, _m, name}, column} -> [{name, Enum.at(projections, column - 1)}]
            {_structural, _column} -> []
          end)

        b = single_body(body)

        if binds_any?(b, Enum.map(subs, &elem(&1, 0))) do
          {:halt, {:error, {:unsupported_pattern, :shadowed_tuple}}}
        else
          b2 = Enum.reduce(subs, b, fn {name, replacement}, expr -> subst_surface_var(expr, name, replacement) end)
          selected_pat = Enum.at(pats, selected)
          meta2 = Keyword.put(meta, :pattern, selected_pat)
          {:cont, {:ok, acc ++ [{:match_arm, meta2, [b2]}]}}
        end
      end
    end)
  end

  #
  # `match %[e₀, e₁, …] | %[p₀, p₁, …] -> body` (simultaneous / Idris'
  # `case (e₀, e₁) of`) is desugared, ONE column at a time, into a nested
  # single-scrutinee match `match e₀ | p₀ -> match %[e₁, …] | %[p₁, …] -> body`.
  # The remaining columns re-enter this same path (their scrutinee is a smaller
  # tuple, or the bare element when only one column is left), so the whole tree
  # is built by re-entry. Each first-column constructor keeps its argument
  # patterns inline, so `desugar_nested_arms` still lowers any nested args, and
  # the inner match on an index-refined scrutinee elides the impossible sibling
  # constructors (e.g. two `Vector`s that share index `n` cannot be `empty`/
  # `prepend`), exactly as the hand-written nested form relies on.
  #
  # Fires only for a tuple scrutinee (≥2 elems) whose arms are ALL guardless
  # tuple patterns of matching arity, with DISTINCT constructor heads in the
  # first column. Anything else (non-tuple scrutinee, a variable/wildcard or a
  # repeated head in the first column) is returned UNCHANGED, so ordinary
  # matches are untouched and still-unsupported shapes reach their existing
  # clean rejection rather than being miscompiled.
  defp desugar_tuple_scrutinee({:tuple, _meta, elems} = scrut, arms)
       when length(elems) >= 2 do
    with {:ok, rows} <- tuple_scrutinee_rows(elems, arms),
         {:ok, new_scrut, new_arms} <- split_first_tuple_column(elems, rows) do
      {new_scrut, new_arms}
    else
      _ -> {scrut, arms}
    end
  end

  defp desugar_tuple_scrutinee(scrut, arms), do: {scrut, arms}

  # Validate every arm is a guardless tuple pattern of the scrutinee's arity;
  # return the rows as `{[col-patterns], body-expr}`.
  defp tuple_scrutinee_rows(elems, arms) do
    n = length(elems)

    Enum.reduce_while(arms, {:ok, []}, fn
      {:match_arm, meta, body}, {:ok, acc} ->
        case Keyword.fetch!(meta, :pattern) do
          {:tuple, _tm, pats} when length(pats) == n ->
            if Keyword.has_key?(meta, :guard) do
              {:halt, :not_applicable}
            else
              {:cont, {:ok, acc ++ [{pats, single_body(body)}]}}
            end

          _ ->
            {:halt, :not_applicable}
        end

      _other, _acc ->
        {:halt, :not_applicable}
    end)
  end

  # Split the first column: outer scrutinee `e₀`, one outer arm per row keeping
  # its first-column pattern, whose body matches the remaining columns. Requires
  # all first-column patterns to be constructors with distinct heads (disjoint,
  # so first-match order is preserved and no row is shadowed).
  defp split_first_tuple_column([e0 | erest], rows) do
    col0 = Enum.map(rows, fn {[p0 | _], _} -> p0 end)

    constructor_heads =
      Enum.flat_map(col0, fn
        {:function_call, fm, _} -> [Keyword.fetch!(fm, :name)]
        _ -> []
      end)

    cond do
      not Enum.all?(col0, fn
        {:function_call, _meta, _arguments} -> true
        {:variable, _meta, _name} -> true
        _ -> false
      end) ->
        :not_applicable

      not distinct?(constructor_heads) ->
        :not_applicable

      # A catch-all row is a continuation for an inner-column mismatch. Splitting
      # it into a sibling outer arm would commit to an earlier constructor and
      # lose that fallthrough. Ordered tuple lowering below preserves it.
      Enum.any?(col0, &match?({:variable, _meta, _name}, &1)) ->
        :not_applicable

      true ->
        arms =
          Enum.map(rows, fn {[p0 | prest], body} ->
            {:match_arm, [pattern: p0], [build_inner_tuple_match(erest, prest, body)]}
          end)

        {:ok, e0, arms}
    end
  end

  # The remaining columns become the inner match. A single remaining column is a
  # bare single-scrutinee match; two or more re-enter `desugar_tuple_scrutinee`
  # as a smaller tuple scrutinee.
  defp build_inner_tuple_match([e1], [p1], body) do
    {:pattern_match, [], [e1, {:match_arm, [pattern: p1], [body]}]}
  end

  defp build_inner_tuple_match(erest, prest, body) when length(erest) >= 2 do
    {:pattern_match, [], [{:tuple, [], erest}, {:match_arm, [pattern: {:tuple, [], prest}], [body]}]}
  end

  defp distinct?(list), do: length(Enum.uniq(list)) == length(list)

  # --- tuple-pattern matching (parity #4) ------------------------------------
  #
  # A Σ/pair is irrefutable — a single tuple-pattern arm `%[x, y] -> body` just
  # destructures. Lower it to the (already-supported) projections `.1`/`.2`:
  # `body[x ↦ p.1, y ↦ p.2]`, elaborated directly. Restricted to a VARIABLE
  # scrutinee (so the projections are cheap and re-evaluation-free) and a flat
  # tuple of variables/wildcards. The scrutinee type owns the arity: checking it
  # here prevents unused extra binders from making a malformed pattern appear to
  # work merely because their out-of-bounds projections are never elaborated.
  defp try_tuple_match(
         {:tuple, _scrut_meta, scrut_elements},
         [
           {:match_arm, tuple_meta, tuple_body},
           {:match_arm, fallback_meta, fallback_body}
         ],
         expected,
         names,
         ctx,
         env
       )
       when length(scrut_elements) >= 2 do
    pattern = Keyword.fetch!(tuple_meta, :pattern)
    fallback_pattern = Keyword.fetch!(fallback_meta, :pattern)

    case {pattern, fallback_pattern} do
      {{:tuple, _pattern_meta, elements}, {:variable, _fallback_meta, fallback_name}}
      when length(elements) == length(scrut_elements) ->
        # A tuple literal of variables is already an evaluated collection of
        # scrutinees, so compile its structural elements directly. This is the
        # simultaneous-match surface used by algorithms that advance multiple
        # lists in lockstep (`match %[xs, ys]`). Non-variable tuple expressions
        # retain the existing path so an effectful expression is never copied.
        if Enum.all?(scrut_elements, &match?({:variable, _meta, _name}, &1)) do
          fallback =
            if fallback_name == "_",
              do: single_body(fallback_body),
              else: subst_surface_var(single_body(fallback_body), fallback_name, {:tuple, [], scrut_elements})

          {success, structural, equalities} =
            compile_tuple_row(elements, scrut_elements, single_body(tuple_body))

          success =
            Enum.reduce(Enum.reverse(equalities), success, fn {left, right}, body ->
              condition = {:binary_op, [category: :comparison, operator: :==], [left, right]}
              {:conditional, [], [condition, body, fallback]}
            end)

          decision =
            Enum.reduce(Enum.reverse(structural), success, fn {value, nested_pattern}, body ->
              nested_pattern_decision(value, nested_pattern, body, fallback)
            end)

          elaborate_expr_checked(decision, expected, names, ctx, env)
        else
          :not_applicable
        end

      {{:tuple, _pattern_meta, _elements}, {:tuple, _fallback_meta, _fallback_elements}} ->
        arms = [
          {:match_arm, tuple_meta, tuple_body},
          {:match_arm, fallback_meta, fallback_body}
        ]

        patterns = [pattern, fallback_pattern]

        if Enum.all?(scrut_elements, &match?({:variable, _meta, _name}, &1)) do
          with :ok <- validate_tuple_pattern_arities(patterns, length(scrut_elements)) do
            lower_ordered_tuple_rows(scrut_elements, arms, expected, names, ctx, env)
          end
        else
          :not_applicable
        end

      _ ->
        :not_applicable
    end
  end

  # Keep the general all-tuple matrix clause after the tuple-plus-catchall
  # clause above. Otherwise its broad `length(arms) >= 2` head claims a
  # two-arm match, returns `:not_applicable` for the catchall, and prevents the
  # ordered-row lowering from ever seeing the match.
  defp try_tuple_match({:tuple, _scrut_meta, scrut_elements}, arms, expected, names, ctx, env)
       when length(scrut_elements) >= 2 and length(arms) >= 2 do
    patterns = Enum.map(arms, fn {:match_arm, meta, _body} -> Keyword.fetch!(meta, :pattern) end)

    if Enum.all?(scrut_elements, &match?({:variable, _meta, _name}, &1)) and
         Enum.all?(patterns, &match?({:tuple, _meta, _elements}, &1)) do
      with :ok <- validate_tuple_pattern_arities(patterns, length(scrut_elements)) do
        lower_ordered_tuple_rows(scrut_elements, arms, expected, names, ctx, env)
      end
    else
      :not_applicable
    end
  end

  defp try_tuple_match(
         {:variable, _sm, _sn} = scrut,
         [
           {:match_arm, tuple_meta, tuple_body},
           {:match_arm, fallback_meta, fallback_body}
         ],
         expected,
         names,
         ctx,
         env
       ) do
    pattern = Keyword.fetch!(tuple_meta, :pattern)
    fallback_pattern = Keyword.fetch!(fallback_meta, :pattern)

    case {pattern, fallback_pattern} do
      {{:tuple, _tm, elements}, {:variable, _fm, fallback_name}} ->
        with {:ok, tuple_arity} <- tuple_pattern_arity(scrut, names, ctx, env),
             :ok <- validate_tuple_pattern_arity(pattern, tuple_arity, length(elements)) do
          fallback =
            if fallback_name == "_",
              do: single_body(fallback_body),
              else: subst_surface_var(single_body(fallback_body), fallback_name, scrut)

          projections = Enum.map(1..tuple_arity, &tuple_proj(scrut, Integer.to_string(&1)))

          {success, structural, equalities} =
            compile_tuple_row(elements, projections, single_body(tuple_body))

          success =
            Enum.reduce(Enum.reverse(equalities), success, fn {left, right}, body ->
              condition =
                {:binary_op, [category: :comparison, operator: :==], [left, right]}

              {:conditional, [], [condition, body, fallback]}
            end)

          decision =
            Enum.reduce(Enum.reverse(structural), success, fn {projection, nested_pattern}, body ->
              nested_pattern_decision(projection, nested_pattern, body, fallback)
            end)

          elaborate_expr_checked(decision, expected, names, ctx, env)
        end

      {{:tuple, _tm, _elements}, {:tuple, _fm, _fallback_elements}} ->
        # A generated two-row decision commonly ends with an explicit tuple of
        # wildcards (`%[_, _]`) rather than a scalar `_`. This clause used to
        # claim that shape and return `:not_applicable`, preventing the general
        # all-tuple matrix clause below from running.
        arms = [
          {:match_arm, tuple_meta, tuple_body},
          {:match_arm, fallback_meta, fallback_body}
        ]

        patterns = [pattern, fallback_pattern]

        with {:ok, tuple_arity} <- tuple_pattern_arity(scrut, names, ctx, env),
             :ok <- validate_tuple_pattern_arities(patterns, tuple_arity) do
          lower_refutable_tuple_match(scrut, arms, tuple_arity, expected, names, ctx, env)
        end

      _ ->
        :not_applicable
    end
  end

  defp try_tuple_match({:variable, _sm, _sn} = scrut, [{:match_arm, meta, body}], expected, names, ctx, env) do
    case Keyword.fetch!(meta, :pattern) do
      {:tuple, _tm, elems} = pattern when is_list(elems) ->
        with {:ok, tuple_arity} <- tuple_pattern_arity(scrut, names, ctx, env),
             :ok <- validate_tuple_pattern_arity(pattern, tuple_arity, length(elems)) do
          case tuple_subs(elems, scrut) do
            {:ok, subs} ->
              b = single_body(body)

              case Enum.find(subs, fn {name, _projection} -> binds_any?(b, [name]) end) do
                {name, _projection} ->
                  {:error,
                   {:unsupported_pattern,
                    %{
                      reason: :shadowed_tuple,
                      name: name,
                      span: pattern_binder_span(pattern, name),
                      type_span: surface_expression_span(pattern),
                      shadow_span: first_binding_span(body, name)
                    }}}

                nil ->
                  b2 = Enum.reduce(subs, b, fn {n, r}, acc -> subst_surface_var(acc, n, r) end)
                  elaborate_expr_checked(b2, expected, names, ctx, env)
              end

            {:error, :refutable_tuple_element} ->
              lower_refutable_tuple_match(scrut, [{:match_arm, meta, body}], tuple_arity, expected, names, ctx, env)
          end
        end

      _ ->
        :not_applicable
    end
  end

  defp try_tuple_match({:variable, _sm, _sn} = scrut, arms, expected, names, ctx, env)
       when length(arms) >= 2 do
    patterns = Enum.map(arms, fn {:match_arm, meta, _body} -> Keyword.fetch!(meta, :pattern) end)

    if Enum.all?(patterns, &match?({:tuple, _meta, _elements}, &1)) do
      with {:ok, tuple_arity} <- tuple_pattern_arity(scrut, names, ctx, env),
           :ok <- validate_tuple_pattern_arities(patterns, tuple_arity) do
        lower_refutable_tuple_match(scrut, arms, tuple_arity, expected, names, ctx, env)
      end
    else
      :not_applicable
    end
  end

  defp try_tuple_match(_scrut, _arms, _expected, _names, _ctx, _env), do: :not_applicable

  defp compile_tuple_row(patterns, projections, body) do
    {substitutions, structural, _first_occurrences, equalities} =
      Enum.zip(patterns, projections)
      |> Enum.reduce({[], [], %{}, []}, fn
        {{:variable, _meta, "_"}, _projection}, acc ->
          acc

        {{:variable, _meta, name}, projection}, {subs, nested, first, equalities} ->
          case Map.fetch(first, name) do
            {:ok, original} ->
              {subs, nested, first, equalities ++ [{original, projection}]}

            :error ->
              {subs ++ [{name, projection}], nested, Map.put(first, name, projection), equalities}
          end

        {nested_pattern, projection}, {subs, nested, first, equalities} ->
          {subs, nested ++ [{projection, nested_pattern}], first, equalities}
      end)

    success =
      Enum.reduce(substitutions, body, fn {name, projection}, expression ->
        subst_surface_var(expression, name, projection)
      end)

    {success, structural, equalities}
  end

  defp nested_pattern_decision(value, pattern, success, fallback) do
    arms = [
      {:match_arm, [pattern: pattern], [success]},
      {:match_arm, [pattern: {:variable, [], "_"}], [fallback]}
    ]

    if special_match_arms?(arms) do
      case desugar_special_match(value, arms, 0) do
        {:ok, decision} -> decision
        {:error, _reason} -> {:pattern_match, [], [value | arms]}
      end
    else
      {:pattern_match, [], [value | arms]}
    end
  end

  defp validate_tuple_pattern_arities(patterns, tuple_arity) do
    Enum.reduce_while(patterns, :ok, fn {:tuple, _meta, elements} = pattern, :ok ->
      case validate_tuple_pattern_arity(pattern, tuple_arity, length(elements)) do
        :ok -> {:cont, :ok}
        {:error, _reason} = error -> {:halt, error}
      end
    end)
  end

  defp lower_refutable_tuple_match(scrut, arms, tuple_arity, expected, names, ctx, env) do
    projections = for index <- 1..tuple_arity, do: tuple_proj(scrut, Integer.to_string(index))

    # A final catch-all is ordered row fallthrough, not merely a coverage arm.
    # Column splitting would commit after the first matching constructor and an
    # inner-column mismatch could never reach that final row.
    if guardless_tuple_catchall?(List.last(arms)) do
      lower_ordered_tuple_rows(projections, arms, expected, names, ctx, env)
    else
      lower_refutable_tuple_match_by_columns(arms, tuple_arity, expected, names, ctx, env, projections)
    end
  end

  defp lower_refutable_tuple_match_by_columns(arms, tuple_arity, expected, names, ctx, env, projections) do
    position = tuple_refutable_position(arms, tuple_arity)
    reordered_projections = move_tuple_position_first(projections, position)

    reordered_arms =
      Enum.map(arms, fn {:match_arm, meta, body} ->
        {:tuple, tuple_meta, elements} = Keyword.fetch!(meta, :pattern)
        pattern = {:tuple, tuple_meta, move_tuple_position_first(elements, position)}
        {:match_arm, Keyword.put(meta, :pattern, pattern), body}
      end)

    synthetic_scrutinee = {:tuple, [], reordered_projections}
    {lowered_scrutinee, lowered_arms} = desugar_tuple_scrutinee(synthetic_scrutinee, reordered_arms)

    if lowered_scrutinee == synthetic_scrutinee do
      lower_ordered_tuple_rows(projections, arms, expected, names, ctx, env)
    else
      lowered_scrutinee
      |> elaborate_match(lowered_arms, expected, names, ctx, env)
      |> contextualize_tuple_pattern_result(arms, tuple_arity, position)
    end
  end

  # The column-splitting fast path above produces compact dependent cases when
  # constructor heads are disjoint.  General ordered matrices (for example
  # `%[Pending(), Submit()]`, `%[Pending(), Cancel()]`, `%[_, Kill()]`) need to
  # preserve source-order fallthrough instead.  Compile each row into decisions
  # over the tuple projections, folding from the last row to the first.
  defp lower_ordered_tuple_rows(projections, arms, expected, names, ctx, env) do
    if guardless_tuple_catchall?(List.last(arms)) do
      decision =
        Enum.reduce(Enum.reverse(arms), nil, fn {:match_arm, meta, body}, fallback ->
          {:tuple, _tuple_meta, patterns} = Keyword.fetch!(meta, :pattern)
          row_body = single_body(body)
          fallback = fallback || row_body
          {success, structural, equalities} = compile_tuple_row(patterns, projections, row_body)

          success =
            case Keyword.fetch(meta, :guard) do
              {:ok, guard} ->
                {bound_guard, _guard_structural, _guard_equalities} =
                  compile_tuple_row(patterns, projections, guard)

                {:conditional, [], [bound_guard, success, fallback]}

              :error ->
                success
            end

          success =
            Enum.reduce(Enum.reverse(equalities), success, fn {left, right}, expression ->
              condition = {:binary_op, [category: :comparison, operator: :==], [left, right]}
              {:conditional, [], [condition, expression, fallback]}
            end)

          Enum.reduce(Enum.reverse(structural), success, fn {projection, pattern}, expression ->
            nested_pattern_decision(projection, pattern, expression, fallback)
          end)
        end)

      elaborate_expr_checked(decision, expected, names, ctx, env)
    else
      {:error,
       {:unsupported_pattern,
        %{
          reason: :tuple_pattern_matrix,
          span: arms |> hd() |> arm_pattern() |> surface_expression_span()
        }}}
    end
  end

  defp guardless_tuple_catchall?({:match_arm, meta, _body}) do
    not Keyword.has_key?(meta, :guard) and
      case Keyword.fetch!(meta, :pattern) do
        {:tuple, _tuple_meta, patterns} -> Enum.all?(patterns, &catchall_pat?/1)
        _ -> false
      end
  end

  defp tuple_refutable_position(arms, tuple_arity) do
    Enum.find(1..tuple_arity, 1, fn position ->
      Enum.any?(arms, fn arm ->
        element = arm |> arm_pattern() |> elem(2) |> Enum.at(position - 1)
        not match?({:variable, _meta, _name}, element)
      end)
    end)
  end

  defp move_tuple_position_first(elements, 1), do: elements

  defp move_tuple_position_first(elements, position) do
    {selected, rest} = List.pop_at(elements, position - 1)
    [selected | rest]
  end

  defp contextualize_tuple_pattern_result(
         {:error, {:source_context, {:missing_branch, branch}, context}},
         arms,
         tuple_arity,
         position
       ) do
    details =
      arms
      |> tuple_pattern_error_context(tuple_arity, position)
      |> Map.put(:branch, branch)

    {:error,
     {:source_context, {:tuple_missing_branch, details},
      context
      |> Map.merge(details)}}
  end

  defp contextualize_tuple_pattern_result({:error, {:missing_branch, branch}}, arms, tuple_arity, position),
    do:
      {:error,
       {:tuple_missing_branch, Map.put(tuple_pattern_error_context(arms, tuple_arity, position), :branch, branch)}}

  defp contextualize_tuple_pattern_result(result, _arms, _tuple_arity, _position), do: result

  defp contextualize_authored_tuple_pattern_result(result, authored_arms, env) do
    case missing_branch_reason(result) do
      {:ok, branch, existing_context} ->
        case authored_tuple_arms(authored_arms, branch, env) do
          [] ->
            result

          tuple_arms ->
            {:tuple, _meta, elements} = tuple_arms |> hd() |> arm_pattern()
            tuple_arity = length(elements)
            position = tuple_refutable_position(tuple_arms, tuple_arity)

            details =
              tuple_arms
              |> tuple_pattern_error_context(tuple_arity, position)
              |> Map.put(:branch, branch)

            reason = {:tuple_missing_branch, details}

            case existing_context do
              nil -> {:error, reason}
              context -> {:error, {:source_context, reason, Map.merge(context, details)}}
            end
        end

      :error ->
        result
    end
  end

  defp missing_branch_reason({:error, {:missing_branch, branch}}), do: {:ok, branch, nil}

  defp missing_branch_reason({:error, {:source_context, {:missing_branch, branch}, context}})
       when is_map(context),
       do: {:ok, branch, context}

  defp missing_branch_reason(_result), do: :error

  defp authored_tuple_arms(arms, branch, env) do
    branch_family = Inductive.ctor_family(env, branch)

    arms
    |> Enum.flat_map(fn {:match_arm, meta, body} ->
      pattern = Keyword.fetch!(meta, :pattern)

      case refutable_tuple_for_family(pattern, branch_family, env) do
        nil -> []
        tuple -> [{:match_arm, Keyword.put(meta, :pattern, tuple), body}]
      end
    end)
  end

  defp refutable_tuple_for_family({:tuple, _meta, elements} = tuple, branch_family, env) do
    if Enum.any?(elements, &pattern_from_family?(&1, branch_family, env)) do
      tuple
    else
      Enum.find_value(elements, &refutable_tuple_for_family(&1, branch_family, env))
    end
  end

  defp refutable_tuple_for_family({:function_call, _meta, arguments}, branch_family, env),
    do: Enum.find_value(arguments, &refutable_tuple_for_family(&1, branch_family, env))

  defp refutable_tuple_for_family({_tag, _meta, children}, branch_family, env) when is_list(children),
    do: Enum.find_value(children, &refutable_tuple_for_family(&1, branch_family, env))

  defp refutable_tuple_for_family(_pattern, _branch_family, _env), do: nil

  defp pattern_from_family?({:function_call, meta, _arguments}, branch_family, env) do
    name =
      case Keyword.fetch!(meta, :name) do
        name when is_binary(name) -> String.to_atom(name)
        name -> name
      end

    key = resolve_ctor_key(env, name)
    Inductive.ctor_family(env, key) == branch_family
  end

  defp pattern_from_family?(_pattern, _branch_family, _env), do: false

  defp tuple_pattern_error_context(arms, tuple_arity, position) do
    element_spans =
      Enum.flat_map(arms, fn arm ->
        case arm |> arm_pattern() |> elem(2) |> Enum.at(position - 1) |> surface_expression_span() do
          %Cure.Diagnostic.Span{} = span -> [span]
          _ -> []
        end
      end)

    insertion_span =
      case arms |> List.last() |> elem(2) |> single_body() |> surface_expression_span() do
        %Cure.Diagnostic.Span{} = span ->
          %{span | start_byte: span.end_byte, start_line: span.end_line, start_column: span.end_column}

        _ ->
          nil
      end

    %{
      tuple_pattern_position: position,
      tuple_pattern_arity: tuple_arity,
      tuple_pattern_element_spans: element_spans,
      tuple_pattern_insertion_span: insertion_span
    }
  end

  defp tuple_pattern_arity(scrut, names, ctx, env) do
    with {:ok, _term, type_value} <- elaborate_expr_typed(scrut, names, ctx, env),
         sigma_fam when not is_nil(sigma_fam) <- Inductive.builtin(env, :sigma) do
      type_term = Quote.reify(type_value, Context.length(ctx), Context.signature(ctx))
      unit_fam = unit_family_name(env)
      unit_ctor = unit_ctor_name(env)

      case count_tele(type_term, ctx, sigma_fam, unit_fam, unit_ctor, 0) do
        {:telescope, arity} -> {:ok, arity}
        :not_telescope -> bare_pair_arity(type_term, ctx, sigma_fam)
      end
    else
      _ -> :not_applicable
    end
  end

  defp bare_pair_arity(type_term, ctx, sigma_fam) do
    case Kernel.normalize(ctx, type_term) do
      {:data, ^sigma_fam, [_domain, _codomain], []} -> {:ok, 2}
      _ -> :not_applicable
    end
  end

  defp validate_tuple_pattern_arity(_pattern, arity, arity), do: :ok

  defp validate_tuple_pattern_arity(pattern, expected, actual) do
    {:error,
     {:source_context, {:tuple_arity_mismatch, expected, actual},
      %{
        span: surface_expression_span(pattern),
        expectation_origin: :pattern,
        expression_category: :tuple_pattern
      }}}
  end

  # A single variable/wildcard arm ignores the scrutinee's structure — an
  # irrefutable bind valid at ANY scrutinee type (Σ, primitive, data), not just
  # `{:vdata}`. The scrutinee is already elaborated (so it is well-typed) before
  # this runs; `_` discards it and a name binds the whole value. This lets a
  # pair/primitive scrutinee carry a lone catch-all without the vdata dispatch
  # rejecting it as `:match_scrutinee_not_data`.
  defp try_trivial_match(scrut_expr, [{:match_arm, meta, body}], expected, names, ctx, env) do
    case Keyword.fetch!(meta, :pattern) do
      {:variable, _m, "_"} ->
        if Keyword.get(meta, :impossible) do
          {:error, {:impossible_default_pattern, "_"}}
        else
          elaborate_expr_checked(single_body(body), expected, names, ctx, env)
        end

      {:variable, _m, name} = pattern ->
        b = single_body(body)

        cond do
          Keyword.get(meta, :impossible) ->
            {:error, {:impossible_default_pattern, name}}

          # A complex scrutinee would be duplicated by substitution; leave those to
          # the ordinary path (which binds via the case machinery).
          not match?({:variable, _sm, _sn}, scrut_expr) ->
            :not_applicable

          binds_any?(b, [name]) ->
            {:error,
             {:unsupported_pattern,
              %{
                reason: :shadowed_catchall,
                name: name,
                span: pattern_binder_span(pattern, name),
                type_span: surface_expression_span(scrut_expr),
                shadow_span: first_binding_span(body, name)
              }}}

          true ->
            elaborate_expr_checked(subst_surface_var(b, name, scrut_expr), expected, names, ctx, env)
        end

      _ ->
        :not_applicable
    end
  end

  defp try_trivial_match(_scrut, _arms, _expected, _names, _ctx, _env), do: :not_applicable

  # A `when` guard on a variable/catch-all pattern desugars to a `:case`-on-Bool
  # chain (`bool_case/5`): `match n | x when g -> a | x -> b` becomes
  # `case g[x↦n] of True -> a[x↦n] | False -> b`, each guarded arm testing its
  # guard and falling through (the `ff` branch) to the remaining arms. The chain
  # must end in an *unguarded* catch-all — the fall-through when every guard is
  # false — unless the untrusted Z3 lint proves the guards exhaustive, in which
  # case the final guarded arm becomes that catch-all (§2.3a); otherwise a
  # still-guarded final arm is non-exhaustive and rejected. Restricted to a
  # variable scrutinee so the substituted `n` is not duplicated-with-effects;
  # richer patterns error rather than silently drop the guard. Lowers through
  # `bool_case/5`; no kernel change. Returns `:not_applicable` only when NO arm
  # is guarded.
  defp try_guard_match(scrut_expr, arms, expected, names, ctx, env) do
    {unguarded_prefix, guarded_suffix} = Enum.split_while(arms, &(not guarded_arm?(&1)))

    cond do
      not Enum.any?(arms, &guarded_arm?/1) ->
        :not_applicable

      unguarded_prefix != [] and guarded_suffix != [] and
          Enum.all?(unguarded_prefix, &(not catchall_pat?(arm_pattern(&1)))) ->
        fallback =
          {:match_arm, [pattern: {:variable, [], "_"}], [{:pattern_match, [], [scrut_expr | guarded_suffix]}]}

        elaborate_match(scrut_expr, unguarded_prefix ++ [fallback], expected, names, ctx, env)

      # A variable scrutinee is substituted into the guard chain as-is: only a
      # variable is duplicated (no recomputation), so the surface path is safe.
      match?({:variable, _, _}, scrut_expr) ->
        guard_chain(scrut_expr, arms, expected, names, ctx, env, [])

      # A non-variable scrutinee would be DUPLICATED (and recomputed) by surface
      # substitution across the guard chain. Bind it ONCE under a fresh Core
      # λ and run the chain over the binder VARIABLE, so every substitution is of a
      # variable — a real `(λ s:T. <chain over s>) e` β-redex the kernel reduces
      # with `e` evaluated once. Closes the `:complex_scrutinee` reach gap.
      true ->
        bind_once_guard(scrut_expr, arms, expected, names, ctx, env)
    end
  end

  # Bind `scrut_expr` once under a fresh λ, then elaborate the guard chain with the
  # fresh binder as a (variable) scrutinee. The outer goal `expected` never mentions
  # the fresh binder, so it is shifted under the binder and the β-redex checks back
  # against `expected` exactly. The fresh name is depth-unique (`$gscrut<n>`) so a
  # nested non-variable guarded match binds a distinct name.
  defp bind_once_guard(scrut_expr, arms, expected, names, ctx, env) do
    with {:ok, scrut_core, scrut_type} <- elaborate_expr_typed(scrut_expr, names, ctx, env) do
      fresh = "$gscrut" <> Integer.to_string(Context.length(ctx))
      dom = Quote.reify(scrut_type, Context.length(ctx), Context.signature(ctx))
      ctx1 = Context.extend(ctx, scrut_type)
      names1 = [fresh | names]
      expected1 = Subst.shift(expected, 1, 0)

      with {:ok, chain} <-
             guard_chain({:variable, [], fresh}, arms, expected1, names1, ctx1, env, []) do
        {:ok, {:app, {:lam, Cure.Core.Grade.unrestricted(), dom, chain}, scrut_core}}
      end
    end
  end

  defp guarded_arm?({:match_arm, meta, _body}), do: Keyword.has_key?(meta, :guard)

  # The final arm closes the chain: it must be an unguarded catch-all — unless
  # the untrusted Z3 lint proves the chain's guards exhaustive (spec
  # 2026-07-08-guard-coverage-lint §2.3a), in which case the final guarded arm
  # IS the catch-all: its provably-true test is elided and its body goes
  # through the ordinary bind_catchall_body path, so the kernel re-checks
  # exactly the term an unguarded catch-all would have produced. Every lint
  # failure (unproven / untranslatable / Z3 unavailable) reproduces today's
  # rejection byte-for-byte — including when the final guard itself fails to
  # elaborate, which was never reached pre-lint.
  defp guard_chain(scrut_expr, [{:match_arm, meta, body}], expected, names, ctx, env, acc) do
    case Keyword.get(meta, :guard) do
      nil ->
        bind_catchall_body(
          scrut_expr,
          Keyword.fetch!(meta, :pattern),
          single_body(body),
          expected,
          names,
          ctx,
          env
        )

      guard ->
        pat = Keyword.fetch!(meta, :pattern)

        elaborated =
          with {:ok, guard_expr} <- guard_bind(scrut_expr, pat, guard) do
            elaborate_expr_checked(guard_expr, bool_type_term(Context.signature(ctx)), names, ctx, env)
          end

        case elaborated do
          {:ok, test} ->
            maybe_warn_shadowed(test, acc, ctx)

            if GuardLint.prove_exhaustive(acc ++ [test], ctx) == :proven do
              bind_catchall_body(scrut_expr, pat, single_body(body), expected, names, ctx, env)
            else
              {:error, {:unsupported_guard, :non_exhaustive}}
            end

          _error ->
            {:error, {:unsupported_guard, :non_exhaustive}}
        end
    end
  end

  # A guarded arm becomes a `:case` on the inductive Bool (`bool_case/5`); an
  # unguarded catch-all before the end shadows every later arm and closes the
  # chain early.
  defp guard_chain(scrut_expr, [{:match_arm, meta, body} | rest], expected, names, ctx, env, acc) do
    pat = Keyword.fetch!(meta, :pattern)

    case Keyword.get(meta, :guard) do
      nil ->
        bind_catchall_body(scrut_expr, pat, single_body(body), expected, names, ctx, env)

      guard ->
        with {:ok, guard_expr} <- guard_bind(scrut_expr, pat, guard),
             {:ok, body_expr} <- guard_bind(scrut_expr, pat, single_body(body)),
             {:ok, test} <-
               elaborate_expr_checked(guard_expr, bool_type_term(Context.signature(ctx)), names, ctx, env),
             {:ok, tt} <- elaborate_expr_checked(body_expr, expected, names, ctx, env),
             # Warn for THIS arm before recursing into the later ones. The check needs only
             # `test` and `acc`, both bound here; running it after the recursion meant every
             # later arm had already recorded its own warning, so `GuardLint.warnings/0` —
             # which restores insertion order by reversing a prepended list — handed back a
             # chain's shadow warnings in descending arm index.
             :ok <- maybe_warn_shadowed(test, acc, ctx),
             {:ok, ff} <- guard_chain(scrut_expr, rest, expected, names, ctx, env, acc ++ [test]) do
          {:ok, bool_case(test, expected, tt, ff, ctx)}
        end
    end
  end

  # Dead-arm lint (§2.1): a guard implied by the disjunction of the guards
  # before it can never fire. Warning only — elaboration is unaffected. The
  # index is the guard's 0-based position among the chain's guarded arms.
  defp maybe_warn_shadowed(_test, [], _ctx), do: :ok

  defp maybe_warn_shadowed(test, acc, ctx) do
    if GuardLint.shadowed?(test, acc, ctx),
      do: GuardLint.record_warning({:guard_shadowed, length(acc)})

    :ok
  end

  # Bind a catch-all pattern's variable to the scrutinee and check the body: `_`
  # discards, a name substitutes the (variable) scrutinee expression. A non-
  # variable pattern under a guarded match is out of this slice's scope.
  defp bind_catchall_body(_scrut, {:variable, _m, "_"}, body, expected, names, ctx, env),
    do: elaborate_expr_checked(body, expected, names, ctx, env)

  defp bind_catchall_body(scrut_expr, {:variable, _m, name} = pattern, body, expected, names, ctx, env) do
    cond do
      not match?({:variable, _sm, _sn}, scrut_expr) -> complex_guard_scrutinee_error(scrut_expr)
      binds_any?(body, [name]) -> shadowed_guard_error(pattern, name, body, :body)
      true -> elaborate_expr_checked(subst_surface_var(body, name, scrut_expr), expected, names, ctx, env)
    end
  end

  defp bind_catchall_body(scrut_expr, {:tuple, _m, pats} = pattern, body, expected, names, ctx, env) do
    with {:ok, body_expr} <- tuple_guard_bind(scrut_expr, pats, body, pattern) do
      elaborate_expr_checked(body_expr, expected, names, ctx, env)
    end
  end

  defp bind_catchall_body(_scrut, pattern, _body, _expected, _names, _ctx, _env),
    do: guarded_pattern_shape_error(pattern)

  # Substitute the pattern variable with the (variable) scrutinee in a guard or
  # body expression, guarding against complex scrutinees and shadow-capture.
  defp guard_bind(_scrut, {:variable, _m, "_"}, expr), do: {:ok, expr}

  defp guard_bind(scrut_expr, {:variable, _m, name} = pattern, expr) do
    cond do
      not match?({:variable, _sm, _sn}, scrut_expr) -> complex_guard_scrutinee_error(scrut_expr)
      binds_any?(expr, [name]) -> shadowed_guard_error(pattern, name, expr, :guard_or_body)
      true -> {:ok, subst_surface_var(expr, name, scrut_expr)}
    end
  end

  defp guard_bind(scrut_expr, {:tuple, _m, pats} = pattern, expr),
    do: tuple_guard_bind(scrut_expr, pats, expr, pattern)

  defp guard_bind(_scrut, pattern, _expr), do: guarded_pattern_shape_error(pattern)

  # Multi-parameter function clauses desugar to a match over a flat tuple of
  # formal arguments. Such a tuple pattern is irrefutable when every leaf is a
  # variable or wildcard, so bind each leaf to its positional projection before
  # elaborating the guard/body. This is the guarded counterpart of
  # `try_tuple_match/6`; constructor/literal leaves remain deliberately outside
  # the catch-all guard chain and are rejected by `tuple_subs/2`.
  defp tuple_guard_bind(scrut_expr, pats, expr, pattern) do
    if match?({:variable, _sm, _sn}, scrut_expr) do
      with {:ok, subs} <- tuple_subs(pats, scrut_expr) do
        bound_names = Enum.map(subs, &elem(&1, 0))

        case Enum.find(bound_names, &binds_any?(expr, [&1])) do
          nil ->
            {:ok,
             Enum.reduce(subs, expr, fn {name, replacement}, acc ->
               subst_surface_var(acc, name, replacement)
             end)}

          name ->
            shadowed_guard_error(pattern, name, expr, :guard_or_body)
        end
      else
        {:error, _reason} -> guarded_pattern_shape_error(pattern)
      end
    else
      complex_guard_scrutinee_error(scrut_expr)
    end
  end

  defp shadowed_guard_error(pattern, name, expression, site) do
    {:error,
     {:unsupported_guard,
      %{
        reason: :shadowed,
        name: name,
        site: site,
        span: pattern_binder_span(pattern, name),
        pattern_span: surface_expression_span(pattern),
        shadow_span: first_binding_span(expression, name)
      }}}
  end

  defp guarded_pattern_shape_error(pattern) do
    {:error,
     {:unsupported_guard,
      %{
        reason: :refutable_pattern,
        shape: pattern_shape(pattern),
        span: surface_expression_span(pattern)
      }}}
  end

  defp complex_guard_scrutinee_error(scrutinee) do
    {:error,
     {:unsupported_guard,
      %{
        reason: :complex_scrutinee,
        span: surface_expression_span(scrutinee)
      }}}
  end

  # Literal patterns on a PRIMITIVE scrutinee (Int/Bool/Float) desugar to a chain
  # of `:case`-on-Bool decisions (`bool_case/5`) — there is no `:vdata` to
  # dispatch on. `match n | 0 -> a | _ -> b` becomes
  # `case (n == 0) of True -> a | False -> b`; `match b | true -> t | false ->
  # f` becomes `case b of True -> t | False -> f`. The already-elaborated Core scrutinee is reused
  # in each equality test (no surface duplication), and the kernel re-checks the
  # assembled chain. Returns `:not_applicable` for a non-primitive scrutinee or
  # arms that are not a clean literal/catch-all list (the ordinary path handles it).
  defp try_literal_match(scrut_expr, arms, scrut_term, scrut_type, expected, names, ctx, env) do
    sig = Context.signature(ctx)
    scrut_type = Normalise.whnf_value(scrut_type, sig)

    case primitive_scrut_kind(scrut_type, sig) do
      {:ok, prim} ->
        pats = Enum.map(arms, fn {:match_arm, m, b} -> {Keyword.fetch!(m, :pattern), single_body(b)} end)

        cond do
          prim == :bool and bool_exhaustive?(pats) ->
            {tb, fb} = bool_bodies(pats)

            with {:ok, t_core} <- elaborate_match_body(tb, expected, names, ctx, env),
                 {:ok, f_core} <- elaborate_match_body(fb, expected, names, ctx, env) do
              {:ok, bool_case(scrut_term, expected, t_core, f_core, ctx)}
            end

          literal_chain?(pats, prim) ->
            literal_chain(scrut_expr, scrut_term, scrut_type, prim, pats, expected, names, ctx, env)

          true ->
            :not_applicable
        end

      :error ->
        :not_applicable
    end
  end

  # The Core **term** for the canonical Bool inductive (the term-level counterpart
  # of Kernel.bool_type_value/1); `eval(bool_type_term(sig), _) == bool_type_value(sig)`.
  defp bool_type_term(sig) do
    fid = Inductive.builtin(sig, :bool) || raise "builtin :bool not seeded (bootstrap/load-order bug)"
    {:data, fid, [], []}
  end

  # Lower a two-way Bool decision to a `:case` on the inductive Bool, with the
  # constant motive `λ_:Bool. motive_body_type` (both branches share the type).
  # The kernel re-checks the assembled `:case`, so nothing built here is trusted.
  defp bool_case(scrut_term, motive_body_type, tt, ff, ctx) do
    sig = Context.signature(ctx)
    bool_ty = bool_type_term(sig)
    true_ctor = resolve_ctor_key(sig, :True)
    false_ctor = resolve_ctor_key(sig, :False)
    motive = {:lam, Cure.Core.Grade.unrestricted(), bool_ty, Cure.Core.Term.shift(motive_body_type, 1, 0)}
    {:case, scrut_term, motive, [{true_ctor || :True, 0, tt}, {false_ctor || :False, 0, ff}]}
  end

  # A Bool scrutinee is now the inductive family (`{:vdata, :Bool, []}`), resolved
  # via the registry; Int/Float stay primitive type-values.
  #
  # NOTE(int-facade): `{:vint_type}` is retired from surface production (spec
  # 2026-07-18 §3a); this clause stays so scrutinee-kind resolution remains
  # total on a legacy/deserialized value still carrying it.
  defp primitive_scrut_kind({:vint_type}, _sig), do: {:ok, :int}
  defp primitive_scrut_kind({:vfloat_type}, _sig), do: {:ok, :float}
  # `Atom` is a sealed primitive base type; its `==`/`!=` lowers to the polymorphic
  # `struct_eq` (a BEAM atom is its own value). Kept out of the arithmetic clause,
  # which never consults `:atom`, so `:ok + :ok` still rejects.
  defp primitive_scrut_kind({:vatom_type}, _sig), do: {:ok, :atom}

  # `Bool` and `Int` are both nullary inductive families now (spec 2026-07-18
  # surface flip retired the primitive `{:vint_type}` node). An `Int`-typed operand
  # is `{:vdata, int_fid, []}`; it maps to `:int` so the arithmetic/comparison/eq
  # `build_binop` clauses fold to the monomorphic native ops exactly as before the
  # flip. Any other nullary family (e.g. `Nat`) stays `:error` → struct_eq path.
  defp primitive_scrut_kind({:vdata, fid, []}, sig) do
    cond do
      fid == Inductive.builtin(sig, :bool) -> {:ok, :bool}
      fid == Inductive.builtin(sig, :int) -> {:ok, :int}
      # `Char` is its own nullary builtin carrier, no longer a typealias for
      # `Bounded(0x110000)`, so it never reaches the applied-`Bounded` clause
      # below. It behaves identically for pattern purposes: its values are
      # compact `{:bounded_lit, k}` (the kernel's sole introduction rule for
      # `Char`), compared with the polymorphic `struct_eq`. Without this clause
      # every char-literal pattern — `['"' | rest]`, the whole of the pure-Cure
      # regex parser — falls out of the literal chain into the constructor
      # matrix, which reports the arm as `{:unsupported_pattern, :literal}`.
      fid == Inductive.builtin(sig, :char) -> {:ok, :bounded}
      true -> :error
    end
  end

  # An applied `Bounded(n)` (Char's underlying type) is an indexed family that
  # erases to a native int. It is NOT one of the monomorphic int/float/bool eq
  # twins, so equality is the polymorphic `struct_eq` — but a literal chain over
  # it lowers exactly like the primitive chains. Arithmetic on it stays rejected
  # (the arithmetic `build_binop` clause has no `:bounded` arm), preserving the
  # `0 ≤ k < n` invariant.
  defp primitive_scrut_kind({:vdata, fid, [_bound]}, sig) do
    if fid == Inductive.builtin(sig, :bounded), do: {:ok, :bounded}, else: :error
  end

  defp primitive_scrut_kind(_type, _sig), do: :error

  defp bool_exhaustive?([{p1, _}, {p2, _}]),
    do: Enum.sort([bool_pat_value(p1), bool_pat_value(p2)]) == [false, true]

  defp bool_exhaustive?(_), do: false

  defp bool_pat_value({:literal, _m, v}) when is_boolean(v), do: v
  defp bool_pat_value(_), do: nil

  defp bool_bodies([{p1, b1}, {_p2, b2}]),
    do: if(bool_pat_value(p1) == true, do: {b1, b2}, else: {b2, b1})

  defp elaborate_match_body(body, expected, names, ctx, env) do
    if effect_goal?(expected, ctx),
      do: elaborate_effect_branch(body, expected, names, ctx, env),
      else: elaborate_expr_checked(body, expected, names, ctx, env)
  end

  # A literal chain is zero or more literal arms of the scrutinee's primitive type
  # followed by a single variable/wildcard catch-all.
  defp literal_chain?(pats, prim) when length(pats) >= 1 do
    {lits, [{last_pat, _}]} = Enum.split(pats, length(pats) - 1)
    Enum.all?(lits, fn {p, _} -> literal_of?(p, prim) or pin_var?(p) end) and catchall_pat?(last_pat)
  end

  defp literal_chain?(_pats, _prim), do: false

  # A pin arm `^x` on a primitive scrutinee behaves like a literal arm whose
  # compared value is the current value of the bound variable `x` (an equality
  # constraint, not a fresh binding). It always needs a trailing catch-all — a pin
  # is never known to be exhaustive.
  defp pin_var?({:pin, _m, [{:variable, _vm, _name}]}), do: true
  defp pin_var?(_p), do: false

  defp literal_of?({:literal, _m, v}, :int), do: is_integer(v)
  defp literal_of?({:literal, _m, v}, :float), do: is_float(v)
  defp literal_of?({:literal, _m, v}, :bool), do: is_boolean(v)
  defp literal_of?({:literal, _m, v}, :atom), do: is_atom(v)
  # A char literal `'a'` carries its integer codepoint (subtype `:char`).
  defp literal_of?({:literal, _m, v}, :bounded), do: is_integer(v)
  defp literal_of?(_p, _prim), do: false

  defp catchall_pat?({:variable, _m, _name}), do: true
  defp catchall_pat?(_p), do: false

  defp lit_core(v, :int), do: {:int_lit, v}
  defp lit_core(v, :float), do: {:float_lit, v}
  defp lit_core(v, :atom), do: {:atom_lit, v}
  defp lit_core(v, :bounded), do: {:bounded_lit, v}

  defp lit_core(v, :bool, env), do: {:ctor, resolve_ctor_key(env, if(v, do: :True, else: :False)), []}
  defp lit_core(v, prim, _env), do: lit_core(v, prim)

  # The final (catch-all) arm: the chain's innermost default branch.
  defp literal_chain(scrut_expr, _scrut_term, _scrut_type, _prim, [{pat, body}], expected, names, ctx, env) do
    case pat do
      {:variable, _m, "_"} ->
        elaborate_match_body(body, expected, names, ctx, env)

      {:variable, _m, name} = pattern ->
        cond do
          not match?({:variable, _sm, _sn}, scrut_expr) ->
            :not_applicable

          binds_any?(body, [name]) ->
            {:error,
             {:unsupported_pattern,
              %{
                reason: :shadowed_literal_catchall,
                name: name,
                span: pattern_binder_span(pattern, name),
                type_span: surface_expression_span(scrut_expr),
                shadow_span: first_binding_span(body, name)
              }}}

          true ->
            elaborate_match_body(subst_surface_var(body, name, scrut_expr), expected, names, ctx, env)
        end
    end
  end

  # A literal arm: test the scrutinee against the literal (a type-directed
  # equality global spine yielding the inductive Bool — K2 phase 2), take this
  # body if equal, else recurse on the rest — the test scrutinised by a `:case`
  # on Bool. `prim` (the scrutinee's primitive kind, already in scope) picks the
  # monomorphic twin; a Bool literal chain uses the Std.Bool `eq` case-def.
  # A `:bounded` (Char) chain uses the polymorphic `struct_eq` — `scrut_type`
  # supplies its erased type argument — instead of a monomorphic eq twin.
  defp literal_chain(
         scrut_expr,
         scrut_term,
         scrut_type,
         prim,
         [{{:literal, _m, v}, body} | rest],
         expected,
         names,
         ctx,
         env
       ) do
    with {:ok, body_core} <- elaborate_match_body(body, expected, names, ctx, env),
         {:ok, rest_core} <-
           literal_chain(scrut_expr, scrut_term, scrut_type, prim, rest, expected, names, ctx, env) do
      test = eq_test_core(prim, scrut_term, lit_core(v, prim, env), scrut_type, ctx)
      {:ok, bool_case(test, expected, body_core, rest_core, ctx)}
    end
  end

  # A pin arm `^x`: same as a literal arm, but the compared value is the current
  # value of the bound variable `x` (elaborated to its core term) rather than a
  # constant. `scrut == x` picks the identical type-directed equality twin.
  defp literal_chain(
         scrut_expr,
         scrut_term,
         scrut_type,
         prim,
         [{{:pin, _m, [{:variable, _vm, name}]}, body} | rest],
         expected,
         names,
         ctx,
         env
       ) do
    with {:ok, x_core, _x_type} <- elaborate_expr_typed({:variable, [], name}, names, ctx, env),
         {:ok, body_core} <- elaborate_match_body(body, expected, names, ctx, env),
         {:ok, rest_core} <-
           literal_chain(scrut_expr, scrut_term, scrut_type, prim, rest, expected, names, ctx, env) do
      test = eq_test_core(prim, scrut_term, x_core, scrut_type, ctx)
      {:ok, bool_case(test, expected, body_core, rest_core, ctx)}
    end
  end

  # The per-arm equality test `scrut == literal` yielding the inductive Bool. A
  # `:bounded` scrutinee (Char) has no monomorphic eq twin, so it uses the
  # polymorphic `struct_eq` applied to the signature-aware readback of the
  # scrutinee type (its type argument is erased at emit).
  # The per-arm equality test `scrut == rhs` yielding the inductive Bool, where
  # `rhs` is an already-built core term (a literal for a literal arm, the pinned
  # variable's term for a pin arm). A `:bounded` scrutinee (Char) has no monomorphic
  # eq twin, so it uses the polymorphic `struct_eq` applied to the signature-aware
  # readback of the scrutinee type (its type argument is erased at emit).
  defp eq_test_core(prim, scrut_term, rhs_core, scrut_type, ctx) when prim in [:bounded, :atom] do
    ty = Quote.reify(scrut_type, Context.length(ctx), Context.signature(ctx))
    {:app, app2(builtin_op_global(:struct_eq), ty, scrut_term), rhs_core}
  end

  defp eq_test_core(prim, scrut_term, rhs_core, _scrut_type, _ctx) do
    eq_global =
      case prim do
        :int -> builtin_op_global(:int_eq)
        :float -> builtin_op_global(:float_eq)
        :bool -> :eq
      end

    app2(eq_global, scrut_term, rhs_core)
  end

  # A flat n-element tuple projects POSITIONALLY: `%[e1, …, en]` binds
  # `e1 = base.1`, `e2 = base.2`, …, `en = base.n` (each `.i` resolves against the
  # flat lowering via `positional_projection`). Each element may itself be a
  # nested tuple, recursing on its own projection base (`base.i.1`, `base.i.2`, …).
  defp tuple_subs(elems, base) do
    elems
    |> Enum.with_index(1)
    |> Enum.reduce_while({:ok, []}, fn {e, i}, {:ok, acc} ->
      case tuple_elem_sub(e, tuple_proj(base, Integer.to_string(i))) do
        {:ok, s} -> {:cont, {:ok, acc ++ s}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp tuple_proj(base, n), do: {:attribute_access, [attribute: n], [base]}

  defp tuple_elem_sub({:variable, _m, "_"}, _proj), do: {:ok, []}
  defp tuple_elem_sub({:variable, _m, name}, proj), do: {:ok, [{name, proj}]}
  defp tuple_elem_sub({:tuple, _m, [_, _ | _] = sub_elems}, proj), do: tuple_subs(sub_elems, proj)
  defp tuple_elem_sub(_other, _proj), do: {:error, :refutable_tuple_element}

  # --- nested-pattern desugaring (parity #3) ---------------------------------
  #
  # Lower nested constructor sub-patterns (`S(S(m))`, `MkPair(Z(), y)`) into
  # nested *single-level* matches, so the existing dependent match machinery
  # (motives, index refinement, catch-all) handles every level unchanged — the
  # kernel `:case` already nests, so this is purely a surface lowering pass. Runs
  # one level per `elaborate_match`; deeper nesting is lowered on re-entry when
  # the emitted inner match is elaborated.
  #
  # Scope: arms are grouped by their outer constructor; each group's argument
  # columns are compiled by the standard pattern-matrix algorithm
  # (Augustsson/Maranget) — left-to-right column selection producing a tree of
  # single-scrutinee matches, so ANY number of nested columns is handled. A
  # top-level catch-all (`_`/`x`) mixed with nesting is woven in as a fallback
  # row for the sub-patterns each nested group leaves uncovered, and kept as the
  # outer catch-all for wholly-unmatched constructors.
  # ── Guards on constructor patterns ──────────────────────────────────────────
  # `match n | S(k) when g -> a | S(k) -> b | Z() -> c` — a guard on a
  # constructor pattern. Idris has no pattern guards; it collapses such an arm
  # into an `if` inside that constructor's case branch, falling through to the
  # next same-constructor arm when the guard is false. We reproduce exactly that:
  # fold each constructor group that carries a guard into ONE guardless arm
  # `C(w…) -> if g₁ then a else if g₂ then … else <closer>`, where the closer is
  # the group's trailing unguarded arm or the match's catch-all. The result is a
  # plain guardless match the ordinary `:vdata` path compiles; the `if`s lower to
  # `:case` on the inductive Bool (through the general `:conditional` clause). No
  # matrix-compiler or kernel change.

  defp ctor_guarded_arm?({:match_arm, meta, _body}) do
    Keyword.has_key?(meta, :guard) and
      match?({:function_call, _m, _args}, Keyword.get(meta, :pattern))
  end

  defp desugar_ctor_guards(arms, scrut_expr) do
    if Enum.any?(arms, &ctor_guarded_arm?/1),
      do: fold_ctor_guard_groups(arms, scrut_expr),
      else: {:ok, arms}
  end

  defp fold_ctor_guard_groups(arms, scrut_expr) do
    {ctor_arms, defaults} = Enum.split_with(arms, &(not default_arm?(&1)))

    with {:ok, closer} <- default_closer(defaults, scrut_expr) do
      order = ctor_arms |> Enum.map(&arm_ctor_name/1) |> Enum.uniq()
      grouped = Enum.group_by(ctor_arms, &arm_ctor_name/1)

      folded =
        Enum.reduce_while(order, {:ok, []}, fn cname, {:ok, acc} ->
          group = Map.fetch!(grouped, cname)

          # Only groups carrying a guard are folded; a plain group passes through
          # unchanged so a genuine duplicate constructor still reaches the
          # downstream duplicate check rather than being silently collapsed.
          if Enum.any?(group, &guarded_arm?/1) do
            case fold_ctor_group(group, closer) do
              {:ok, arm} -> {:cont, {:ok, acc ++ [arm]}}
              {:error, _} = e -> {:halt, e}
            end
          else
            {:cont, {:ok, acc ++ group}}
          end
        end)

      with {:ok, folded_arms} <- folded, do: {:ok, folded_arms ++ defaults}
    end
  end

  # The match's trailing catch-all is the fall-through for a group whose last arm
  # is still guarded. `:none` = no catch-all (a still-guarded last arm is then
  # non-exhaustive). More than one default is out of scope.
  defp default_closer([], _scrut), do: {:ok, :none}

  defp default_closer([{:match_arm, dmeta, dbody0}], scrut_expr) do
    {:variable, _m, dvname} = pattern = Keyword.fetch!(dmeta, :pattern)
    body = single_body(dbody0)

    if dvname != "_" and binds_any?(body, [dvname]) do
      shadowed_guard_error(pattern, dvname, body, :body)
    else
      case resolve_default_body(dvname, body, scrut_expr) do
        {:ok, db} -> {:ok, {:some, db}}
        {:error, :nonvariable_scrutinee} -> complex_guard_scrutinee_error(scrut_expr)
      end
    end
  end

  defp default_closer(defaults, _scrut) do
    {:match_arm, meta, _body} = List.last(defaults)
    {:variable, _variable_meta, name} = Keyword.fetch!(meta, :pattern)
    {:error, {:duplicate_default_pattern, name}}
  end

  # Fold one constructor group's rows (each `C(v…) [when g] -> body`, all single
  # level and sharing arity k) into a single `C(w₁..w_k) -> <if-chain>`.
  defp fold_ctor_group([{:match_arm, meta0, _} | _] = group, closer) do
    {:function_call, fmeta, args0} = Keyword.fetch!(meta0, :pattern)
    cname = Keyword.fetch!(fmeta, :name)
    k = length(args0)
    wilds = for i <- 1..k//1, do: {:variable, [], "$g" <> cname <> Integer.to_string(i)}
    wnames = Enum.map(wilds, fn {:variable, _m, n} -> n end)

    with {:ok, chain} <- build_guard_chain(group, wnames, closer) do
      {:ok, {:match_arm, [pattern: {:function_call, fmeta, wilds}], [chain]}}
    end
  end

  # An unguarded row terminates the chain (its body; later rows shadowed). A
  # guarded last row falls through to the catch-all, or is non-exhaustive if
  # there is none.
  defp build_guard_chain([{:match_arm, meta, body}], wnames, closer) do
    with {:ok, subs} <- guard_row_renaming(meta, wnames, body) do
      case Keyword.get(meta, :guard) do
        nil ->
          {:ok, rename_all(single_body(body), subs)}

        guard ->
          case closer do
            {:some, db} ->
              {:ok, mk_if(rename_all(guard, subs), rename_all(single_body(body), subs), db)}

            :none ->
              {:error, {:unsupported_guard, :non_exhaustive}}
          end
      end
    end
  end

  defp build_guard_chain([{:match_arm, meta, body} | rest], wnames, closer) do
    with {:ok, subs} <- guard_row_renaming(meta, wnames, body) do
      case Keyword.get(meta, :guard) do
        nil ->
          {:ok, rename_all(single_body(body), subs)}

        guard ->
          with {:ok, else_} <- build_guard_chain(rest, wnames, closer) do
            {:ok, mk_if(rename_all(guard, subs), rename_all(single_body(body), subs), else_)}
          end
      end
    end
  end

  defp mk_if(cond, then_, else_), do: {:conditional, [], [cond, then_, else_]}

  # Map a row's constructor-argument variable names onto the shared fresh binders
  # `w₁..w_k`. Rejects (shadow) if the row's body/guard rebinds a source name, to
  # keep the surface substitution capture-free (mirrors `compile_group`).
  defp guard_row_renaming(meta, wnames, body) do
    {:function_call, _fm, argpats} = Keyword.fetch!(meta, :pattern)
    oldnames = Enum.map(argpats, fn {:variable, _m, n} -> n end)
    subs = Enum.zip(oldnames, wnames)
    guard = Keyword.get(meta, :guard)
    exprs = [single_body(body) | if(guard, do: [guard], else: [])]

    shadowed =
      Enum.find_value(oldnames, fn name ->
        Enum.find_value(exprs, fn expression ->
          if binds_any?(expression, [name]), do: {name, expression}, else: nil
        end)
      end)

    case shadowed do
      {name, expression} ->
        shadowed_guard_error(Keyword.fetch!(meta, :pattern), name, expression, :constructor_branch)

      nil ->
        {:ok, subs}
    end
  end

  defp rename_all(expr, subs) do
    Enum.reduce(subs, expr, fn {old, new}, e ->
      subst_surface_var(e, old, {:variable, [], new})
    end)
  end

  # A monotonic per-process counter yielding a unique infix for generated
  # scrutinee names, so nested-pattern lowerings at different match sites (and
  # different nesting depths) never produce colliding — hence capturing — names.
  # Process-local: one elaboration runs sequentially in one process, and tests
  # assert only on the {:ok, _} verdict, never on generated names.
  defp fresh_tag do
    n = Process.get(:cure_desugar_gensym, 0)
    Process.put(:cure_desugar_gensym, n + 1)
    Integer.to_string(n) <> "$"
  end

  defp desugar_nested_arms(arms, scrut_expr) do
    cond do
      not Enum.any?(arms, &arm_has_nested?/1) ->
        {:ok, arms}

      Enum.any?(arms, &default_arm?/1) ->
        desugar_with_default(arms, scrut_expr)

      true ->
        compile_nested_groups(arms)
    end
  end

  # A nested match with a trailing top-level catch-all `… | x -> d`. Resolve the
  # catch-all body (binding its name to the scrutinee), weave it as a wildcard
  # fallback row into every nested group so uncovered sub-patterns fall through to
  # it, then keep a top-level `_ -> d` for constructors with no arm at all.
  defp desugar_with_default(arms, scrut_expr) do
    {ctor_arms, defaults} = Enum.split_with(arms, &(not default_arm?(&1)))

    case defaults do
      [{:match_arm, dmeta, dbody0} = default] ->
        pattern = Keyword.fetch!(dmeta, :pattern)
        {:variable, _m, dvname} = pattern

        cond do
          default != List.last(arms) ->
            next_arm = Enum.at(arms, Enum.find_index(arms, &(&1 == default)) + 1)

            {:error,
             {:unreachable_after_default_pattern,
              %{
                name: dvname,
                span: surface_expression_span(arm_pattern(next_arm)),
                default_span: surface_expression_span(pattern)
              }}}

          dvname != "_" and binds_any?(dbody0, [dvname]) ->
            {:error,
             {:unsupported_pattern,
              %{
                reason: :shadowed_default,
                name: dvname,
                span: pattern_binder_span(pattern, dvname),
                shadow_span: first_binding_span(dbody0, dvname)
              }}}

          true ->
            case resolve_default_body(dvname, single_body(dbody0), scrut_expr) do
              {:ok, dbody} ->
                with {:ok, compiled} <- compile_nested_groups(weave_default(ctor_arms, dbody)) do
                  {:ok, compiled ++ [{:match_arm, [pattern: {:variable, [], "_"}], dbody}]}
                end

              {:error, :nonvariable_scrutinee} ->
                {:error,
                 {:unsupported_pattern,
                  %{
                    reason: :named_default_nonvariable,
                    name: dvname,
                    span: pattern_binder_span(pattern, dvname),
                    type_span: surface_expression_span(scrut_expr)
                  }}}
            end
        end

      [_first | _rest] ->
        {:match_arm, meta, _body} = List.last(defaults)
        {:variable, _m, name} = Keyword.fetch!(meta, :pattern)
        {:error, {:duplicate_default_pattern, name}}

      [] ->
        compile_nested_groups(arms)
    end
  end

  # `_` needs no binding; a named catch-all binds the whole scrutinee, so it is
  # only supported over a variable scrutinee (substitute its name), never a
  # complex scrutinee expression (nothing to bind to).
  defp resolve_default_body("_", dbody, _scrut), do: {:ok, dbody}

  defp resolve_default_body(dvname, dbody, {:variable, _m, sname}) do
    if binds_any?(dbody, [dvname]),
      do: {:error, :shadowed},
      else: {:ok, subst_surface_var(dbody, dvname, {:variable, [], sname})}
  end

  defp resolve_default_body(_dvname, _dbody, _scrut), do: {:error, :nonvariable_scrutinee}

  # Append a wildcard fallback arm (`C(_…) -> d`) to each group that has nesting,
  # so the group's matrix falls back to the catch-all body for uncovered
  # sub-patterns. Non-nested groups are already exhaustive and left untouched.
  defp weave_default(ctor_arms, dbody) do
    order = ctor_arms |> Enum.map(&arm_ctor_name/1) |> Enum.uniq()
    grouped = Enum.group_by(ctor_arms, &arm_ctor_name/1)

    Enum.flat_map(order, fn cname ->
      group = Map.fetch!(grouped, cname)

      if Enum.any?(group, &arm_has_nested?/1) do
        {:function_call, fmeta, args0} = arm_pattern(hd(group))
        wilds = for i <- 1..length(args0)//1, do: {:variable, [], "$fb" <> cname <> Integer.to_string(i)}
        group ++ [{:match_arm, [pattern: {:function_call, fmeta, wilds}], dbody}]
      else
        group
      end
    end)
  end

  defp arm_pattern({:match_arm, meta, _body}), do: Keyword.fetch!(meta, :pattern)

  defp default_arm?({:match_arm, meta, _body}),
    do: match?({:variable, _m, _v}, Keyword.fetch!(meta, :pattern))

  defp arm_has_nested?({:match_arm, meta, _body}) do
    case Keyword.fetch!(meta, :pattern) do
      {:function_call, _m, args} -> Enum.any?(args, &(not pat_arg_leaf?(&1)))
      _ -> false
    end
  end

  # A constructor-pattern argument is a LEAF (not a nested sub-pattern needing
  # matrix lowering) if it is a bare variable or a named-implicit annotation.
  defp pat_arg_leaf?({:variable, _m, _v}), do: true
  defp pat_arg_leaf?({:named_implicit_pat, _m, _children}), do: true
  defp pat_arg_leaf?(_), do: false

  # Group arms by outer constructor (first-appearance order, within-group order
  # preserved for first-match), then compile each group to one single-level arm.
  defp compile_nested_groups(arms) do
    order = arms |> Enum.map(&arm_ctor_name/1) |> Enum.uniq()
    grouped = Enum.group_by(arms, &arm_ctor_name/1)

    Enum.reduce_while(order, {:ok, []}, fn cname, {:ok, acc} ->
      case compile_ctor_group(cname, Map.fetch!(grouped, cname)) do
        {:ok, group_arms} -> {:cont, {:ok, acc ++ group_arms}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp arm_ctor_name({:match_arm, meta, _body}) do
    {:function_call, fmeta, _args} = Keyword.fetch!(meta, :pattern)
    Keyword.fetch!(fmeta, :name)
  end

  # A group with a nested arm is compiled by the matrix algorithm; a group with
  # none is passed through unchanged (so a genuine duplicate constructor still
  # reaches `partition_arms`' duplicate check).
  defp compile_ctor_group(_cname, arms) do
    if Enum.any?(arms, &arm_has_nested?/1), do: compile_group(arms), else: {:ok, arms}
  end

  # `arms` all share an outer constructor `C/k`. Emit `C(v₁..v_k) -> <matrix>`,
  # where `<matrix>` compiles the k argument columns (rows = each arm's sub-
  # patterns → body) into a tree of single-scrutinee matches.
  defp compile_group([{:match_arm, meta0, _} | _] = arms) do
    {:function_call, fmeta, args0} = Keyword.fetch!(meta0, :pattern)
    cname = Keyword.fetch!(fmeta, :name)
    k = length(args0)

    # Shadow guard: a naive surface substitution would capture if a body rebinds
    # one of the pattern variables it substitutes. Reject rather than miscompile.
    pvars =
      arms
      |> Enum.flat_map(fn {:match_arm, m, _} ->
        {:function_call, _fm, as} = Keyword.fetch!(m, :pattern)
        Enum.flat_map(as, &pattern_vars_deep/1)
      end)
      |> Enum.uniq()

    case nested_pattern_shadow(arms, pvars) do
      %{name: name, pattern: pattern, shadow_span: shadow_span} ->
        {:error,
         {:unsupported_pattern,
          %{
            reason: :shadowed_nested,
            name: name,
            span: pattern_binder_span(pattern, name),
            type_span: surface_expression_span(pattern),
            shadow_span: shadow_span
          }}}

      nil ->
        # Seed the fresh scrutinee names with a per-invocation unique tag. Every
        # deeper name (`split_ctor_arms`, `split_default`) derives from these, so a
        # unique seed makes the WHOLE lowered subtree's names unique. Without it,
        # two independently-desugared nested matches — an outer arm whose body is
        # itself a nested match — regenerate identical names (`$nSome1_Y1`) and the
        # inner binder captures a reference the outer desugaring baked into the
        # body (variable capture → spurious `:branch_type`). See
        # nested_match_capture_test.exs.
        tag = fresh_tag()
        fresh = for i <- 1..k//1, do: "$n" <> tag <> cname <> Integer.to_string(i)

        rows =
          Enum.map(arms, fn {:match_arm, m, b} ->
            {:function_call, _fm, as} = Keyword.fetch!(m, :pattern)

            body =
              if Keyword.get(m, :impossible, false),
                do: @contextual_impossible_body,
                else: single_body(b)

            {as, Keyword.get(m, :guard), body}
          end)

        case compile_matrix(fresh, rows) do
          {:ok, inner} ->
            outer_pat = {:function_call, fmeta, Enum.map(fresh, &{:variable, [], &1})}
            {:ok, [{:match_arm, [pattern: outer_pat], inner}]}

          {:error, _} = err ->
            err
        end
    end
  end

  defp nested_pattern_shadow(arms, pattern_vars) do
    Enum.find_value(arms, fn {:match_arm, meta, body} ->
      pattern = Keyword.fetch!(meta, :pattern)
      guard = Keyword.get(meta, :guard)

      Enum.find_value(pattern_vars, fn name ->
        cond do
          binds_any?(single_body(body), [name]) ->
            %{name: name, pattern: pattern, shadow_span: first_binding_span(body, name)}

          guard && binds_any?(guard, [name]) ->
            %{name: name, pattern: pattern, shadow_span: first_binding_span(guard, name)}

          true ->
            nil
        end
      end)
    end)
  end

  defp pattern_vars_deep({:variable, _m, "_"}), do: []
  defp pattern_vars_deep({:variable, _m, v}), do: [v]
  defp pattern_vars_deep({:function_call, _m, args}), do: Enum.flat_map(args, &pattern_vars_deep/1)
  defp pattern_vars_deep(_), do: []

  # Pattern-matrix compilation. `scruts` are fresh scrutinee variable names or
  # projection expressions; each
  # row is `{[pattern…], guard, body}` (guard is `nil` or a surface expr) with one
  # pattern per remaining scrutinee. Emits a tree of single-scrutinee
  # `{:pattern_match}` nodes; every emitted match is single-level, so it re-uses
  # the dependent elaborator per node. At a leaf (no columns left), the reached
  # rows are folded into a `:case`-on-Bool `if`-chain: a guarded row tests its guard
  # and falls through to the next reached row, an unguarded row terminates the
  # chain (later rows shadowed), à la the Wadler/Augustsson `match … default`
  # continuation. All still over surface names, so no de-Bruijn weakening.
  defp compile_matrix([], rows), do: fold_leaf_rows(rows)

  defp compile_matrix([v | vs], rows) do
    col = Enum.map(rows, fn {[p | _ps], _g, _b} -> p end)

    case tuple_matrix_arity(col) do
      arity when is_integer(arity) ->
        expand_tuple_matrix_column(v, vs, rows, arity)

      nil ->
        cond do
          Enum.all?(col, &match?({:variable, _m, _n}, &1)) ->
            replacement = matrix_scrutinee(v)

            rows2 =
              Enum.map(rows, fn {[{:variable, _m, x} | ps], g, body} ->
                {ps, subst_guard(g, x, replacement), subst_surface_var(body, x, replacement)}
              end)

            compile_matrix(vs, rows2)

          Enum.all?(col, &match?({kind, _m, _v} when kind in [:literal, :variable], &1)) ->
            compile_matrix_literal_split(v, vs, rows, col)

          true ->
            compile_matrix_split(v, vs, rows, col)
        end
    end
  end

  # Literal columns cannot become Core constructor branches, but an ordinary
  # surface `match` already has a checked literal-dispatch path.
  defp compile_matrix_literal_split(v, vs, rows, col) do
    literals =
      col
      |> Enum.filter(&match?({:literal, _m, _value}, &1))
      |> Enum.uniq_by(fn {:literal, meta, value} -> {Keyword.get(meta, :subtype), value} end)

    with {:ok, literal_arms} <- split_literal_arms(literals, v, vs, rows) do
      if Enum.any?(col, &match?({:variable, _m, _name}, &1)) do
        with {:ok, default_inner} <- split_default(matrix_scrutinee(v), vs, rows) do
          default = {:match_arm, [pattern: {:variable, [], "#{matrix_name(v)}_d"}], default_inner}
          {:ok, {:pattern_match, [], [matrix_scrutinee(v) | literal_arms ++ [default]]}}
        end
      else
        {:ok, {:pattern_match, [], [matrix_scrutinee(v) | literal_arms]}}
      end
    end
  end

  defp split_literal_arms(literals, v, vs, rows) do
    Enum.reduce_while(literals, {:ok, []}, fn literal, {:ok, acc} ->
      {:literal, literal_meta, literal_value} = literal
      literal_key = {Keyword.get(literal_meta, :subtype), literal_value}

      sub_rows =
        Enum.flat_map(rows, fn {[p | ps], guard, body} ->
          case p do
            {:literal, meta, value} ->
              if {Keyword.get(meta, :subtype), value} == literal_key,
                do: [{ps, guard, body}],
                else: []

            {:variable, _meta, name} ->
              replacement = matrix_scrutinee(v)
              [{ps, subst_guard(guard, name, replacement), subst_surface_var(body, name, replacement)}]
          end
        end)

      case compile_matrix(vs, sub_rows) do
        {:ok, inner} ->
          arm = {:match_arm, [pattern: literal], inner}
          {:cont, {:ok, acc ++ [arm]}}

        {:error, _} = error ->
          {:halt, error}
      end
    end)
  end

  defp matrix_name(name) when is_binary(name), do: name
  defp matrix_name(_expression), do: "$projection"

  defp tuple_matrix_arity(column) do
    arities =
      Enum.flat_map(column, fn
        {:tuple, _meta, elements} -> [length(elements)]
        _other -> []
      end)
      |> Enum.uniq()

    cond do
      arities == [] ->
        nil

      length(arities) != 1 ->
        nil

      Enum.all?(column, fn
        {:tuple, _meta, _elements} -> true
        {:variable, _meta, _name} -> true
        _other -> false
      end) ->
        hd(arities)

      true ->
        nil
    end
  end

  defp expand_tuple_matrix_column(v, vs, rows, arity) do
    scrutinee = matrix_scrutinee(v)

    projections =
      for index <- 1..arity do
        tuple_proj(scrutinee, Integer.to_string(index))
      end

    expanded_rows =
      Enum.map(rows, fn
        {[{:tuple, _meta, elements} | patterns], guard, body} ->
          {elements ++ patterns, guard, body}

        {[{:variable, _meta, name} | patterns], guard, body} ->
          wildcards = for _index <- 1..arity, do: {:variable, [], "_"}

          {wildcards ++ patterns, subst_guard(guard, name, scrutinee), subst_surface_var(body, name, scrutinee)}
      end)

    compile_matrix(projections ++ vs, expanded_rows)
  end

  defp matrix_scrutinee(name) when is_binary(name), do: {:variable, [], name}
  defp matrix_scrutinee(expression), do: expression

  # Fold the rows reaching a matrix leaf into an `if`-chain. An unguarded row is
  # an unconditional match: it terminates the chain (identical to the previous
  # first-match behaviour when no row is guarded). A guarded final row with no
  # unguarded successor is non-exhaustive.
  defp fold_leaf_rows([{[], nil, body} | _]), do: {:ok, body}

  defp fold_leaf_rows([{[], guard, body} | rest]) do
    with {:ok, else_} <- fold_leaf_rows(rest) do
      {:ok, {:conditional, [], [guard, body, else_]}}
    end
  end

  defp fold_leaf_rows([]), do: {:error, {:unsupported_guard, :non_exhaustive}}

  defp subst_guard(nil, _name, _repl), do: nil
  defp subst_guard(guard, name, repl), do: subst_surface_var(guard, name, repl)

  # Column `v` has ≥1 constructor pattern: branch on each distinct constructor
  # (first-appearance order), plus a catch-all if any row has a variable there.
  defp compile_matrix_split(v, vs, rows, col) do
    ctors =
      col
      |> Enum.flat_map(fn
        {:function_call, m, _a} -> [Keyword.fetch!(m, :name)]
        _ -> []
      end)
      |> Enum.uniq()

    has_var = Enum.any?(col, &match?({:variable, _m, _n}, &1))
    seed = if is_binary(v), do: v, else: "$matrix_" <> fresh_tag()
    scrutinee = matrix_scrutinee(v)

    with {:ok, ctor_arms} <- split_ctor_arms(ctors, seed, scrutinee, vs, rows) do
      arms =
        if has_var do
          {:ok, default_inner} = split_default(scrutinee, vs, rows)
          ctor_arms ++ [{:match_arm, [pattern: {:variable, [], seed <> "_d"}], default_inner}]
        else
          ctor_arms
        end

      {:ok, {:pattern_match, [], [scrutinee | arms]}}
    end
  end

  defp split_ctor_arms(ctors, seed, scrutinee, vs, rows) do
    Enum.reduce_while(ctors, {:ok, []}, fn cname, {:ok, acc} ->
      arity = split_arity(cname, rows)
      ws = for i <- 1..arity//1, do: seed <> "_" <> cname <> Integer.to_string(i)

      sub_rows =
        Enum.flat_map(rows, fn {[p | ps], g, body} ->
          case p do
            {:function_call, m, qs} ->
              if Keyword.fetch!(m, :name) == cname, do: [{qs ++ ps, g, body}], else: []

            {:variable, _m, x} ->
              wilds = for w <- ws, do: {:variable, [], w <> "_x"}
              [{wilds ++ ps, subst_guard(g, x, scrutinee), subst_surface_var(body, x, scrutinee)}]
          end
        end)

      case compile_matrix(ws ++ vs, sub_rows) do
        {:ok, inner} ->
          pat = {:function_call, [name: cname], Enum.map(ws, &{:variable, [], &1})}
          {:cont, {:ok, acc ++ [{:match_arm, [pattern: pat], inner}]}}

        {:error, _} = err ->
          {:halt, err}
      end
    end)
  end

  # Arity of `cname` from the first row that mentions it explicitly.
  defp split_arity(cname, rows) do
    Enum.find_value(rows, 0, fn {[p | _], _g, _b} ->
      case p do
        {:function_call, m, qs} -> if Keyword.fetch!(m, :name) == cname, do: length(qs)
        _ -> nil
      end
    end)
  end

  # Catch-all sub-matrix for constructors not explicitly listed: only the
  # variable rows survive (each binding its variable to `v`), column dropped.
  defp split_default(scrutinee, vs, rows) do
    default_rows =
      Enum.flat_map(rows, fn {[p | ps], g, body} ->
        case p do
          {:variable, _m, x} ->
            [{ps, subst_guard(g, x, scrutinee), subst_surface_var(body, x, scrutinee)}]

          _ ->
            []
        end
      end)

    compile_matrix(vs, default_rows)
  end

  # Build `{arm_map, default}` where arm_map is cname => {:matched, pattern, body}
  # | {:impossible_marked, pattern}, and `default` is `nil` or `{vname, body}` for
  # a single variable/wildcard catch-all arm (`x -> …` / `_ -> …`), which covers
  # every constructor not explicitly matched (Idris/Lean variable-pattern
  # coverage). Validates every constructor arm names one of dname's OWN declared
  # constructors (spec §5 step 2 gap) and rejects duplicate arms / duplicate
  # defaults / an impossible-marked catch-all.
  # A bare capitalized pattern (`Lt`) parses as a variable — the parser has no
  # type information — but when the name resolves to a NULLARY constructor of the
  # scrutinee's family it is a constructor pattern, not a fresh binder: `Lt` ≡
  # `Lt()` (Idris/Agda/Lean read an uppercase bare pattern as a nullary
  # constructor). Rewrite it to the canonical `Ctor()` node so the constructor
  # path handles it identically to the parenthesized spelling. Every genuine
  # variable/wildcard pattern — and any capitalized name that is NOT a nullary
  # constructor of this family — is left untouched, so it still binds/defaults.
  defp desugar_nullary_ctor_pattern({:variable, _meta, vname} = pat, sig, env, dname) do
    cname = resolve_ctor_key(env, String.to_atom(vname))

    case Inductive.get_ctor(env, cname) do
      %{args: []} ->
        if Inductive.ctor_family(sig, cname) == dname,
          do: {:function_call, [name: vname], []},
          else: pat

      _ ->
        pat
    end
  end

  defp desugar_nullary_ctor_pattern(pat, _sig, _env, _dname), do: pat

  defp partition_arms(arms, ctx, env, dname) do
    sig = Context.signature(ctx)

    Enum.reduce_while(arms, {:ok, {%{}, nil}}, fn {:match_arm, arm_meta, body}, {:ok, {acc, default}} ->
      pattern = arm_meta |> Keyword.fetch!(:pattern) |> desugar_nullary_ctor_pattern(sig, env, dname)

      case pattern do
        {:variable, _vmeta, vname} ->
          cond do
            Keyword.get(arm_meta, :impossible) == true ->
              {:halt, {:error, {:impossible_default_pattern, vname}}}

            default != nil ->
              {:halt, {:error, {:duplicate_default_pattern, vname}}}

            vname != "_" and binds_any?(body, [vname]) ->
              {:halt,
               {:error,
                {:unsupported_pattern,
                 %{
                   reason: :shadowed_default,
                   name: vname,
                   span: pattern_binder_span(pattern, vname),
                   shadow_span: first_binding_span(body, vname)
                 }}}}

            true ->
              {:cont, {:ok, {acc, {vname, single_body(body)}}}}
          end

        _ ->
          case constructor_pattern(pattern) do
            {:error, _} = err ->
              {:halt, err}

            {:ok, {cname0, _vars}} ->
              cname = resolve_ctor_key(env, cname0)
              ctor = Inductive.get_ctor(env, cname)
              arity_check = if ctor, do: validate_constructor_pattern_arity(pattern, ctor, cname), else: :ok
              pattern = rekey_pattern_name(pattern, cname)

              cond do
                ctor == nil ->
                  {:halt, unknown_pattern_constructor_error(pattern, cname, env, dname)}

                Inductive.ctor_family(sig, cname) != dname ->
                  {:halt, shadowed_or_foreign_ctor(env, sig, cname0, cname, dname)}

                match?({:error, _}, arity_check) ->
                  {:halt, arity_check}

                Map.has_key?(acc, cname) ->
                  {:halt, {:error, {:duplicate_branch, cname}}}

                Keyword.get(arm_meta, :impossible) == true ->
                  {:cont, {:ok, {Map.put(acc, cname, {:impossible_marked, pattern}), default}}}

                true ->
                  {:cont, {:ok, {Map.put(acc, cname, {:matched, pattern, single_body(body)}), default}}}
              end
          end
      end
    end)
  end

  # ── Join points (plan slice 4c) ─────────────────────────────────────────────
  # Core `:case` has no default branch, so a surface catch-all becomes one branch
  # per uncovered constructor — and `elaborate_default_branch/10` re-elaborates
  # its body for each. The copies MULTIPLY through nesting: `k` nested catch-alls
  # over an `n`-constructor type used to yield `(n-1)^k` copies (measured: 25 for
  # k=2, n=6). A join point binds the body once and calls it from each branch.
  #
  # No new Core former is needed. Given the motive `λ(s : S). R`, bind
  #
  #     j = {:lam, ω, S, body}   at   {:pi, ω, S, R}
  #
  # in the `:let` binder, and make each defaulted branch `{:app, j, scrut}`. The λ
  # is load-bearing: a bare `:let` of `body` would be EAGER (`Emit` lowers `:let`
  # to a match block), so the catch-all would run even when a real arm matched.
  # It also subsumes the surface substitution — a named catch-all `x -> …` is
  # precisely the λ's binder, so `x` is the scrutinee's value by construction.
  #
  # NOT a soundness fix. Idris combines branch usages by agreement rather than
  # summation (`LinearCheck.idr:528-540`), and the copies always landed in
  # DISJOINT constructor branches, so a linear variable in the catch-all was
  # already counted once. This buys term size, which on an ESP32 is flash.
  #
  # Fire only where it pays and where it is obviously type-correct:
  #
  #   * ≥2 uncovered constructors — one call site would pay a closure to save
  #     nothing;
  #   * no carried index equality, and an UNINDEXED family — otherwise `motive`
  #     is not the plain `λ(s : S). R` this encoding reads it as;
  #   * a NON-DEPENDENT motive (`R` does not mention `s`). A dependent `R` would
  #     type each branch at `R[s := C(args…)]`, so the join would have to be
  #     applied to the branch's reconstructed constructor — including its erased
  #     telescope args — rather than to `scrut`. Left as today's expansion.
  defp join_point?(default, uncovered, carried, idx_vals, motive) do
    # `:qtt_join_disabled` is a TEST HOOK: the usage checker (`Relevance`) now
    # un-joins the shared continuation correctly (review F11), so the join is safe
    # to emit even in graded defs. The differential test sets this flag to force the
    # per-branch form and assert the un-join verdict matches it. Unset in production.
    default != nil and length(uncovered) >= 2 and carried == nil and idx_vals == [] and
      match?({:lam, _g, _s, _r}, motive) and
      not MapSet.member?(free_indices(elem(motive, 3), 0), 0) and
      not Process.get(:qtt_join_disabled, false)
  end

  defp elaborate_join(false, _default, _names, _ctx, _env, _motive), do: {:ok, nil}

  defp elaborate_join(true, {vname, body_expr}, names, ctx, env, {:lam, _g, s_term, r_term}) do
    # `r_term` already lives under the motive's binder, so in `ctx1` it IS the
    # catch-all's expected type — no shift.
    ctx1 = Context.extend(ctx, Eval.eval(s_term, Context.env(ctx)))
    names1 = [vname | names]

    with {:ok, body} <- elaborate_expr_checked(body_expr, r_term, names1, ctx1, env) do
      {:ok, {{:pi, Grade.unrestricted(), s_term, r_term}, {:lam, Grade.unrestricted(), s_term, body}}}
    end
  end

  # Wrap the assembled `:case` in the join binder and discharge every marker.
  # Inserting a binder between the context and the case shifts everything inside
  # by one: `scrut` and `motive` at cutoff 0, a branch body at cutoff `arity` (its
  # own constructor binders must not move). Inside a branch the join sits at index
  # `arity`, and the scrutinee it is applied to has travelled under `1 + arity`
  # binders.
  defp wrap_join(case_term, nil), do: case_term

  defp wrap_join({:case, scrut, motive, branches}, {join_ty, join_val}) do
    branches1 =
      Enum.map(branches, fn
        {c, arity, @join_marker} -> {c, arity, {:app, {:var, arity}, Subst.shift(scrut, 1 + arity, 0)}}
        {c, arity, body} -> {c, arity, Subst.shift(body, 1, arity)}
      end)

    inner = {:case, Subst.shift(scrut, 1, 0), Subst.shift(motive, 1, 0), branches1}
    {:let, Grade.unrestricted(), join_ty, join_val, inner}
  end

  # A variable/wildcard catch-all covers `cname` (not explicitly matched): rebuild
  # the constructor pattern `cname(fresh…)`, substitute the catch-all's name with
  # that reconstruction in the body (so the bound var resolves to the very term
  # the kernel's branch goal expects), and route through the normal matched-branch
  # path — index inversion, goal refinement, carried-eq, and scrutinee
  # substitution all apply unchanged. E-layer, no TCB.
  defp elaborate_default_branch(
         verdict,
         cname,
         {vname, body_expr},
         names,
         ctx,
         env,
         param_vals,
         idx_terms,
         scrut_term,
         result_type_term,
         carried,
         motive
       ) do
    # A surface constructor pattern names only the PRESENT (non-erased) args; the
    # erased indices are reconstructed from the telescope, not bound in the source.
    %{quantities: quantities} = Inductive.get_ctor(env, cname)
    present = Enum.count(quantities, &Grade.present?/1)
    fresh = default_pattern_vars(cname, present)
    syn_pattern = {:function_call, [name: Atom.to_string(cname)], Enum.map(fresh, &{:variable, [], &1})}

    cond do
      vname == "_" ->
        elaborate_matched_branch(
          verdict,
          syn_pattern,
          body_expr,
          names,
          ctx,
          env,
          param_vals,
          idx_terms,
          scrut_term,
          result_type_term,
          carried,
          motive
        )

      true ->
        body2 = subst_surface_var(body_expr, vname, syn_pattern)

        elaborate_matched_branch(
          verdict,
          syn_pattern,
          body2,
          names,
          ctx,
          env,
          param_vals,
          idx_terms,
          scrut_term,
          result_type_term,
          carried,
          motive
        )
    end
  end

  # Fresh, collision-proof binder names for a synthesized catch-all constructor
  # pattern (`$<ctor>_<n>`); empty for a nullary constructor.
  defp default_pattern_vars(cname, arity) do
    for i <- 1..arity//1, do: "$" <> Atom.to_string(cname) <> "_" <> Integer.to_string(i)
  end

  defp elaborate_matched_branch(
         verdict,
         pattern,
         body_expr,
         names,
         ctx,
         env,
         scrut_param_vals,
         _scrut_idx_terms,
         scrut_term,
         result_type_term,
         carried,
         motive
       ) do
    pattern = internalize_branch_wildcards(pattern)
    {:ok, {cname, pattern_vars}} = constructor_pattern(pattern)

    %{args: telescope, quantities: quantities, result_indices: result_indices, plicities: plicities} =
      Inductive.get_ctor(env, cname)

    arity = length(telescope)

    instantiated_result_indices =
      Kernel.instantiate_branch_result_indices(
        result_indices,
        arity,
        scrut_param_vals,
        Context.length(ctx)
      )

    branch_names = branch_scope(telescope, quantities, plicities, pattern_vars) ++ names

    case verdict do
      :impossible ->
        # Matched arm on a genuinely unreachable constructor the user did NOT mark
        # impossible: elaborate the body unchecked (the kernel discharges it too).
        branch_ctx = extend_context(ctx, telescope, scrut_param_vals)

        with {:ok, body_term, _type} <- elaborate_expr_typed(body_expr, branch_names, branch_ctx, env) do
          {:ok, {cname, length(telescope), body_term}}
        end

      _solved_or_trivial ->
        # The kernel's `branch_unify` verdict is the COMPLETE index inversion for
        # this branch — both `ctor-arg := scrut-index` (Vec-style) AND
        # `scrut-index-var := ctor-result` (e.g. `n := Z` for `v : NV(n)` matched
        # by `vz : NV(Z)`). The with-rematch path already uses it; the plain path
        # previously reimplemented a strictly weaker subset (`branch_index_subst`)
        # that missed the second direction, so a goal mentioning the scrutinee's
        # index in a nested position (`Eq(NV(n), …)`) never refined per branch.
        subst =
          case verdict do
            {:solved, s} -> s
            :trivial -> %{}
          end

        # C-c (spec 2026-07-08 §2.3): split the pattern's named implicits into
        # BINDINGS (an unforced position written as a bare variable — binds the
        # anonymized erased telescope slot at quantity 0, Relevance policing any
        # relevant use) and CHECKS (forced positions, plus unforced dot/non-var
        # forms that keep the `{:named_implicit_unforced,…}` reject). Compute the
        # split and the renamed branch scope ONCE, before the carried/plain
        # dispatch, so BOTH paths honor the binding.
        {bindings, checks} = split_named_implicits(pattern, subst, arity, telescope, quantities)

        tele_names =
          Enum.reduce(bindings, branch_scope(telescope, quantities, plicities, pattern_vars), fn {name,
                                                                                                  {:variable, _, vname},
                                                                                                  _named_meta,
                                                                                                  _constructor_meta},
                                                                                                 acc ->
            p = Enum.find_index(telescope, fn {n, _t} -> n == String.to_atom(name) end)
            List.replace_at(acc, arity - 1 - p, to_string(vname))
          end)

        branch_names = tele_names ++ names

        if carried != nil do
          elaborate_carried_eq_branch(
            cname,
            telescope,
            result_indices,
            body_expr,
            branch_names,
            ctx,
            env,
            scrut_param_vals,
            result_type_term,
            carried,
            checks,
            subst
          )
        else
          branch_ctx =
            ctx
            |> extend_context(telescope, scrut_param_vals)
            |> specialize_branch_context_subst(subst)

          # Merge in the scrutinee VALUE substitution (`v ↦ ctor`) so a goal that
          # mentions the scrutinee value itself (`Eq(T, v, v)`) refines to the
          # branch constructor alongside the index inversion — the shared
          # `refine_branch_goal` (Task 3.4), also used by the with-rematch path.
          branch_expected =
            instantiate_branch_motive(
              motive,
              instantiated_result_indices,
              cname,
              arity,
              subst,
              branch_ctx
            )

          # Lean substitutes a variable major premise by `ctor fields` in the
          # entire subgoal — context AND everything elaborated inside it
          # (`Meta/Tactic/Cases.lean:219-227`, the `subst.insert majorFVarId
          # ctorApp`). Cure's surface analog: free occurrences of the scrutinee
          # NAME in the branch body become the branch pattern expression, whose
          # vars are already bound in branch scope and elaborate to exactly the
          # `ctor_term` the kernel's branch goal expects. Without this, a body
          # like `refl(v)` keeps `v` opaque (`v ≢ vz`) even though the goal
          # correctly refined to `Eq(NV(Z), vz, vz)`.
          refined_body_expr =
            refine_scrutinee_in_body(body_expr, scrut_term, pattern, pattern_vars, names)

          elaborate_checked_candidate = fn candidate ->
            case elaborate_branch_body(candidate, branch_expected, branch_names, branch_ctx, env) do
              {:ok, term} = ok ->
                case Kernel.check(branch_ctx, term, Eval.eval(branch_expected, Context.env(branch_ctx))) do
                  :ok -> ok
                  {:error, reason} -> {:error, {:branch_type, cname, reason}}
                end

              {:error, _} = error ->
                error
            end
          end

          body_result = fn ->
            if length(plicities) == arity and Enum.all?(plicities, &(&1 == :explicit)) do
              elaborate_checked_candidate.(refined_body_expr)
            else
              case elaborate_checked_candidate.(body_expr) do
                {:ok, _} = ok ->
                  ok

                {:error, _} = original ->
                  case elaborate_checked_candidate.(refined_body_expr) do
                    {:ok, _} = ok -> ok
                    {:error, _} -> original
                  end
              end
            end
          end

          with :ok <-
                 check_named_implicits(checks, subst, arity, telescope, branch_ctx, branch_names, env),
               {:ok, body_term} <- body_result.() do
            {:ok, {cname, arity, body_term}}
          end
        end
    end
  end

  # Named-implicit annotations `{k = <expr>}` on this branch's constructor
  # pattern are check-and-discard: for each, resolve the named erased index to
  # its telescope position `p`, read the forced value `d` the kernel's index
  # inversion pinned at that position (`subst[arity-1-p]`), elaborate the user's
  # forced inner expression to a term `t` in the branch frame, and require `t`
  # convertible with `d`. The annotation binds nothing and produces no runtime
  # term, so on success we simply continue; on mismatch the branch is rejected.
  #
  # The `checks` argument is the pre-split CHECK list from
  # `split_named_implicits/4` (C-c, spec 2026-07-08 §2.3) — the bindings have
  # already been peeled off and named in the branch scope. An unforced position
  # written as a bare variable BINDS instead (split off there); reaching the
  # `{:named_implicit_unforced,…}` error below with a dot/non-variable inner
  # means nothing was pinned to check against — write a bare variable to bind
  # the index instead.
  defp check_named_implicits(checks, subst, arity, telescope, branch_ctx, branch_names, env) do
    checks
    |> Enum.reduce_while(:ok, fn {name, inner, named_meta, constructor_meta}, :ok ->
      case named_implicit_forced_value(name, subst, arity, telescope) do
        {:ok, d} ->
          expr = forced_inner_expr(inner)

          case elaborate_expr_typed(expr, branch_names, branch_ctx, env) do
            {:ok, t_term, _ty} ->
              if Cure.Core.Conv.conv?(
                   t_term,
                   d,
                   Context.env(branch_ctx),
                   Context.length(branch_ctx),
                   Context.signature(branch_ctx)
                 ) do
                {:cont, :ok}
              else
                {:halt,
                 {:error,
                  forced_pattern_mismatch_error(
                    name,
                    inner,
                    named_meta,
                    constructor_meta,
                    t_term,
                    d,
                    branch_names
                  )}}
              end

            {:error, _} = err ->
              {:halt, err}
          end

        :error ->
          {:halt,
           {:error,
            named_implicit_unforced_error(
              name,
              inner,
              named_meta,
              constructor_meta
            )}}
      end
    end)
  end

  # Position of the erased index named `name` in the constructor telescope, then
  # the forced value the branch-unify substitution pinned there. de Bruijn: the
  # telescope binds left-to-right, so position `p` is variable `arity-1-p`.
  defp named_implicit_forced_value(name, subst, arity, telescope) do
    key = String.to_atom(name)

    case Enum.find_index(telescope, fn {n, _t} -> n == key end) do
      nil ->
        :error

      p ->
        case Map.get(subst, arity - 1 - p) do
          nil -> :error
          d -> {:ok, d}
        end
    end
  end

  # The forced inner of a named-implicit is normally a dot pattern `.<expr>`; peel
  # the forced wrapper (it is not valid in ordinary expression elaboration) and
  # elaborate the underlying expression. A non-dot inner is elaborated as-is.
  defp forced_inner_expr({:forced_pattern, _m, [inner]}), do: inner
  defp forced_inner_expr(other), do: other

  defp forced_pattern_mismatch_error(
         name,
         inner,
         named_meta,
         constructor_meta,
         written,
         expected,
         branch_names
       ) do
    forced_info =
      case inner do
        {:forced_pattern, meta, _children} -> Cure.MetaAST.Metadata.source_info(meta)
        _ -> nil
      end

    named_info = Cure.MetaAST.Metadata.source_info(named_meta)
    constructor_info = Cure.MetaAST.Metadata.source_info(constructor_meta)
    span = (forced_info && forced_info.whole) || (named_info && named_info.whole)

    {:source_context, {:forced_pattern_mismatch, written, expected},
     %{
       line: span && span.start_line,
       column: span && span.start_column,
       length: span && max(1, span.end_column - span.start_column),
       span: span,
       forced_pattern_span: forced_info && forced_info.whole,
       forced_value_span: forced_info && (forced_info.body || List.first(forced_info.operands)),
       named_implicit_span: named_info && named_info.whole,
       named_implicit_name_span: named_info && named_info.name,
       constructor_span: constructor_info && constructor_info.whole,
       constructor_name_span: constructor_info && (constructor_info.callee || constructor_info.name),
       constructor: Keyword.get(constructor_meta, :name),
       implicit_name: name,
       written: written,
       expected: expected,
       written_surface: forced_term_surface(written, branch_names),
       expected_surface: forced_term_surface(expected, branch_names),
       expectation_origin: :pattern,
       expression_category: :forced_pattern
     }}
  end

  defp named_implicit_unforced_error(name, inner, named_meta, constructor_meta) do
    forced_info =
      case inner do
        {:forced_pattern, meta, _children} -> Cure.MetaAST.Metadata.source_info(meta)
        _ -> nil
      end

    named_info = Cure.MetaAST.Metadata.source_info(named_meta)
    constructor_info = Cure.MetaAST.Metadata.source_info(constructor_meta)
    span = (forced_info && forced_info.whole) || (named_info && named_info.whole)

    {:source_context, {:named_implicit_unforced, name},
     %{
       line: span && span.start_line,
       column: span && span.start_column,
       length: span && max(1, span.end_column - span.start_column),
       span: span,
       forced_pattern_span: forced_info && forced_info.whole,
       named_implicit_span: named_info && named_info.whole,
       named_implicit_name_span: named_info && named_info.name,
       constructor_span: constructor_info && constructor_info.whole,
       constructor_name_span: constructor_info && (constructor_info.callee || constructor_info.name),
       constructor: Keyword.get(constructor_meta, :name),
       implicit_name: name,
       expectation_origin: :pattern,
       expression_category: :named_implicit_pattern,
       named_implicit_status: :unforced
     }}
  end

  defp forced_term_surface({:var, index}, names),
    do: Enum.at(names, index) || "?"

  defp forced_term_surface({:ctor, constructor, arguments}, names) do
    name = constructor |> Cure.Elab.Name.base() |> to_string()
    arguments = Enum.map(arguments, &forced_term_surface(&1, names))
    if arguments == [], do: name, else: "#{name}(#{Enum.join(arguments, ", ")})"
  end

  defp forced_term_surface(_term, _names), do: nil

  @doc """
  Public soundness-probe shim for the forced-annotation check of ONE named
  implicit `{name = .t}` on constructor `cname`, exposed for the Antigen
  `forcing/dot` metatheory vertical (#24). It rebuilds the branch frame exactly
  as `elaborate_matched_branch/10` does — `extend_context(ctx, telescope,
  scrut_param_vals) |> specialize_branch_context_subst(subst)` — and DELEGATES to
  the same `named_implicit_forced_value/4` (telescope-position → pinned forced
  value) and `Cure.Core.Conv.conv?/5` the real `check_named_implicits/7` uses.

  The caller supplies the ALREADY-ELABORATED written value `t_term` (the vertical
  builds it correct-by-construction), so this omits only the surface
  `elaborate_expr_typed` step; the forced-value resolution, the `:unforced` gate,
  and the convertibility decision are the production code paths verbatim. Returns
  `:ok` | `{:forced_pattern_mismatch, t_term, d}` | `{:named_implicit_unforced,
  name}`, matching `check_named_implicits/7`'s three outcomes.
  """
  @spec forced_check_probe(
          Env.t(),
          Context.t(),
          atom(),
          [term()],
          %{optional(integer()) => term()},
          String.t(),
          term()
        ) :: :ok | {:forced_pattern_mismatch, term(), term()} | {:named_implicit_unforced, String.t()}
  def forced_check_probe(env, ctx, cname, scrut_param_vals, subst, name, t_term) do
    %{args: telescope} = Inductive.get_ctor(env, cname)
    arity = length(telescope)

    branch_ctx =
      ctx
      |> extend_context(telescope, scrut_param_vals)
      |> specialize_branch_context_subst(subst)

    case named_implicit_forced_value(name, subst, arity, telescope) do
      {:ok, d} ->
        if Cure.Core.Conv.conv?(
             t_term,
             d,
             Context.env(branch_ctx),
             Context.length(branch_ctx),
             Context.signature(branch_ctx)
           ) do
          :ok
        else
          {:forced_pattern_mismatch, t_term, d}
        end

      :error ->
        {:named_implicit_unforced, name}
    end
  end

  # Step 3b branch. The motive (see `wrap_motive_carried_eq`) makes this branch's
  # expected type `Π(prf : Eq(T, idx, ctor_idx)). G'[jₚₒₛ↦ctor_idx]`, where
  # `ctor_idx` is this constructor's result index at the carried position. Bind
  # `prf`, transport each index-mentioning sibling `h : H[idx]` to `H[ctor_idx]`
  # via `rewrite prf (λz. H[idx↦z]) h`, and emit `λprf. (λh'. body) transport`.
  # Mirrors capability-B's `elaborate_with_eq_branch`, keyed on the index term.
  defp elaborate_carried_eq_branch(
         cname,
         telescope,
         result_indices,
         body_expr,
         branch_names,
         ctx,
         env,
         scrut_param_vals,
         result_type_term,
         carried,
         pattern,
         subst
       ) do
    %{pos: pos, idx_term: idx_term, idx_type_term: idx_type_term, siblings: siblings} = carried
    arity = length(telescope)

    branch_ctx0 =
      ctx
      |> extend_context(telescope, scrut_param_vals)
      |> specialize_branch_context_subst(subst)

    # C-a (spec 2026-07-08 §2.1): run the forced named-implicit check on this
    # carried-eq branch too, in the same pre-proof frame the plain path uses
    # (`branch_ctx0` specialized by the branch-unify subst) — otherwise a wrong
    # dot on a carried branch is silently discarded.
    check_ctx = branch_ctx0

    with :ok <- check_named_implicits(pattern, subst, arity, telescope, check_ctx, branch_names, env) do
      # `ctor_idx` — this constructor's result index at the carried position, in the
      # branch_ctx0 frame (telescope bound). `Eq(T, idx, ctor_idx)` is the proof the
      # motive hands each branch (kernel checks the branch at `motive @ ctor_idx`).
      ctor_idx = result_indices |> Enum.at(pos) |> replace_branch_vars(subst)

      idx_branch =
        idx_term
        |> Subst.shift(arity, 0)
        |> replace_branch_vars(subst)

      type_branch =
        idx_type_term
        |> Subst.shift(arity, 0)
        |> replace_branch_vars(subst)

      eq_dom_term = mk_eq(type_branch, idx_branch, ctor_idx)
      branch_ctx1 = Context.extend(branch_ctx0, Eval.eval(eq_dom_term, Context.env(branch_ctx0)))

      # Constants in branch_ctx1 (ctx + telescope + prf). `sc` shifts a ctx-frame
      # term past the telescope and the prf binder; `pat_b1` is `ctor_idx` past prf.
      sc = arity + 1
      idx_b1 = Subst.shift(idx_branch, 1, 0)
      t_b1 = Subst.shift(type_branch, 1, 0)
      pat_b1 = Subst.shift(ctor_idx, 1, 0)

      sib_data =
        siblings
        # Bind outer siblings before inner siblings. An inner sibling's type may
        # depend on an outer sibling's value, so the transported outer value must
        # already be available when that type is reconstructed.
        |> Enum.sort_by(& &1.index, :desc)
        |> Enum.map(fn %{index: idx, name: sname, type_term: h_ctx} ->
          h_shifted =
            h_ctx
            |> Subst.shift(arity, 0)

          h_refined = replace_branch_vars(h_shifted, subst)

          h_b1 = Subst.shift(h_refined, 1, 0)

          %{
            index: idx,
            name: sname,
            source_dom: h_b1,
            dom: replace_term_scoped(h_b1, idx_b1, pat_b1)
          }
        end)

      m = length(sib_data)

      rebound_sib_data =
        sib_data
        |> Enum.with_index()
        |> Enum.map(fn {sibling, prior_siblings} ->
          Map.merge(sibling, %{
            bound_source_dom: rebind_carried_sibling_term(sibling.source_dom, sib_data, prior_siblings, sc),
            bound_dom: rebind_carried_sibling_term(sibling.dom, sib_data, prior_siblings, sc)
          })
        end)

      branch_ctx_full =
        Enum.reduce(rebound_sib_data, branch_ctx1, fn %{bound_dom: rebound_domain}, c ->
          # Every domain is authored in branch_ctx1. Each preceding transported
          # sibling adds a newer binder. Weaken the domain past that prefix, then
          # redirect references to those siblings from their original outer
          # binders to the transported binders. Merely weakening is insufficient
          # for a dependent sibling such as `suffix : Path(destination, ...)`:
          # it leaves `suffix` indexed by the old destination.
          Context.extend(c, Eval.eval(rebound_domain, Context.env(c)))
        end)

      body_names = Enum.reduce(sib_data, [carried_prf_name() | branch_names], fn %{name: s}, acc -> [s | acc] end)

      # Compose the carried equation with every ordinary constructor-index
      # substitution. Previously this path replaced only `idx`; activating a
      # convoy could therefore leave unrelated result indices abstract even
      # though the same branch unifier had solved them.
      carried_replaced_goal =
        result_type_term
        |> Subst.shift(arity, 0)
        |> replace_branch_vars(subst)

      carried_normalized_goal = Kernel.normalize(check_ctx, carried_replaced_goal)

      branch_goal0 =
        carried_normalized_goal
        |> replace_term(idx_branch, ctor_idx)

      cod_expected =
        branch_goal0
        # The body is checked under the proof binder and the transported sibling
        # telescope. Its goal must name those NEW sibling values too: merely
        # weakening leaves dependent occurrences pointing at the original outer
        # values (`View(char, destination, regular, constraints)` after matching
        # a singleton membership), so the constructor indices remain rigid and
        # appear unconstrained. Use the same canonical rebinding applied to each
        # sibling domain, now across the complete transported prefix.
        |> Subst.shift(1, 0)
        |> rebind_carried_sibling_term(sib_data, m, sc)
        |> then(&Kernel.normalize(branch_ctx_full, &1))

      body_result = elaborate_branch_body(body_expr, cod_expected, body_names, branch_ctx_full, env)

      with {:ok, inner} <- body_result do
        source_pack_type = dependent_pack_type(Enum.map(rebound_sib_data, & &1.bound_source_dom), env)
        refined_pack_type = dependent_pack_type(Enum.map(rebound_sib_data, & &1.bound_dom), env)

        source_pack =
          dependent_pack_value(
            Enum.map(rebound_sib_data, fn %{index: index} -> {:var, index + sc} end),
            env
          )

        pack_motive =
          {:lam, Cure.Core.Grade.unrestricted(), t_b1, abstract_term(source_pack_type, idx_b1, 0)}

        transported_pack =
          {:app, transport_case({:var, 0}, t_b1, pack_motive, idx_b1), source_pack}

        pack_ctx = Context.extend(branch_ctx1, Eval.eval(refined_pack_type, Context.env(branch_ctx1)))
        pack_type_under_binder = Subst.shift(refined_pack_type, 1, 0)

        projections =
          dependent_pack_projections(pack_type_under_binder, {:var, 0}, m, pack_ctx, env)

        body_under_pack =
          inner
          |> Subst.shift(1, m)
          |> Subst.instantiate(projections)

        wrapped =
          {:app, {:lam, Cure.Core.Grade.unrestricted(), refined_pack_type, body_under_pack}, transported_pack}

        {:ok, {cname, arity, {:lam, Cure.Core.Grade.unrestricted(), eq_dom_term, wrapped}}}
      end
    end
  end

  defp carried_prf_name, do: "$carried_idx_prf"

  defp dependent_pack_type([domain], _env), do: domain

  defp dependent_pack_type([domain | rest], env) do
    sigma = Inductive.builtin(env, :sigma)
    tail = dependent_pack_type(rest, env)
    family = {:lam, Cure.Core.Grade.unrestricted(), domain, tail}
    {:data, sigma, [domain, family], []}
  end

  defp dependent_pack_value([value], _env), do: value

  defp dependent_pack_value([value | rest], env) do
    {:ctor, sigma_ctor_name(env), [value, dependent_pack_value(rest, env)]}
  end

  # The compiler pack has exactly `count` logical siblings. Its final sibling is
  # atomic even when that sibling's OWN type is Sigma: recursing until the type
  # ceases to be Sigma eta-expanded a lone dependent-pair sibling and changed its
  # Core identity. Unpack by the construction-site arity, not by the payload's
  # user-authored shape.
  defp dependent_pack_projections(_type, value, 1, _ctx, _env), do: [value]

  defp dependent_pack_projections(type, value, count, ctx, env) when count > 1 do
    sigma = Inductive.builtin(env, :sigma)

    case Kernel.normalize(ctx, type) do
      {:data, ^sigma, [domain, family], []} ->
        first = core_sigma_projection(:sigma_first, domain, family, value, env)
        second = core_sigma_projection(:sigma_second, domain, family, value, env)
        tail_type = Kernel.normalize(ctx, {:app, family, first})
        [first | dependent_pack_projections(tail_type, second, count - 1, ctx, env)]

      _not_a_pack ->
        [value]
    end
  end

  defp core_sigma_projection(name, domain, family, value, env) do
    key = Env.resolve_key(env, env.defs, name)

    {:app, {:app, {:app, {:global, key}, domain}, family}, value}
  end

  defp rebind_carried_sibling_term(term, siblings, prior_count, scope_shift) do
    shifted = Subst.shift(term, prior_count, 0)

    subst =
      siblings
      |> Enum.take(prior_count)
      |> Enum.with_index()
      |> Map.new(fn {%{index: original_index}, introduced_at} ->
        original_var = original_index + scope_shift + prior_count
        rebound_var = prior_count - introduced_at - 1
        {original_var, {:var, rebound_var}}
      end)

    replace_branch_vars(shifted, subst)
  end

  defp elaborate_branch_body(@contextual_impossible_body, expected, _names, ctx, env),
    do: contextual_absurd(ctx, expected, env)

  defp elaborate_branch_body({:rewrite_expr, _meta, _children} = expr, expected, names, ctx, env),
    do: elaborate_expr_checked(expr, expected, names, ctx, env)

  # A nested `match` arm body is a checking-mode expression: `expected` is the
  # (index-refined) result type for this branch, exactly what its motive needs.
  defp elaborate_branch_body({:pattern_match, _meta, _children} = expr, expected, names, ctx, env),
    do:
      if(effect_goal?(expected, ctx),
        do: elaborate_effect_branch(expr, expected, names, ctx, env),
        else: elaborate_expr_checked(expr, expected, names, ctx, env)
      )

  # A nested `with` arm body: like a nested `match` body, a checking-mode
  # expression whose `expected` is this branch's (index/value-refined) goal —
  # route to the checked dispatcher so with-abstractions nest and compose.
  defp elaborate_branch_body({:with_abs, _meta, _children} = expr, expected, names, ctx, env),
    do:
      if(effect_goal?(expected, ctx),
        do: elaborate_effect_branch(expr, expected, names, ctx, env),
        else: elaborate_expr_checked(expr, expected, names, ctx, env)
      )

  defp elaborate_branch_body({:function_call, meta, _args} = expr, expected, names, ctx, env) do
    if effect_goal?(expected, ctx) do
      elaborate_effect_branch(expr, expected, names, ctx, env)
    else
      name = Keyword.get(meta, :name)

      cond do
        name == "reflexive" ->
          elaborate_expr_checked(expr, expected, names, ctx, env)

        is_binary(name) and
            Inductive.get_ctor(env, resolve_ctor_key(env, String.to_atom(name))) != nil ->
          # A constructor branch body. Infer FIRST — this preserves every case that
          # already worked, including a reconstruction whose indices the present
          # arguments determine and the carried-index-Eq transport (which wraps an
          # inferred body). Retry in checking mode — letting the branch's expected
          # type drive the constructor — when inference cannot pin the erased indices
          # (`prim()`/`seq(l,r)` reconstructed at a refined index with no present
          # argument to solve `av`/`bv` from: `:unsolved_metavariables`) OR when a
          # field is not inferable at all (`:unsupported_expression`) — e.g. an
          # unannotated lambda in a field like `MkLensRep(v, fn new -> ...)`, whose
          # domain only the field type supplies. Both are exactly the cases Idris
          # handles by checking the arm body against the match's expected type; the
          # kernel re-checks either way, so this only ever accepts well-typed terms.
          case elaborate_expr_typed(expr, names, ctx, env) do
            {:ok, term, _type} ->
              {:ok, term}

            {:error, {:unsolved_metavariables, _}} ->
              elaborate_expr_checked(expr, expected, names, ctx, env)

            {:error, {:unsupported_expression, _}} ->
              elaborate_expr_checked(expr, expected, names, ctx, env)

            {:error, _} = orig ->
              # Inference of a constructor arm can ALSO fail with an index/result
              # mismatch when a FIELD's type depends on an index that no present
              # argument determines — the index is only available from the branch's
              # refined goal. `MkP(reflexive(OT()))` at the refined goal `P(OA)`:
              # `MkP : Eq(f(x), OT) -> P(x)`, and `reflexive(OT()) : Eq(OT, OT)` hides
              # `f(OA)` behind an ι-reduction, so the field cannot fix the index `x`;
              # inference reaches the checking-less ctor path, leaves the index a
              # metavariable, and rejects with `f(?0) ≠ OT` (`:index_mismatch`). Retry
              # in checking mode so the goal seeds the constructor's indices
              # (`elaborate_ctor_app_bidirectional` pins `x := OA` from `P(OA)` before
              # checking the field). Strictly additive: reached only after inference
              # already errored, the ORIGINAL inference error is surfaced if the
              # checked retry also fails, and the kernel re-checks the assembled term —
              # so this only ever admits well-typed constructors. This is exactly how
              # Idris checks a constructor arm body against the match's expected type.
              case elaborate_expr_checked(expr, expected, names, ctx, env) do
                {:ok, _} = ok -> ok
                {:error, _} -> orig
              end
          end

        true ->
          # An ordinary (non-constructor) function-call arm body. Infer FIRST to
          # preserve every case that already worked; retry in checking mode when
          # inference cannot solve the call's result-type metavariables — a
          # polymorphic nullary function like `empty() -> Iter(t)` whose `t` has no
          # argument to fix it (`:unsolved_metavariables`) — or when an argument is
          # not inferable (`:unsupported_expression`, e.g. an unannotated lambda
          # passed to a higher-order call), letting the branch's expected type drive
          # it. Mirrors the constructor-arm path above; Idris checks arm bodies
          # against the match's expected type, and the kernel re-checks either way.
          case elaborate_expr_typed(expr, names, ctx, env) do
            {:ok, term, _type} -> {:ok, term}
            {:error, {:unsolved_metavariables, _}} -> elaborate_expr_checked(expr, expected, names, ctx, env)
            {:error, {:unsupported_expression, _}} -> elaborate_expr_checked(expr, expected, names, ctx, env)
            {:error, _} = err -> err
          end
      end
    end
  end

  # A tuple `%[a, b, …]` (dependent-pair / flat Σ-telescope introduction) as a
  # branch body: a checking-mode expression against this branch's (index-refined)
  # Σ type — the expected type pins the components' erased indices (an FRP `step`'s
  # `prim()` continuation has no other way to solve its index metas; likewise a
  # flat n-ary tuple whose last component is a bare `[]` needs the goal's `List(_)`
  # to solve the inner `Nil` element). Without this a Σ-returning eliminator fails
  # its arms with `:unsupported_expression`, or an inner `[]` fails infer-only with
  # `{:unsolved_metavariables, :Nil}`. Matches ANY arity ≥ 2: the 2-tuple is a bare
  # dependent pair, arity ≥ 3 is the flat telescope (#35) — both check identically.
  #
  # Under an `Effect(R)` goal the type to check against is `R`, not `Effect(R)` —
  # there is no effect head to check a Σ against — and the pure value is then
  # lifted with `pure`. `elaborate_effect_branch` does exactly that.
  defp elaborate_branch_body({:tuple, _meta, elems} = expr, expected, names, ctx, env)
       when length(elems) >= 2 do
    if effect_goal?(expected, ctx),
      do: elaborate_effect_branch(expr, expected, names, ctx, env),
      else: elaborate_expr_checked(expr, expected, names, ctx, env)
  end

  # A `[] -> []` (or `[a,b] -> [...]`) arm body: check it against the branch goal
  # so a bare `[]` arm pins its element type from the goal instead of failing
  # infer-only with `{:unsolved_metavariables, :Nil}` (Finding A). `expected` here
  # is the refined branch goal; `elaborate_expr_checked` self-desugars the `:list`.
  # Under an `Effect(R)` goal the element type lives in `R`, so the same detour
  # through the pure-lift applies (a bare `[]` arm would otherwise fail with
  # `{:unsolved_metavariables, :Nil}`).
  defp elaborate_branch_body({:list, _, _} = expr, expected, names, ctx, env) do
    if effect_goal?(expected, ctx),
      do: elaborate_effect_branch(expr, expected, names, ctx, env),
      else: elaborate_expr_checked(expr, expected, names, ctx, env)
  end

  defp elaborate_branch_body({:block, meta, _statements} = expr, expected, names, ctx, env) do
    cond do
      effect_goal?(expected, ctx) ->
        elaborate_effect_branch(expr, expected, names, ctx, env)

      Keyword.get(meta, :induction_case_body, false) ->
        elaborate_expr_checked(expr, expected, names, ctx, env)

      true ->
        case elaborate_expr_typed(expr, names, ctx, env) do
          {:ok, term, type} ->
            {:ok, maybe_inject_union(term, type, expected, ctx, env)}

          {:error, _} ->
            case elaborate_expr_checked(expr, expected, names, ctx, env) do
              {:ok, _} = ok -> ok
              {:error, _} = checked_error -> checked_error
            end
        end
    end
  end

  # Induction hypotheses are generated at a proposition specialized to the
  # recursive constructor field. Check a bare hypothesis body against the
  # refined branch goal here instead of taking the ordinary infer-first path;
  # that gives E113 the authored use range and both propositions when the user
  # tries to use the hypothesis for a different specialization.
  defp elaborate_branch_body({:variable, meta, _name} = expr, expected, names, ctx, env) do
    cond do
      effect_goal?(expected, ctx) ->
        elaborate_effect_branch(expr, expected, names, ctx, env)

      match?({:vtype, _}, Eval.eval(expected, Context.env(ctx))) ->
        # A branch of a large elimination is checked against `Type`. Inferring a
        # same-named record identifier first would select its value constructor
        # (`fields -> Record`) before the expected universe can select the family.
        elaborate_expr_checked(expr, expected, names, ctx, env)

      Keyword.has_key?(meta, :induction_hypothesis) ->
        elaborate_expr_checked(expr, expected, names, ctx, env)

      true ->
        case elaborate_expr_typed(expr, names, ctx, env) do
          {:ok, term, type} ->
            {:ok, maybe_inject_union(term, type, expected, ctx, env)}

          {:error, _} = orig ->
            case elaborate_expr_checked(expr, expected, names, ctx, env) do
              {:ok, _} = ok -> ok
              {:error, _} -> orig
            end
        end
    end
  end

  # The general branch body: inferred FIRST. `maybe_inject_union/5` is a strict no-op unless
  # this branch's goal is a generated anonymous-union family — in which case the
  # inferred body is injected (a member value) or widened (a narrower union, as
  # produced by a sub-union arm's `assert_type` ascription) into the goal. Without it
  # a sub-union arm's body has the SUB-union's type while the motive demands the wide
  # one, and the kernel rejects the branch with `:branch_type`.
  #
  # On inference FAILURE, retry in CHECKING mode against the branch goal. Inference
  # does not thread the refined goal, so a body that needs it to make progress is
  # wrongly rejected — canonically a BLOCK body (`let x = e in body`) whose inner
  # DEPENDENT `match` on a local/let-bound variable relies on the goal to FORCE the
  # constructor-field index binders (else a proof field keeps its type over the OPAQUE
  # erased indices `$erased_x`/`$erased_k` instead of the scrutinee's concrete `x, k`,
  # and a later reduction-requiring use fails conversion at mismatched de Bruijn
  # depths). Checking mode threads the goal in — reaching the index-forcing branch
  # path exactly as a ctor-call body (`Branch(k, match compareKeys(x, k), r)`) already
  # does. Not per-shape (block, and any other shape reaching this catch-all): whatever
  # body inference rejects for lack of the goal gets one goal-informed retry. Surface
  # the ORIGINAL inference error if the checked retry also fails; strictly additive
  # (only on failure), and the kernel re-checks the assembled branch.
  defp elaborate_branch_body(expr, expected, names, ctx, env) do
    if effect_goal?(expected, ctx) do
      elaborate_effect_branch(expr, expected, names, ctx, env)
    else
      case elaborate_expr_typed(expr, names, ctx, env) do
        {:ok, term, type} ->
          {:ok, maybe_inject_union(term, type, expected, ctx, env)}

        {:error, _} = orig ->
          case elaborate_expr_checked(expr, expected, names, ctx, env) do
            {:ok, _} = ok ->
              ok

            {:error, _cr} ->
              orig
          end
      end
    end
  end

  # `R` of an `Effect(R)` goal, as a Core type. Only call under `effect_goal?/2`.
  defp effect_result_type(expected, ctx) do
    sig = Context.signature(ctx)
    {:veffect_type, result_value} = Normalise.whnf_value(Eval.eval(expected, Context.env(ctx)), sig)

    Quote.reify(result_value, Context.length(ctx), sig)
  end

  @doc false
  def effect_goal?(expected, ctx) do
    value = Eval.eval(expected, Context.env(ctx))
    whnf = Normalise.whnf_value(value, Context.signature(ctx))
    match?({:veffect_type, _}, whnf)
  end

  # Check a branch against its goal, lifting a pure value into `Effect(T)` when
  # direct elaboration shows that it is pure. Direct checking comes first: it
  # lets an expected `Effect(Pid(m))` solve the concrete process-index implicit
  # on `beam_ops self` instead of attempting unconstrained inference.
  @doc false
  def elaborate_effect_branch(expr, expected, names, ctx, env) do
    result =
      if effect_goal?(expected, ctx) do
        case expr do
          {:pattern_match, _, _} ->
            elaborate_expr_checked(expr, expected, names, ctx, env)

          {:with_abs, _, _} ->
            elaborate_expr_checked(expr, expected, names, ctx, env)

          {:conditional, _, _} ->
            elaborate_expr_checked(expr, expected, names, ctx, env)

          _ ->
            case elaborate_expr_checked(expr, expected, names, ctx, env) do
              {:ok, _term} = ok ->
                ok

              {:error, checked_error} ->
                case elaborate_expr_typed(expr, names, ctx, env) do
                  {:ok, _term, {:veffect_type, _}} ->
                    {:error, checked_error}

                  {:ok, _term, type} ->
                    result_type = effect_result_type(expected, ctx)

                    with {:ok, pure_term} <- elaborate_expr_checked(expr, result_type, names, ctx, env) do
                      {:ok, {:effect_pure, maybe_inject_union(pure_term, type, result_type, ctx, env)}}
                    else
                      {:error, _} -> {:error, checked_error}
                    end

                  # Inference failed — but an INTRODUCTION FORM has no inference rule
                  # at all (a bare data constructor is `:ctor_requires_checking_mode`;
                  # a bare `[]` is `{:unsolved_metavariables, :Nil}`), so a pure branch
                  # body like `%[:noreply, state]` is never inferable and would never
                  # reach the lift above. Check it at the result type and lift, exactly
                  # as the trailing expression of an effectful `let`-block does.
                  {:error, _} ->
                    result_type = effect_result_type(expected, ctx)

                    case elaborate_expr_checked(expr, result_type, names, ctx, env) do
                      {:ok, pure_term} -> {:ok, effect_pure_for_bind(pure_term, result_type, ctx)}
                      {:error, _} -> {:error, checked_error}
                    end
                end
            end
        end
      else
        with {:ok, term, type} <- elaborate_expr_typed(expr, names, ctx, env) do
          {:ok, maybe_inject_union(term, type, expected, ctx, env)}
        end
      end

    attach_effect_context(result, expr)
  end

  defp attach_effect_context({:error, {:source_context, reason, context}}, expression)
       when is_map(context) do
    if Map.get(context, :expectation_origin) in [nil, :annotation] do
      {:error, {:source_context, reason, Map.merge(context, expectation_context(expression, :effects, :effect, nil))}}
    else
      {:error, {:source_context, reason, context}}
    end
  end

  defp attach_effect_context({:error, reason}, expression),
    do: {:error, {:source_context, reason, expectation_context(expression, :effects, :effect, nil)}}

  defp attach_effect_context(result, _expression), do: result

  # A `let x = e ⏎ …` block elaborates to the Core `:let` binder:
  # `{:let, Cure.Core.Grade.unrestricted(), T, e, body}`, binding `e` EXACTLY ONCE.
  #
  # Previously this desugared by SURFACE substitution (`body[x := e]`), which
  # re-elaborated `e` at every use site and dropped it entirely at zero uses —
  # the recorded root cause of let-duplication and the join-point residual, and a
  # silent aliasing engine that would defeat any future linearity check.
  # Substitution was kept only because it made a let-bound value *transparent* in
  # a later dependent type; a β-redex binds once but loses that transparency.
  #
  # The Core `:let` supplies both (Idris `Core/TT/Binder.idr` `Let`, Lean
  # `Expr.letE`): ζ makes the variable definitionally its value. Here the
  # elaborator's own context gets the same treatment via `Context.extend_def/3`,
  # so `elaborate_expr_typed` on the remainder sees `x` as its value and dependent
  # lets keep checking. The kernel re-checks the emitted `:let` regardless.
  defp elaborate_let_block([final], expected_core, names, ctx, env) do
    sig = Context.signature(ctx)

    case Normalise.whnf_value(Eval.eval(expected_core, Context.env(ctx)), sig) do
      # The block's result type is `Effect(R)`. The final expression is either
      # already effectful (return it, checked against `Effect(R)`) or a plain
      # value to lift with `pure` — Idris's `do`-block whose last statement is a
      # value gets an implicit `pure` (design 2026-07-09-effect-type-former §5.1).
      {:veffect_type, r_val} ->
        r_reified = Quote.reify(r_val, Context.length(ctx), sig)

        case elaborate_expr_typed(final, names, ctx, env) do
          {:ok, _core, ty} ->
            case Normalise.whnf_value(ty, sig) do
              # Already effectful — check against `Effect(R)` and keep it.
              {:veffect_type, _} ->
                elaborate_expr_checked(final, expected_core, names, ctx, env)

              # A pure value — check at `R` and wrap in `pure`.
              _ ->
                with {:ok, r_core} <- elaborate_expr_checked(final, r_reified, names, ctx, env) do
                  {:ok, effect_pure_for_bind(r_core, r_reified, ctx)}
                end
            end

          # Non-inferable final: try the pure-wrap; if THAT fails too, surface the
          # original inference error rather than the (likely less informative) one.
          {:error, _} = err ->
            case elaborate_expr_checked(final, r_reified, names, ctx, env) do
              {:ok, r_core} ->
                {:ok, effect_pure_for_bind(r_core, r_reified, ctx)}

              {:error, _e2} ->
                err
            end
        end

      # A pure block — the existing behaviour.
      _ ->
        elaborate_expr_checked(final, expected_core, names, ctx, env)
    end
  end

  defp elaborate_let_block(
         [{:macro_check, _meta, [condition, failure]} | rest],
         expected_core,
         names,
         ctx,
         env
       )
       when rest != [] do
    with {:ok, condition_core} <-
           elaborate_expr_checked(condition, bool_type_term(Context.signature(ctx)), names, ctx, env),
         {:ok, failure_core} <- elaborate_expr_checked(failure, expected_core, names, ctx, env),
         {:ok, body_core} <- elaborate_let_block(rest, expected_core, names, ctx, env) do
      {:ok, bool_case(condition_core, expected_core, body_core, failure_core, ctx)}
    end
  end

  defp elaborate_let_block(
         [{:assignment, meta, [{:variable, _, name}, rhs]} = assignment | rest],
         expected_core,
         names,
         ctx,
         env
       ) do
    if not Keyword.get(meta, :let, false) do
      {:error, {:unsupported_block_statement, assignment}}
    else
      # A surface grade (`let c :linear = e`, plan slice 5b); absent means ω.
      grade = Keyword.get(meta, :grade, Grade.unrestricted())

      case Keyword.get(meta, :type_annotation) do
        nil -> let_inferred(name, rhs, meta, grade, rest, expected_core, names, ctx, env)
        ann -> let_ascribed(name, rhs, ann, meta, grade, rest, expected_core, names, ctx, env)
      end
    end
  end

  # A pattern-valued let is the single-arm form of the ordinary typed pattern
  # eliminator. Keeping the authored pattern intact means constructor, tuple,
  # list, record, map, binary, pin, and nested patterns all take the same path as
  # `match`; the match checker also supplies the structured impossible-pattern
  # and missing-branch diagnostics. The scrutinee remains a single Core `case`
  # input, so an effectful initializer is evaluated exactly once.
  defp elaborate_let_block(
         [{:assignment, meta, [pattern, rhs]} = assignment | rest],
         expected_core,
         names,
         ctx,
         env
       )
       when rest != [] do
    if Keyword.get(meta, :let, false) do
      # Match dispatch has several structural fast paths (notably tuple
      # projection) which deliberately require a variable scrutinee so they
      # cannot duplicate an effectful expression. Give every pattern-let that
      # same safe shape: evaluate the initializer once, then eliminate the
      # fresh binder. `$` is not a source identifier character, so authored
      # code cannot capture this name.
      scrutinee_name = "$letpat" <> fresh_tag()
      scrutinee = {:variable, [], scrutinee_name}
      body = {:block, Keyword.take(meta, [:line, :col]), rest}
      arm = {:match_arm, Keyword.put([], :pattern, pattern), [body]}
      match = {:pattern_match, Keyword.take(meta, [:line, :col]), [scrutinee, arm]}

      binding =
        {:assignment, Keyword.merge(Keyword.take(meta, [:line, :col]), let: true, opaque: true), [scrutinee, rhs]}

      elaborate_let_block([binding, match], expected_core, names, ctx, env)
    else
      {:error, {:unsupported_block_statement, assignment}}
    end
  end

  defp elaborate_let_block(other, _expected_core, _names, _ctx, _env),
    do: {:error, {:unsupported_block, other}}

  defp elaborate_macro_failure(meta, args, names, ctx, env) do
    syntax_family = Env.resolve_key(env, env.families, :Syntax)
    syntax_type = {:data, syntax_family, [], []}

    with {:ok, arg_terms} <-
           Enum.reduce_while(args, {:ok, []}, fn arg, {:ok, acc} ->
             case elaborate_expr_checked(arg, syntax_type, names, ctx, env) do
               {:ok, term} -> {:cont, {:ok, [term | acc]}}
               {:error, _} = error -> {:halt, error}
             end
           end),
         %{name: failure_ctor} <- Inductive.get_ctor(env, :Failure) do
      name = Keyword.get(meta, :name, "?")
      {:ok, {:ctor, failure_ctor, [{:atom_lit, String.to_atom(name)}, core_list(Enum.reverse(arg_terms))]}}
    else
      nil -> {:error, {:unknown_macro_failure, Keyword.get(meta, :name, "?")}}
    end
  end

  defp core_list(items), do: Enum.reduce(Enum.reverse(items), {:ctor, :Nil, []}, &{:ctor, :Cons, [&1, &2]})

  # INFERENCE-mode block: build the `:let` Core chain (the final statement is
  # inferred, each `let` binds its rhs with a ζ definition so a later statement
  # sees the concrete value) and return only the term — the `{:block}` clause of
  # `elaborate_expr_typed/4` hands it to `Kernel.infer` for its type. Mirrors
  # `elaborate_let_block/5`/`bind_once_let/10`, minus the threaded expected type.
  defp infer_block_term([final], names, ctx, env) do
    with {:ok, term, _type} <- elaborate_expr_typed(final, names, ctx, env), do: {:ok, term}
  end

  defp infer_block_term(
         [{:assignment, meta, [{:variable, _, name}, rhs]} = assignment | rest],
         names,
         ctx,
         env
       ) do
    if not Keyword.get(meta, :let, false) do
      {:error, {:unsupported_block_statement, assignment}}
    else
      grade = Keyword.get(meta, :grade, Grade.unrestricted())

      with {:ok, rhs_core, ty_core, ty_value} <- block_rhs(rhs, meta, names, ctx, env) do
        rhs_value = Eval.eval(rhs_core, Context.env(ctx))
        ctx1 = Context.extend_def(ctx, ty_value, rhs_value)

        with {:ok, body_core} <- infer_block_term(rest, [name | names], ctx1, env) do
          {:ok, {:let, grade, ty_core, rhs_core, body_core}}
        end
      end
    end
  end

  defp infer_block_term(other, _names, _ctx, _env), do: {:error, {:unsupported_block, other}}

  # A `let` binding's rhs, settled to `{rhs_core, ty_core, ty_value}`. An
  # unannotated `let x = e` synthesises `e`'s type (SIGNATURE-AWARE reify, as
  # `let_inferred/9`); an ascribed `let x : T = e` checks `e` against `T`.
  defp block_rhs(rhs, meta, names, ctx, env) do
    case Keyword.get(meta, :type_annotation) do
      nil ->
        with {:ok, rhs_core, rhs_type} <- elaborate_expr_typed(rhs, names, ctx, env) do
          ty_core = Quote.reify(rhs_type, Context.length(ctx), Context.signature(ctx))
          {:ok, rhs_core, ty_core, rhs_type}
        end

      ann ->
        with {:ok, ty_core} <- elaborate_type(ann, names, env, ctx),
             {:ok, rhs_core} <- elaborate_expr_checked(rhs, ty_core, names, ctx, env) do
          {:ok, rhs_core, ty_core, Eval.eval(ty_core, Context.env(ctx))}
        end
    end
  end

  # `let x : T = e` — BIDIRECTIONAL. The ascription supplies the type a
  # check-only rhs cannot synthesise, so the rhs is elaborated in CHECKING mode
  # (exactly what surface substitution did at each use site) and bound ONCE.
  # This is the general escape from the check-only residual.
  defp let_ascribed(name, rhs, ann, meta, grade, rest, expected_core, names, ctx, env) do
    with {:ok, ty_core} <- elaborate_type(ann, names, env, ctx),
         ty_value = Eval.eval(ty_core, Context.env(ctx)) do
      case Normalise.whnf_value(ty_value, Context.signature(ctx)) do
        {:veffect_type, _} ->
          with {:ok, rhs_core} <- check_local_binding_rhs(rhs, ty_core, name, meta, names, ctx, env) do
            bind_once_let(name, rhs_core, ty_core, ty_value, grade, rest, expected_core, names, ctx, env)
          end

        _ ->
          elaborate_non_effect_ascribed_let(
            name,
            rhs,
            meta,
            grade,
            rest,
            ty_core,
            ty_value,
            expected_core,
            names,
            ctx,
            env
          )
      end
    end
  end

  defp elaborate_non_effect_ascribed_let(
         name,
         rhs,
         meta,
         grade,
         rest,
         ty_core,
         ty_value,
         expected_core,
         names,
         ctx,
         env
       ) do
    effect_type = {:effect_type, ty_core}

    # Prefer the annotation exactly as written. An actually effectful RHS cannot
    # check at T and falls through to Effect(T); a pure or check-only RHS succeeds
    # once without first constructing and discarding a lifted effect program.
    case check_local_binding_rhs(rhs, ty_core, name, meta, names, ctx, env) do
      {:ok, rhs_core} ->
        bind_once_let(
          name,
          rhs_core,
          ty_core,
          ty_value,
          grade,
          rest,
          expected_core,
          names,
          ctx,
          env
        )

      {:error, pure_error} ->
        case check_local_binding_rhs(rhs, effect_type, name, meta, names, ctx, env) do
          {:ok, rhs_core} ->
            effectful_let_bind(
              name,
              rhs_core,
              ty_value,
              grade,
              rest,
              expected_core,
              names,
              ctx,
              env
            )

          {:error, _effect_error} ->
            {:error, pure_error}
        end
    end
  end

  defp check_local_binding_rhs(rhs, expected, name, meta, names, ctx, env) do
    case elaborate_expr_checked(rhs, expected, names, ctx, env) do
      {:error, reason} = error ->
        if Keyword.get(meta, :have, false) do
          {:error, attach_expectation_context(reason, rhs, :local_fact, name, nil)}
        else
          error
        end

      result ->
        result
    end
  end

  # `let x = e` — synthesise `e`'s type, then bind once.
  defp let_inferred(name, rhs, meta, grade, rest, expected_core, names, ctx, env) do
    case elaborate_expr_typed(rhs, names, ctx, env) do
      {:ok, rhs_core, rhs_type} ->
        case Normalise.whnf_value(rhs_type, Context.signature(ctx)) do
          # An EFFECTFUL rhs: `let x = eff()` where `eff() : Effect(T)`. Do NOT
          # bind `x : Effect(T)` via `:let`; sequence with `bind`, whose
          # continuation binds `x : T` — the UNWRAPPED payload the effect
          # produces (Idris's `x <- eff; rest` ⟶ `bind eff (λ x:T. rest)`,
          # design 2026-07-09-effect-type-former §5.1). The kernel re-checks the
          # emitted `effect_bind`.
          {:veffect_type, payload_val} ->
            # A surface grade (`let r :linear = eff()`) rides onto the `bind`
            # continuation's binder — the effect's RESULT `r` is used per `grade`
            # (linear channels: used exactly once). Relevance enforces it; the
            # kernel's `bind` accepts the continuation's own grade.
            effectful_let_bind(name, rhs_core, payload_val, grade, rest, expected_core, names, ctx, env)

          # A PURE rhs — the existing path. SIGNATURE-AWARE reify: a
          # `{:vdata, name, args}` value flattens a family's params and indices
          # into one list; without the signature the split is not recoverable and
          # the read-back puts them all in `params`, so a `:let` over an indexed
          # family fails the kernel's arity check (`:arg_arity`). Agda
          # `getNumberOfParameters` / Lean `inductive_val.get_nparams`.
          _ ->
            ty_core = Quote.reify(rhs_type, Context.length(ctx), Context.signature(ctx))

            rest =
              if Keyword.get(meta, :opaque, false),
                do: rest,
                else: expose_transparent_tuple_scrutinee(rest, name, rhs)

            bind_once_let(
              name,
              rhs_core,
              ty_core,
              rhs_type,
              grade,
              rest,
              expected_core,
              names,
              ctx,
              env,
              Keyword.get(meta, :opaque, false)
            )
        end

      # The rhs has no INFERABLE type — a bare lambda, an `if`/`pickup`, any
      # check-only shape. Surface substitution never had to infer it: it
      # re-elaborated the rhs in CHECKING mode at each use site. A `:let` must
      # commit to one type up front, so it needs `let x : T = e` (`let_ascribed/8`).
      {:error, _} ->
        cond do
          # A GRADE cannot survive this branch. Every path below abandons the `:let`
          # node and surface-substitutes the rhs, so there is nowhere to record the
          # grade and it would be silently dropped — the program would compile, pass,
          # and lie about its linearity. A graded `let` must produce a real `:let`.
          # Ascribing the binding gives `let_ascribed/9`, which always builds one.
          Keyword.has_key?(meta, :grade) ->
            {:error,
             local_binding_annotation_error(
               :graded_let_needs_annotation,
               name,
               meta,
               rhs,
               count_surface_uses(rest, name)
             )}

          # Shadowing + non-inferable is unrepresentable: substitution would
          # capture and an unannotated `:let` cannot be built. Report the
          # actionable local-binding problem rather than leaking the rhs's
          # infer-only `:unsupported_expression` failure.
          Enum.any?(rest, &binds_any?(&1, [name])) ->
            {:error,
             local_binding_annotation_error(
               :let_needs_annotation,
               name,
               meta,
               rhs,
               count_surface_uses(rest, name),
               :shadowed_before_use,
               first_binding_span(rest, name)
             )}

          # Substitution is only safe at EXACTLY ONE use:
          #
          #   * ≥2 uses  — it DUPLICATES the rhs. That is what made surface
          #     substitution a silent aliasing engine.
          #   * 0 uses   — it DROPS the rhs, which is therefore never elaborated:
          #     an ill-typed unused binding sails through to a green build.
          #     (It also means a zero-use binding would not RUN once effects
          #     arrive — that is `effect_bind`'s job, not this path's.)
          #
          # Both are refused, and the message says how to fix it: ascribe the
          # binding (`let x : T = e`) and it binds once, checked.
          count_surface_uses(rest, name) != 1 ->
            {:error,
             local_binding_annotation_error(
               :let_needs_annotation,
               name,
               meta,
               rhs,
               count_surface_uses(rest, name)
             )}

          # Exactly one use: the rhs is elaborated once, in checking mode, at that
          # use site. No duplication, and it IS type-checked.
          true ->
            rest
            |> Enum.map(&subst_surface_var(&1, name, rhs))
            |> elaborate_let_block(expected_core, names, ctx, env)
        end
    end
  end

  # Preserve the single Core `let`, but expose a pure tuple initializer to a
  # directly following match. Tuple-matrix lowering needs the authored element
  # expressions to build its decision tree; retaining only the local variable
  # can leave a dependent Sigma closure tied to the pre-let context and obscure
  # its telescope arity. This rewrite does not duplicate evaluation: tuple
  # construction remains in the Core let, while the match sees only the tuple's
  # already-bound element expressions.
  defp expose_transparent_tuple_scrutinee(rest, name, {:tuple, _, _} = rhs) do
    Enum.map(rest, fn
      {:pattern_match, meta, [{:variable, _, ^name} | arms]} ->
        {:pattern_match, meta, [rhs | arms]}

      expression ->
        expression
    end)
  end

  defp expose_transparent_tuple_scrutinee(rest, _name, _rhs), do: rest

  defp local_binding_annotation_error(
         kind,
         name,
         meta,
         rhs,
         use_count,
         reason \\ :initializer_not_inferable,
         shadow_span \\ nil
       ) do
    info = Cure.MetaAST.Metadata.source_info(meta)

    details = %{
      name: name,
      grade: Keyword.get(meta, :grade),
      use_count: use_count,
      reason: reason,
      span: info && info.whole,
      name_span: info && info.name,
      grade_span: info && (Map.get(info.fields, :grade) || info.annotation),
      initializer_span: surface_expression_span(rhs),
      shadow_span: shadow_span
    }

    {kind, details}
  end

  defp first_binding_span(list, name) when is_list(list) do
    Enum.find_value(list, &first_binding_span(&1, name))
  end

  defp first_binding_span({:match_arm, meta, body}, name) do
    pattern = Keyword.get(meta, :pattern)
    pattern_binder_span(pattern, name) || first_binding_span(body, name)
  end

  defp first_binding_span({:lambda, meta, children}, name) do
    parameter_span =
      Enum.find_value(Keyword.get(meta, :params, []), fn
        {:param, pmeta, ^name} ->
          case Cure.MetaAST.Metadata.source_info(pmeta) do
            %Cure.MetaAST.SourceInfo{name: %Cure.Diagnostic.Span{} = span} -> span
            %Cure.MetaAST.SourceInfo{whole: %Cure.Diagnostic.Span{} = span} -> span
            _ -> nil
          end

        _ ->
          nil
      end)

    parameter_span || first_binding_span(List.wrap(children), name)
  end

  defp first_binding_span({_tag, _meta, children}, name) when is_list(children),
    do: first_binding_span(children, name)

  defp first_binding_span(_other, _name), do: nil

  defp pattern_binder_span({:variable, meta, name}, name) do
    case Cure.MetaAST.Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{name: %Cure.Diagnostic.Span{} = span} -> span
      %Cure.MetaAST.SourceInfo{whole: %Cure.Diagnostic.Span{} = span} -> span
      _ -> nil
    end
  end

  defp pattern_binder_span({:typed_pattern, meta, [name, _type]}, name) when is_binary(name) do
    case Cure.MetaAST.Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{name: %Cure.Diagnostic.Span{} = span} -> span
      %Cure.MetaAST.SourceInfo{whole: %Cure.Diagnostic.Span{} = span} -> span
      _ -> nil
    end
  end

  defp pattern_binder_span({_tag, _meta, children}, name) when is_list(children),
    do: Enum.find_value(children, &pattern_binder_span(&1, name))

  defp pattern_binder_span(list, name) when is_list(list),
    do: Enum.find_value(list, &pattern_binder_span(&1, name))

  defp pattern_binder_span(_other, _name), do: nil

  # `let x : T = e ⏎ rest`  ⟶  `{:let, Cure.Core.Grade.unrestricted(), T, e, rest}` with `x := e` in the context.
  defp bind_once_let(
         name,
         rhs_core,
         ty_core,
         ty_value,
         grade,
         rest,
         expected_core,
         names,
         ctx,
         env,
         opaque \\ false
       ) do
    rhs_value = Eval.eval(rhs_core, Context.env(ctx))

    # `extend_def/3`, not `extend/2`: the binder is definitionally its value (ζ),
    # so a later `SNat(k)` sees `k`'s concrete value — the one thing a β-redex
    # cannot give. A shadowing binder deeper in `rest` correctly shadows this de
    # Bruijn binder, so no capture guard is needed on this path.
    ctx1 =
      if opaque,
        do: Context.extend(ctx, ty_value),
        else: Context.extend_def(ctx, ty_value, rhs_value)

    names1 = [name | names]
    expected1 = Subst.shift(expected_core, 1, 0)

    with {:ok, body_core} <- elaborate_let_block(rest, expected1, names1, ctx1, env) do
      {:ok, {:let, grade, ty_core, rhs_core, body_core}}
    end
  end

  # `let x = eff  ⏎ rest`  where `eff : Effect(T)`  ⟶  `bind(eff, λ x:T. rest)`.
  #
  # The continuation binds the UNWRAPPED payload `x : T` as an OPAQUE binder
  # (`extend/2`, not `extend_def/3`): the effect's result is NOT definitionally
  # known — it is whatever the effect will produce at run time — so `x` must stay
  # a variable, unlike a pure `let` whose value is transparent (ζ).
  #
  # de Bruijn: `t_core` is the lambda's DOMAIN, well-formed OUTSIDE its own binder,
  # so it is reified at the current depth `Context.length(ctx)`. `rest` is the
  # lambda BODY, elaborated under one new binder (`ctx1`, `names1`), so the block's
  # expected type is shifted by one (`expected1`). The kernel re-checks the node.
  defp effectful_let_bind(name, rhs_core, payload_val, grade, rest, expected_core, names, ctx, env) do
    t_core = Quote.reify(payload_val, Context.length(ctx), Context.signature(ctx))
    ctx1 = Context.extend(ctx, payload_val)
    names1 = [name | names]
    expected1 = Subst.shift(expected_core, 1, 0)

    with {:ok, body_core} <- elaborate_let_block(rest, expected1, names1, ctx1, env) do
      {:ok, {:effect_bind, rhs_core, {:lam, grade, t_core, body_core}}}
    end
  end

  # `effect_bind` is inferred without a continuation result goal. A pure tuple
  # therefore cannot be inferred directly inside `effect_pure`, even after it
  # has been checked against the surrounding effect result. Bind the checked
  # payload with an ordinary Core let so the continuation infers `pure(var)`
  # from the let domain. The let is erased by the normal emitter and preserves
  # the single evaluation of the payload.
  defp effect_pure_for_bind(core, type_core, ctx) do
    case Kernel.infer(ctx, {:effect_pure, core}) do
      {:ok, _} ->
        {:effect_pure, core}

      {:error, _} ->
        {:let, Grade.unrestricted(), type_core, core, {:effect_pure, {:var, 0}}}
    end
  end

  # Free occurrences of surface variable `name` in the remaining statements.
  # Mirrors `subst_surface_var/3`'s traversal (which is likewise shadowing-blind;
  # the shadowing case is rejected before either is reached).
  defp count_surface_uses(list, name) when is_list(list),
    do: Enum.reduce(list, 0, &(count_surface_uses(&1, name) + &2))

  defp count_surface_uses({:variable, _meta, name}, name), do: 1

  # Bare local references retain the parser's nullary-call shape until name
  # resolution.  A uniquely visible local binder shadows any global with the
  # same spelling, so this is the same occurrence class as `:variable` for
  # capture-checked surface substitution.
  defp count_surface_uses({:function_call, meta, []}, name) when is_list(meta),
    do: if(Keyword.get(meta, :name) == name, do: 1, else: 0)

  defp count_surface_uses({_tag, _meta, children}, name) when is_list(children),
    do: Enum.reduce(children, 0, &(count_surface_uses(&1, name) + &2))

  defp count_surface_uses(_other, _name), do: 0

  # Surface-level scrutinee refinement (Lean `Cases.lean:219-227`): in a branch,
  # a VARIABLE scrutinee *is* the pattern, so free occurrences of its name in
  # the branch body are replaced by the pattern expression. Bails out — leaving
  # today's behavior, which the kernel re-check keeps sound — when the name does
  # not uniquely resolve to the scrutinee (an inner binding shadows it), when
  # the pattern itself rebinds the name, or when a nested match arm binds a name
  # that would shadow the scrutinee or capture a pattern var.
  defp refine_scrutinee_in_body(body_expr, {:var, i}, pattern, pattern_vars, names) do
    scrut_name = Enum.at(names, i)

    stripped = strip_named_implicits(pattern)

    if is_binary(scrut_name) and
         Enum.find_index(names, &(&1 == scrut_name)) == i and
         scrut_name not in pattern_vars and
         expressible_pattern?(stripped) and
         not binds_any?(body_expr, [scrut_name | pattern_vars]) do
      subst_surface_var(body_expr, scrut_name, stripped)
    else
      body_expr
    end
  end

  defp refine_scrutinee_in_body(body_expr, _scrut_term, _pattern, _pattern_vars, _names),
    do: body_expr

  # Can this branch pattern be rendered into TERM position? A wildcard `_` has
  # no value, so a pattern containing one (`[_ | _]`) is not expressible; the
  # surface scrutinee-refinement must be skipped for it (the scrutinee variable
  # stays in branch scope with its original type and the body checks against
  # that directly). Rendering `[_ | _]` as an expression resolved both `_`s to
  # the head element binder and mis-typed the tail slot.
  defp expressible_pattern?({:variable, _meta, "_"}), do: false

  defp expressible_pattern?({_tag, _meta, children}) when is_list(children),
    do: Enum.all?(children, &expressible_pattern?/1)

  defp expressible_pattern?(list) when is_list(list),
    do: Enum.all?(list, &expressible_pattern?/1)

  defp expressible_pattern?(_other), do: true

  defp subst_surface_var({:variable, _meta, name}, name, replacement), do: replacement

  defp subst_surface_var({:function_call, meta, []} = call, name, replacement) when is_list(meta) do
    if Keyword.get(meta, :name) == name, do: replacement, else: call
  end

  defp subst_surface_var({tag, meta, children}, name, replacement) when is_list(children),
    do:
      {tag, subst_surface_meta(meta, name, replacement), Enum.map(children, &subst_surface_var(&1, name, replacement))}

  defp subst_surface_var(other, _name, _replacement), do: other

  # A curried call `f(x)(y)` parses with its callee expression stashed in META
  # (`callee:`, parser.ex `parse_call`), NOT in the node's children — so the
  # generic child walk above would skip any variable inside the callee. Rewrite
  # the `:callee` sub-expression too, or a nested-match desugaring (or a `let`)
  # that renames `x` leaves the `x` inside `f(x)` untouched, and it reaches the
  # kernel as an undefined `{:global, :x}`.
  defp subst_surface_meta(meta, name, replacement) when is_list(meta) do
    case Keyword.fetch(meta, :callee) do
      {:ok, callee} ->
        Keyword.put(meta, :callee, subst_surface_var(callee, name, replacement))

      :error ->
        meta
    end
  end

  # Does any nested binder in the remaining statements bind one of `avoid`?
  #
  # This guards `elaborate_let_block`'s surface-substitution branch against CAPTURE.
  # Answering `false` sends the block down the substitution path, so a binder we fail
  # to see here silently rewrites a position it must not touch. Both binding forms
  # must be recognized:
  #
  #   * a match arm's pattern — which lives in the arm's META, not its children, so
  #     the generic child walk never sees it. Previously only a `{:function_call, …}`
  #     pattern's DIRECT variable arguments were collected, so a bare catch-all arm
  #     (`x -> S(x)`) and any nested/aliased pattern went unnoticed.
  #   * a lambda's parameters — likewise in META (`params:`), not children. A lambda
  #     shadowing an outer `let` name had its body rewritten, so `let x = Z()` turned
  #     `fn(x) -> S(x)` into `fn(x) -> S(Z())`: still well-typed, kernel-accepted, and
  #     computing the wrong value.
  #
  # Over-reporting merely costs the (safe) bind-once β-redex path; under-reporting is a
  # miscompilation. When in doubt, say true.
  defp binds_any?({:match_arm, meta, body}, avoid) do
    vars = meta |> Keyword.get(:pattern) |> pattern_binders()
    Enum.any?(vars, &(&1 in avoid)) or binds_any?(body, avoid)
  end

  defp binds_any?({:lambda, meta, children}, avoid) do
    params = for {:param, _pmeta, p} <- Keyword.get(meta, :params, []), do: p

    Enum.any?(params, &(&1 in avoid)) or
      children |> List.wrap() |> Enum.any?(&binds_any?(&1, avoid))
  end

  defp binds_any?({_tag, _meta, children}, avoid) when is_list(children),
    do: Enum.any?(children, &binds_any?(&1, avoid))

  defp binds_any?(list, avoid) when is_list(list),
    do: Enum.any?(list, &binds_any?(&1, avoid))

  defp binds_any?(_other, _avoid), do: false

  # Every name a pattern binds. In pattern position every `{:variable, _, v}` node IS a
  # binder, at any depth — nested constructor arguments, as-patterns, list/tuple
  # patterns. Constructor NAMES live in meta (`name:`), never as children, so this
  # never mistakes a constructor for a binder.
  defp pattern_binders({:variable, _meta, v}), do: [v]

  # `n: Int` (a UNION type member) or `rest: Bool | Atom` (a sub-union) — the bound
  # name is a bare STRING in the child list (`parser.ex` `maybe_wrap_as/2`'s `:colon`
  # clause), not a `{:variable, …}` node, so the generic clause below would silently
  # miss it: `Enum.flat_map(["n", type_ast], &pattern_binders/1)` finds nothing for the
  # bare string "n" and instead picks up names from `type_ast` (e.g. "Int"), which are
  # TYPE references, not binders. Without this clause, `binds_any?/2` — the capture
  # guard `elaborate_let_block` and every other surface-substitution site relies on —
  # silently fails to see a typed-pattern's shadowing, letting `let n = <check-only
  # rhs>` substitute straight through a later `n: Int -> n` arm and rewrite the INNER,
  # freshly-matched `n` into the OUTER let-bound expression.
  defp pattern_binders({:typed_pattern, _meta, [name, _type_ast]}) when is_binary(name),
    do: [name]

  defp pattern_binders({_tag, _meta, children}) when is_list(children),
    do: Enum.flat_map(children, &pattern_binders/1)

  defp pattern_binders(list) when is_list(list), do: Enum.flat_map(list, &pattern_binders/1)
  defp pattern_binders(_other), do: []

  # Wave-2 List sugar → ctor-call surface form (reuses all ctor machinery).
  #   []            -> Nil()
  #   [h | t]       -> Cons(h, t)              (meta carries `cons: true`)
  #   [e1, …, eN]   -> Cons(e1, Cons(…, Nil))  (right fold)
  # Recurses into sub-elements/sub-patterns so a list-of-lists desugars fully.
  # `m` threads the original node's line/col into the synthesized ctor calls.
  defp desugar_list({:list, m, []}), do: ctor_call("Nil", m, [])

  defp desugar_list({:list, m, [h, t]} = _node) do
    if Keyword.get(m, :cons, false) do
      ctor_call("Cons", m, [desugar_list(h), desugar_list(t)])
    else
      # a 2-element literal (no cons flag) folds like any other literal
      fold_list_literal([h, t], m)
    end
  end

  defp desugar_list({:list, m, elems}), do: fold_list_literal(elems, m)
  defp desugar_list(other), do: other

  defp check_list_literal(meta, elements, expected, element_type, names, ctx, env) do
    cons = resolve_ctor_key(env, :Cons)
    nil_ctor = resolve_ctor_key(env, :Nil)

    result =
      if Keyword.get(meta, :cons, false) and length(elements) == 2 do
        [head, tail] = elements

        with {:ok, head_core} <- check_list_element(head, element_type, names, ctx, env),
             {:ok, tail_core} <- elaborate_expr_checked(tail, expected, names, ctx, env) do
          {:ok, {:ctor, cons, [head_core, tail_core]}}
        end
      else
        check_list_elements(elements, element_type, names, ctx, env, cons, {:ctor, nil_ctor, []})
      end

    with {:ok, term} <- result,
         :ok <- Kernel.check(ctx, term, Eval.eval(expected, Context.env(ctx))) do
      {:ok, term}
    end
  end

  defp check_list_elements(elements, element_type, names, ctx, env, cons, tail) do
    Enum.reduce_while(Enum.reverse(elements), {:ok, tail}, fn element, {:ok, acc} ->
      case check_list_element(element, element_type, names, ctx, env) do
        {:ok, core} -> {:cont, {:ok, {:ctor, cons, [core, acc]}}}
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  defp check_list_element(element, expected, names, ctx, env) do
    case elaborate_expr_checked(element, expected, names, ctx, env) do
      {:ok, _core} = ok ->
        ok

      {:error, reason} ->
        # Constructor syntax checked against the wrong family reports
        # `:foreign_ctor` at the low-level boundary (`true` against `Int`, for
        # example). A homogeneous collection already knows this is a type
        # mismatch, not a missing name. Infer the authored element independently
        # to retain the established E093 collection diagnostic; if it is not
        # independently valid, preserve its original error.
        case elaborate_expr_typed(element, names, ctx, env) do
          {:ok, _term, actual_value} ->
            actual = Quote.reify(actual_value, Context.length(ctx), Context.signature(ctx))
            {:error, {:cannot_unify, actual, expected}}

          {:error, _} ->
            {:error, reason}
        end
    end
  end

  defp infer_list_literal(_meta, [], _names, _ctx, _env), do: :fallback

  defp infer_list_literal(meta, [head | rest], names, ctx, env) do
    case elaborate_expr_typed(head, names, ctx, env) do
      {:ok, head_core, element_value} ->
        element_type = Quote.reify(element_value, Context.length(ctx), env)
        family = Inductive.builtin(env, :list)

        if is_nil(family) do
          :fallback
        else
          expected = {:data, family, [element_type], []}
          cons = resolve_ctor_key(env, :Cons)

          with {:ok, tail_core} <- infer_list_tail(meta, rest, expected, element_type, names, ctx, env, cons),
               term = {:ctor, cons, [head_core, tail_core]} do
            {:ok, term, {:vdata, family, [element_value]}}
          end
        end

      {:error, _} ->
        # A blocked first element (notably an empty nested list) may be solved by
        # a later element through the constructor solver. Preserve that complete
        # path instead of turning the optimization into a new rejection.
        :fallback
    end
  end

  defp infer_list_tail(meta, rest, expected, element_type, names, ctx, env, cons) do
    if Keyword.get(meta, :cons, false) and length(rest) == 1 do
      elaborate_expr_checked(hd(rest), expected, names, ctx, env)
    else
      nil_ctor = resolve_ctor_key(env, :Nil)
      check_list_elements(rest, element_type, names, ctx, env, cons, {:ctor, nil_ctor, []})
    end
  end

  # Wadler comprehension translation, right-folded over the qualifier list. The
  # body of an exhausted qualifier list is a singleton `[e]`; a generator wraps
  # the remainder in a `flat_map` lambda; a filter guards it with `if … else []`.
  defp desugar_comprehension([], body, line), do: {:ok, {:list, [line: line], [body]}}

  defp desugar_comprehension([{:generator, _gm, [pat, source]} | rest], body, line) do
    with {:ok, param} <- generator_param(pat),
         {:ok, inner} <- desugar_comprehension(rest, body, line) do
      lambda = {:lambda, [params: [param], line: line], [inner]}
      {:ok, {:function_call, [name: "flat_map", line: line], [source, lambda]}}
    end
  end

  # A byte generator is an ordinary list generator after the standard-library
  # byte view has been applied. Sized/typed bit segments remain a deliberate
  # unsupported extension until their runtime representation exists.
  defp desugar_comprehension([{:binary_generator, _gm, [pattern, source]} | rest], body, line) do
    with {:ok, param} <- binary_generator_param(pattern),
         {:ok, inner} <- desugar_comprehension(rest, body, line) do
      lambda = {:lambda, [params: [param], line: line], [inner]}
      bytes = {:function_call, [name: "to_bytes", line: line], [source]}
      {:ok, {:function_call, [name: "flat_map", line: line], [bytes, lambda]}}
    end
  end

  defp desugar_comprehension([qual | rest], body, line) do
    cond_ast =
      case qual do
        {:filter, _fm, [c]} -> c
        other -> other
      end

    with {:ok, inner} <- desugar_comprehension(rest, body, line) do
      {:ok, {:conditional, [line: line], [cond_ast, inner, {:list, [line: line], []}]}}
    end
  end

  # A generator binds a single variable in this first port; a destructuring
  # generator (`{a, b} <- xs`) is rejected rather than silently mistyped.
  defp generator_param({:variable, _m, name}), do: {:ok, {:param, [], name}}
  defp generator_param(other), do: {:error, {:unsupported_comprehension_pattern, other}}

  defp binary_generator_param({:literal, meta, [{:bin_segment, segment_meta, [pattern]}]}) do
    if Keyword.get(meta, :subtype) == :bytes and
         is_nil(Keyword.get(segment_meta, :size)) and
         is_nil(Keyword.get(segment_meta, :type)) do
      generator_param(pattern)
    else
      {:error, {:unsupported_binary_generator_pattern, pattern}}
    end
  end

  defp binary_generator_param(pattern),
    do: {:error, {:unsupported_binary_generator_pattern, pattern}}

  # `%{k: v, …}` → nested `Std.Map.put(k, v, …)` over `Std.Map.new()`. `%{}`
  # folds to a bare `new()`. Shared by the typed and checked map clauses.
  defp desugar_map(pairs, line) do
    Enum.reduce(Enum.reverse(pairs), {:function_call, [name: "new", line: line], []}, fn
      {:pair, _pm, [key, value]}, acc ->
        {:function_call, [name: "put", line: line], [key, value, acc]}
    end)
  end

  # A `match` whose arms are map patterns cannot go through the constructor-match
  # machinery (an Erlang map is not a Cure inductive). Map matching is OPEN — keys
  # absent from the pattern are ignored — so it desugars to `has_key`-guarded
  # conditionals over `Std.Map`, exactly the shape a hand-written lookup takes:
  #
  #   match m
  #     %{a: v, tag: :hit} -> body
  #     _                  -> default
  #
  #   ⇒ if has_key(:a, m) and has_key(:tag, m) and get(:tag, m) == :hit
  #        then (let v = get(:a, m); body)
  #        else default
  #
  # Because matching is open it is non-exhaustive, so the arm list MUST end in a
  # wildcard/variable default. Value positions are variable binders, `_`, or
  # literals (an equality guard). The enclosing module must `use Std.Map` so the
  # emitted `has_key`/`get` resolve, like map literals.
  def map_match_arms?(arms) do
    Enum.any?(arms, fn
      {:match_arm, meta, _body} when is_list(meta) ->
        match?({:map, _m, _pairs}, Keyword.get(meta, :pattern))

      _ ->
        false
    end)
  end

  # A binary pattern arm is a `:bytes` literal used as a match pattern.
  def binary_match_arms?(arms) do
    Enum.any?(arms, fn
      {:match_arm, meta, _body} when is_list(meta) ->
        case Keyword.get(meta, :pattern) do
          {:literal, lmeta, segs} when is_list(lmeta) and is_list(segs) ->
            Keyword.get(lmeta, :subtype) == :bytes

          _ ->
            false
        end

      _ ->
        false
    end)
  end

  # Map and byte-binary patterns are not Cure inductives, so a `match` carrying
  # them desugars (surface → surface) to guarded conditionals rather than going
  # through the constructor-match machinery. Both entry-point modes share this.
  def special_match_arms?(arms), do: map_match_arms?(arms) or binary_match_arms?(arms)

  def desugar_special_match(scrut, arms, line) do
    cond do
      map_match_arms?(arms) -> desugar_map_match_once(scrut, arms, line)
      binary_match_arms?(arms) -> desugar_binary_arms(scrut, arms, line)
    end
  end

  def desugar_map_match(scrut, arms, line), do: desugar_map_match_once(scrut, arms, line)

  # `has_key` and `get` both inspect the map scrutinee. Repeating an arbitrary
  # dependent expression beneath both helpers can make implicit insertion solve
  # a projection metavariable under a helper-local Π binder. Bind a non-variable
  # scrutinee once, opaquely, before building those calls. The emitted Core let
  # still evaluates the expression once; opacity only prevents ζ-reduction while
  # elaborating the let body.
  defp desugar_map_match_once({:variable, _meta, _name} = scrut, arms, line),
    do: desugar_map_arms(scrut, arms, line)

  defp desugar_map_match_once(scrut, arms, line) do
    name = "$map_scrutinee_" <> fresh_tag()
    variable = {:variable, [], name}

    with {:ok, body} <- desugar_map_arms(variable, arms, line) do
      binding = {:assignment, [let: true, opaque: true, line: line], [variable, scrut]}
      {:ok, {:block, [line: line], [binding, body]}}
    end
  end

  # A wildcard/variable arm terminates the chain: `_` yields its body directly, a
  # named binder binds the whole scrutinee first.
  defp desugar_map_arms(_scrut, [], _line), do: {:error, {:map_match_needs_default}}

  defp desugar_map_arms(scrut, [{:match_arm, meta, [body]} | rest], line) do
    case Keyword.get(meta, :pattern) do
      {:map, _mm, pairs} ->
        with {:ok, presence, value_eqs, binds, nested} <- map_arm_guard_binds(scrut, pairs, line),
             {:ok, else_expr} <- desugar_map_arms(scrut, rest, line) do
          # Cure's `and` is strict, so a value `get` must never run on an absent
          # key: gate all `get`s behind the (total) presence guard structurally.
          # Only once every listed key is present are the value-equality checks
          # and the binding `get`s evaluated.
          matched_body =
            Enum.reduce(Enum.reverse(nested), body, fn {value, pattern}, success ->
              {:pattern_match, [line: line],
               [
                 value,
                 {:match_arm, [pattern: pattern], [success]},
                 {:match_arm, [pattern: {:variable, [], "_"}], [else_expr]}
               ]}
            end)

          then_body =
            if binds == [],
              do: matched_body,
              else: {:block, [line: line], binds ++ [matched_body]}

          inner =
            case value_eqs do
              [] -> then_body
              _ -> {:conditional, [line: line], [conjoin(value_eqs, line), then_body, else_expr]}
            end

          {:ok, {:conditional, [line: line], [conjoin(presence, line), inner, else_expr]}}
        end

      {:variable, _vm, "_"} ->
        {:ok, body}

      {:variable, vm, name} ->
        bind = {:assignment, [let: true, line: line], [{:variable, vm, name}, scrut]}
        {:ok, {:block, [line: line], [bind, body]}}

      other ->
        {:error, {:unsupported_map_match_arm, other}}
    end
  end

  # Fold a map pattern's pairs into (a) presence guards — every listed key must be
  # present (`has_key`, total), (b) value-equality guards for literal positions
  # (`get(k) == lit`, evaluated only after presence holds), and (c) the `let`
  # bindings for variable value positions.
  defp map_arm_guard_binds(scrut, pairs, line) do
    Enum.reduce_while(pairs, {:ok, [], [], [], []}, fn
      {:pair, _pm, [{:literal, kmeta, key}, valpat]}, {:ok, presence, value_eqs, binds, nested}
      when is_atom(key) ->
        if Keyword.get(kmeta, :subtype) in [:symbol, :atom] do
          key_lit = {:literal, [subtype: :symbol], key}
          present = mk_call("has_key", [key_lit, scrut], line)

          case valpat do
            {:variable, _vm, "_"} ->
              {:cont, {:ok, presence ++ [present], value_eqs, binds, nested}}

            {:variable, _vm, _name} ->
              bind =
                {:assignment, [let: true, line: line], [valpat, mk_call("get", [key_lit, scrut], line)]}

              {:cont, {:ok, presence ++ [present], value_eqs, binds ++ [bind], nested}}

            {:literal, _lm, _lv} = lit ->
              eq =
                {:binary_op, [category: :comparison, operator: :==, line: line],
                 [mk_call("get", [key_lit, scrut], line), lit]}

              {:cont, {:ok, presence ++ [present], value_eqs ++ [eq], binds, nested}}

            other ->
              value = mk_call("get", [key_lit, scrut], line)

              {:cont, {:ok, presence ++ [present], value_eqs, binds, nested ++ [{value, other}]}}
          end
        else
          {:halt, {:error, {:unsupported_map_key_pattern, key}}}
        end

      {:pair, _pm, [other_key, _v]}, _acc ->
        {:halt, {:error, {:unsupported_map_key_pattern, other_key}}}
    end)
    |> case do
      {:ok, presence, value_eqs, binds, nested} ->
        {:ok, presence, value_eqs, binds, nested}

      {:error, _} = e ->
        e
    end
  end

  # An empty pattern `%{}` matches any map, so an absent guard is `true`.
  defp conjoin([], _line), do: {:literal, [subtype: :boolean], true}
  defp conjoin([g], _line), do: g

  defp conjoin([g | rest], line),
    do: {:binary_op, [category: :boolean, operator: :and, line: line], [g, conjoin(rest, line)]}

  defp mk_call(name, args, line), do: {:function_call, [name: name, line: line], args}

  # Byte-binary patterns, the destructuring twin of `desugar_map_arms`. A match
  # whose arms are `<<…>>` patterns desugars to `byte_size`-guarded conditionals
  # over `Std.Binary`: the length guard (`==` for a fixed pattern, `>=` when a
  # `rest::binary` tail is present) gates the byte reads, then literal byte
  # positions add `byte_at(b, i) == lit` guards and variable positions bind
  # `byte_at(b, i)` / `drop_bytes(b, k)`. Open-ended, so a trailing default arm is
  # required. Sized/typed segments (`x::float`) are rejected, not mislowered.
  defp desugar_binary_arms(_scrut, [], _line), do: {:error, {:binary_match_needs_default}}

  defp desugar_binary_arms(scrut, [{:match_arm, meta, [body]} | rest], line) do
    case Keyword.get(meta, :pattern) do
      {:literal, lmeta, segs} = pat ->
        if Keyword.get(lmeta, :subtype) == :bytes do
          with {:ok, length_guard, value_guards, binds} <- binary_arm_guard_binds(scrut, segs, line),
               {:ok, else_expr} <- desugar_binary_arms(scrut, rest, line) do
            then_body = if binds == [], do: body, else: {:block, [line: line], binds ++ [body]}

            inner =
              case value_guards do
                [] -> then_body
                _ -> {:conditional, [line: line], [conjoin(value_guards, line), then_body, else_expr]}
              end

            {:ok, {:conditional, [line: line], [length_guard, inner, else_expr]}}
          end
        else
          {:error, {:unsupported_binary_match_arm, pat}}
        end

      {:variable, _vm, "_"} ->
        {:ok, body}

      {:variable, vm, name} ->
        bind = {:assignment, [let: true, line: line], [{:variable, vm, name}, scrut]}
        {:ok, {:block, [line: line], [bind, body]}}

      other ->
        {:error, {:unsupported_binary_match_arm, other}}
    end
  end

  # Split a byte pattern's segments into (a) the length guard, (b) literal-byte
  # equality guards, and (c) the variable/tail `let` bindings. The optional
  # `rest::binary` tail must come last; any other typed segment is rejected.
  defp binary_arm_guard_binds(scrut, segs, line) do
    {fixed, tail} = split_binary_tail(segs)

    with {:ok, value_guards, binds} <- fixed_byte_guards(scrut, fixed, line),
         {:ok, tail_binds} <- tail_bind(scrut, tail, length(fixed), line) do
      n = {:literal, [subtype: :integer, line: line], length(fixed)}
      size = mk_call("byte_size", [scrut], line)

      op = if tail == :none, do: :==, else: :>=
      length_guard = {:binary_op, [category: :comparison, operator: op, line: line], [size, n]}

      {:ok, length_guard, value_guards, binds ++ tail_binds}
    end
  end

  # The last segment is a tail iff it is an unsized binary-family segment.
  defp split_binary_tail(segs) do
    case List.last(segs) do
      {:bin_segment, meta, [v]} = seg ->
        if Keyword.get(meta, :type) in [:binary, :bytes, :bitstring, :bits] and
             is_nil(Keyword.get(meta, :size)) do
          {Enum.drop(segs, -1), {:tail, v, seg}}
        else
          {segs, :none}
        end

      _ ->
        {segs, :none}
    end
  end

  defp fixed_byte_guards(scrut, segs, line) do
    segs
    |> Enum.with_index()
    |> Enum.reduce_while({:ok, [], []}, fn {seg, i}, {:ok, guards, binds} ->
      idx = {:literal, [subtype: :integer, line: line], i}

      case seg do
        {:bin_segment, _sm, [{:variable, _vm, "_"}]} ->
          {:cont, {:ok, guards, binds}}

        {:bin_segment, _sm, [{:variable, _vm, _name} = v]} ->
          bind = {:assignment, [let: true, line: line], [v, mk_call("byte_at", [scrut, idx], line)]}
          {:cont, {:ok, guards, binds ++ [bind]}}

        {:bin_segment, _sm, [{:literal, _lm, byteval} = lit]} when is_integer(byteval) ->
          eq =
            {:binary_op, [category: :comparison, operator: :==, line: line],
             [mk_call("byte_at", [scrut, idx], line), lit]}

          {:cont, {:ok, guards ++ [eq], binds}}

        other ->
          {:halt, {:error, {:unsupported_binary_segment, other}}}
      end
    end)
  end

  defp tail_bind(_scrut, :none, _n, _line), do: {:ok, []}

  defp tail_bind(scrut, {:tail, tailvar, seg}, n, line) do
    case tailvar do
      {:variable, _tm, "_"} ->
        {:ok, []}

      {:variable, _tm, _name} ->
        nlit = {:literal, [subtype: :integer, line: line], n}
        {:ok, [{:assignment, [let: true, line: line], [tailvar, mk_call("drop_bytes", [scrut, nlit], line)]}]}

      _ ->
        {:error, {:unsupported_binary_segment, seg}}
    end
  end

  # `<<b1, b2, …>>` → `Std.Binary.of_bytes([b1, b2, …])`: a byte binary literal is
  # a list of byte values packed into a BEAM binary. Only default 8-bit-integer
  # segments are supported here; a typed segment (`x::float`, `x::binary`) is a
  # deferred rich-bit-syntax case and is rejected rather than mislowered. The
  # module must `use Std.Binary`.
  # `"a#{e}b"` → `Std.String.concat("a", Std.String.concat(e, "b"))`: a right fold
  # over the segments. Literal chunks stay `:string` literals (each desugars to a
  # nominal `String`); holes are the segment expressions unchanged, so a hole is
  # elaborated against `concat`'s `String` parameter — a String hole checks, a
  # non-String hole is a type error (Show-based conversion is #21).
  #
  # The fold names `Std.String.concat` by CANONICAL KEY, for the same reason
  # `desugar_string/2` names the `String` constructor that way: this call is
  # written by the compiler, not by the module the literal appears in, and that
  # module never imported `Std.String`. It went through `Std.Binary.str_concat`
  # while `String` was a typealias for `List(Char)`; once `String` became nominal
  # that made every interpolation ill-typed, because the literal chunks are
  # `String` and `str_concat` is a `List(Char)` operation. Concatenation has one
  # canonical owner and interpolation must route through it.
  defp desugar_interpolation(segments, line) do
    case Enum.reverse(segments) do
      [] ->
        {:literal, [subtype: :string, line: line], ""}

      [last | rest] ->
        concat = Atom.to_string(Cure.Elab.Name.qualify("Std.String", :concat))
        Enum.reduce(rest, last, fn seg, acc -> mk_call(concat, [seg, acc], line) end)
    end
  end

  # Rich bit-syntax specifiers (`::16`, `::float`, `::size(n)`, unit/signedness/
  # endianness) live in the segment meta after parsing. `of_bytes` packs a list
  # of 8-bit bytes and cannot express any of them, so a sized/typed segment is
  # REJECTED here rather than silently mislowered — dropping a `::16` size would
  # feed a >255 value to `list_to_binary` and crash at runtime. Rich bit-syntax
  # construction is a deferred value-surface case in the dependent pipeline.
  @rich_segment_keys [:size, :type, :unit, :signedness, :endianness]

  def desugar_bytes(segments, line) do
    Enum.reduce_while(segments, {:ok, []}, fn
      {:bin_segment, sm, [expr]} = seg, {:ok, acc} ->
        cond do
          Enum.any?(@rich_segment_keys, &(Keyword.get(sm, &1) != nil)) ->
            {:halt, {:error, {:unsupported_binary_segment, seg}}}

          true ->
            {:cont, {:ok, acc ++ [expr]}}
        end

      other, _acc ->
        {:halt, {:error, {:unsupported_binary_segment, other}}}
    end)
    |> case do
      {:ok, values} ->
        {:ok, mk_call("of_bytes", [{:list, [line: line], values}], line)}

      {:error, _} = e ->
        e
    end
  end

  # A source string constructs the nominal `Std.String` record around its decoded
  # character list. The constructor is named by its CANONICAL KEY, not by the
  # qualified surface spelling `Std.String.String`: this call is written by the
  # compiler, not by the module the literal appears in, and that module never
  # imported `Std.String`. A surface spelling has to survive qualified-module
  # availability lookup, which it cannot in a module that made no such import —
  # it falls through to a verbatim `{:global, :"Std.String.String"}` that no
  # environment defines. The key still carries the owner, so it keeps the
  # collision-avoidance the qualified spelling was chosen for (a user's
  # `Std.Json.String` is a different key).
  defp desugar_string(value, meta) when is_binary(value) do
    name = Atom.to_string(Cure.Elab.Name.qualify("Std.String", :String))
    {:function_call, [name: name] ++ generated_meta(meta), [desugar_string_characters(value, meta)]}
  end

  defp desugar_string_characters(value, meta, literal_meta \\ []) when is_binary(value) do
    loc = generated_meta(meta)

    chars =
      Enum.map(String.to_charlist(value), fn cp ->
        {:literal, [subtype: :char] ++ literal_meta ++ loc, cp}
      end)

    {:list, meta, chars}
  end

  defp fold_list_literal(elems, m) do
    Enum.reduce(Enum.reverse(elems), ctor_call("Nil", m, []), fn e, acc ->
      ctor_call("Cons", m, [desugar_list(e), acc])
    end)
  end

  defp ctor_call(name, m, args),
    do: {:function_call, [name: name] ++ generated_meta(m), args}

  defp generated_meta(meta) when is_list(meta) do
    Keyword.take(meta, [
      :line,
      :col,
      :column,
      :source_info,
      :provenance,
      :source_provenance,
      :expansion_provenance
    ])
  end

  defp generated_meta(_meta), do: []

  # Rewrite `:list` patterns in each match arm to the ctor-call form before any
  # downstream pattern pass runs (the pattern-position half of desugar_list/1).
  defp desugar_list_patterns(arms) do
    Enum.map(arms, fn
      {:match_arm, meta, body} ->
        pattern = meta |> Keyword.fetch!(:pattern) |> desugar_pattern_lists()
        {:match_arm, Keyword.put(meta, :pattern, pattern), body}

      other ->
        other
    end)
  end

  # List sugar may occur at any depth in a constructor pattern. Rewriting only
  # a top-level `:list` leaves e.g. `Parsed(_, ['*' | _])` opaque to the pattern
  # matrix: it sees neither a constructor nor a variable in that column and
  # drops the row while constructing the fallback branch. Normalize recursively
  # so every downstream pattern pass receives the same Cons/Nil representation.
  defp desugar_pattern_lists({:list, _, _} = pattern), do: desugar_list(pattern)

  defp desugar_pattern_lists({:function_call, meta, args}) do
    {:function_call, meta, Enum.map(args, &desugar_pattern_lists/1)}
  end

  # A tuple pattern is a structural pattern container too. Without descending
  # here, list sugar nested in `%[[head | tail], other]` reaches the tuple
  # matrix as an opaque `:list` node. The matrix then rejects a pattern that the
  # equivalent pair of nested matches accepts. Normalize tuple elements before
  # tuple projection so both surfaces share the constructor-pattern path.
  defp desugar_pattern_lists({:tuple, meta, elements}) do
    {:tuple, meta, Enum.map(elements, &desugar_pattern_lists/1)}
  end

  defp desugar_pattern_lists({:named_implicit_pat, meta, children}) do
    {:named_implicit_pat, meta, Enum.map(children, &desugar_pattern_lists/1)}
  end

  defp desugar_pattern_lists(pattern), do: pattern

  # Typed constructor payloads (`Some(value: Int)`) are a surface ascription on
  # an ordinary constructor binder. Remove the annotation before the existing
  # pattern matrix, but retain its type AST in arm metadata for the validation
  # pass in `elaborate_match/6`. Keeping this generic avoids teaching any macro
  # about the elaborator's constructor representation.
  defp desugar_typed_constructor_args(arms) do
    Enum.map(arms, fn
      {:match_arm, meta, body} = arm ->
        case Keyword.get(meta, :pattern) do
          {:function_call, pattern_meta, args} ->
            {args, annotations} = clean_typed_constructor_args(args, 0, [], [])

            meta =
              if annotations == [],
                do: meta,
                else: Keyword.put(meta, :typed_pattern_types, Enum.reverse(annotations))

            {:match_arm, Keyword.put(meta, :pattern, {:function_call, pattern_meta, args}), body}

          _ ->
            arm
        end

      other ->
        other
    end)
  end

  defp clean_typed_constructor_args([], _index, args, annotations), do: {Enum.reverse(args), annotations}

  defp clean_typed_constructor_args([{:typed_pattern, pattern_meta, [name, type_ast]} | rest], index, args, annotations)
       when is_binary(name) do
    clean_typed_constructor_args(
      rest,
      index + 1,
      [{:variable, pattern_meta, name} | args],
      [{index, name, type_ast, pattern_meta} | annotations]
    )
  end

  defp clean_typed_constructor_args([arg | rest], index, args, annotations) do
    clean_typed_constructor_args(rest, index + 1, [arg | args], annotations)
  end

  defp validate_typed_pattern_annotations(arms, {:vdata, dname, combined_vals}, names, ctx, env) do
    pc = Inductive.param_count(env, dname)
    {param_vals, _idx_vals} = Enum.split(combined_vals, pc)

    Enum.reduce_while(arms, :ok, fn
      {:match_arm, meta, _body}, :ok ->
        case Keyword.get(meta, :typed_pattern_types, []) do
          [] ->
            {:cont, :ok}

          annotations ->
            pattern = Keyword.fetch!(meta, :pattern)

            with {:ok, {cname, _pattern_vars}} <- constructor_pattern(pattern),
                 %{args: telescope, quantities: quantities} <- Inductive.get_ctor(env, cname),
                 branch_ctx <- extend_context(ctx, telescope, param_vals),
                 :ok <-
                   validate_constructor_payload_types(
                     annotations,
                     telescope,
                     quantities,
                     branch_ctx,
                     names,
                     env,
                     cname,
                     pattern
                   ) do
              {:cont, :ok}
            else
              {:error, _} = error -> {:halt, error}
              nil -> {:halt, {:error, {:unknown_constructor, cname_from_pattern(pattern)}}}
            end
        end

      _arm, :ok ->
        {:cont, :ok}
    end)
    |> case do
      :ok -> :ok
      {:error, _} = error -> error
    end
  end

  defp validate_typed_pattern_annotations(_arms, _scrut_type, _names, _ctx, _env), do: :ok

  defp validate_constructor_payload_types(
         annotations,
         telescope,
         quantities,
         branch_ctx,
         names,
         env,
         constructor,
         pattern
       ) do
    present_positions =
      quantities
      |> Enum.with_index()
      |> Enum.filter(fn {quantity, _index} -> Grade.present?(quantity) end)
      |> Enum.map(&elem(&1, 1))

    Enum.reduce_while(annotations, :ok, fn {position, binder, type_ast, pattern_meta}, :ok ->
      case Enum.at(present_positions, position) do
        nil ->
          {:halt,
           typed_pattern_arity_error(
             position,
             binder,
             type_ast,
             pattern_meta,
             constructor,
             pattern,
             length(present_positions)
           )}

        telescope_position ->
          branch_index = length(telescope) - 1 - telescope_position
          actual = Context.lookup(branch_ctx, branch_index)

          case elaborate_type(type_ast, names, env) do
            {:ok, annotated} when not is_nil(actual) ->
              actual_term = Quote.reify(actual, Context.length(branch_ctx))
              expected_term = Subst.shift(annotated, length(telescope), 0)

              if Conv.conv?(
                   expected_term,
                   actual_term,
                   Context.env(branch_ctx),
                   Context.length(branch_ctx),
                   Context.signature(branch_ctx)
                 ) do
                {:cont, :ok}
              else
                {:halt,
                 typed_pattern_annotation_error(
                   {:typed_pattern_type_mismatch, type_ast},
                   type_ast,
                   position,
                   binder,
                   pattern_meta,
                   constructor,
                   pattern,
                   actual_term,
                   expected_term
                 )}
              end

            {:ok, annotated} ->
              {:halt,
               typed_pattern_annotation_error(
                 {:typed_pattern_type_mismatch, type_ast},
                 type_ast,
                 position,
                 binder,
                 pattern_meta,
                 constructor,
                 pattern,
                 nil,
                 annotated
               )}

            {:error, reason} ->
              {:halt,
               typed_pattern_annotation_error(
                 {:typed_pattern_type_error, reason},
                 type_ast,
                 position,
                 binder,
                 pattern_meta,
                 constructor,
                 pattern,
                 nil,
                 nil
               )}
          end
      end
    end)
  end

  defp typed_pattern_arity_error(position, binder, type_ast, pattern_meta, constructor, pattern, visible_arity) do
    pattern_info = Cure.MetaAST.Metadata.source_info(pattern_meta)
    constructor_info = pattern |> elem(1) |> Cure.MetaAST.Metadata.source_info()
    supplied_arity = pattern |> elem(2) |> length()
    annotation_span = surface_expression_span(type_ast)
    typed_pattern_span = rewrite_span(pattern_info && pattern_info.whole, annotation_span)
    span = typed_pattern_span || (constructor_info && constructor_info.whole)

    {:error,
     {:source_context, {:typed_pattern_arity, position},
      %{
        line: span && span.start_line,
        column: span && span.start_column,
        length: span && max(1, span.end_byte - span.start_byte),
        span: span,
        typed_pattern_span: typed_pattern_span,
        binder_span: pattern_info && pattern_info.name,
        annotation_span: annotation_span,
        constructor_pattern_span: constructor_info && constructor_info.whole,
        constructor_name_span: constructor_info && (constructor_info.name || constructor_info.callee),
        constructor: constructor,
        binder: binder,
        argument_index: position,
        supplied_arity: supplied_arity,
        visible_arity: visible_arity,
        checking: :pattern,
        expression_category: :pattern,
        expectation_origin: :pattern
      }}}
  end

  defp typed_pattern_annotation_error(
         reason,
         type_ast,
         position,
         binder,
         pattern_meta,
         constructor,
         pattern,
         actual_type,
         annotated_type
       ) do
    case surface_expression_span(type_ast) do
      %Cure.Diagnostic.Span{} = span ->
        pattern_info = Cure.MetaAST.Metadata.source_info(pattern_meta)
        constructor_info = pattern |> elem(1) |> Cure.MetaAST.Metadata.source_info()

        {:error,
         {:source_context, reason,
          %{
            line: span.start_line,
            column: span.start_column,
            length: max(1, span.end_byte - span.start_byte),
            span: span,
            expectation_span: span,
            checking: :pattern,
            expression_category: :pattern,
            expectation_origin: :pattern,
            argument_index: position,
            binder: binder,
            typed_pattern_span: pattern_info && pattern_info.whole,
            binder_span: pattern_info && pattern_info.name,
            annotation_span: pattern_info && pattern_info.annotation,
            constructor_pattern_span: constructor_info && constructor_info.whole,
            constructor_name_span: constructor_info && constructor_info.name,
            constructor: constructor,
            annotated_type: annotated_type,
            field_type: actual_type
          }}}

      _ ->
        {:error, reason}
    end
  end

  defp cname_from_pattern({:function_call, meta, _args}), do: Keyword.get(meta, :name)
  defp cname_from_pattern(_pattern), do: nil

  # A constructor branch binds every Core field, including a surface `_`.
  # Anonymous fields must stay unavailable to authored code, but they still need
  # an internal name when the matched value is reconstructed in a dependent
  # branch (`project(scrutinee)` must reduce after `match scrutinee`).  Leaving
  # the literal `_` in that reconstruction is ambiguous: expression elaboration
  # can resolve repeated wildcards to an unrelated field, so the old refiner
  # conservatively kept the scrutinee opaque.  Give each positional wildcard a
  # collision-proof branch-only name instead.  The user's body is untouched;
  # only the compiler's pattern scope and reconstructed constructor see it.
  defp internalize_branch_wildcards({:function_call, meta, args}) do
    constructor = Keyword.get(meta, :name, "constructor")

    {args, _position} =
      Enum.map_reduce(args, 0, fn
        argument, position when is_tuple(argument) ->
          if named_implicit_arg?(argument) do
            {argument, position}
          else
            replacement =
              case argument do
                {:variable, variable_meta, "_"} ->
                  {:variable, variable_meta, "$wildcard_#{constructor}_#{position}"}

                other ->
                  other
              end

            {replacement, position + 1}
          end

        argument, position ->
          {argument, position + 1}
      end)

    {:function_call, meta, args}
  end

  defp internalize_branch_wildcards(pattern), do: pattern

  defp constructor_pattern({:function_call, meta, args}) do
    cname = meta |> Keyword.fetch!(:name) |> String.to_atom()

    # A named-implicit dot pattern `{k = …}` annotates an erased index by name; it
    # binds nothing at runtime and is check-and-discarded in the branch path, so
    # it is partitioned out here. What REMAINS are the positional (present-arg)
    # sub-patterns, which — as today — must each be a bare variable. A NESTED
    # constructor/literal sub-pattern (`S(S(m))`, `C(Z(),y)`) still needs decision-
    # tree lowering (parity #3), so report a clean error on any non-variable
    # positional arg.
    positional = Enum.reject(args, &named_implicit_arg?/1)

    if Enum.all?(positional, &match?({:variable, _m, _v}, &1)) do
      vars = Enum.map(positional, fn {:variable, _meta, v} -> v end)

      # Patterns must be linear: a repeated binder (`C(x, x)`) is not a valid
      # pattern — the body's reference is ambiguous and equality between two
      # positions must be witnessed by a proof, not a repeated name (Idris/Agda).
      # The bare wildcard `_` binds nothing, so it may repeat.
      non_wild = Enum.reject(vars, &(&1 == "_"))

      case non_wild -- Enum.uniq(non_wild) do
        [] -> {:ok, {cname, vars}}
        [dup | _] -> {:error, {:nonlinear_pattern, String.to_atom(dup)}}
      end
    else
      offending = Enum.find(positional, &(not match?({:variable, _meta, _name}, &1)))

      {:error,
       {:unsupported_pattern,
        %{
          reason: :unlowered_nested_constructor_argument,
          shape: pattern_shape(offending),
          span: surface_expression_span(offending)
        }}}
    end
  end

  defp constructor_pattern(other), do: unsupported_pattern_error(other)

  defp unsupported_pattern_error(pattern) do
    reason = {:unsupported_pattern, pattern_shape(pattern)}

    span =
      case pattern do
        {:range, meta, _children} when is_list(meta) ->
          case Cure.MetaAST.Metadata.source_info(meta) do
            %Cure.MetaAST.SourceInfo{operator: %Cure.Diagnostic.Span{} = operator} -> operator
            %Cure.MetaAST.SourceInfo{whole: %Cure.Diagnostic.Span{} = whole} -> whole
            _ -> nil
          end

        _ ->
          surface_expression_span(pattern)
      end

    case span do
      %Cure.Diagnostic.Span{} ->
        {:error,
         {:source_context, reason,
          %{
            line: span.start_line,
            column: span.start_column,
            length: max(1, span.end_byte - span.start_byte),
            span: span,
            checking: :pattern,
            expression_category: :pattern,
            expectation_origin: :pattern
          }}}

      _ ->
        {:error, reason}
    end
  end

  defp unknown_pattern_constructor_error(pattern, cname, env, family) do
    span =
      case pattern do
        {:function_call, meta, _args} when is_list(meta) ->
          case Cure.MetaAST.Metadata.source_info(meta) do
            %Cure.MetaAST.SourceInfo{callee: %Cure.Diagnostic.Span{} = callee} -> callee
            %Cure.MetaAST.SourceInfo{name: %Cure.Diagnostic.Span{} = name} -> name
            %Cure.MetaAST.SourceInfo{whole: %Cure.Diagnostic.Span{} = whole} -> whole
            _ -> nil
          end

        _ ->
          surface_expression_span(pattern)
      end

    candidates =
      env
      |> Inductive.ctors_of(family)
      |> Enum.map(fn ctor ->
        {owner, name} = Cure.Elab.Name.split(ctor.name)

        %{
          id: ctor.name,
          candidate_id: ctor.name,
          name: name,
          namespace: :constructor,
          owner: owner || family,
          arity: Enum.count(Map.get(ctor, :plicities, []), &(&1 == :explicit)),
          imported: true,
          origin: :matched_type
        }
      end)

    context = %{
      span: span,
      checking: :pattern,
      expectation_origin: :pattern,
      expression_category: :pattern,
      name_candidates: candidates,
      name_arity: pattern_argument_count(pattern)
    }

    context =
      case span do
        %Cure.Diagnostic.Span{} ->
          Map.merge(context, %{
            line: span.start_line,
            column: span.start_column,
            length: max(1, span.end_byte - span.start_byte)
          })

        _ ->
          context
      end

    {:error, {:source_context, {:unknown_pattern_constructor, cname}, context}}
  end

  defp pattern_argument_count({:function_call, _meta, args}) when is_list(args), do: length(args)
  defp pattern_argument_count(_pattern), do: nil

  defp named_implicit_arg?({:named_implicit_pat, _m, _children}), do: true
  defp named_implicit_arg?(_), do: false

  # A pattern's value-reconstruction (spliced into a branch body by
  # `desugar_as_patterns` and `refine_scrutinee_in_body`) must carry no
  # `{:named_implicit_pat,…}` annotation nodes — they are pattern-only
  # syntax, invalid in expression position (spec 2026-07-08 §2.2). The
  # positional-only form is what Idris/Lean substitute for the scrutinee.
  # Recursive: nested constructor sub-patterns are cleaned too.
  defp strip_named_implicits({:function_call, m, args}) do
    positional =
      args
      |> Enum.reject(&named_implicit_arg?/1)
      |> Enum.map(&strip_named_implicits/1)

    {:function_call, m, positional}
  end

  defp strip_named_implicits(other), do: other

  # The named-implicit annotations of a constructor pattern, as `{name, inner}`
  # pairs (empty for a pattern without any). Used by `elaborate_matched_branch`
  # to run the forced-index convertibility check.
  defp constructor_named_implicits({:function_call, constructor_meta, args}),
    do:
      for(
        {:named_implicit_pat, m, [inner]} <- args,
        do: {Keyword.get(m, :name), inner, m, constructor_meta}
      )

  defp constructor_named_implicits(_), do: []

  # Split a pattern's named implicits per spec 2026-07-08 §2.3. A bare variable
  # binds an unforced position, and also binds a FORCED relevant implicit: the
  # latter is retained at runtime, so hiding it merely because the result index
  # also determines it would make `{k : T}` less usable than an ordinary field.
  # Forced erased positions remain check-only, preserving the quantity-0 rule.
  defp split_named_implicits(pattern, subst, arity, telescope, quantities) do
    pattern
    |> constructor_named_implicits()
    |> Enum.split_with(fn {name, inner, _named_meta, _constructor_meta} ->
      position = Enum.find_index(telescope, fn {n, _t} -> n == String.to_atom(name) end)

      match?({:variable, _, _}, inner) and position != nil and
        (named_implicit_forced_value(name, subst, arity, telescope) == :error or
           not Grade.erased?(Enum.at(quantities, position)))
    end)
  end

  defp pattern_shape(p) when is_tuple(p) and tuple_size(p) > 0, do: elem(p, 0)
  defp pattern_shape(_), do: :unknown

  @doc """
  LHS re-match (ports Idris `TTImp.WithClause.getMatch`). Match the parent
  function's original parameter patterns positionally against a with-clause's
  RESTATED patterns, producing a substitution `%{parent_var_name => refined
  surface pattern}`. This is the map that refines the branch goal and sibling
  types by the index a with-clause restates (`n` ↦ `S(m)`).

  Handled (the faithful first slice):
    * variable ↦ variable    — an alias (`n` restated as `m`)
    * variable ↦ constructor — the refinement (`n` restated as `S(m)`)
    * constructor ↦ constructor — structural recursion into matching args

  A restated pattern that is a non-constructor EXPRESSION (e.g. `k + k`) is
  rejected with `{:with_rematch_non_constructor_pattern, …}` — that is the
  deferred forced/dot-pattern case (ledger #5), not a crash.
  """
  @spec match_parent_lhs([term()], [term()]) :: {:ok, %{String.t() => term()}} | {:error, term()}
  def match_parent_lhs(originals, restated) when length(originals) == length(restated) do
    originals
    |> Enum.zip(restated)
    |> Enum.reduce_while({:ok, %{}}, fn {orig, pat}, {:ok, acc} ->
      case match_one_lhs(orig, pat, acc) do
        {:ok, acc2} -> {:cont, {:ok, acc2}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  def match_parent_lhs(originals, restated),
    do: {:error, {:with_rematch_arity_mismatch, length(originals), length(restated)}}

  # A parent variable (or `{:param,…}`) binds to its restated pattern, provided
  # the pattern is a variable or a (possibly nested) constructor application.
  defp match_one_lhs({:variable, _, name}, restated, acc), do: bind_var_lhs(name, restated, acc)
  defp match_one_lhs({:param, _, name}, restated, acc), do: bind_var_lhs(name, restated, acc)

  # Parent constructor vs restated constructor: names + arity must agree, then
  # recurse into the arguments (the getMatch IApp case).
  defp match_one_lhs({:function_call, m1, a1}, {:function_call, m2, a2}, acc) do
    n1 = Keyword.get(m1, :name)
    n2 = Keyword.get(m2, :name)

    cond do
      n1 != n2 ->
        {:error, {:with_rematch_ctor_mismatch, n1, n2}}

      length(a1) != length(a2) ->
        {:error, {:with_rematch_arity_mismatch, length(a1), length(a2)}}

      true ->
        a1
        |> Enum.zip(a2)
        |> Enum.reduce_while({:ok, acc}, fn {o, p}, {:ok, a} ->
          case match_one_lhs(o, p, a) do
            {:ok, a2} -> {:cont, {:ok, a2}}
            {:error, _} = err -> {:halt, err}
          end
        end)
    end
  end

  defp match_one_lhs(orig, _restated, _acc),
    do: {:error, {:with_rematch_unsupported_parent_pattern, pattern_shape(orig)}}

  defp bind_var_lhs(name, restated, acc) do
    if valid_restated_pattern?(restated) do
      merge_lhs_match(acc, name, restated)
    else
      {:error, {:with_rematch_non_constructor_pattern, pattern_shape(restated)}}
    end
  end

  # mergeMatches: a name may be restated more than once only if consistently.
  defp merge_lhs_match(acc, name, pat) do
    case Map.fetch(acc, name) do
      :error ->
        {:ok, Map.put(acc, name, pat)}

      {:ok, existing} ->
        if strip_pattern_meta(existing) == strip_pattern_meta(pat),
          do: {:ok, acc},
          else: {:error, {:with_rematch_inconsistent_binding, name}}
    end
  end

  # A restated pattern must be a variable or a constructor application whose
  # every argument is itself such a pattern. Anything else (binary ops, literal
  # arithmetic, …) is a non-constructor expression — the deferred forced case.
  defp valid_restated_pattern?({:variable, _, _}), do: true

  # A call-shaped node in pattern position is a constructor candidate regardless
  # of capitalization. Indexed GADT constructors are commonly lowercase
  # (`szero`, `ssuc`); branch elaboration validates their identity later.
  defp valid_restated_pattern?({:function_call, _meta, args}),
    do: Enum.all?(args, &valid_restated_pattern?/1)

  defp valid_restated_pattern?(_), do: false

  # Structural equality of surface patterns, ignoring meta.
  defp strip_pattern_meta({:variable, _, n}), do: {:variable, n}

  defp strip_pattern_meta({:function_call, meta, args}),
    do: {:function_call, Keyword.get(meta, :name), Enum.map(args, &strip_pattern_meta/1)}

  defp strip_pattern_meta(other), do: other

  # Names for the branch's telescope binders, most-recently-bound first. Surface
  # pattern variables name present (ω) positions. Erased constructor existentials
  # get distinct internal names: they are still quantity-0 (so relevance rejects
  # computational use), but branch substitutions can address each slot without
  # collapsing them all to the old, ambiguous `_erased` name. A source-level name
  # requested with `{index = binder}` replaces this internal name below.
  # Assign each constructor telescope slot a branch-scope name. POSITIONAL slots
  # (plicity `:explicit`) consume the next surface pattern variable; NON-positional
  # slots (plicity `:implicit` — an erased inferred index OR a relevant implicit
  # `{k:T}`) get a synthetic name, replaced by the user's binder only if they name
  # it via `{k = kk}` (see `split_named_implicits`). Positional-vs-not keys off
  # PLICITY, not quantity: a relevant implicit is ω yet non-positional.
  defp branch_scope(telescope, quantities, plicities, pattern_vars) do
    {names_in_order, _rest} =
      Enum.zip([telescope, quantities, plicities])
      |> Enum.with_index()
      |> Enum.map_reduce(pattern_vars, fn
        {{{_tele_name, _type}, _q, :explicit}, _i}, [v | rest] -> {v, rest}
        {{{tele_name, _type}, :erased, :implicit}, i}, vars -> {"$erased_#{tele_name}_#{i}", vars}
        {{{tele_name, _type}, _q, :implicit}, i}, vars -> {"$implicit_#{tele_name}_#{i}", vars}
      end)

    Enum.reverse(names_in_order)
  end

  defp validate_constructor_pattern_arity(pattern, ctor, cname, pattern_vars \\ nil) do
    pattern_vars =
      case pattern_vars do
        nil ->
          case constructor_pattern(pattern) do
            {:ok, {_name, vars}} -> vars
            _ -> []
          end

        vars ->
          vars
      end

    expected = Enum.count(Inductive.plicities_of(ctor), &(&1 == :explicit))
    actual = length(pattern_vars)

    if expected == actual do
      :ok
    else
      {:error,
       {:pattern_arity_mismatch,
        %{
          constructor: cname,
          display_name: pattern_display_name(pattern, cname),
          expected: expected,
          actual: actual,
          direction: if(actual < expected, do: :too_few, else: :too_many),
          span: surface_expression_span(pattern)
        }}}
    end
  end

  defp pattern_display_name({:function_call, meta, _args}, fallback) when is_list(meta),
    do: Keyword.get(meta, :name, to_string(fallback))

  defp pattern_display_name(_pattern, fallback), do: to_string(fallback)

  # Shared branch-goal refinement (Task 3.4) — ONE equation-compiler refinement
  # behind two front-ends (plain `match` `elaborate_matched_branch` and
  # `with`-rematch `elaborate_rematch_branch`). Composes (1a) index inversion (the
  # `branch_unify` verdict `subst`) with (1b) scrutinee-VALUE refinement: a
  # variable scrutinee is keyed into the subst at `i + arity`; a computed one has
  # its occurrences replaced by the branch constructor as a whole term (matching
  # `build_motive`'s kabstract — the kernel checks this branch at `motive @ ctor`).
  defp instantiate_branch_motive(motive, constructor_indices, cname, arity, subst, branch_ctx) do
    ctor_term = branch_constructor_term(cname, arity)

    motive
    |> Subst.shift(arity, 0)
    |> then(fn shifted_motive ->
      Enum.reduce(constructor_indices ++ [ctor_term], shifted_motive, fn argument, application ->
        {:app, application, argument}
      end)
    end)
    |> replace_branch_vars(subst)
    |> then(&Kernel.normalize(branch_ctx, &1))
  end

  defp refine_branch_goal_term(result_type_term, scrut_term, cname, arity, subst) do
    ctor_term = branch_constructor_term(cname, arity)

    subst_with_scrut =
      case scrut_term do
        {:var, i} -> Map.put(subst, i + arity, ctor_term)
        _other -> subst
      end

    shifted_goal = Subst.shift(result_type_term, arity, 0)

    shifted_goal =
      case scrut_term do
        {:var, _} ->
          shifted_goal

        computed ->
          replace_term_scoped(
            shifted_goal,
            Subst.shift(computed, arity, 0),
            ctor_term
          )
      end

    replace_branch_vars(shifted_goal, subst_with_scrut)
  end

  defp branch_constructor_term(cname, 0), do: {:ctor, cname, []}

  defp branch_constructor_term(cname, arity) do
    args = for i <- 0..(arity - 1), do: {:var, arity - 1 - i}
    {:ctor, cname, args}
  end

  # Extend the branch context with a constructor's argument telescope. The
  # telescope's type terms are written in the constructor's own isolated frame
  # `ctx_full = params ++ args`, so — mirroring the kernel's `extend_with_
  # telescope` — evaluate each against a local value environment seeded with the
  # scrutinee's actual parameter values (`param_vals`) beneath fresh neutrals for
  # the args already bound. A parameter reference in an arg type (e.g. `rest : a`
  # in `prepend`) then resolves to the scrutinee's parameter, not a stray outer
  # binder. Values carry absolute de Bruijn *levels*, so param_vals stay valid as
  # the context grows. For a parameter-free family this is the previous behavior.
  defp extend_context(ctx, telescope, param_vals) do
    {ctx_final, _local_vals} =
      Enum.reduce(telescope, {ctx, Enum.reverse(param_vals)}, fn {_name, type_term}, {c, local_vals} ->
        type_value = Eval.eval(type_term, local_vals)

        fresh_val = {:vneutral, {:nvar, Context.length(c)}}
        {Context.extend(c, type_value), [fresh_val | local_vals]}
      end)

    ctx_final
  end

  defp replace_branch_vars({:var, i}, subst), do: replace_branch_var(i, subst, 0)

  defp replace_branch_vars({:pi, _g, d, c}, subst),
    do:
      {:pi, Cure.Core.Grade.unrestricted(), replace_branch_vars(d, subst),
       replace_branch_vars(c, shift_subst(subst, 1))}

  defp replace_branch_vars({:lam, _g, d, b}, subst),
    do:
      {:lam, Cure.Core.Grade.unrestricted(), replace_branch_vars(d, subst),
       replace_branch_vars(b, shift_subst(subst, 1))}

  defp replace_branch_vars({:app, f, a}, subst),
    do: {:app, replace_branch_vars(f, subst), replace_branch_vars(a, subst)}

  defp replace_branch_vars({:data, n, ps, is}, subst),
    do: {:data, n, Enum.map(ps, &replace_branch_vars(&1, subst)), Enum.map(is, &replace_branch_vars(&1, subst))}

  defp replace_branch_vars({:ctor, n, args}, subst),
    do: {:ctor, n, Enum.map(args, &replace_branch_vars(&1, subst))}

  defp replace_branch_vars({:case, scr, m, brs}, subst),
    do:
      {:case, replace_branch_vars(scr, subst), replace_branch_vars(m, subst),
       Enum.map(brs, fn {c, ar, b} -> {c, ar, replace_branch_vars(b, shift_subst(subst, ar))} end)}

  defp replace_branch_vars(other, _subst), do: other

  defp shift_subst(subst, amount) do
    Map.new(subst, fn {k, v} -> {k + amount, Subst.shift(v, amount, 0)} end)
  end

  defp replace_branch_var(i, subst, depth) when depth < 100_000 do
    case Map.get(subst, i) do
      nil -> {:var, i}
      {:var, ^i} -> {:var, i}
      {:var, j} -> replace_branch_var(j, subst, depth + 1)
      term -> replace_branch_vars(term, subst)
    end
  end

  defp replace_branch_var(i, _subst, _depth), do: {:var, i}

  @doc """
  Elaborate a constructor application `C(a₁, …, aₙ)`, inferring the erased index
  arguments (quantity 0) from the runtime-relevant (quantity ω) arguments'
  types (design spec §5.2). `present_args` is `[{core_term, type_value}]` — the
  already-elaborated ω arguments with their inferred types.

  Fresh metavariables stand in for the erased arguments; each ω argument's
  expected telescope type is specialised with the choices so far (`Subst`) and
  unified against the provided argument's type (`Unify`). On success every
  metavariable is solved, and the fully-applied `{:ctor, …}` term plus its result
  type (the family at the computed indices) are returned.

  `present_args` is `[{core_term, type_term}]` — each ω argument with its type
  already reified as a term in the caller's de Bruijn frame.
  """
  @spec elaborate_ctor_app(Env.t(), atom(), [{term(), term()}], Context.t() | nil) ::
          {:ok, term(), Cure.Core.Value.t()} | {:error, term()}
  def elaborate_ctor_app(env, cname, present_args, ctx \\ nil, expected_core \\ nil) do
    ctor = Inductive.get_ctor(env, cname)
    family = Inductive.ctor_family(env, cname)

    if is_nil(ctor) or is_nil(family) do
      {:error, {:unknown_constructor, cname}}
    else
      # The family's parameters are bound outside the constructor's arg telescope
      # (the kernel checks it as `ctx_full = params ++ args`). A constructor arg
      # type — e.g. `prepend`'s `x : a` — can reference a parameter, so model the
      # parameters as leading erased slots: their metavariables are seeded into
      # the substitution frame and solved by unifying the present arguments. For
      # a parameter-free family this prefix is empty (unchanged behavior).
      param_tele = Inductive.param_telescope(env, family) || []
      # Family parameters are always solved (never positional) → plicity :implicit.
      param_slots = Enum.map(param_tele, fn entry -> {entry, :erased, :implicit} end)
      plicities = Inductive.plicities_of(ctor)
      telescope = param_slots ++ Enum.zip([ctor.args, ctor.quantities, plicities])
      pc = length(param_tele)
      init = {:ok, MetaCtx.new(), [], present_args}

      telescope
      |> Enum.reduce_while(init, &solve_arg(&1, &2, env, ctx))
      |> pin_ctor_result(expected_core, family, ctor, pc, env)
      |> finish_ctor_app(cname, family, ctor, pc, ctx)
    end
  end

  # Checking-mode index inference: unify the constructor's RESULT type (built with
  # the erased-index metavariables still open) against the expected type, pinning
  # indices the present arguments could not. A nullary constructor whose indices
  # are all erased — `prim : SF(av, bv, DCau)` reconstructed in a dependent-match
  # branch expecting `SF(as, bs, DCau)` — has NO present argument to solve `av`/`bv`
  # from; the expected type is their only source. In inference mode (`expected_core
  # == nil`) this is a no-op, so ordinary constructor applications are unchanged.
  defp pin_ctor_result({:ok, mctx, chosen, []} = ok, expected_core, family, ctor, pc, env)
       when expected_core != nil do
    {param_vals, args} = Enum.split(chosen, pc)
    seed = param_vals ++ args
    params = Enum.map(Map.get(ctor, :result_params, []), &Subst.instantiate(&1, seed))
    indices = Enum.map(ctor.result_indices, &Subst.instantiate(&1, seed))
    result_term = {:data, family, params, indices}

    case Unify.unify(result_term, expected_core, mctx, env) do
      {:ok, mctx2} -> {:ok, mctx2, chosen, []}
      # Leave the mismatch to `finish_ctor_app` (unsolved metas) or the kernel's
      # own re-check — never silently accept.
      {:error, _} -> ok
    end
  end

  defp pin_ctor_result(acc, _expected_core, _family, _ctor, _pc, _env), do: acc

  # One telescope slot: erased → fresh meta; present → unify expected vs actual.
  # `env` is threaded as the conversion signature so a present argument whose type
  # carries a *computed* index (`seq`'s `dmeet(d1, d2)`) unifies up-to-δ against
  # the expected `DDec` — closing the composed-computed-index reach (Idris parity)
  # without any kernel change (`Unify` uses the trusted `Conv`; the kernel still
  # re-checks the assembled ctor). See `Unify.unify/4`.
  # An IMPLICIT slot (an erased inferred index OR a relevant implicit `{k:T}`) is
  # never positional: insert a fresh meta, solved by unifying a later explicit
  # argument's type or the expected result. Positional-vs-not keys off PLICITY,
  # not quantity — a relevant implicit is ω yet still solved, not passed.
  defp solve_arg({{_name, type_term}, _grade, :implicit}, {:ok, mctx, chosen, present}, _env, _ctx) do
    {mctx, id} = MetaCtx.fresh(mctx, Subst.instantiate(type_term, chosen))
    {:cont, {:ok, mctx, chosen ++ [{:meta, id}], present}}
  end

  defp solve_arg({{_name, _type_term}, _grade, :explicit}, {:ok, _mctx, _chosen, []}, _env, _ctx),
    do: {:halt, {:error, :too_few_arguments}}

  defp solve_arg(
         {{_name, type_term}, _grade, :explicit},
         {:ok, mctx, chosen, [{arg, arg_type_term} | rest]},
         env,
         ctx
       ) do
    expected = Subst.instantiate(type_term, chosen)

    case unify_in_context(expected, arg_type_term, mctx, env, ctx) do
      {:ok, mctx} ->
        {:cont, {:ok, mctx, chosen ++ [arg], rest}}

      {:error, reason} ->
        # The domain may be a generated anonymous-union family that goal-directed
        # solving has already pinned (see `elaborate_global_app`). Unification has no
        # coercion, so a MEMBER argument fails against it — inject the member's
        # constructor and retry. This is the same check-position coercion applied
        # everywhere else, at the one place where the argument's domain is only known
        # after the goal has been solved.
        case inject_arg_into_union(arg, arg_type_term, Unify.zonk(expected, mctx), env) do
          nil ->
            {:halt, {:error, {:index_mismatch, reason}}}

          injected ->
            case unify_in_context(expected, Unify.zonk(expected, mctx), mctx, env, ctx) do
              {:ok, mctx} -> {:cont, {:ok, mctx, chosen ++ [injected], rest}}
              {:error, _} -> {:halt, {:error, {:index_mismatch, reason}}}
            end
        end
    end
  end

  defp unify_in_context(left, right, mctx, env, nil), do: Unify.unify(left, right, mctx, env)

  defp unify_in_context(left, right, mctx, env, ctx) do
    case Unify.unify(left, right, mctx, env) do
      {:ok, _} = ok ->
        ok

      {:error, _} ->
        zonked_left = Unify.zonk(left, mctx)
        zonked_right = Unify.zonk(right, mctx)
        normalized_left = contextual_normalize_cached(zonked_left, mctx, ctx)
        normalized_right = contextual_normalize_cached(zonked_right, mctx, ctx)

        case Unify.unify(normalized_left, normalized_right, mctx, env) do
          {:ok, _} = ok ->
            ok

          {:error, contextual_reason} ->
            convertible? =
              not has_meta?(normalized_left) and not has_meta?(normalized_right) and
                Conv.conv?(
                  normalized_left,
                  normalized_right,
                  Context.env(ctx),
                  Context.length(ctx),
                  Context.signature(ctx)
                )

            if convertible? do
              {:ok, mctx}
            else
              {:error, contextual_reason}
            end
        end
    end
  end

  # Contextual normalization is pure for a fixed conversion environment: all
  # metavariables have already been zonked and temporarily reified as synthetic
  # globals. Keep this cache local to the current elaboration operation so a
  # source-hash/interface never observes speculative normal forms.
  defp contextual_normalize_cached(term, mctx, ctx) do
    CallAttemptProfile.increment(:contextual_normalize_calls)

    key = {
      term,
      MetaCtx.revision(mctx),
      Context.signature(ctx),
      Context.length(ctx)
    }

    case AttemptCache.fetch(:normalize, key, fn -> contextual_normalize_meta_aware(term, ctx) end) do
      {:hit, normalized} ->
        CallAttemptProfile.increment(:contextual_normalize_cache_hits)
        normalized

      {:miss, normalized} ->
        CallAttemptProfile.increment(:contextual_normalize_cache_misses)
        normalized
    end
  end

  defp contextual_normalize_meta_aware(term, ctx) do
    term
    |> map_contextual_metas(fn id -> {:global, :"$contextual_meta$#{id}"} end)
    |> then(&Kernel.normalize(ctx, &1))
    |> map_contextual_metas(fn
      name when is_atom(name) ->
        case Atom.to_string(name) do
          "$contextual_meta$" <> id -> {:meta, String.to_integer(id)}
          _ -> {:global, name}
        end
    end)
  end

  defp map_contextual_metas({:meta, id}, mapper), do: mapper.(id)

  defp map_contextual_metas({:global, name}, mapper) do
    case Atom.to_string(name) do
      "$contextual_meta$" <> _ -> mapper.(name)
      _ -> {:global, name}
    end
  end

  defp map_contextual_metas(term, mapper) when is_tuple(term),
    do: term |> Tuple.to_list() |> Enum.map(&map_contextual_metas(&1, mapper)) |> List.to_tuple()

  defp map_contextual_metas(term, mapper) when is_list(term),
    do: Enum.map(term, &map_contextual_metas(&1, mapper))

  defp map_contextual_metas(term, _mapper), do: term

  # Inject a TERM whose inferred type is a member of the (already-solved) union domain.
  # Term-level, not value-level: at this point everything is a Core term, so no Context
  # is needed. Returns nil when the domain is not a union or the argument is not one of
  # its members — the caller then reports the ordinary unification failure.
  defp inject_arg_into_union(arg, arg_type_term, {:data, ukey, [], []}, env) do
    if Cure.Elab.Union.union_family?(ukey) do
      cname = Cure.Elab.Union.ctor_key(ukey, %{key: Cure.Elab.Union.member_key(arg_type_term)})
      if Inductive.get_ctor(env, cname), do: {:ctor, cname, [arg]}, else: nil
    end
  end

  defp inject_arg_into_union(_arg, _arg_type_term, _expected, _env), do: nil

  defp finish_ctor_app({:error, _} = err, _cname, _family, _ctor, _pc, _ctx), do: err

  defp finish_ctor_app({:ok, _mctx, _chosen, [_ | _]}, _cname, _family, _ctor, _pc, _ctx),
    do: {:error, :too_many_arguments}

  defp finish_ctor_app({:ok, mctx, chosen, []}, cname, family, ctor, pc, ctx) do
    all = Enum.map(chosen, &Unify.zonk(&1, mctx))

    if Enum.any?(all, &has_meta?/1) do
      {:error, {:unsolved_metavariables, cname}}
    else
      # `chosen` is [solved parameters] ++ [constructor args]. The Core `:ctor`
      # term carries only the constructor args (parameters are erased and
      # recovered from the value's type); result params/indices reference
      # `ctx_full = params ++ args`, so instantiate them with the full frame.
      {param_vals, args} = Enum.split(all, pc)
      seed = param_vals ++ args
      params = Enum.map(Map.get(ctor, :result_params, []), &Subst.instantiate(&1, seed))
      indices = Enum.map(ctor.result_indices, &Subst.instantiate(&1, seed))

      # The result type's computed indices reference the CALLER's context vars
      # (e.g. `seq`'s result `SF(app(av,cv), …)`). Evaluate under the caller's
      # environment so those free de Bruijn variables get the correct neutral
      # levels — evaluating under `[]` mis-levels them, which is invisible when a
      # ctor is checked directly (the kernel re-infers) but CORRUPTS meta-solving
      # when this inferred type feeds further elaboration (a computed-index ctor
      # applied as another ctor's argument, e.g. `loop(seq(a,b))`). Mirrors
      # `finish_global_app`. With no caller context (isolated unit calls), fall
      # back to `[]` — those terms are closed, so the frame is immaterial.
      caller_env = if ctx, do: Context.env(ctx), else: []
      result_type = Eval.eval({:data, family, params, indices}, caller_env)
      {:ok, {:ctor, cname, args}, result_type}
    end
  end

  # Bidirectional application for a global with implicit (erased) parameters, used
  # only as a fallback when the ordinary inference path fails — a call whose
  # argument cannot be inferred in isolation but *can* be checked once the callee's
  # implicit parameters are solved, e.g. `map(s, Cons(Z(), Nil()))` whose list
  # argument is underdetermined until `a` is fixed from `s : (Nat) -> Nat`.
  #
  # It folds the callee's Π telescope left to right: each erased slot becomes a
  # fresh metavariable; each present slot's domain is instantiated with the
  # arguments chosen so far and zonked — if that domain is now metavariable-free
  # the argument is *checked* against it (so an underdetermined constructor
  # argument reaches the checking-mode constructor path), otherwise the argument is
  # *inferred* and its type unified against the domain to solve the metavariables.
  # `finish_global_app` assembles and the caller's kernel re-check gates the result,
  # so nothing unsound rests on the inference order.
  #
  # `name` is NOT guaranteed to be a def here. Several callers reach this
  # function speculatively: `elaborate_global_app_expected/6` routes any
  # placeholder-bearing call through it, and
  # `Cure.Elab.Resolve.method_call_checked_candidates/7` walks EVERY anonymous
  # instance registered for an interface and elaborates each candidate's mangled
  # method global, discarding the ones that error. A candidate whose global is
  # absent from this environment is an ordinary miss for those callers, so it
  # must be reported as `:unknown_global` — an unmatched `Env.get_def/2` would
  # raise `MatchError` out of a fold that is written to tolerate failure, taking
  # down the whole compilation and hiding every later diagnostic in the run.
  defp elaborate_implicit_app_bidirectional(env, name, arg_asts, names, ctx, expected \\ nil) do
    case Env.get_def(env, name) do
      %{type: pi_type, quantities: quantities} = defn ->
        plicities =
          Map.get(defn, :plicities) ||
            Enum.map(quantities, fn
              :erased -> :implicit
              _ -> :explicit
            end)

        elaborate_implicit_app_bidirectional(
          env,
          name,
          arg_asts,
          names,
          ctx,
          expected,
          pi_type,
          quantities,
          plicities
        )

      nil ->
        {:error, {:unknown_global, name}}
    end
  end

  defp elaborate_implicit_app_bidirectional(
         env,
         name,
         arg_asts,
         names,
         ctx,
         expected,
         pi_type,
         quantities,
         plicities
       ) do
    {domains, codomain} = peel_pi(pi_type, length(quantities))

    # Transparent aliases in an expected result must be unfolded before the
    # goal-first implicit solve. Refinement aliases are the load-bearing case:
    # `PositiveNatural` normalizes to `Sigma(Nat, IsPositive)`, which determines
    # the hidden predicate of `refine` before its proof argument is checked.
    # `finish_global_app` already performs this normalization for its final solve;
    # doing the same in the pre-pass prevents argument order from hiding that goal.
    expected_for_goal =
      if expected != nil do
        case Kernel.normalize(ctx, expected) do
          :fuel_exhausted -> expected
          normalized -> normalized
        end
      end

    # Quantity controls relevance; plicity controls whether a surface argument is
    # consumed. In particular `@erased witness : T` is explicit-but-erased, while
    # `{witness : T}` is implicit-and-erased. Collapsing both to `:erased` shifted
    # every later argument in the goal-directed path.
    slots = Enum.zip([domains, quantities, plicities])
    init = {:ok, MetaCtx.new(), [], arg_asts, []}

    # GOAL-DIRECTED solving from the concrete return-type goal — ordinary
    # bidirectional propagation (Idris/Agda/Lean): unify the codomain against the
    # expected type FIRST, so a leading implicit determined only by the result is
    # solved before its dependent argument slots are elaborated. This is the path
    # taken when an argument cannot be inferred standalone, in two shapes:
    #
    #   * an anonymous-union value slot (`Std.Map.put(:a, 1, Std.Map.new())` —
    #     `new()`'s implicits have nothing to fix them): without goal-first solving
    #     the domain `?v` stays a meta, the slot is DEFERRED and later resolved by
    #     inferring the argument, locking `?v := Int` and LOSING the union;
    #   * a lambda argument whose domain the goal alone fixes (`mk(fn(x) -> x.1)`
    #     at `Box(Tuple(Int,Int), Int)` — `mk : {s} -> {a} -> (s -> a) -> Box(s,a)`):
    #     without it `?s`/`?a` stay metas, so `fn(x) -> x.1` is checked at `?s -> ?a`
    #     and the projection cannot lower (`:unsupported_expression`). When NO later
    #     argument constrains the implicit (only lambdas, or a single argument), the
    #     cross-argument deferral cannot rescue it, but the goal can.
    #
    # `bidir_solve_codomain_from_goal` swallows unification failure, so a goal that
    # does not inform the codomain leaves the accumulator untouched — the ordinary
    # left-to-right slot solving then runs exactly as before, and the kernel
    # re-checks the assembled term regardless. Restricted to a META-FREE goal so a
    # still-open expected type (nothing to solve against) skips the pre-pass.
    seed_from_goal? =
      union_goal?(expected_for_goal) or
        (not is_nil(expected_for_goal) and not Unify.has_meta?(expected_for_goal))

    {init, slots} =
      if seed_from_goal? do
        # Allocate the REAL leading erased/placeholder metas before solving the
        # codomain. Previously only erased slots were retained; explicit `_`
        # slots were represented by disposable padding metas during goal
        # unification, then allocated afresh in the main pass and stayed
        # unsolved (`box(_) : Box(Z)`). Stop at the first ordinary present
        # argument so its existing bidirectional checking order is unchanged.
        {seeded, rest} = bidir_seed_goal_prefix(slots, init, names, ctx, env)
        seeded = bidir_solve_codomain_from_goal(seeded, codomain, expected_for_goal, env, rest)

        {seeded, rest}
      else
        {init, slots}
      end

    slots
    |> Enum.reduce_while(init, &bidir_app_slot(&1, &2, names, ctx, env))
    |> resolve_deferred_slots(names, ctx, env)
    |> finish_global_app(name, codomain, ctx, env, expected)
  end

  defp bidir_seed_goal_prefix(
         [slot = {_dom, _grade, :implicit} | rest],
         acc,
         names,
         ctx,
         env
       ) do
    {:cont, acc} = bidir_app_slot(slot, acc, names, ctx, env)
    bidir_seed_goal_prefix(rest, acc, names, ctx, env)
  end

  defp bidir_seed_goal_prefix(
         [slot | rest],
         {:ok, _mctx, _chosen, [{:variable, _meta, "_"} | _], _deferred} = acc,
         names,
         ctx,
         env
       ) do
    {:cont, acc} = bidir_app_slot(slot, acc, names, ctx, env)
    bidir_seed_goal_prefix(rest, acc, names, ctx, env)
  end

  defp bidir_seed_goal_prefix(slots, acc, _names, _ctx, _env), do: {acc, slots}

  # `solve_codomain_from_goal/5` for the bidirectional accumulator's 5-tuple. Same
  # contract: pad `chosen` to the full binder stack (Subst.instantiate indexes against
  # all of it), unify the codomain with the goal, and swallow failure so the ordinary
  # path still produces the honest error.
  defp bidir_solve_codomain_from_goal(
         {:ok, mctx, chosen, args, deferred},
         codomain,
         expected,
         env,
         remaining
       ) do
    {mctx_padded, padded} =
      Enum.reduce(remaining, {mctx, chosen}, fn {dom, _q, _plicity}, {m, acc} ->
        {m, id} = MetaCtx.fresh(m, Subst.instantiate(dom, acc))
        {m, acc ++ [{:meta, id}]}
      end)

    case Unify.unify(Subst.instantiate(codomain, padded), expected, mctx_padded, env) do
      {:ok, mctx2} -> {:ok, mctx2, chosen, args, deferred}
      {:error, _} -> {:ok, mctx, chosen, args, deferred}
    end
  end

  defp bidir_solve_codomain_from_goal({:error, _} = err, _cod, _exp, _env, _rem), do: err

  @doc """
  Type-position entry for implicit insertion (spec 2026-07-08 §7): elaborate an
  application of a global that carries implicit (erased) parameters, from its
  SURFACE argument ASTs, in the caller's typing context. Used by the
  return-type lowering in `Cure.Elab.Declarations` — term position reaches the
  same machinery via `elaborate_named_call`. The kernel re-checks the assembled
  signature, so nothing unsound rests on this path.
  """
  def elaborate_implicit_global_app(env, name, arg_asts, names, ctx) do
    elaborate_implicit_app_bidirectional(env, name, arg_asts, names, ctx)
  end

  defp bidir_app_slot(
         {dom, _grade, :implicit},
         {:ok, mctx, chosen, args, deferred},
         _names,
         _ctx,
         _env
       ) do
    {mctx, id} = MetaCtx.fresh(mctx, Subst.instantiate(dom, chosen))
    {:cont, {:ok, mctx, chosen ++ [{:meta, id}], args, deferred}}
  end

  defp bidir_app_slot(
         {_dom, _grade, :explicit},
         {:ok, _mctx, _chosen, [], _deferred},
         _names,
         _ctx,
         _env
       ),
       do: {:halt, {:error, :too_few_arguments}}

  # An explicit `_` in call-argument position is a goal-directed placeholder,
  # not a reference to a global named `_`. Seed a term metavariable at this
  # slot and continue: a later dependent argument may determine its VALUE.
  # `finish_global_app` rejects it if it remains
  # unsolved, and the assembled application is kernel-checked by the caller, so
  # no placeholder can escape into Core.
  defp bidir_app_slot(
         {dom, _grade, :explicit},
         {:ok, mctx, chosen, [{:variable, _meta, "_"} | rest], deferred},
         _names,
         _ctx,
         _env
       ) do
    dom_inst = Enum.map(chosen, &Unify.zonk(&1, mctx)) |> then(&Subst.instantiate(dom, &1))
    {mctx, id} = MetaCtx.fresh(mctx, dom_inst)
    {:cont, {:ok, mctx, chosen ++ [{:meta, id}], rest, deferred}}
  end

  # A supplied explicit argument — grade governs later USAGE counting
  # (`relevance.ex`), not slot mechanics: unrestricted, linear, affine, and
  # explicit-erased binders all consume one surface argument here, mirroring
  # `solve_arg/3`'s telescope slot.
  defp bidir_app_slot(
         {dom, _grade, :explicit},
         {:ok, mctx, chosen, [arg | rest], deferred},
         names,
         ctx,
         env
       ) do
    # ZONK-then-instantiate, not instantiate-then-zonk: `Subst.instantiate` shifts a
    # substituted term across binders, `Unify.zonk` does not. A domain that is a Π
    # (a function-typed argument, `(a) -> a`) whose earlier sibling already solved the
    # metavariable to a term with FREE de Bruijn variables would otherwise reach the
    # checking mode below with the codomain occurrence unshifted (`{:var,2}` where
    # `{:var,3}` is due). Resolving the metavariables into the substitution first lets
    # `instantiate` place them at the right depth. See the twin fix in
    # `resolve_deferred_slots`; a closed solution shifts to a no-op, so scalar/data
    # domains are unaffected.
    dom_inst = Enum.map(chosen, &Unify.zonk(&1, mctx)) |> then(&Subst.instantiate(dom, &1))

    if has_meta?(dom_inst) do
      # Domain still unsolved — infer the argument and unify to solve metavariables.
      case elaborate_expr_typed(arg, names, ctx, env) do
        {:ok, term, ty} ->
          # Recover the (params, indices) split that the sig-less `Quote.reify`
          # collapses (elaborator.ex:1268 `resplit_data`), so an argument type that
          # carries a NESTED indexed family — e.g. a Sigma projection's `p` whose
          # type is `Sigma(x: Dec, SF(as, bs, x))` — does not reach the kernel with
          # SF's indices smuggled into its param slot (a false `:arg_arity`).
          ty_term = resplit_data(Quote.reify(ty, Context.length(ctx)), env)

          case Unify.unify(dom_inst, ty_term, mctx, env) do
            {:ok, mctx} ->
              {:cont, {:ok, mctx, chosen ++ [term], rest, deferred}}

            {:error, reason} ->
              # The argument HAS a type (`elaborate_expr_typed` succeeded), but it does
              # not unify against the still-meta-bearing domain — the domain is a redex
              # STUCK on an unsolved metavariable a LATER sibling determines. Example
              # (the intrinsic well-scoped-BST recursion): the proof domain
              # `elt(EFin x, ?hi) = OT` is a case-tree stuck on `?hi`, and the supplied
              # proof's type is `slt(x, k) = OT`; only once the trailing tree argument
              # solves `?hi := EFin k` does `elt(EFin x, EFin k)` ι-reduce to `slt(x, k)`
              # and match. DEFER exactly as the inference-FAILURE branch does — a
              # placeholder holds the slot, later siblings solve the domain, and
              # `resolve_deferred_slots` re-checks the argument against the now-concrete
              # domain. `mctx` here is the PRE-unify context (the failed unify's partial
              # solution is discarded), so nothing leaks. Only when a later argument
              # actually exists (`rest != []`) — otherwise nothing could rescue the
              # domain and the honest unify error is surfaced immediately. The assembled
              # call is kernel-re-checked by `finish_global_app`, so this order change
              # rests on nothing unsound.
              if rest == [] do
                {:halt, {:error, reason}}
              else
                {mctx, ph} = MetaCtx.fresh(mctx)

                {:cont, {:ok, mctx, chosen ++ [{:meta, ph}], rest, deferred ++ [{ph, arg, dom, length(chosen)}]}}
              end
          end

        {:error, _} ->
          # A lambda argument whose Π domain still bears a metavariable in its
          # CODOMAIN (`(n:N) -> ?F(n)`) cannot infer standalone; try solving the
          # codomain metavariable under the binder first (higher-order/Miller,
          # ledger #10). Only if that does not apply do we defer.
          case try_lambda_meta_pi(arg, dom_inst, mctx, names, ctx, env) do
            {:ok, mctx, lam_term} ->
              {:cont, {:ok, mctx, chosen ++ [lam_term], rest, deferred}}

            :fallthrough ->
              # An underdetermined argument at a still-unsolved domain — e.g. `fz()` at
              # `Fin(?n)`, whose index only a *later* argument (the vector) determines.
              # It cannot infer standalone, so defer it: a placeholder metavariable holds
              # its position in `chosen` (keeping later domains' de Bruijn frames aligned),
              # and `resolve_deferred_slots` checks it against the now-solved domain and
              # back-patches the placeholder once the later arguments have run.
              {mctx, ph} = MetaCtx.fresh(mctx)
              {:cont, {:ok, mctx, chosen ++ [{:meta, ph}], rest, deferred ++ [{ph, arg, dom, length(chosen)}]}}
          end
      end
    else
      # Domain fully known — check the argument against it (reaches checking mode).
      case elaborate_expr_checked(arg, dom_inst, names, ctx, env) do
        {:ok, term} -> {:cont, {:ok, mctx, chosen ++ [term], rest, deferred}}
        {:error, _} = err -> {:halt, err}
      end
    end
  end

  # A lambda argument at a Π domain whose CODOMAIN still bears a metavariable
  # (`(n:N) -> ?F(n)`) cannot be inferred standalone, and the general checking
  # judgement (`elaborate_expr_checked`) does not thread `mctx`, so it would
  # reject the unsolved codomain. Here `mctx` IS in scope, so we solve it: bind
  # the parameter, INFER the body, and unify the reconstructed Π against the
  # expected one — the codomain metavariable is then solved *under the binder*
  # (the Miller pattern `?F(n) := λn. body_ty`, ledger #10). Single-parameter
  # lambda over a literal Π with a meta-free domain; any other shape falls through
  # to the deferral path. Additive/fallback-only: reached only after inference has
  # already failed, and the assembled call is kernel-re-checked by
  # `finish_global_app`, so nothing unsound rests on the solve.
  defp try_lambda_meta_pi({:lambda, meta, [body_expr]}, {:pi, _g, dom_term, cod_term}, mctx, names, ctx, env) do
    case Keyword.fetch!(meta, :params) do
      [{:param, _pm, pname}] ->
        if has_meta?(dom_term) do
          :fallthrough
        else
          dom_value = Eval.eval(dom_term, Context.env(ctx))
          ctx1 = Context.extend(ctx, dom_value)

          case elaborate_expr_typed(body_expr, [pname | names], ctx1, env) do
            {:ok, body_term, body_ty} ->
              # Pass the signature so an indexed-family body type like
              # `Equivalent(Nat,n,n)` is read back as params+indices instead of the
              # flat `{:data, :Equivalent, all, []}` shape. This term may become the
              # solution for a codomain metavariable (`?P := λn. Equivalent(Nat,n,n)`),
              # and the later `P(Zero)` kernel check expects the split form.
              body_ty_term = Quote.reify(body_ty, Context.length(ctx1), env)

              case Unify.unify(
                     {:pi, Cure.Core.Grade.unrestricted(), dom_term, cod_term},
                     {:pi, Cure.Core.Grade.unrestricted(), dom_term, body_ty_term},
                     mctx,
                     env
                   ) do
                {:ok, mctx} ->
                  {:ok, mctx, {:lam, Cure.Core.Grade.unrestricted(), dom_term, body_term}}

                {:error, _} ->
                  :fallthrough
              end

            {:error, _} ->
              :fallthrough
          end
        end

      _ ->
        :fallthrough
    end
  end

  defp try_lambda_meta_pi(_arg, _dom_inst, _mctx, _names, _ctx, _env), do: :fallthrough

  # Second pass over the arguments deferred by `bidir_app_slot` (each an
  # underdetermined argument whose domain metavariables a later argument solves).
  # By now those metavariables are solved, so each deferred domain instantiates to a
  # concrete type; check the argument against it and solve the placeholder to the
  # resulting term. A deferred domain still bearing a metavariable means no later
  # argument determined it — a genuinely ambiguous call, reported as unsolved.
  defp resolve_deferred_slots({:error, _} = err, _names, _ctx, _env), do: err

  defp resolve_deferred_slots({:ok, mctx, chosen, args, []}, _names, _ctx, _env),
    do: {:ok, mctx, chosen, args}

  defp resolve_deferred_slots({:ok, mctx, chosen, args, deferred}, names, ctx, env) do
    Enum.reduce_while(deferred, {:ok, mctx}, fn {ph, arg, dom, k}, {:ok, mctx} ->
      # ZONK the chosen prefix FIRST, THEN instantiate — not instantiate-then-zonk.
      # `Subst.instantiate` is binder-aware (it shifts a substituted term when it
      # crosses a binder), but `Unify.zonk` is NOT: it replaces a solved `{:meta,id}`
      # with its solution verbatim. When a deferred domain is a Π (`(a) -> a`, a lambda
      # argument's type) and the metavariable a later sibling solved to a term with
      # FREE de Bruijn variables (a rigid parameter, `?a := {:var,2}`), the occurrence
      # in the codomain sits UNDER the domain binder and must shift to `{:var,3}`.
      # Instantiate-then-zonk left it at `{:var,2}` (`conversion_failure {:var,3}
      # {:var,2}`); resolving the metavariables into the substitution and letting
      # `instantiate` place them restores the shift. A closed solution (`Nat`, `Z` —
      # every constructor-domain deferral) shifts to a no-op, so those are unaffected.
      dom_inst =
        Enum.take(chosen, k) |> Enum.map(&Unify.zonk(&1, mctx)) |> then(&Subst.instantiate(dom, &1))

      # If a later sibling argument did not fully determine this deferred domain,
      # the deferred argument may still determine it FROM ITS OWN constructor
      # result type — `empty : Vector(a', Z)` unified against the domain
      # `Vector(Nat, ?n)` solves `?n := Z` (and `a' := Nat`). Attempt that solve in
      # the CALLER's `mctx` so the freshly-solved domain metavariable propagates to
      # the rest of the call (e.g. `prepend`'s result index). Only a genuinely
      # ambiguous domain — one no argument, including the deferred one, determines —
      # survives with a metavariable and is reported as unsolved. The assembled call
      # is kernel-re-checked by `finish_global_app`, so this inference-order change
      # rests on nothing unsound.
      {mctx, dom_inst} =
        if has_meta?(dom_inst) do
          mctx = solve_deferred_domain(arg, dom_inst, mctx, names, ctx, env)
          {mctx, Unify.zonk(dom_inst, mctx)}
        else
          {mctx, dom_inst}
        end

      if has_meta?(dom_inst) do
        # A deferred LAMBDA whose Π domain a later sibling has now solved, but whose
        # CODOMAIN no argument determines (`(Int) -> ?b`): solve the codomain UNDER
        # the binder by inferring the body. This is the same Miller solve
        # `bidir_app_slot` attempts eagerly — there it fell through because the
        # domain was still `?a` at the time (`try_lambda_meta_pi` requires a meta-free
        # domain), and nothing ever re-offered it. Retrying it HERE is the second half
        # of the postponement: an argument is deferred precisely so a later sibling can
        # solve what it needs, and a lambda needs its DOMAIN, not only its family
        # indices (which is all `solve_deferred_domain` recovers). Without this,
        # `app2(fn(x) -> x + 10, xs)` rejects while `app2(xs, fn(x) -> x + 10)`
        # elaborates — argument ORDER decided typability.
        case try_lambda_meta_pi(arg, dom_inst, mctx, names, ctx, env) do
          {:ok, mctx, lam_term} ->
            {:cont, {:ok, MetaCtx.put_solution(mctx, ph, lam_term)}}

          :fallthrough ->
            {:halt, {:error, {:unsolved_metavariables, :deferred_argument}}}
        end
      else
        case elaborate_expr_checked(arg, dom_inst, names, ctx, env) do
          {:ok, term} -> {:cont, {:ok, MetaCtx.put_solution(mctx, ph, term)}}
          {:error, _} = err -> {:halt, err}
        end
      end
    end)
    |> case do
      {:ok, mctx} -> {:ok, mctx, chosen, args}
      {:error, _} = err -> err
    end
  end

  # Solve a deferred argument's remaining domain metavariables from the argument's
  # OWN constructor, threading `mctx`. When `arg` is a constructor application whose
  # family matches `dom_inst`'s, build the constructor's result-type template over
  # fresh metavariables (mirroring `finish_ctor_app`'s `params ++ args` seed) and
  # unify it against `dom_inst` — this LINKS the template's parameter/index
  # metavariables to whatever `dom_inst` already fixes (and vice versa). The
  # template alone rarely settles everything (`prepend`'s result index is `S(n)`,
  # with `n` still open), so we then process each PRESENT field to solve the rest:
  # infer the field argument and unify its type against the field's expected type
  # (`x : a` fixes the parameter), and when a field cannot infer standalone recurse
  # on it (`xs = empty()` fixes the length index from `empty`'s own `Z`). The result
  # is meta-solving only — `mctx` is mutated in place and the caller re-zonks
  # `dom_inst`; the actual argument term is still built by the ordinary
  # checking-mode elaboration once the domain is concrete, and the whole call is
  # kernel-re-checked by `finish_global_app`, so nothing unsound rests on this.
  # Additive and best-effort: a non-constructor argument, a foreign family, or a
  # unification failure (a genuine index mismatch like `empty : …Z` at `…S(n)`)
  # leaves `mctx` untouched, so a genuinely ambiguous domain still rejects.
  defp solve_deferred_domain({:function_call, meta, cargs}, dom_inst, mctx, names, ctx, env) do
    with name when is_binary(name) <- Keyword.get(meta, :name),
         cname = resolve_ctor_key(env, String.to_atom(name)),
         ctor when not is_nil(ctor) <- Inductive.get_ctor(env, cname),
         family when not is_nil(family) <- Inductive.ctor_family(env, cname),
         pc = length(Inductive.param_telescope(env, family) || []),
         {mctx_try, seed} <- fresh_seed(mctx, pc + length(ctor.args)),
         params = Enum.map(Map.get(ctor, :result_params, []), &Subst.instantiate(&1, seed)),
         indices = Enum.map(ctor.result_indices, &Subst.instantiate(&1, seed)),
         {:ok, mctx_try} <- unify_data_components(family, params, indices, dom_inst, mctx_try, env) do
      solve_ctor_present_fields(ctor, cargs, seed, pc, mctx_try, names, ctx, env)
    else
      _ -> mctx
    end
  end

  defp solve_deferred_domain(_arg, _dom_inst, mctx, _names, _ctx, _env), do: mctx

  # Simultaneous (component-wise) unification of a constructor's result-type
  # template `{:data, family, params, indices}` against a domain `dom_inst`,
  # tolerating a stuck component. A whole-tuple `Unify.unify` is all-or-nothing:
  # a single index that cannot unify NOW aborts every other component's solving.
  # For a constructor whose result carries a COMPUTED index — `ATimes : Acc(l,m1)
  # -> Acc(r,m2) -> Acc(PTimes(l,r), add(m1,m2))` — the `add(m1',m2')` index is a
  # stuck neutral at deferral time (its scrutinee `m1'` is an unsolved seed meta),
  # so whole-tuple unification against `Acc(PTimes(PA(?a),…), S(Z))` fails and the
  # caller's `solve_ctor_present_fields` never runs — leaving the sibling implicit
  # `?a` (which the STRUCTURAL first index and the present field `AAtomA : …PA(TA)…`
  # jointly determine) unsolved. Unifying each param/index pair independently and
  # KEEPING the solutions from the pairs that succeed lets the structural component
  # solve what it can while the stuck one is simply skipped; the present fields then
  # finish the job, and the computed index reduces once its arguments are known.
  #
  # Meta-solving only, and best-effort: a failing pair leaves `mctx` untouched (never
  # fabricates a solution), and the assembled call is kernel-re-checked by
  # `finish_global_app`, so a genuinely ambiguous domain still rejects and nothing
  # unsound rests on the partial solve. Family/arity mismatch is a real error, not a
  # stuck component, so it returns `:mismatch` and the caller keeps the original mctx.
  defp unify_data_components(family, params, indices, dom_inst, mctx, env) do
    case dom_inst do
      {:data, ^family, dparams, dindices}
      when length(dparams) == length(params) and length(dindices) == length(indices) ->
        mctx =
          Enum.zip(params ++ indices, dparams ++ dindices)
          |> Enum.reduce(mctx, fn {a, b}, m ->
            case Unify.unify(a, b, m, env) do
              {:ok, m2} -> m2
              {:error, _} -> m
            end
          end)

        {:ok, mctx}

      _ ->
        :mismatch
    end
  end

  # Allocate `n` fresh metavariables from `mctx`, returning the updated context and
  # the `[{:meta, id}]` seed frame.
  defp fresh_seed(mctx, n) do
    Enum.reduce(1..n//1, {mctx, []}, fn _, {m, acc} ->
      {m, id} = MetaCtx.fresh(m)
      {m, acc ++ [{:meta, id}]}
    end)
  end

  # Walk a constructor's fields, solving the seed's remaining metavariables from the
  # PRESENT field arguments. Mirrors `check_ctor_args`' framing exactly: each field
  # type is instantiated over `params ++ (field values so far)` — a growing frame
  # whose LENGTH the de Bruijn indices depend on, so the seed value of every field
  # (the pinned metavariable for an erased index, the elaborated term for a present
  # one) is threaded through `acc`. Erased fields carry no surface argument (their
  # value is a seed metavariable a present field determines); a present field whose
  # instantiated type still bears a metavariable is solved from its argument
  # (inferred and unified, or recursively solved when it cannot infer standalone —
  # `xs = empty()` fixing the length index from `empty`'s own `Z`). Best-effort:
  # any failure returns the `mctx` reached so far, which the caller re-zonks and
  # gates, so a genuinely ambiguous domain still rejects.
  defp solve_ctor_present_fields(ctor, arg_asts, seed, pc, mctx, names, ctx, env) do
    params = Enum.take(seed, pc)
    slots = Enum.zip([ctor.args, ctor.quantities, Inductive.plicities_of(ctor)])
    solve_fields(slots, arg_asts, seed, pc, params, [], mctx, names, ctx, env)
  end

  defp solve_fields([], _asts, _seed, _pc, _params, _acc, mctx, _names, _ctx, _env), do: mctx

  # IMPLICIT slot (erased index OR relevant `{k:T}`): non-positional, its value is
  # the seed metavariable a present field determines. Keyed off plicity, not
  # quantity — a relevant implicit is ω yet still seeded, not consumed.
  defp solve_fields([{{_fn, _ft}, _q, :implicit} | slots], asts, seed, pc, params, acc, mctx, names, ctx, env) do
    val = seed |> Enum.at(pc + length(acc)) |> Unify.zonk(mctx)
    solve_fields(slots, asts, seed, pc, params, [val | acc], mctx, names, ctx, env)
  end

  defp solve_fields([{{_fn, _ft}, _q, :explicit} | _slots], [], _seed, _pc, _params, _acc, mctx, _names, _ctx, _env),
    do: mctx

  defp solve_fields([{{_fn, ftype}, _q, :explicit} | slots], [arg | rest], seed, pc, params, acc, mctx, names, ctx, env) do
    ftype_inst = ftype |> Subst.instantiate(params ++ Enum.reverse(acc)) |> Unify.zonk(mctx)

    {mctx, val} = solve_field(arg, ftype_inst, mctx, names, ctx, env)
    solve_fields(slots, rest, seed, pc, params, [val | acc], mctx, names, ctx, env)
  end

  # Solve a present field's expected type from its argument and return an updated
  # `mctx` and a value term for the frame. When the type is concrete, check the
  # argument; when it still bears a metavariable, infer the argument and unify its
  # type against the expected type (or, if it cannot infer standalone, recursively
  # solve it from its own constructor and then check against the now-concrete type).
  # A field that cannot be elaborated contributes the expected type's own shape as an
  # opaque placeholder value — enough to keep later fields' frames aligned; the
  # caller's re-zonk and the kernel re-check gate correctness regardless.
  defp solve_field(arg, ftype_inst, mctx, names, ctx, env) do
    cond do
      not has_meta?(ftype_inst) ->
        term =
          case elaborate_expr_checked(arg, ftype_inst, names, ctx, env) do
            {:ok, term} -> term
            {:error, _} -> ftype_inst
          end

        {mctx, term}

      true ->
        case elaborate_expr_typed(arg, names, ctx, env) do
          {:ok, term, ty} ->
            ty_term = Quote.reify(ty, Context.length(ctx))

            case Unify.unify(ftype_inst, ty_term, mctx, env) do
              {:ok, mctx} -> {mctx, term}
              {:error, _} -> {mctx, term}
            end

          {:error, _} ->
            mctx = solve_deferred_domain(arg, ftype_inst, mctx, names, ctx, env)
            concrete = Unify.zonk(ftype_inst, mctx)

            term =
              if has_meta?(concrete) do
                concrete
              else
                case elaborate_expr_checked(arg, concrete, names, ctx, env) do
                  {:ok, term} -> term
                  {:error, _} -> concrete
                end
              end

            {mctx, term}
        end
    end
  end

  # Bidirectional checking-mode constructor elaboration. It is the primary path
  # whenever a constructor has an expected result type: rather than infer each
  # argument independently, it solves the family parameters from the *expected*
  # type — the constructor's
  # result applied to fresh metavariables, unified against `expected_core` — and
  # then *checks* each present argument against its field type instantiated with
  # the solved parameters (and the arguments checked so far, mirroring
  # `solve_arg`'s frame). The assembled constructor is still kernel-re-checked by
  # the caller, so this can only ever accept a term the kernel independently
  # accepts. The caller retains inference as a compatibility fallback when this
  # goal-directed pass is inapplicable.
  defp elaborate_ctor_app_bidirectional(env, cname, arg_asts, names, ctx, expected_core)
       when expected_core != nil do
    # Constructor result pinning must see through reducible aliases before it
    # seeds implicit fields from the goal. Otherwise a nullary indexed
    # constructor nested in a dependent field is inferred without its hidden
    # indices and fails as `:unsolved_metavariables` (or later `:ctor_arity`),
    # even though the aliased goal determines them completely.
    expected_core = Kernel.normalize(ctx, expected_core)
    ctor = Inductive.get_ctor(env, cname)
    family = Inductive.ctor_family(env, cname)
    param_tele = Inductive.param_telescope(env, family) || []
    pc = length(param_tele)

    cond do
      is_nil(ctor) or is_nil(family) ->
        {:error, {:unknown_constructor, cname}}

      # Guard-ordered AFTER the nil check: the ctor's plicities are only reached
      # once `ctor` is known non-nil (an unknown ctor would otherwise crash here
      # before the graceful error above could fire). Positional arg count is the
      # number of EXPLICIT slots — an implicit `{k:T}` is solved, not passed.
      Enum.count(Inductive.plicities_of(ctor), &(&1 == :explicit)) != length(arg_asts) ->
        constructor_arity_error(ctor, cname, arg_asts)

      true ->
        # Fresh metas for the params ++ every argument (including erased index
        # fields), so the constructor's result type — which references that whole
        # frame — can be built and pinned against the goal before any argument is
        # known. Pinning solves the parameters and the erased indices; the present
        # fields are then checked against their now-concrete types.
        {mctx, seed} = fresh_seed(MetaCtx.new(), pc + length(ctor.args))

        params = Enum.map(Map.get(ctor, :result_params, []), &Subst.instantiate(&1, seed))
        indices = Enum.map(ctor.result_indices, &Subst.instantiate(&1, seed))

        result_term = {:data, family, params, indices}

        slots =
          [ctor.args, ctor.quantities, Inductive.plicities_of(ctor)]
          |> Enum.zip()
          |> Enum.with_index()
          |> Enum.map(fn {{{_fn, ftype}, q, p}, i} -> {i, ftype, q, p} end)

        case Unify.unify(result_term, expected_core, mctx, env) do
          {:ok, mctx} ->
            solved_params = seed |> Enum.take(pc) |> Enum.map(&Unify.zonk(&1, mctx))

            if Enum.any?(solved_params, &has_meta?/1) do
              {:error, {:unsolved_parameters, cname}}
            else
              check_ctor_args(slots, arg_asts, seed, pc, solved_params, [], mctx, names, ctx, env, cname, [])
            end

          {:error, _} ->
            # The full result-pin failed. It may fail only because a COMPUTED result
            # index is stuck — `ATimes : … -> Acc(PTimes(l,r), add(m1,m2))` checked
            # against `Acc(…, S(Z))`, where `add(m1,m2)` cannot reduce until the field
            # `AAtomA` fixes `m1`. Rather than reject, pin the indices that DO unify
            # (structural ones — `PTimes(l,r)`, solving `l`/`r`) and DEFER the stuck
            # equations. The deferred equations are retried inside the field-resolution
            # fixpoint (`resolve_ctor_fields`): once a sibling field solves their metas
            # the computed index reduces (`add(S(Z),m2)` → `S(m2)`) and solves the rest.
            # This is Idris's simultaneous-unification behaviour, scoped to the one
            # constructor: field checks and result-index constraints solve as ONE
            # constraint set with postponement. The assembled term is still
            # kernel-re-checked by the caller, so nothing unsound is admitted — a
            # deferred equation that stays unsatisfiable surfaces as an unsolved
            # metavariable or a kernel type error, never silent acceptance.
            case partial_pin_result(result_term, expected_core, mctx, env) do
              :mismatch ->
                {:error,
                 {:constructor_result_mismatch, %{constructor: cname, actual: result_term, expected: expected_core}}}

              :not_applicable ->
                {:error, :constructor_result_not_applicable}

              {mctx, deferred} ->
                # Params that pinned structurally are passed for the de Bruijn frame;
                # any still-open param is caught downstream (unsolved metavariable /
                # kernel re-check), never silently accepted.
                partial_params = seed |> Enum.take(pc) |> Enum.map(&Unify.zonk(&1, mctx))
                check_ctor_args(slots, arg_asts, seed, pc, partial_params, [], mctx, names, ctx, env, cname, deferred)
            end
        end
    end
  end

  defp attach_constructor_result_mismatch({:error, {:source_context, reason, existing}}, details, meta, args) do
    {:error, {:source_context, reason, Map.merge(constructor_result_mismatch_context(details, meta, args), existing)}}
  end

  defp attach_constructor_result_mismatch({:error, reason}, details, meta, args) do
    {:error, {:source_context, reason, constructor_result_mismatch_context(details, meta, args)}}
  end

  defp attach_nested_constructor_context(
         {:error, {:unsolved_metavariables, name} = reason},
         args,
         owner
       ) do
    case nested_constructor_site(args, name) do
      {argument_index, expression} ->
        span = surface_expression_span(expression)

        {:error,
         {:source_context, reason,
          %{
            line: span && span.start_line,
            column: span && span.start_column,
            length: span && max(1, span.end_column - span.start_column),
            span: span,
            checking: owner,
            expression_category: :function_call,
            expectation_origin: :constructor_argument,
            argument_index: argument_index
          }}}

      nil ->
        {:error, reason}
    end
  end

  defp attach_nested_constructor_context(error, _args, _owner), do: error

  defp nested_constructor_site(args, target) do
    target = target |> Cure.Elab.Name.base() |> to_string()

    args
    |> Enum.with_index()
    |> Enum.find_value(fn {argument, index} ->
      case nested_named_call(argument, target) do
        nil -> nil
        expression -> {index, expression}
      end
    end)
  end

  defp nested_named_call({:function_call, meta, children} = expression, target)
       when is_list(meta) do
    if Keyword.get(meta, :name) |> to_string() == target do
      expression
    else
      Enum.find_value(children, &nested_named_call(&1, target))
    end
  end

  defp nested_named_call({_tag, _meta, children}, target) when is_list(children),
    do: Enum.find_value(children, &nested_named_call(&1, target))

  defp nested_named_call(children, target) when is_list(children),
    do: Enum.find_value(children, &nested_named_call(&1, target))

  defp nested_named_call(_expression, _target), do: nil

  defp constructor_result_mismatch_context(details, meta, args) do
    info = Cure.MetaAST.Metadata.source_info(meta)

    %{
      span: info && info.whole,
      application_span: info && info.whole,
      callee_span: info && info.callee,
      argument_spans: Enum.map(args, &surface_expression_span/1),
      constructor: Map.get(details, :constructor),
      constructor_actual_type: Map.get(details, :actual),
      constructor_expected_type: Map.get(details, :expected),
      constructor_result_mismatch: true,
      expectation_origin: :annotation,
      expression_category: :constructor_application
    }
  end

  # Assemble a constructor's argument list against the solved parameters and the
  # binder-solved erased indices. Walks every field: an erased field takes its
  # value from the pinned metavariable (an index the expected type determined); a
  # present field is checked against its field type instantiated with the
  # parameters and every earlier field value (the same `params ++ fields` frame the
  # de Bruijn layout uses). The erased field values are kept in the assembled
  # `{:ctor, …}`, matching `finish_ctor_app`.
  defp check_ctor_args(slots, arg_asts, seed, pc, params, _acc0, mctx, names, ctx, env, cname, deferred) do
    # Idris-style DEFERRAL (TTImp.Elab.App `checkRestApp`/`checkRtoL`): a present field whose
    # instantiated type still carries a metavariable is POSTPONED, its siblings resolved first —
    # which solves that metavariable — and it is then checked. Iterated to a fixpoint so any
    # dependency order works. Erased index slots seed the assembly with their goal-pinned
    # metavariable and are re-zonked at the end; positions are kept so the de Bruijn frame stays
    # correct regardless of resolution order.
    # Positional-vs-not keys off PLICITY: EXPLICIT slots consume the surface
    # arguments; IMPLICIT slots (erased index OR relevant `{k:T}`) seed from their
    # goal-pinned metavariable and are solved by unification. The retained value
    # (relevant implicit) vs dropped one (erased) is a quantity concern erasure
    # handles later — both flow identically here.
    case resolve_ctor_argument_values(slots, arg_asts, seed, pc, params, mctx, names, ctx, env, cname, deferred) do
      {:ok, vals, _mctx} ->
        {:ok, {:ctor, cname, vals}}

      {:error, _} = err ->
        err
    end
  end

  defp resolve_ctor_argument_values(slots, arg_asts, seed, pc, params, mctx, names, ctx, env, cname, deferred) do
    args_by_pos =
      slots
      |> Enum.filter(fn {_i, _ft, _q, p} -> p == :explicit end)
      |> Enum.map(&elem(&1, 0))
      |> Enum.zip(arg_asts)
      |> Map.new()

    acc0 = for {i, _ft, _q, :implicit} <- slots, into: %{}, do: {i, Enum.at(seed, pc + i)}
    pending = for {i, ft, _q, :explicit} <- slots, do: {i, ft}

    case resolve_ctor_fields(pending, acc0, args_by_pos, seed, pc, params, mctx, names, ctx, env, cname, deferred, %{}) do
      {:ok, acc_map, mctx} ->
        vals = for i <- 0..(length(slots) - 1)//1, do: Unify.zonk(Map.fetch!(acc_map, i), mctx)

        if Enum.any?(vals, &has_meta?/1),
          do: {:error, {:unsolved_index, cname}},
          else: {:ok, vals, mctx}

      {:error, _} = err ->
        err
    end
  end

  # The retry queue is indexed by blocker metavariables. A successful field wakes
  # only the fields that depend on the changed constraint (plus fields whose
  # preceding frame value changed), instead of restarting every pending field.
  defp resolve_ctor_fields(pending, acc_map, args, seed, pc, params, mctx, names, ctx, env, cname, deferred, attempted) do
    pending_map = Map.new(pending)
    slot_count = max(length(seed) - pc, 0)

    prefix_values =
      for i <- 0..(slot_count - 1)//1 do
        Map.get(acc_map, i, Enum.at(seed, pc + i))
      end

    state = %{
      pending: pending_map,
      field_types: pending_map,
      seed_fields: acc_map,
      args: args,
      seed: seed,
      pc: pc,
      params: params,
      names: names,
      ctx: ctx,
      env: env,
      cname: cname,
      declaration: Env.current_def(env),
      deferred_equations: deferred,
      mctx: mctx,
      queue: Map.keys(pending_map) |> Enum.sort(),
      acc_map: acc_map,
      attempted: attempted,
      blocker_index: %{},
      field_blockers: %{},
      fallback_fields: MapSet.new(),
      fallback_attempts: %{},
      prefix_view: Prefix.new(prefix_values),
      value_revision: 0
    }

    resolve_ctor_fields_state(state)
  end

  defp resolve_ctor_fields_state(state) do
    old_mctx = state.mctx
    {mctx, deferred, deferred_prog} = retry_deferred(state.deferred_equations, state.mctx, state.env)

    state =
      state
      |> Map.put(:mctx, mctx)
      |> Map.put(:deferred_equations, deferred)
      |> wake_constructor_fields(changed_meta_ids(old_mctx, mctx))
      |> then(fn state -> if deferred_prog, do: enqueue_all_pending(state), else: state end)

    case resolve_ctor_field_queue(state) do
      {:error, _} = error ->
        error

      {state, progress} ->
        cond do
          map_size(state.pending) == 0 ->
            {:ok, state.acc_map, state.mctx}

          progress or state.queue != [] ->
            resolve_ctor_fields_state(state)

          true ->
            {:error,
             {:unsolved_field_type,
              %{
                constructor: state.cname,
                fields: Map.keys(state.pending) |> Enum.sort(),
                revision: MetaCtx.revision(state.mctx),
                field_diagnostics:
                  state.pending
                  |> Map.keys()
                  |> Enum.sort()
                  |> Enum.map(&constructor_field_diagnostic(state, &1))
              }}}
        end
    end
  end

  defp resolve_ctor_field_queue(%{queue: []} = state), do: {state, false}

  defp resolve_ctor_field_queue(state) do
    [i | queue] = state.queue
    state = %{state | queue: queue}

    if not Map.has_key?(state.pending, i) do
      resolve_ctor_field_queue(state)
    else
      if Map.get(state.fallback_attempts, i, 0) >= @constructor_fallback_retry_limit do
        {:error,
         {:unsolved_field_type,
          constructor_field_diagnostic(state, i,
            fallback_attempts: Map.get(state.fallback_attempts, i, 0),
            fallback_limit_exceeded: true
          )}}
      else
        ftype = Map.fetch!(state.field_types, i)
        frame = Frame.new(state.params, state.prefix_view, i, &Unify.zonk(&1, state.mctx))
        ftype_inst = ftype |> Subst.instantiate(frame) |> Unify.zonk(state.mctx)
        arg = Map.fetch!(state.args, i)

        fingerprint =
          {state.value_revision, field_fingerprint(ftype_inst, state.mctx), surface_attempt_fingerprint(arg)}

        if Map.get(state.attempted, i) == fingerprint do
          CallAttemptProfile.increment(:constructor_field_retry_skipped)
          resolve_ctor_field_queue(state)
        else
          state = %{state | attempted: Map.put(state.attempted, i, fingerprint)}

          case try_ctor_field(arg, ftype_inst, state.mctx, state.names, state.ctx, state.env) do
            {:blocked, blockers} ->
              state = register_field_blockers(state, i, blockers)
              resolve_ctor_field_queue(state)

            {:error, reason} ->
              {:error, reason}

            {:ok, term, mctx2} ->
              state = resolve_ctor_field(state, i, term)
              # A later field may depend on this position through its de-Bruijn
              # frame without mentioning a metavariable at all. Its blocker set
              # is therefore empty until this value is present; enqueue the
              # suffix explicitly when a preceding field resolves.
              state =
                enqueue_constructor_fields(
                  state,
                  Enum.filter(Map.keys(state.pending), &(&1 > i))
                )

              state =
                state
                |> Map.put(:mctx, mctx2)
                |> wake_constructor_fields(changed_meta_ids(state.mctx, mctx2))

              case resolve_ctor_field_queue(state) do
                {state, _progress} -> {state, true}
                error -> error
              end
          end
        end
      end
    end
  end

  defp try_ctor_field(arg, ftype_inst, mctx, names, ctx, env) do
    if has_meta?(ftype_inst) do
      case try_infer_field(arg, ftype_inst, mctx, names, ctx, env) do
        {:ok, term, _typed_type, mctx2} ->
          {:ok, term, mctx2}

        {:blocked, blockers, _attempt_state} ->
          CallAttemptProfile.increment(:constructor_field_retries)
          {:blocked, blockers}

        {:error, reason} ->
          {:error, reason}
      end
    else
      case elaborate_expr_checked(arg, ftype_inst, names, ctx, env) do
        {:ok, term} -> {:ok, term, mctx}
        {:error, _} = error -> error
      end
    end
  end

  defp resolve_ctor_field(state, i, term) do
    state
    |> Map.update!(:pending, &Map.delete(&1, i))
    |> Map.update!(:acc_map, &Map.put(&1, i, term))
    |> Map.update!(:prefix_view, &Prefix.put(&1, i, term))
    |> Map.update!(:value_revision, &(&1 + 1))
    |> remove_field_blockers(i)
  end

  defp register_field_blockers(state, i, blockers) do
    state = remove_field_blockers(state, i)
    blockers = Enum.uniq(blockers)

    if blockers == [] do
      %{state | fallback_fields: MapSet.put(state.fallback_fields, i)}
    else
      index =
        Enum.reduce(blockers, state.blocker_index, fn id, index ->
          Map.update(index, id, MapSet.new([i]), &MapSet.put(&1, i))
        end)

      %{state | blocker_index: index, field_blockers: Map.put(state.field_blockers, i, blockers)}
    end
  end

  defp remove_field_blockers(state, i) do
    blockers = Map.get(state.field_blockers, i, [])

    index =
      Enum.reduce(blockers, state.blocker_index, fn id, index ->
        case Map.get(index, id) do
          nil ->
            index

          fields ->
            fields = MapSet.delete(fields, i)
            if MapSet.size(fields) == 0, do: Map.delete(index, id), else: Map.put(index, id, fields)
        end
      end)

    %{
      state
      | blocker_index: index,
        field_blockers: Map.delete(state.field_blockers, i),
        fallback_fields: MapSet.delete(state.fallback_fields, i)
    }
  end

  defp wake_constructor_fields(state, ids) do
    waiting =
      Enum.flat_map(Enum.uniq(ids), fn id ->
        state.blocker_index |> Map.get(id, MapSet.new()) |> MapSet.to_list()
      end)

    fallback = if ids == [], do: [], else: MapSet.to_list(state.fallback_fields)
    waiting = Enum.uniq(waiting ++ fallback)
    CallAttemptProfile.increment(:constructor_field_wakeups, length(waiting))

    state =
      Enum.reduce(waiting, state, fn field, state ->
        fallback? = MapSet.member?(state.fallback_fields, field)

        state = remove_field_blockers(state, field)

        if fallback? do
          Map.update!(state, :fallback_attempts, &Map.update(&1, field, 1, fn attempts -> attempts + 1 end))
        else
          state
        end
      end)

    enqueue_constructor_fields(state, waiting)
  end

  defp enqueue_all_pending(state), do: enqueue_constructor_fields(state, Map.keys(state.pending))

  defp enqueue_constructor_fields(state, indices) do
    queue =
      (state.queue ++ Enum.filter(indices, &Map.has_key?(state.pending, &1)))
      |> Enum.uniq()
      |> Enum.sort()

    %{state | queue: queue}
  end

  defp changed_meta_ids(old, new) do
    old_revision = MetaCtx.revision(old)
    new_revision = MetaCtx.revision(new)

    if new_revision >= old_revision do
      MetaCtx.changed_ids_since(new, old_revision)
    else
      ids = MapSet.union(MapSet.new(Map.keys(old.solutions)), MapSet.new(Map.keys(new.solutions)))
      Enum.filter(MapSet.to_list(ids), fn id -> MetaCtx.solution(old, id) != MetaCtx.solution(new, id) end)
    end
  end

  defp surface_attempt_fingerprint(arg),
    do: :erlang.phash2(Cure.MetaAST.Metadata.semantic_key(arg))

  defp constructor_field_diagnostic(state, field, extra \\ []) do
    arg = Map.get(state.args, field)
    field_type = Map.get(state.field_types, field)

    instantiated =
      if field_type do
        frame = Frame.new(state.params, state.prefix_view, field, &Unify.zonk(&1, state.mctx))
        field_type |> Subst.instantiate(frame) |> Unify.zonk(state.mctx)
      end

    blockers = Map.get(state.field_blockers, field, [])

    %{
      constructor: state.cname,
      field: field,
      field_span: surface_expression_span(arg),
      surface_argument: arg,
      field_type: field_type,
      instantiated_field_type: instantiated,
      blocker_ids: blockers,
      blocker_assignments: Map.new(blockers, &{&1, MetaCtx.solution(state.mctx, &1)}),
      revision: MetaCtx.revision(state.mctx),
      attempt_count: Map.get(state.fallback_attempts, field, 0),
      declaration: Map.get(state, :declaration),
      macro_provenance: surface_expression_provenance(arg)
    }
    |> Map.merge(Map.new(extra))
  end

  defp surface_expression_provenance(arg) do
    case Cure.MetaAST.Metadata.source_info(arg) do
      %{provenance: provenance} when is_list(provenance) and provenance != [] -> provenance
      _ -> nil
    end
  end

  # Pin a constructor's result type against the goal COMPONENT-WISE, tolerating a
  # stuck computed index. Each result parameter/index is unified against the
  # corresponding goal component independently; the ones that unify refine `mctx`,
  # and the ones that don't (a computed index like `add(m1,m2)` whose metas aren't
  # yet known) are returned as DEFERRED `{actual, expected}` equations for the field
  # fixpoint to retry. Returns `:mismatch` when the goal is not the same data family
  # at the same arity — a genuine result-type mismatch, not a solving-order issue.
  defp partial_pin_result({:data, fam, ap, ai}, {:data, fam, ep, ei}, mctx, env)
       when length(ap) == length(ep) and length(ai) == length(ei) do
    Enum.zip(ap ++ ai, ep ++ ei)
    |> Enum.reduce_while({mctx, []}, fn {actual, expected}, {m, deferred} ->
      case Unify.unify(actual, expected, m, env) do
        {:ok, m2} ->
          {:cont, {m2, deferred}}

        {:error, _} ->
          if definite_constructor_result_clash?(Unify.zonk(actual, m), Unify.zonk(expected, m)) do
            {:halt, :mismatch}
          else
            {:cont, {m, [{actual, expected} | deferred]}}
          end
      end
    end)
  end

  # A goal with a different outer type is not an indexed-result clash. Let the
  # original inference/checking error explain that call; this specialized path is
  # only for constructors whose own family matches the expected family.
  defp partial_pin_result(_actual, _expected, _mctx, _env), do: :not_applicable

  defp definite_constructor_result_clash?({:data, left, _, _}, {:data, right, _, _}),
    do: left != right

  defp definite_constructor_result_clash?({:ctor, left, _}, {:ctor, right, _}),
    do: left != right

  defp definite_constructor_result_clash?({:global, left}, {:global, right}),
    do: left != right

  defp definite_constructor_result_clash?({:global, left}, {:data, right, _, _}),
    do: left != right

  defp definite_constructor_result_clash?({:data, left, _, _}, {:global, right}),
    do: left != right

  defp definite_constructor_result_clash?(left, right)
       when is_tuple(left) and is_tuple(right) and tuple_size(left) == 1 and tuple_size(right) == 1 do
    primitive_type_head?(elem(left, 0)) and primitive_type_head?(elem(right, 0)) and left != right
  end

  defp definite_constructor_result_clash?(_left, _right), do: false

  defp primitive_type_head?(head),
    do:
      head in [
        :int_type,
        :float_type,
        :string_type,
        :binary_type,
        :atom_type,
        :char_type,
        :type
      ]

  # Retry each deferred result-index equation after zonking both sides. Solved
  # equations are dropped; unsolved ones are kept for a later sweep. Returns the
  # refined context, the still-deferred equations, and whether any were discharged
  # (progress, which keeps the field fixpoint iterating).
  defp retry_deferred(deferred, mctx, env) do
    Enum.reduce(deferred, {mctx, [], false}, fn {lhs, rhs}, {m, still, prog} ->
      # A deferred equation may be stuck only because its head is a recursive
      # definition.  Use the elaborator's meta-aware WHNF: unlike the ordinary
      # kernel normalizer it treats unsolved metas as opaque neutrals, while
      # still reducing a closed prefix such as `add(S(Z), ?m)` to `S(?m)`.
      # Calling the kernel normalizer here would be invalid because it cannot
      # evaluate elaborator-only `{:meta, id}` terms.
      left = Unify.whnf_meta_aware(lhs, m, env)
      right = Unify.whnf_meta_aware(rhs, m, env)

      case Unify.unify(left, right, m, env) do
        {:ok, m2} -> {m2, still, true}
        {:error, _} -> {m, [{lhs, rhs} | still], prog}
      end
    end)
  end

  defp field_fingerprint(term, mctx) do
    {
      Unify.zonk(term, mctx),
      MetaCtx.revision(mctx),
      term |> meta_ids() |> Enum.sort()
    }
  end

  # Infer an argument independently and unify its type back into `mctx`, solving a field-type
  # metavariable that only this argument determines (e.g. a recursive call whose result type
  # fixes an intermediate index). Returns `:defer` when the argument cannot be inferred in
  # isolation (e.g. a nullary constructor with its own implicit index) — it is retried once its
  # field type becomes concrete.
  defp try_infer_field(arg, ftype_inst, mctx, names, ctx, env) do
    CallAttemptProfile.increment(:constructor_field_attempts)

    # Do not consult the ordinary constructor-attempt cache here. Its key is
    # `{constructor, surface_args}` and deliberately omits the expected field
    # type. A nested constructor can therefore have been blocked once against
    # an unresolved `Acc(?p, ?n)` and later become solvable against
    # `Acc(PStar(PA(TA)), ?n)`; reusing the old result would discard precisely
    # the refinement the retry queue just made. The queue's fingerprint already
    # suppresses identical field attempts, so this path remains bounded without
    # conflating distinct expected types.
    cached_block =
      has_meta?(ftype_inst) and
        blocked_constructor_cached?(arg, env) and
        not partially_refined_field?(ftype_inst)

    initial =
      if cached_block do
        CallAttemptProfile.increment(:constructor_field_blocked)
        CallAttemptProfile.increment(:constructor_field_reused)
        {:blocked, [], :cached_constructor}
      else
        try_infer_field_uncached(arg, ftype_inst, mctx, names, ctx, env)
      end

    case initial do
      {:blocked, _blockers, _attempt_state} = blocked ->
        # Inference cannot determine a constructor's own implicit indices when
        # the field goal has already solved some indices but still contains a
        # parent metavariable (`AStar : Acc(PStar(PA(TA)), ?n)`). Propagate the
        # constructor's result template through the partial goal first; this is
        # the same meta-solving pass used for deferred application domains and
        # does not fabricate a value when the families/indices do not match.
        solved =
          if nullary_constructor_call?(arg, env) and partially_refined_field?(ftype_inst),
            do: solve_deferred_domain(arg, ftype_inst, mctx, names, ctx, env),
            else: mctx

        if solved != mctx do
          resolved_type = Unify.zonk(ftype_inst, solved)

          if has_meta?(resolved_type) do
            {:blocked, field_blockers(resolved_type, :deferred_field), :deferred_field}
          else
            case elaborate_expr_checked(arg, resolved_type, names, ctx, env) do
              {:ok, term} ->
                {:ok, term, resolved_type, solved}

              {:error, reason} ->
                {:error, reason}
            end
          end
        else
          blocked
        end

      other ->
        other
    end
  end

  defp try_infer_field_uncached(arg, ftype_inst, mctx, names, ctx, env) do
    with {:ok, term, ty} <- elaborate_expr_typed(arg, names, ctx, env),
         ty_term = Quote.reify(ty, Context.length(ctx)),
         {:ok, mctx2} <- Unify.unify(ftype_inst, ty_term, mctx, env) do
      {:ok, term, ty_term, mctx2}
    else
      {:error, reason} when is_tuple(reason) ->
        if rigid_field_error?(reason) do
          CallAttemptProfile.increment(:constructor_field_hard_failures)
          {:error, reason}
        else
          CallAttemptProfile.increment(:constructor_field_blocked)
          {:blocked, field_blockers(ftype_inst, reason), reason}
        end

      _other ->
        CallAttemptProfile.increment(:constructor_field_blocked)
        {:blocked, field_blockers(ftype_inst, :unknown_field_constraint), :unknown_field_constraint}
    end
  end

  defp partially_refined_field?({:data, _family, params, indices} = type) do
    has_meta?(type) and Enum.any?(params ++ indices, &(not match?({:meta, _}, &1)))
  end

  defp partially_refined_field?(_type), do: false

  defp nullary_constructor_call?({:function_call, meta, args}, env) when is_list(meta) do
    with name when is_binary(name) <- Keyword.get(meta, :name),
         ctor = Inductive.get_ctor(env, resolve_ctor_key(env, String.to_atom(name))),
         true <- not is_nil(ctor) do
      Enum.count(Inductive.plicities_of(ctor), &(&1 == :explicit)) == 0 and args == []
    else
      _ -> false
    end
  end

  defp nullary_constructor_call?(_arg, _env), do: false

  defp field_blockers(ftype_inst, reason) do
    (meta_ids(ftype_inst) ++ meta_ids(reason)) |> Enum.uniq() |> Enum.sort()
  end

  defp meta_ids(term), do: meta_ids(term, MapSet.new()) |> MapSet.to_list()

  defp meta_ids({:meta, id}, ids), do: MapSet.put(ids, id)

  defp meta_ids(term, ids) when is_tuple(term),
    do: term |> Tuple.to_list() |> Enum.reduce(ids, &meta_ids/2)

  defp meta_ids(term, ids) when is_list(term), do: Enum.reduce(term, ids, &meta_ids/2)
  defp meta_ids(_term, ids), do: ids

  defp rigid_field_error?({:source_context, reason, _context}), do: rigid_field_error?(reason)

  defp rigid_field_error?({:index_mismatch, reason}), do: rigid_field_error?(reason)

  defp rigid_field_error?({:cannot_unify, left, right}),
    do: not has_meta?(left) and not has_meta?(right) and definite_constructor_result_clash?(left, right)

  defp rigid_field_error?({:conversion_failure, actual, expected}),
    do:
      not has_meta?(actual) and not has_meta?(expected) and
        definite_constructor_result_clash?(actual, expected)

  defp rigid_field_error?(_reason), do: false

  defp with_constructor_retry_cache(fun) when is_function(fun, 0) do
    AttemptCache.scope(fun)
  end

  defp remember_blocked_constructor(cname, args, result) do
    if match?({:error, _}, result) and blocked_constructor_reason?(elem(result, 1)) do
      AttemptCache.put(:blocked, {cname, args}, true)
    end

    :ok
  end

  defp blocked_constructor_cached?({:function_call, meta, args}, env) when is_list(meta) do
    name = Keyword.get(meta, :name)

    if is_binary(name) do
      key = resolve_ctor_key(env, String.to_atom(name))
      match?({:ok, true}, AttemptCache.get(:blocked, {key, args}))
    else
      false
    end
  end

  defp blocked_constructor_cached?(_arg, _env), do: false

  defp blocked_constructor_reason?({:source_context, reason, _context}),
    do: blocked_constructor_reason?(reason)

  defp blocked_constructor_reason?({:unsolved_metavariables, _}), do: true
  defp blocked_constructor_reason?({:unsolved_index, _}), do: true
  defp blocked_constructor_reason?({:unsolved_field_type, _}), do: true
  defp blocked_constructor_reason?(_), do: false

  # Inference-mode counterpart of `elaborate_ctor_app_bidirectional`, used only as
  # a fallback when up-front inference of a constructor's arguments fails (a nested
  # underdetermined constructor as a bare argument, `Cons(Z(), Nil())`, whose inner
  # `Nil()` no expected type reaches). Elaborates the arguments left to right,
  # solving the family parameters from the ones that infer (`Z() : Nat` fixes `a`)
  # and *checking* those that do not against their now-concrete field type
  # (`Nil()` against `Lst(Nat)`). The resulting argument/type pairs feed the
  # ordinary `elaborate_ctor_app`, which re-derives parameters and result type, so
  # nothing new is trusted. Unlike the original all-present-only fallback, this
  # uses the same complete constructor slot frame as checking mode: implicit and
  # erased slots receive metas, explicit fields are solved to a fixpoint, and
  # blocked fields are retried after their siblings refine the frame. This is the
  # application strategy used by Idris (`checkRtoL`), Lean (result propagation +
  # postponed terms), and Agda (blocked argument constraints).
  defp elaborate_ctor_app_infer_bidirectional(env, cname, arg_asts, names, ctx) do
    ctor = Inductive.get_ctor(env, cname)
    family = Inductive.ctor_family(env, cname)
    param_tele = Inductive.param_telescope(env, family) || []
    pc = length(param_tele)

    cond do
      is_nil(ctor) or is_nil(family) ->
        {:error, {:unknown_constructor, cname}}

      Enum.count(Inductive.plicities_of(ctor), &(&1 == :explicit)) != length(arg_asts) ->
        constructor_arity_error(ctor, cname, arg_asts)

      true ->
        {mctx, seed} = fresh_seed(MetaCtx.new(), pc + length(ctor.args))
        params = Enum.take(seed, pc)

        slots =
          [ctor.args, ctor.quantities, Inductive.plicities_of(ctor)]
          |> Enum.zip()
          |> Enum.with_index()
          |> Enum.map(fn {{{_fn, ftype}, q, p}, i} -> {i, ftype, q, p} end)

        case resolve_ctor_argument_values(slots, arg_asts, seed, pc, params, mctx, names, ctx, env, cname, []) do
          {:ok, vals, mctx} ->
            param_vals = params |> Enum.map(&Unify.zonk(&1, mctx))

            if Enum.any?(param_vals, &has_meta?/1) do
              {:error, {:unsolved_parameters, cname}}
            else
              full = param_vals ++ vals
              result_params = Enum.map(Map.get(ctor, :result_params, []), &Subst.instantiate(&1, full))
              result_indices = Enum.map(ctor.result_indices, &Subst.instantiate(&1, full))
              type = Eval.eval({:data, family, result_params, result_indices}, Context.env(ctx))
              {:ok, {:ctor, cname, vals}, type}
            end

          {:error, _} = err ->
            err
        end
    end
  end

  defp validate_constructor_arity(env, cname, args, display_name) do
    case Inductive.get_ctor(env, cname) do
      nil ->
        :ok

      ctor ->
        expected = Enum.count(Inductive.plicities_of(ctor), &(&1 == :explicit))
        actual = length(args)

        if expected == actual,
          do: :ok,
          else: constructor_arity_error(ctor, cname, args, display_name)
    end
  end

  defp constructor_arity_error(ctor, cname, args, display_name \\ nil) do
    {:error,
     {:constructor_arity_mismatch,
      %{
        name: cname,
        display_name: display_name,
        expected: Enum.count(Inductive.plicities_of(ctor), &(&1 == :explicit)),
        actual: length(args)
      }}}
  end

  # A saturated call to a global function with implicit (erased) parameters.
  # Peels the function's Π telescope, pairs each domain with its quantity, and
  # runs the shared `solve_arg` loop: erased slots become fresh metavariables,
  # present slots unify against the supplied arguments. Returns the applied term
  # and its result type (the codomain instantiated with the solved arguments).
  defp elaborate_global_app(env, name, present_args, ctx, expected \\ nil) do
    %{type: pi_type, quantities: quantities} = defn = Env.get_def(env, name)
    {domains, codomain} = peel_pi(pi_type, length(quantities))

    # A global def has no relevant-implicit surface (that is a constructor-index
    # feature), so plicity derives from quantity: erased ⇒ :implicit (meta),
    # else :explicit (positional) — preserving the pre-plicity `solve_arg`
    # behavior now that the slot carries an explicit plicity.
    slot_plicities =
      case Map.get(defn, :plicities) do
        ps when is_list(ps) ->
          ps

        _ ->
          Enum.map(quantities, fn
            :erased -> :implicit
            _ -> :explicit
          end)
      end

    telescope = Enum.zip([Enum.map(domains, &{:_, &1}), quantities, slot_plicities])
    init = {:ok, MetaCtx.new(), [], present_args}

    # GOAL-DIRECTED solving, for an anonymous-union goal only.
    #
    # `solve_arg` receives arguments already elaborated and merely UNIFIES each domain
    # against the argument's inferred type. So for `Std.Map.put(:a, 1, …)` checked at
    # `Map(Atom, Int | Bool)`, the value slot's domain is the still-unsolved implicit
    # `?v`, and unifying it with the argument's `Int` locks `?v := Int`. The codomain
    # is only unified with the goal afterwards (in `finish_global_app`), by which point
    # `Map(Atom, Int)` no longer matches `Map(Atom, Union<Bool|Int>)` — and there is no
    # container covariance to rescue it. The union never got a chance to inject.
    #
    # Implicit (erased) slots come FIRST in the telescope, so their metavariables exist
    # before any present argument is processed. Solving the codomain against the goal at
    # that point pins `?v := Union<Bool|Int>`, and `solve_arg` can then coerce each value
    # into it (see the union clause there). This is how Idris/Agda elaborate an
    # application: the goal flows in before the arguments.
    #
    # GATED on the goal mentioning a generated union family. Doing it for EVERY checked
    # call is the fully Idris-faithful behaviour and is the natural generalisation, but
    # it reorders solving for every call in the language — a broad regression surface
    # that deserves its own change. Gated, no non-union program's inference can differ.
    {erased, rest} = Enum.split_while(telescope, fn {_d, q, _p} -> q == :erased end)

    init =
      if union_goal?(expected) do
        erased
        |> Enum.reduce_while(init, &solve_arg(&1, &2, env, ctx))
        |> solve_codomain_from_goal(codomain, expected, env, rest)
      else
        init
      end

    telescope = if union_goal?(expected), do: rest, else: telescope

    telescope
    |> Enum.reduce_while(init, &solve_arg(&1, &2, env, ctx))
    |> finish_global_app(name, codomain, ctx, env, expected)
  end

  @doc """
  True iff `expected` is a Core type mentioning a generated anonymous-union family.

  `Declarations.elaborate_body/6` uses this to route a union-goal body through CHECK
  mode. Its default is infer, which never threads the declared return type into the
  application — so goal-directed solving (see `elaborate_global_app`) would never see a
  goal, and a value destined for a union member would lock the union's implicit to its
  own type instead.
  """
  @spec union_goal?(term()) :: boolean()
  def union_goal?(nil), do: false

  def union_goal?(term) when is_tuple(term) do
    case term do
      {:data, name, _p, _i} ->
        Cure.Elab.Union.union_family?(name) or
          term |> Tuple.to_list() |> Enum.any?(&union_goal?/1)

      _ ->
        term |> Tuple.to_list() |> Enum.any?(&union_goal?/1)
    end
  end

  def union_goal?(list) when is_list(list), do: Enum.any?(list, &union_goal?/1)
  def union_goal?(_other), do: false

  # Unify the codomain against the goal so goal-determined implicits are solved BEFORE
  # the present arguments are matched. A failure is swallowed: the ordinary path then
  # produces the honest error, and the kernel independently re-checks the assembled
  # term, so this can only SOLVE metavariables — never cause an unsound accept.
  #
  # `chosen` holds only the ERASED prefix, but `Subst.instantiate/2` indexes the codomain
  # against the FULL binder stack — instantiating with a short list mis-indexes and the
  # unify then fails silently, leaving the implicit unsolved (which is the whole bug this
  # exists to fix). So pad to full arity with placeholder metas for the not-yet-processed
  # present slots. They are used only to index the substitution and are discarded: the
  # real arguments are unified against their domains by `solve_arg` as usual.
  defp solve_codomain_from_goal({:ok, mctx, chosen, present}, codomain, expected, env, remaining) do
    {mctx_padded, padded} =
      Enum.reduce(remaining, {mctx, chosen}, fn {{_n, ty}, _q, _p}, {m, acc} ->
        {m, id} = MetaCtx.fresh(m, Subst.instantiate(ty, acc))
        {m, acc ++ [{:meta, id}]}
      end)

    case Unify.unify(Subst.instantiate(codomain, padded), expected, mctx_padded, env) do
      {:ok, mctx2} -> {:ok, mctx2, chosen, present}
      {:error, _} -> {:ok, mctx, chosen, present}
    end
  end

  defp solve_codomain_from_goal({:error, _} = err, _codomain, _expected, _env, _remaining), do: err

  defp peel_pi(type, 0), do: {[], type}

  defp peel_pi({:pi, _g, d, c}, n) do
    {ds, co} = peel_pi(c, n - 1)
    {[d | ds], co}
  end

  defp finish_global_app({:error, _} = err, _name, _cod, _ctx, _env, _expected), do: err

  defp finish_global_app({:ok, _mctx, _chosen, [_ | _]}, _name, _cod, _ctx, _env, _expected),
    do: {:error, :too_many_arguments}

  defp finish_global_app({:ok, mctx, chosen, []}, name, codomain, ctx, env, expected) do
    name = Env.resolve_key(env, env.defs, name)

    # When an expected result type is threaded in from checking mode, unify the
    # instantiated codomain against it BEFORE the `has_meta?` rejection below. This
    # lets an implicit determined by NEITHER argument — only by the expected return
    # type (a phantom parameter, `mk : {a} -> {b} -> a -> Const(a, b)` at
    # `-> Const(Nat, Bool)`) — get solved. The instantiated codomain lives in the
    # caller's frame, the same frame as `expected`, so they unify directly (no
    # shift). A unify failure is swallowed (keep the old mctx) so the honest
    # `:unsolved_metavariables` error is still produced below; the caller's kernel
    # re-check independently gates the assembled term, so this only SOLVES
    # metavariables and cannot cause an unsound accept.
    expected_for_unify =
      if expected != nil do
        case Kernel.normalize(ctx, expected) do
          :fuel_exhausted -> expected
          normalized -> normalized
        end
      end

    mctx =
      if expected_for_unify != nil do
        case Unify.unify(Subst.instantiate(codomain, chosen), expected_for_unify, mctx, env) do
          {:ok, mctx2} -> mctx2
          {:error, _} -> mctx
        end
      else
        mctx
      end

    args = Enum.map(chosen, &Unify.zonk(&1, mctx))

    if Enum.any?(args, &has_meta?/1) do
      {:error, {:unsolved_metavariables, name}}
    else
      term = Enum.reduce(args, {:global, name}, fn a, acc -> {:app, acc, a} end)
      # The instantiated codomain lives in the caller's frame; evaluate it under
      # the caller's environment so its context variables get correct de Bruijn
      # levels (evaluating under `[]` would conflate index and level).
      result_type = Eval.eval(Subst.instantiate(codomain, args), Context.env(ctx))
      {:ok, term, result_type}
    end
  end

  defp has_meta?({:meta, _}), do: true
  defp has_meta?({:data, _n, ps, is}), do: Enum.any?(ps ++ is, &has_meta?/1)
  defp has_meta?({:ctor, _n, args}), do: Enum.any?(args, &has_meta?/1)
  defp has_meta?({:app, f, x}), do: has_meta?(f) or has_meta?(x)
  defp has_meta?({:pi, _g, d, c}), do: has_meta?(d) or has_meta?(c)
  defp has_meta?({:lam, _g, d, b}), do: has_meta?(d) or has_meta?(b)
  defp has_meta?({:let, _g, t, v, b}), do: has_meta?(t) or has_meta?(v) or has_meta?(b)

  defp has_meta?({:case, s, m, branches}),
    do: has_meta?(s) or has_meta?(m) or Enum.any?(branches, fn {_ctor, _arity, body} -> has_meta?(body) end)

  defp has_meta?({:effect_type, inner}), do: has_meta?(inner)
  defp has_meta?({:effect_pure, value}), do: has_meta?(value)
  defp has_meta?({:effect_bind, effect, continuation}), do: has_meta?(effect) or has_meta?(continuation)
  defp has_meta?(_), do: false

  # -- parameters / binders ---------------------------------------------------

  defp elaborate_params([], _scope, _env), do: {:ok, []}

  defp elaborate_params([{:param, pmeta, pname} | rest], scope, env) do
    with {:ok, ptype} <- elaborate_type(Keyword.fetch!(pmeta, :type), scope, env),
         {:ok, more} <- elaborate_params(rest, [pname | scope], env) do
      {:ok, [{pname, ptype} | more]}
    end
  end

  # Wrap a Core body in λ's (or Π's) over the parameter telescope, p0 outermost.
  # Same shape as `Declarations.wrap_binders/3`: the binder tuple is assembled
  # from a TAG, invisible to any textual migration. Grade threaded explicitly.
  defp wrap(tag, tele, body) do
    g = Cure.Core.Grade.unrestricted()
    Enum.reduce(Enum.reverse(tele), body, fn {_name, type}, acc -> {tag, g, type, acc} end)
  end

  defp single_body([expr]), do: expr
  defp single_body(expr), do: expr

  # -- expressions ------------------------------------------------------------

  @doc false
  def elaborate_expr({:variable, _meta, "Type"}, _scope, _env), do: {:ok, {:type, 0}}

  def elaborate_expr({:variable, meta, name}, scope, env) do
    case Enum.find_index(scope, &(&1 == name)) do
      nil ->
        case resolve_free(name, env) do
          {:error, reason} -> {:error, attach_variable_context(reason, meta, name)}
          result -> result
        end

      index ->
        {:ok, {:var, index}}
    end
  end

  def elaborate_expr({:function_call, meta, args}, scope, env)
      when is_list(meta) do
    if Keyword.get(meta, :record) do
      with {:ok, positional} <- desugar_record_construction(meta, args, env) do
        elaborate_expr(positional, scope, env)
      end
    else
      elaborate_named_call_scoped(meta, args, scope, env)
    end
  end

  def elaborate_expr({:unsafe_expression, meta, _children}, _scope, _env),
    do: {:error, {:unsafe_call_required, %{span: Keyword.get(meta, :unsafe_span)}}}

  def elaborate_expr({:record_update, meta, children}, scope, env) do
    with {:ok, positional} <- desugar_record_update(meta, children, env) do
      elaborate_expr(positional, scope, env)
    end
  end

  # Pair introduction `%[a, b]` in the scope-based term builder (function
  # arguments and other sub-terms). Emits the builtin Sigma ctor `mk_pair`; its Σ
  # type is derived by `Kernel.infer` on the enclosing application, which checks the
  # ctor against the callee's domain (so a dependent Σ parameter is honoured too).
  def elaborate_expr({:tuple, _meta, [a, b]}, scope, env) do
    with {:ok, a_core} <- elaborate_expr(a, scope, env),
         {:ok, b_core} <- elaborate_expr(b, scope, env) do
      {:ok, {:ctor, sigma_ctor_name(env), [a_core, b_core]}}
    end
  end

  def elaborate_expr({:literal, meta, value} = expr, scope, env) do
    case Keyword.get(meta, :subtype) do
      :boolean when is_boolean(value) ->
        {:ok, {:ctor, resolve_ctor_key(env, if(value, do: :True, else: :False)), []}}

      :integer when is_integer(value) ->
        {:ok, {:int_lit, value}}

      :float when is_float(value) ->
        {:ok, {:float_lit, value}}

      # The guard is required, not cosmetic: an unguarded negative `{:bounded_lit,
      # k}` reaching the kernel raises an uncaught `FunctionClauseError`
      # (`Kernel.infer/2` has no catch-all) — see spec §3.4.
      :char when is_integer(value) and value >= 0 and value <= 0x10FFFF ->
        {:ok, {:bounded_lit, value}}

      :char when is_integer(value) ->
        {:error, {:char_literal_out_of_range, value}}

      # A string literal argument IS `List(Char)` — desugar to its char-literal
      # list and re-enter, exactly as the typed/checked paths do (so `f("hi")`
      # and `f(['h','i'])` build the identical Cons spine).
      :string when is_binary(value) ->
        elaborate_expr(desugar_string(value, meta), scope, env)

      # A symbol literal argument `:ok` is an `Atom` value (Core `{:atom_lit, a}`).
      :symbol when is_atom(value) ->
        {:ok, {:atom_lit, value}}

      _ ->
        {:error, {:unsupported_expression, expr}}
    end
  end

  def elaborate_expr({:list, _, _} = node, scope, env),
    do: elaborate_expr(desugar_list(node), scope, env)

  # Quasiquotation (SP5.1): `quote <form>` lowers to the `Std.Syntax` builder
  # expression that constructs the reflected form, with `$(e)` splice holes
  # elaborated in place. Pure surface sugar — the lowered term re-enters the
  # ordinary elaborator (TCB delta 0).
  def elaborate_expr({:quoted_syntax, _meta, [inner]}, scope, env),
    do: elaborate_expr(Cure.Compiler.MacroSyntax.lower_quote(inner), scope, env)

  def elaborate_expr({:async_operation, meta, _children}, _scope, _env),
    do: {:error, unsupported_async_error(meta)}

  # A `$(e)` / `$(e ...)` splice reaching the elaborator as a bare node means it
  # sits outside any enclosing `quote` — a category error. Inside a quote,
  # `lower_quote/1` consumes the splice wrapper (only its inner expression
  # survives), so this clause fires only for an orphan splice.
  def elaborate_expr({tag, meta, _}, _scope, _env) when tag in [:splice, :splice_group],
    do: {:error, splice_outside_quote_error(tag, meta)}

  def elaborate_expr(other, _scope, _env) do
    {:error, {:unsupported_expression, other}}
  end

  defp unsupported_async_error(meta) do
    {:unsupported_async,
     %{
       primitive: :spawn,
       stage: :dependent_runtime,
       span: surface_expression_span({:async_operation, meta, []})
     }}
  end

  defp splice_outside_quote_error(tag, meta) do
    {:splice_outside_quote,
     %{
       form: tag,
       stage: :elaboration,
       span: surface_expression_span({tag, meta, []})
     }}
  end

  # The registered Sigma constructor name (canonically `:mk_pair`), resolved via the
  # builtin registry (§1.4) rather than hard-coded; defaults to `:mk_pair` when no
  # Sigma family is registered (a raw `Env.empty()` elaboration).
  defp sigma_ctor_name(env) do
    with fam when not is_nil(fam) <- Inductive.builtin(env, :sigma),
         [%{name: n} | _] <- Inductive.ctors_of(env, fam) do
      n
    else
      _ -> :mk_pair
    end
  end

  defp unit_family_name(env), do: Env.resolve_key(env, env.families, :Unit)

  defp unit_ctor_name(env), do: Env.resolve_key(env, env.ctors, :unit)

  # `Tuple(A, B, ...)` is parsed as a dedicated `:tuple_type` in annotation
  # position, but as an ordinary call when it occurs in the body of a
  # Type-returning function. Types are first-class there too: route the call
  # through the same tuple-type lowering used by annotations instead of trying
  # to resolve a nonexistent runtime value named `Tuple`.
  defp elaborate_named_call_scoped([{:name, "Tuple"} | _], args, scope, env) do
    elaborate_type(
      {:tuple_type, [arity: length(args), binders: List.duplicate("_", length(args))], args},
      scope,
      env
    )
  end

  defp elaborate_named_call_scoped(meta, args, scope, env) do
    name = Keyword.fetch!(meta, :name)
    atom = String.to_atom(name)
    resolved_ctor = resolve_ctor_key(env, atom)
    ctor = Inductive.get_ctor(env, resolved_ctor)
    resolved_def = resolve_def_key(env, name, atom)
    {meta, args} = normalize_constructor_named_args(meta, args, ctor)

    alignment =
      cond do
        ctor ->
          align_constructor_args(resolved_ctor, ctor, meta, args)

        Env.get_def(env, resolved_def) ->
          Cure.Elab.Overload.align(env, resolved_def, args, Keyword.get(meta, :arg_labels))

        true ->
          {:ok, args}
      end

    with {:ok, args} <- alignment,
         {:ok, core_args} <- map_elaborate(args, scope, env, &elaborate_expr/3) do
      cond do
        ctor ->
          ctor_key = resolved_ctor

          # A constructor head applied to arguments is a saturated constructor, not
          # a chain of `{:app, …}`. Mirror `elaborate_type/3`'s ctor-aware clause:
          # this saturated-call clause builds the saturated ctor directly, while
          # `resolve_free` eta-expands bare positive-arity ctors (all-present,
          # unindexed) into lambdas and yields the nullary `{:ctor, atom, []}`
          # form otherwise.
          {:ok, {:ctor, ctor_key, core_args}}

        # A type FAMILY applied in EXPRESSION position — a type-level function body
        # such as `fn F(a) -> Type = Option(a)`, or a large-elim selector branch
        # returning a per-kind representation type over the ambient parameters
        # (`FocusShape(k, a, s)`). Split the arguments into the family's parameters
        # (prefix) and indices (suffix) and build the saturated `{:data, …}` node,
        # exactly as the type path does (`declarations.ex` `idx_to_core`). A local
        # binder shadows a family, so only take this branch when the name is NOT in
        # scope (an applied bound variable stays an `{:app, …}` chain below). Without
        # this the head resolved to `{:data, atom, [], []}` and the arguments were
        # `{:app}`-chained OUTSIDE it, so the kernel saw a 0-parameter data node
        # where the family needs parameters → a false `:arg_arity`.
        name not in scope and Inductive.family?(env, atom) ->
          family_key = Env.resolve_key(env, env.families, atom)
          {params, indices} = Enum.split(core_args, Inductive.param_count(env, family_key))
          {:ok, {:data, family_key, params, indices}}

        true ->
          with {:ok, head} <- elaborate_expr({:variable, [], name}, scope, env) do
            {:ok, Enum.reduce(core_args, head, fn arg, acc -> {:app, acc, arg} end)}
          end
      end
    end
  end

  # A free name is a nullary constructor, a global definition, or (fallback) a global ref.
  defp resolve_free(name, env) do
    atom = String.to_atom(name)

    cond do
      Inductive.get_ctor(env, atom) ->
        eta_expand_bare_ctor(env, Env.resolve_key(env, env.ctors, atom))

      Inductive.family?(env, atom) ->
        {:ok, {:data, Env.resolve_key(env, env.families, atom), [], []}}

      # A machine PRIMITIVE base type (Int/Float/Binary/Atom) in value position
      # is a first-class value of type `Type` — the same first-classness families
      # already get above (Idris/Agda/Lean: a type constructor name in term
      # position IS the type value). Primitives are `Env.put_primitive` bindings,
      # not families, so without this they fell through to `{:global, :Int}` →
      # `:unknown_global`. The kernel already types the primitive Core node
      # (`{:int_type}`, …) at `{:vtype, 0}`; this is a pure resolution fix.
      prim = Env.primitive(env, name) ->
        {:ok, prim}

      # Bare VALUE position mirrors the call-position R7 trichotomy: a name
      # provided by ≥2 re-keyed imports with no local/unshadowed winner is
      # ambiguous (E089), same tuple shape as the call site.
      length(Cure.Elab.Resolution.ambiguous_modules(env, atom)) >= 2 ->
        {:error, {:ambiguous_name, atom, Cure.Elab.Resolution.ambiguous_modules(env, atom)}}

      # A bare def key present is the local winner (or a non-colliding import that
      # kept its bare key): keep it. `resolve_bare/2`'s contract requires
      # this bare-absence check before the shadowed-import fallback, otherwise a
      # re-keyed sibling (`Std.Nat#plus`) would override a local `plus`.
      Env.get_def(env, atom) ->
        {:ok, {:global, Env.resolve_key(env, env.defs, atom)}}

      # No local winner, no ambiguity: if exactly one re-keyed import provides
      # the name, resolve to that qualified key; else keep the bare global.
      true ->
        case Cure.Elab.Resolution.resolve_bare(env, atom) do
          {:ok, key} -> {:ok, {:global, key}}
          _ -> {:ok, {:global, atom}}
        end
    end
  end

  # A bare name checked against a universe is in type position. Records bind
  # their family and constructor under the same source spelling, so family/type
  # bindings must win here even though constructors correctly win in ordinary
  # expression position. This mirrors Declarations.resolve_index_name/2 for
  # expression bodies whose result itself is a type (large elimination).
  defp resolve_type_free(name, env) do
    atom = String.to_atom(name)

    cond do
      primitive = Env.primitive(env, name) ->
        {:ok, primitive}

      Inductive.family?(env, atom) ->
        {:ok, {:data, Env.resolve_key(env, env.families, atom), [], []}}

      Env.get_def(env, atom) ->
        {:ok, {:global, Env.resolve_key(env, env.defs, atom)}}

      match?({:ok, _}, Cure.Elab.Resolution.resolve_bare(env, atom)) ->
        {:ok, key} = Cure.Elab.Resolution.resolve_bare(env, atom)

        cond do
          Inductive.family?(env, key) -> {:ok, {:data, key, [], []}}
          Env.get_def(env, key) -> {:ok, {:global, key}}
          true -> :error
        end

      true ->
        :error
    end
  end

  # A bare positive-arity constructor reference eta-expands to nested lambdas
  # (`S` becomes `λ n:Nat. S(n)`) so first-class ctor values elaborate instead
  # of dying at the kernel's arity check (:ctor_arity) — the general gap behind
  # spec 2026-07-08-nat-int-erasure rule 4 (Idris allows bare `S` everywhere).
  # Scope: ctors whose args are all explicit/:unrestricted and whose result carries
  # no params/indices. An implicit-carrying or indexed ctor keeps today's
  # nullary resolution (and today's downstream error): a lambda-typed value
  # cannot receive implicit insertion at its call sites, so eta-expanding it
  # would produce an unusable value rather than a working one.
  defp eta_expand_bare_ctor(env, atom) do
    %{args: tele, quantities: qs, result_params: rp, result_indices: ri} =
      Inductive.get_ctor(env, atom)

    k = length(tele)

    if k > 0 and Enum.all?(qs, &Grade.present?/1) and rp == [] and ri == [] do
      body_args = for i <- (k - 1)..0//-1, do: {:var, i}
      body = {:ctor, atom, body_args}

      {:ok,
       Enum.reduce(Enum.reverse(tele), body, fn {_name, dom}, acc ->
         {:lam, Cure.Core.Grade.unrestricted(), dom, acc}
       end)}
    else
      {:ok, {:ctor, atom, []}}
    end
  end

  # -- type expressions -------------------------------------------------------

  # Type→Core lowering has a single source of truth: `Declarations.lower_type/3`
  # (the live signature path's `idx_to_core`). This legacy entry — reached only by
  # `elaborate/2`, a pre-dependent-pipeline signature elaborator — delegates there
  # so both share name resolution, param/index splitting, and numeric-index
  # lowering (`Bounded(5)` → `{:nat_lit, 5}`) rather than reinventing an
  # impoverished copy that turned every unbound name into a phantom `{:data, …}`.
  defp elaborate_type(ast, scope, env), do: Cure.Elab.Declarations.lower_type(ast, scope, env)
  defp elaborate_type(ast, scope, env, ctx), do: Cure.Elab.Declarations.lower_type(ast, scope, env, ctx)

  # -- helpers ----------------------------------------------------------------

  defp simplify_outside_justification(meta) do
    info = Cure.MetaAST.Metadata.source_info(meta)

    {:error,
     {:simplification_failed,
      %Cure.Diagnostic.SimplificationProblem{
        kind: :inadmissible_rule,
        command: info && info.whole,
        before_goal: nil,
        after_goal: nil,
        cause: :outside_justification
      }}}
  end

  defp map_elaborate(asts, scope, env, fun) do
    Enum.reduce_while(asts, {:ok, []}, fn ast, {:ok, acc} ->
      case fun.(ast, scope, env) do
        {:ok, core} -> {:cont, {:ok, acc ++ [core]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end
end
