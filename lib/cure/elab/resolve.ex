defmodule Cure.Elab.Resolve do
  @moduledoc """
  Resolve an interface-method call to a concrete implementation, and supply the
  dictionary a constrained function needs at its concrete call sites.

  When the head-positioned argument has a concrete type constructor (`Int`,
  `Bool`, a user ADT, …), a method inlines to the instance's mangled global
  (static dispatch). When the head is a rigid type variable — inside a
  polymorphic function constrained by `where Iface(a)` — the method projects off
  the implicit dictionary parameter that the constraint introduced (dynamic
  dispatch through a threaded runtime dictionary).

  A call to a constrained function (`same(x, y)` where `same` carries `where
  Eqs(a)`) is intercepted here too: the dictionary the callee expects is resolved
  from the argument that fixes `a` and appended as a trailing argument, so the
  ordinary implicit applicator threads it through.
  """

  alias Cure.Core.{Context, Env, Eval, Quote, Term}
  alias Cure.Elab.{Coherence, Elaborator, Interface}

  @doc "Is `atom` the name of a method declared by some in-scope interface?"
  @spec method?(Env.t(), atom()) :: boolean()
  def method?(env, atom), do: Interface.for_method(env, atom) != nil and not owned_definition?(env, atom)

  # A module that defines `fn combine` of its own means THAT function, even when
  # an ambient interface happens to declare a method by the same name. Method
  # dispatch is tried BEFORE the ordinary global path, so without this guard an
  # unrelated local definition is silently reinterpreted as a method call and
  # then fails on its head argument's type — `Std.Proof.LinearArithmetic.combine/3`
  # reporting `{:no_instance, :Semigroup, :"Std.Nat#Nat"}` for a function that has
  # nothing to do with semigroups.
  #
  # This mirrors `Env.resolve_key/3`'s owned-first order rather than inventing a
  # second precedence rule. An interface's own declaration is not a definition,
  # and an implementation's methods are registered under mangled names, so a
  # method still dispatches inside its declaring module and in every instance.
  defp owned_definition?(%Env{module_owner: nil}, _atom), do: false

  defp owned_definition?(%Env{module_owner: owner} = env, atom),
    do: Map.has_key?(env.defs, Cure.Elab.Name.qualify(owner, atom))

  @doc "Does this interface method determine its instance head only from its result?"
  def result_dispatched_method?(env, method) do
    case Interface.for_method(env, method) do
      nil -> false
      desc -> is_nil(head_argument_index(desc, method))
    end
  end

  @doc "Does `atom` name a global function that carries `where` constraints?"
  @spec constrained?(Env.t(), atom()) :: boolean()
  def constrained?(env, atom), do: Env.constrained(env, atom) != nil

  @doc """
  Elaborate `method(args...)` by resolving the instance from the head-positioned
  argument's type. Returns `{:ok, term, type_value}` or an error (notably
  `{:no_instance, iface, head}`).
  """
  @spec method_call(Env.t(), atom(), [term()], [term()], term()) ::
          {:ok, term(), term()} | {:error, term()}
  def method_call(env, method, args, names, ctx) do
    desc = Interface.for_method(env, method)
    idx = head_param_index(desc, method)
    head_ast = Enum.at(args, idx)

    # Only the head-positioned argument is elaborated here — enough to classify the
    # instance. The remaining arguments (which may be lambdas needing checking mode)
    # are elaborated by the application machinery once the callee is fixed.
    with {:ok, _term, tval} <- Elaborator.elaborate_expr_typed(head_ast, names, ctx, env) do
      case classify(env, tval, MapSet.new()) do
        {:concrete, hc} -> concrete(env, desc, method, hc, tval, args, names, ctx)
        {:rigid, lvl} -> abstract(env, desc, method, args, lvl, names, ctx)
        {:unknown, tval2} -> {:error, {:no_instance, desc.name, tval2}}
      end
    end
  end

  @doc "Resolve a result-dispatched method using its checking-mode expected type."
  def method_call_checked(env, method, args, expected_core, names, ctx) do
    desc = Interface.for_method(env, method)

    # A result-dispatched method may be called under a polymorphic constraint:
    #
    #   from_json_value(value) : Result(t, DecodeError)
    #     requires FromJSON(t)
    #
    # There is no argument whose type is `t`, but checking mode already knows
    # the complete expected result. Recover the interface head from the method's
    # declared result shape. A rigid head dispatches through the dictionary
    # binder introduced by `requires`; a concrete head can use the ordinary
    # static path. Previously this case fell through to candidate enumeration,
    # which cannot find a concrete implementation for a rigid variable and
    # misleadingly reported `no_instance` for the whole `Result(...)` type.
    checked_head = result_head_value(desc, method, expected_core, ctx, env)

    case checked_head do
      {:rigid, level} ->
        checked_dispatch(abstract(env, desc, method, args, level, names, ctx))

      {:concrete, head, type_value} ->
        checked_dispatch(concrete(env, desc, method, head, type_value, args, names, ctx))

      :unknown ->
        method_call_checked_candidates(env, desc, method, args, expected_core, names, ctx)
    end
  end

  defp checked_dispatch({:ok, term, _type}), do: {:ok, term}
  defp checked_dispatch({:error, _reason} = error), do: error

  defp method_call_checked_candidates(env, desc, method, args, expected_core, names, ctx) do
    candidates =
      case Env.coherence(env) do
        %Coherence{anon: anon} ->
          for {{iface, _head}, ref} <- anon, iface == desc.name, do: ref

        _ ->
          []
      end

    successes =
      Enum.reduce(candidates, [], fn ref, acc ->
        mangled = Map.fetch!(ref.methods, method)

        case Elaborator.elaborate_implicit_global_app(env, mangled, args, names, ctx) do
          {:ok, term, type} ->
            case Cure.Core.Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
              :ok -> [{term, type} | acc]
              {:error, _} -> acc
            end

          {:error, _} ->
            acc
        end
      end)

    case successes do
      [{term, _type}] -> {:ok, term}
      [] -> {:error, {:no_instance, desc.name, expected_core}}
      _ -> {:error, {:ambiguous_instance_for_expected_type, desc.name, expected_core}}
    end
  end

  defp result_head_value(desc, method, expected_core, ctx, env) do
    return_ast = Map.fetch!(desc.methods, method).return_type

    case result_head_core(return_ast, expected_core, desc.head_var) do
      {:ok, head_core} ->
        case classify(env, Eval.eval(head_core, Context.env(ctx)), MapSet.new()) do
          {:rigid, _} = rigid -> rigid
          {:concrete, head} -> {:concrete, head, Eval.eval(head_core, Context.env(ctx))}
          {:unknown, _} -> :unknown
        end

      :error ->
        :unknown
    end
  end

  defp result_head_core({:variable, _meta, head_var}, core, head_var), do: {:ok, core}

  defp result_head_core({:function_call, _meta, ast_args}, {:data, _family, params, indices}, head_var) do
    find_result_head(ast_args, params ++ indices, head_var)
  end

  defp result_head_core(_ast, _core, _head_var), do: :error

  defp find_result_head(ast_args, core_args, head_var) do
    ast_args
    |> Enum.zip(core_args)
    |> Enum.reduce_while(:error, fn {ast, core}, :error ->
      case result_head_core(ast, core, head_var) do
        {:ok, _} = found -> {:halt, found}
        :error -> {:cont, :error}
      end
    end)
  end

  @doc """
  Elaborate a call to a constrained global `name(args...)`, appending the
  dictionary each `where Iface(a)` clause requires. The dictionary is resolved
  from the argument fixing `a` (concrete head → the instance dictionary value;
  rigid head → the in-scope dictionary binder) and threaded as a trailing
  argument through the ordinary implicit applicator.
  """
  @spec constrained_call(Env.t(), atom(), [term()], [term()], term()) ::
          {:ok, term(), term()} | {:error, term()}
  def constrained_call(env, name, args, names, ctx) do
    specs = Env.constrained(env, name)

    with {:ok, dict_asts} <- dict_arguments(specs, args, names, ctx, env) do
      Elaborator.elaborate_implicit_global_app(env, name, args ++ dict_asts, names, ctx)
    end
  end

  @doc "Elaborate a constrained global whose expected result may determine a constraint head."
  def constrained_call_checked(env, name, args, expected_core, names, ctx) do
    specs = Env.constrained(env, name)

    with {:ok, dict_asts} <- dict_arguments_checked(specs, name, args, expected_core, names, ctx, env),
         {:ok, term, _type} <-
           Elaborator.elaborate_implicit_global_app(env, name, args ++ dict_asts, names, ctx),
         :ok <- Cure.Core.Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
      {:ok, term}
    end
  end

  @doc """
  Build the dictionary value for interface `iface` at concrete head `head`:
  the single-constructor record `Iface{ m1 = impl₁, … }` over the instance's
  mangled method globals. Its type is `Iface(head)`. Used by the elaborator when
  it reaches a `{:dict_value, iface, head}` synthetic argument.
  """
  @spec dict_value(Env.t(), atom(), atom(), term(), [term()], term()) ::
          {:ok, term(), term()} | {:error, term()}
  def dict_value(env, iface, head, type_value, names, ctx) do
    with {:ok, term} <- dict_term_for_type_value(env, iface, head, type_value, names, ctx) do
      iface_key = Env.resolve_key(env, env.families, iface)
      head_type = Quote.reify(type_value, Context.length(ctx))
      type = Eval.eval({:data, iface_key, [head_type], []}, Context.env(ctx))
      {:ok, term, type}
    end
  end

  @doc "Resolve an interface dictionary directly from an already inferred type value."
  @spec dictionary_for_type_value(Env.t(), atom(), term(), term()) ::
          {:ok, term(), term()} | {:error, term()}
  def dictionary_for_type_value(env, iface, type_value, ctx) do
    case classify(env, type_value, MapSet.new()) do
      {:concrete, head} -> dict_value(env, iface, head, type_value, [], ctx)
      {:rigid, level} -> {:error, {:no_instance, iface, {:rigid, level}}}
      {:unknown, value} -> {:error, {:no_instance, iface, value}}
    end
  end

  # -- head classification ----------------------------------------------------

  # The head-positioned parameter is the one whose interface-signature type mentions
  # the head variable. A first-order interface mentions it BARE (`x : a`); a
  # higher-kinded one mentions it APPLIED (`container : f(a)`) and never bare — its
  # inferred type (`List(Int)`) still names the instance's type constructor, so that
  # parameter is the dispatch head just the same.
  #
  # Both forms are located explicitly. Defaulting the higher-kinded case to parameter
  # 0 only worked while the applied-head parameter happened to be declared first;
  # reordering to `fmap(g: (a) -> b, container: f(a))` — legal, and nothing in the
  # parser or `Cure.Elab.Interface` forbids it — classified `g` as the head and
  # reported `{:no_instance, ...}` for a correctly registered instance.
  #
  # `Interface.collect_head_uses/3` classifies the same two shapes; keep them aligned.
  defp head_param_index(desc, method) do
    head_argument_index(desc, method) || 0
  end

  defp head_argument_index(desc, method) do
    info = Map.fetch!(desc.methods, method)
    hv = desc.head_var

    bare =
      Enum.find_index(info.params, fn {:param, pm, _} ->
        match?({:variable, _, ^hv}, Keyword.fetch!(pm, :type))
      end)

    applied =
      Enum.find_index(info.params, fn {:param, pm, _} ->
        applied_head?(Keyword.fetch!(pm, :type), hv)
      end)

    # `|| 0` is unreachable for any interface `Interface.infer_head_kind/3` accepted
    # (it requires at least one bare or applied use somewhere in the interface), but a
    # method that mentions the head only in its RETURN type has no head parameter.
    bare || applied
  end

  # `f(a)` — the head variable in applied (higher-kinded) position. A function type
  # parses as `{:function_call, [name: "Function", function_type: true], _}`, so it
  # only matches when the interface's head variable is literally named `Function`.
  defp applied_head?({:function_call, fmeta, _args}, hv), do: Keyword.get(fmeta, :name) == hv
  defp applied_head?(_type, _hv), do: false

  # NOTE(int-facade): kept for totality on a legacy/deserialized `{:vint_type}`
  # value; fresh elaboration never produces one (spec 2026-07-18 §3a) — `Int`
  # normally reaches classification as `{:vdata, int_fid, []}`.
  defp classify(_env, {:vint_type}, _seen), do: {:concrete, :Int}
  defp classify(_env, {:vfloat_type}, _seen), do: {:concrete, :Float}
  defp classify(_env, {:vatom_type}, _seen), do: {:concrete, :Atom}
  # String has no primitive value former: `String = List(Char)` (the landed
  # value-surface design), so it reaches dispatch as the `nglobal` alias `String`
  # and is unfolded to `List(Char)` by the neutral-global clause below — it never
  # arrives as a `{:vstring_type}`. (`{:string_type}` is only an E-layer head-atom
  # sentinel in `head_type_core`; it is never evaluated.)
  defp classify(_env, {:vdata, name, _vs}, _seen), do: {:concrete, name}
  defp classify(_env, {:vneutral, {:nvar, lvl}}, _seen), do: {:rigid, lvl}

  # A transparent type synonym in head position (`String = List(Char)`) reaches
  # dispatch as a neutral global, because delta-reduction is on-demand. Unfold it
  # to its normal form and re-classify, so `combine` on a `String` finds the
  # `List` instance — the same alias-normalisation the coherence *registration*
  # side does (`Implementation.head_key`, which whnf's the elaborated head). Only
  # nullary type-level defs unfold; `seen` guards a cyclic alias chain.
  defp classify(env, {:vneutral, {:nglobal, name}} = v, seen) do
    if MapSet.member?(seen, name) do
      {:unknown, v}
    else
      case Env.get_def(env, name) do
        %{type: {:type, _}, body: body} when not is_nil(body) ->
          classify(env, Eval.eval(body, []), MapSet.put(seen, name))

        _ ->
          {:unknown, v}
      end
    end
  end

  defp classify(_env, other, _seen), do: {:unknown, other}

  # -- concrete (static) dispatch ---------------------------------------------
  # Inline the instance's mangled method global and elaborate the call through the
  # ordinary implicit-aware application machinery (so a lambda argument like
  # `fmap`'s `g` is checked against its domain, and any method-level implicits are
  # solved).
  defp concrete(env, desc, method, head, type_value, args, names, ctx) do
    case Coherence.lookup_anon(Env.coherence(env), desc.name, head) do
      {:ok, ref} ->
        mangled = Map.fetch!(ref.methods, method)

        with {:ok, dict_asts} <- instance_constraint_dict_asts(ref, type_value, names, ctx, env) do
          Elaborator.elaborate_implicit_global_app(env, mangled, args ++ dict_asts, names, ctx)
        end

      {:error, _} ->
        {:error, {:no_instance, desc.name, head}}
    end
  end

  # -- abstract (dynamic) dispatch --------------------------------------------
  # The head is a rigid type variable `a` at de Bruijn level `lvl`; the enclosing
  # `where Iface(a)` constraint put a dictionary binder of type `Iface(a)` in
  # scope. Find it by type (the only binder whose type is `Iface(<that rigid a>)`),
  # project the method field off it, and apply to the arguments (checking each so a
  # lambda argument is honoured).
  defp abstract(env, desc, method, args, lvl, names, ctx) do
    case find_dict_binder(ctx, names, desc.name, lvl, env) do
      {:ok, dict_name} ->
        with {:ok, proj, ptype} <-
               Elaborator.project_record_field(
                 {:variable, [], dict_name},
                 Atom.to_string(method),
                 names,
                 ctx,
                 env
               ) do
          Elaborator.apply_checked_args(proj, ptype, args, names, ctx, env)
        end

      :error ->
        {:error, {:no_instance, desc.name, {:rigid, lvl}}}
    end
  end

  # The surface name of the in-scope binder whose type value is exactly
  # `Iface(<rigid var at level lvl>)`, or `:error` if none.
  defp find_dict_binder(ctx, names, iface, lvl, env) do
    iface = Env.resolve_key(env, env.families, iface)
    target = {:vdata, iface, [{:vneutral, {:nvar, lvl}}]}
    n = Context.length(ctx)

    if n == 0 do
      :error
    else
      Enum.reduce_while(0..(n - 1), :error, fn k, _acc ->
        name = Enum.at(names, k)

        if is_binary(name) and Context.lookup(ctx, k) == target do
          {:halt, {:ok, name}}
        else
          {:cont, :error}
        end
      end)
    end
  end

  # -- dictionary arguments for a constrained call ----------------------------

  # One dictionary argument AST per constraint, in order. A concrete head yields
  # a `{:dict_value, iface, head}` synthetic node (the elaborator builds the
  # instance dictionary); a rigid head yields a reference to the in-scope
  # dictionary binder (re-threading the caller's own dictionary).
  defp dict_arguments(specs, args, names, ctx, env) do
    Enum.reduce_while(specs, {:ok, []}, fn spec, {:ok, acc} ->
      head_ast = Enum.at(args, spec.head_arg_index)

      case Elaborator.elaborate_expr_typed(head_ast, names, ctx, env) do
        {:ok, _term, tval} ->
          head_value = constraint_head_from_argument(spec, tval, ctx)

          case classify(env, head_value, MapSet.new()) do
            {:concrete, head} ->
              {:cont, {:ok, acc ++ [{:dict_value, spec.iface, head, head_value}]}}

            {:rigid, lvl} ->
              case find_dict_binder(ctx, names, spec.iface, lvl, env) do
                {:ok, dname} -> {:cont, {:ok, acc ++ [{:variable, [], dname}]}}
                :error -> {:halt, {:error, {:no_instance, spec.iface, {:rigid, lvl}}}}
              end

            {:unknown, tval2} ->
              {:halt, {:error, {:no_instance, spec.iface, tval2}}}
          end

        {:error, _} = err ->
          {:halt, err}
      end
    end)
  end

  defp dict_arguments_checked(specs, callee, args, expected_core, names, ctx, env) do
    Enum.reduce_while(specs, {:ok, []}, fn spec, {:ok, acc} ->
      result =
        if is_integer(spec.head_arg_index) do
          dictionary_ast_from_argument(spec, Enum.at(args, spec.head_arg_index), names, ctx, env)
        else
          dictionary_ast_from_result(spec, callee, expected_core, names, ctx, env)
        end

      case result do
        {:ok, dict_ast} -> {:cont, {:ok, acc ++ [dict_ast]}}
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  defp dictionary_ast_from_argument(spec, head_ast, names, ctx, env) do
    with {:ok, _term, tval} <- Elaborator.elaborate_expr_typed(head_ast, names, ctx, env) do
      dictionary_ast_from_type(spec, constraint_head_from_argument(spec, tval, ctx), names, ctx, env)
    end
  end

  defp constraint_head_from_argument(spec, type_value, ctx) do
    core = Quote.reify(type_value, Context.length(ctx))

    case result_head_core(Map.get(spec, :head_arg_type), core, spec.tyvar) do
      {:ok, head_core} -> Eval.eval(head_core, Context.env(ctx))
      :error -> type_value
    end
  end

  defp dictionary_ast_from_result(spec, callee, expected_core, names, ctx, env) do
    case result_head_core(spec.return_type, expected_core, spec.tyvar) do
      {:ok, head_core} ->
        dictionary_ast_from_type(spec, Eval.eval(head_core, Context.env(ctx)), names, ctx, env)

      # No argument fixes the head, and the expected type does not have the
      # declared result's shape, so there is nothing to read the head off. The
      # author has to widen or correct the annotation — which means the reason
      # has to carry enough to say which annotation and what shape it must take.
      :error ->
        {:error,
         {:constraint_head_not_determined,
          %{
            interface: spec.iface,
            type_variable: spec.tyvar,
            callee: callee,
            result_type: spec.return_type,
            expected: expected_core
          }}}
    end
  end

  defp dictionary_ast_from_type(spec, tval, names, ctx, env) do
    case classify(env, tval, MapSet.new()) do
      {:concrete, head} ->
        {:ok, {:dict_value, spec.iface, head, tval}}

      {:rigid, lvl} ->
        case find_dict_binder(ctx, names, spec.iface, lvl, env) do
          {:ok, dname} -> {:ok, {:variable, [], dname}}
          :error -> {:error, {:no_instance, spec.iface, {:rigid, lvl}}}
        end

      {:unknown, value} ->
        {:error, {:no_instance, spec.iface, value}}
    end
  end

  defp instance_constraint_dict_asts(ref, type_value, names, ctx, env) do
    bindings = bind_instance_type(Map.get(ref, :for_type), type_value, %{})

    ref
    |> Map.get(:constraints, [])
    |> Enum.reduce_while({:ok, []}, fn constraint, {:ok, acc} ->
      with {:ok, iface, required_type} <- constraint_type_value(constraint, bindings),
           {:ok, dict_ast} <- dictionary_ast_for_value(iface, required_type, names, ctx, env) do
        {:cont, {:ok, acc ++ [dict_ast]}}
      else
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  defp dictionary_ast_for_value(iface, type_value, names, ctx, env) do
    case classify(env, type_value, MapSet.new()) do
      {:concrete, head} ->
        {:ok, {:dict_value, iface, head, type_value}}

      {:rigid, level} ->
        case find_dict_binder(ctx, names, iface, level, env) do
          {:ok, name} -> {:ok, {:variable, [], name}}
          :error -> {:error, {:no_instance, iface, {:rigid, level}}}
        end

      {:unknown, value} ->
        {:error, {:no_instance, iface, value}}
    end
  end

  defp bind_instance_type({:variable, _meta, name}, value, bindings) do
    if type_variable_name?(name), do: Map.put(bindings, name, value), else: bindings
  end

  defp bind_instance_type({:function_call, _meta, ast_args}, {:vdata, _name, value_args}, bindings) do
    ast_args
    |> Enum.zip(value_args)
    |> Enum.reduce(bindings, fn {ast, value}, acc -> bind_instance_type(ast, value, acc) end)
  end

  defp bind_instance_type(_surface, _value, bindings), do: bindings

  defp constraint_type_value({:function_call, meta, [{:variable, _vm, name}]}, bindings) do
    case Map.fetch(bindings, name) do
      {:ok, value} -> {:ok, String.to_atom(Keyword.fetch!(meta, :name)), value}
      :error -> {:error, {:instance_constraint_not_determined, name}}
    end
  end

  defp constraint_type_value(constraint, _bindings),
    do: {:error, {:unsupported_parameterized_instance_constraint, constraint}}

  # The single-constructor record value `Iface{ m1 = impl₁, … }`: the interface's
  # constructor applied to the instance's mangled method globals, in method order.
  # The erased head parameter is NOT a `:ctor` argument (it is recovered from the
  # value's type), so only the method fields appear.
  #
  # Each method is eta-expanded to its full arity — `λx.λy. impl(x, y)` rather than
  # a bare `{:global, impl}`. A dictionary method is projected and then applied one
  # argument at a time (the curried function-value ABI), but a multi-argument global
  # emits as a fixed-arity `fun name/n`, which a 1-argument apply would mis-call. The
  # eta-expansion lowers to curried 1-argument funs whose inner *saturated* spine is
  # a direct `impl(x, y)` call — ABI-correct at both the projection and the call.
  defp dict_term_for_type_value(env, iface, head, type_value, names, ctx) do
    case Coherence.lookup_anon(Env.coherence(env), iface, head) do
      {:ok, ref} ->
        bindings = bind_instance_type(Map.get(ref, :for_type), type_value, %{})

        with {:ok, dependencies} <- instance_constraint_terms(ref, bindings, names, ctx, env) do
          type_args =
            ref
            |> Map.get(:for_type)
            |> surface_type_variables()
            |> Enum.map(&Map.fetch!(bindings, &1))
            |> Enum.map(&Quote.reify(&1, Context.length(ctx)))

          {:ok, dict_term_from_ref(env, iface, ref, type_args, dependencies)}
        end

      {:error, _} ->
        {:error, {:no_instance, iface, head}}
    end
  end

  defp instance_constraint_terms(ref, bindings, names, ctx, env) do
    ref
    |> Map.get(:constraints, [])
    |> Enum.reduce_while({:ok, []}, fn constraint, {:ok, acc} ->
      with {:ok, iface, type_value} <- constraint_type_value(constraint, bindings),
           {:ok, term} <- dictionary_term_for_value(iface, type_value, names, ctx, env) do
        {:cont, {:ok, acc ++ [term]}}
      else
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  defp dictionary_term_for_value(iface, type_value, names, ctx, env) do
    case classify(env, type_value, MapSet.new()) do
      {:concrete, head} ->
        dict_term_for_type_value(env, iface, head, type_value, names, ctx)

      {:rigid, level} ->
        case find_dict_binder(ctx, names, iface, level, env) do
          {:ok, name} ->
            case Enum.find_index(names, &(&1 == name)) do
              nil -> {:error, {:no_instance, iface, {:rigid, level}}}
              index -> {:ok, {:var, index}}
            end

          :error ->
            {:error, {:no_instance, iface, {:rigid, level}}}
        end

      {:unknown, value} ->
        {:error, {:no_instance, iface, value}}
    end
  end

  defp surface_type_variables(nil), do: []

  defp surface_type_variables({:variable, _meta, name}) do
    if type_variable_name?(name), do: [name], else: []
  end

  defp surface_type_variables({:function_call, _meta, args}),
    do: args |> Enum.flat_map(&surface_type_variables/1) |> Enum.uniq()

  defp surface_type_variables(_surface), do: []

  defp type_variable_name?(<<first::utf8, _rest::binary>>), do: first in ?a..?z
  defp type_variable_name?(_name), do: false

  @doc """
  The dictionary value for an instance `ref`, independent of how the instance is registered.
  `dict_term/3` reaches this through the anonymous registry; `Cure.Elab.Implementation` uses it
  directly for a NAMED implementation, whose ref lives in the coherence table's `named` map and
  is invisible to `lookup_anon/3`.
  """
  @spec dict_term_from_ref(Env.t(), atom(), map()) :: term()
  def dict_term_from_ref(env, iface, ref) do
    desc = Env.get_interface(env, iface)

    fields =
      Enum.map(desc.method_order, fn m ->
        arity = length(Map.fetch!(desc.methods, m).params)
        eta_expand(env, Map.fetch!(ref.methods, m), arity)
      end)

    {:ctor, Env.resolve_key(env, env.ctors, iface), fields}
  end

  defp dict_term_from_ref(env, iface, ref, [], []), do: dict_term_from_ref(env, iface, ref)

  defp dict_term_from_ref(env, iface, ref, type_args, dependencies) do
    desc = Env.get_interface(env, iface)

    fields =
      Enum.map(desc.method_order, fn method ->
        arity = length(Map.fetch!(desc.methods, method).params)
        eta_expand_parameterized(env, Map.fetch!(ref.methods, method), arity, type_args, dependencies)
      end)

    {:ctor, Env.resolve_key(env, env.ctors, iface), fields}
  end

  defp eta_expand_parameterized(env, gname, arity, type_args, dependencies) do
    %{type: pi} = Env.get_def(env, gname)

    {callee, specialised_pi} =
      Enum.reduce(type_args, {{:global, gname}, pi}, fn argument, {term, {:pi, _grade, _domain, codomain}} ->
        {
          {:app, term, Term.shift(argument, arity, 0)},
          instantiate_codomain(codomain, argument)
        }
      end)

    domains = peel_domains(specialised_pi, arity)

    body =
      Enum.reduce(0..(arity - 1), callee, fn index, term ->
        {:app, term, {:var, arity - 1 - index}}
      end)

    body =
      Enum.reduce(dependencies, body, fn dependency, term ->
        {:app, term, Term.shift(dependency, arity, 0)}
      end)

    Enum.reduce(Enum.reverse(domains), body, fn domain, term ->
      {:lam, Cure.Core.Grade.unrestricted(), domain, term}
    end)
  end

  defp instantiate_codomain(codomain, argument) do
    codomain
    |> Term.subst(0, Term.shift(argument, 1, 0))
    |> Term.shift(-1, 0)
  end

  @doc "The Core type `Iface(head)` of a dictionary value for `iface` at `head`."
  @spec dict_type_term(Env.t(), atom(), atom()) :: term()
  def dict_type_term(env, iface, head),
    do: {:data, Env.resolve_key(env, env.families, iface), [head_type_core(head)], []}

  # `λ(d0).…λ(d_{n-1}). gname(v0, …, v_{n-1})` — the global eta-expanded to arity
  # `n`, taking each binder domain from the global's own Π type (closed for a
  # non-dependent method signature). A bare global (`n = 0`, or the value is used
  # unapplied) needs no wrapper.
  defp eta_expand(_env, gname, 0), do: {:global, gname}

  defp eta_expand(env, gname, arity) do
    %{type: pi} = Env.get_def(env, gname)
    domains = peel_domains(pi, arity)

    body =
      Enum.reduce(0..(arity - 1), {:global, gname}, fn i, acc ->
        {:app, acc, {:var, arity - 1 - i}}
      end)

    Enum.reduce(Enum.reverse(domains), body, fn dom, acc -> {:lam, Cure.Core.Grade.unrestricted(), dom, acc} end)
  end

  defp peel_domains(_pi, 0), do: []
  defp peel_domains({:pi, _g, dom, cod}, n), do: [dom | peel_domains(cod, n - 1)]
  defp peel_domains(_other, _n), do: []

  # `Int` is no longer a primitive: surface `Int` resolves to the inductive family
  # `Std.Int#Int` via the generic data clause below (spec 2026-07-18 surface flip),
  # exactly as `Nat` does. Float/String remain primitive base types.
  defp head_type_core(:Float), do: {:float_type}
  defp head_type_core(:String), do: {:string_type}
  defp head_type_core(name), do: {:data, name, [], []}
end
