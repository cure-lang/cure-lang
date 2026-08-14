defmodule Cure.Elab.TotalityClosure do
  @moduledoc """
  The **untrusted** type-level totality driver (design spec §5, §7).

  The kernel re-checks each totality certificate (`Kernel.validate_certificate`,
  M7.2); this module decides *which* functions must be certified — the half of
  §7 the kernel does not do. It computes the transitive closure of every global
  reachable from a **type position** (an index expression in a constructor
  signature, a telescope type) — these are the functions whose reduction the
  type-checker relies on, so they must be total — and submits each to the
  kernel. A member that fails certification surfaces as the §10
  `:totality_required` diagnostic, naming the offending function.

  Runtime-only partial functions (referenced in no type) are *not* required to
  be total. Being untrusted, a function this walk misses simply stays
  uncertified (opaque to δ) — never a soundness hole (§7). Surface `@total`
  flags and the whole-program wiring are added at integration time (M9.2).
  """

  alias Cure.Core.{Env, Kernel}
  alias Cure.Elab.TotalityGraph

  @doc "The set of global function names reachable from a type position (transitively)."
  @spec type_level_fns(Env.t()) :: MapSet.t(atom())
  def type_level_fns(%Env{} = env) do
    seeds = seed_globals(env)
    close_unchecked(env, MapSet.to_list(seeds), seeds)
  end

  @doc """
  Submit every type-level function to the kernel for certification, threading the
  resulting (certification-augmented) signature. Returns `{:error,
  {:totality_required, name}}` for the first that cannot be certified.
  """
  @spec certify_type_level(Env.t()) :: {:ok, Env.t()} | {:error, {:totality_required, atom()}}
  def certify_type_level(%Env{} = env) do
    case certify_type_level_detailed(env) do
      {:error, {:totality_required, name, _reason}} -> {:error, {:totality_required, name}}
      result -> result
    end
  end

  @doc false
  @spec certify_type_level_detailed(Env.t()) ::
          {:ok, Env.t()}
          | {:error, {:totality_required, atom(), term()}}
          | {:error, {:totality_closure_unresolved, map()}}
  def certify_type_level_detailed(%Env{} = env) do
    seeds = seed_globals(env)

    with {:ok, closure} <- checked_closure(env, MapSet.to_list(seeds)) do
      names = certifiable_names(env, closure)

      case certify_partition(env, names) do
        {:ok, certified} ->
          {:ok, certified}

        {:error, {:not_total, members}} ->
          {:error, {:totality_required, first_required(members, names), :not_total}}

        {:error, reason} ->
          {:error, {:totality_required, List.first(names), reason}}
      end
    end
  end

  @doc """
  Certify the ordinary total-function closure rooted at compile-time callbacks.

  `computed by` executes a normal Cure function, so its reducer may need to
  unfold imported helpers such as `Std.List.map` and source-level syntax
  builders. Those helpers are not necessarily reachable from a type position;
  certification therefore starts from the callback's elaborated Core globals
  and follows the same kernel-checked closure discipline. This expands
  reducibility for the untrusted compile-time evaluator without changing the
  trusted Core or making runtime functions globally transparent.
  """
  @spec certify_roots(Env.t(), [atom()]) :: {:ok, Env.t()} | {:error, term()}
  def certify_roots(%Env{} = env, roots) when is_list(roots) do
    with {:ok, closure} <- checked_closure(env, roots) do
      names = certifiable_names(env, closure)

      case certify_partition(env, names) do
        {:ok, certified} ->
          {:ok, certified}

        {:error, {:not_total, members}} ->
          {:error, {:compile_time_totality, first_required(members, names), :not_total}}

        {:error, reason} ->
          {:error, {:compile_time_totality, List.first(names), reason}}
      end
    end
  end

  defp certify_partition(env, []), do: {:ok, env}

  defp certify_partition(env, names) do
    if Enum.any?(names, &pending_definition?(env, &1)) do
      # Agda's `termMutual` waits for the complete mutual block. A pending
      # skeleton has no trustworthy outgoing calls, so the only sound result is
      # deferral: retain opacity and retry after body checking completes.
      {:ok, env}
    else
      with {:ok, prepared} <- Kernel.prepare_direct_call_summaries(env, names) do
        partition = TotalityGraph.propose_partition(prepared, names)
        Kernel.validate_scc_certificates(prepared, partition, names)
      end
    end
  end

  defp pending_definition?(env, name),
    do: match?(%{body: {:hole, _}}, Env.get_def(env, name))

  defp certifiable_names(env, names) do
    names
    |> Enum.filter(fn name ->
      case Env.get_def(env, name) do
        %{body: {:hole, _}} -> not Env.total?(env, name)
        %{body: body} when not is_nil(body) and not is_tuple(body) -> true
        %{body: {:extern, _}} -> false
        %{body: nil} -> false
        %{body: _body} -> true
        nil -> false
      end
    end)
    |> Enum.uniq()
    |> Enum.sort()
  end

  defp first_required(members, names) do
    member_set = MapSet.new(members)
    Enum.find(names, List.first(members), &MapSet.member?(member_set, &1))
  end

  @doc """
  Re-certify runtime defs that a *declaration-order* deferral left uncertified.

  `Certificate.terminating?/3` deliberately defers (stays uncertified) a def with a
  still-`{:hole, "__pending__"}` callee, because that callee's onward calls are
  invisible and the SCC cannot be trusted (mutual-recursion soundness). The per-def
  `maybe_certify` in `Declarations` runs in declaration order, so a total function
  that calls a helper declared *below* it — `reverse` → `reverse_acc` — is certified
  while the helper is still pending and is deferred. `certify_type_level/1` only
  re-certifies functions reachable from a type position, so a runtime-only total
  function stays uncertified forever.

  This sweep runs once every body is present. It resubmits every uncertified,
  non-extern, non-builtin def with a real (non-pending) body to the kernel. It is a
  no-op for genuinely partial functions: the kernel re-derives the certificate and
  rejects them exactly as before. No fixpoint is needed — `terminating?/3` reads
  bodies, not the `certified` set, so a single pass over the complete env is exact.
  """
  @spec certify_deferred(Env.t()) :: Env.t()
  def certify_deferred(%Env{totality_certified: nil} = env), do: env

  def certify_deferred(%Env{defs: defs} = env) do
    Enum.reduce(defs, env, fn {name, def}, acc ->
      cond do
        Env.total?(acc, name) ->
          acc

        is_nil(def.body) ->
          acc

        match?(%{body: {:hole, _}}, def) ->
          acc

        match?(%{body: {:extern, _}}, def) ->
          acc

        not is_nil(Map.get(def, :builtin_op)) ->
          acc

        true ->
          case Kernel.validate_certificate(acc, name) do
            {:ok, acc2} -> acc2
            {:error, _} -> acc
          end
      end
    end)
  end

  # -- seeds: globals appearing in family/constructor type positions ----------

  defp seed_globals(%Env{families: families, ctors: ctors}) do
    from_families =
      families |> Map.values() |> Enum.flat_map(fn f -> tele_globals(f.params) ++ tele_globals(f.indices) end)

    from_ctors =
      ctors
      |> Map.values()
      |> Enum.flat_map(fn c -> tele_globals(c.args) ++ Enum.flat_map(c.result_indices, &collect/1) end)

    MapSet.new(from_families ++ from_ctors)
  end

  defp tele_globals(tele), do: Enum.flat_map(tele, fn {_name, ty} -> collect(ty) end)

  # Transitive closure: a type-level function's callees are themselves type-level.
  defp close_unchecked(_env, [], acc), do: acc

  defp close_unchecked(env, [name | rest], acc) do
    case Env.get_def(env, name) do
      nil ->
        close_unchecked(env, rest, acc)

      %{body: body} ->
        fresh = body |> collect() |> Enum.reject(&MapSet.member?(acc, &1))
        close_unchecked(env, rest ++ fresh, Enum.reduce(fresh, acc, &MapSet.put(&2, &1)))
    end
  end

  # Certification is a proof obligation, so its dependency walk cannot use the
  # inspection helper's historical "missing means leaf" convention. Track the
  # first predecessor path while closing and fail before asking the kernel to
  # certify a caller whose body contains an unresolved global.
  defp checked_closure(%Env{} = env, roots) do
    roots = Enum.uniq(roots)
    queue = Enum.map(roots, &{&1, &1, [&1]})
    checked_closure(env, queue, MapSet.new(roots))
  end

  defp checked_closure(_env, [], seen), do: {:ok, seen}

  defp checked_closure(env, [{name, root, path} | rest], seen) do
    case Env.get_def(env, name) do
      nil ->
        if legitimate_boundary?(env, name) do
          checked_closure(env, rest, seen)
        else
          {:error, {:totality_closure_unresolved, %{definition: name, root: root, closure_path: path}}}
        end

      %{body: body} ->
        fresh = body |> collect() |> Enum.reject(&MapSet.member?(seen, &1))
        next = Enum.map(fresh, &{&1, root, path ++ [&1]})
        checked_closure(env, rest ++ next, Enum.reduce(fresh, seen, &MapSet.put(&2, &1)))
    end
  end

  defp legitimate_boundary?(env, name) do
    not is_nil(Env.builtin_op(env, name)) or not is_nil(Env.inline_hint(env, name))
  end

  # -- collect global names occurring in a Core term --------------------------

  defp collect({:global, n}), do: [n]
  defp collect({:pi, _g, d, c}), do: collect(d) ++ collect(c)
  defp collect({:lam, _g, d, b}), do: collect(d) ++ collect(b)
  defp collect({:app, f, a}), do: collect(f) ++ collect(a)

  defp collect({:data, _n, ps, is}),
    do: Enum.flat_map(ps, &collect/1) ++ Enum.flat_map(is, &collect/1)

  defp collect({:ctor, _n, args}), do: Enum.flat_map(args, &collect/1)

  defp collect({:case, s, m, brs}),
    do: collect(s) ++ collect(m) ++ Enum.flat_map(brs, fn {_c, _ar, b} -> collect(b) end)

  defp collect({:let, _g, ty, value, body}),
    do: collect(ty) ++ collect(value) ++ collect(body)

  defp collect({:effect_type, inner}), do: collect(inner)
  defp collect({:effect_pure, value}), do: collect(value)
  defp collect({:effect_bind, effect, continuation}), do: collect(effect) ++ collect(continuation)

  # Fail closed, like `Validator.children/1` and `Certificate.walk_node/4`: descend into
  # every element of an unrecognized node that is itself a term-tuple or a list of them.
  # The catch-all used to answer `[]` — "no globals here" — for any shape this list does not
  # name, so a global reachable only through such a node never entered the closure and was
  # never submitted for certification. That is a totality hole, not a missed optimisation.
  # Genuine leaves (`{:var,_}`, `{:type,_}`, `{:int_lit,_}`) carry only atoms and integers
  # and yield nothing.
  defp collect(term) when is_tuple(term) do
    term
    |> Tuple.to_list()
    |> Enum.flat_map(fn
      child when is_tuple(child) -> collect(child)
      children when is_list(children) -> Enum.flat_map(children, &collect_child/1)
      _leaf -> []
    end)
  end

  defp collect(_), do: []

  defp collect_child(child) when is_tuple(child), do: collect(child)
  defp collect_child(_other), do: []
end
