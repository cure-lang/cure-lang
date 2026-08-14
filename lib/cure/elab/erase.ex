defmodule Cure.Elab.Erase do
  @moduledoc """
  {0,ω} erasure of Core terms (design spec §8 / M9.1).

  Dependent indices exist only for type-checking; at runtime they carry no
  information, so erasure drops every `:erased` constructor argument (the
  quantities recorded by the elaborator, M8.3). What remains is a plain,
  non-dependent value the runtime can represent directly — e.g. `seq` erases from
  its seven-argument dependent form to the two stream functions it actually
  stores.

  `has_hole?/1` reports whether a term still contains an unfilled hole; a program
  with holes typechecks but must not be emitted (§6 negative #5).
  """

  alias Cure.Core.{Grade, Inductive}
  alias Cure.Elab.Collapsible

  @doc "Erase a Core term to its runtime form (drop erased constructor arguments)."
  @spec erase(Cure.Core.Env.t(), Cure.Core.Term.t()) :: Cure.Core.Term.t()
  def erase(env, {:ctor, cname, args}) do
    quantities = Inductive.ctor_quantities(env, cname) || List.duplicate(:unrestricted, length(args))

    if length(args) == length(quantities) do
      kept =
        args
        |> Enum.zip(quantities)
        # A runtime value exists for every grade EXCEPT `0`. Asking
        # `q == :unrestricted` would silently drop `:linear` and `:affine`
        # arguments — the grade carrier is not a two-point lattice any more.
        |> Enum.filter(fn {_arg, q} -> Grade.present?(q) end)
        |> Enum.map(fn {arg, _q} -> erase(env, arg) end)

      {:ctor, cname, kept}
    else
      # Fewer (or more) args than the ctor's full arity means the term is already
      # erased — re-zipping the full quantity vector against the shrunk arg list
      # would realign survivors onto leading positions and drop them. Keep every
      # arg and only recurse, so erase(erase(t)) == erase(t).
      {:ctor, cname, Enum.map(args, &erase(env, &1))}
    end
  end

  def erase(env, {:lam, g, dom, body}), do: {:lam, g, erase(env, dom), erase(env, body)}

  # The administrative identity `let x = value in x` is exactly `value`: it
  # neither duplicates nor drops evaluation. Proof-command facts commonly
  # finish in this shape, so eliminating it prevents compile-time command
  # scaffolding from becoming runtime BEAM structure. This is a general,
  # semantics-preserving Core erasure rule, not proof-specific lowering.
  def erase(env, {:let, _g, _ty, val, {:var, 0}}), do: erase(env, val)

  # Other `:let`s survive erasure: their whole point is that `val` is emitted ONCE and
  # bound to a BEAM variable. Dropping it here would reintroduce the duplication
  # the binder exists to remove. The ascription is erased like any other type.
  def erase(env, {:let, _g, ty, val, body}) do
    erased_value = erase(env, val)

    case erase(env, body) do
      {:var, 0} -> erased_value
      erased_body -> {:let, Cure.Core.Grade.unrestricted(), erase(env, ty), erased_value, erased_body}
    end
  end

  def erase(env, {:app, _f, _x} = app) do
    {head, args} = spine(app, [])

    erased =
      case head do
        # `cure_erased` is the terminal runtime representation of a proof/index
        # witness that has no computational content. Convoy discharge can expose
        # an application whose function position was itself an erased binder;
        # after that binder is replaced, the term is syntactically
        # `cure_erased(arg)`. It is not a constructor function and must not reach
        # Erlang lowering as a local call. The argument occupied an erased
        # position already validated by Relevance, so the whole application
        # contracts to the same terminal placeholder.
        {:ctor, :cure_erased, []} ->
          {:ctor, :cure_erased, []}

        {:case, scrutinee, motive, branches} when branches != [] ->
          case convoy_grades(branches, length(args)) do
            {:ok, grades} ->
              erased_branches =
                Enum.map(branches, fn {cname, arity, body} ->
                  {cname, arity, erase_convoy_body(env, body, grades)}
                end)

              erased_head = erase(env, {:case, scrutinee, motive, erased_branches})

              if erased_placeholder_application?(erased_head) do
                {:ctor, :cure_erased, []}
              else
                args
                |> Enum.zip(grades)
                |> Enum.filter(fn {_arg, grade} -> Grade.present?(grade) end)
                |> Enum.map(fn {arg, _grade} -> erase(env, arg) end)
                |> Enum.reduce(erased_head, fn arg, acc -> {:app, acc, arg} end)
              end

            :error ->
              args
              |> Enum.map(&erase(env, &1))
              |> Enum.reduce(erase(env, head), fn arg, acc -> {:app, acc, arg} end)
          end

        {:global, name} ->
          quantities =
            case Cure.Core.Env.get_def(env, name) do
              %{quantities: qs} when is_list(qs) -> qs
              _ -> List.duplicate(:unrestricted, length(args))
            end

          if length(args) >= length(quantities) do
            # Full or over-application: filter the callee's own parameters by their
            # quantity, and keep every argument beyond them (those apply to the
            # *result* `mk()(z)` and are always present).
            padded = quantities ++ List.duplicate(:unrestricted, length(args) - length(quantities))

            args
            |> Enum.zip(padded)
            # A runtime value exists for every grade EXCEPT `0`. Asking
            # `q == :unrestricted` would silently drop `:linear` and `:affine`
            # arguments — the grade carrier is not a two-point lattice any more.
            |> Enum.filter(fn {_arg, q} -> Grade.present?(q) end)
            |> Enum.map(fn {arg, _q} -> erase(env, arg) end)
            |> Enum.reduce({:global, name}, fn arg, acc -> {:app, acc, arg} end)
          else
            # Fewer args than the callee's parameters means the erased ones were
            # already dropped by a prior pass; re-filtering would realign the full
            # quantity vector and drop a present arg. Keep all, recurse — idempotent.
            args
            |> Enum.map(&erase(env, &1))
            |> Enum.reduce({:global, name}, fn arg, acc -> {:app, acc, arg} end)
          end

        # A constructor heading a curried spine is the same term as the flat `{:ctor, name, args}`
        # node, and must erase to the same runtime shape. The bare fallback below kept every
        # argument, erased ones included — so an erased index literally survived into the runtime
        # term, and two Core encodings of one value erased differently. `Relevance`, the dual
        # pass, already anticipates this head shape in `callee_quantities/3`; `Erase` did not.
        {:ctor, cname, head_args} ->
          all = head_args ++ args
          quantities = Inductive.ctor_quantities(env, cname) || List.duplicate(:unrestricted, length(all))

          if length(all) >= length(quantities) do
            # Saturated (or over-applied, when a field is itself a function): the leading
            # `length(quantities)` arguments are the ctor's own fields and collapse into the flat
            # node; anything beyond applies to the result and is always present.
            {fields, extra} = Enum.split(all, length(quantities))

            kept =
              fields
              |> Enum.zip(quantities)
              # A runtime value exists for every grade EXCEPT `0`. Asking
              # `q == :unrestricted` would silently drop `:linear` and `:affine`
              # arguments — the grade carrier is not a two-point lattice any more.
              |> Enum.filter(fn {_arg, q} -> Grade.present?(q) end)
              |> Enum.map(fn {arg, _q} -> erase(env, arg) end)

            extra
            |> Enum.map(&erase(env, &1))
            |> Enum.reduce({:ctor, cname, kept}, fn arg, acc -> {:app, acc, arg} end)
          else
            # Partially applied, or already erased: filtering would realign the quantity vector
            # onto the wrong positions. Keep every argument and recurse, so erase(erase(t)) is
            # erase(t) — the same reasoning as the flat `{:ctor, …}` and `{:global, …}` clauses.
            args
            |> Enum.map(&erase(env, &1))
            |> Enum.reduce(erase(env, head), fn arg, acc -> {:app, acc, arg} end)
          end

        _ ->
          args
          |> Enum.map(&erase(env, &1))
          |> Enum.reduce(erase(env, head), fn arg, acc -> {:app, acc, arg} end)
      end

    if erased_placeholder_application?(erased), do: {:ctor, :cure_erased, []}, else: erased
  end

  def erase(env, {:pi, g, d, c}), do: {:pi, g, erase(env, d), erase(env, c)}

  def erase(env, {:data, n, ps, is}),
    do: {:data, n, Enum.map(ps, &erase(env, &1)), Enum.map(is, &erase(env, &1))}

  # Collapsible-family elimination (Phase B, spec "Phase-B encoding amendment"):
  # a case whose single branch names the sole constructor of its family, all of
  # whose fields are erased (e.g. `Equivalent`'s `reflexive`), carries zero
  # runtime information — the matched shape is forced, so the case erases to its
  # branch body outright (Brady/McBride/McKinna collapsible families; this is
  # what lets the J/subst transport's proof scrutinee vanish at runtime exactly
  # as the retired `{:rewrite}` node's proof did). The branch's erased binders
  # are instantiated with an inert placeholder: they can only occur in positions
  # erasure drops anyway (all fields are `:erased`, and erased pattern binders
  # are surface-inaccessible), so the placeholder never survives into runtime-
  # relevant code. MUST stay in lockstep with `Relevance.collapsible_case?/2`,
  # which exempts the scrutinee from the relevance check on the same class —
  # keeping the case here would emit a scrutinee referencing dropped binders.
  def erase(env, {:case, s, m, branches}) do
    case Collapsible.classify(env, branches) do
      :unreachable ->
        {:ctor, :cure_erased, []}

      {:collapse, {_cname, arity, body}} ->
        body
        |> Cure.Elab.Subst.instantiate(List.duplicate({:ctor, :cure_erased, []}, arity))
        |> then(&erase(env, &1))

      :runtime ->
        {:case, erase(env, s), erase(env, m), Enum.map(branches, fn {c, ar, b} -> {c, ar, erase(env, b)} end)}
    end
  end

  # Effect nodes are NEVER dropped (§5.3): erasure recurses into their subterms —
  # dropping any erased args WITHIN — but keeps the effect structure, since the
  # runtime must still perform the effect. Without these they hit the identity
  # catch-all and an erased arg inside an effect would survive to emit.
  def erase(env, {:effect_type, t}), do: {:effect_type, erase(env, t)}
  def erase(env, {:effect_pure, a}), do: {:effect_pure, erase(env, a)}
  def erase(env, {:effect_bind, e, k}), do: {:effect_bind, erase(env, e), erase(env, k)}

  def erase(_env, term), do: term

  defp spine({:app, f, x}, acc), do: spine(f, [x | acc])
  defp spine(head, acc), do: {head, acc}

  defp erased_placeholder_application?(term) do
    case spine(term, []) do
      {{:ctor, :cure_erased, []}, _arguments} -> true
      _ -> false
    end
  end

  defp convoy_grades(branches, arity) do
    grades = Enum.map(branches, fn {_cname, _ctor_arity, body} -> lambda_grades(body, arity, []) end)

    case grades do
      [first | rest] ->
        if length(first) == arity and Enum.all?(rest, &(&1 == first)), do: {:ok, first}, else: :error

      _ ->
        :error
    end
  end

  defp lambda_grades(_body, 0, acc), do: Enum.reverse(acc)
  defp lambda_grades({:lam, grade, _domain, body}, count, acc), do: lambda_grades(body, count - 1, [grade | acc])
  defp lambda_grades(_body, _count, _acc), do: []

  defp erase_convoy_body(env, body, []), do: erase(env, body)

  defp erase_convoy_body(env, {:lam, grade, domain, body}, [expected | rest]) do
    if Grade.erased?(expected) do
      body
      |> Cure.Elab.Subst.instantiate([{:ctor, :cure_erased, []}])
      |> then(&erase_convoy_body(env, &1, rest))
    else
      {:lam, grade, erase(env, domain), erase_convoy_body(env, body, rest)}
    end
  end

  @doc "Does the term still contain an unfilled hole?"
  @spec has_hole?(Cure.Core.Term.t()) :: boolean()
  def has_hole?({:hole, _name}), do: true
  def has_hole?({:lam, _g, d, b}), do: has_hole?(d) or has_hole?(b)
  def has_hole?({:let, _g, t, v, b}), do: has_hole?(t) or has_hole?(v) or has_hole?(b)
  def has_hole?({:pi, _g, d, c}), do: has_hole?(d) or has_hole?(c)
  def has_hole?({:app, f, x}), do: has_hole?(f) or has_hole?(x)
  def has_hole?({:ctor, _n, args}), do: Enum.any?(args, &has_hole?/1)
  def has_hole?({:data, _n, ps, is}), do: Enum.any?(ps ++ is, &has_hole?/1)

  def has_hole?({:case, s, m, branches}),
    do: has_hole?(s) or has_hole?(m) or Enum.any?(branches, fn {_c, _ar, b} -> has_hole?(b) end)

  def has_hole?({:effect_type, inner}), do: has_hole?(inner)
  def has_hole?({:effect_pure, value}), do: has_hole?(value)
  def has_hole?({:effect_bind, effect, continuation}), do: has_hole?(effect) or has_hole?(continuation)

  def has_hole?(_term), do: false
end
