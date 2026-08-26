defmodule Cure.Elab.Rewrite do
  @moduledoc "Compile-time equality transport and rewrite planning."

  alias Cure.Core.{Grade, Inductive}
  alias Cure.Elab.Subst

  defmodule Occurrence do
    @moduledoc "A stable, left-to-right occurrence in a normalized rewrite target."
    @enforce_keys [:term, :source_path, :traversal_path, :number]
    defstruct [:term, :source_path, :traversal_path, :number]
  end

  def eq_parts({:vdata, family, [ty, a, b]}, signature) do
    if family == Inductive.builtin(signature, :eq),
      do: {:ok, ty, a, b},
      else: {:error, :rewrite_proof_not_equality}
  end

  def eq_parts(_other, _signature), do: {:error, :rewrite_proof_not_equality}

  def legacy_plan(proof, ty, a, b, expected) do
    cond do
      contains_term?(expected, a) ->
        with {:ok, symmetric} <- symmetry_proof(proof, ty, a),
             {:ok, motive} <- motive_for(expected, a, ty) do
          {:ok, fn body -> {:app, transport_case(symmetric, ty, motive, b), body} end, replace_term(expected, a, b)}
        end

      contains_term?(expected, b) ->
        {:ok, motive} = motive_for(expected, b, ty)

        {:ok, fn body -> {:app, transport_case(proof, ty, motive, a), body} end, replace_term(expected, b, a)}

      true ->
        {:error, {:rewrite_no_match, a, b, expected}}
    end
  end

  def directed_plan(proof, ty, a, b, expected, direction, selector \\ nil) do
    {target, replacement} = if direction == :backwards, do: {b, a}, else: {a, b}
    occurrences = occurrences(expected, target)

    with {:ok, occurrence} <- select_occurrence(occurrences, occurrences(expected, replacement), direction, selector),
         rewritten = replace_at(expected, occurrence.traversal_path, replacement),
         {:ok, motive} <- motive_at(expected, occurrence.traversal_path, ty),
         {:ok, transport_proof, left} <- transport_for_direction(direction, proof, ty, a, b) do
      {:ok, fn evidence -> {:app, transport_case(transport_proof, ty, motive, left), evidence} end, rewritten,
       occurrences}
    end
  end

  def directed_transform(proof, ty, a, b, proposition, direction, selector \\ nil) do
    {target, replacement} = if direction == :backwards, do: {b, a}, else: {a, b}
    occurrences = occurrences(proposition, target)

    with {:ok, occurrence} <- select_occurrence(occurrences, occurrences(proposition, replacement), direction, selector),
         rewritten = replace_at(proposition, occurrence.traversal_path, replacement),
         {:ok, motive} <- motive_at(proposition, occurrence.traversal_path, ty),
         {:ok, transport_proof, left} <- evidence_transport(direction, proof, ty, a, b) do
      {:ok, fn evidence -> {:app, transport_case(transport_proof, ty, motive, left), evidence} end, rewritten,
       occurrences}
    end
  end

  def occurrences(term, target) do
    term
    |> collect_occurrences(target, [])
    |> Enum.with_index(1)
    |> Enum.map(fn {{matched, path}, number} ->
      %Occurrence{term: matched, source_path: [:normalized_goal | path], traversal_path: path, number: number}
    end)
  end

  defp select_occurrence([], [_ | _], direction, _selector), do: {:error, {:reverse_only, direction}}
  defp select_occurrence([], [], _direction, _selector), do: {:error, {:no_occurrence, []}}
  defp select_occurrence([occurrence], _opposite, _direction, nil), do: {:ok, occurrence}

  defp select_occurrence(occurrences, _opposite, _direction, nil),
    do: {:error, {:ambiguous_occurrence, occurrences}}

  defp select_occurrence(occurrences, _opposite, _direction, number) when is_integer(number) and number > 0 do
    case Enum.find(occurrences, &(&1.number == number)) do
      nil -> {:error, {:invalid_occurrence, number, occurrences}}
      occurrence -> {:ok, occurrence}
    end
  end

  defp transport_for_direction(:backwards, proof, _ty, a, _b), do: {:ok, proof, a}

  defp transport_for_direction(:forward, proof, ty, a, b) do
    with {:ok, symmetric} <- symmetry_proof(proof, ty, a), do: {:ok, symmetric, b}
  end

  defp evidence_transport(:forward, proof, _ty, a, _b), do: {:ok, proof, a}

  defp evidence_transport(:backwards, proof, ty, a, b) do
    with {:ok, symmetric} <- symmetry_proof(proof, ty, a), do: {:ok, symmetric, b}
  end

  defp motive_at(expected, path, ty) do
    marker = {:global, :"$cure_rewrite_occurrence"}
    marked = replace_at(expected, path, marker)
    {:ok, {:lam, Grade.unrestricted(), ty, abstract_term(marked, marker, 0)}}
  end

  defp collect_occurrences(term, target, path) when term == target, do: [{term, path}]

  defp collect_occurrences({:pi, grade, domain, codomain}, target, path) do
    collect_occurrences(grade, target, path ++ [0]) ++
      collect_occurrences(domain, target, path ++ [1]) ++
      collect_occurrences(codomain, Subst.shift(target, 1, 0), path ++ [2])
  end

  defp collect_occurrences({:lam, grade, domain, body}, target, path) do
    collect_occurrences(grade, target, path ++ [0]) ++
      collect_occurrences(domain, target, path ++ [1]) ++
      collect_occurrences(body, Subst.shift(target, 1, 0), path ++ [2])
  end

  defp collect_occurrences({:case, scrutinee, motive, branches}, target, path) do
    collect_occurrences(scrutinee, target, path ++ [0]) ++
      collect_occurrences(motive, target, path ++ [1]) ++
      (branches
       |> Enum.with_index()
       |> Enum.flat_map(fn {{_constructor, arity, body}, index} ->
         collect_occurrences(body, Subst.shift(target, arity, 0), path ++ [2, index, 2])
       end))
  end

  defp collect_occurrences(term, target, path) do
    term
    |> children()
    |> Enum.with_index()
    |> Enum.flat_map(fn {child, index} -> collect_occurrences(child, target, path ++ [index]) end)
  end

  defp replace_at(_term, [], replacement), do: replacement

  defp replace_at(term, [index | rest], replacement) do
    updated = term |> children() |> List.update_at(index, &replace_at(&1, rest, replacement))
    rebuild(term, updated)
  end

  def mk_eq(ty, a, b), do: {:data, :"Std.Equivalent#Equivalent", [ty], [a, b]}
  def mk_refl(x), do: {:ctor, :"Std.Equivalent#reflexive", [x]}

  def transport_case(proof, ty, motive, left) do
    scrutinee_type =
      {:data, :"Std.Equivalent#Equivalent", [Subst.shift(ty, 2, 0)], [{:var, 1}, {:var, 0}]}

    arrow =
      {:pi, Grade.unrestricted(), {:app, Subst.shift(motive, 3, 0), {:var, 2}},
       {:app, Subst.shift(motive, 4, 0), {:var, 2}}}

    arrow_motive =
      {:lam, Grade.unrestricted(), ty,
       {:lam, Grade.unrestricted(), Subst.shift(ty, 1, 0), {:lam, Grade.unrestricted(), scrutinee_type, arrow}}}

    identity_domain = {:app, Subst.shift(motive, 1, 0), Subst.shift(left, 1, 0)}

    {:case, proof, arrow_motive,
     [{:"Std.Equivalent#reflexive", 1, {:lam, Grade.unrestricted(), identity_domain, {:var, 0}}}]}
  end

  def symmetry_proof(proof, ty, a) do
    motive_body = mk_eq(Subst.shift(ty, 1, 0), {:var, 0}, Subst.shift(a, 1, 0))
    motive = {:lam, Grade.unrestricted(), ty, motive_body}
    {:ok, {:app, transport_case(proof, ty, motive, a), mk_refl(a)}}
  end

  defp motive_for(expected, target, ty),
    do: {:ok, {:lam, Grade.unrestricted(), ty, abstract_term(expected, target, 0)}}

  def contains_term?(term, target),
    do: term == target or Enum.any?(children(term), &contains_term?(&1, target))

  @doc """
  Report whether an outer-context term occurs beneath binders, shifting the
  searched term as each binder is crossed. This is the occurrence-check twin of
  `replace_term_scoped/3`; using the binder-blind predicate before a scoped
  replacement can incorrectly discard a dependency exposed inside a case arm.
  """
  def contains_term_scoped?(term, target), do: do_contains_term_scoped?(term, target)

  defp do_contains_term_scoped?(term, target) when term == target, do: true

  defp do_contains_term_scoped?({:pi, _grade, domain, codomain}, target) do
    do_contains_term_scoped?(domain, target) or
      do_contains_term_scoped?(codomain, Subst.shift(target, 1, 0))
  end

  defp do_contains_term_scoped?({:lam, _grade, domain, body}, target) do
    do_contains_term_scoped?(domain, target) or
      do_contains_term_scoped?(body, Subst.shift(target, 1, 0))
  end

  defp do_contains_term_scoped?({:case, scrutinee, motive, branches}, target) do
    do_contains_term_scoped?(scrutinee, target) or
      do_contains_term_scoped?(motive, target) or
      Enum.any?(branches, fn {_constructor, arity, body} ->
        do_contains_term_scoped?(body, Subst.shift(target, arity, 0))
      end)
  end

  defp do_contains_term_scoped?(term, target) when is_list(term),
    do: Enum.any?(term, &do_contains_term_scoped?(&1, target))

  defp do_contains_term_scoped?(term, target),
    do: Enum.any?(children(term), &do_contains_term_scoped?(&1, target))

  def replace_term(term, target, replacement) when term == target, do: replacement

  def replace_term(term, target, replacement) when is_list(term),
    do: Enum.map(term, &replace_term(&1, target, replacement))

  def replace_term(term, target, replacement),
    do: rebuild(term, Enum.map(children(term), &replace_term(&1, target, replacement)))

  @doc """
  Replace a term beneath binders, shifting the target and replacement with the
  binder depth. Use this when the searched term originates in an outer context
  but the containing term may include Π/λ/case binders.
  """
  def replace_term_scoped(term, target, replacement),
    do: do_replace_term_scoped(term, target, replacement)

  defp do_replace_term_scoped(term, target, replacement) when term == target,
    do: replacement

  defp do_replace_term_scoped({:pi, grade, domain, codomain}, target, replacement) do
    {:pi, grade, do_replace_term_scoped(domain, target, replacement),
     do_replace_term_scoped(codomain, Subst.shift(target, 1, 0), Subst.shift(replacement, 1, 0))}
  end

  defp do_replace_term_scoped({:lam, grade, domain, body}, target, replacement) do
    {:lam, grade, do_replace_term_scoped(domain, target, replacement),
     do_replace_term_scoped(body, Subst.shift(target, 1, 0), Subst.shift(replacement, 1, 0))}
  end

  defp do_replace_term_scoped({:case, scrutinee, motive, branches}, target, replacement) do
    {:case, do_replace_term_scoped(scrutinee, target, replacement), do_replace_term_scoped(motive, target, replacement),
     Enum.map(branches, fn {constructor, arity, body} ->
       {constructor, arity,
        do_replace_term_scoped(
          body,
          Subst.shift(target, arity, 0),
          Subst.shift(replacement, arity, 0)
        )}
     end)}
  end

  defp do_replace_term_scoped(term, target, replacement) when is_list(term),
    do: Enum.map(term, &do_replace_term_scoped(&1, target, replacement))

  defp do_replace_term_scoped(term, target, replacement),
    do: rebuild(term, Enum.map(children(term), &do_replace_term_scoped(&1, target, replacement)))

  def abstract_term(term, target, depth) when term == target, do: {:var, depth}
  def abstract_term({:var, index}, _target, depth) when index >= depth, do: {:var, index + 1}
  def abstract_term({:var, _} = variable, _target, _depth), do: variable

  def abstract_term({:pi, grade, domain, codomain}, target, depth),
    do:
      {:pi, grade, abstract_term(domain, target, depth), abstract_term(codomain, Subst.shift(target, 1, 0), depth + 1)}

  def abstract_term({:lam, grade, domain, body}, target, depth),
    do: {:lam, grade, abstract_term(domain, target, depth), abstract_term(body, Subst.shift(target, 1, 0), depth + 1)}

  def abstract_term({:case, scrutinee, motive, branches}, target, depth) do
    {:case, abstract_term(scrutinee, target, depth), abstract_term(motive, target, depth),
     Enum.map(branches, fn {constructor, arity, body} ->
       {constructor, arity, abstract_term(body, Subst.shift(target, arity, 0), depth + arity)}
     end)}
  end

  def abstract_term(term, target, depth) when is_tuple(term),
    do: rebuild(term, Enum.map(children(term), &abstract_term(&1, target, depth)))

  def abstract_term(term, target, depth) when is_list(term),
    do: Enum.map(term, &abstract_term(&1, target, depth))

  def abstract_term(term, _target, _depth), do: term

  defp children(term) when is_tuple(term), do: term |> Tuple.to_list() |> tl()
  defp children(term) when is_list(term), do: term
  defp children(_term), do: []

  defp rebuild(term, children) when is_tuple(term), do: List.to_tuple([elem(term, 0) | children])
  defp rebuild(term, children) when is_list(term), do: children
  defp rebuild(term, _children), do: term
end
