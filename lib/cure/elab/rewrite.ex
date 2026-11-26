defmodule Cure.Elab.Rewrite do
  @moduledoc "Compile-time equality transport and rewrite planning."

  alias Cure.Core.{Grade, Inductive, Normalise, Term}
  alias Cure.Elab.Subst

  defmodule Occurrence do
    @moduledoc "A stable, left-to-right occurrence in a normalized rewrite target."
    @enforce_keys [:term, :source_path, :traversal_path, :number]
    defstruct [:term, :source_path, :traversal_path, :number]
  end

  def eq_parts({:vdata, family, [_level, ty, a, b]}, signature) do
    if family == Inductive.builtin(signature, :eq),
      do: {:ok, Normalise.whnf_value(ty, signature), a, b},
      else: {:error, :rewrite_proof_not_equality}
  end

  def eq_parts({:vdata, family, [ty, a, b]}, signature) do
    if family == Inductive.builtin(signature, :eq),
      do: {:ok, Normalise.whnf_value(ty, signature), a, b},
      else: {:error, :rewrite_proof_not_equality}
  end

  def eq_parts(_other, _signature), do: {:error, :rewrite_proof_not_equality}

  def legacy_plan(proof, ty, a, b, expected) do
    cond do
      contains_term_scoped?(expected, a) ->
        with {:ok, symmetric} <- symmetry_proof(proof, ty, a),
             {:ok, motive} <- motive_for(expected, a, ty) do
          {:ok, fn body -> {:app, transport_case(symmetric, ty, motive, b), body} end,
           replace_term_scoped(expected, a, b)}
        end

      contains_term_scoped?(expected, b) ->
        {:ok, motive} = motive_for(expected, b, ty)

        {:ok, fn body -> {:app, transport_case(proof, ty, motive, a), body} end, replace_term_scoped(expected, b, a)}

      true ->
        {:error, {:rewrite_no_match, a, b, expected}}
    end
  end

  @doc """
  Rewrite EVERY occurrence of the theorem's target side, left to right.

  Opt-in (`rewrite using e all`). The default stays single-occurrence, where
  an ambiguous match is `E111` — stricter than Lean's silent rewrite-all.

  Each step is an ordinary single-occurrence transport over the term produced
  by the previous step, so the composed builder is a chain of already-proven
  transports rather than a new kind of evidence. A step that finds no
  occurrence stops the fold, which makes `all` idempotent on a fully-rewritten
  goal instead of failing.

  Level-atom paths use one ordinary transport with a batched motive instead:
  canonical rebuilding can merge or reorder atoms, so sequential reuse of
  original numeric paths would rewrite the wrong occurrence. Both paths are
  checked by the same kernel at the original goal.
  """
  def directed_plan(proof, ty, a, b, expected, direction, selector \\ nil)

  def directed_plan(proof, ty, a, b, expected, direction, :all) do
    {target, replacement} = if direction == :backwards, do: {b, a}, else: {a, b}
    occurrences = occurrences(expected, target)

    cond do
      Enum.any?(occurrences, &level_path?(expected, &1.traversal_path)) ->
        paths = Enum.map(occurrences, & &1.traversal_path)
        marker = {:global, :"$cure_rewrite_occurrence"}
        rewritten = replace_paths(expected, paths, replacement, 0)
        marked = replace_paths(expected, paths, marker, 0)
        motive = {:lam, motive_grade(ty), ty, abstract_term(marked, marker, 0)}

        with {:ok, transport_proof, left} <- transport_for_direction(direction, proof, ty, a, b) do
          build = fn evidence -> {:app, transport_case(transport_proof, ty, motive, left), evidence} end
          {:ok, build, rewritten, occurrences}
        end

      occurrences != [] ->
        Enum.reduce(occurrences, {:ok, fn evidence -> evidence end, expected, occurrences}, fn occurrence,
                                                                                               {:ok, outer, term, all} ->
          rewritten = replace_at(term, occurrence.traversal_path, replacement)
          {:ok, motive} = motive_at(term, occurrence.traversal_path, ty)
          {:ok, transport_proof, left} = transport_for_direction(direction, proof, ty, a, b)
          build = fn evidence -> {:app, transport_case(transport_proof, ty, motive, left), evidence} end
          {:ok, fn evidence -> outer.(build.(evidence)) end, rewritten, all}
        end)

      occurrences(expected, replacement) != [] ->
        {:error, {:reverse_only, direction}}

      true ->
        {:error, {:no_occurrence, []}}
    end
  end

  def directed_plan(proof, ty, a, b, expected, direction, selector) do
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
    {:ok, {:lam, motive_grade(ty), ty, abstract_term(marked, marker, 0)}}
  end

  # Rebuilding a level can reorder or merge atoms. Transform all selected
  # ORIGINAL paths before rebuilding that level; never reuse stale positions.
  defp level_path?(_term, []), do: false
  defp level_path?({tag, _}, [_ | _]) when tag in [:type, :level_value], do: true

  defp level_path?(term, [index | rest]),
    do: level_path?(Enum.fetch!(children(term), index), rest)

  defp paths_below(paths, index), do: for([head | tail] <- paths, head == index, do: tail)

  defp replace_paths(term, [], _replacement, _depth), do: term

  defp replace_paths(term, paths, replacement, depth) do
    if [] in paths,
      do: Subst.shift(replacement, depth, 0),
      else: replace_path_children(term, paths, replacement, depth)
  end

  defp replace_path_children({tag, grade, domain, body}, paths, replacement, depth) when tag in [:pi, :lam],
    do:
      {tag, grade, replace_paths(domain, paths_below(paths, 1), replacement, depth),
       replace_paths(body, paths_below(paths, 2), replacement, depth + 1)}

  defp replace_path_children({:let, grade, type, value, body}, paths, replacement, depth),
    do:
      {:let, grade, replace_paths(type, paths_below(paths, 1), replacement, depth),
       replace_paths(value, paths_below(paths, 2), replacement, depth),
       replace_paths(body, paths_below(paths, 3), replacement, depth + 1)}

  defp replace_path_children({:case, scrutinee, motive, branches}, paths, replacement, depth) do
    branch_paths = paths_below(paths, 2)

    branches =
      branches
      |> Enum.with_index()
      |> Enum.map(fn {{constructor, arity, body}, index} ->
        selected = branch_paths |> paths_below(index) |> paths_below(1)
        {constructor, arity, replace_paths(body, selected, replacement, depth + arity)}
      end)

    {:case, replace_paths(scrutinee, paths_below(paths, 0), replacement, depth),
     replace_paths(motive, paths_below(paths, 1), replacement, depth), branches}
  end

  defp replace_path_children(term, paths, replacement, depth) do
    updated =
      term
      |> children()
      |> Enum.with_index()
      |> Enum.map(fn {child, index} -> replace_paths(child, paths_below(paths, index), replacement, depth) end)

    rebuild(term, updated)
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

  defp collect_occurrences({:let, _grade, type, value, body}, target, path) do
    collect_occurrences(type, target, path ++ [1]) ++
      collect_occurrences(value, target, path ++ [2]) ++
      collect_occurrences(body, Subst.shift(target, 1, 0), path ++ [3])
  end

  defp collect_occurrences({:case, scrutinee, motive, branches}, target, path) do
    collect_occurrences(scrutinee, target, path ++ [0]) ++
      collect_occurrences(motive, target, path ++ [1]) ++
      (branches
       |> Enum.with_index()
       |> Enum.flat_map(fn {{_constructor, arity, body}, index} ->
         collect_occurrences(body, Subst.shift(target, arity, 0), path ++ [2, index, 1])
       end))
  end

  defp collect_occurrences(term, target, path) do
    term
    |> children()
    |> Enum.with_index()
    |> Enum.flat_map(fn {child, index} -> collect_occurrences(child, target, path ++ [index]) end)
  end

  defp replace_at(term, path, replacement), do: replace_at(term, path, replacement, 0)

  defp replace_at(_term, [], replacement, depth), do: Subst.shift(replacement, depth, 0)

  defp replace_at({tag, grade, domain, body}, [2 | rest], replacement, depth) when tag in [:pi, :lam],
    do: {tag, grade, domain, replace_at(body, rest, replacement, depth + 1)}

  defp replace_at({:let, grade, type, value, body}, [3 | rest], replacement, depth),
    do: {:let, grade, type, value, replace_at(body, rest, replacement, depth + 1)}

  defp replace_at({:case, scrutinee, motive, branches}, [2, index, 1 | rest], replacement, depth) do
    branches =
      List.update_at(branches, index, fn {constructor, arity, body} ->
        {constructor, arity, replace_at(body, rest, replacement, depth + arity)}
      end)

    {:case, scrutinee, motive, branches}
  end

  defp replace_at(term, [index | rest], replacement, depth) do
    updated = term |> children() |> List.update_at(index, &replace_at(&1, rest, replacement, depth))
    rebuild(term, updated)
  end

  def mk_eq(ty, a, b), do: {:data, :"Std.Equivalent#Equivalent", [eq_level(ty), ty], [a, b]}
  def mk_eq(level, ty, a, b), do: {:data, :"Std.Equivalent#Equivalent", [level, ty], [a, b]}
  def mk_refl(x), do: {:ctor, :"Std.Equivalent#reflexive", [x]}

  defp eq_level({:type, {:finite, level}}), do: {:level_value, Cure.Core.UniverseLevel.succ(level)}
  defp eq_level(_ty), do: {:level_value, Cure.Core.UniverseLevel.zero()}

  @doc "An ordinary constant transport motive using the existing carrier-grade policy."
  def constant_motive(ty, expected),
    do: {:lam, motive_grade(ty), ty, Subst.shift(expected, 1, 0)}

  def transport_case(proof, ty, motive, left) do
    scrutinee_type =
      {:data, :"Std.Equivalent#Equivalent", [Subst.shift(eq_level(ty), 2, 0), Subst.shift(ty, 2, 0)],
       [{:var, 1}, {:var, 0}]}

    arrow =
      {:pi, Grade.unrestricted(), {:app, Subst.shift(motive, 3, 0), {:var, 2}},
       {:app, Subst.shift(motive, 4, 0), {:var, 2}}}

    arrow_motive =
      {:lam, motive_grade(ty), ty,
       {:lam, motive_grade(ty), Subst.shift(ty, 1, 0), {:lam, Grade.unrestricted(), scrutinee_type, arrow}}}

    identity_domain = {:app, Subst.shift(motive, 1, 0), Subst.shift(left, 1, 0)}

    {:case, proof, arrow_motive,
     [{:"Std.Equivalent#reflexive", 1, {:lam, Grade.unrestricted(), identity_domain, {:var, 0}}}]}
  end

  def symmetry_proof(proof, ty, a) do
    motive_body = mk_eq(Subst.shift(ty, 1, 0), {:var, 0}, Subst.shift(a, 1, 0))
    motive = {:lam, motive_grade(ty), ty, motive_body}
    {:ok, {:app, transport_case(proof, ty, motive, a), mk_refl(a)}}
  end

  defp motive_for(expected, target, ty),
    do: {:ok, {:lam, motive_grade(ty), ty, abstract_term(expected, target, 0)}}

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

  defp do_contains_term_scoped?({:let, _grade, type, value, body}, target) do
    do_contains_term_scoped?(type, target) or
      do_contains_term_scoped?(value, target) or
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

  defp do_replace_term_scoped({:let, grade, type, value, body}, target, replacement) do
    {:let, grade, do_replace_term_scoped(type, target, replacement), do_replace_term_scoped(value, target, replacement),
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

  def abstract_term({:let, grade, type, value, body}, target, depth),
    do:
      {:let, grade, abstract_term(type, target, depth), abstract_term(value, target, depth),
       abstract_term(body, Subst.shift(target, 1, 0), depth + 1)}

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

  defp motive_grade({:level_type}), do: :erased
  defp motive_grade(_domain), do: Grade.unrestricted()

  defp children({tag, _} = term) when tag in [:type, :level_value], do: Term.level_atoms(term)
  defp children({:level_type}), do: []
  defp children(term) when is_tuple(term), do: term |> Tuple.to_list() |> tl()
  defp children(term) when is_list(term), do: term
  defp children(_term), do: []

  defp rebuild({:type, sort} = term, atoms),
    do: {:type, Cure.Elab.UniverseTraversal.map_sort(sort, atom_replacements(term, atoms))}

  defp rebuild({:level_value, level} = term, atoms),
    do: {:level_value, Cure.Elab.UniverseTraversal.map_level(level, atom_replacements(term, atoms))}

  defp rebuild(term, children) when is_tuple(term), do: List.to_tuple([elem(term, 0) | children])
  defp rebuild(term, children) when is_list(term), do: children
  defp rebuild(term, _children), do: term

  defp atom_replacements(term, replacements) do
    original = Term.level_atoms(term)

    unless length(original) == length(replacements),
      do: raise(ArgumentError, "level rewrite changed its atom-slot arity")

    table = Map.new(Enum.zip(original, replacements))
    &Map.fetch!(table, &1)
  end
end
