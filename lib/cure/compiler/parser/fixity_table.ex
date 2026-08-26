defmodule Cure.Compiler.Parser.FixityTable do
  @moduledoc """
  Session-scoped fixity table assembled from `precedencegroup`/`infix`/`prefix`/
  `postfix` declarations.

  The table records precedence *groups* (each with an associativity and a partial
  order over other groups, given by `higher_than`/`lower_than`) and the operator
  lexemes assigned to those groups. From the group partial order it computes an
  integer *binding power* per group, so the Pratt parser can bind operators
  exactly as the declarations require.

  This is the declaration-driven successor to the static
  `Cure.Compiler.Parser.Precedence` table. In this task it is purely additive:
  it is built and queried in isolation. Later tasks flip the expression parser's
  binding-power decisions onto it and retire the static module.

  ## Binding powers

  Groups are linearised from the `higher_than`/`lower_than` relation by a local
  Kahn topological sort (lowest-binding first) and assigned binding powers on a
  fixed stride so that a left/non-associative operator's `right = left + 1` never
  collides with the next group up. For a group `g` with binding power `bp`:

  - `:left`  → `infix_bp` = `{bp, bp + 1}`
  - `:none`  → `infix_bp` = `{bp, bp + 1}` (chaining is rejected separately)
  - `:right` → `infix_bp` = `{bp, bp}`

  ## Complexity

  Ranks and the reachability closure are computed once per `add_group/2` (groups
  are few, and construction is not a hot path). Every query —
  `infix_bp/2`, `non_assoc?/2`, `incomparable?/3` — is an O(1) map lookup, so the
  Pratt loop stays linear (heeds the parser-quadratic-token-lookup history).
  """

  @stride 10

  @type group_name :: atom()
  @type assoc :: :left | :right | :none
  @type fixity :: :infix | :prefix | :postfix

  defstruct groups: %{}, ops: %{}, ranks: %{}, reach: %{}

  @type op_entry :: %{group: group_name()}
  @type t :: %__MODULE__{
          groups: %{group_name() => %{assoc: assoc(), higher_than: [group_name()], lower_than: [group_name()]}},
          ops: %{String.t() => %{optional(fixity()) => op_entry()}},
          ranks: %{group_name() => pos_integer()},
          reach: %{group_name() => MapSet.t(group_name())}
        }

  @doc "An empty fixity table."
  @spec new() :: t()
  def new, do: %__MODULE__{}

  @doc """
  Register a precedence group.

  Options:
    * `:assoc` — `:left` (default), `:right`, or `:none`
    * `:higher_than` — groups this group binds tighter than (default `[]`)
    * `:lower_than` — groups this group binds looser than (default `[]`)

  Recomputes the memoized binding-power ranks and reachability closure.
  """
  @spec add_group(t(), group_name(), keyword()) :: t()
  def add_group(%__MODULE__{groups: groups} = table, name, opts \\ []) when is_atom(name) do
    entry = %{
      assoc: Keyword.get(opts, :assoc, :left),
      higher_than: Keyword.get(opts, :higher_than, []),
      lower_than: Keyword.get(opts, :lower_than, [])
    }

    %{table | groups: Map.put(groups, name, entry)}
    |> recompute()
  end

  @doc """
  Register an infix operator `lexeme` in `group`.

  A lexeme may hold both an infix and a prefix/postfix registration (e.g. `-`
  is infix subtraction *and* prefix negation); the fixities are stored side by
  side and the per-fixity queries pick out the one they need.
  """
  @spec add_infix(t(), String.t(), group_name(), keyword()) :: t()
  def add_infix(table, lexeme, group, opts \\ []), do: add_op(table, lexeme, :infix, group, opts)

  @doc "Register a prefix operator `lexeme` in `group`. See `add_infix/4`."
  @spec add_prefix(t(), String.t(), group_name(), keyword()) :: t()
  def add_prefix(table, lexeme, group, opts \\ []), do: add_op(table, lexeme, :prefix, group, opts)

  @doc "Register a postfix operator `lexeme` in `group`. See `add_infix/4`."
  @spec add_postfix(t(), String.t(), group_name(), keyword()) :: t()
  def add_postfix(table, lexeme, group, opts \\ []), do: add_op(table, lexeme, :postfix, group, opts)

  defp add_op(%__MODULE__{ops: ops} = table, lexeme, fixity, group, _opts)
       when is_binary(lexeme) and is_atom(group) do
    entry = %{group: group}
    by_fixity = ops |> Map.get(lexeme, %{}) |> Map.put(fixity, entry)
    %{table | ops: Map.put(ops, lexeme, by_fixity)}
  end

  @doc """
  Conflict-aware registration of an operator `lexeme` in a fixity slot.

  Unlike `add_infix`/`add_prefix`/`add_postfix` (last-write-wins), `merge_op`
  enforces the single-fixity-per-slot invariant used when assembling a module's
  fixity table from its `use`-closure:

    * slot empty → add it, `{:ok, table}`
    * slot holds the *same* group → no-op, `{:ok, table}`
    * slot holds a *different* group → `{:error, {:conflicting_operator_fixity,
      {lexeme, existing_group, new_group}}}`

  Different fixity slots for one lexeme (e.g. infix `-` and prefix `-`) never
  conflict.
  """
  @spec merge_op(t(), String.t(), fixity(), group_name()) ::
          {:ok, t()} | {:error, {:conflicting_operator_fixity, {String.t(), group_name(), group_name()}}}
  def merge_op(%__MODULE__{ops: ops} = table, lexeme, fixity, group)
      when is_binary(lexeme) and is_atom(group) and fixity in [:infix, :prefix, :postfix] do
    case ops |> Map.get(lexeme, %{}) |> Map.get(fixity) do
      nil -> {:ok, add_op(table, lexeme, fixity, group, [])}
      %{group: ^group} -> {:ok, table}
      %{group: other} -> {:error, {:conflicting_operator_fixity, {lexeme, other, group}}}
    end
  end

  @doc """
  Conflict-aware registration of a precedence group.

  Unlike `add_group` (last-write-wins), `merge_group` enforces one body per
  group name when assembling a module's fixity table:

    * name absent → add it, `{:ok, table}`
    * name present with an *identical* body → no-op, `{:ok, table}`
    * name present with a *different* body → `{:error,
      {:conflicting_precedence_group, {name, existing_body, new_body}}}`
  """
  @spec merge_group(t(), group_name(), keyword()) ::
          {:ok, t()} | {:error, {:conflicting_precedence_group, {group_name(), map(), map()}}}
  def merge_group(%__MODULE__{groups: groups} = table, name, opts) when is_atom(name) do
    new_body = group_body(opts)

    case Map.get(groups, name) do
      nil -> {:ok, add_group(table, name, opts)}
      ^new_body -> {:ok, table}
      existing -> {:error, {:conflicting_precedence_group, {name, existing, new_body}}}
    end
  end

  # Mirror EXACTLY the map `add_group/3` stores in `groups`.
  defp group_body(opts) do
    %{
      assoc: Keyword.get(opts, :assoc, :left),
      higher_than: Keyword.get(opts, :higher_than, []),
      lower_than: Keyword.get(opts, :lower_than, [])
    }
  end

  @doc """
  Returns `{left_bp, right_bp}` for an infix operator `lexeme`, or `:not_infix`
  when the lexeme is unregistered or registered with a non-infix fixity.
  """
  @spec infix_bp(t(), String.t()) :: {pos_integer(), pos_integer()} | :not_infix
  def infix_bp(%__MODULE__{ops: ops, groups: groups, ranks: ranks}, lexeme) do
    with %{infix: %{group: group}} <- Map.get(ops, lexeme),
         %{assoc: assoc} <- Map.get(groups, group),
         bp when is_integer(bp) <- Map.get(ranks, group) do
      right = if assoc == :right, do: bp, else: bp + 1
      {bp, right}
    else
      _ -> :not_infix
    end
  end

  @doc """
  The `{binding_power, associativity}` of a registered `lexeme` — its group's
  rank and associativity, with infix fixity preferred, then prefix, then postfix
  — or `:unknown` when the lexeme is unregistered. Only the ORDER of the binding
  power relative to other groups is significant. The printer uses this to
  parenthesise a reprint by any operator's real precedence, built-in or
  user-declared, instead of a hardcoded table.
  """
  @spec precedence(t(), String.t()) :: {pos_integer(), assoc()} | :unknown
  def precedence(%__MODULE__{ops: ops, groups: groups, ranks: ranks}, lexeme) do
    with group when is_atom(group) <- primary_group(Map.get(ops, lexeme)),
         %{assoc: assoc} <- Map.get(groups, group),
         bp when is_integer(bp) <- Map.get(ranks, group) do
      {bp, assoc}
    else
      _ -> :unknown
    end
  end

  @doc "Returns the right binding power of a prefix operator `lexeme`, or `:not_prefix`."
  @spec prefix_bp(t(), String.t()) :: pos_integer() | :not_prefix
  def prefix_bp(%__MODULE__{ops: ops, ranks: ranks}, lexeme) do
    with %{prefix: %{group: group}} <- Map.get(ops, lexeme),
         bp when is_integer(bp) <- Map.get(ranks, group) do
      bp
    else
      _ -> :not_prefix
    end
  end

  @doc """
  True when any of `lexeme`'s fixity groups is non-associative (`assoc: :none`),
  which the parser refuses to chain.
  """
  @spec non_assoc?(t(), String.t()) :: boolean()
  def non_assoc?(%__MODULE__{ops: ops, groups: groups}, lexeme) do
    case Map.get(ops, lexeme) do
      by_fixity when is_map(by_fixity) ->
        Enum.any?(by_fixity, fn {_fixity, %{group: group}} ->
          match?(%{assoc: :none}, Map.get(groups, group))
        end)

      _ ->
        false
    end
  end

  @doc "True when `lexeme` is registered in any fixity in this table."
  @spec declares?(t(), String.t()) :: boolean()
  def declares?(%__MODULE__{ops: ops}, lexeme), do: Map.has_key?(ops, lexeme)

  @doc """
  True when the two operators' groups are incomparable: neither group reaches the
  other in the transitive closure of the `higher_than`/`lower_than` relation.
  Unregistered lexemes are treated as incomparable.
  """
  @spec incomparable?(t(), String.t(), String.t()) :: boolean()
  def incomparable?(%__MODULE__{ops: ops, reach: reach}, lexeme_a, lexeme_b) do
    with ga when is_atom(ga) <- primary_group(Map.get(ops, lexeme_a)),
         gb when is_atom(gb) <- primary_group(Map.get(ops, lexeme_b)) do
      cond do
        ga == gb -> false
        MapSet.member?(Map.get(reach, ga, MapSet.new()), gb) -> false
        MapSet.member?(Map.get(reach, gb, MapSet.new()), ga) -> false
        true -> true
      end
    else
      _ -> true
    end
  end

  @doc """
  Returns the fixity of a registered `lexeme`, or `nil`. When a lexeme carries
  more than one fixity (e.g. `-` is both infix and prefix), the infix fixity is
  reported in preference, then prefix, then postfix.
  """
  @spec fixity(t(), String.t()) :: fixity() | nil
  def fixity(%__MODULE__{ops: ops}, lexeme) do
    case Map.get(ops, lexeme) do
      by_fixity when is_map(by_fixity) ->
        Enum.find([:infix, :prefix, :postfix], &Map.has_key?(by_fixity, &1))

      _ ->
        nil
    end
  end

  @doc """
  The precedence group a registered `lexeme` belongs to (infix fixity wins, then
  prefix, then postfix), or `nil` when the lexeme is unregistered. Used to name
  the groups in an `:ambiguous_precedence` parse error.
  """
  @spec group_of(t(), String.t()) :: group_name() | nil
  def group_of(%__MODULE__{ops: ops}, lexeme), do: primary_group(Map.get(ops, lexeme))

  # The representative group for a lexeme (infix wins, then prefix, then
  # postfix), used by `incomparable?/3` when a lexeme carries several fixities.
  defp primary_group(by_fixity) when is_map(by_fixity) do
    case Enum.find([:infix, :prefix, :postfix], &Map.has_key?(by_fixity, &1)) do
      nil -> nil
      fixity -> by_fixity |> Map.fetch!(fixity) |> Map.fetch!(:group)
    end
  end

  defp primary_group(_), do: nil

  @doc """
  The group names that lie on a declared precedence cycle, sorted, or `[]` when
  the relation is acyclic. A cycle means a set of groups each claim (directly or
  transitively) to bind tighter than one another — an unsatisfiable order the
  Kahn linearisation in `recompute/1` would otherwise resolve silently. A group
  is on a cycle exactly when it is reachable from one of its own successors along
  the ascending "binds looser -> binds tighter" edges.
  """
  @spec cyclic_groups(t()) :: [group_name()]
  def cyclic_groups(%__MODULE__{groups: groups}) do
    nodes = all_nodes(groups)
    edges = ascending_edges(groups, nodes)

    nodes
    |> Enum.filter(fn n ->
      succ = Map.get(edges, n, MapSet.new())
      MapSet.member?(dfs(edges, succ, MapSet.new()), n)
    end)
    |> Enum.sort()
  end

  # -- Ranking + reachability (memoized on add_group) -------------------------

  defp recompute(%__MODULE__{groups: groups} = table) do
    nodes = all_nodes(groups)
    edges = ascending_edges(groups, nodes)
    ordered = kahn(nodes, edges)

    ranks =
      ordered
      |> Enum.with_index(1)
      |> Map.new(fn {name, i} -> {name, i * @stride} end)

    %{table | ranks: ranks, reach: reachability(nodes, edges)}
  end

  # All group names mentioned anywhere: declared groups plus any referenced in a
  # relation before their own declaration is seen.
  defp all_nodes(groups) do
    Enum.reduce(groups, MapSet.new(Map.keys(groups)), fn {_name, %{higher_than: h, lower_than: l}}, acc ->
      acc |> add_all(h) |> add_all(l)
    end)
    |> MapSet.to_list()
  end

  defp add_all(set, names), do: Enum.reduce(names, set, &MapSet.put(&2, &1))

  # A directed "binds looser -> binds tighter" edge set. `a -> b` means group `a`
  # has a strictly lower binding power than `b`.
  #   higher_than: [x] on g  ⇒  g binds tighter than x  ⇒  edge x -> g
  #   lower_than:  [y] on g  ⇒  g binds looser than y   ⇒  edge g -> y
  defp ascending_edges(groups, nodes) do
    base = Map.new(nodes, &{&1, MapSet.new()})

    Enum.reduce(groups, base, fn {g, %{higher_than: higher, lower_than: lower}}, acc ->
      acc =
        Enum.reduce(higher, acc, fn x, a ->
          Map.update(a, x, MapSet.new([g]), &MapSet.put(&1, g))
        end)

      Enum.reduce(lower, acc, fn y, a ->
        Map.update(a, g, MapSet.new([y]), &MapSet.put(&1, y))
      end)
    end)
  end

  # Deterministic Kahn topological sort (ascending binding power first). Cycles,
  # if any are declared, degrade gracefully: remaining nodes are appended in
  # sorted order so the result is always a complete linearisation.
  defp kahn(nodes, edges) do
    indeg =
      Enum.reduce(edges, Map.new(nodes, &{&1, 0}), fn {_from, tos}, acc ->
        Enum.reduce(tos, acc, fn to, a -> Map.update(a, to, 1, &(&1 + 1)) end)
      end)

    frontier = for {n, 0} <- indeg, into: MapSet.new(), do: n
    do_kahn(frontier, indeg, edges, [])
  end

  defp do_kahn(frontier, indeg, edges, acc) do
    case MapSet.size(frontier) do
      0 ->
        # Any nodes left with positive in-degree are in a declared cycle; append
        # them deterministically rather than dropping them.
        leftover = for {n, d} <- indeg, d > 0, do: n
        Enum.reverse(acc) ++ Enum.sort(leftover)

      _ ->
        n = frontier |> MapSet.to_list() |> Enum.min()
        frontier = MapSet.delete(frontier, n)

        {indeg, frontier} =
          edges
          |> Map.get(n, MapSet.new())
          |> Enum.reduce({indeg, frontier}, fn m, {ind, fr} ->
            d = Map.get(ind, m, 0) - 1
            ind = Map.put(ind, m, d)
            fr = if d == 0, do: MapSet.put(fr, m), else: fr
            {ind, fr}
          end)

        # Mark `n` consumed so it never re-enters the frontier.
        do_kahn(frontier, Map.put(indeg, n, -1), edges, [n | acc])
    end
  end

  # Transitive closure: reach[a] = every group reachable from `a` following the
  # ascending edges (i.e. every group that binds strictly tighter than `a`).
  defp reachability(nodes, edges) do
    Map.new(nodes, fn n -> {n, dfs(edges, MapSet.new([n]), MapSet.new()) |> MapSet.delete(n)} end)
  end

  defp dfs(edges, frontier, seen) do
    case MapSet.to_list(MapSet.difference(frontier, seen)) do
      [] ->
        seen

      fresh ->
        seen = MapSet.union(seen, MapSet.new(fresh))

        next =
          Enum.reduce(fresh, MapSet.new(), fn n, acc ->
            MapSet.union(acc, Map.get(edges, n, MapSet.new()))
          end)

        dfs(edges, next, seen)
    end
  end
end
