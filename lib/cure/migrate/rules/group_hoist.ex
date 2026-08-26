defmodule Cure.Migrate.Rules.GroupHoist do
  @moduledoc """
  Migration rule: relocate an in-body `@group(...)` decorator to directly above
  the module's `mod` declaration (spec §5.5). This is the facility's first
  *relocation* rule — it moves a node rather than transforming one in place.

  ## Representation

  A `@group(:x)` decorator parses to a standalone `{:decorator, [name: "group",
  …], [symbol]}` node that is a **sibling** in the top-level block's children,
  not a field on the module node. "Above `mod`" vs "in body" is purely the
  decorator's position in that sibling list relative to the
  `{:container, [container_type: :module, …], _}` node:

    * in-body   → `[container(mod), decorator, …]`
    * above-mod → `[decorator, container(mod), …]`

  So the hoist removes each group decorator sitting *after* the module container
  and re-inserts it immediately *before* that container, preserving their order.

  ## Trivia

  Because the decorator node itself is relocated (not rebuilt), its attached
  `:leading`/`:trailing` comments travel with it automatically — a trailing
  comment like `@group(:core)  # tag` rides above `mod`. Blank-line spacing
  between the hoisted decorator and `mod` is governed by the printer's §5.4
  rule 3 (exactly one blank between top-level items), not by this rule.

  Idempotent: a decorator already above the module container is left in place and
  produces no warning.
  """

  alias Cure.Migrate.Rule

  @doc "The registry entry for this rule."
  @spec rule() :: Rule.t()
  def rule do
    %Rule{
      id: :W_group_hoist,
      description: "an in-body `@group(...)` decorator is hoisted above `mod`",
      phase: :syntactic,
      tier: :machine,
      since: "2026",
      detect_and_rewrite: &detect_and_rewrite/2,
      warning_template: "`@group(...)` will be hoisted above `mod`"
    }
  end

  @doc false
  @spec detect_and_rewrite(Rule.ast(), Rule.ctx()) :: Rule.result()
  def detect_and_rewrite({:block, meta, children}, _ctx) do
    # A mover is an *in-body* `@group` decorator — one that sits AFTER some module
    # container AND is not already directly above a module. Each mover hoists to
    # just before its NEAREST PRECEDING module, not the first: a file may hold
    # more than one `mod`, and a group under a later module must stay with that
    # module (keying every mover to the first module silently re-associated the
    # group with the wrong one).
    #
    # "Already above-mod" must be excluded here, not just handled by `hoist/1`:
    # `cure migrate` runs `run_to_fixpoint`, which threads the AST between passes
    # WITHOUT reparsing. After pass 1 hoists a group directly above its module,
    # that decorator is a sibling sitting *after* the previous module — so a
    # detector that flagged it purely by "a module precedes it" would re-flag and
    # re-hoist it on pass 2, walking non-first-module groups one module toward the
    # top of the file each pass. Recognising the above-mod form makes the rewrite
    # idempotent (and correct on multi-module files).
    movers =
      for {node, idx} <- Enum.with_index(children),
          group_decorator?(node) and preceding_module?(children, idx) and
            not above_mod?(children, idx),
          do: node

    case movers do
      [] ->
        :no_change

      _ ->
        new_ast = {:block, meta, hoist(children)}
        {:rewrite, new_ast, Enum.map(movers, &decorator_line/1)}
    end
  end

  def detect_and_rewrite(_ast, _ctx), do: :no_change

  # True when a module container precedes position `idx` in the sibling list.
  defp preceding_module?(children, idx) do
    children |> Enum.take(idx) |> Enum.any?(&module_container?/1)
  end

  # True when the `@group` at `idx` is already directly above a module: every
  # sibling between it and the next module container is itself a group decorator
  # (a contiguous decorator stack atop that module). Such a group belongs to the
  # FOLLOWING module and is left in place — it is not an in-body mover.
  defp above_mod?(children, idx) do
    case children |> Enum.drop(idx + 1) |> Enum.drop_while(&group_decorator?/1) do
      [next | _] -> module_container?(next)
      [] -> false
    end
  end

  # Rebuild the sibling list so every in-body `@group` moves to just before its
  # own module. Nodes before the first module stay put (already above-mod); then
  # each module's segment (the run up to the next module) has its in-body group
  # decorators lifted ahead of that module, its other nodes kept after it. A
  # trailing run of group decorators at the END of a segment sits directly above
  # the NEXT module — those are that module's above-mod groups and stay put.
  defp hoist(children) do
    {prefix, rest} = Enum.split_while(children, &(not module_container?(&1)))
    prefix ++ hoist_segments(rest)
  end

  defp hoist_segments([]), do: []

  defp hoist_segments([container | tail]) do
    {segment_body, next} = Enum.split_while(tail, &(not module_container?(&1)))
    {body, trailing} = split_off_above_mod(segment_body, next)
    {groups, others} = Enum.split_with(body, &group_decorator?/1)
    groups ++ [container | others] ++ trailing ++ hoist_segments(next)
  end

  # Peel the contiguous run of group decorators at the END of a segment — when
  # another module follows, that run sits directly above it and must stay. With
  # no following module (`next == []`), every group belongs to the current
  # module's body and none is peeled.
  defp split_off_above_mod(segment_body, []), do: {segment_body, []}

  defp split_off_above_mod(segment_body, _next) do
    {rev_trailing, rev_body} =
      segment_body |> Enum.reverse() |> Enum.split_while(&group_decorator?/1)

    {Enum.reverse(rev_body), Enum.reverse(rev_trailing)}
  end

  defp module_container?({:container, meta, _}), do: Keyword.get(meta, :container_type) == :module
  defp module_container?(_), do: false

  defp group_decorator?({:decorator, meta, _}), do: Keyword.get(meta, :name) == "group"
  defp group_decorator?(_), do: false

  defp decorator_line({:decorator, meta, _}),
    do: Rule.source_span(meta, :name) || Rule.source_span(meta, :whole) || Rule.source_line(meta)
end
