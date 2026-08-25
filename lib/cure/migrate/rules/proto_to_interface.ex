defmodule Cure.Migrate.Rules.ProtoToInterface do
  @moduledoc """
  Migration rule: rewrite the legacy `proto`/`impl` keyword forms to the
  canonical `interface`/`implementation` forms (spec §5.3, the first
  `retires_keywords` rule). Semantics-preserving spelling change; body and
  trivia are preserved. The two forms are NOT structurally symmetric
  (confirmed in Task 9 Step 1): `proto`/`impl` share the generic `:container`
  tag discriminated by `container_type`, while `interface`/`implementation`
  are their own distinct tags with differently-named and, in `interface`'s
  case, partly *derived* (`defaults`) meta — so this rule constructs fresh
  meta for the target node rather than relabeling the source node's meta.
  `enforced_in: nil` — the keyword stays live until a future edition
  schedules its retirement.

  ## Tier: `:review`, not `:machine` (verified deviation from plan §Task 9)

  The plan assigned `:machine`, which would let `cure build` normalize the
  rewrite in-memory (`Cure.Migrate.commit/4` folds `:machine` rewrites under
  `:safe_only`, the mode `Cure.Compiler` uses in `migrate_warn/5`,
  `lib/cure/compiler.ex`). At the time this rule was written, `proto`/`impl`
  (`:protocol`/`:trait` containers) were compiled by the classic pipeline,
  whereas `interface`/`implementation` were handled only by the dependent
  elaborator (`Cure.Elab.Interface` / `Cure.Elab.Implementation`); normalizing
  the rewrite in-build would have rerouted the stdlib's own `Ord`/`Show` to a
  pipeline that could not yet compile them, turning `cure.compile_stdlib` red
  and breaking every build. The classic checker and code generator have since
  been removed entirely (see CHANGELOG.md's "[Unreleased] one dependent
  compiler pipeline" entry), and the stdlib has migrated off `proto`/`impl`
  (`Std.Comparable` replaces `Std.Ord`; `Std.Equatable` backs `==`/`!=`), so
  that specific build-breakage risk no longer applies. `:review` remains the
  conservative choice for a different reason now: `Cure.Elab.Declarations`,
  the dependent pipeline's sole elaborator for container declarations, has no
  clause for `:protocol`/`:trait` container types, so there is currently no
  pipeline that compiles a `proto`/`impl` declaration left un-rewritten under
  `:safe_only`. `cure migrate` (which runs `apply: :all`) still applies the
  rewrite as designed. Promoting to `:machine` should be paired with either
  adding dependent-pipeline support for the legacy containers or accepting
  that `:safe_only` leaves such a file uncompilable until `cure migrate` is
  run. This satisfies the plan's own tier definition (`:machine` = "certified
  semantics-preserving"; the rewrite is not, in-build) rather than its
  literal tag.
  """
  alias Cure.Compiler.Trivia
  alias Cure.Migrate.Rule

  @spec rule() :: Rule.t()
  def rule do
    %Rule{
      id: :W_proto_to_interface,
      description: "legacy `proto`/`impl` is rewritten to `interface`/`implementation`",
      phase: :syntactic,
      # See moduledoc: `:review`, not `:machine` — normalizing this rewrite
      # in-build reroutes the stdlib's proto/impl to the dependent pipeline,
      # which cannot yet compile Ord/Show, breaking every build.
      tier: :review,
      since: "2026",
      enforced_in: nil,
      retires_keywords: ["proto", "impl"],
      detect_and_rewrite: &detect_and_rewrite/2,
      warning_template: "`proto`/`impl` will be rewritten to `interface`/`implementation`"
    }
  end

  @spec detect_and_rewrite(Rule.ast(), Rule.ctx()) :: Rule.result()
  def detect_and_rewrite(ast, _ctx) do
    {new_ast, lines} = walk(ast, [])

    case lines do
      [] -> :no_change
      _ -> {:rewrite, new_ast, lines |> Enum.reverse() |> Enum.uniq()}
    end
  end

  # `proto`/`impl` are both `{:container, meta, body}`; `container_type`
  # (`:protocol` / `:trait`) is the real discriminator (Task 9 Step 1). Any
  # other `:container` (mod/rec/enum/...) recurses unchanged.
  defp walk({:container, meta, body}, lines) do
    case Keyword.get(meta, :container_type) do
      :protocol ->
        {new_body, lines} = walk(body, lines)

        new_meta = [
          name: Keyword.fetch!(meta, :name),
          params: Keyword.get(meta, :type_params, []),
          defaults: interface_defaults(new_body),
          line: Rule.source_line(meta),
          col: Keyword.get(meta, :col)
        ]

        # Carry the container node's own leading/trailing/trailer comments onto
        # the new node (`Trivia.carry/2`, the helper for restructuring rules);
        # body-node trivia rides along inside `new_body`.
        new_node = Trivia.carry({:container, meta, body}, {:interface, new_meta, new_body})
        {new_node, [Rule.source_span(meta, :opener) || Rule.source_line(meta) | lines]}

      :trait ->
        {new_body, lines} = walk(body, lines)

        new_meta =
          [
            interface: Keyword.fetch!(meta, :protocol),
            for: Keyword.fetch!(meta, :for),
            for_type: Keyword.fetch!(meta, :for_type),
            as: nil,
            line: Rule.source_line(meta),
            col: Keyword.get(meta, :col)
          ]
          |> maybe_put(:constraints, Keyword.get(meta, :constraints))

        new_node =
          Trivia.carry({:container, meta, body}, {:implementation, new_meta, new_body})

        {new_node, [Rule.source_span(meta, :opener) || Rule.source_line(meta) | lines]}

      _ ->
        {new_body, lines} = walk(body, lines)
        {{:container, meta, new_body}, lines}
    end
  end

  defp walk({k, meta, ch}, lines) when is_list(ch) do
    {ch, lines} = walk(ch, lines)
    {{k, meta, ch}, lines}
  end

  defp walk({k, meta, name, inner}, lines) when is_binary(name) do
    {inner, lines} = walk(inner, lines)
    {{k, meta, name, inner}, lines}
  end

  defp walk(l, lines) when is_list(l), do: Enum.map_reduce(l, lines, &walk/2)
  defp walk(other, lines), do: {other, lines}

  # Mirrors parse_interface's own `defaults` derivation (parser.ex:3658-3664):
  # a method with a `= body` (a non-empty function_def) is a default.
  defp interface_defaults(body) do
    body
    |> Enum.flat_map(fn
      {:function_def, m, [expr | _]} -> [{Keyword.get(m, :name), expr}]
      _ -> []
    end)
    |> Map.new()
  end

  defp maybe_put(kw, _key, nil), do: kw
  defp maybe_put(kw, key, val), do: Keyword.put(kw, key, val)
end
