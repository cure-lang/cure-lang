defmodule Cure.Migrate.Rules.ModuleRename do
  @moduledoc """
  Migration rule: a `use`/qualified reference to a stdlib module that was
  *renamed* on this edition is updated to the module's new name. A rename is a
  pure spelling change — the module still exists and its public functions keep
  their names — so this is a fully mechanical, semantics-preserving rewrite.

  ## The rename table

  `@renames` maps each retired module name to its replacement. It is the single
  source of truth; adding a future rename is a one-line entry. Today it carries
  the `main`→this-edition renames uncovered by the branch inventory:

    * `Std.Eq` → `Std.Equatable` (the equality *protocol* was renamed to spell
      out its Idris2-style interface name; `eq/2`, `ne/2` are unchanged).

  A module that was *removed* with no replacement (e.g. `Std.Equal`, `Std.Refine`)
  is NOT a rename — it cannot be rewritten to anything — and is handled by the
  warn-only `Cure.Migrate.Rules.RemovedModule` rule instead.

  ## Where a module name appears

  Two reference shapes carry a module name and are rewritten in place:

    * `{:import, [source: "Std.Eq", …], _}` — a `use Std.Eq` statement, whose
      `:source` meta is the module name verbatim.
    * `{:function_call, [name: "Std.Eq.eq", …], _}` — a qualified call, whose
      `:name` meta is `"<Module>.<fn>"`. Only the module *prefix* (up to and
      including the final `.`) is rewritten; the function segment is untouched.

  A bare dotted `{:variable, _, "Std.Eq.x"}` (a qualified value not in call
  position) is rewritten the same way, defensively — an unqualified variable
  never matches a `"<Module>."` prefix so it is transparent.
  """

  alias Cure.Migrate.Rule

  # Retired module name → replacement. The whole rule is driven from this map.
  @renames %{"Std.Eq" => "Std.Equatable"}

  @doc "The registry entry for this rule."
  @spec rule() :: Rule.t()
  def rule do
    %Rule{
      id: :W_module_rename,
      description: "a reference to a renamed stdlib module is updated to its new name",
      phase: :syntactic,
      tier: :machine,
      since: "2026",
      enforced_in: "2026",
      detect_and_rewrite: &detect_and_rewrite/2,
      warning_template: "renamed stdlib module: reference updated to its new name"
    }
  end

  @doc false
  @spec detect_and_rewrite(Rule.ast(), Rule.ctx()) :: Rule.result()
  def detect_and_rewrite(ast, _ctx) do
    {new_ast, lines} = walk(ast, [])

    case lines do
      [] -> :no_change
      _ -> {:rewrite, new_ast, lines |> Enum.reverse() |> Enum.uniq()}
    end
  end

  # ── AST walk ────────────────────────────────────────────────────────────────

  # `use <Module>`: rename an exact module `source`.
  defp walk({:import, meta, ch}, lines) do
    {meta, lines} = walk_meta(meta, lines)
    {ch, lines} = walk(ch, lines)

    case Map.fetch(@renames, Keyword.get(meta, :source)) do
      {:ok, new} -> {{:import, Keyword.put(meta, :source, new), ch}, [location(meta, :name) | lines]}
      :error -> {{:import, meta, ch}, lines}
    end
  end

  # Qualified call `<Module>.<fn>(…)`: rename the module prefix of `name`.
  defp walk({:function_call, meta, ch}, lines) do
    {meta, lines} = walk_meta(meta, lines)
    {ch, lines} = walk(ch, lines)

    case rename_qualified(Keyword.get(meta, :name)) do
      {:ok, new} -> {{:function_call, Keyword.put(meta, :name, new), ch}, [location(meta, :callee) | lines]}
      :error -> {{:function_call, meta, ch}, lines}
    end
  end

  # Bare qualified value reference `<Module>.<name>` (defensive).
  defp walk({:variable, meta, name}, lines) when is_binary(name) do
    {meta, lines} = walk_meta(meta, lines)

    case rename_qualified(name) do
      {:ok, new} -> {{:variable, meta, new}, [location(meta, :name) | lines]}
      :error -> {{:variable, meta, name}, lines}
    end
  end

  # Attribute access chain `<Module>.<Attr>` in type/value positions.
  defp walk({:attribute_access, meta, [target]} = node, lines) do
    case rename_attribute_access(node) do
      {:ok, new_node, loc_meta} ->
        {new_node, [location(loc_meta, :name) | lines]}

      :error ->
        {meta, lines} = walk_meta(meta, lines)
        {target, lines} = walk(target, lines)
        {{:attribute_access, meta, [target]}, lines}
    end
  end

  defp walk({k, meta, ch}, lines) when is_list(meta) do
    {meta, lines} = walk_meta(meta, lines)
    {ch, lines} = walk(ch, lines)
    {{k, meta, ch}, lines}
  end

  defp walk({k, meta, name, inner}, lines) when is_binary(name) do
    {meta, lines} = walk_meta(meta, lines)
    {inner, lines} = walk(inner, lines)
    {{k, meta, name, inner}, lines}
  end

  defp walk(l, lines) when is_list(l) do
    Enum.map_reduce(l, lines, fn child, acc -> walk(child, acc) end)
  end

  defp walk(other, lines), do: {other, lines}

  defp rename_attribute_access({:attribute_access, meta, [{:variable, v_meta, "Std"}]}) do
    attr = Keyword.get(meta, :attribute)
    full = "Std." <> to_string(attr)

    case Map.fetch(@renames, full) do
      {:ok, new_full} ->
        "Std." <> new_attr = new_full
        {:ok, {:attribute_access, Keyword.put(meta, :attribute, new_attr), [{:variable, v_meta, "Std"}]}, meta}

      :error ->
        :error
    end
  end

  defp rename_attribute_access({:attribute_access, meta, [target]}) do
    case rename_attribute_access(target) do
      {:ok, new_target, loc_meta} ->
        {:ok, {:attribute_access, meta, [new_target]}, loc_meta}

      :error ->
        :error
    end
  end

  defp rename_attribute_access(_), do: :error

  defp walk_meta(meta, lines) when is_list(meta) do
    if Keyword.keyword?(meta) do
      Enum.map_reduce(meta, lines, fn {k, v}, lines ->
        {new_v, lines} = walk_meta_val(v, lines)
        {{k, new_v}, lines}
      end)
    else
      {meta, lines}
    end
  end

  defp walk_meta(meta, lines), do: {meta, lines}

  defp walk_meta_val({type, meta, _} = node, lines)
       when is_atom(type) and is_list(meta) and tuple_size(node) == 3 do
    walk(node, lines)
  end

  defp walk_meta_val(list, lines) when is_list(list) do
    if Enum.any?(list, &match?({t, m, _} when is_atom(t) and is_list(m), &1)) do
      Enum.map_reduce(list, lines, fn el, lines -> walk_meta_val(el, lines) end)
    else
      {list, lines}
    end
  end

  defp walk_meta_val(other, lines), do: {other, lines}

  # ── Helpers ─────────────────────────────────────────────────────────────────

  # `"Std.Eq.eq"` -> `{:ok, "Std.Equatable.eq"}` iff some rename key is a strict
  # module prefix (`"Std.Eq."`); `:error` otherwise (including a bare name with
  # no dot, which can never carry a module prefix).
  defp rename_qualified(name) when is_binary(name) do
    Enum.find_value(@renames, :error, fn {old, new} ->
      prefix = old <> "."

      if String.starts_with?(name, prefix) do
        rest = binary_part(name, byte_size(prefix), byte_size(name) - byte_size(prefix))
        {:ok, new <> "." <> rest}
      end
    end)
  end

  defp rename_qualified(_), do: :error

  defp location(meta, role), do: Rule.source_span(meta, role) || Rule.source_line(meta)
end
