defmodule Cure.Migrate.Rules.RemovedModule do
  @moduledoc """
  Migration rule: a `use`/qualified reference to a stdlib module that was
  *removed* on this edition with no drop-in replacement. Unlike a rename, there
  is no name to rewrite to — the feature is gone — so this rule is **warn-only**:
  it returns `{:warn, lines}`, leaving the source untouched so the file still
  parses and the author can see exactly where the dead reference is, then port it
  by hand. This is the "at least emit a warning" path for changes that are not
  mechanically migratable.

  ## The removed set

  `@removed` maps each retired module name to a short reason, surfaced in this
  rule's moduledoc for the porter (the emitted warning carries the generic
  `warning_template`; the reason column documents intent):

    * `Std.Equal` — the value-level equality module was folded into
      `Std.Equatable`; port `Std.Equal` references there (the method names differ,
      so it is not a pure prefix rename).
    * `Std.Refine` — refinement types were removed from Cure (SMT trust-boundary
      decision); a refined type must be re-expressed as an ordinary type plus an
      explicit proof obligation, which no rewrite can synthesize.

  A module that was merely *renamed* (still exists, functions intact) is handled
  by `Cure.Migrate.Rules.ModuleRename`, which rewrites rather than warns.

  Reference shapes are the same two `ModuleRename` recognizes: an `{:import,
  [source: …], _}` `use` statement and a qualified `{:function_call, [name:
  "<Module>.<fn>"], _}` (plus a defensive bare dotted `{:variable, …}`).
  """

  alias Cure.Migrate.Rule

  # Removed module name → why (documentation only; the warning uses the template).
  @removed %{
    "Std.Equal" => "folded into Std.Equatable",
    "Std.Refine" => "refinement types were removed from Cure"
  }

  @doc "The registry entry for this rule."
  @spec rule() :: Rule.t()
  def rule do
    %Rule{
      id: :W_removed_module,
      description: "a reference to a removed stdlib module is flagged (no auto-migration)",
      phase: :syntactic,
      tier: :manual,
      since: "2026",
      enforced_in: "2026",
      detect_and_rewrite: &detect_and_rewrite/2,
      warning_template: "removed stdlib module: no automatic migration — port this reference by hand"
    }
  end

  @doc false
  @spec detect_and_rewrite(Rule.ast(), Rule.ctx()) :: Rule.result()
  def detect_and_rewrite(ast, _ctx) do
    case ast |> collect_lines([]) |> Enum.reverse() |> Enum.uniq() do
      [] -> :no_change
      lines -> {:warn, lines}
    end
  end

  # ── AST walk: collect the line of every reference to a removed module ─────────

  defp collect_lines({:import, meta, ch}, acc) do
    acc = if Map.has_key?(@removed, Keyword.get(meta, :source)), do: [location(meta, :name) | acc], else: acc
    collect_lines(ch, acc)
  end

  defp collect_lines({:function_call, meta, ch}, acc) do
    acc = if removed_qualified?(Keyword.get(meta, :name)), do: [location(meta, :callee) | acc], else: acc
    collect_lines(ch, acc)
  end

  defp collect_lines({:variable, meta, name}, acc) when is_binary(name) do
    if removed_qualified?(name), do: [location(meta, :name) | acc], else: acc
  end

  defp collect_lines({_k, _meta, ch}, acc) when is_list(ch), do: collect_lines(ch, acc)
  defp collect_lines({_k, _meta, name, inner}, acc) when is_binary(name), do: collect_lines(inner, acc)
  defp collect_lines(l, acc) when is_list(l), do: Enum.reduce(l, acc, &collect_lines/2)
  defp collect_lines(_other, acc), do: acc

  # ── Helpers ─────────────────────────────────────────────────────────────────

  # True iff `name` is a qualified reference whose module prefix is a removed one.
  defp removed_qualified?(name) when is_binary(name) do
    Enum.any?(@removed, fn {mod, _reason} -> String.starts_with?(name, mod <> ".") end)
  end

  defp removed_qualified?(_), do: false

  defp location(meta, role), do: Rule.source_span(meta, role) || Rule.source_line(meta)
end
