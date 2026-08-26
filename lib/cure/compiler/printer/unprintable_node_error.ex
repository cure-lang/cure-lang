defmodule Cure.Compiler.Printer.UnprintableNodeError do
  @moduledoc """
  Raised when `Cure.Compiler.Printer` is asked to render an AST node kind it
  has no clause for. Whole-file reprint (migration facility, Approach A)
  requires the Printer to be total; a silent `inspect` fallback used to emit
  unparseable output (spec §3 Bug 1). Failing loudly converts a future gap
  into an immediate crash at the first offending node.
  """
  defexception [:node]

  @impl true
  def message(%__MODULE__{node: node}) do
    kind =
      case node do
        {k, _meta, _} when is_atom(k) -> inspect(k)
        _ -> "non-tuple"
      end

    pos =
      case node do
        {_k, meta, _} when is_list(meta) ->
          " at line #{Keyword.get(meta, :line, "?")}, col #{Keyword.get(meta, :col, "?")}"

        _ ->
          ""
      end

    "Printer has no clause for AST node kind #{kind}#{pos}. " <>
      "Add a `to_string/3` clause in Cure.Compiler.Printer. Node: #{inspect(node)}"
  end
end
