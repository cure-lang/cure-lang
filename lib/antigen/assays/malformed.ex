defmodule Antigen.Assays.Malformed do
  @moduledoc """
  `term/rejection` — a NEGATIVE soundness vertical. Oracle = the known label
  (`:ill_typed`): a malformed term MUST be rejected by `Kernel.infer`. An accepted
  malformed term is a soundness infection (the kernel admitted a term with no valid
  type). Unlike `Assays.Term` (which treats an infer failure as a violation), this
  assay treats an infer *success* as the violation.

  Drives `infer`'s defensive rejection clauses that no well-typed generator reaches:
  `:absurd_in_reachable_position`, `:unknown_global`, `{:unknown_family, _}`,
  `{:unknown_ctor, _}`, `:case_scrutinee_not_data`, plus `ensure_pi`/`ensure_eq`
  guards.
  """
  alias Antigen.{Challenge, Generators}
  alias Cure.Core.Kernel

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :malformed, label: :ill_typed, payload: p}) do
    ctx = Generators.SigMenu.rebuild_context(Generators.SigMenu.env_of(p.sig), p.ctx)

    case Kernel.infer(ctx, p.term) do
      {:error, _} -> :ok
      {:ok, ty} -> {:violation, {:malformed_accepted, p.term, ty}}
    end
  end
end
