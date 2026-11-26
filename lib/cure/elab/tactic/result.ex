defmodule Cure.Elab.Tactic.Result do
  @moduledoc """
  Remaining goals and checked solutions produced by a tactic.

  Solutions are keyed by original goal identity, so sequencing and focusing
  retain the evidence needed to reconstruct a closed proof.
  """

  defstruct goals: [], solutions: %{}

  @type t :: %__MODULE__{
          goals: [Cure.Elab.ProofGoal.t()],
          solutions: %{reference() => %{evidence: term(), trace: [term()]}}
        }
end
