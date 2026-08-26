defmodule Antigen.Assays.Indexed do
  @moduledoc """
  `indexed/case` (spec 2026-07-01-antigen-indexed-case). Oracle = the known label.
  The kernel must accept a challenge's def iff it is well-typed: a `:ill_typed`
  challenge that `check_def` accepts is a **soundness infection**; a `:well_typed`
  challenge that `check_def` rejects is an incompleteness bug.
  """
  alias Antigen.{Challenge, Generators}
  alias Cure.Core.Kernel

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :indexed_case, label: label, payload: %{def_name: dn}} = c) do
    env = Generators.Indexed.env_of(c)
    verdict = Kernel.check_def(env, dn)

    case {label, verdict} do
      {:well_typed, :ok} -> :ok
      {:ill_typed, {:error, _}} -> :ok
      # Legacy coverage corpus entries used `:ill_typed` for a case over the
      # literal `A`. Value-specialized coverage makes those terms well-typed;
      # retain them as positive replay seeds while the new
      # `coverage_unknown_gap` twin guards opaque-variable exhaustiveness.
      {:ill_typed, :ok} when dn == :coverage_gap -> :ok
      {:well_typed, {:error, reason}} -> {:violation, {:wrongly_rejected, {dn, reason}}}
      {:ill_typed, :ok} -> {:violation, {:wrongly_accepted, dn}}
    end
  end
end
