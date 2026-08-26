defmodule Antigen.Assays.Rewrite do
  @moduledoc """
  `rewrite/eq` (spec 2026-07-02-antigen-eq-rewrite). Oracle = the known label.
  The kernel must accept a challenge's def iff it is `:well_typed`: an
  `:ill_typed` challenge that `check_def` accepts is a **soundness infection**;
  a `:well_typed` challenge that `check_def` rejects is an incompleteness bug.
  """
  alias Antigen.{Challenge, Generators}
  alias Cure.Core.Kernel

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :rewrite_eq, label: label, payload: %{def_name: dn}} = c) do
    env = Generators.Rewrite.env_of(c)

    case {label, Kernel.check_def(env, dn)} do
      {:well_typed, :ok} -> :ok
      {:ill_typed, {:error, _}} -> :ok
      {:well_typed, {:error, reason}} -> {:violation, {:wrongly_rejected, {dn, reason}}}
      {:ill_typed, :ok} -> {:violation, {:wrongly_accepted, dn}}
    end
  end
end
