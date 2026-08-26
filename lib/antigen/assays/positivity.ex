defmodule Antigen.Assays.Positivity do
  @moduledoc """
  `positivity` (spec §4.2). Oracle = the known label. The kernel must accept a
  family iff it is strictly positive: a labeled-negative family that is accepted,
  or a labeled-positive family that is rejected, is an infection.
  """
  alias Antigen.{Challenge, Generators}
  alias Cure.Core.Inductive

  # Real kernel op, the byte-identical default for the `:family` `run/1` clause.
  @real_kernel %{positive?: &Inductive.positive?/2}

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :family} = c), do: run(c, @real_kernel)

  # Multi-family positivity challenge (W4 through-constructor shape): reuses the
  # :indexed_case record shape; the SUBJECT family is by convention the LAST
  # entry of payload.families. The def slot is an inert placeholder.
  def run(%Challenge{kind: :indexed_case, assay: "positivity", label: label, payload: %{families: families}} = c) do
    env = Generators.Indexed.env_of(c)
    {%{name: subject}, _ctors} = List.last(families)
    verdict = Inductive.positive?(env, Inductive.get_family(env, subject))

    case {label, verdict} do
      {:positive, :ok} -> :ok
      {:negative, {:error, _}} -> :ok
      {:positive, {:error, reason}} -> {:violation, {:wrongly_rejected, reason}}
      {:negative, :ok} -> {:violation, {:wrongly_accepted, subject}}
    end
  end

  @doc "Same as the `:family` `run/1` clause but with an injectable kernel-op map (sensitivity test seam)."
  def run(%Challenge{kind: :family, label: label, payload: %{family: fam}} = c, k) do
    env = Generators.Positivity.env_of(c)
    verdict = k.positive?.(env, Inductive.get_family(env, fam.name))

    case {label, verdict} do
      {:positive, :ok} -> :ok
      {:negative, {:error, _}} -> :ok
      {:positive, {:error, reason}} -> {:violation, {:wrongly_rejected, reason}}
      {:negative, :ok} -> {:violation, {:wrongly_accepted, fam.name}}
    end
  end
end
