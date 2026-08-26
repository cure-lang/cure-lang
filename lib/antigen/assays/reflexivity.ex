defmodule Antigen.Assays.Reflexivity do
  @moduledoc """
  `reflexivity-as-normalization` (spec §4.3). Reflexivity of conversion ≡ deep
  normalization, so a fuel-bounded `conv(t, t')` is a non-normalization detector
  that relies only on whether the checker *halts*, not on its verdict. Fuel
  exhaustion = a (suspected non-termination) infection.

  The fuel is a FIXED committed constant — identical on every machine and run mode
  — so a committed antibody replays to the same verdict everywhere (spec §8).
  """
  alias Antigen.{Challenge, Generators}
  alias Cure.Core.Conv

  # Fixed δ-unfold budget (spec §8). A genuinely-normalizing conversion resolves in
  # a handful of unfolds; this margin only ever trips on non-normalization.
  @fuel 500_000

  # Real kernel op, the byte-identical default for `run/1`.
  @real_kernel %{conv_within: &Conv.conv_within?/6}

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :forcing_pair} = c), do: run(c, @real_kernel)

  @doc "Same as `run/1` but with an injectable kernel-op map (sensitivity test seam)."
  def run(%Challenge{kind: :forcing_pair, payload: %{t: t, tprime: tprime}} = c, k) do
    env = Generators.Forcing.certified_env_of(c)

    case k.conv_within.(t, tprime, [], 0, env, @fuel) do
      :fuel_exhausted -> {:violation, {:non_normalizing, :conv_exceeded_fuel}}
      {:ok, _} -> :ok
    end
  end
end
