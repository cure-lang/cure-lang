defmodule Antigen.Assays.Totality do
  @moduledoc """
  `totality/diverging` + `totality/terminating` (spec §4.1). Oracle = the known
  label; the certifier is a static structural analysis that terminates on its own,
  so no fuel is needed.

    * `:diverging` — the certifier must NOT certify a by-construction non-terminating
      def. Any certified member is a **soundness infection** (the confirmed hole).
    * `:terminating` — the certifier must certify a by-construction total def. A
      rejected member is an incompleteness bug.
  """
  alias Antigen.{Challenge, Generators}
  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :def_group, label: :diverging, payload: %{focus: focus}} = c) do
    env = Generators.Totality.env_of(c)
    certified = Enum.filter(focus, &certifies?(env, &1))
    if certified == [], do: :ok, else: {:violation, {:wrongly_certified, certified}}
  end

  def run(%Challenge{kind: :def_group, label: :terminating, payload: %{focus: focus}} = c) do
    env = Generators.Totality.env_of(c)
    rejected = Enum.reject(focus, &certifies?(env, &1))
    if rejected == [], do: :ok, else: {:violation, {:wrongly_rejected, rejected}}
  end

  defp certifies?(env, name), do: Cure.Elab.TotalityClosure.provably_total?(env, name)
end
