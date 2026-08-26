defmodule Antigen.Assays.Mutation do
  @moduledoc """
  The inverted "rejection" assay (spec §6.1). An ill-typed `:mutant_term` MUST be
  rejected by `Kernel.infer`; a correct rejection (`{:error, _}`) passes (`:ok`),
  and acceptance (`{:ok, _}`) is an unsoundness antibody. Uses `infer` (needs no
  expected type) — its `{:error, _}` is the unambiguous "rejected" signal.
  """
  alias Antigen.Challenge
  alias Antigen.Generators.SigMenu
  alias Cure.Core.Kernel

  @spec run(Challenge.t()) :: :ok | {:violation, tuple()}
  def run(challenge), do: run(challenge, &Kernel.infer/2)

  @doc "Same as `run/1` but with an injectable infer function (test seam)."
  def run(%Challenge{kind: :mutant_term, payload: p}, infer_fun) do
    env = SigMenu.env_of(p.sig)
    ctx = SigMenu.rebuild_context(env, p.ctx)

    case infer_fun.(ctx, p.term) do
      {:error, _reason} -> :ok
      {:ok, _ty} -> {:violation, {:accepted_ill_typed, p.term, p.fault}}
    end
  end
end
