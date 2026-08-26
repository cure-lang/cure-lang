defmodule Cure.Core.MetaCheck do
  @moduledoc """
  Metatheory regression harnesses for the trusted Core (K11a): subject reduction
  (#638) and progress (#639). These are property predicates driven over corpora
  by the harness test files; they are guardrails, not proofs, and each corpus
  grows as later waves land.
  """

  alias Cure.Core.{Kernel, Conv, Context}

  @doc """
  Subject reduction (#638): `term` infers a type, its normal form infers a type,
  and the two types are definitionally equal. False if ill-typed or fuel-exhausted.
  """
  @spec type_preserved?(Context.t(), tuple()) :: boolean()
  def type_preserved?(ctx, term) do
    with {:ok, ty1} <- Kernel.infer(ctx, term),
         nf when nf != :fuel_exhausted <- Kernel.normalize(ctx, term),
         {:ok, ty2} <- Kernel.infer(ctx, nf) do
      Conv.conv_values?(ty1, ty2, Context.length(ctx), Context.signature(ctx))
    else
      _ -> false
    end
  end

  @doc """
  Progress (#639): a closed well-typed `term` normalizes (no fuel exhaustion) to a
  term with a canonical/value head — never a stuck eliminator. False if ill-typed.
  """
  @spec progresses?(Context.t(), tuple()) :: boolean()
  def progresses?(ctx, term) do
    case Kernel.infer(ctx, term) do
      {:ok, _ty} ->
        case Kernel.normalize(ctx, term) do
          :fuel_exhausted -> false
          nf -> canonical_head?(nf)
        end

      _ ->
        false
    end
  end

  defp canonical_head?({:lam, _, _, _}), do: true
  defp canonical_head?({:ctor, _, _}), do: true
  defp canonical_head?({:type, _}), do: true
  defp canonical_head?({:pi, _, _, _}), do: true
  defp canonical_head?({:data, _, _, _}), do: true
  # NOTE(int-facade): kept for totality on a legacy/deserialized `{:int_type}`
  # node; fresh elaboration never produces one (spec 2026-07-18 §3a).
  defp canonical_head?({:int_type}), do: true
  defp canonical_head?({:int_lit, _}), do: true
  defp canonical_head?({:nat_lit, _}), do: true
  defp canonical_head?({:bounded_lit, _}), do: true
  defp canonical_head?({:float_type}), do: true
  defp canonical_head?({:binary_type}), do: true
  defp canonical_head?({:atom_type}), do: true
  defp canonical_head?({:atom_lit, _}), do: true
  defp canonical_head?({:float_lit, _}), do: true
  # Inert effect values are canonical heads (never stuck eliminators): a
  # well-typed `Effect`/`pure`/`bind` normal form progresses, it is not stuck.
  defp canonical_head?({:effect_type, _}), do: true
  defp canonical_head?({:effect_pure, _}), do: true
  defp canonical_head?({:effect_bind, _, _}), do: true
  defp canonical_head?(_), do: false
end
