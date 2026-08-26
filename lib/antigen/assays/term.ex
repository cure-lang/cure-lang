defmodule Antigen.Assays.Term do
  @moduledoc """
  The Tier-B differential self-consistency assays (spec §7). Each consumes a
  `:typed_term` challenge and probes the kernel against itself:

    * term/infer_check       — infer(t)=A ⟹ check(t,A)=:ok ∧ A ≡ claimed T
    * term/subject_reduction — nf(t) still checks at A
    * term/normalization     — nf(nf t)=nf t, nf t re-checks, C2 round-trips
    * term/erasure_preservation — nf(erase t) ≡ erase(nf t) (erasure commutes with reduction)

  Fuel exhaustion at any stage is its own violation class `{:fuel_exhausted,
  stage}` — a suspected non-normalization, never conflated with a mismatch.
  """
  alias Antigen.Challenge
  alias Antigen.Generators.SigMenu
  alias Cure.Core.{Kernel, Normalise, Conv, Serialize, Context}
  alias Cure.Elab.Erase

  @assay_fuel 500_000
  def assay_fuel, do: @assay_fuel

  # Real kernel ops, the byte-identical default for `run/1`. `run/2` reads its
  # kernel calls from an injected map (Run C sensitivity seam); the other calls
  # (`Normalise`, `Conv`, `Serialize`) stay direct. `erase` is here (not direct)
  # so the erasure_preservation negative control can inject a corrupted eraser.
  @real_kernel %{infer: &Kernel.infer/2, check: &Kernel.check/3, erase: &Erase.erase/2}

  @doc "The real kernel-op map — extend it (`%{__real__() | op: stub}`) to inject a broken op."
  def __real__, do: @real_kernel

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :typed_term} = c), do: run(c, @real_kernel)

  @doc "Same as `run/1` but with an injectable kernel-op map (sensitivity test seam)."
  def run(%Challenge{kind: :typed_term, assay: assay, payload: p}, k) do
    env = SigMenu.env_of(p.sig)
    ctx = SigMenu.rebuild_context(env, p.ctx)

    case k.infer.(ctx, p.term) do
      {:ok, inferred} -> dispatch(assay, ctx, p, inferred, k)
      {:error, e} -> {:violation, {:infer_failed, e}}
    end
  end

  # --- term/infer_check ------------------------------------------------------
  defp dispatch("term/infer_check", ctx, p, inferred, k) do
    depth = Context.length(ctx)
    inferred_term = Normalise.quote(inferred, depth)

    cond do
      k.check.(ctx, p.term, inferred) != :ok ->
        {:violation, {:check_disagrees, k.check.(ctx, p.term, inferred)}}

      not converges?(inferred_term, p.type, ctx) ->
        {:violation, {:inferred_type_mismatch, inferred_term, p.type}}

      true ->
        :ok
    end
  end

  # --- term/subject_reduction ------------------------------------------------
  # `fuel: @assay_fuel` is required, not cosmetic: `Normalise.nf/3`'s default
  # (2-arg call) is `fuel: :infinity`, which would make `:fuel_exhausted`
  # below permanently unreachable — silently defeating locked decision #6
  # ("fixed committed fuel decides verdicts") and this module's own moduledoc
  # claim that fuel exhaustion is its own violation class.
  defp dispatch("term/subject_reduction", ctx, p, inferred, k) do
    case Normalise.nf(ctx, p.term, fuel: @assay_fuel) do
      :fuel_exhausted ->
        {:violation, {:fuel_exhausted, :nf}}

      nf ->
        case k.check.(ctx, nf, inferred) do
          :ok -> :ok
          err -> {:violation, {:nf_ill_typed, err}}
        end
    end
  end

  # --- term/normalization ----------------------------------------------------
  defp dispatch("term/normalization", ctx, p, inferred, k) do
    with nf when nf != :fuel_exhausted <- Normalise.nf(ctx, p.term, fuel: @assay_fuel),
         nf2 when nf2 != :fuel_exhausted <- Normalise.nf(ctx, nf, fuel: @assay_fuel) do
      cond do
        nf2 != nf -> {:violation, {:not_idempotent, nf, nf2}}
        k.check.(ctx, nf, inferred) != :ok -> {:violation, {:nf_ill_typed, nf}}
        not round_trips?(nf) -> {:violation, {:c2_round_trip, nf}}
        true -> :ok
      end
    else
      :fuel_exhausted -> {:violation, {:fuel_exhausted, :nf}}
    end
  end

  # --- term/erasure_preservation ---------------------------------------------
  # Formulation (a), spec §8-2: erasure commutes with reduction —
  # nf(erase t) ≡ erase(nf t). A sound eraser drops only computationally
  # irrelevant ({0}) arguments, so it cannot change what reduces; the two orders
  # of "erase" and "normalize" must agree. `erase` is read from the op-map so the
  # negative control can inject a reduction-state-dependent eraser (which breaks
  # the commutation). Compared via `Serialize.encode` (canonical), matching the
  # other assays' comparison discipline.
  defp dispatch("term/erasure_preservation", ctx, p, _inferred, k) do
    # Erase.erase needs the %Env{} SIGNATURE (to read ctor quantity vectors),
    # not Context.env/1's de Bruijn value environment.
    env = Context.signature(ctx)
    erased = k.erase.(env, p.term)

    with {:ok, nf_erased} <- nf_or_fuel(erased, ctx),
         {:ok, nf_t} <- nf_or_fuel(p.term, ctx) do
      erased_nf_t = k.erase.(env, nf_t)

      if Serialize.encode(nf_erased) == Serialize.encode(erased_nf_t) do
        :ok
      else
        {:violation, {:erasure_not_preserved, %{lhs: nf_erased, rhs: erased_nf_t}}}
      end
    else
      {:fuel, stage} -> {:violation, {:fuel_exhausted, stage}}
    end
  end

  # Normalize a Core term, distinguishing fuel exhaustion (matches how the
  # term/normalization clause reads `Normalise.nf/3`'s `:fuel_exhausted` sentinel).
  defp nf_or_fuel(term, ctx) do
    case Normalise.nf(ctx, term, fuel: @assay_fuel) do
      :fuel_exhausted -> {:fuel, :nf}
      nf -> {:ok, nf}
    end
  end

  defp converges?(t1, t2, ctx) do
    case Conv.conv_within?(t1, t2, Context.env(ctx), Context.length(ctx), Context.signature(ctx), @assay_fuel) do
      {:ok, true} -> true
      _ -> false
    end
  end

  defp round_trips?(term) do
    case Serialize.decode(Serialize.encode(term)) do
      {:ok, ^term} -> true
      _ -> false
    end
  end
end
