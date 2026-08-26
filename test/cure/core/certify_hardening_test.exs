defmodule Cure.Core.CertifyHardeningTest do
  @moduledoc """
  Hardening of the certification trust marker (A5; two exposures flagged by the
  Phase-4a adversarial verification, a9962257).

  (1) `unfold_certified_head` (`normalise.ex`) evals a certified body in the EMPTY
      env, so an OPEN certified body's free de Bruijn variables surface as neutral
      `{:nvar, k}` and alias whatever the ambient context binds at level `k` — a
      capture. Fix: `Env.certify/2` refuses to certify an open body, and the
      unfold site stays stuck when handed a body that is not closed (robust even
      against a raw-struct forgery of the marker).

  (2) A forged cert on a NON-TOTAL (but closed) def must never let δ-unfolding
      diverge. For a bare self-loop (`loop : Nat = loop`), `unfold_certified_head`
      (`normalise.ex`) detects that δ-unfolding reproduces the IDENTICAL neutral
      each step (no progress possible, ever) and freezes it as stuck after a
      single step (07006ad4, added for indexed branch refinement) — so
      `conv_within?` now decides `{:ok, false}` almost immediately instead of
      spending its whole fuel budget. That is a sound answer (a term that only
      ever unfolds to itself can never become `Z`) and still never diverges;
      pinned here as a regression characterization. The unbounded `conv?/5`
      fast-path trusts certs, which only the kernel-validated path
      (`validate_certificate`) can legitimately produce.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Conv, Env, Inductive, Normalise}

  @nat {:data, :Nat, [], []}
  @z {:ctor, :Z, []}

  defp nat_env do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Nat, [], [], 0), [
      Inductive.ctor(:Z, [], []),
      Inductive.ctor(:S, [{:n, @nat}], [])
    ])
  end

  # `bad : Nat` with an OPEN body — the bare free variable `{:var, 3}` (no binder
  # encloses it, so index 3 escapes).
  defp env_with_open_bad, do: Env.add_def(nat_env(), :bad, @nat, {:var, 3})

  # Raw-struct forgery of the certified marker (bypasses `Env.certify/2`).
  defp forge_cert(env, name), do: %{env | certified: MapSet.put(env.certified, name)}

  describe "exposure (1): open certified body must never capture" do
    test "Env.certify refuses an open-bodied def (defense-in-depth)" do
      assert_raise ArgumentError, fn -> Env.certify(env_with_open_bad(), :bad) end
    end

    test "a raw-struct-forged open cert stays stuck under nf — no capture (backstop)" do
      env = forge_cert(env_with_open_bad(), :bad)
      ctx = Context.empty(env)

      # Pre-fix this unfolds the open body in the empty env and leaks the captured
      # free variable `{:var, 3}`. The backstop must instead leave the global
      # neutral un-unfolded.
      result = Normalise.nf(ctx, {:global, :bad})
      refute result == {:var, 3}
      assert result == {:global, :bad}
    end

    test "a certified def with a genuinely CLOSED body still unfolds (no regression)" do
      # `k : Nat = Z` — closed, total; certification and δ must still work.
      env = nat_env() |> Env.add_def(:k, @nat, @z) |> Env.certify(:k)
      ctx = Context.empty(env)
      assert Normalise.nf(ctx, {:global, :k}) == @z
    end
  end

  describe "exposure (2): forged non-total cert stays fuel-bounded (characterization)" do
    test "conv_within? on a forged non-total closed cert decides false, well within budget" do
      # `loop : Nat = loop` — closed (so the closed-body guard does not apply) but
      # non-total. A forged cert lets δ attempt to unfold it; `unfold_certified_head`
      # detects the unfold reproduces the IDENTICAL `{:nglobal, :loop}` neutral and
      # freezes it as stuck after one step, so conversion decides `loop` cannot be
      # `Z` — a sound answer, reached using almost none of the fuel budget. Never
      # `:fuel_exhausted`, and never a hang.
      env = nat_env() |> Env.add_def(:loop, @nat, {:global, :loop}) |> forge_cert(:loop)

      assert {:ok, false} = Conv.conv_within?({:global, :loop}, @z, env, 0, env, 50)
    end
  end
end
