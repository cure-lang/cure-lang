defmodule Antigen.CertifyHardeningAntibodyTest do
  @moduledoc """
  A5 antibody — the certificate TRUST MARKER stays sound and terminating even
  under a forged or open certificate.

  `stuck_elim_delta` (the existing certificate-family antibody) exercises the
  δ-of-stuck-eliminator seam given a *legitimately certified total* signature
  (bodies minted through `Kernel.validate_certificate`, which are closed by
  construction). It cannot reach the failure this pins, because the legit path
  never produces an open or non-total cert. This antibody attacks the marker
  itself — the two exposures flagged by the Phase-4a verification:

    * an OPEN certified body must never δ-unfold (it would eval in the empty env
      and leak/capture a context variable) — the "equates no distinct normal
      forms" guard specialised to the certificate seam;
    * a forged NON-TERMINATING cert must stay fuel-bounded under the metered
      conversion path — the termination guard.

  A `forge/2` raw-struct write bypasses `Env.certify/2` on purpose, to prove the
  `normalise` unfold-site backstop holds independently of the `certify` assertion.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Conv, Env, Inductive, Normalise}

  @nat {:data, :Nat, [], []}
  @z {:ctor, :Z, []}
  defp s(x), do: {:ctor, :S, [x]}

  defp nat_env do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Nat, [], [], 0), [
      Inductive.ctor(:Z, [], []),
      Inductive.ctor(:S, [{:n, @nat}], [])
    ])
  end

  # Raw-struct forgery of the certified marker (bypasses Env.certify/2).
  defp forge(env, name), do: %{env | certified: MapSet.put(env.certified, name)}

  test "termination guard: certify refuses to mint a marker for an open body" do
    env = Env.add_def(nat_env(), :bad, @nat, {:var, 3})
    assert_raise ArgumentError, fn -> Env.certify(env, :bad) end
  end

  test "soundness guard: a forged OPEN cert never δ-unfolds (no captured variable leaks)" do
    env = nat_env() |> Env.add_def(:bad, @nat, {:var, 3}) |> forge(:bad)
    ctx = Context.empty(env)

    # The open body's free `{:var, 3}` must not surface via δ. The neutral stays
    # un-unfolded; nothing outside the input term (no free/garbage index) appears.
    result = Normalise.nf(ctx, {:global, :bad})
    assert result == {:global, :bad}
    refute leaks_free_var?(result)
  end

  test "soundness guard: a forged open cert cannot equate the global with a distinct closed term" do
    env = nat_env() |> Env.add_def(:bad, @nat, {:var, 3}) |> forge(:bad)

    assert {:ok, false} = Conv.conv_within?({:global, :bad}, @z, [], 0, env, 200)
    assert {:ok, false} = Conv.conv_within?({:global, :bad}, s(@z), [], 0, env, 200)
  end

  test "termination guard: a forged NON-TERMINATING closed cert stays fuel-bounded" do
    env = nat_env() |> Env.add_def(:loop, @nat, {:global, :loop}) |> forge(:loop)

    # The normalizer recognizes an unfold that reproduces the exact neutral
    # head and freezes it immediately. It therefore returns a decisive false
    # result instead of spending the whole budget rediscovering the same loop.
    assert {:ok, false} = Conv.conv_within?({:global, :loop}, @z, [], 0, env, 200)
  end

  test "control: a legitimately certified CLOSED total body still δ-unfolds" do
    env = nat_env() |> Env.add_def(:k, @nat, s(@z)) |> Env.certify(:k)
    ctx = Context.empty(env)
    assert Normalise.nf(ctx, {:global, :k}) == s(@z)
  end

  # A leaked free variable would appear as a bare `{:var, k}` in the normal form
  # (the empty-env eval of an open body produced `{:var, -4}` pre-fix).
  defp leaks_free_var?({:var, _}), do: true
  defp leaks_free_var?(t) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&leaks_free_var?/1)
  defp leaks_free_var?(l) when is_list(l), do: Enum.any?(l, &leaks_free_var?/1)
  defp leaks_free_var?(_), do: false
end
