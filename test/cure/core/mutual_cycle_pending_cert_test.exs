defmodule Cure.Core.MutualCyclePendingCertTest do
  @moduledoc """
  Termination certification must not certify a member of a *mutual* cycle while a
  sibling's body is still a pending placeholder. The elaborator registers every
  signature first, then elaborates bodies in declaration order, certifying each as
  it lands (`declarations.ex` `maybe_certify`, so a later def's type may δ-reduce
  an earlier total one). But `Certificate.mutual_group` reconstructs the SCC from
  sibling **bodies** read out of the env — and an as-yet-unelaborated sibling still
  carries a `{:hole, "__pending__"}` body with no visible callees. So the SCC
  collapses to a singleton, the size-change check sees no self-call, and a
  divergent mutual member (`f(n) = g(n)`, `g(n) = f(n)`) is wrongly certified
  total. A false certificate is δ-transparent, so this leaks a non-terminating
  definition into conversion. Certification must be *deferred* (return false) while
  any callee is still pending; the whole-program `TotalityClosure` sweep re-certifies
  once every body exists.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.Env

  # f(n) = g(n) ; g(n) = f(n) — a divergent mutual pair.
  defp f_body, do: {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:app, {:global, :g}, {:var, 0}}}
  defp g_body, do: {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:app, {:global, :f}, {:var, 0}}}

  defp pi, do: {:pi, Cure.Core.Grade.unrestricted(), {:type, 0}, {:type, 0}}

  test "an earlier mutual member is NOT certified while its sibling body is pending" do
    # Mid-body_pass: f's real body is registered; g is still a pending placeholder.
    env =
      Env.empty()
      |> Env.add_def(:f, pi(), f_body())
      |> Env.add_def(:g, pi(), {:hole, "__pending__"})

    refute Cure.Elab.TotalityClosure.provably_total?(env, :f),
           "f is half of a divergent cycle; with g pending the SCC is invisible — must defer"
  end

  test "once the sibling body exists, the divergent pair is correctly rejected" do
    env =
      Env.empty()
      |> Env.add_def(:f, pi(), f_body())
      |> Env.add_def(:g, pi(), g_body())

    refute Cure.Elab.TotalityClosure.provably_total?(env, :f),
           "f(n)=g(n), g(n)=f(n) is non-total — the mutual size-change check rejects it"
  end

  test "a genuine self-recursive callee that is elaborated is unaffected (control)" do
    # h(n) = case n of Z => Z | S(m) => h(m) — structurally decreasing, total.
    h_body =
      {:lam, Cure.Core.Grade.unrestricted(), {:type, 0},
       {:case, {:var, 0}, {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:type, 0}},
        [
          {:Z, 0, {:ctor, :Z, []}},
          {:S, 1, {:app, {:global, :h}, {:var, 0}}}
        ]}}

    env = Env.empty() |> Env.add_def(:h, pi(), h_body)
    assert Cure.Test.TotalityCertificateHelper.provably_total?(env, :h)
  end
end
