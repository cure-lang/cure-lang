defmodule Antigen.GuardedLambdaSizeChangeAntibodyTest do
  @moduledoc """
  TCB antibody (K-bug 2, spec `2026-07-18-elaborator-gaps-verified-status.md` §2) —
  the size-change termination certificate must certify continuation-style
  ("guarded-lambda") recursion whose recursive self-call sits inside an UNAPPLIED
  lambda, when that recursion is genuinely total.

  ## The bug this pins (RED at authoring)

  For a free-monad-style `bind`:

      data F(a) = Pure(a) | Bind(Dec, Dec -> F(a))

      bind(m, f) =
        case m of
          Pure(x)   -> f(x)
          Bind(e,g) -> Bind(e, fn(y) -> bind(g(y), f))     -- self-call under fn(y)

  proof-carrying totality pipeline leaves `bind` uncertified. The
  `{:lam,...}` walk (`certificate.ex` ~197) correctly descends under the unapplied
  lambda, but the self-call's argument `g(y)` is an `{:app,...}` (a smaller field
  applied to the bound `y`), and `arg_relation/2` (~320–334) has cases only for a
  bare `{:var,i}` or a reconstruction-equal `{:ctor,...}` — every `{:app,...}`
  falls to the `:unknown` catch-all. No `:smaller` diagonal survives, so `bind`
  fails certification. Because δ-unfolding in conversion is gated on
  `Env.certified?` (`conv.ex:10–15`), an uncertified `bind` is opaque and never
  δ-unfolds, so every `bind(...)` in a type/index position is stuck
  (`:conversion_failure`).

  This is a COMPLETENESS gap: the recursion is total (the recursive occurrence is
  inert behind an unforced binder — Nakano-style guarded / coinductive Freer-monad
  `bind`; when conversion later opens the continuation on a fresh free `y`, the
  inner `case` gets stuck on the neutral scrutinee `g(y)` and its branches are
  never forced, so the symbolic unfolding halts at depth 1). The trusted kernel
  never accepts anything ill-typed; rejecting a total function is conservative, not
  unsound. So this is a MUST-CERTIFY reach pin.

  ## Obligations

    * REACH (total guarded-lambda must certify) — the `bind` above certifies.
      RED until the size-change criterion recognizes a guarded/deferred self-call
      under an unapplied lambda.

    * CONTROL (diverging guarded-lambda stays rejected) — a same-shaped `bind`
      whose self-call REGROWS the identical matched node
      (`Bind(e,g) -> Bind(e, fn(y) -> bind(Bind(e,g), f))`) genuinely loops once
      the continuation is forced, and MUST stay rejected. This guards the
      soundness boundary: today `arg_relation` returns `:unknown` for ANY
      `{:app,...}` regardless of head, so a naive "application of a smaller var ⇒
      smaller" fix would be UNSOUND — it would certify this diverging control too.
      The fix must lean on the guarded/coinductive argument (recursion behind an
      unforced binder), not a blanket app-is-smaller rule. If CONTROL ever goes
      green while it still diverges, the fix infected soundness: STOP.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Builtins, Env, Grade}

  # data F(a) = Pure(a) | Bind(Dec, Dec -> F(a))
  #   bind : Dec -> Dec -> Dec   (indices erased for the size-change frame)
  #   Outer lambda binds m (param 0), inner lambda binds f (param 1).
  #   Pre-branch, under both lambdas: var 0 = f, var 1 = m.
  defp g, do: Grade.unrestricted()
  defp dec, do: {:data, :Dec, [], []}
  defp motive, do: {:lam, g(), dec(), dec()}
  # Pure(x) -> f(x);  x at var0, f shifts 0->1
  defp pure_branch, do: {:app, {:var, 1}, {:var, 0}}
  defp ty, do: {:pi, g(), dec(), {:pi, g(), dec(), dec()}}

  defp env_for(body), do: Env.add_def(Builtins.seed_ops(Env.empty()), :bind, ty(), body)

  # --- TOTAL: Bind(e,g) -> Bind(e, fn(y) -> bind(g(y), f)) -------------------
  # inside Bind branch (ar=2): var0=g, var1=e, var2=f, var3=m
  # + y lambda shifts +1:      var0=y, var1=g, var2=e, var3=f, var4=m
  defp total_body do
    inner_lam =
      {:lam, g(), dec(), {:app, {:app, {:global, :bind}, {:app, {:var, 1}, {:var, 0}}}, {:var, 3}}}

    bind_branch = {:ctor, :Bind, [{:var, 1}, inner_lam]}

    {:lam, g(), dec(),
     {:lam, g(), dec(), {:case, {:var, 1}, motive(), [{:Pure, 1, pure_branch()}, {:Bind, 2, bind_branch}]}}}
  end

  # --- CONTROL: Bind(e,g) -> Bind(e, fn(y) -> bind(Bind(e,g), f)) ------------
  # Regrows the untouched matched node instead of descending into `g`: the
  # returned continuation calls bind on the identical Bind(e,g) forever.
  defp diverging_body do
    div_inner_lam =
      {:lam, g(), dec(), {:app, {:app, {:global, :bind}, {:ctor, :Bind, [{:var, 2}, {:var, 1}]}}, {:var, 3}}}

    div_bind_branch = {:ctor, :Bind, [{:var, 1}, div_inner_lam]}

    {:lam, g(), dec(),
     {:lam, g(), dec(), {:case, {:var, 1}, motive(), [{:Pure, 1, pure_branch()}, {:Bind, 2, div_bind_branch}]}}}
  end

  test "REACH: total guarded-lambda bind certifies" do
    body = total_body()

    assert Cure.Elab.TotalityClosure.provably_total?(env_for(body), :bind),
           "total continuation-style bind must certify under guarded size-change"
  end

  test "CONTROL: regrowing (diverging) guarded-lambda bind stays rejected" do
    body = diverging_body()

    refute Cure.Elab.TotalityClosure.provably_total?(env_for(body), :bind),
           "the regrowing guarded-lambda bind genuinely diverges and must NOT be certified"
  end
end
