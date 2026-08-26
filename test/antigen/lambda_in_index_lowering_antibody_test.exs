defmodule Antigen.LambdaInIndexLoweringAntibodyTest do
  @moduledoc """
  E-layer antibody (E10a, spec `2026-07-18-elaborator-gaps-verified-status.md` §3) —
  a `fn(y) -> …` LAMBDA appearing in a dependent INDEX position (nested inside a
  term-level function application that is itself an index argument) must lower and
  type-check, WITHOUT the widening ever admitting an ill-typed or false-equation
  program.

  ## The gap this closes (RED before the fix)

  The return type `Equivalent(Eff, bind(m, fn(y) -> Pure(y)), …)` carries a lambda
  in index position. Two E/P-layer defects blocked it:

    * the type parser (`parser.ex:parse_type_arrow`) misparsed `fn(y) -> …` as a
      parenthesized arrow TYPE (`Function(y, …)`), so the binder dangled as a
      `{:global, :y}` and normalisation crashed / `:unknown_global`d; and
    * even once parsed, `idx_to_core` had no `{:lambda, …}` clause — a bare binder
      has no domain until CHECKED against the callee's Π-domain, which the
      syntax-directed lowering cannot supply (`:unsupported_index_expr`).

  The fix parses the lambda as a `{:lambda, …}` in type position and routes an
  application carrying one through the bidirectional term elaborator
  (`elaborate_implicit_app_bidirectional`), which checks the lambda at the
  callee's Π-domain. This is an E-layer widening; the kernel re-checks the
  assembled Core term, so the antibody's job is to prove the widening is
  CONSERVATIVE — it lets the previously-rejected well-typed program through and
  nothing else.

  ## Obligations

    * REACH — the identical-lambda program (`bind(m, λy.Pure y)` on BOTH sides of
      `Equivalent`, closed by `reflexive`) elaborates. RED before the fix.

    * CONTROL A (false equation stays rejected) — DISTINCT lambdas on the two
      sides (`λy.Pure y` vs `λy.Pure D0`) make the equation false; `reflexive` on
      the first side must NOT prove it. Guards against a lowering that collapses
      distinct lambdas or fabricates a unifier — the soundness tripwire.

    * CONTROL B (ill-typed lambda body stays rejected) — a lambda whose body calls
      an unknown global (`λy.nope y`) in index position must be rejected, proving
      the delegation genuinely type-checks the lambda body rather than lowering it
      blindly.

  A fix that greens REACH without regressing either CONTROL is sound: the
  widening admits the well-typed program and continues to reject the false
  equation and the ill-typed body.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  # Shared preamble: the free-monad `Eff` with a higher-order `Bind`, the total
  # `bind`, and `Std.Equivalent` in scope. Only the final `Equivalent(…)`-typed
  # def differs across the three obligations.
  defp src(final_def) do
    """
    mod LamIdx
      use Std.Equivalent
      type Dec = D0 | D1
      type Eff = Pure(Dec) | Bind(Dec, (Dec) -> Eff)
      fn bind(m: Eff, f: (Dec) -> Eff) -> Eff = match m
        Pure(x) -> f(x)
        Bind(e, g) -> Bind(e, fn(y) -> bind(g(y), f))
      #{final_def}
    end
    """
  end

  # ---- Obligation 1: REACH (identical-lambda program elaborates) -------------

  test "REACH: a lambda in index position lowers and the reflexive proof closes" do
    reach =
      "fn refl_bind(m: Eff) -> " <>
        "Equivalent(Eff, bind(m, fn(y) -> Pure(y)), bind(m, fn(y) -> Pure(y))) = " <>
        "reflexive(bind(m, fn(y) -> Pure(y)))"

    assert {:ok, _} = Program.elaborate(src(reach))
  end

  # ---- Obligation 2: CONTROL A (false equation stays rejected) ---------------

  test "CONTROL A: distinct lambdas make a false equation that reflexive cannot prove" do
    bad =
      "fn bad(m: Eff) -> " <>
        "Equivalent(Eff, bind(m, fn(y) -> Pure(y)), bind(m, fn(y) -> Pure(D0))) = " <>
        "reflexive(bind(m, fn(y) -> Pure(y)))"

    assert {:error, _} = Program.elaborate(src(bad))
  end

  # ---- Obligation 3: CONTROL B (ill-typed lambda body stays rejected) --------

  test "CONTROL B: an ill-typed lambda body in index position is rejected" do
    bad =
      "fn bad2(m: Eff) -> " <>
        "Equivalent(Eff, bind(m, fn(y) -> nope(y)), m) = reflexive(m)"

    assert {:error, _} = Program.elaborate(src(bad))
  end
end
