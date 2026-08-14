defmodule Cure.Core.SizeChangeTest do
  @moduledoc """
  Size-change termination certification (#14) in the totality certificate (TCB).

  These exercise the proof-carrying totality path directly on Core terms
  whose shapes were pinned by empirically elaborating the corresponding Cure
  sources (`ack`, `f`, `loop`, `plus`) and inspecting the resulting bodies — so
  the de Bruijn indices and the `{:ctor, :S, [var: n]}` reconstructions here are
  exactly what the elaborator emits, not hand-invented.

  Nat = Z | S(Nat). After `k` leading lambdas, param i (0-based, outermost first)
  is de Bruijn `var (k-1-i)`. A `{:case, scrut, motive, branches}` S-branch binds
  the predecessor at index 0 and shifts outer indices up by 1.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive, SizeChange}

  # -- Nat as an inductive, plus term constructors ----------------------------

  @nat {:data, :Nat, [], []}
  @nat_motive {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}

  defp z, do: {:ctor, :Z, []}
  defp s(t), do: {:ctor, :S, [t]}
  defp v(i), do: {:var, i}

  defp base_env do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Nat, [], [], 0), [
      Inductive.ctor(:Z, [], []),
      Inductive.ctor(:S, [{:data, :Nat, [], []}], [])
    ])
  end

  # case on a Nat scrutinee with a Z-branch (arity 0) and an S-branch (arity 1).
  defp ncase(scrut, s_body, z_body) do
    {:case, scrut, @nat_motive, [{:S, 1, s_body}, {:Z, 0, z_body}]}
  end

  defp call2(name, a, b), do: {:app, {:app, {:global, name}, a}, b}

  # -- Bodies (shapes confirmed by elaborating the real Cure sources) ---------

  # ack(m,n): m=var1, n=var0 initially.
  #   Z m  -> S n
  #   S p  -> ( n=var1, p=var0 )
  #             Z n -> ack(p, S Z)                 [p=var0]
  #             S q -> ack(p, ack(S p, q))         [p=var1, q=var0; S p reconstructs m]
  defp ack_body do
    inner =
      ncase(
        v(1),
        # S q branch: p shifted to var1, q=var0
        call2(:ack, v(1), call2(:ack, s(v(1)), v(0))),
        # Z n branch: p=var0
        call2(:ack, v(0), s(z()))
      )

    {:lam, Cure.Core.Grade.unrestricted(), @nat,
     {:lam, Cure.Core.Grade.unrestricted(), @nat, ncase(v(1), inner, s(v(0)))}}
  end

  defp ack_type, do: {:pi, Cure.Core.Grade.unrestricted(), @nat, {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}}

  # swap f(a,b): a=var1, b=var0.
  #   Z a -> Z
  #   S x -> ( b=var1, x=var0 )
  #            Z b -> f(x, x)              [x=var0]
  #            S y -> f(y, x)              [x=var1, y=var0]
  defp swap_body do
    inner =
      ncase(
        v(1),
        # S y: x shifted to var1, y=var0
        call2(:f, v(0), v(1)),
        # Z b: x=var0
        call2(:f, v(0), v(0))
      )

    {:lam, Cure.Core.Grade.unrestricted(), @nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, ncase(v(1), inner, z())}}
  end

  defp swap_type, do: {:pi, Cure.Core.Grade.unrestricted(), @nat, {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}}

  # lexicographic with a PASS-THROUGH first coordinate (needs only literal-equal,
  # no reconstruction): lex(a,b): a=var1, b=var0.
  #   Z a -> Z
  #   S x -> ( b=var1, x=var0 )
  #            Z b -> lex(x, x)            [first coord decreases: x < a]
  #            S y -> lex(a, y)            [a stays (SAME var), b decreases: y < b]
  # Here in the S y branch a is unmatched and passed as the same de Bruijn var.
  defp lex_body do
    inner =
      ncase(
        v(1),
        # S y: after two S-branch shifts a sits at var3 (pass-through, literal-equal)
        call2(:lex, v(3), v(0)),
        # Z b: x=var0
        call2(:lex, v(0), v(0))
      )

    {:lam, Cure.Core.Grade.unrestricted(), @nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, ncase(v(1), inner, z())}}
  end

  defp lex_type, do: {:pi, Cure.Core.Grade.unrestricted(), @nat, {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}}

  # course-of-values style: cov(a,b): a=var1, b=var0.
  #   Z a -> Z
  #   S x -> ( b=var1, x=var0 )
  #            Z b -> cov(x, S x)          [x < a; S x reconstructs nothing tracked here]
  #            S y -> cov(a, y) ... but a is rebuilt as S x to exercise reconstruct-equal:
  #            S y -> cov(S x, y)          [S x reconstructs a=S x -> Equal; y < b -> Smaller]
  defp cov_body do
    inner =
      ncase(
        v(1),
        # S y branch: x shifted to var1, y=var0. cov(S x, y): S(var1) reconstructs a.
        call2(:cov, s(v(1)), v(0)),
        # Z b branch: x=var0. cov(x, S x).
        call2(:cov, v(0), s(v(0)))
      )

    {:lam, Cure.Core.Grade.unrestricted(), @nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, ncase(v(1), inner, z())}}
  end

  defp cov_type, do: {:pi, Cure.Core.Grade.unrestricted(), @nat, {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}}

  # loop(a,b) = loop(S a, S b): a=var1, b=var0. NO case — a and b are unmatched.
  # The rebuilt S a / S b do NOT reconstruct any matched form (a,b unmatched),
  # so reconstruct-equal must NOT fire; all arcs unknown -> rejected.
  defp loop_body do
    {:lam, Cure.Core.Grade.unrestricted(), @nat,
     {:lam, Cure.Core.Grade.unrestricted(), @nat, call2(:loop, s(v(1)), s(v(0)))}}
  end

  defp loop_type, do: {:pi, Cure.Core.Grade.unrestricted(), @nat, {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}}

  # plus(a,b): single fixed decreasing position (regression / no-regression).
  #   Z a -> b
  #   S x -> S(plus(x, b))    [x=var0 < a, b shifted to var1]
  defp plus_body do
    {:lam, Cure.Core.Grade.unrestricted(), @nat,
     {:lam, Cure.Core.Grade.unrestricted(), @nat,
      ncase(
        v(1),
        # S x: x=var0, b=var1
        s(call2(:plus, v(0), v(1))),
        # Z a: b=var0
        v(0)
      )}}
  end

  defp plus_type, do: {:pi, Cure.Core.Grade.unrestricted(), @nat, {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}}

  alias Cure.Test.TotalityCertificateHelper

  defp terminating?(env, name) do
    TotalityCertificateHelper.provably_total?(env, name)
  end

  # -- Must flip to TOTAL (currently rejected by the single-position check) ----

  test "Ackermann certifies total (needs reconstruct-equal on the rebuilt S m)" do
    env = Env.add_def(base_env(), :ack, ack_type(), ack_body())
    assert terminating?(env, :ack)
  end

  test "swap f(S x,S y)=f(y,x) certifies total (permuting descent)" do
    env = Env.add_def(base_env(), :f, swap_type(), swap_body())
    assert terminating?(env, :f)
  end

  test "lexicographic with pass-through first coordinate certifies total" do
    env = Env.add_def(base_env(), :lex, lex_type(), lex_body())
    assert terminating?(env, :lex)
  end

  test "course-of-values with rebuilt-equal first coordinate certifies total" do
    env = Env.add_def(base_env(), :cov, cov_type(), cov_body())
    assert terminating?(env, :cov)
  end

  # -- Must stay REJECTED (non-total control) ---------------------------------

  test "loop(a,b)=loop(S a,S b) is rejected: reconstruct-equal does NOT fire on unmatched params" do
    # a and b are never matched, so S(a)/S(b) reconstruct no tracked form; every
    # arc is :unknown, the sole idempotent loop has no :smaller diagonal.
    env = Env.add_def(base_env(), :loop, loop_type(), loop_body())
    refute terminating?(env, :loop)
  end

  # -- No regression: single fixed decreasing position still certifies --------

  test "plus (single fixed decreasing position) still certifies total" do
    env = Env.add_def(base_env(), :plus, plus_type(), plus_body())
    assert terminating?(env, :plus)
  end

  test "sparse matrix validation rejects invalid relations and coordinates" do
    assert SizeChange.valid?(%SizeChange.Matrix{rows: 1, columns: 1, entries: %{{0, 0} => :smaller}})

    refute SizeChange.valid?(%SizeChange.Matrix{
             rows: 1,
             columns: 1,
             entries: %{{1, 0} => :smaller}
           })

    refute SizeChange.valid?(%SizeChange.Matrix{
             rows: 1,
             columns: 1,
             entries: %{{0, 0} => :strictly_better}
           })
  end
end
