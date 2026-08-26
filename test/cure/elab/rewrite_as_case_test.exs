defmodule Cure.Elab.RewriteAsCaseTest do
  @moduledoc """
  Phase B (identity-type-as-inductive, spec 2026-07-04): `rewrite p in body`
  must desugar to a single-branch inductive `:case` on `p | reflexive(w) -> …`,
  emitting NO primitive `{:rewrite, …}` Core node.

  Two fixtures pin the two shapes the revert of `d44edb8` (`c635e8c`) identified
  as distinct:

    (a) VARIABLE endpoints  — the proof's endpoints are (or reduce through) plain
        variables the branch unifier can substitute (`rw01` shape).
    (b) COMPUTED endpoints  — the proof's endpoints are applications, not
        variables (`frp01_par_assoc` shape). This is the case the naive
        body-shift `rw_case_build` drifted (accept→reject); it MUST still accept
        and carry no `{:rewrite}` node.

  Both are RED today: the current elaborator emits `{:rewrite, …}` for every
  producer site.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program
  alias Cure.Core.{Env, Validator}

  defp rewrite_nodes(env, fn_name) do
    env
    |> Env.get_def(fn_name)
    |> Map.fetch!(:body)
    |> Validator.nodes()
    |> Enum.filter(&match?({:rewrite, _, _, _}, &1))
  end

  # (a) variable-endpoint rewrite: rw01's `plus_zero_right`.
  @variable_src """
  mod RwCaseVar
    type Nat = Z | S(Nat)
    fn plus(m: Nat, n: Nat) -> Nat = match m
      Z() -> n
      S(k) -> S(plus(k, n))
    fn plus_zero_right(n: Nat) -> Equivalent(Nat, plus(n, Z), n) = match n
      Z() -> reflexive(Z)
      S(k) -> rewrite plus_zero_right(k) in reflexive(S(k))
  end
  """

  test "(a) a variable-endpoint rewrite accepts and emits no {:rewrite} node" do
    assert {:ok, env} = Program.elaborate(@variable_src)

    assert rewrite_nodes(env, :plus_zero_right) == [],
           "plus_zero_right body must contain no {:rewrite, …} node after Phase B"
  end

  # (b) computed-endpoint rewrite: a miniature `frp01_par_assoc`. `appAssoc`'s
  # SCons branch rewrites along a proof whose endpoints are `app(…)` applications,
  # not variables — the sentinel that killed the naive attempt.
  @computed_src """
  mod RwCaseComputed
    type Sig = SigC | SigE
    type SList = SNil | SCons(Sig, SList)
    fn app(xs: SList, ys: SList) -> SList = match xs
      SNil() -> ys
      SCons(x, r) -> SCons(x, app(r, ys))
    fn appAssoc(xs: SList, ys: SList, zs: SList) -> Equivalent(SList, app(xs, app(ys, zs)), app(app(xs, ys), zs)) = match xs
      SNil() -> reflexive(app(ys, zs))
      SCons(x, r) -> rewrite appAssoc(r, ys, zs) in reflexive(SCons(x, app(app(r, ys), zs)))
  end
  """

  test "(b) a computed-endpoint rewrite accepts and emits no {:rewrite} node" do
    assert {:ok, env} = Program.elaborate(@computed_src)

    assert rewrite_nodes(env, :appAssoc) == [],
           "appAssoc body (computed endpoints) must contain no {:rewrite, …} node after Phase B"
  end

  # (c) with-transport, capability B (`elaborate_with_eq_branch`): mirrors
  # `wi05_sibling_refine` — the sibling `pf : SNat(g(n))` is transported along
  # the branch's scrutinee equation. Producer site B2 (was :1912).
  @with_src """
  mod RwCaseWith
    type Nat = Z | S(Nat)
    type SNat indices (m: Nat)
      szero : SNat(Z)
      ssuc : SNat(m) -> SNat(S(m))
    fn g(x: Nat) -> Nat = match x
      Z() -> Z()
      S(k) -> S(k)
    fn consume(m: Nat, s: SNat(m)) -> Nat = m
    fn foo(n: Nat, pf: SNat(g(n))) -> Nat =
      with g(n)
        Z() -> consume(Z(), pf)
        S(k) -> consume(S(k), pf)
  end
  """

  test "(c) with-clause sibling transport accepts and emits no {:rewrite} node" do
    assert {:ok, env} = Program.elaborate(@with_src)

    assert rewrite_nodes(env, :foo) == [],
           "with-transport (wi05 shape) must contain no {:rewrite, …} node after Phase B"
  end

  # (d) carried-index-eq transport (`elaborate_carried_eq_branch`): a sibling
  # `w : F(app(p,q))` returned under branches whose goal 3a-refines to the
  # constructor's index — transported along the carried `Eq(SList, app(p,q), …)`.
  # Producer site B2 (was :3477).
  @carried_src """
  mod RwCaseCarried
    type Nat = Z | S(Nat)
    type SList = SNil | SCons(Nat, SList)
    fn app(xs: SList, ys: SList) -> SList = match xs
      SNil() -> ys
      SCons(h, t) -> SCons(h, app(t, ys))
    type F indices (xs: SList)
      leaf : F(SNil())
      mk : F(as) -> F(bs) -> F(app(as, bs))
    fn keep({p: SList}, {q: SList}, v: F(app(p, q)), w: F(app(p, q))) -> F(app(p, q)) =
      match v
        leaf() -> w
        mk(l, r) -> w
  end
  """

  test "(d) carried-index sibling transport accepts and emits no {:rewrite} node" do
    assert {:ok, env} = Program.elaborate(@carried_src)

    assert rewrite_nodes(env, :keep) == [],
           "carried-eq transport must contain no {:rewrite, …} node after Phase B"
  end

  # (e) bridge_step deletion pin (Task B2 Step 1 finding). `bridge_step` — the
  # definitional-occurrence bridge built for rw07 (commit 2ac4add) — was
  # DELETED rather than migrated, on dual evidence of unreachability:
  #
  #   1. EMPIRICAL (CURE_REWRITE_LOG=1 trace, 2026-07-08, this branch): across
  #      the full rewrite/refl/frp oracle corpus no fixture ever logs a
  #      "bridge candidate" or "bridge_step" line; only rw03_no_occurrence even
  #      reaches `find_bridge` ("find_bridge: 0 reducible subterms") before
  #      correctly rejecting. rw07/rw09 — the fixtures the bridge existed for —
  #      route through the plain `contains_a` path.
  #
  #   2. STRUCTURAL: `find_bridge` fired only if some global-app subterm `s` of
  #      the ALREADY-NORMALIZED goal satisfied `normalize(s) != s`. Since
  #      ef3e958 (lazy δ-unfolding — a recursive global stuck on a neutral
  #      stays folded, eliminating the δ-inconsistent normal forms that froze
  #      rw07's `plus(Z,n)` subterm) and the nf idempotence fix (pinned by
  #      normalise_test "nf is idempotent…"), `Kernel.normalize` = reify∘eval
  #      is compositional and idempotent: every subterm of a normal form — in
  #      particular every folded stuck global spine, whose args are reified
  #      values — re-normalizes to itself in the same ctx. The bridge's firing
  #      condition was unsatisfiable, and `rewrite_plan`'s only entry point
  #      normalizes `expected` first (`elaborate_expr_checked`'s rewrite_expr
  #      clause), so the cond arm was dead code.
  #
  # This test pins the shape that ORIGINALLY needed the bridge (rw07: the proof
  # endpoint `plus(n,Z)` is present only after the goal's inner `plus(Z,n)`
  # reduces): it must keep accepting through `contains_a`, with no bridge
  # machinery and no {:rewrite} node.
  @rw07_src """
  mod RwCaseConv
    type Nat = Z | S(Nat)
    fn plus(m: Nat, n: Nat) -> Nat = match m
      Z() -> n
      S(k) -> S(plus(k, n))
    fn plus_zero_right(n: Nat) -> Equivalent(Nat, plus(n, Z), n) = match n
      Z() -> reflexive(Z)
      S(k) -> rewrite plus_zero_right(k) in reflexive(S(k))
    fn conv_occurrence(n: Nat) -> Equivalent(Nat, plus(plus(Z, n), Z), n) = rewrite plus_zero_right(n) in reflexive(n)
  end
  """

  test "(e) rw07's definitional-occurrence shape accepts without bridge_step, no {:rewrite} node" do
    assert {:ok, env} = Program.elaborate(@rw07_src)

    assert rewrite_nodes(env, :conv_occurrence) == [],
           "conv_occurrence must accept via contains_a with no {:rewrite, …} node"
  end
end
