defmodule Cure.Elab.CarriedIndexEqTest do
  @moduledoc """
  Phase 2 — carried equalities. When a dependent `match` on an indexed scrutinee
  produces a branch whose constructor result index is a STUCK computed term
  (`app(as, bs)` — append is not injective, so first-order unification against the
  scrutinee's index `app(p, q)` gets stuck), the branch goal is not refined by
  `build_motive` (which only generalizes index *variables*, not computed index
  terms). A branch body that reconstructs a value typed at the constructor's index
  (`mk(l, r) : F(app(as, bs))`) against a goal at the scrutinee's index
  (`F(app(p, q))`) therefore needs the stuck equation `app(p, q) = app(as, bs)`
  to be CARRIED. This mirrors the paper's `par : SF(av,bv,d1) -> SF(cv,dv,d2) ->
  SF(app(av,cv), ...)`.

  Lean (verified from `~/Develop/lean4` source, subagent a34a4b73) requires OPT-IN
  `match h:` syntax for stuck equations (`MatcherInfo.DiscrInfo.hName?`,
  `UnifyEq.lean:121-124` throws when unnamed); Cure's Phase 2 is a deliberate
  AUTOMATION of that opt-in. Soundness rests on the same kernel-checked Eq-arrow
  vehicle as capability B: `motive = λ(w:Idx). Eq(Idx, e, w) -> G[e↦w]`, discharged
  by `refl` at the match site, generalized here from the scrutinee VALUE to its
  computed INDEX. The Eq endpoints are the NON-indexed carrier (`SList`), so this
  avoids the `Quote.reify` indexed-family collapse (Phase 5).
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  # SList carrier + append (certified so its redexes reduce), and an F family
  # whose `mk` constructor has a computed append result index.
  @preamble """
    type SList = SNil | SCons(Nat, SList)
    fn app(xs: SList, ys: SList) -> SList = match xs
      SNil() -> ys
      SCons(h, t) -> SCons(h, app(t, ys))
    type F indices (xs: SList)
      leaf : F(SNil())
      mk : F(as) -> F(bs) -> F(app(as, bs))
  """

  defp mod(body), do: "mod P\n  type Nat = Z | S(Nat)\n" <> @preamble <> body <> "end\n"

  test "reconstructing mk(l,r):F(app(as,bs)) at goal F(app(p,q)) needs the carried index eq" do
    # In the `mk` branch, `mk(l, r) : F(app(as, bs))` while the goal is
    # `F(app(p, q))`. These indices are distinct stuck neutrals; the branch
    # type-checks ONLY if `app(p,q) = app(as,bs)` is carried. RED today.
    src =
      mod("""
        fn rebuild({p: SList}, {q: SList}, v: F(app(p, q))) -> F(app(p, q)) =
          match v
            leaf() -> leaf()
            mk(l, r) -> mk(l, r)
      """)

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "carried index eq does not admit an ill-typed reconstruction (soundness control)" do
    # The `leaf` arm is well-typed (`leaf() : F(SNil)` at goal `F(SNil)`), so the
    # ONLY reason to reject is the `mk` arm: swapping the sub-values
    # (`mk(r, l) : F(app(bs, as))`) against the refined goal `F(app(as, bs))`
    # requires `app(as, bs) = app(bs, as)`, which does NOT hold (append is not
    # commutative). Isolating the swap this way makes the control a true guard
    # that the refined motive does not over-accept.
    src =
      mod("""
        fn rebuild({p: SList}, {q: SList}, v: F(app(p, q))) -> F(app(p, q)) =
          match v
            leaf() -> leaf()
            mk(l, r) -> mk(r, l)
      """)

    assert {:error, _} = Program.elaborate(src)
  end
end
