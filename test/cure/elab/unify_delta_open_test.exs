defmodule Cure.Elab.UnifyDeltaOpenTest do
  @moduledoc """
  The elaborator unifier's last-resort δ/ι-convertibility fallback must fire for OPEN (free de
  Bruijn var) but metavariable-FREE terms, not just closed ones — evaluated under a neutral env of
  the current binder depth (exactly how the kernel checks under binders). Before the fix, a `data`
  index like `elt(EFin x, EFin k)` vs its ι-reduct `slt(x, k)`, or a `mem(x, Node(l,v,r))` vs
  `mem(x, l)` redex reached during index/argument unification, failed `:cannot_unify` because the
  `closed?` guard rejected the free vars — forcing explicit reduction-bridge lemmas in every
  dependent proof. This exercises the fix (a real search-tree proof that needs no bridges) and its
  soundness antibody (a genuinely non-convertible open pair still fails).
  """
  use ExUnit.Case, async: false

  alias Cure.Elab.Program

  test "open meta-free convertible terms unify (no reduction-bridge lemmas needed)" do
    # A search-tree `mem = lmem` proof written WITHOUT the ml_*/ll_* reduction bridges: the
    # trans-chain endpoints `mem(x, Node(l,v,r))` / `lmem(x, Node(l,v,r))` must δ/ι-reduce during
    # unification to match `mem(x, l)` / `orb(...)`. Red before the fix (`:index_mismatch` /
    # `:cannot_unify`), green after.
    src = """
    mod DeltaUnifyRegression
      use Std.Equivalent
      type OKey = OA | OB | OC
      type OBit = OF | OT
      fn orb(a: OBit, b: OBit) -> OBit = match a
        OF() -> b
        OT() -> OT()
      fn andb(a: OBit, b: OBit) -> OBit = match a
        OF() -> OF()
        OT() -> b
      fn cmp(x: OKey, y: OKey) -> OBit = match x
        OA() -> match y
          OA() -> OF()
          OB() -> OT()
          OC() -> OT()
        OB() -> match y
          OA() -> OF()
          OB() -> OF()
          OC() -> OT()
        OC() -> match y
          OA() -> OF()
          OB() -> OF()
          OC() -> OF()
      fn keq(x: OKey, y: OKey) -> OBit = match x
        OA() -> match y
          OA() -> OT()
          OB() -> OF()
          OC() -> OF()
        OB() -> match y
          OA() -> OF()
          OB() -> OT()
          OC() -> OF()
        OC() -> match y
          OA() -> OF()
          OB() -> OF()
          OC() -> OT()
      fn orb_of_r(a: OBit) -> Equivalent(OBit, orb(a, OF()), a) = match a
        OF() -> reflexive(OF())
        OT() -> reflexive(OT())
      fn orb_cong_l(c: OBit, {a: OBit}, {a2: OBit}, e: Equivalent(OBit, a, a2)) -> Equivalent(OBit, orb(a, c), orb(a2, c)) =
        rewrite e in reflexive(orb(a2, c))
      fn orb_cong_r(a: OBit, {b: OBit}, {b2: OBit}, e: Equivalent(OBit, b, b2)) -> Equivalent(OBit, orb(a, b), orb(a, b2)) =
        rewrite e in reflexive(orb(a, b2))
      fn andb_l(a: OBit, c: OBit, e: Equivalent(OBit, andb(a, c), OT())) -> Equivalent(OBit, a, OT()) = match a
        OT() -> reflexive(OT())
        OF() -> match e
      fn andb_r(a: OBit, c: OBit, e: Equivalent(OBit, andb(a, c), OT())) -> Equivalent(OBit, c, OT()) = match a
        OT() -> e
        OF() -> match e
      fn strict_trans(x: OKey, y: OKey, z: OKey, p: Equivalent(OBit, cmp(x, y), OT()), q: Equivalent(OBit, cmp(y, z), OT())) -> Equivalent(OBit, cmp(x, z), OT()) = match x
        OA() -> match z
          OA() -> match y
            OA() -> match p
            OB() -> match q
            OC() -> match q
          OB() -> reflexive(OT())
          OC() -> reflexive(OT())
        OB() -> match z
          OA() -> match y
            OA() -> match p
            OB() -> match p
            OC() -> match q
          OB() -> match y
            OA() -> match p
            OB() -> match p
            OC() -> match q
          OC() -> reflexive(OT())
        OC() -> match y
          OA() -> match p
          OB() -> match p
          OC() -> match p
      fn strict_neq(x: OKey, y: OKey, p: Equivalent(OBit, cmp(x, y), OT())) -> Equivalent(OBit, keq(x, y), OF()) = match x
        OA() -> match y
          OA() -> match p
          OB() -> reflexive(OF())
          OC() -> reflexive(OF())
        OB() -> match y
          OA() -> match p
          OB() -> match p
          OC() -> reflexive(OF())
        OC() -> match y
          OA() -> match p
          OB() -> match p
          OC() -> match p
      fn strict_neq_r(x: OKey, y: OKey, p: Equivalent(OBit, cmp(y, x), OT())) -> Equivalent(OBit, keq(x, y), OF()) = match x
        OA() -> match y
          OA() -> match p
          OB() -> match p
          OC() -> match p
        OB() -> match y
          OA() -> reflexive(OF())
          OB() -> match p
          OC() -> match p
        OC() -> match y
          OA() -> reflexive(OF())
          OB() -> reflexive(OF())
          OC() -> match p
      type Tree = Leaf | Node(Tree, OKey, Tree)
      fn mem(x: OKey, t: Tree) -> OBit = match t
        Leaf()        -> OF()
        Node(l, v, r) -> match cmp(x, v)
          OT() -> mem(x, l)
          OF() -> match keq(x, v)
            OT() -> OT()
            OF() -> mem(x, r)
      fn lmem(x: OKey, t: Tree) -> OBit = match t
        Leaf()        -> OF()
        Node(l, v, r) -> orb(keq(x, v), orb(lmem(x, l), lmem(x, r)))
      fn alllt(t: Tree, b: OKey) -> OBit = match t
        Leaf()        -> OT()
        Node(l, v, r) -> andb(cmp(v, b), andb(alllt(l, b), alllt(r, b)))
      fn allgt(t: Tree, b: OKey) -> OBit = match t
        Leaf()        -> OT()
        Node(l, v, r) -> andb(cmp(b, v), andb(allgt(l, b), allgt(r, b)))
      fn isbst(t: Tree) -> OBit = match t
        Leaf()        -> OT()
        Node(l, v, r) -> andb(isbst(l), andb(isbst(r), andb(alllt(l, v), allgt(r, v))))
      fn below_not_lmem(x: OKey, b: OKey, t: Tree, pxb: Equivalent(OBit, cmp(x, b), OT()), pgt: Equivalent(OBit, allgt(t, b), OT())) -> Equivalent(OBit, lmem(x, t), OF()) = match t
        Leaf()        -> reflexive(OF())
        Node(l, v, r) -> rewrite strict_neq(x, v, strict_trans(x, b, v, pxb, andb_l(cmp(b, v), andb(allgt(l, b), allgt(r, b)), pgt))) in rewrite below_not_lmem(x, b, l, pxb, andb_l(allgt(l, b), allgt(r, b), andb_r(cmp(b, v), andb(allgt(l, b), allgt(r, b)), pgt))) in rewrite below_not_lmem(x, b, r, pxb, andb_r(allgt(l, b), allgt(r, b), andb_r(cmp(b, v), andb(allgt(l, b), allgt(r, b)), pgt))) in reflexive(OF())
      fn above_not_lmem(x: OKey, b: OKey, t: Tree, pbx: Equivalent(OBit, cmp(b, x), OT()), plt: Equivalent(OBit, alllt(t, b), OT())) -> Equivalent(OBit, lmem(x, t), OF()) = match t
        Leaf()        -> reflexive(OF())
        Node(l, v, r) -> rewrite strict_neq_r(x, v, strict_trans(v, b, x, andb_l(cmp(v, b), andb(alllt(l, b), alllt(r, b)), plt), pbx)) in rewrite above_not_lmem(x, b, l, pbx, andb_l(alllt(l, b), alllt(r, b), andb_r(cmp(v, b), andb(alllt(l, b), alllt(r, b)), plt))) in rewrite above_not_lmem(x, b, r, pbx, andb_r(alllt(l, b), alllt(r, b), andb_r(cmp(v, b), andb(alllt(l, b), alllt(r, b)), plt))) in reflexive(OF())
      fn eq_below(l: Tree, r: Tree, pgt: Equivalent(OBit, allgt(r, OB()), OT()), ih: Equivalent(OBit, mem(OA(), l), lmem(OA(), l))) -> Equivalent(OBit, mem(OA(), Node(l, OB(), r)), lmem(OA(), Node(l, OB(), r))) =
        trans(ih, sym(trans(orb_cong_r(lmem(OA(), l), below_not_lmem(OA(), OB(), r, reflexive(OT()), pgt)), orb_of_r(lmem(OA(), l)))))
      fn eq_above(l: Tree, r: Tree, plt: Equivalent(OBit, alllt(l, OA()), OT()), ih: Equivalent(OBit, mem(OB(), r), lmem(OB(), r))) -> Equivalent(OBit, mem(OB(), Node(l, OA(), r)), lmem(OB(), Node(l, OA(), r))) =
        trans(ih, sym(orb_cong_l(lmem(OB(), r), above_not_lmem(OB(), OA(), l, reflexive(OT()), plt))))
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "antibody: a non-convertible open pair still fails to unify" do
    # `unwrap(Wrap(Wrap(x)))` reduces to `Wrap(x)`, NOT `x`; the fix must NOT equate these distinct
    # normal forms. Forcing the comparison through data-index unification keeps it rejected.
    src = """
    mod DeltaOpenAntibody
      type T = Leaf | Wrap(T)
      fn unwrap(x: T) -> T = match x
        Leaf() -> Leaf()
        Wrap(y) -> y
      type Box indices (t: T)
        MkBox : Box(t)
      fn mk(x: T) -> Box(unwrap(Wrap(Wrap(x)))) = MkBox()
      fn use_box(x: T, b: Box(x)) -> T = x
      fn bad(x: T) -> T = use_box(x, mk(x))
    end
    """

    assert {:error, _} = Program.elaborate(src)
  end
end
