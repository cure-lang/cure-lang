defmodule Antigen.SiblingContextRefinementAntibodyTest do
  @moduledoc """
  E-layer antibody (E1 + E1-sub, spec `2026-07-18-elaborator-gaps-verified-status.md`)
  — a dependent match on EVIDENCE must refine the whole local CONTEXT, not only the
  motive (McBride "refine the whole context"). The refinement is delivered by
  `specialize_branch_context_subst`, which rewrites BOTH `ctx.types` and `ctx.env`
  by the branch-unify substitution, so a refined sibling binder is seen by

    * the coverage/impossibility checker  — E1 (the headline), and
    * the WRITTEN body terms the programmer spelled — E1-sub.

  Both reach cases already elaborate in this tree (they were closed by the
  `specialize_branch_context_subst` + `refine_scrutinee_in_body` work); the oracle
  probes `e1sib`/`e1sub` pin the ACCEPT direction against Idris. This antibody pins
  the other half — that the refinement is SOUND, not a blanket accept: the same
  shapes with a WRONG sibling constructor / WRONG target index are still rejected.

  ## Obligations

    * E1 REACH — after matching the `SendSendK` evidence, the sibling behaviour `b`
      is refined to `BSend(y, k)`, so a nested `match b` covering ONLY the `BSend`
      arm is exhaustive (the `BNil`/`BRecv` shapes are impossible under refinement).

    * E1 CONTROL — the SAME program but the nested `match b` supplies the WRONG arm
      (`BRecv`). Under the refinement `b = BSend(y, k)` that arm is impossible, so
      the kernel must reject (the refinement is genuine, not a fabricated unifier).

    * E1-sub REACH — after matching the `RIsA` evidence, the sibling role `r` is
      refined to `RA`, so the written body term `project(k, r)` becomes convertible
      with the goal RHS `project(k, RA)` and `reflexive(project(k, r))` closes.

    * E1-sub CONTROL — the SAME program but the goal RHS is `project(k, RB)`. The
      refinement `r := RA` reaches the written `r` and makes the two sides `RA` vs
      `RB` — distinct — so the kernel must reject.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  # ---- E1: sibling context refinement reaches the coverage checker ------------

  # `coverage`'s `SendSendK` arm refines `b` to `BSend(y, k)`; the nested `match b`
  # supplies `arm`. REACH gives the possible arm, CONTROL the impossible one.
  defp e1_src(arm) do
    """
    mod E1Ab
      type Tag = TA | TB
      type Behaviour = BNil | BRecv(Tag, Behaviour) | BSend(Tag, Behaviour)
      type TagList = TNil | TCons(Tag, TagList)
      fn infer(b: Behaviour) -> TagList = match b
        BNil()      -> TNil
        BRecv(t, k) -> infer(k)
        BSend(t, k) -> TCons(t, infer(k))
      type Member indices (t: Tag, ts: TagList)
        MemHere  : Member(t, TCons(t, rest))
        MemThere : Member(t, rest) -> Member(t, TCons(y, rest))
      type SendsIn indices (b: Behaviour, t: Tag)
        SendHere  : SendsIn(BSend(t, k), t)
        SendSendK : SendsIn(k, t) -> SendsIn(BSend(y, k), t)
      fn coverage(b: Behaviour, {t: Tag}, sends: SendsIn(b, t)) -> Member(t, infer(b)) = match sends
        SendHere()    -> MemHere()
        SendSendK(s2) -> match b
          #{arm}
    end
    """
  end

  test "E1 REACH: refined sibling `b = BSend` makes a single-arm nested match exhaustive" do
    assert {:ok, _} = Program.elaborate(e1_src("BSend(y, k) -> MemThere(coverage(k, s2))"))
  end

  test "E1 CONTROL: the impossible `BRecv` arm under the refinement is rejected" do
    assert {:error, _} = Program.elaborate(e1_src("BRecv(y, k) -> MemThere(coverage(k, s2))"))
  end

  # ---- E1-sub: sibling refinement reaches the written body term ---------------

  # `use_it`'s `RIsA` arm refines `r` to `RA`; the written body term `project(k, r)`
  # must meet the goal RHS `project(k, rhs)`. REACH targets `RA` (convertible),
  # CONTROL targets `RB` (distinct).
  defp e1sub_src(rhs) do
    """
    mod E1SubAb
      type Role = RA | RB
      type TB2 = T | F
      fn role_eq(x: Role, y: Role) -> TB2 = match x
        RA() -> match y
          RA() -> T
          RB() -> F
        RB() -> match y
          RA() -> F
          RB() -> T
      type Tag = TA | TB
      type Local = LEnd | LSend(Tag, Local)
      type Global = GEnd | GMsg(Role, Tag, Global)
      fn project(g: Global, r: Role) -> Local = match g
        GEnd()           -> LEnd
        GMsg(from, t, k) -> match role_eq(from, r)
          T() -> LSend(t, project(k, r))
          F() -> project(k, r)
      type RoleIs indices (r: Role)
        RIsA : RoleIs(RA)
      fn use_it(k: Global, r: Role, ev: RoleIs(r)) -> Equivalent(Local, project(k, r), project(k, #{rhs})) = match ev
        RIsA() -> reflexive(project(k, r))
    end
    """
  end

  test "E1-sub REACH: refined sibling `r = RA` reaches the written `project(k, r)`" do
    assert {:ok, _} = Program.elaborate(e1sub_src("RA"))
  end

  test "E1-sub CONTROL: refinement reaches the written term, so `RA` vs `RB` is rejected" do
    assert {:error, _} = Program.elaborate(e1sub_src("RB"))
  end
end
