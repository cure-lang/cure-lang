defmodule Cure.Core.MutualRecursionReductionTest do
  @moduledoc """
  A mutually-recursive group must be certified TOTAL *as a unit* — every SCC
  member δ-reduces, regardless of declaration order — so a later definition can
  reduce any member in a type/conversion.

  Bug (pre-fix): `Kernel.validate_certificate/2` certified only the single
  submitted name, so a mutual group was certified member-by-member. The
  first-declared member deferred (its sibling's body was still a pending hole)
  and stayed uncertified — opaque to δ — until the end-of-module sweep, which
  runs AFTER dependent definitions are already checked. So `dual(dual(LEnd))`
  stayed a stuck neutral inside a proof declared after the pair, whenever `dual`
  happened to be the first-declared member. The tell: swapping declaration order
  fixed the same proof.

  Fix: certifying a group member certifies the whole proven-total SCC. Both
  declaration orders now certify both members immediately, and the
  mutually-inductive proof checks.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.Env
  alias Cure.Elab.Program

  # `dual` declared FIRST (the order that failed pre-fix).
  @dual_first """
  mod DualFirst
    use Std.Equivalent
    type Tag = TA | TB
    type Local = LEnd | LSel(Branches) | LBra(Branches)
    type Branches = BNil | BCons(Tag, Local, Branches)
    fn dual(l: Local) -> Local = match l
      LEnd()     -> LEnd()
      LSel(bs)   -> LBra(dual_branches(bs))
      LBra(bs)   -> LSel(dual_branches(bs))
    fn dual_branches(bs: Branches) -> Branches = match bs
      BNil()            -> BNil()
      BCons(t, l, rest) -> BCons(t, dual(l), dual_branches(rest))
    fn check_reduce() -> Equivalent(Local, dual(dual(LEnd())), LEnd()) = reflexive(LEnd())
  end
  """

  # `dual_branches` declared first (the order that worked even pre-fix).
  @branches_first """
  mod BranchesFirst
    use Std.Equivalent
    type Tag = TA | TB
    type Local = LEnd | LSel(Branches) | LBra(Branches)
    type Branches = BNil | BCons(Tag, Local, Branches)
    fn dual_branches(bs: Branches) -> Branches = match bs
      BNil()            -> BNil()
      BCons(t, l, rest) -> BCons(t, dual(l), dual_branches(rest))
    fn dual(l: Local) -> Local = match l
      LEnd()     -> LEnd()
      LSel(bs)   -> LBra(dual_branches(bs))
      LBra(bs)   -> LSel(dual_branches(bs))
    fn check_reduce() -> Equivalent(Local, dual(dual(LEnd())), LEnd()) = reflexive(LEnd())
  end
  """

  test "mutual pair reduces in a later proof regardless of declaration order (dual first)" do
    assert {:ok, sig} = Program.elaborate(@dual_first)
    assert Env.certified?(sig, :"DualFirst#dual"), "dual must be certified"
    assert Env.certified?(sig, :"DualFirst#dual_branches"), "dual_branches must be certified"
  end

  test "mutual pair reduces in a later proof regardless of declaration order (branches first)" do
    assert {:ok, sig} = Program.elaborate(@branches_first)
    assert Env.certified?(sig, :"BranchesFirst#dual")
    assert Env.certified?(sig, :"BranchesFirst#dual_branches")
  end

  # Soundness guardrail: certifying the whole SCC must NOT certify a NON-total
  # group. A divergent mutual pair (`f(x) = g(x)`, `g(x) = f(x)`, no decrease
  # through the cycle) is rejected by the size-change criterion, so neither member
  # may be certified — else δ would unfold them and loop / equate distinct forms.
  @divergent """
  mod Divergent
    type L = A | B
    fn f(x: L) -> L = g(x)
    fn g(x: L) -> L = f(x)
  end
  """

  test "a divergent mutual pair stays uncertified (fix does not over-certify)" do
    assert {:ok, sig} = Program.elaborate(@divergent)
    refute Env.certified?(sig, :"Divergent#f"), "divergent f must NOT be certified"
    refute Env.certified?(sig, :"Divergent#g"), "divergent g must NOT be certified"
  end
end
