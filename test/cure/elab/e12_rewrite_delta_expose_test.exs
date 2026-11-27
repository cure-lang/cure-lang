defmodule Cure.Elab.E12RewriteDeltaExposeTest do
  @moduledoc """
  Regression and negative-control tests for Phase 6 reach closure:
  - E12: `rewrite` (legacy `rewrite p in body` and tactic `rewrite using p`)
    exposes targets buried inside a certified definition's stuck `case`
    scrutinee via bounded WHNF (`stuck_cases: :expose`).
  - E13: reflexive/diagonal GADT constructor (`SubRefl : Sub(l, l)`) propagates
    subsequent refinement to the goal.
  - E10: free-monad `bind` with named function and partial-application
    continuations reduces in dependent index position.
  """

  use ExUnit.Case, async: true

  @base_decls """
    use Std.Equivalent
    type Role = RA | RB
    type Bool2 = T | F
    type Global = GEnd | GMsg(Role, Role, Global)
    type Local = LEnd | LSend(Local) | LRecv(Local)

    fn role_eq(a: Role, b: Role) -> Bool2 = match a
      RA() -> match b
        RA() -> T()
        RB() -> F()
      RB() -> match b
        RA() -> F()
        RB() -> T()

    fn project(g: Global, r: Role) -> Local = match g
      GEnd() -> LEnd()
      GMsg(fr, to, k) -> match role_eq(fr, r)
        T() -> LSend(project(k, r))
        F() -> match role_eq(to, r)
          T() -> LRecv(project(k, r))
          F() -> project(k, r)
  """

  test "E12 REACH: legacy rewrite exposes δ-hidden target under certified definition" do
    src = """
    mod E12LegacyReach
    #{@base_decls}
      fn proj_bystander(fr: Role, to: Role, k: Global, r: Role, p1: Equivalent(Bool2, role_eq(fr, r), F()), p2: Equivalent(Bool2, role_eq(to, r), F())) -> Equivalent(Local, project(GMsg(fr, to, k), r), project(k, r)) =
        rewrite p1 in rewrite p2 in reflexive(project(k, r))
    end
    """

    assert {:ok, :"Cure.E12LegacyReach"} = Cure.Compiler.compile_and_load(src, file: "e12_legacy.cure")
  end

  test "E12 REACH: proof-chain tactic rewrite exposes δ-hidden target under certified definition" do
    src = """
    mod E12TacticReach
    #{@base_decls}
      fn proj_bystander(fr: Role, to: Role, k: Global, r: Role, p1: Equivalent(Bool2, role_eq(fr, r), F()), p2: Equivalent(Bool2, role_eq(to, r), F())) -> Equivalent(Local, project(GMsg(fr, to, k), r), project(k, r)) =
        proof chain
          project(GMsg(fr, to, k), r) == project(k, r) because
            rewrite using p1
            rewrite using p2
            simplify
    end
    """

    assert {:ok, :"Cure.E12TacticReach"} = Cure.Compiler.compile_and_load(src, file: "e12_tactic.cure")
  end

  test "E12 CONTROL: false bystander goal is still rejected by the kernel" do
    src = """
    mod E12FalseControl
    #{@base_decls}
      fn proj_bystander_bad(fr: Role, to: Role, k: Global, r: Role, p1: Equivalent(Bool2, role_eq(fr, r), F()), p2: Equivalent(Bool2, role_eq(to, r), F())) -> Equivalent(Local, project(GMsg(fr, to, k), r), LEnd()) =
        rewrite p1 in rewrite p2 in reflexive(LEnd())
    end
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(src, file: "e12_false.cure")
  end

  test "E12 CONTROL: genuine non-occurrence still rejects with rewrite_no_match" do
    src = """
    mod E12NoMatchControl
    #{@base_decls}
      fn no_match(fr: Role, to: Role, r: Role, p1: Equivalent(Bool2, role_eq(fr, r), F())) -> Equivalent(Local, LEnd(), LEnd()) =
        rewrite p1 in reflexive(LEnd())
    end
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(src, file: "e12_nomatch.cure")
  end

  test "E13 REACH: reflexive/diagonal GADT SubRefl propagates refinement to goal" do
    src = """
    mod E13DiagonalReach
      type LType = LEnd | LSel(LType, LType)
      indexed type Sub indices (x: LType, y: LType)
        SubRefl : {l: LType} -> Sub(l, l)
      indexed type LStep indices (x: LType, y: LType)
        LStSelL : {kL: LType} -> {kR: LType} -> LStep(LSel(kL, kR), kL)
      indexed type StepTo indices (x: LType)
        MkStepTo : {a: LType} -> {b: LType} -> LStep(a, b) -> StepTo(a)

      fn sub_step(a: LType, b: LType, b2: LType, sub: Sub(a, b), st: LStep(b, b2)) -> StepTo(a) = match sub
        SubRefl() -> match st
          LStSelL() -> MkStepTo(LStSelL())
    end
    """

    assert {:ok, :"Cure.E13DiagonalReach"} = Cure.Compiler.compile_and_load(src, file: "e13_reach.cure")
  end

  test "E10 REACH: higher-order named and partial-app continuations reduce in index position" do
    src = """
    mod E10HoIndexReach
      use Std.Equivalent
      type Dec = D0 | D1
      type Eff = Pure(Dec) | Bind(Dec, (Dec) -> Eff)
      fn ret(x: Dec) -> Eff = Pure(x)
      fn bind(m: Eff, f: (Dec) -> Eff) -> Eff = match m
        Pure(x) -> f(x)
        Bind(e, g) -> Bind(e, fn(y) -> bind(g(y), f))
      fn kcomp(f: (Dec) -> Eff, g: (Dec) -> Eff) -> (Dec) -> Eff = fn(y) -> bind(f(y), g)
      fn left_id_ret(x: Dec) -> Equivalent(Eff, bind(Pure(x), ret), Pure(x)) = reflexive(Pure(x))
      fn left_id_kcomp(x: Dec, f: (Dec) -> Eff, g: (Dec) -> Eff) -> Equivalent(Eff, bind(Pure(x), kcomp(f, g)), bind(f(x), g)) = reflexive(bind(f(x), g))
    end
    """

    assert {:ok, :"Cure.E10HoIndexReach"} = Cure.Compiler.compile_and_load(src, file: "e10_reach.cure")
  end
end
