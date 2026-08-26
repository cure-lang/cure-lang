defmodule Cure.Elab.CtorGuardTest do
  use ExUnit.Case, async: false
  alias Cure.Elab.{Program, Emit}

  # Constructor-guard desugaring (elaborator.ex `desugar_ctor_guards` /
  # `fold_ctor_guard_groups`): several match arms sharing ONE constructor but
  # carrying different `when` guards must fold into a SINGLE case branch that
  # destructures the constructor once and dispatches the guards in source order,
  # with the unguarded arm of the same constructor (or an outer default) as the
  # fall-through. This whole path was reachable from surface syntax but untested.

  @src """
  mod P
  type NList = NNil | NCons(Nat, NList)

  fn classify(xs: NList) -> Nat = match xs
    NCons(h, t) when h == Z() -> one()
    NCons(h, t) when h == S(Z()) -> two()
    NCons(h, t) -> zero()
    NNil() -> three()
  end

  fn zero() -> Nat = Z()
  fn one() -> Nat = S(Z())
  fn two() -> Nat = S(S(Z()))
  fn three() -> Nat = S(S(S(Z())))

  fn mk0() -> NList = NCons(Z(), NNil())
  fn mk1() -> NList = NCons(S(Z()), NNil())
  fn mk2() -> NList = NCons(S(S(Z())), NNil())
  fn mkE() -> NList = NNil()
  """

  test "same-constructor guarded arms elaborate (the fold runs)" do
    assert {:ok, %Cure.Core.Env{}} = Program.elaborate(@src)
  end

  test "the folded guards dispatch correctly at runtime on the BEAM" do
    {:ok, env} = Program.elaborate(@src)

    {:ok, mod} =
      Emit.compile_and_load(env,
        module: :"Cure.CtorGuardE2E",
        functions: [:classify, :zero, :one, :two, :three, :mk0, :mk1, :mk2, :mkE]
      )

    classify = fn builder -> apply(mod, :classify, [apply(mod, builder, [])]) end

    # h == Z ⇒ first guard fires ⇒ one()
    assert classify.(:mk0) == apply(mod, :one, [])
    # h == S Z ⇒ second guard fires ⇒ two()
    assert classify.(:mk1) == apply(mod, :two, [])
    # h is neither ⇒ falls through the folded Cons branch to the unguarded arm ⇒ zero()
    assert classify.(:mk2) == apply(mod, :zero, [])
    # a DISTINCT constructor is untouched by the fold ⇒ three()
    assert classify.(:mkE) == apply(mod, :three, [])
  end

  # An OUTER default (a variable/wildcard arm) — rather than an unguarded arm of the
  # same constructor — supplies the fall-through for the guarded group.
  @wild_src """
  mod P
  type NList = NNil | NCons(Nat, NList)

  fn g(xs: NList) -> Nat = match xs
    NCons(h, t) when h == Z() -> one()
    rest -> zero()
  end

  fn zero() -> Nat = Z()
  fn one() -> Nat = S(Z())
  fn mk0() -> NList = NCons(Z(), NNil())
  fn mk1() -> NList = NCons(S(Z()), NNil())
  fn mkE() -> NList = NNil()
  """

  test "a wildcard default closes the guarded group (elaborates + dispatches)" do
    {:ok, env} = Program.elaborate(@wild_src)

    {:ok, mod} =
      Emit.compile_and_load(env,
        module: :"Cure.CtorGuardWildE2E",
        functions: [:g, :zero, :one, :mk0, :mk1, :mkE]
      )

    g = fn b -> apply(mod, :g, [apply(mod, b, [])]) end
    # guard fires
    assert g.(:mk0) == apply(mod, :one, [])
    # guard fails ⇒ wildcard default
    assert g.(:mk1) == apply(mod, :zero, [])
    # Nil ⇒ wildcard default
    assert g.(:mkE) == apply(mod, :zero, [])
  end

  # A constructor whose arms are ALL guarded, with no unguarded arm and no outer
  # default, cannot be shown exhaustive (guards are opaque booleans) — the
  # elaborator must reject it rather than emit a partial match.
  @nonexhaustive_src """
  mod P
  type NList = NNil | NCons(Nat, NList)

  fn f(xs: NList) -> Nat = match xs
    NCons(h, t) when h == Z() -> S(Z())
    NNil() -> Z()
  end
  """

  test "a fully-guarded constructor group with no fall-through is rejected" do
    assert {:error, error} = Program.elaborate(@nonexhaustive_src)
    assert {:unsupported_guard, :non_exhaustive} = Program.semantic_error(error)
  end
end
