defmodule Cure.Elab.GeneralizingMatchTest do
  @moduledoc """
  Phase 3 / Track B1 — the generalizing match front-end composes BOTH scrutinee-
  refinement mechanisms in one clause:

    * (1a) dependency reversion / index inversion + sibling refinement — capability
      C's `with … | …` rematch (`elaborate_with_rematch`);
    * (1b) occurrence-abstraction of the scrutinee VALUE in the goal — the Phase-2½
      value-refinement that plain `match` gained (`elaborate_matched_branch`).

  The `with`-rematch path already shares `build_motive` (so the motive abstracts a
  computed scrutinee), but its BRANCH elaboration only applied the index inversion,
  not the value-refinement — so a rematch whose GOAL names the scrutinee value
  (`Equivalent(NV(n), view(n), view(n))`) failed to refine per branch (`vz` branch goal
  stayed `Equivalent(NV(n), …)` instead of `Equivalent(NV(Z), vz, vz)`). Idris `case` accepts the
  combined shape.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  @preamble """
    type Nat = Z | S(Nat)
    type SNat indices (n: Nat)
      szero : SNat(Z)
      ssuc : SNat(n) -> SNat(S(n))
    type NV indices (n: Nat)
      vz : NV(Z)
      vs : SNat(n) -> NV(S(n))
    fn toS(m: Nat) -> SNat(m) = match m
      Z() -> szero()
      S(j) -> ssuc(toS(j))
    fn view(n: Nat) -> NV(n) = match n
      Z() -> vz()
      S(m) -> vs(toS(m))
  """
  defp mod(b), do: "mod P\n" <> @preamble <> b <> "end\n"

  test "(gm01) with-rematch whose goal names the scrutinee value refines per branch" do
    # Capability C (with-rematch on the indexed NV via `view(n)`) AND capability A
    # (goal `Equivalent(NV(n), view(n), view(n))` names the scrutinee value). Each branch
    # must refine the goal to the branch constructor: vz → Equivalent(NV(Z), vz, vz);
    # vs(s) → Equivalent(NV(S m), vs s, vs s), which reflexive(ctor) inhabits.
    src =
      mod("""
        fn foo(n: Nat, w: SNat(n)) -> Equivalent(NV(n), view(n), view(n)) =
          with view(n)
            Z(), w | vz() -> reflexive(vz())
            S(m), w | vs(s) -> reflexive(vs(s))
      """)

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "(gm02 control) plain with-rematch, goal names only the index — already worked" do
    # No value-in-goal: the goal is `SNat(n)`, refined only by the index inversion.
    # This is the pre-existing capability-C behaviour and must stay green.
    src =
      mod("""
        fn foo(n: Nat, w: SNat(n)) -> SNat(n) =
          with view(n)
            Z(), w | vz() -> szero()
            S(m), w | vs(s) -> ssuc(s)
      """)

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "(gm03 soundness control) a mismatched-constructor body at the refined goal is rejected" do
    # In the vz branch the goal refines to Equivalent(NV(Z), vz, vz). Returning
    # reflexive(vs(szero())) (: Equivalent(NV(S _), …)) must be rejected — the value refinement
    # must not over-accept.
    src =
      mod("""
        fn foo(n: Nat, w: SNat(n)) -> Equivalent(NV(n), view(n), view(n)) =
          with view(n)
            Z(), w | vz() -> reflexive(vs(szero()))
            S(m), w | vs(s) -> reflexive(vs(s))
      """)

    assert {:error, _} = Program.elaborate(src)
  end
end
