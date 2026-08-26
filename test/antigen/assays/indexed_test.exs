defmodule Antigen.Assays.IndexedTest do
  use ExUnit.Case, async: true
  alias Antigen.Assays.Indexed, as: A
  alias Antigen.Generators.Indexed, as: G

  test "4.1 well-typed branch-family case is accepted (no violation)" do
    assert :ok == A.run(G.branch_family(:well_typed))
  end

  test "4.1 ill-typed foreign-branch case must be rejected by the kernel" do
    # SOUNDNESS assertion: the kernel must NOT accept a Dec case with a Foo branch.
    # If this returns a {:wrongly_accepted, _} violation, the kernel has a hole —
    # apply the family-scoping fix, then this returns :ok.
    assert :ok == A.run(G.branch_family(:ill_typed))
  end

  test "4.2 a known Tri constructor specializes to its reachable branch" do
    assert :ok == A.run(G.coverage(:well_typed))
  end

  test "4.2 a non-exhaustive case on an opaque Tri variable is rejected" do
    assert :ok == A.run(G.coverage(:ill_typed))
  end

  test "4.3 ill-typed wrap-branch (wrong body type) must be rejected" do
    assert :ok == A.run(G.refinement(:ill_typed))
  end

  test "4.3 refinement-complete well-typed case is now accepted (completeness fix)" do
    # Pre-fix this replayed {:wrongly_rejected, {:refine, :branch_type}} (the
    # documented incompleteness). unify_indices now solves n := Causal from the
    # wrap ctor's ground result index and refines h : Ix n to Ix Causal.
    assert :ok == A.run(G.refinement(:well_typed))
  end

  test "4.4 well-formed motive is accepted" do
    assert :ok == A.run(G.motive_wf(:well_typed))
  end

  test "4.4 over-applied (malformed) motive must be rejected" do
    assert :ok == A.run(G.motive_wf(:ill_typed))
  end

  test "4.5 impossible wrap-branch (scrutinee Ix Dcoupled) is discharged and accepted" do
    # The wrap ctor builds Ix Causal, so on an Ix Dcoupled scrutinee its branch is
    # unreachable; its deliberately ill-typed body is not checked. Completeness.
    assert :ok == A.run(G.discharge(:well_typed))
  end

  test "4.5 SOUNDNESS: the SAME ill-typed body in a REACHABLE branch must be rejected" do
    # Scrutinee Ix Causal ⇒ wrap IS reachable ⇒ the {:type,0} body must be checked
    # and rejected. If the kernel ever over-fires discharge on a reachable branch,
    # this replays {:wrongly_accepted, _} — the antibody goes red.
    assert :ok == A.run(G.discharge(:ill_typed))
  end

  test "4.6 injectivity: an equation solved by descending through MkWr is accepted" do
    # Result index MkWr(Causal) vs scrutinee index MkWr(n) unifies only by
    # descending through the shared MkWr head (injectivity) to solve n := Causal.
    assert :ok == A.run(G.injectivity(:well_typed))
  end

  test "4.6 SOUNDNESS: injectivity must not fabricate an unentailed equation" do
    # The branch can only ever derive n := Causal; a body demanding IW(MkWr Dcoupled)
    # must be rejected. If injectivity ever produced n := Dcoupled (or dropped the
    # descent and mis-refined), this replays {:wrongly_accepted, _} — antibody red.
    assert :ok == A.run(G.injectivity(:ill_typed))
  end

  # -- W3: deletion rule (pre-port banking spec §4 W3; roadmap A2/#23) --------
  test "W3 deletion: equal literal indices are consistent — branch reachable, well-typed body accepted" do
    assert :ok == A.run(G.deletion(:well_typed))
  end

  test "W3 deletion: equal literal indices never discharge the branch — ill-typed body rejected" do
    assert :ok == A.run(G.deletion(:ill_typed))
  end
end
