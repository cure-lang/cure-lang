defmodule Antigen.OverloadInIndexResolutionAntibodyTest do
  @moduledoc """
  E-layer antibody (E11, spec `2026-07-18-elaborator-gaps-verified-status.md` §3) —
  a bare OVERLOADED name (≥2 same-spelling members discriminated by argument type)
  appearing in a dependent INDEX position must resolve by argument type there
  exactly as it does in term position, WITHOUT the widening ever admitting an
  ill-typed program, silently mis-resolving to the wrong member, or crashing the
  kernel on a genuinely ambiguous set.

  ## The gap this closes (RED before the fix)

  A return-type index like `Equivalent(Box, pick(MkB(Red()), MkB(Green())), …)`
  lowers through `idx_to_core → lower_applied_type`. That path never consulted the
  overload set: `applied_def_key`'s pre-overload resolver mis-picked an ambient
  same-name provider (`plus(MkM …)` → the ambient `Std.Nat#plus`), and the kernel
  then crashed reducing the wrong member against the wrong constructor
  (`ι: no branch for constructor :MkM`). Term position already resolved correctly
  via `overload_candidates/2` + `Overload.resolve/5`; the index path did not.

  The fix routes a bare, unshadowed, unqualified applied name whose overload set
  has ≥2 members through the SAME machinery term position uses
  (`Elaborator.elaborate_overloaded_app/7`), before the pre-overload key resolver.
  This is an E-layer widening; the kernel re-checks the assembled Core term, so the
  antibody's job is to prove the widening is CONSERVATIVE — it lets the
  previously-crashing well-typed program through, resolves to the RIGHT member, and
  fails closed on everything else.

  ## Obligations

    * REACH — the type-distinguishable program (`pick` has a `Box` member and a
      `Bag` member; the index occurrence is applied to `Box` args) elaborates, and
      the reflexive proof closes only because the Box member's body (`= b`) reduces
      correctly. RED before the fix (kernel crash).

    * CONTROL A (mis-resolution / false equation stays rejected) — the SAME
      well-typed occurrence, but the equation claims the wrong result
      (`pick(MkB Red, MkB Green) ≡ MkB Red` when the Box member returns its second
      argument, `MkB Green`). It must be rejected. This guards against a resolution
      that picks the wrong member, or one that fabricates a unifier — the resolved
      member must genuinely reduce, and to the value its own clauses dictate.

    * CONTROL B (genuine ambiguity fails closed, not crash) — two members with
      indistinguishable signatures (`(Box, Box) -> Box` twice) in index position
      must surface a clean `{:ambiguous_overload, …}` error, NEVER the pre-fix
      kernel crash. Proves the widening degrades to a diagnosable rejection.

  A fix that greens REACH without regressing either CONTROL is sound: the widening
  admits the well-typed program, resolves to the correct member, and continues to
  reject a false equation and a genuinely ambiguous set.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  # Shared preamble: a two-member overload set for `pick`, one over `Box` and one
  # over `Bag`, plus `Std.Equivalent` in scope. Only the final `Equivalent(…)`-typed
  # def differs between REACH and CONTROL A.
  defp src(final_def) do
    """
    mod OvIdx
      use Std.Equivalent
      type Colour = Red | Green
      type Box = MkB(Colour)
      type Bag = MkG(Colour)
      fn pick(a: Box, b: Box) -> Box = match a
        MkB(x) -> b
      fn pick(a: Bag, b: Bag) -> Bag = match a
        MkG(x) -> b
      #{final_def}
    end
    """
  end

  # ---- Obligation 1: REACH (overload resolves in index; proof closes) --------

  test "REACH: an overloaded name in index position resolves by argument type" do
    reach =
      "fn resolves() -> " <>
        "Equivalent(Box, pick(MkB(Red()), MkB(Green())), MkB(Green())) = " <>
        "reflexive(MkB(Green()))"

    assert {:ok, _} = Program.elaborate(src(reach))
  end

  # ---- Obligation 2: CONTROL A (mis-resolution / false equation rejected) ----

  test "CONTROL A: a false equation over the resolved member stays rejected" do
    bad =
      "fn bad() -> " <>
        "Equivalent(Box, pick(MkB(Red()), MkB(Green())), MkB(Red())) = " <>
        "reflexive(MkB(Red()))"

    assert {:error, _} = Program.elaborate(src(bad))
  end

  # ---- Obligation 3: CONTROL B (genuine ambiguity fails closed) --------------

  test "CONTROL B: a genuinely ambiguous overload in index position fails closed" do
    ambiguous = """
    mod OvIdxAmb
      use Std.Equivalent
      type Colour = Red | Green
      type Box = MkB(Colour)
      fn pick(a: Box, b: Box) -> Box = match a
        MkB(x) -> b
      fn pick(a: Box, b: Box) -> Box = match a
        MkB(x) -> a
      fn resolves() -> Equivalent(Box, pick(MkB(Red()), MkB(Green())), MkB(Green())) = reflexive(MkB(Green()))
    end
    """

    assert {:error, {:ambiguous_overload, :pick, _}} = Program.elaborate(ambiguous)
  end
end
