defmodule Cure.Elab.CtorArgDeferralTest do
  @moduledoc """
  E6: constructor-argument elaboration defers a field whose type still carries a metavariable
  (an intermediate existential fixed by a SIBLING argument, not by the goal), resolves the
  siblings first, then checks the deferred field — the Idris `checkRestApp`/`checkRtoL` order,
  iterated to a fixpoint. Before this, `check_ctor_args` processed fields strictly left-to-right
  and failed with `:unsolved_field_type`/`:unsolved_metavariables`.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  defp check(defs) do
    src = """
    mod E6T
      type Phase = Up | Down
      type Fail indices (b1: Nat, p1: Phase, b2: Nat, p2: Phase)
        FRestart  : Fail(S(n), Up, n, Up)
        FShutdown : Fail(Z, Up, Z, Down)
      type FailRun indices (b1: Nat, p1: Phase, b2: Nat, p2: Phase)
        FRDone : FailRun(b, p, b, p)
        FRMore : Fail(b1, p1, bm, pm) -> FailRun(bm, pm, b2, p2) -> FailRun(b1, p1, b2, p2)
    #{defs}
    end
    """

    case Program.elaborate(src) do
      {:ok, _} -> :accept
      {:error, _} -> :reject
    end
  end

  test "intermediate existential solved by an EARLIER sibling (FShutdown before FRDone)" do
    # FRMore(FShutdown(), FRDone()): FShutdown : Fail(Z,Up,Z,Down) fixes bm=Z,pm=Down, so FRDone
    # checks against the now-concrete FailRun(Z,Down,Z,Down).
    assert check("""
             fn one() -> FailRun(Z, Up, Z, Down) = FRMore(FShutdown(), FRDone())
           """) == :accept
  end

  test "intermediate existential solved by a LATER sibling (FRestart deferred until the recursive arg)" do
    # FRMore(FRestart(), eventually_down(k)): FRestart's own implicit index cannot be inferred
    # in isolation; it is deferred until the second field (a recursive call, type
    # FailRun(k,Up,Z,Down)) solves bm=k,pm=Up, after which FRestart checks against Fail(S(k),Up,k,Up).
    assert check("""
             fn eventually_down(n: Nat) -> FailRun(n, Up, Z, Down) = match n
               Z()  -> FRMore(FShutdown(), FRDone())
               S(k) -> FRMore(FRestart(), eventually_down(k))
           """) == :accept
  end

  test "deferral does not mask a genuine type error" do
    # Goal FailRun(Z, Up, Z, Down): once the deferred FRestart field resolves to Fail(Z, Up, Z,
    # Down), FRestart : Fail(S(n), Up, n, Up) cannot match (S(n) != Z, Up != Down), so this is
    # correctly rejected — postponement only reorders, it never accepts an ill-typed term.
    assert check("""
             fn bad() -> FailRun(Z, Up, Z, Down) = FRMore(FRestart(), FRDone())
           """) == :reject
  end
end
