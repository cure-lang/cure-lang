defmodule Cure.Elab.WithRematchElabTest do
  @moduledoc """
  Elaboration of with-clause LHS re-matching over an INDEXED view (Idris-parity
  indexed views). A rematch clause restates the parent LHS refined (`n` ↦ `S(m)`
  / `Z`); the body then uses a sibling `w : SNat(n)` at its REFINED type
  (`SNat(S m)` / `SNat(Z)`). The refinement is supplied soundly by the kernel's
  indexed `:case` (index inversion + branch-context specialization); the
  elaborator threads it into the branch goal + sibling context so the body
  elaborates. No TCB change.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  # Nat, its singleton SNat(n), and an indexed view NV(n) whose `vs` constructor
  # carries the SNat singleton (the workaround for un-nameable dependent ctor
  # args). `view n : NV n`; matching it refines `n`.
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

  defp mod(body), do: "mod P\n" <> @preamble <> body <> "end\n"

  test "rematch refines sibling w:SNat(n) -> SNat(S m)/SNat(Z); body returns it" do
    # foo returns the sibling `w` at goal SNat(n). In each branch the LHS-rematch
    # refines `n`, so both the goal AND `w`'s type refine in lockstep — returning
    # `w` type-checks ONLY if BOTH the branch goal and the sibling context are
    # refined by the restated index. (Without threading the whole clause errors.)
    src =
      mod("""
        fn foo(n: Nat, w: SNat(n)) -> SNat(n) =
          with view(n)
            Z(), w | vz() -> w
            S(m), w | vs(s) -> w
      """)

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "rematch body building a fresh refined value uses the with-bound singleton" do
    # In the S(m) branch the with-pattern binds `s : SNat(m)`; `ssuc(s) : SNat(S m)`
    # matches the refined goal SNat(n) = SNat(S m). Exercises goal refinement with
    # a non-trivial body.
    src =
      mod("""
        fn foo(n: Nat, w: SNat(n)) -> SNat(n) =
          with view(n)
            Z(), w | vz() -> szero()
            S(m), w | vs(s) -> ssuc(s)
      """)

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "body consumes the refined sibling w:SNat(S m) (load-bearing on sibling refinement)" do
    # `rel`'s implicit index `k` is inferred from the with-bound singleton
    # `s : SNat(m)` (so k := m); its second argument then requires `SNat(S m)`.
    # Passing `w` type-checks ONLY because the branch context refined
    # `w : SNat(n)` to `SNat(S m)`. Toggling off that refinement makes this
    # arm fail with an index mismatch, so the sibling threading is load-bearing.
    src =
      mod("""
        fn rel({k: Nat}, a: SNat(k), b: SNat(S(k))) -> Nat = Z()
        fn foo(n: Nat, w: SNat(n)) -> Nat =
          with view(n)
            Z(), w | vz() -> Z()
            S(m), w | vs(s) -> rel(s, w)
      """)

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "rematch rejects a body relying on an unentailed refinement (soundness)" do
    # The vs branch entails n := S m, never n := Z. A body returning szero()
    # (: SNat(Z)) where the goal is SNat(n) = SNat(S m) must be rejected.
    src =
      mod("""
        fn foo(n: Nat, w: SNat(n)) -> SNat(n) =
          with view(n)
            Z(), w | vz() -> szero()
            S(m), w | vs(s) -> szero()
      """)

    assert {:error, _} = Program.elaborate(src)
  end
end
