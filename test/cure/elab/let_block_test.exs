defmodule Cure.Elab.LetBlockTest do
  @moduledoc """
  `let x = e ⏎ body` blocks in the dependent elaborator. The surface parses to
  `{:block, [{:assignment, [let: true], [var, rhs]}, …, body]}`; the elaborator
  desugars each binding to a β-redex `(λ x:T. body) e` (there is no `:let` in
  Core), which the kernel re-checks. Previously `:unsupported_expression`.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  @nat "  type Nat = Z | S(Nat)\n"

  test "a single let in a function body elaborates" do
    src = "mod L\n" <> @nat <> "  fn f(n: Nat) -> Nat =\n    let m = S(n)\n    S(m)\n"
    assert {:ok, _} = Program.elaborate(src)
  end

  test "chained lets elaborate (each binder in scope of the next)" do
    src = "mod L\n" <> @nat <> "  fn f(n: Nat) -> Nat =\n    let a = S(n)\n    let b = S(a)\n    S(b)\n"
    assert {:ok, _} = Program.elaborate(src)
  end

  test "a let-bound value is usable at a dependent (indexed) type" do
    src =
      "mod L\n" <>
        @nat <>
        "  type SNat indices (k: Nat)\n    szero : SNat(Z)\n    ssuc : SNat(k) -> SNat(S(k))\n" <>
        "  fn g(n: Nat, s: SNat(n)) -> SNat(S(n)) =\n    let t = ssuc(s)\n    t\n"

    assert {:ok, _} = Program.elaborate(src)
  end

  test "soundness control: a body ill-typed under the let binding is rejected" do
    # m : Nat; returning m where a SNat is required must still be rejected.
    src =
      "mod L\n" <>
        @nat <>
        "  type SNat indices (k: Nat)\n    szero : SNat(Z)\n    ssuc : SNat(k) -> SNat(S(k))\n" <>
        "  fn bad(n: Nat) -> SNat(n) =\n    let m = S(n)\n    m\n"

    assert {:error, _} = Program.elaborate(src)
  end
end
