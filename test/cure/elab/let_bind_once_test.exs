defmodule Cure.Elab.LetBindOnceTest do
  @moduledoc """
  `let x = e ⏎ body` must elaborate to the Core `{:let, Cure.Core.Grade.unrestricted(), ty, e, body}` binder, so
  `e` occurs **once** in the term regardless of how often `x` is used.

  Before the `:let` former existed, `elaborate_let_block/5` eliminated the binding
  by *surface substitution*: `e` was re-elaborated at every use site and dropped
  entirely at zero uses. That is the recorded root cause of the let-duplication
  and join-point bugs, and it is unsound the moment a linear value passes through
  it — the elaborator manufactures the aliasing the type system forbids.

  These tests assert the observable consequences (occurrence count in the
  elaborated Core, and evaluation-order-visible binding structure), not the shape
  of any private function.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.Env
  alias Cure.Elab.Program

  @nat "  type Nat = Z | S(Nat)\n"

  # Count subterms structurally equal to `needle` anywhere in `term`.
  defp occurrences(term, needle) when term == needle, do: 1

  defp occurrences(term, needle) when is_tuple(term),
    do: term |> Tuple.to_list() |> Enum.reduce(0, &(occurrences(&1, needle) + &2))

  defp occurrences(list, needle) when is_list(list),
    do: Enum.reduce(list, 0, &(occurrences(&1, needle) + &2))

  defp occurrences(_, _), do: 0

  defp lets(term) when is_tuple(term) do
    self = if elem(term, 0) == :let, do: 1, else: 0
    self + (term |> Tuple.to_list() |> Enum.reduce(0, &(lets(&1) + &2)))
  end

  defp lets(list) when is_list(list), do: Enum.reduce(list, 0, &(lets(&1) + &2))
  defp lets(_), do: 0

  defp body_of!(src, fname) do
    assert {:ok, env} = Program.elaborate(src)
    %{body: body} = Env.get_def(env, fname)
    body
  end

  describe "bind-once" do
    test "a let used twice binds its rhs exactly once" do
      src =
        "mod L\n" <>
          @nat <>
          "  fn add(a: Nat, b: Nat) -> Nat = a\n" <>
          "  fn f(n: Nat) -> Nat =\n    let m = S(n)\n    add(m, m)\n"

      body = body_of!(src, :f)

      # `S(n)` is the rhs. Under surface substitution it appears twice.
      assert occurrences(body, {:ctor, :"L#S", [{:var, 0}]}) == 1
      assert lets(body) == 1
    end

    test "a let used zero times still binds its rhs (it is not dropped)" do
      src = "mod L\n" <> @nat <> "  fn f(n: Nat) -> Nat =\n    let m = S(n)\n    n\n"
      body = body_of!(src, :f)

      assert lets(body) == 1
      assert occurrences(body, {:ctor, :"L#S", [{:var, 0}]}) == 1
    end

    test "chained lets nest rather than duplicate" do
      src =
        "mod L\n" <>
          @nat <>
          "  fn add(a: Nat, b: Nat) -> Nat = a\n" <>
          "  fn f(n: Nat) -> Nat =\n    let a = S(n)\n    let b = S(a)\n    add(b, b)\n"

      body = body_of!(src, :f)
      assert lets(body) == 2
    end
  end

  describe "ζ keeps dependent lets working" do
    # This is the property surface substitution used to buy and a β-redex loses.
    # It must survive the switch to the `:let` binder.
    test "a let-bound value is usable at a dependent (indexed) type" do
      src =
        "mod L\n" <>
          @nat <>
          "  type SNat indices (k: Nat)\n    szero : SNat(Z)\n    ssuc : SNat(k) -> SNat(S(k))\n" <>
          "  fn g(n: Nat, s: SNat(n)) -> SNat(S(n)) =\n    let t = ssuc(s)\n    t\n"

      assert {:ok, _} = Program.elaborate(src)
    end

    test "a let-bound Nat is transparent in a later index position" do
      src =
        "mod L\n" <>
          @nat <>
          "  type SNat indices (k: Nat)\n    szero : SNat(Z)\n    ssuc : SNat(k) -> SNat(S(k))\n" <>
          "  fn h() -> SNat(S(Z())) =\n    let k = Z()\n    ssuc(szero())\n"

      assert {:ok, _} = Program.elaborate(src)
    end

    test "soundness control: a body ill-typed under the binding is still rejected" do
      src =
        "mod L\n" <>
          @nat <>
          "  type SNat indices (k: Nat)\n    szero : SNat(Z)\n    ssuc : SNat(k) -> SNat(S(k))\n" <>
          "  fn bad(n: Nat) -> SNat(n) =\n    let m = S(n)\n    m\n"

      assert {:error, _} = Program.elaborate(src)
    end
  end

  describe "bidirectional let (ascription closes the check-only residual)" do
    # A bare lambda has no inferable type, so bind-once cannot commit to one.
    # `let f : T = fn(x) -> …` supplies it, and the rhs is elaborated in CHECKING
    # mode — exactly what surface substitution did at each use site, done once.
    test "an ascribed lambda rhs binds once" do
      src =
        "mod L\n" <>
          "  fn ap(f: (Int) -> Int, n: Int) -> Int = f(n)\n" <>
          "  fn f(n: Int) -> Int =\n    let g : (Int) -> Int = fn(x) -> x + 1\n    ap(g, n) + ap(g, n)\n"

      body = body_of!(src, :f)
      assert lets(body) == 1
    end

    test "an ascribed rhs is checked, not merely trusted" do
      src =
        "mod L\n" <>
          "  fn f(n: Int) -> Int =\n    let g : (Int) -> Int = n\n    n\n"

      assert {:error, _} = Program.elaborate(src)
    end

    # Without an ascription and without inference, substitution would DUPLICATE
    # the rhs at every use site. Two uses ⇒ diagnostic, not silent duplication.
    test "an unannotated non-inferable rhs used twice is a clear error" do
      src =
        "mod L\n" <>
          "  fn ap(f: (Int) -> Int, n: Int) -> Int = f(n)\n" <>
          "  fn f(n: Int) -> Int =\n    let g = fn(x) -> x + 1\n    ap(g, n) + ap(g, n)\n"

      assert {:error, {:source_context, {:let_needs_annotation, %{name: "g"}}, _}} = Program.elaborate(src)
    end

    # Zero uses: substitution DROPS the rhs, so it is never elaborated and an
    # ill-typed one sails through. Unchecked code must not reach a green build.
    test "an unused, ill-typed, non-inferable rhs is rejected (not silently dropped)" do
      src =
        "mod L\n" <>
          "  fn f(n: Int) -> Int =\n    let g = fn(x) -> nonexistent_thing(x)\n    n\n"

      assert {:error, _} = Program.elaborate(src)
    end

    test "an ascribed unused rhs IS elaborated, and its errors surface" do
      src =
        "mod L\n" <>
          "  fn f(n: Int) -> Int =\n    let g : (Int) -> Int = fn(x) -> nonexistent_thing(x)\n    n\n"

      assert {:error, _} = Program.elaborate(src)
    end

    # One use cannot duplicate, so substitution stays legal (and is what the
    # stdlib relies on today).
    test "an unannotated non-inferable rhs used once still elaborates" do
      src =
        "mod L\n" <>
          "  fn ap(f: (Int) -> Int, n: Int) -> Int = f(n)\n" <>
          "  fn f(n: Int) -> Int =\n    let g = fn(x) -> x + 1\n    ap(g, n)\n"

      assert {:ok, _} = Program.elaborate(src)
    end
  end
end
