defmodule Cure.Elab.PickupTest do
  @moduledoc """
  `pickup` predicate dispatch (value-surface Wave 1). It desugars to a
  right-nested `:conditional` chain and reuses that path's Bool-guard and
  branch-join checks verbatim — no kernel change, no new Core. Guards must be
  Bool; all branch bodies must join. Tests use Bool guards + Nat bodies only
  (the dependent pipeline's supported surface); the classic pickup oracle's
  Atom/atom-literal cases are out of reach for the dependent path today.

  Tests 1, 2, 3, 5, 6 are bare top-level `pickup` bodies — these reach
  `elaborate_expr_typed`'s `:pickup` clause (a bare top-level body is always
  elaborated in infer mode by `declarations.ex`'s `elaborate_body/6`; see the
  plan's Anchors section). Test 4 nests `pickup` as the else-branch of a
  top-level `if` specifically to reach `elaborate_expr_checked`'s `:pickup`
  clause: `:conditional` (unlike `:pickup`) IS in `elaborate_body`'s
  whitelist, so the outer `if` is checked-mode, and its checked `:conditional`
  clause (elaborator.ex:1024-1028) checks BOTH branches via
  `elaborate_expr_checked` — landing the nested `pickup` there for real.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Emit}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  test "3-way pickup with an else terminator selects each branch at runtime" do
    src =
      @nat <>
        "  fn pick(b1: Bool, b2: Bool) -> Nat =\n" <>
        "    pickup\n" <>
        "      b1 -> Z()\n" <>
        "      b2 -> S(Z())\n" <>
        "      else -> S(S(Z()))\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Pickup1", functions: [:pick])

    assert apply(mod, :pick, [true, false]) == :Z
    assert apply(mod, :pick, [false, true]) == {:S, :Z}
    assert apply(mod, :pick, [false, false]) == {:S, {:S, :Z}}
  end

  test "trailing `true ->` terminator form (no pickup_else node) evaluates its body when reached" do
    src =
      @nat <>
        "  fn always_b() -> Nat =\n" <>
        "    pickup\n" <>
        "      false -> Z()\n" <>
        "      true  -> S(Z())\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Pickup2", functions: [:always_b])

    # first guard is literal false, so the trailing-true terminator body is reached
    assert apply(mod, :always_b, []) == {:S, :Z}
  end

  test "a degenerate single-clause `pickup else -> e` collapses to its body" do
    src =
      @nat <>
        "  fn only() -> Nat =\n" <>
        "    pickup\n" <>
        "      else -> S(Z())\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Pickup3", functions: [:only])

    assert apply(mod, :only, []) == {:S, :Z}
  end

  test "a pickup nested as an `if`'s else-branch elaborates in checked position" do
    # Both a bare top-level `pickup` body (Wave 4 added `:pickup` to
    # declarations.ex's elaborate_body whitelist) and this nested case reach
    # elaborate_expr_checked's `:pickup` clause. The distinction this test still
    # usefully exercises is the PATH: here the nested `pickup` arrives via the
    # OUTER `:conditional`'s checked branches (elaborator.ex:1074-1080 checks both
    # then/else via elaborate_expr_checked), landing in the `:pickup` clause that
    # way — rather than via elaborate_body's own (now-present) `:pickup` clause.
    src =
      @nat <>
        "  fn checked(b1: Bool, b2: Bool) -> Nat = if b1 then Z() else pickup\n" <>
        "    b2 -> S(Z())\n" <>
        "    else -> S(S(Z()))\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Pickup4", functions: [:checked])

    assert apply(mod, :checked, [true, true]) == :Z
    assert apply(mod, :checked, [false, true]) == {:S, :Z}
    assert apply(mod, :checked, [false, false]) == {:S, {:S, :Z}}
  end

  test "a non-Bool guard is rejected" do
    # guard `n` : Nat, not Bool — the conditional path's Bool check rejects it.
    src =
      @nat <>
        "  fn bad(n: Nat) -> Nat =\n" <>
        "    pickup\n" <>
        "      n -> Z()\n" <>
        "      else -> S(Z())\nend\n"

    assert {:error, _} = Program.elaborate(src)
  end

  test "non-joining branch types are rejected" do
    # then-branch : Nat, else-branch : Bool — no single result type.
    src =
      @nat <>
        "  fn bad2(b: Bool) -> Nat =\n" <>
        "    pickup\n" <>
        "      b -> Z()\n" <>
        "      else -> true\nend\n"

    assert {:error, _} = Program.elaborate(src)
  end
end
