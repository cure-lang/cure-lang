defmodule Cure.Elab.LetCaptureAvoidanceTest do
  @moduledoc """
  Regression: `let` must not capture a nested binder that shadows its name.

  `elaborate_let_block/5` desugars `let x = e ⏎ rest` by SURFACE substitution —
  `rest[x := e]` — unless a later binder shadows `x`, in which case it falls back
  to a bind-once β-redex `(λx:T. rest) e`. Shadowing is detected by `binds_any?/2`,
  so a binder that predicate cannot see gets its body silently rewritten.

  Two binding forms were invisible, because both keep their bound names in the
  node's META rather than among the children the walk traverses:

    * a LAMBDA's parameters (`meta[:params]`) — `binds_any?` had no lambda clause
      at all, so it walked straight through into the body;
    * a MATCH ARM's pattern (`meta[:pattern]`) — only a `{:function_call, _, args}`
      pattern's direct variable arguments were collected, so a bare catch-all arm
      (`x -> S(x)`), and any nested or aliased pattern, went unnoticed.

  These are silent-wrong-answer bugs, not crashes. `let x = Z()` rewrote
  `fn(x) -> S(x)` into `fn(x) -> S(Z())`: a lambda that ignores its own argument.
  The result is still perfectly well-typed at `(Nat) -> Nat`, so the kernel accepts
  it and the program computes the wrong function.

  Over-reporting a binder merely costs the (safe) β-redex path. Under-reporting is
  a miscompilation. When extending `binds_any?`, err toward `true`.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Emit, Program}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  test "a lambda parameter shadowing an outer let-bound name is not captured" do
    src =
      @nat <>
        "  fn ap(f: (Nat) -> Nat, x: Nat) -> Nat = f(x)\n" <>
        "  fn g() -> Nat =\n    let x = Z()\n    ap(fn(x) -> S(x), S(S(Z())))\nend\n"

    {:ok, env} = Program.elaborate(src)

    {:ok, mod} =
      Emit.compile_and_load(env, module: :"Cure.Test.LetCaptureLambda", functions: [:ap, :g])

    # `fn(x) -> S(x)` applied to S(S(Z())) is S(S(S(Z()))) — the lambda's own
    # parameter, not the outer let's Z(), flows into its body.
    assert apply(mod, :g, []) == {:S, {:S, {:S, :Z}}}
  end

  test "a bare-variable match-arm pattern shadowing an outer let-bound name is not captured" do
    src =
      @nat <>
        "  fn g() -> Nat =\n    let x = Z()\n    match S(S(Z()))\n      x -> S(x)\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Test.LetCaptureArm", functions: [:g])

    # The catch-all arm binds `x` to the scrutinee S(S(Z())); the body sees THAT
    # `x`, not the outer let's Z().
    assert apply(mod, :g, []) == {:S, {:S, {:S, :Z}}}
  end

  test "a nested constructor pattern's binder shadowing an outer let-bound name is not captured" do
    src =
      @nat <>
        "  fn g() -> Nat =\n    let x = Z()\n    match S(S(Z()))\n      S(x) -> S(x)\n      Z() -> Z()\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Test.LetCaptureNested", functions: [:g])

    # `S(x)` binds x := S(Z()); the body rebuilds S(S(Z())), not S(Z()).
    assert apply(mod, :g, []) == {:S, {:S, :Z}}
  end

  test "a let-bound name with no shadowing binder still substitutes" do
    # The bind-once β-redex fallback must not swallow the ordinary path: `x` is
    # free in the lambda body here, so the outer let's value must reach it.
    src =
      @nat <>
        "  fn ap(f: (Nat) -> Nat, x: Nat) -> Nat = f(x)\n" <>
        "  fn g() -> Nat =\n    let x = S(Z())\n    ap(fn(y) -> S(x), Z())\nend\n"

    {:ok, env} = Program.elaborate(src)

    {:ok, mod} =
      Emit.compile_and_load(env, module: :"Cure.Test.LetNoShadow", functions: [:ap, :g])

    assert apply(mod, :g, []) == {:S, {:S, :Z}}
  end
end
