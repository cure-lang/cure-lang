defmodule Cure.Elab.FirstClassFunctionTest do
  @moduledoc """
  First-class functions (Idris parity). Three layers cooperate:

    * a non-dependent arrow type `(A) -> B` elaborates to a native Core Π
      (`declarations.ex` `arrow_to_pi`), so the kernel can apply function-typed
      values and check lambdas against them;
    * a lambda `fn(y) -> body` is elaborated in checking mode against the
      expected Π (`elaborator.ex` `elaborate_lambda`), currying multi-parameter
      lambdas;
    * codegen erases every function value—lambdas and named definitions alike—to
      the same curried 1-arg BEAM closure ABI and applies one argument at a time
      (`emit.ex`).

  Oracle `func/fn01_higher_order` + `func/fn02_lambda_body` pin accept/accept.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Emit}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  test "a higher-order function applied to a named function runs end-to-end" do
    src =
      @nat <>
        "  fn ap(f: (Nat) -> Nat, x: Nat) -> Nat = f(x)\n" <>
        "  fn inc(n: Nat) -> Nat = S(n)\n" <>
        "  fn g() -> Nat = ap(inc, S(Z()))\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.FcfHof", functions: [:ap, :inc, :g])

    # ap(inc, S(Z)) = inc(S(Z)) = S(S(Z)).
    assert apply(mod, :g, []) == {:S, {:S, :Z}}
  end

  test "a multi-argument named function value uses the curried closure ABI" do
    src =
      @nat <>
        "  fn apply2(f: (Nat) -> (Nat) -> Nat, x: Nat, y: Nat) -> Nat = f(x, y)\n" <>
        "  fn first(x: Nat, _y: Nat) -> Nat = x\n" <>
        "  fn g() -> Nat = apply2(first, S(Z()), Z())\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.FcfNamedCurry", functions: [:apply2, :first, :g])

    assert apply(mod, :g, []) == {:S, :Z}
  end

  test "a lambda returned by a function is a curried BEAM fun" do
    src = @nat <> "  fn mk() -> (Nat) -> Nat = fn(y) -> S(y)\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.FcfLam", functions: [:mk])

    f = apply(mod, :mk, [])
    assert is_function(f, 1)
    assert f.(:Z) == {:S, :Z}
  end

  test "a function-typed parameter is applied (closure application)" do
    src = @nat <> "  fn ap(f: (Nat) -> Nat, x: Nat) -> Nat = f(x)\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.FcfAp", functions: [:ap])

    assert apply(mod, :ap, [fn n -> {:S, n} end, :Z]) == {:S, :Z}
  end

  test "a curried two-parameter lambda applies one argument at a time" do
    src = @nat <> "  fn adder() -> (Nat) -> (Nat) -> Nat = fn(a) -> fn(b) -> S(a)\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.FcfCurry", functions: [:adder])

    g = apply(mod, :adder, [])
    assert g.(:Z).({:S, :Z}) == {:S, :Z}
  end

  test "a lambda passed as a higher-order argument runs end-to-end" do
    # Bidirectional application routes the callee's parameter type `(Nat)->Nat` to
    # the untyped lambda so it can be checked (`elaborate_bidirectional_app`).
    src =
      @nat <>
        "  fn ap(f: (Nat) -> Nat, x: Nat) -> Nat = f(x)\n" <>
        "  fn g(n: Nat) -> Nat = ap(fn(y) -> S(y), n)\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.FcfLamArg", functions: [:ap, :g])

    # ap((\y. S y), Z) = S(Z).
    assert apply(mod, :g, [:Z]) == {:S, :Z}
  end

  test "chained application of a call result runs (mk()(z))" do
    # `mk()(z)` parses with the inner call as `:callee`; the elaborator applies the
    # outer argument to mk's function-typed result, and codegen calls mk() then
    # applies z to the returned fun (erase keeps the over-applied argument).
    src =
      @nat <>
        "  fn mk() -> (Nat) -> Nat = fn(y) -> S(y)\n" <>
        "  fn g(z: Nat) -> Nat = mk()(z)\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.FcfChain", functions: [:mk, :g])

    assert apply(mod, :g, [:Z]) == {:S, :Z}
  end

  test "multi-level chained application (adder()(a)(b))" do
    src =
      @nat <>
        "  fn adder() -> (Nat) -> (Nat) -> Nat = fn(a) -> fn(b) -> S(a)\n" <>
        "  fn g() -> Nat = adder()(S(Z()))(Z())\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.FcfChain2", functions: [:adder, :g])

    # S(a) with a = S(Z).
    assert apply(mod, :g, []) == {:S, {:S, :Z}}
  end

  test "a lambda checked against a non-function type is rejected" do
    src = @nat <> "  fn bad() -> Nat = fn(y) -> S(y)\nend\n"

    assert {:error, _} = Program.elaborate(src)
  end
end
