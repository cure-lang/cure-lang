defmodule Cure.Elab.FunctionTypeAliasTest do
  @moduledoc """
  Function-type aliases (Idris parity): `type Endo = (Nat) -> Nat`.

  Two parts. The parser accepts a function-type right-hand side for a type alias
  (previously only ADT variants / simple aliases / refinements parsed there — a
  leading `(` was an unexpected token). And `build_context` weak-head-normalises
  each parameter type, so an `Endo`-typed parameter is stored as the underlying Π
  the kernel inspects when the parameter is applied (`f(x)`) — otherwise the alias
  stayed a neutral global and `ensure_pi` reported `:not_a_function`. The whnf is
  conversion-preserving (the alias is definitionally its RHS), so this is an
  elaborator-only change; the kernel is untouched.

  Oracle `alias/al02_function_type` pins accept/accept.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Emit}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  test "a function-type alias is declared and an aliased parameter is applied" do
    src =
      @nat <>
        "  type Endo = (Nat) -> Nat\n" <>
        "  fn ap(f: Endo, x: Nat) -> Nat = f(x)\n" <>
        "  fn inc(n: Nat) -> Nat = S(n)\n" <>
        "  fn g() -> Nat = ap(inc, Z())\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.FnAlias", functions: [:ap, :inc, :g])

    # ap(inc, Z()) = inc(Z()) = S(Z).
    assert apply(mod, :g, []) == {:S, :Z}
  end

  test "a bare data alias still parses and elaborates" do
    # Guard that routing a `(`-led RHS to the type-expression parser did not
    # disturb the ordinary alias path.
    {:ok, _env} =
      Program.elaborate(@nat <> "  type Count = Nat\n  fn f(c: Count) -> Nat = c\nend\n")
  end
end
