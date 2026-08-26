defmodule Cure.Elab.GadtResultIndexVarTest do
  @moduledoc """
  A GADT constructor whose result index mentions a free variable that appears
  *only inside a constructor* — `fz : Fin(S(m))` / `FZ : Fin (S n)`, where `m`
  occurs nowhere in an argument — is now auto-bound as an erased implicit index
  argument (Idris parity). Previously the variable was unbound and construction
  failed `:index_mismatch`, because `collect_implicit_vars` only picked up index
  variables that were *bare* arguments of a family application; a variable nested
  in `S(m)` was missed. `collect_index_expr_vars` now recurses into constructor
  applications, typing each free variable by the enclosing constructor's field
  type. Oracle `dep/dep02_fin_construction` pins accept/accept.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Emit}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  test "a constructor with a result-only index variable elaborates and constructs" do
    src =
      @nat <>
        "  type Fin indices (n: Nat)\n" <>
        "    fz : Fin(S(m))\n    fs : Fin(m) -> Fin(S(m))\n" <>
        "  fn f1() -> Fin(S(S(Z))) = fs(fz())\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.FinIdx", functions: [:f1])

    assert apply(mod, :f1, []) == {:fs, :fz}
  end

  test "the result-only index still constrains: a wrong index annotation is rejected" do
    # `fz()` has index `S(m)` for some m, so it can never inhabit `Fin(Z)`.
    assert {:error, _} =
             Program.elaborate(
               @nat <>
                 "  type Fin indices (n: Nat)\n" <>
                 "    fz : Fin(S(m))\n    fs : Fin(m) -> Fin(S(m))\n" <>
                 "  fn bad() -> Fin(Z) = fz()\nend\n"
             )
  end
end
