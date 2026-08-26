defmodule Cure.Elab.DependentConstructionTest do
  @moduledoc """
  Constructing an indexed (GADT) value from its constructors in checking position
  (Idris parity). `prepend(Z(), empty())` at `-> Vector(Nat, S(Z))` failed: the
  inner `empty()` is underdetermined until `prepend`'s parameter/index are pinned
  from the expected type, and the checking-mode constructor fallback bailed on
  `prepend`'s erased index field.

  `elaborate_ctor_app_bidirectional` now handles erased index fields: it seeds a
  metavariable for the parameters and every field, pins them by unifying the
  constructor's result against the goal (solving the parameter `a` and the index
  `n`), then checks each *present* field against its now-concrete type while
  threading the pinned erased-index values into the assembled term (the same
  `params ++ fields` de Bruijn frame). The kernel re-checks the result, so nothing
  new is trusted.

  Oracle `dep/dep01_vector_construction` pins accept/accept.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Emit}

  @vec "mod M\n  type Nat = Z | S(Nat)\n" <>
         "  type Vector(a: Type) indices (n: Nat)\n" <>
         "    empty : Vector(a, Z)\n" <>
         "    prepend : a -> Vector(a, n) -> Vector(a, S(n))\n"

  test "a nested dependent vector is constructed in return position and runs" do
    src =
      @vec <>
        "  fn v2() -> Vector(Nat, S(S(Z))) = prepend(Z(), prepend(S(Z()), empty()))\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.DepV2", functions: [:v2])

    assert apply(mod, :v2, []) == {:prepend, :Z, {:prepend, {:S, :Z}, :empty}}
  end

  test "a construction whose index disagrees with the annotation is rejected" do
    # length annotation S(Z) (one) but two prepends — the pinned index cannot solve.
    assert {:error, _} =
             Program.elaborate(
               @vec <>
                 "  fn bad() -> Vector(Nat, S(Z)) = prepend(Z(), prepend(Z(), empty()))\nend\n"
             )
  end

  test "a dependent pair packs a vector with its length and projects" do
    # `Sigma(n: Nat, Vector(Nat, n))`: the second component `prepend(Z(),
    # prepend(S(Z()), empty()))` is checked against `Vector(Nat, S(S(Z)))` — the
    # codomain instantiated at the first component. `elaborate_body` routes the
    # tuple through checking mode so the dependent codomain reaches the second
    # component. Oracle `dep/dep03_dependent_pair`.
    src =
      @vec <>
        "  fn twoVec() -> Sigma(n: Nat, Vector(Nat, n)) = %[S(S(Z)), prepend(Z(), prepend(S(Z()), empty()))]\n" <>
        "  fn theLen() -> Nat = twoVec().1\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.DepPair", functions: [:twoVec, :theLen])

    assert apply(mod, :theLen, []) == {:S, {:S, :Z}}
  end
end
