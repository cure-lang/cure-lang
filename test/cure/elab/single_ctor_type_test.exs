defmodule Cure.Elab.SingleCtorTypeTest do
  @moduledoc """
  Single-constructor data types (Idris parity). `type Box = MkBox(Nat)` used to
  parse as a `:type_annotation` (a type alias) because only a `|`-separated body
  became an `:enum` container, so `Box` was never registered as an inductive
  family and a `match` on it failed `:match_scrutinee_not_data`. The parser now
  treats a lone constructor *with fields* (`variant: true` `{:function_def}`) as a
  one-constructor family; a genuine alias RHS (a plain type expression) stays a
  `:type_annotation`. Oracle `match/mt20_single_ctor_type` pins accept/accept.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Emit}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  test "a single-constructor type can be matched and run" do
    src =
      @nat <>
        "  type Box = MkBox(Nat)\n  fn un(b: Box) -> Nat = match b\n    MkBox(x) -> x\n" <>
        "  fn g() -> Nat = un(MkBox(S(Z())))\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.SingleCtorBox", functions: [:un, :g])

    assert apply(mod, :g, []) == {:S, :Z}
  end

  test "a single constructor with several fields destructures" do
    src =
      @nat <>
        "  type Pair = MkPair(Nat, Nat)\n  fn first(p: Pair) -> Nat = match p\n    MkPair(a, b) -> a\n" <>
        "  fn g() -> Nat = first(MkPair(S(Z()), Z()))\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.SingleCtorPair", functions: [:first, :g])

    assert apply(mod, :g, []) == {:S, :Z}
  end
end
