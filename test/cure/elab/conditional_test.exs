defmodule Cure.Elab.ConditionalTest do
  @moduledoc """
  `if cond then a else b` (surface `{:conditional}`) elaborates to the dependent
  Boolean eliminator `{:bool_elim}` (the committed TCB primitive) and runs on the
  BEAM. Bool literals `true`/`false` (`{:literal, subtype: :boolean}`) elaborate to
  `{:bool_lit, _}`. This is the first untrusted increment built on `bool_elim`:
  no kernel change — the elaborator produces a `bool_elim` term the kernel already
  checks, and `emit` lowers it to a BEAM `case … of true/false`.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Emit}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  test "if on a Bool parameter runs both branches on the BEAM" do
    src =
      @nat <>
        "  fn f(b: Bool) -> Nat = if b then S(Z()) else Z()\n" <>
        "  fn onTrue() -> Nat = f(true)\n" <>
        "  fn onFalse() -> Nat = f(false)\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Cond1", functions: [:f, :onTrue, :onFalse])

    assert apply(mod, :onTrue, []) == {:S, :Z}
    assert apply(mod, :onFalse, []) == :Z
  end

  test "a bare bool literal elaborates and runs" do
    src = "mod M\n  fn yes() -> Bool = true\n  fn no() -> Bool = false\nend\n"
    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Cond2", functions: [:yes, :no])

    assert apply(mod, :yes, []) == true
    assert apply(mod, :no, []) == false
  end

  test "if with a bool-literal condition is total and picks the branch" do
    src = @nat <> "  fn pick() -> Nat = if true then Z() else S(Z())\nend\n"
    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Cond3", functions: [:pick])
    assert apply(mod, :pick, []) == :Z
  end

  test "a branch whose type disagrees with the other is rejected" do
    # then : Nat, else : Bool — no single result type; the kernel rejects.
    src = @nat <> "  fn bad(b: Bool) -> Nat = if b then Z() else true\nend\n"
    assert {:error, _} = Program.elaborate(src)
  end
end
