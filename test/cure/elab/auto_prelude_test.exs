defmodule Cure.Elab.AutoPreludeTest do
  @moduledoc """
  The dependent-clean core-prelude subset {Std.Bool, Std.Nat} auto-loads into
  every module — no `use` required. Core/Equal/Refine and the Eq/Ord/Show/Functor
  protocols stay explicit (not yet dependent-elaborable / instance-coupling). The
  prelude modules themselves do NOT auto-import (self-contained on seeded builtins).
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  test "connectives (Std.Bool) resolve without `use Std.Bool`" do
    src = "mod UsesBool\n  fn andb(a: Bool, b: Bool) -> Bool = a and b\nend\n"
    assert {:ok, _env} = Program.elaborate(src)
  end

  test "Std.Nat `plus` resolves without `use Std.Nat`" do
    src = "mod UsesNat\n  fn twice(n: Nat) -> Nat = plus(n, n)\nend\n"
    assert {:ok, _env} = Program.elaborate(src)
  end

  test "Bool and Nat both auto-load together (no `use`)" do
    src = "mod UsesBoth\n  fn f(a: Bool, n: Nat) -> Nat = plus(n, plus(n, n))\nend\n"
    assert {:ok, _env} = Program.elaborate(src)
  end

  test "a module declaring its own `type Nat` is NOT collided by auto-imported Std.Nat" do
    # dep04/dep10/fn09-style: a local `Nat = Zero | Suc` must remain canonical;
    # Std.Nat (Z | S) must be skipped, not merged in as a conflicting family.
    src =
      "mod OwnNat\n  type Nat = Zero | Suc(Nat)\n" <>
        "  fn add(a: Nat, b: Nat) -> Nat = match a\n    Zero() -> b\n    Suc(m) -> Suc(add(m, b))\nend\n"

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "a local definition shadows an auto-imported one (no collision error)" do
    # A module defining its own `plus` must still elaborate (local wins).
    src = "mod ShadowsPlus\n  fn plus(a: Bool, b: Bool) -> Bool = a\n  fn use_it(x: Bool) -> Bool = plus(x, x)\nend\n"
    assert {:ok, _env} = Program.elaborate(src)
  end
end
