defmodule Cure.Elab.CallArgumentPlaceholderTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "an explicit placeholder is solved from a later dependent argument" do
    source = """
    mod PlaceholderLater
      type Nat = Z | S(Nat)
      type Is indices (n: Nat)
        IsZ : Is(Z)
        IsS : Is(n) -> Is(S(n))
      fn index(n: Nat, w: Is(n)) -> Nat = n
      fn zero() -> Nat = index(_, IsZ())
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "a dependent argument can solve a placeholder with a carried runtime value" do
    source = """
    mod PlaceholderCarried
      type Nat = Z | S(Nat)
      type Box indices (n: Nat)
        MkBox : (value: Nat) -> Box(value)
      fn index(n: Nat, box: Box(n)) -> Nat = n
      fn zero() -> Nat = index(_, MkBox(Z()))
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "the expected result can solve a dependent placeholder" do
    source = """
    mod PlaceholderExpected
      type Nat = Z | S(Nat)
      type Box indices (n: Nat)
        MkBox : (value: Nat) -> Box(value)
      fn box(n: Nat) -> Box(n) = MkBox(n)
      fn zero() -> Box(Z) = box(_)
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "an unconstrained explicit placeholder remains an error" do
    source = """
    mod PlaceholderAmbiguous
      type Nat = Z | S(Nat)
      fn first(x: Nat, y: Nat) -> Nat = x
      fn bad() -> Nat = first(_, Z())
    end
    """

    assert {:error, _reason} = Program.elaborate(source)
  end

  test "underscore outside a call argument is not promoted to a hole" do
    source = """
    mod PlaceholderScope
      type Nat = Z | S(Nat)
      fn bad() -> Nat = _
    end
    """

    assert {:error, _reason} = Program.elaborate(source)
  end
end
