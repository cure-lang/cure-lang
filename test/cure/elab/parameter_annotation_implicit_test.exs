defmodule Cure.Elab.ParameterAnnotationImplicitTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "a term call in a dependent parameter annotation inserts erased arguments" do
    src = """
    mod ParameterAnnotationImplicit
      type Nat = Z | S(Nat)
      type Flag = Off | On
      type Box(n: Nat) = MkBox
      type Witness(a: Type) indices (value: a)
        MkWitness : Witness(a, value)

      fn choose({n: Nat}, value: Box(n), _flag: Flag) -> Box(n) = value

      fn consume(
        n: Nat,
        value: Box(n),
        witness: Witness(Box(n), choose(value, On()))
      ) -> Nat = n
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end
