defmodule Cure.Elab.MutualTypeDeclarationsTest do
  @moduledoc """
  Type declarations in a module may reference each other regardless of source
  order — a forward reference to a type declared later, and mutual recursion
  between two types, both elaborate. This is the standard `data`-block behaviour
  in Idris/Agda/Haskell: all type *headers* in a declaration group are in scope
  before any constructor *body* is elaborated.

  Before the header pre-pass, `Cure.Elab.Program`'s `register_pass` elaborated
  each type container fully (header + constructors) in source order, so a
  constructor field naming a not-yet-elaborated sibling failed the kernel's
  `{:global, name}` lookup with `:unknown_global`. Backward references already
  worked (the sibling was elaborated first), which is what these tests contrast
  against.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  defp elaborates?(src) do
    case Program.elaborate(src) do
      {:ok, _env} -> :ok
      {:error, e} -> {:error, e}
    end
  end

  test "a constructor field may forward-reference a type declared later" do
    src = """
    mod P
      type A = MkA(B)
      type B = MkB
    end
    """

    assert :ok = elaborates?(src)
  end

  test "backward references keep working (regression guard)" do
    src = """
    mod P
      type B = MkB
      type A = MkA(B)
    end
    """

    assert :ok = elaborates?(src)
  end

  test "two types may be mutually recursive" do
    src = """
    mod P
      type A = MkA(B)
      type B = MkB(A) | NilB
    end
    """

    assert :ok = elaborates?(src)
  end

  test "a record field may forward-reference a later enum (the Std.Json shape)" do
    # Mirrors `Std.Json`: a `rec`/struct whose field type names a `type` declared
    # further down the module.
    src = """
    mod P
      rec Pair
        value: Value
      type Value = IntV(Int) | NilV
    end
    """

    assert :ok = elaborates?(src)
  end

  test "a type alias wins over a same-spelled constructor in type position" do
    src = """
    mod ConstructorAliasSeparation
      use Std.String

      type Value = String(String) | Empty

      rec Error
        message: String

      fn text(value: Value) -> String =
        match value
          String(contents) -> contents
          Empty() -> ""
    end
    """

    assert :ok = elaborates?(src)
  end
end
