defmodule Cure.E2E.TypesAsValuesTest do
  @moduledoc """
  Types are first-class VALUES of type `Type` (Idris/Agda/Lean parity: a type
  constructor name in term position elaborates to the type value, `Int : Type`).

  Cure resolves inductive families in value position to `{:data, F, [], []}`
  already; this pins the same for the machine PRIMITIVE base types (Int, Float,
  Binary, Atom), which are `Env.put_primitive` bindings rather than families and
  used to fall through to `{:global, :Int}` → `:unknown_global`. The kernel
  already types the primitive Core nodes at `{:vtype, 0}`, so this is a pure
  E-layer resolution fix (zero TCB).
  """
  use ExUnit.Case, async: false

  alias Cure.Elab.Program

  defp elab(src) do
    try do
      Program.elaborate(src)
    rescue
      e -> {:raise, Exception.message(e)}
    catch
      k, v -> {:raise, "#{inspect(k)}: #{inspect(v)}"}
    end
  end

  test "a primitive type name in return-value position elaborates as a Type value" do
    src = """
    mod TAV
      fn f() -> Type = Int
    """

    assert {:ok, _env} = elab(src)
  end

  test "each machine primitive (Int/Float/Binary/Atom) is a first-class Type value" do
    for prim <- ["Int", "Float", "Binary", "Atom"] do
      src = """
      mod TAV
        fn f() -> Type = #{prim}
      """

      assert {:ok, _env} = elab(src), "#{prim} should elaborate as a Type value"
    end
  end

  test "a primitive type flows through a let binding" do
    src = """
    mod TAV
      fn f() -> Type =
        let x = Int
        x
    """

    assert {:ok, _env} = elab(src)
  end

  test "a primitive type passes as an argument to a Type -> Type function" do
    src = """
    mod TAV
      fn id(x: Type) -> Type = x
      fn f() -> Type = id(Int)
    """

    assert {:ok, _env} = elab(src)
  end

  test "a type-returning match branches over primitive Type values" do
    src = """
    mod TAV
      fn pick(b: Bool) -> Type =
        match b
          true -> Int
          false -> Float
    """

    assert {:ok, _env} = elab(src)
  end
end
