defmodule Cure.Elab.InstanceSignatureConversionTest do
  @moduledoc """
  Phase 1: an instance method whose type does not match the interface's
  (head-substituted) signature is rejected by kernel conversion with a
  `:method_signature_mismatch` sited at the implementation.

  Note: the passing instance body uses `a == b` rather than the primitive
  `Std.Builtin.struct_eq` spelling — surface-callable builtins land in a later
  task. `==` already lowers correctly (Color → struct_eq), so this program
  compiles today and exercises exactly the signature-conversion path this task
  installs.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  test "a mismatched return type is rejected at the implementation" do
    src = """
    mod M
      use Std.Equatable
      type Color = Red | Green | Blue
      implementation Equatable for Color
        fn `==`(a: Color, b: Color) -> Color = a
    end
    """

    assert {:error, {:method_signature_mismatch, %{interface: :Equatable, method: :==}}} =
             Program.elaborate(src)
  end

  test "a correctly-typed instance passes conversion" do
    src = """
    mod M
      use Std.Equatable
      type Color = Red | Green | Blue
      implementation Equatable for Color
        fn `==`(a: Color, b: Color) -> Bool = a == b
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end
