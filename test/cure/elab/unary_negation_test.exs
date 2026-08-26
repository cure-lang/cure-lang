defmodule Cure.Elab.UnaryNegationTest do
  @moduledoc """
  Unary numeric negation `-x` in the dependent pipeline. The classic codegen
  supports it; the elaborator handled only `not`/`bnot` and dropped `-x` to
  `{:unsupported_expression, …}`. Negation is pure and total — it lowers to the
  existing type-directed builtins `int_neg : Int -> Int` / `float_neg : Float ->
  Float`, chosen by the operand's primitive kind exactly like binary arithmetic.

  Part of the pre-#18 surface-construct port batch (see
  memory pre18-surface-construct-gaps): every construct the classic codegen
  supports must work through the sole dependent pipeline before classic is ripped
  out, or deleting classic silently removes a live language feature.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Emit, Program}

  test "integer negation lowers to int_neg and runs" do
    src = """
    mod M
      fn neg(x: Int) -> Int = -x
    end
    """

    assert {:ok, env} = Program.elaborate(src)

    assert {:ok, mod} =
             Emit.compile_and_load(env, module: :"Cure.Test.IntNeg", functions: [:neg])

    assert apply(mod, :neg, [5]) == -5
    assert apply(mod, :neg, [-3]) == 3
  end

  test "float negation lowers to float_neg and runs" do
    src = """
    mod M
      fn neg(x: Float) -> Float = -x
    end
    """

    assert {:ok, env} = Program.elaborate(src)

    assert {:ok, mod} =
             Emit.compile_and_load(env, module: :"Cure.Test.FloatNeg", functions: [:neg])

    assert apply(mod, :neg, [2.5]) == -2.5
  end

  test "negation of a non-numeric operand is rejected" do
    src = """
    mod M
      fn bad(b: Bool) -> Bool = -b
    end
    """

    assert {:error, _} = Program.elaborate(src)
  end
end
