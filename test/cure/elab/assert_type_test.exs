defmodule Cure.Elab.AssertTypeTest do
  @moduledoc """
  `assert_type expr : T` in the dependent pipeline. It is a compile-time type
  assertion: the elaborator checks `expr` against `T` and the wrapper is erased
  (the emitted code is just `expr`, no runtime cost) — mirroring the classic
  codegen, which strips it. The check runs in CHECKING mode against the lowered
  `T`, so `assert_type` doubles as a local type ascription that can steer
  inference.

  Part of the pre-#18 surface-construct port batch (see
  memory pre18-surface-construct-gaps): every construct the classic codegen
  supports must work through the sole dependent pipeline before classic is ripped
  out, or deleting classic silently removes a live language feature.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Emit, Program}

  test "a well-typed assertion elaborates, erases the wrapper, and runs" do
    src = """
    mod M
      fn f(x: Int) -> Int = assert_type x : Int
    end
    """

    assert {:ok, env} = Program.elaborate(src)

    assert {:ok, mod} =
             Emit.compile_and_load(env, module: :"Cure.Test.AssertOk", functions: [:f])

    assert apply(mod, :f, [7]) == 7
  end

  test "an assertion whose type disagrees with the expression is rejected" do
    src = """
    mod M
      fn f(x: Int) -> Bool = assert_type x : Bool
    end
    """

    assert {:error, _} = Program.elaborate(src)
  end
end
