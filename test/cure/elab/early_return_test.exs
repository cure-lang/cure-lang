defmodule Cure.Elab.EarlyReturnTest do
  @moduledoc """
  `return e` in the dependent pipeline. The classic codegen implemented it with
  `throw({:cure_return, e})` + a wrapping `try/catch` — an imperative, non-total
  unwind. That escape mechanism is dropped (it needs the same monadic/exception
  structure as `throw`, which the total dependent language does not provide). What
  survives is the STRUCTURED, checked meaning: in tail position `return e` is
  simply `e` — the value of the enclosing function or branch — so it elaborates as
  the identity on `e`, carrying `e`'s type, with no runtime wrapper.

  Part of the pre-#18 surface-construct port batch (see
  memory pre18-surface-construct-gaps): every construct the classic codegen
  supports must work through the sole dependent pipeline before classic is ripped
  out, or deleting classic silently removes a live language feature.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Emit, Program}

  test "return at the function tail is the identity on its expression" do
    src = """
    mod M
      fn f(x: Int) -> Int = return x + 1
    end
    """

    assert {:ok, env} = Program.elaborate(src)

    assert {:ok, mod} =
             Emit.compile_and_load(env, module: :"Cure.Test.RetTail", functions: [:f])

    assert apply(mod, :f, [5]) == 6
  end

  test "return in each branch tail of a conditional" do
    src = """
    mod M
      fn g(x: Int) -> Int = if x > 0 then return 1 else return 0
    end
    """

    assert {:ok, env} = Program.elaborate(src)

    assert {:ok, mod} =
             Emit.compile_and_load(env, module: :"Cure.Test.RetBranch", functions: [:g])

    assert apply(mod, :g, [3]) == 1
    assert apply(mod, :g, [-1]) == 0
  end
end
