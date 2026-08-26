defmodule Cure.Elab.DroppedEffectsRejectedTest do
  @moduledoc """
  Pins the DROP decisions of the pre-#18 surface-construct batch (see
  memory pre18-surface-construct-gaps): the imperative, non-total BEAM effects the
  classic codegen lowered — `throw` and raw `receive`/`spawn` — are NOT ported
  into the dependent pipeline. A total dependent language
  has no unwinding `throw` and no raw process algebra; concurrency is expressed
  through the `fsm`/`actor` families, and `throw` would need monadic structure the
  language does not provide. Each must therefore be REJECTED at elaboration.

  This is a guard, not a feature: it exists so that after the #18 rip-out (which
  deletes the classic pathway that DID implement these) none of them silently
  reappears or starts elaborating. If a future change makes any of these accepted,
  that is a decision to revisit here — not something to slip in unnoticed.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "throw is rejected (no total unwinding escape)" do
    src = """
    mod M
      fn f(x: Int) -> Int = throw x
    end
    """

    assert {:error, reason} = Program.elaborate(src)
    assert inspect(reason) =~ "throw"
  end

  test "raw receive is rejected (use the fsm/actor families)" do
    src = """
    mod M
      fn f() -> Int = receive
        x -> x
    end
    """

    assert {:error, _reason} = Program.elaborate(src)
  end

  test "raw spawn is rejected (use the fsm/actor families)" do
    src = """
    mod M
      fn f() -> Int = spawn(fn() -> 0)
    end
    """

    assert {:error, _reason} = Program.elaborate(src)
  end
end
