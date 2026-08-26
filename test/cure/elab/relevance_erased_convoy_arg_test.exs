defmodule Cure.Elab.RelevanceErasedConvoyArgTest do
  @moduledoc """
  Robustness: an ERASED implicit used RELEVANTLY inside a present-position argument
  of a `match`/`rewrite` convoy must be REJECTED CLEANLY, not crash.

  `Relevance.walk_convoy_branches/4` computed each convoy argument's usage with a
  hard `{:ok, ua} = walk(arg, …, :present_arg, …)` match. When `arg` relevantly uses
  an erased binder — e.g. `orb_r({x}, {y}, py) = rewrite py in orb_t_r(x)`, where the
  erased `x` is passed to the present-position call `orb_t_r(x)` under the `rewrite`'s
  case convoy — `walk` correctly returns `{:error, :erased_used_relevantly}`, but the
  hard match raised a `MatchError` instead of surfacing the type error. Now the
  per-argument walk propagates the error.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "erased implicit used relevantly under a rewrite convoy is a clean error, not a crash" do
    src = """
    mod Crash
      type B = F | T
      fn orb(x: B, y: B) -> B = match x
        F() -> y
        T() -> T
      fn orb_t_r(x: B) -> Equivalent(B, orb(x, T), T) = match x
        F() -> reflexive(T)
        T() -> reflexive(T)
      fn orb_r({x: B}, {y: B}, py: Equivalent(B, y, T)) -> Equivalent(B, orb(x, y), T) = rewrite py in orb_t_r(x)
    end
    """

    assert {:error, {:erased_used_relevantly, _}} = Program.semantic_result(Program.elaborate(src))
  end

  test "the same helper with an EXPLICIT operand elaborates (the fix is behaviour-preserving)" do
    src = """
    mod Ok
      type B = F | T
      fn orb(x: B, y: B) -> B = match x
        F() -> y
        T() -> T
      fn orb_t_r(x: B) -> Equivalent(B, orb(x, T), T) = match x
        F() -> reflexive(T)
        T() -> reflexive(T)
      fn orb_r(x: B, {y: B}, py: Equivalent(B, y, T)) -> Equivalent(B, orb(x, y), T) = rewrite py in orb_t_r(x)
    end
    """

    assert {:ok, _} = Program.semantic_result(Program.elaborate(src))
  end
end
