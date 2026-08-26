defmodule Cure.Elab.MatchArmFunctionCallCheckingTest do
  @moduledoc """
  A `match`/`case` arm whose body is a call to a polymorphic global FUNCTION
  (not a constructor) must be checked against the branch's expected type, so the
  function's result type variable is solved from the goal.

  `elaborate_branch_body/5` already infers-then-retries-in-checking-mode for a
  CONSTRUCTOR arm body (an unsolved erased index is pinned from the goal), but
  the catch-all for an ordinary function call was infer-ONLY. So
  `match xs | [] -> nothing() | ...` where `nothing() -> Option(t)` left `t`
  unsolved and failed `{:unsolved_metavariables, :nothing}`, even though the
  match's expected type (`Option(Int)`) determines it. Idris checks arm bodies
  against the match's expected type; Cure now mirrors the constructor-arm path.

  This is the blocker that kept `Std.Iter` off the dependent pipeline
  (`cycle`'s `[] -> empty()` arm, `empty() -> Iter(t)`).
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "a polymorphic function call in a match arm is pinned by the match's expected type" do
    src = """
    mod M
      use Std.Option
      fn nothing() -> Option(t) = None()
      fn pick(list: List(Int)) -> Option(Int) =
        match list
          []      -> nothing()
          [x | _] -> Some(x)
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end
