defmodule Cure.Stdlib.ResultTypeTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Program
  alias Cure.Core.Inductive

  # `Result(t, e)` must be a REAL inductive type declared in the stdlib, not an
  # undeclared tag the classic pipeline tolerated. With the declaration present,
  # `Std.Result` elaborates through the dependent pipeline and `Result` is a
  # registered family with `Ok`/`Error` constructors — a user can open
  # `result.cure` and see exactly what a `Result` is.

  test "Std.Result elaborates through the dependent pipeline" do
    src = File.read!("lib/std/result.cure")
    assert {:ok, env} = Program.elaborate(src)
    assert Inductive.get_family(env, :Result)
    assert Inductive.get_ctor(env, :Ok)
    assert Inductive.get_ctor(env, :Error)
  end

  test "a program can construct and match a stdlib Result" do
    src = """
    mod UseResult
      use Std.Result
      fn label(r: Result(Int, Int)) -> Int =
        match r
          Ok(v) -> v
          Error(e) -> e
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end
