defmodule Cure.Elab.EmitEmptyCaseTest do
  # K4 §H: ex-falso is an empty-branch `{:case, scrut, motive, []}` — the
  # scrutinee's type is provably uninhabited, so the point is unreachable. Emit
  # must lower it to a crash stub, NOT an invalid 0-clause Erlang `case X of end`
  # (which the Erlang compiler rejects).
  use ExUnit.Case, async: true
  alias Cure.Core.Env
  alias Cure.Elab.Emit

  test "an empty-branch (ex-falso) case compiles to an unreachable stub" do
    body = {:case, {:int_lit, 0}, {:type, 0}, []}
    env = Env.empty() |> Env.add_def(:exf, {:type, 0}, body, [])
    assert {:ok, _mod} = Emit.compile_and_load(env, module: :K4EmptyCaseEmitTest, functions: [:exf])
  end
end
