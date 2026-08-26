defmodule Cure.Core.IntFamilyTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Builtins, Env, Inductive}

  test "seed registers the Int inductive family with FromNat/NegativeSuccessor" do
    env = Builtins.seed(Env.empty())
    fid = Inductive.builtin(env, :int)
    assert fid != nil
    assert :ok == Builtins.validate!(env, :int, fid)

    names =
      env
      |> Inductive.ctors_of(fid)
      |> Enum.map(fn c -> Cure.Elab.Name.base(c.name) end)
      |> Enum.sort()

    assert names == ["FromNat", "NegativeSuccessor"]
  end
end
