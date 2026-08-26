defmodule Antigen.Generators.ContextTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.SigMenu
  alias Antigen.Backend.StreamData, as: B
  alias Cure.Core.Kernel

  test "every generated telescope is well-formed (each entry checks in its outer prefix)" do
    env = SigMenu.env_of(:v1)
    samples = B.interp(Antigen.Generators.Context.gen(env)) |> Enum.take(50)

    for ctx_types <- samples do
      # Walk outermost-first; each entry's type must be a valid Type in its prefix.
      Enum.reduce(Enum.reverse(ctx_types), Cure.Core.Context.empty(env), fn ty, prefix ->
        assert {:ok, _sort} = Kernel.infer(prefix, ty)
        Cure.Core.Context.extend(prefix, Cure.Core.Eval.eval(ty, Cure.Core.Context.env(prefix)))
      end)
    end
  end

  test "at least some samples exercise a dependent entry (Vec(n) after an n : Nat)" do
    env = SigMenu.env_of(:v1)
    samples = B.interp(Antigen.Generators.Context.gen(env)) |> Enum.take(200)
    assert Enum.any?(samples, fn ctx -> Enum.any?(ctx, &match?({:data, :Vec, _, _}, &1)) end)
  end
end
