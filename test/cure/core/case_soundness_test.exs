defmodule Cure.Core.CaseSoundnessTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive, Kernel}

  @dec {:data, :Dec, [], []}

  test "a case branch naming a constructor of a foreign family is rejected" do
    env =
      Env.empty()
      |> Inductive.declare(
        Inductive.family(:Dec, [], [], 0),
        [Inductive.ctor(:Dcoupled, [], []), Inductive.ctor(:Causal, [], [])]
      )
      |> Inductive.declare(Inductive.family(:Foo, [], [], 0), [Inductive.ctor(:MkFoo, [], [])])
      |> Env.add_def(
        :probe,
        @dec,
        {:case, {:ctor, :Causal, []}, {:lam, Cure.Core.Grade.unrestricted(), @dec, @dec},
         [
           {:Dcoupled, 0, {:ctor, :Causal, []}},
           {:Causal, 0, {:ctor, :Dcoupled, []}},
           {:MkFoo, 0, {:ctor, :Dcoupled, []}}
         ]}
      )

    assert {:error, _} = Kernel.check_def(env, :probe)
  end
end
