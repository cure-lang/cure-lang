defmodule Cure.Test.ProofSnapshotFixture do
  @moduledoc false

  alias Cure.Core.{Env, Grade, Inductive}

  def environment do
    family = Inductive.family(:Packed, [], [{:A, {:type, 0}}], 1)
    args = [{:A, {:type, 0}}, {:x, {:var, 0}}]
    pack = Inductive.ctor(:Pack, args, [{:var, 1}])
    computed = {:app, {:lam, Grade.unrestricted(), {:type, 0}, {:var, 0}}, {:var, 1}}
    alternate = Inductive.ctor(:Alternate, args, [computed])
    goal = {:data, :"Boundary#Packed", [], [{:atom_type}]}
    value = {:ctor, :"Boundary#Pack", [{:atom_type}, {:atom_lit, :payload}]}

    motive =
      {:lam, Grade.unrestricted(), {:type, 0},
       {:lam, Grade.unrestricted(), {:data, :"Boundary#Packed", [], [{:var, 0}]}, {:var, 1}}}

    program =
      {:case, value, motive, [{:"Boundary#Pack", 2, {:var, 0}}, {:"Boundary#Alternate", 2, {:var, 0}}]}

    Env.empty()
    |> Env.with_owner("Boundary")
    |> Inductive.declare(family, [pack, alternate])
    |> Env.add_def(:packed, goal, value)
    |> Env.add_def(:unpack, {:atom_type}, program)
    |> Env.add_def(:held, {:atom_type}, {:atom_lit, :hidden})
    |> Env.add_def(:answer, {:atom_type}, {:atom_lit, :answer})
    # A finite metadata fixture, not a new semantic totality proof.
    |> Env.certify(:answer)
  end
end
