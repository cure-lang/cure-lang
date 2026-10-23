defmodule Cure.Test.ProofScrutineeFixture do
  @moduledoc false

  alias Cure.Core.{Env, Eval, Grade, ProofWire, Quote}
  alias Cure.Test.{ProofBundleFixture, ProofCaseFixture, ProofSnapshotFixture}

  # Only this fixed, reviewed terminating corpus is executed.
  def cases do
    g = Grade.unrestricted()
    atom = {:atom_type}
    payload = {:atom_lit, :payload}
    packed = {:ctor, :"Boundary#Pack", [atom, payload]}
    kind = {:data, :"Boundary#Packed", [], [atom]}
    identity = {:lam, g, atom, {:var, 0}}
    %{body: {:case, ^packed, motive, branches}} = Env.get_def(ProofSnapshotFixture.environment(), :"Boundary#unpack")
    beta = {:app, {:lam, g, atom, {:ctor, :"Boundary#Pack", [atom, {:var, 0}]}}, payload}
    zeta = {:let, g, kind, packed, {:var, 0}}
    eager = {:app, {:lam, g, atom, {:ctor, :"Boundary#Pack", [atom, {:var, 0}]}}, {:app, identity, payload}}
    packed_value = Eval.eval(packed, [])

    [
      {:beta, {:case, beta, motive, branches}, []},
      {:zeta, {:case, zeta, motive, branches}, []},
      {:eager, {:case, eager, motive, branches}, []},
      {:variable, {:case, {:var, 0}, motive, branches}, [packed_value]},
      {:outer, {:case, {:var, 1}, atom, [{:"Boundary#Pack", 2, {:var, 2}}]}, [{:vatom, :hidden}, packed_value]},
      {:capture, {:case, zeta, atom, [{:"Boundary#Pack", 2, {:lam, g, atom, {:app, identity, {:var, 1}}}}]}, []},
      {:nested,
       {:case,
        {:let, g, atom, {:ctor, :"Boundary#Pack", [atom, {:ctor, :"Boundary#Alternate", [atom, payload]}]}, {:var, 0}},
        atom, [{:"Boundary#Pack", 2, {:var, 0}}]}, []},
      {:skipped,
       {:case, zeta, atom, [{:"Boundary#Alternate", 2, {:hole, "payload"}}, {:"Boundary#Pack", 2, {:var, 0}}]}, []},
      {:inert_motive, {:case, zeta, {:hole, "payload"}, [{:"Boundary#Pack", 2, {:var, 0}}]}, []},
      {:zero,
       {:case, {:let, g, atom, {:ctor, :"Boundary#Pack", []}, {:var, 0}}, atom, [{:"Boundary#Pack", 0, payload}]}, []}
    ]
  end

  def to_agda do
    observations = Enum.map_join(cases(), "\n", &observation/1)
    boundaries = Enum.map_join(boundaries(), "\n", &boundary/1)

    {:ok,
     """
     {-# OPTIONS --guardedness #-}
     -- Fixed actual Eval/Quote observations; not universal implementation refinement.
     module Fixtures.ExecutableScrutinee where
     open import Data.Bool using (true)
     open import Data.Char using (Char)
     open import Data.List using (List; []; _∷_)
     open import Data.String.Base using (toList)
     open import Relation.Binary.PropositionalEquality using (_≡_; refl)
     open import Core.Syntax using (Term)
     open import Core.Grade using (erased; linear; affine; unrestricted)
     open import Core.Universe using (l0; l1; l2)
     import Core.ClosureEval as E
     import Core.Wire as W
     import Fixtures.ExecutableBundle as Bundle
     open import Proof.CheckedAdmissionExamples using (pick)
     open import Core.CheckedAdmission using (present)

     read-term : (cs : List Char) → present (W.decode-term Bundle.table cs) ≡ true → Term
     read-term cs = pick (W.decode-term Bundle.table cs)

     #{observations}
     #{boundaries}
     """}
  end

  defp boundaries do
    layouts =
      for key <- [:filtered, :erased] do
        {^key, {:case, scrutinee, motive, branches}, []} =
          Enum.find(ProofCaseFixture.cases(), &(elem(&1, 0) == key))

        computed = {:let, Grade.unrestricted(), {:atom_type}, scrutinee, {:var, 0}}
        {key, {:case, computed, motive, branches}}
      end

    layouts ++
      [{:neutral, {:case, {:global, :"Boundary#packed"}, {:atom_type}, [{:"Boundary#Pack", 2, {:var, 0}}]}}]
  end

  defp boundary({key, program}) do
    quoted = Quote.reify(Eval.eval(program, []), 0)
    name = Atom.to_string(key)

    """
    #{name}-program : Term
    #{name}-program = #{term(program)}
    #{name}-actual-quoted : Term
    #{name}-actual-quoted = #{term(quoted)}
    """
  end

  defp observation({key, program, environment}) do
    actual = Eval.eval(program, environment)
    quoted = Quote.reify(actual, 0)
    name = key |> Atom.to_string() |> String.replace("_", "-")

    """
    #{name}-program : Term
    #{name}-program = #{term(program)}
    #{name}-environment : List E.Value
    #{name}-environment = #{values(environment)}
    #{name}-value : E.Value
    #{name}-value = #{value(actual)}
    #{name}-quoted : Term
    #{name}-quoted = #{term(quoted)}
    """
  end

  defp term(term) do
    {:ok, characters} = ProofWire.encode_term(term, ProofBundleFixture.table())
    ~s|(read-term (toList "#{characters}") refl)|
  end

  defp values([]), do: "[]"
  defp values(values), do: "(" <> Enum.map_join(values, " ∷ ", &value/1) <> " ∷ [])"
  defp value({:vatom_type}), do: "E.v-atom-type"
  defp value({:vatom, name}), do: "(E.v-atom #{inspect(Atom.to_string(name))})"
  defp value({:vctor, name, args}), do: "(E.v-ctor #{inspect(Atom.to_string(name))} #{values(args)})"

  defp value({:vlam, grade, domain, {:closure, env, body}}),
    do: "(E.v-lam #{grade} #{value(domain)} #{values(env)} #{term(body)})"
end
