defmodule Cure.Test.ProofConstructorFixture do
  @moduledoc false

  alias Cure.Core.{Eval, Grade, ProofWire, Quote}
  alias Cure.Test.{ProofBundleFixture, ProofSnapshotFixture}

  def table, do: ProofBundleFixture.table() ++ ["First"]

  # Fixed, reviewed terminating observations only. No submitted-program API.
  def cases do
    g = Grade.unrestricted()
    atom = {:atom_type}
    payload = {:atom_lit, :payload}
    identity = {:lam, g, atom, {:var, 0}}
    packed = {:ctor, :"Boundary#Pack", [atom, payload]}
    goal = {:data, :"Boundary#Packed", [], [atom]}
    field = {:let, g, atom, {:app, identity, payload}, {:var, 0}}

    [
      {:packed, packed, [], 0},
      {:redex, {:ctor, :"Boundary#Pack", [atom, field]}, [], 0},
      {:nested, {:ctor, :"Boundary#Pack", [atom, {:ctor, :"Boundary#Alternate", [atom, payload]}]}, [], 0},
      {:field_closure, {:ctor, :"Boundary#Pack", [{:lam, g, atom, {:app, identity, {:var, 0}}}]}, [], 0},
      {:captured, {:let, g, goal, packed, {:lam, g, atom, {:var, 1}}}, [], 0},
      {:under_binder, {:lam, g, atom, {:ctor, :"Boundary#Pack", [atom, {:var, 0}]}}, [], 0},
      {:open, {:ctor, :"Boundary#Pack", [atom, {:var, 0}]}, [{:vneutral, {:nvar, 0}}], 1},
      {:global_field, {:ctor, :"Boundary#Pack", [atom, {:global, :"Boundary#answer"}]}, [], 0},
      {:case_tree,
       {:case, packed, atom,
        [{:"Boundary#Pack", 2, {:ctor, :"Boundary#Pack", [atom, {:ctor, :"Boundary#Alternate", [atom, {:var, 0}]}]}}]},
       [], 0},
      {:case_field,
       {:case, {:ctor, :"Boundary#Pack", [atom, {:ctor, :"Boundary#Alternate", [atom, payload]}]}, atom,
        [{:"Boundary#Pack", 2, {:var, 0}}]}, [], 0}
    ]
  end

  def to_agda do
    observations = Enum.map_join(cases(), "\n", &observation/1)
    names = Enum.map_join(table(), " ∷ ", &inspect/1) <> " ∷ []"
    atom = {:atom_type}
    data = {:data, :"Boundary#Packed", [], [atom]}
    data_value = Eval.eval(data, [])
    # This RAW compaction control is not asserted well typed: actual First
    # compacts its erased bound without inspecting the bound's value shape.
    first = {:ctor, :First, [atom]}
    compact = Quote.reify(Eval.eval(first, []), 0)
    flat = Quote.reify(data_value, 0)
    split = Quote.reify(data_value, 0, ProofSnapshotFixture.environment())

    {:ok,
     """
     {-# OPTIONS --guardedness #-}
     -- Fixed actual observations, not universal Eval/Quote correspondence.
     module Fixtures.ExecutableConstructor where
     open import Data.Bool using (true)
     open import Data.Char using (Char)
     open import Data.List using (List; []; _∷_)
     open import Data.String.Base using (toList)
     open import Relation.Binary.PropositionalEquality using (_≡_; refl)
     open import Core.Syntax using (Name; Term)
     open import Core.Grade using (erased; linear; affine; unrestricted)
     open import Core.Universe using (l0; l1; l2)
     import Core.ClosureEval as E
     import Core.Wire as W
     open import Proof.CheckedAdmissionExamples using (pick)
     open import Core.CheckedAdmission using (present)

     table : List Name
     table = #{names}
     read-term : (cs : List Char) → present (W.decode-term table cs) ≡ true → Term
     read-term cs = pick (W.decode-term table cs)

     #{observations}
     compact-program : Term
     compact-program = #{term(first)}
     compact-actual-quoted : Term
     compact-actual-quoted = #{term(compact)}
     data-program : Term
     data-program = #{term(data)}
     data-flat-quoted : Term
     data-flat-quoted = #{term(flat)}
     data-split-quoted : Term
     data-split-quoted = #{term(split)}
     """}
  end

  defp observation({key, program, environment, depth}) do
    actual = Eval.eval(program, environment)
    quoted = Quote.reify(actual, depth)
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
    {:ok, characters} = ProofWire.encode_term(term, table())
    ~s|(read-term (toList "#{characters}") refl)|
  end

  defp values([]), do: "[]"
  defp values(values), do: "(" <> Enum.map_join(values, " ∷ ", &value/1) <> " ∷ [])"
  defp value({:vtype, level}), do: "(E.v-type l#{level})"
  defp value({:vatom_type}), do: "E.v-atom-type"
  defp value({:vatom, name}), do: "(E.v-atom #{inspect(Atom.to_string(name))})"
  defp value({:vctor, name, fields}), do: "(E.v-ctor #{inspect(Atom.to_string(name))} #{values(fields)})"

  defp value({:vlam, g, domain, {:closure, environment, body}}),
    do: "(E.v-lam #{g} #{value(domain)} #{values(environment)} #{term(body)})"

  defp value({:vneutral, {:nvar, level}}), do: "(E.v-neutral (E.n-var #{level}))"
  defp value({:vneutral, {:nglobal, name}}), do: "(E.v-neutral (E.n-global #{inspect(Atom.to_string(name))}))"
end
