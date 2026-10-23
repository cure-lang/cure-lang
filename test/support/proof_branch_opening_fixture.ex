defmodule Cure.Test.ProofBranchOpeningFixture do
  @moduledoc false

  alias Cure.Core.{Eval, Grade, Inductive, ProofWire, Quote}
  alias Cure.Test.ProofDataSpineFixture

  def table, do: ProofDataSpineFixture.table() ++ ["Opening#Frame"]

  # Raw operational observations only: fresh fields carry no assumed native
  # type telescope. No arbitrary submitted-program or unbounded omega API.
  def cases do
    atom = {:atom_type}
    g = Grade.unrestricted()
    payload = {:vatom, :payload}
    ambient = [{:vneutral, {:nvar, 0}}]
    identity = {:lam, g, atom, {:var, 0}}
    data = {:data, :"Spine#Indexed", [atom], [{:atom_lit, :payload}]}
    data_value = Eval.eval(data, [])

    [
      {:zero, 0, 0, [payload], {:var, 0}},
      {:one, 0, 1, [], {:var, 0}},
      {:first, 1, 3, ambient, {:var, 2}},
      {:last, 1, 3, ambient, {:var, 0}},
      {:outer, 1, 3, ambient, {:var, 3}},
      {:closure, 0, 2, [payload], {:lam, g, atom, {:app, identity, {:var, 3}}}},
      {:spine, 1, 2, ambient, {:ctor, :"Opening#Frame", [{:var, 1}, {:var, 0}, {:var, 2}]}},
      {:redex, 0, 2, [], {:let, g, atom, {:app, identity, {:var, 1}}, {:var, 0}}},
      {:data, 1, 2, ambient, {:data, :"Spine#Indexed", [atom], [{:var, 1}]}},
      {:capture, 0, 1, [data_value], {:lam, g, atom, {:var, 2}}},
      {:case, 1, 2, ambient, {:case, {:ctor, :"Opening#Frame", [{:var, 1}]}, atom, [{:"Opening#Frame", 1, {:var, 0}}]}}
    ]
  end

  def to_agda do
    names = Enum.map_join(table(), " ∷ ", &inspect/1) <> " ∷ []"
    observations = Enum.map_join(cases(), "\n", &observation/1)

    {:ok,
     """
     {-# OPTIONS --guardedness #-}
     -- Fixed actual Eval.open_branch/Quote observations, not universal refinement.
     module Fixtures.ExecutableBranchOpening where
     open import Data.Bool using (true)
     open import Data.Char using (Char)
     open import Data.List using (List; []; _∷_)
     open import Data.Nat using (ℕ)
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
     """}
  end

  defp observation({key, depth, arity, env, body}) do
    # This fixed lambda exposes the actual captured opening frame without
    # evaluating an arbitrary branch body as a frame-construction oracle.
    probe = {:lam, Grade.unrestricted(), {:atom_type}, {:var, 0}}
    {:vlam, _g, _domain, {:closure, opened, _probe_body}} = Eval.open_branch(env, probe, arity, depth)
    actual = Eval.open_branch(env, body, arity, depth)
    quoted = Quote.reify(actual, depth + arity, ProofDataSpineFixture.environment())
    name = Atom.to_string(key)

    """
    #{name}-depth : ℕ
    #{name}-depth = #{depth}
    #{name}-arity : ℕ
    #{name}-arity = #{arity}
    #{name}-environment : List E.Value
    #{name}-environment = #{values(env)}
    #{name}-opened : List E.Value
    #{name}-opened = #{values(opened)}
    #{name}-body : Term
    #{name}-body = #{term(body)}
    #{name}-value : E.Value
    #{name}-value = #{value(actual)}
    #{name}-quoted : Term
    #{name}-quoted = #{term(quoted)}
    """
  end

  defp term(term) do
    {:ok, chars} = ProofWire.encode_term(term, table())
    ~s|(read-term (toList "#{chars}") refl)|
  end

  defp values([]), do: "[]"
  defp values(values), do: "(" <> Enum.map_join(values, " ∷ ", &value/1) <> " ∷ [])"
  defp value({:vatom_type}), do: "E.v-atom-type"
  defp value({:vatom, name}), do: "(E.v-atom #{inspect(Atom.to_string(name))})"
  defp value({:vneutral, {:nvar, level}}), do: "(E.v-neutral (E.n-var #{level}))"
  defp value({:vctor, name, args}), do: "(E.v-ctor #{inspect(Atom.to_string(name))} #{values(args)})"

  defp value({:vdata, name, args}) do
    %{params: params} = Inductive.get_family(ProofDataSpineFixture.environment(), name)
    {ps, is} = Enum.split(args, length(params))
    "(E.v-data #{inspect(Atom.to_string(name))} #{values(ps)} #{values(is)})"
  end

  defp value({:vlam, grade, domain, {:closure, env, body}}),
    do: "(E.v-lam #{grade} #{value(domain)} #{values(env)} #{term(body)})"
end
