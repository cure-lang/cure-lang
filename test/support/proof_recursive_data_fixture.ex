defmodule Cure.Test.ProofRecursiveDataFixture do
  @moduledoc false

  alias Cure.Core.{Eval, Grade, Inductive, ProofRecipe, ProofWire, Quote}
  alias Cure.Test.ProofDataSpineFixture

  def table, do: ProofDataSpineFixture.table() ++ ["Spine#Box"]

  # Reviewed terminating observations only; the nested/Box terms are RAW
  # operational controls, not all asserted accepted by the native checker.
  def cases do
    g = Grade.unrestricted()
    atom = {:atom_type}
    data = {:data, :"Spine#Indexed", [atom], [{:atom_lit, :payload}]}

    [
      {:canonical, data, [], 0},
      {:nested, {:data, :"Spine#Indexed", [data], [{:atom_lit, :payload}]}, [], 0},
      {:domain, {:lam, g, data, {:var, 0}}, [], 0},
      {:body, {:lam, g, atom, data}, [], 0},
      {:capture, {:let, g, {:type, 1}, data, {:lam, g, atom, {:var, 1}}}, [], 0},
      {:application, {:app, {:lam, g, {:type, 1}, {:var, 0}}, data}, [], 0},
      {:pi, {:pi, g, data, data}, [], 0},
      {:field, {:ctor, :"Spine#Box", [data]}, [], 0},
      {:case, {:case, {:ctor, :"Spine#Box", [data]}, atom, [{:"Spine#Box", 1, {:var, 0}}]}, [], 0},
      {:open, {:data, :"Spine#Indexed", [atom], [{:var, 0}]}, [{:vneutral, {:nvar, 0}}], 1}
    ]
  end

  def checking_request do
    g = Grade.unrestricted()
    data = {:data, :"Spine#Indexed", [{:atom_type}], [{:atom_lit, :payload}]}
    beta = {:app, {:lam, g, {:type, 1}, {:var, 0}}, data}
    kind = {:r_data, [:r_leaf], [:r_leaf]}
    beta_kind = {:r_app, {:r_lam, :r_leaf, :r_leaf}, kind}

    {:checking, {:lam, g, data, {:var, 0}}, {:r_lam, kind, :r_leaf}, {:r_pi, kind, kind}, {:pi, g, beta, beta},
     {:r_pi, beta_kind, beta_kind}}
  end

  def to_agda do
    observations = Enum.map_join(cases(), "\n", &observation/1)
    names = Enum.map_join(table(), " ∷ ", &inspect/1) <> " ∷ []"

    {:ok, checking} = ProofRecipe.encode_checking(checking_request(), ProofDataSpineFixture.table())

    {:ok,
     """
     {-# OPTIONS --guardedness #-}
     -- Actual signature-aware recursive observations, not universal extraction.
     module Fixtures.ExecutableRecursiveData where
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
     -- Checking uses the ORIGINAL checked registry's name table, not the
     -- extra raw Box name used by the observation-only term table above.
     checking-characters : List Char
     checking-characters = toList "#{checking}"
     """}
  end

  defp observation({key, program, env, depth}) do
    actual = Eval.eval(program, env)
    signature = ProofDataSpineFixture.environment()
    quoted = Quote.reify(actual, depth, signature)
    fallback = Quote.reify(actual, depth)
    name = Atom.to_string(key)

    """
    #{name}-program : Term
    #{name}-program = #{term(program)}
    #{name}-environment : List E.Value
    #{name}-environment = #{values(env)}
    #{name}-value : E.Value
    #{name}-value = #{value(actual)}
    #{name}-quoted : Term
    #{name}-quoted = #{term(quoted)}
    #{name}-fallback : Term
    #{name}-fallback = #{term(fallback)}
    """
  end

  defp term(term) do
    {:ok, chars} = ProofWire.encode_term(term, table())
    ~s|(read-term (toList "#{chars}") refl)|
  end

  defp values([]), do: "[]"
  defp values(values), do: "(" <> Enum.map_join(values, " ∷ ", &value/1) <> " ∷ [])"
  defp value({:vtype, level}), do: "(E.v-type l#{level})"
  defp value({:vatom_type}), do: "E.v-atom-type"
  defp value({:vatom, name}), do: "(E.v-atom #{inspect(Atom.to_string(name))})"
  defp value({:vneutral, {:nvar, level}}), do: "(E.v-neutral (E.n-var #{level}))"
  defp value({:vctor, name, args}), do: "(E.v-ctor #{inspect(Atom.to_string(name))} #{values(args)})"

  defp value({:vdata, name, args}) do
    %{params: params} = Inductive.get_family(ProofDataSpineFixture.environment(), name)
    {ps, is} = Enum.split(args, length(params))
    "(E.v-data #{inspect(Atom.to_string(name))} #{values(ps)} #{values(is)})"
  end

  defp value({:vlam, g, domain, {:closure, env, body}}),
    do: "(E.v-lam #{g} #{value(domain)} #{values(env)} #{term(body)})"

  defp value({:vpi, g, domain, {:closure, env, body}}),
    do: "(E.v-pi #{g} #{value(domain)} #{values(env)} #{term(body)})"
end
