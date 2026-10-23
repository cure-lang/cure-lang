defmodule Cure.Test.ProofDataSpineFixture do
  @moduledoc false

  alias Cure.Core.{Env, Eval, Grade, Inductive, ProofRecipe, ProofSnapshot, ProofWire, Quote}

  def table, do: ["", "Spine#Indexed", "Spine#Unknown", "A", "x", "payload"]

  def environment do
    family = Inductive.family(:Indexed, [{:A, {:type, 0}}], [{:x, {:var, 0}}], 1)
    Env.empty() |> Env.with_owner("Spine") |> Inductive.declare(family, [])
  end

  # Fixed terminating observations only; malformed raw splits are controls,
  # not asserted accepted declarations or native typing.
  def cases do
    atom = {:atom_type}
    payload = {:atom_lit, :payload}
    g = Grade.unrestricted()
    identity = {:lam, g, atom, {:var, 0}}
    pi = {:pi, g, atom, atom}

    [
      {:canonical, {:data, :"Spine#Indexed", [atom], [payload]}, [], 0},
      {:redex, {:data, :"Spine#Indexed", [atom], [{:let, g, atom, {:app, identity, payload}, {:var, 0}}]}, [], 0},
      {:parameter, {:data, :"Spine#Indexed", [{:app, {:lam, g, {:type, 0}, {:var, 0}}, atom}], [payload]}, [], 0},
      {:closure, {:data, :"Spine#Indexed", [pi], [{:lam, g, atom, {:app, identity, {:var, 0}}}]}, [], 0},
      {:open, {:data, :"Spine#Indexed", [atom], [{:var, 0}]}, [{:vneutral, {:nvar, 0}}], 1},
      {:short, {:data, :"Spine#Indexed", [atom], []}, [], 0},
      {:extra, {:data, :"Spine#Indexed", [atom], [payload, payload]}, [], 0},
      {:unknown, {:data, :"Spine#Unknown", [atom], [payload]}, [], 0},
      {:forged, {:data, :"Spine#Indexed", [], [atom, payload]}, [], 0},
      {:ill_typed, {:data, :"Spine#Indexed", [atom], [atom]}, [], 0}
    ]
  end

  def to_agda do
    with {:ok, snapshot} <- ProofSnapshot.to_agda(environment(), "Fixtures.ExecutableDataSpine"),
         {:ok, certificate} <-
           ProofRecipe.encode_certificate(
             {:certificate, [{:family_recipe, [:r_leaf], [:r_leaf], []}], []},
             table()
           ) do
      names = Enum.map_join(table(), " ∷ ", &inspect/1) <> " ∷ []"
      observations = Enum.map_join(cases(), "\n", &observation/1)

      {:ok,
       "{-# OPTIONS --guardedness #-}\n" <>
         snapshot <>
         """

         open import Data.Char using (Char)
         open import Data.List using (List)
         open import Data.String.Base using (toList)
         open import Relation.Binary.PropositionalEquality using (_≡_; refl)
         import Core.ClosureEval as E
         import Core.Wire as W
         open import Proof.CheckedAdmissionExamples using (pick)
         open import Core.CheckedAdmission using (present)
         table : List Name
         table = #{names}
         certificate-characters : List Char
         certificate-characters = toList "#{certificate}"
         read-term : (cs : List Char) → present (W.decode-term table cs) ≡ true → Term
         read-term cs = pick (W.decode-term table cs)
         #{observations}
         """}
    end
  end

  defp observation({key, program, env, depth}) do
    {:vdata, name, flat} = Eval.eval(program, env)
    quoted = Quote.reify({:vdata, name, flat}, depth, environment())
    fallback = Quote.reify({:vdata, name, flat}, depth)
    label = key |> Atom.to_string() |> String.replace("_", "-")

    """
    #{label}-program : Term
    #{label}-program = #{term(program)}
    #{label}-flat : List E.Value
    #{label}-flat = #{values(flat)}
    #{label}-quoted : Term
    #{label}-quoted = #{term(quoted)}
    #{label}-fallback : Term
    #{label}-fallback = #{term(fallback)}
    """
  end

  defp term(term) do
    {:ok, characters} = ProofWire.encode_term(term, table())
    ~s|(read-term (toList "#{characters}") refl)|
  end

  defp values([]), do: "[]"
  defp values(values), do: "(" <> Enum.map_join(values, " ∷ ", &value/1) <> " ∷ [])"
  defp value({:vatom_type}), do: "E.v-atom-type"
  defp value({:vatom, name}), do: "(E.v-atom #{inspect(Atom.to_string(name))})"
  defp value({:vneutral, {:nvar, level}}), do: "(E.v-neutral (E.n-var #{level}))"

  defp value({:vlam, g, domain, {:closure, env, body}}),
    do: "(E.v-lam #{g} #{value(domain)} #{values(env)} #{term(body)})"

  defp value({:vpi, g, domain, {:closure, env, body}}),
    do: "(E.v-pi #{g} #{value(domain)} #{values(env)} #{term(body)})"
end
