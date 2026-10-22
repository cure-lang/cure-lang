defmodule Cure.Test.ProofClosureFixture do
  @moduledoc false

  alias Cure.Core.{Eval, Grade, ProofWire, Quote}
  alias Cure.Test.ProofBundleFixture

  # Only these reviewed terminating observations are executed. This module
  # exposes no arbitrary-program evaluator/capture API.
  def cases do
    g = Grade.unrestricted()
    atom = {:atom_type}
    payload = {:atom_lit, :payload}
    identity = {:lam, g, atom, {:var, 0}}
    function_type = {:pi, g, atom, atom}
    domain = {:let, g, {:type, 0}, atom, {:var, 0}}

    [
      {:beta, {:app, identity, payload}, [], 0, atom},
      {:argument, {:app, identity, {:app, identity, payload}}, [], 0, atom},
      {:capture, {:app, {:lam, g, atom, {:lam, g, atom, {:app, identity, {:var, 1}}}}, payload}, [], 0, function_type},
      {:higher, {:app, {:lam, g, function_type, {:app, {:var, 0}, payload}}, identity}, [], 0, atom},
      {:let, {:let, g, atom, {:app, identity, payload}, {:var, 0}}, [], 0, atom},
      {:domain, {:lam, g, domain, {:var, 0}}, [], 0, function_type},
      {:annotation, {:let, g, {:hole, "payload"}, payload, {:var, 0}}, [], 0, atom},
      {:neutral, {:app, {:var, 0}, payload}, [{:vneutral, {:nvar, 0}}], 1, atom},
      {:global, {:global, :"Boundary#answer"}, [], 0, atom},
      {:pi, {:pi, g, domain, atom}, [], 0, {:type, 0}}
    ]
  end

  def to_agda do
    observations = Enum.map_join(cases(), "\n", &observation/1)

    {:ok,
     """
     {-# OPTIONS --guardedness #-}
     -- Reviewed actual Eval/Quote observations, not universal execution refinement.
     module Fixtures.ExecutableClosure where
     open import Data.Bool using (true)
     open import Data.Char using (Char)
     open import Data.List using (List; []; _∷_)
     open import Data.Maybe using (just)
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
     """}
  end

  defp observation({key, program, environment, depth, goal}) do
    # Do not move these calls into a public arbitrary-input API: Eval and
    # closure readback are not known total on untrusted raw terms.
    actual = Eval.eval(program, environment)
    quoted = Quote.reify(actual, depth)
    name = Atom.to_string(key)

    """
    #{name}-program : Term
    #{name}-program = #{term(program)}
    #{name}-environment : List E.Value
    #{name}-environment = #{values(environment)}
    #{name}-value : E.Value
    #{name}-value = #{value(actual)}
    #{name}-quoted : Term
    #{name}-quoted = #{term(quoted)}
    #{name}-goal : Term
    #{name}-goal = #{term(goal)}
    """
  end

  defp term(term) do
    {:ok, characters} = ProofWire.encode_term(term, ProofBundleFixture.table())
    ~s|(read-term (toList "#{characters}") refl)|
  end

  defp values([]), do: "[]"
  defp values(values), do: "(" <> Enum.map_join(values, " ∷ ", &value/1) <> " ∷ [])"
  defp value({:vtype, level}), do: "(E.v-type l#{level})"
  defp value({:vatom_type}), do: "E.v-atom-type"
  defp value({:vatom, name}), do: "(E.v-atom #{inspect(Atom.to_string(name))})"

  defp value({:vlam, g, domain, {:closure, environment, body}}),
    do: "(E.v-lam #{g} #{value(domain)} #{values(environment)} #{term(body)})"

  defp value({:vpi, g, domain, {:closure, environment, body}}),
    do: "(E.v-pi #{g} #{value(domain)} #{values(environment)} #{term(body)})"

  defp value({:vneutral, head}), do: "(E.v-neutral #{neutral(head)})"
  defp neutral({:nvar, level}), do: "(E.n-var #{level})"
  defp neutral({:nglobal, name}), do: "(E.n-global #{inspect(Atom.to_string(name))})"
  defp neutral({:napp, function, argument}), do: "(E.n-app #{neutral(function)} #{value(argument)})"
end
