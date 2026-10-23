defmodule Cure.Test.ProofComparisonFixture do
  @moduledoc false

  alias Cure.Core.{Conv, Eval, Grade, ProofWire, Quote}
  alias Cure.Test.{ProofBundleFixture, ProofSnapshotFixture}

  # Only reviewed terminating pairs are executed, never arbitrary input.
  def cases do
    g = Grade.unrestricted()
    atom = {:atom_type}
    payload = {:atom_lit, :payload}
    identity = {:lam, g, atom, {:var, 0}}
    beta = {:app, identity, payload}
    beta_type = {:app, {:lam, g, {:type, 0}, {:var, 0}}, atom}
    neutral = [{:vneutral, {:nvar, 0}}]
    data = {:data, :"Boundary#Packed", [], [atom]}

    [
      {:beta, beta, payload, [], 0, false},
      {:zeta, {:let, g, atom, payload, {:var, 0}}, beta, [], 0, false},
      {:lambda, {:lam, g, atom, {:app, identity, {:var, 0}}}, identity, [], 0, false},
      {:pi, {:pi, g, atom, beta_type}, {:pi, g, atom, atom}, [], 0, false},
      {:lambda_grade, {:lam, Grade.one(), atom, {:var, 0}}, identity, [], 0, false},
      {:pi_grade, {:pi, Grade.one(), atom, atom}, {:pi, g, atom, atom}, [], 0, false},
      {:universe, {:type, 0}, {:type, 1}, [], 0, false},
      {:name, payload, {:atom_lit, :hidden}, [], 0, false},
      {:eta, {:lam, g, atom, {:app, {:var, 1}, {:var, 0}}}, {:var, 0}, neutral, 1, false},
      {:domain, {:lam, g, atom, payload}, {:lam, g, {:type, 0}, payload}, [], 0, false},
      {:delta, {:global, :"Boundary#answer"}, {:atom_lit, :answer}, [], 0, true},
      {:data, data, data, [], 0, true}
    ]
  end

  def to_agda do
    observations = Enum.map_join(cases(), "\n", &observation/1)

    {:ok,
     """
     {-# OPTIONS --guardedness #-}
     -- Reviewed actual Conv/Quote observations; not universal conversion refinement.
     module Fixtures.ExecutableComparison where
     open import Data.Bool using (Bool; true; false)
     open import Data.List using (List; []; _∷_)
     open import Data.Nat using (ℕ)
     open import Data.String.Base using (toList)
     open import Relation.Binary.PropositionalEquality using (refl)
     open import Core.Syntax using (Term)
     import Core.ClosureEval as E
     open import Fixtures.ExecutableClosure using (read-term)

     #{observations}
     """}
  end

  defp observation({key, left, right, environment, depth, with_signature}) do
    signature = if with_signature, do: ProofSnapshotFixture.environment()
    actual = Conv.conv?(left, right, environment, depth, signature)
    lq = Quote.reify(Eval.eval(left, environment), depth, signature)
    rq = Quote.reify(Eval.eval(right, environment), depth, signature)
    name = key |> Atom.to_string() |> String.replace("_", "-")

    """
    #{name}-left #{name}-right #{name}-left-quoted #{name}-right-quoted : Term
    #{name}-left = #{term(left)}
    #{name}-right = #{term(right)}
    #{name}-left-quoted = #{term(lq)}
    #{name}-right-quoted = #{term(rq)}
    #{name}-environment : List E.Value
    #{name}-environment = #{environment(environment)}
    #{name}-depth : ℕ
    #{name}-depth = #{depth}
    #{name}-actual #{name}-quoted-equal #{name}-with-signature : Bool
    #{name}-actual = #{actual}
    #{name}-quoted-equal = #{lq == rq}
    #{name}-with-signature = #{with_signature}
    """
  end

  defp term(term) do
    {:ok, chars} = ProofWire.encode_term(term, ProofBundleFixture.table())
    ~s|(read-term (toList "#{chars}") refl)|
  end

  defp environment([]), do: "[]"

  defp environment(values),
    do:
      "(" <>
        Enum.map_join(values, " ∷ ", fn {:vneutral, {:nvar, level}} -> "(E.v-neutral (E.n-var #{level}))" end) <>
        " ∷ [])"
end
