defmodule Cure.Test.ProofQuotationFixture do
  @moduledoc false

  alias Cure.Core.{Eval, Grade, ProofWire, Quote}
  alias Cure.Test.ProofBundleFixture

  # Reviewed terminating observations only. No arbitrary-input Eval/Quote API.
  def cases do
    g = Grade.unrestricted()
    atom = {:atom_type}
    identity = {:lam, g, atom, {:var, 0}}
    function = {:pi, g, atom, atom}
    neutral = {:vneutral, {:nvar, 0}}
    domain = {:pi, g, atom, {:let, g, {:type, 0}, atom, {:var, 0}}}

    dependent =
      {:lam, g, {:type, 0}, {:lam, g, {:var, 0}, {:app, {:lam, g, {:var, 1}, {:var, 0}}, {:var, 0}}}}

    [
      {:dependent, dependent, [], 0, {:pi, g, {:type, 0}, {:pi, g, {:var, 0}, {:var, 1}}}},
      {:argument, {:app, {:var, 0}, {:lam, g, atom, {:app, identity, {:var, 0}}}}, [neutral], 1, atom},
      {:domain, {:lam, g, domain, {:var, 0}}, [], 0, {:pi, g, function, function}},
      {:global, {:lam, g, atom, {:global, :"Boundary#answer"}}, [], 0, function},
      {:eta, {:lam, g, atom, {:app, {:var, 1}, {:var, 0}}}, [neutral], 1, function}
    ]
  end

  def to_agda do
    observations = Enum.map_join(cases(), "\n", &observation/1)

    {:ok,
     """
     {-# OPTIONS --guardedness #-}
     -- Reviewed current Quote observations, not universal implementation refinement.
     module Fixtures.ExecutableQuotation where
     open import Data.List using (List; []; _∷_)
     open import Data.String.Base using (toList)
     open import Relation.Binary.PropositionalEquality using (refl)
     open import Core.Syntax using (Term)
     open import Core.Grade using (erased; linear; affine; unrestricted)
     open import Core.Universe using (l0; l1; l2)
     import Core.ClosureEval as E
     open import Fixtures.ExecutableClosure using (read-term)

     #{observations}
     """}
  end

  defp observation({key, program, environment, depth, goal}) do
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

  defp value({:vlam, g, domain, {:closure, env, body}}),
    do: "(E.v-lam #{g} #{value(domain)} #{values(env)} #{term(body)})"

  defp value({:vpi, g, domain, {:closure, env, body}}),
    do: "(E.v-pi #{g} #{value(domain)} #{values(env)} #{term(body)})"

  defp value({:vneutral, head}), do: "(E.v-neutral #{neutral(head)})"
  defp neutral({:nvar, level}), do: "(E.n-var #{level})"
  defp neutral({:nglobal, name}), do: "(E.n-global #{inspect(Atom.to_string(name))})"
  defp neutral({:napp, function, argument}), do: "(E.n-app #{neutral(function)} #{value(argument)})"
end
