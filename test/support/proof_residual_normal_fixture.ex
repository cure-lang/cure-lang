defmodule Cure.Test.ProofResidualNormalFixture do
  @moduledoc false

  alias Cure.Core.{Env, Eval, Grade, ProofWire, Quote}
  alias Cure.Test.{ProofBundleFixture, ProofSnapshotFixture}

  # Fixed terminating observations only. The checker does not evaluate
  # submitted syntax, and unbounded actual Eval is never called on omega.
  def cases do
    g = Grade.unrestricted()
    atom = {:atom_type}
    %{body: {:case, _packed, motive, branches}} = Env.get_def(ProofSnapshotFixture.environment(), :"Boundary#unpack")
    opaque = {:case, {:global, :"Boundary#packed"}, motive, branches}
    [{pack_name, 2, _body}, alternate] = branches
    branch = {pack_name, 2, {:app, {:lam, g, {:var, 1}, {:var, 0}}, {:var, 0}}}
    motive_type = {:pi, g, {:type, 0}, {:pi, g, {:data, :"Boundary#Packed", [], [{:var, 0}]}, {:type, 0}}}

    [
      {:opaque, opaque, [], 0},
      {:branch, {:case, {:global, :"Boundary#packed"}, motive, [branch, alternate]}, [], 0},
      {:motive, {:case, {:global, :"Boundary#packed"}, {:let, g, motive_type, motive, {:var, 0}}, branches}, [], 0},
      {:nested, {:case, opaque, atom, branches}, [], 0},
      {:lambda, {:lam, g, atom, opaque}, [], 0},
      {:ctor, {:ctor, :"Boundary#Pack", [atom, opaque]}, [], 0},
      {:data, {:data, :"Boundary#Packed", [], [opaque]}, [], 0},
      {:open, {:case, {:var, 0}, atom, branches}, [{:vneutral, {:nvar, 0}}], 1},
      {:delta, {:global, :"Boundary#answer"}, [], 0},
      {:beta, {:app, {:lam, g, atom, {:var, 0}}, {:atom_lit, :payload}}, [], 0}
    ]
  end

  def to_agda do
    observations = Enum.map_join(cases(), "\n", &observation/1)

    {:ok,
     """
     {-# OPTIONS --guardedness #-}
     -- Fixed actual residual Quote observations, not universal execution refinement.
     module Fixtures.ExecutableResidualNormal where
     open import Data.Bool using (true)
     open import Data.Char using (Char)
     open import Data.List using (List; []; _∷_)
     open import Data.String.Base using (toList)
     open import Relation.Binary.PropositionalEquality using (_≡_; refl)
     open import Core.Syntax using (Term)
     import Core.Wire as W
     import Fixtures.ExecutableBundle as Bundle
     open import Proof.CheckedAdmissionExamples using (pick)
     open import Core.CheckedAdmission using (present)
     read-term : (cs : List Char) → present (W.decode-term Bundle.table cs) ≡ true → Term
     read-term cs = pick (W.decode-term Bundle.table cs)
     #{observations}
     """}
  end

  defp observation({key, program, env, depth}) do
    quoted = Quote.reify(Eval.eval(program, env), depth, ProofSnapshotFixture.environment())
    name = Atom.to_string(key)

    """
    #{name}-program : Term
    #{name}-program = #{term(program)}
    #{name}-quoted : Term
    #{name}-quoted = #{term(quoted)}
    """
  end

  defp term(term) do
    {:ok, chars} = ProofWire.encode_term(term, ProofBundleFixture.table())
    ~s|(read-term (toList "#{chars}") refl)|
  end
end
