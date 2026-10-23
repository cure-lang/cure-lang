defmodule Cure.Test.ProofRecursiveCaseFixture do
  @moduledoc false

  alias Cure.Core.{Env, Eval, Grade, ProofWire, Quote}
  alias Cure.Test.{ProofBundleFixture, ProofSnapshotFixture}

  # Fixed terminating corpus only. Unbounded actual Eval never sees omega.
  def cases do
    g = Grade.unrestricted()
    atom = {:atom_type}
    payload = {:atom_lit, :payload}
    packed = {:ctor, :"Boundary#Pack", [atom, payload]}
    %{body: unpack} = Env.get_def(ProofSnapshotFixture.environment(), :"Boundary#unpack")
    {:case, ^packed, motive, branches} = unpack
    inner = {:case, packed, atom, [{:"Boundary#Pack", 2, packed}]}
    identity = {:lam, g, atom, {:var, 0}}
    type_case = type_case()

    [
      {:unpack, unpack, []},
      {:scrutinee, {:case, inner, motive, branches}, []},
      {:body, {:case, packed, atom, [{:"Boundary#Pack", 2, unpack}]}, []},
      {:application, {:app, identity, unpack}, []},
      {:field, {:ctor, :"Boundary#Pack", [atom, unpack]}, []},
      {:lambda, {:lam, g, atom, {:case, {:ctor, :"Boundary#Pack", [atom, {:var, 0}]}, motive, branches}}, []},
      {:pi, {:pi, g, type_case, atom}, []},
      {:type, type_case, []},
      {:capture,
       {:case, packed, atom,
        [
          {:"Boundary#Pack", 2,
           {:lam, g, atom,
            {:case, {:ctor, :"Boundary#Pack", [atom, {:var, 1}]}, atom, [{:"Boundary#Pack", 2, {:var, 0}}]}}}
        ]}, []},
      {:outer,
       {:case, packed, atom,
        [
          {:"Boundary#Pack", 2,
           {:case, {:ctor, :"Boundary#Alternate", [atom, {:var, 0}]}, atom, [{:"Boundary#Alternate", 2, {:var, 4}}]}}
        ]}, [{:vatom, :hidden}]}
    ]
  end

  def type_case do
    g = Grade.unrestricted()
    atom = {:atom_type}
    motive = {:lam, g, {:type, 0}, {:lam, g, {:data, :"Boundary#Packed", [], [{:var, 0}]}, {:type, 0}}}

    {:case, {:ctor, :"Boundary#Pack", [atom, {:atom_lit, :payload}]}, motive,
     [{:"Boundary#Pack", 2, atom}, {:"Boundary#Alternate", 2, atom}]}
  end

  def to_agda do
    observations = Enum.map_join(cases(), "\n", &observation/1)
    g = Grade.unrestricted()
    neutral = {:lam, g, {:atom_type}, {:case, {:var, 0}, {:atom_type}, [{:"Boundary#Pack", 2, {:var, 0}}]}}
    quoted = Quote.reify(Eval.eval(neutral, []), 0)

    {:ok,
     """
     {-# OPTIONS --guardedness #-}
     -- Fixed actual recursive-case observations, not universal correspondence.
     module Fixtures.ExecutableRecursiveCase where
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
     latent-neutral-program : Term
     latent-neutral-program = #{term(neutral)}
     latent-neutral-actual-quoted : Term
     latent-neutral-actual-quoted = #{term(quoted)}
     """}
  end

  defp observation({key, program, env}) do
    actual = Eval.eval(program, env)
    quoted = Quote.reify(actual, 0)
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
    """
  end

  defp term(term) do
    {:ok, chars} = ProofWire.encode_term(term, ProofBundleFixture.table())
    ~s|(read-term (toList "#{chars}") refl)|
  end

  defp values([]), do: "[]"
  defp values(values), do: "(" <> Enum.map_join(values, " ∷ ", &value/1) <> " ∷ [])"
  defp value({:vatom_type}), do: "E.v-atom-type"
  defp value({:vatom, name}), do: "(E.v-atom #{inspect(Atom.to_string(name))})"
  defp value({:vctor, name, fields}), do: "(E.v-ctor #{inspect(Atom.to_string(name))} #{values(fields)})"

  defp value({:vlam, g, domain, {:closure, env, body}}),
    do: "(E.v-lam #{g} #{value(domain)} #{values(env)} #{term(body)})"

  defp value({:vpi, g, domain, {:closure, env, body}}),
    do: "(E.v-pi #{g} #{value(domain)} #{values(env)} #{term(body)})"
end
