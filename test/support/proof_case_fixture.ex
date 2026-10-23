defmodule Cure.Test.ProofCaseFixture do
  @moduledoc false

  alias Cure.Core.{Env, Eval, Grade, ProofWire, Quote}
  alias Cure.Test.{ProofBundleFixture, ProofSnapshotFixture}

  # Fixed terminating observations only; this is not an arbitrary Eval API.
  def cases do
    g = Grade.unrestricted()
    atom = {:atom_type}
    payload = {:atom_lit, :payload}
    identity = {:lam, g, atom, {:var, 0}}
    cname = :"Boundary#Pack"
    args = [atom, payload]
    %{body: unpack} = Env.get_def(ProofSnapshotFixture.environment(), :"Boundary#unpack")

    [
      {:unpack, unpack, []},
      {:last, case_term(args, [{cname, 2, {:var, 0}}]), []},
      {:first, case_term(args, [{cname, 2, {:var, 1}}]), []},
      {:outer, case_term(args, [{cname, 2, {:var, 2}}]), [{:vatom, :hidden}]},
      {:nested, case_term(args, [{cname, 2, {:lam, g, atom, {:app, identity, {:var, 1}}}}]), []},
      {:nested_outer, case_term(args, [{cname, 2, {:lam, g, atom, {:app, identity, {:var, 3}}}}]), [{:vatom, :hidden}]},
      {:zero, case_term([], [{cname, 0, payload}]), []},
      {:redex,
       case_term([atom, {:app, identity, payload}], [
         {cname, 2, {:let, g, atom, {:var, 0}, {:app, identity, {:var, 0}}}}
       ]), []},
      {:duplicate, case_term(args, [{cname, 2, {:var, 1}}, {cname, 2, {:var, 0}}]), []},
      {:skipped, case_term(args, [{:"Boundary#Alternate", 2, {:hole, "payload"}}, {cname, 2, {:var, 0}}]), []},
      {:inert_motive, {:case, {:ctor, cname, args}, {:hole, "payload"}, [{cname, 2, {:var, 0}}]}, []},
      # Actual Eval accepts these layouts; exact-arity MODEL must not.
      {:filtered, case_term([payload, atom, payload], [{cname, 2, {:var, 0}}]), []},
      {:erased, case_term([payload], [{cname, 2, {:var, 0}}]), []}
    ]
  end

  def to_agda do
    observations = Enum.map_join(cases(), "\n", &observation/1)

    {:ok,
     """
     {-# OPTIONS --guardedness #-}
     -- Reviewed actual Eval/Quote results, not universal execution refinement.
     module Fixtures.ExecutableCase where
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
     """}
  end

  defp case_term(args, branches), do: {:case, {:ctor, :"Boundary#Pack", args}, {:atom_type}, branches}

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
  defp value({:vtype, level}), do: "(E.v-type l#{level})"
  defp value({:vatom_type}), do: "E.v-atom-type"
  defp value({:vatom, name}), do: "(E.v-atom #{inspect(Atom.to_string(name))})"

  defp value({:vlam, g, domain, {:closure, environment, body}}),
    do: "(E.v-lam #{g} #{value(domain)} #{values(environment)} #{term(body)})"
end
