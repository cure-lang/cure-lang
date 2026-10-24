defmodule Cure.Test.ProofResidualQuotationFixture do
  @moduledoc false

  alias Cure.Core.{Eval, Grade, Inductive, ProofWire, Quote}
  alias Cure.Test.{ProofBundleFixture, ProofNeutralCaseFixture, ProofSnapshotFixture}

  # Reviewed terminating observations only. Several wrappers intentionally
  # exercise raw operational syntax, not native typing or actual totality.
  def cases do
    g = Grade.unrestricted()
    atom = {:atom_type}
    payload = {:atom_lit, :payload}
    previous = ProofNeutralCaseFixture.cases()
    [{:opaque, {:case, global, motive, branches} = opaque, [], 0} | _] = previous
    captured = Eval.eval(opaque, [])
    fields = {:ctor, :"Boundary#Pack", [atom, opaque]}
    nested = {:case, opaque, atom, branches}
    packed = {:data, :"Boundary#Packed", [], [atom]}
    motive_domain = {:data, :"Boundary#Packed", [], [{:var, 0}]}
    constant_motive = fn result -> {:lam, g, {:type, 0}, {:lam, g, motive_domain, result}} end
    constant_branches = fn body -> Enum.map(branches, fn {name, ar, _old} -> {name, ar, body} end) end

    packed_case =
      {:case, global, constant_motive.(packed), constant_branches.({:ctor, :"Boundary#Pack", [atom, payload]})}

    previous ++
      [
        {:lam_body, {:lam, g, atom, opaque}, [], 0},
        {:lam_domain, {:lam, g, opaque, {:var, 0}}, [], 0},
        {:pi_body, {:pi, g, atom, opaque}, [], 0},
        {:ctor_field, fields, [], 0},
        {:data_index, {:data, :"Boundary#Packed", [], [opaque]}, [], 0},
        {:neutral_function, {:app, opaque, payload}, [], 0},
        {:neutral_argument, {:app, global, opaque}, [], 0},
        {:beta_argument, {:app, {:lam, g, atom, {:var, 0}}, opaque}, [], 0},
        {:let_capture, {:let, g, atom, opaque, {:lam, g, atom, {:var, 1}}}, [], 0},
        {:environment, {:lam, g, atom, {:var, 1}}, [captured], 0},
        {:fresh_capture, {:case, global, atom, [{:"Boundary#Pack", 3, {:lam, g, atom, {:var, 4}}}]}, [captured], 0},
        {:exact_case, {:case, fields, motive, branches}, [], 0},
        {:nested_motive, {:case, global, opaque, branches}, [], 0},
        {:branch_binder,
         {:case, global, atom,
          [{:"Boundary#Pack", 2, {:lam, g, atom, {:case, {:var, 2}, atom, [{:"Boundary#Pack", 0, {:var, 1}}]}}}]}, [],
         0},
        {:triple, {:case, global, atom, [{:"Boundary#Pack", 2, nested}]}, [], 0},
        {:typed_scrutinee, {:case, packed_case, motive, branches}, [], 0},
        {:typed_branch, {:case, global, constant_motive.(atom), constant_branches.(opaque)}, [], 0}
      ]
  end

  def to_agda do
    observations = Enum.map_join(cases(), "\n", &observation/1)

    {:ok,
     """
     {-# OPTIONS --guardedness #-}
     -- Fixed actual recursive residual observations, not universal extraction.
     module Fixtures.ExecutableResidualQuotation where
     open import Data.Bool using (true)
     open import Data.Char using (Char)
     open import Data.List using (List; []; _∷_)
     open import Data.Nat using (ℕ)
     open import Data.String.Base using (toList)
     open import Relation.Binary.PropositionalEquality using (_≡_; refl)
     open import Core.Syntax using (Term; Branch)
     open import Core.Grade using (erased; linear; affine; unrestricted)
     open import Core.Universe using (l0; l1; l2)
     import Core.ClosureEval as E
     import Core.Wire as W
     import Fixtures.ExecutableBundle as Bundle
     open import Proof.CheckedAdmissionExamples using (pick)
     open import Core.CheckedAdmission using (present)
     read-term : (cs : List Char) → present (W.decode-term Bundle.table cs) ≡ true → Term
     read-term cs = pick (W.decode-term Bundle.table cs)
     branches-of : Term → List Branch
     branches-of (Core.Syntax.tm-case s m branches) = branches
     branches-of other = []
     #{observations}
     """}
  end

  defp observation({key, program, env, depth}) do
    actual = Eval.eval(program, env)
    quoted = Quote.reify(actual, depth, ProofSnapshotFixture.environment())
    name = key |> Atom.to_string() |> String.replace("_", "-")

    """
    #{name}-program : Term
    #{name}-program = #{term(program)}
    #{name}-environment : List E.Value
    #{name}-environment = #{values(env)}
    #{name}-depth : ℕ
    #{name}-depth = #{depth}
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
  defp value({:vtype, level}), do: "(E.v-type l#{level})"
  defp value({:vatom_type}), do: "E.v-atom-type"
  defp value({:vatom, name}), do: "(E.v-atom #{inspect(Atom.to_string(name))})"
  defp value({:vneutral, head}), do: "(E.v-neutral #{neutral(head)})"
  defp value({:vctor, name, args}), do: "(E.v-ctor #{inspect(Atom.to_string(name))} #{values(args)})"

  defp value({:vdata, name, args}) do
    %{params: params} = Inductive.get_family(ProofSnapshotFixture.environment(), name)
    {ps, is} = Enum.split(args, length(params))
    "(E.v-data #{inspect(Atom.to_string(name))} #{values(ps)} #{values(is)})"
  end

  defp value({:vlam, g, domain, {:closure, env, body}}),
    do: "(E.v-lam #{g} #{value(domain)} #{values(env)} #{term(body)})"

  defp value({:vpi, g, domain, {:closure, env, body}}),
    do: "(E.v-pi #{g} #{value(domain)} #{values(env)} #{term(body)})"

  defp neutral({:nvar, level}), do: "(E.n-var #{level})"
  defp neutral({:nglobal, name}), do: "(E.n-global #{inspect(Atom.to_string(name))})"
  defp neutral({:napp, head, argument}), do: "(E.n-app #{neutral(head)} #{value(argument)})"

  defp neutral({:ncase, head, {:closure, env, motive}, branches}) do
    # Verify every actual closure captures the SAME caller, recursively.
    restored = Enum.map(branches, fn {name, ar, {:closure, ^env, body}} -> {name, ar, body} end)
    source = {:case, {:global, :"Boundary#packed"}, motive, restored}
    "(E.n-case #{neutral(head)} #{values(env)} #{term(motive)} (branches-of #{term(source)}))"
  end
end
