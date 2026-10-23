defmodule Cure.Test.ProofNeutralCaseFixture do
  @moduledoc false

  alias Cure.Core.{Env, Eval, Grade, ProofWire, Quote}
  alias Cure.Test.{ProofBundleFixture, ProofResidualNormalFixture, ProofSnapshotFixture}

  # Fixed terminating actual observations. Raw/open metadata is not a typing
  # certificate, and no actual unbounded call is made on omega.
  def cases do
    g = Grade.unrestricted()
    atom = {:atom_type}
    payload = {:atom_lit, :payload}

    %{body: {:case, _packed, motive, branches} = unpack} =
      Env.get_def(ProofSnapshotFixture.environment(), :"Boundary#unpack")

    global = {:global, :"Boundary#packed"}
    opaque = {:case, global, motive, branches}
    data_type = {:data, :"Boundary#Packed", [], [atom]}
    ambient = [{:vneutral, {:nvar, 0}}]
    capture_body = {:let, g, atom, {:var, 2}, {:var, 1}}
    capture_branches = Enum.map(branches, fn {name, ar, _body} -> {name, ar, capture_body} end)

    data_branches =
      Enum.map(branches, fn {name, ar, _body} -> {name, ar, {:data, :"Boundary#Packed", [], [{:var, 1}]}} end)

    shared_case_branches = Enum.map(branches, fn {name, ar, _body} -> {name, ar, unpack} end)
    prefix = Enum.take(ProofResidualNormalFixture.cases(), 3)

    prefix ++
      [
        {:scrutinee, {:case, {:app, {:lam, g, data_type, {:var, 0}}, global}, motive, branches}, [], 0},
        {:open, {:case, {:var, 0}, atom, branches}, ambient, 1},
        {:spine,
         {:case, {:app, {:var, 0}, payload}, atom,
          [{:"Boundary#Pack", 2, {:var, 2}}, {:"Boundary#Alternate", 2, {:var, 2}}]}, ambient, 1},
        {:zero, {:case, global, atom, [{:"Boundary#Pack", 0, payload}]}, [], 0},
        {:multi, {:case, global, atom, [{:"Boundary#Pack", 3, {:lam, g, atom, {:var, 4}}}]}, [{:vatom, :payload}], 0},
        {:capture, {:case, {:let, g, atom, {:atom_lit, :hidden}, global}, motive, capture_branches},
         [{:vatom, :payload}], 0},
        {:data, {:case, global, atom, data_branches}, [], 0},
        {:shared_case, {:case, global, atom, shared_case_branches}, [], 0},
        {:delta, {:case, {:global, :"Boundary#answer"}, atom, [{:"Boundary#Pack", 0, payload}]}, [], 0},
        {:nested_scrutinee, {:case, opaque, atom, branches}, [], 0},
        {:nested_branch, {:case, global, atom, [{:"Boundary#Pack", 2, opaque}]}, [], 0}
      ]
  end

  def to_agda do
    observations = Enum.map_join(cases(), "\n", &observation/1)

    {:ok,
     """
     {-# OPTIONS --guardedness #-}
     -- Fixed actual neutral captures/readbacks, not universal implementation refinement.
     module Fixtures.ExecutableNeutralCase where
     open import Data.Bool using (true)
     open import Data.Char using (Char)
     open import Data.List using (List; []; _∷_)
     open import Data.Nat using (ℕ)
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

  defp observation({key, {:case, _scrutinee, motive, branches} = program, env, depth}) do
    {:vneutral, {:ncase, head, {:closure, ^env, ^motive}, captured_branches}} = actual = Eval.eval(program, env)

    restored =
      Enum.map(captured_branches, fn {name, ar, {:closure, ^env, body}} -> {name, ar, body} end)

    if restored != branches, do: raise("neutral capture changed branch metadata or order")
    quoted = Quote.reify(actual, depth, ProofSnapshotFixture.environment())
    label = key |> Atom.to_string() |> String.replace("_", "-")
    # Nested head syntax is retained as a boundary observation; shared
    # E.Neutral cannot represent it yet, so do not invent a model value.
    captured_head =
      case key do
        :nested_scrutinee -> ""
        _ -> "#{label}-head : E.Neutral\n#{label}-head = #{neutral(head)}\n"
      end

    """
    #{label}-program : Term
    #{label}-program = #{term(program)}
    #{label}-environment : List E.Value
    #{label}-environment = #{values(env)}
    #{label}-captured-environment : List E.Value
    #{label}-captured-environment = #{values(env)}
    #{label}-depth : ℕ
    #{label}-depth = #{depth}
    #{captured_head}#{label}-quoted : Term
    #{label}-quoted = #{term(quoted)}
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
  defp value({:vneutral, head}), do: "(E.v-neutral #{neutral(head)})"
  defp neutral({:nvar, level}), do: "(E.n-var #{level})"
  defp neutral({:nglobal, name}), do: "(E.n-global #{inspect(Atom.to_string(name))})"
  defp neutral({:napp, head, argument}), do: "(E.n-app #{neutral(head)} #{value(argument)})"
end
