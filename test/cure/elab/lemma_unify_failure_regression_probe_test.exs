defmodule Cure.Elab.LemmaUnifyFailureRegressionProbeTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.ProofSearch
  alias Cure.Core.{Context, Env, Inductive}

  # A single registered lemma under head Q whose conclusion does NOT unify with
  # the actual goal (index mismatch: lemma proves Q(A()), goal asks for Q(B())).
  # No local/projection candidates exist either. resolve/3 must gracefully
  # decline (:none) — a non-matching lemma is completely ordinary, not an
  # ambiguity.
  defp env_with_mismatched_lemma do
    env = Env.empty()
    idx_family = Inductive.family(:Idx, [], [], 0)
    a_ctor = Inductive.ctor(:A, [], [])
    b_ctor = Inductive.ctor(:B, [], [])
    env = Inductive.declare(env, idx_family, [a_ctor, b_ctor])

    q_family = Inductive.family(:Q, [], [{:explicit, {:data, :Idx, [], []}}], 0)
    q_ctor = Inductive.ctor(:mkQ, [], [{:ctor, :A, []}])
    env = Inductive.declare(env, q_family, [q_ctor])

    pi = {:pi, :omega, {:data, :Q, [], [{:ctor, :A, []}]}, {:data, :Q, [], [{:ctor, :A, []}]}}
    Env.put_lemma(env, :Q, %{name: :identity_on_a, type: pi, arity: 1})
  end

  test "a lemma whose conclusion fails to unify with the goal is a routine decline, not an error" do
    env = env_with_mismatched_lemma()
    ctx = Context.empty(env)
    goal = {:data, :Q, [], [{:ctor, :B, []}]}

    assert :none = ProofSearch.resolve(goal, ctx, env)
  end
end
