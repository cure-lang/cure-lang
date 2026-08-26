defmodule Cure.Elab.LemmaSubgoalAmbiguityProbeTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.ProofSearch
  alias Cure.Core.{Context, Env, Eval, Inductive}

  # Family P (a proof-carrying witness) and Q, with a single lemma `needs_p`
  # that proves Q from a P hypothesis. Two DISTINCT local hypotheses of type P
  # are in scope, so the lemma's OWN sub-goal (P) is itself ambiguous.
  defp env_with_lemma do
    env = Env.empty()
    p_family = Inductive.family(:P, [], [], 0)
    p_ctor = Inductive.ctor(:mkP, [], [])
    env = Inductive.declare(env, p_family, [p_ctor])

    q_family = Inductive.family(:Q, [], [], 0)
    q_ctor = Inductive.ctor(:mkQ, [{:explicit, {:data, :P, [], []}}], [])
    env = Inductive.declare(env, q_family, [q_ctor])

    pi = {:pi, :omega, {:data, :P, [], []}, {:data, :Q, [], []}}
    Env.put_lemma(env, :Q, %{name: :needs_p, type: pi, arity: 1})
  end

  test "an ambiguous SUB-GOAL inside an otherwise-unique lemma application surfaces as ambiguity, not :none" do
    env = env_with_lemma()
    p_val = Eval.eval({:data, :P, [], []}, [])
    # Two local hypotheses `a : P` and `b : P` — the lemma's hypothesis is
    # satisfiable two distinct ways.
    ctx = Context.empty(env) |> Context.extend(p_val) |> Context.extend(p_val)

    goal = {:data, :Q, [], []}

    result = ProofSearch.resolve(goal, ctx, env)

    # The design's discipline (§6) is: "two or more distinct candidate terms →
    # hard ambiguity error naming the competing lemmas/hypotheses" — applied at
    # EVERY resolve/4 call, including recursive sub-goal calls. An ambiguous
    # sub-goal inside the only applicable lemma means there is genuinely no
    # single well-defined proof term for the outer goal either; the ambiguity
    # should be surfaced, not silently downgraded to "no proof found."
    assert {:error, {:ambiguous_proof_search, _subgoal, provenance}} = result
    assert length(provenance) == 2
  end
end
