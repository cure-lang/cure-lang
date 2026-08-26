defmodule Cure.Elab.JoinLambdaGradeLandmineTest do
  @moduledoc """
  Structural guard for a landmine both round-3 red-team agents flagged: the un-join
  scales a join argument by the continuation lambda's DECLARED grade `lg`
  (`scale(us0, lg)`). Today every `:lam` is `ω` (no surface syntax grades a lambda
  parameter), so this is safe. But if a future slice makes a `{:lam, :erased, …}`
  reachable under a `:let`+`:case`, `mul(:erased, _) = :erased` would annihilate the
  argument's usage while `Erase` still keeps it — an under-rejection.

  There is no surface syntax to produce a restricted lambda grade, so this drives
  `Relevance.check/4` on a hand-built Core term directly. `join_view` must refuse to
  un-join when `lg` is restricted, falling back to the sound generic `:let` path. If
  it did NOT, the linear `v` below (used once via `let x2 = v` AND once via `j(v)` in
  every branch) would have its `j(v)` use annihilated to `:erased` and the two uses
  would combine to `:linear` instead of `:unrestricted` — accepting a double-use.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Env, Inductive}
  alias Cure.Elab.Relevance

  @nat {:data, :Nat, [], []}

  defp nat_env do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Nat, [], [], 0), [
      Inductive.ctor(:Z, [], []),
      Inductive.ctor(:S, [n: @nat], [])
    ])
  end

  # `f(@linear v : Nat)` whose body is:
  #   let x2 = v                          -- v used once (level 0)
  #   let j = (λ z:erased. Z())           -- a continuation that IGNORES z
  #   match x2                            -- (an ungraded Nat scrutinee)
  #     Z()   -> j(v)                     -- v used again
  #     S(_)  -> j(v)                     -- v used again
  # v is genuinely used twice on every path → the linear obligation is violated.
  # de Bruijn (walk starts at depth 1, v at level 0):
  #   let x2=v  binds level 1 (body at depth 2)
  #   let j=λ   binds level 2 (body at depth 3); λ's z is a fresh binder at level 2 in the value
  #   case at depth 3: x2 = {:var,1}; in Z branch (depth 3) j={:var,0}, v={:var,2};
  #                    in S branch (depth 4) j={:var,1}, v={:var,3}
  defp body do
    {:let, :unrestricted, @nat, {:var, 0},
     {:let, :unrestricted, {:pi, :unrestricted, @nat, @nat}, {:lam, :erased, @nat, {:ctor, :Z, []}},
      {:case, {:var, 1}, {:lam, :unrestricted, @nat, @nat},
       [
         {:Z, 0, {:app, {:var, 0}, {:var, 2}}},
         {:S, 1, {:app, {:var, 1}, {:var, 3}}}
       ]}}}
  end

  test "an erased-grade continuation does NOT annihilate a join argument's usage" do
    # With the `lg` guard, `join_view` refuses to un-join (lg = :erased is restricted)
    # and the generic `:let` path ω-scales the whole lambda value, so `v`'s use in
    # `j(v)` is counted and the double-use is rejected.
    assert {:error, {:usage_violation, %{declared: :linear}}} =
             Relevance.check(nat_env(), :f, [:linear], body())
  end
end
