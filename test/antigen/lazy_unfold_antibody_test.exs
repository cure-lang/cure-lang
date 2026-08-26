defmodule Antigen.LazyUnfoldAntibodyTest do
  @moduledoc """
  A6 antibody — LAZY UNFOLDING at the `Normalise` δ-seam stays sound and
  terminating.

  Guards the change that makes a certified *recursive* global stay FOLDED when
  unfolding it would only re-expose an eliminator that is itself stuck on a
  neutral (Idris/Lean/Agda's "stuck matcher ⇒ keep folded"). Before the fix the
  normalizer eagerly expanded `plus n Z` into `case n {…}`, so the SAME stuck
  recursive call had two shapes (folded in one spine, expanded in another) — a
  δ-inconsistent normal form that broke the elaborator's syntactic
  occurrence-matching and could make conversion δ-loop on open terms.

  This antibody pins the three properties the fix must hold:

    * TERMINATION — `plus n Z` (and nested/`multi`-occurrence variants) normalize
      in bounded fuel and never expand into an ever-deepening case tree;
    * CANONICAL FORM — a stuck recursive call has ONE shape everywhere, so every
      occurrence of `plus n Z` in a goal reifies identically (the rw08 root
      cause);
    * NO DISTINCT-NF COLLAPSE — freezing only makes normal forms MORE distinct:
      it must never equate `plus n Z` with `n` (they are only *propositionally*
      equal — that is exactly why `rewrite` is needed), while genuine ι-progress
      under a *constructor* scrutinee (`plus Z n ≡ n`, `plus (S Z) Z ≡ S Z`) must
      still fire (no over-freezing into incompleteness).
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Conv, Env, Inductive, Normalise}

  @nat {:data, :Nat, [], []}
  @z {:ctor, :Z, []}
  defp s(x), do: {:ctor, :S, [x]}

  # plus(m, n) = match m { Z -> n ; S(k) -> S(plus(k, n)) }
  #
  # Recursive on the FIRST argument, so `plus n Z` (n neutral) is stuck: the
  # scrutinee never becomes a constructor, and unfolding only exposes the inner
  # `case`. This is the canonical function that provoked the rw08 hang.
  defp plus_body do
    z_branch = {:Z, 0, {:var, 0}}
    s_branch = {:S, 1, s({:app, {:app, {:global, :plus}, {:var, 0}}, {:var, 1}})}

    {:lam, Cure.Core.Grade.unrestricted(), @nat,
     {:lam, Cure.Core.Grade.unrestricted(), @nat,
      {:case, {:var, 1}, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}, [z_branch, s_branch]}}}
  end

  defp env do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Nat, [], [], 0), [
      Inductive.ctor(:Z, [], []),
      Inductive.ctor(:S, [{:n, @nat}], [])
    ])
    |> Env.add_def(
      :plus,
      {:pi, Cure.Core.Grade.unrestricted(), @nat, {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}},
      plus_body()
    )
    |> Env.certify(:plus)
  end

  # A context with one Nat variable in scope — `{:var, 0}` is a stuck neutral `n`.
  defp ctx1, do: Context.extend(Context.empty(env()), {:vdata, :Nat, []})
  defp neutral_n, do: {:var, 0}
  defp plus(a, b), do: {:app, {:app, {:global, :plus}, a}, b}

  # Evaluation env/depth for conversion of OPEN terms mentioning `n` (level 0).
  defp open_env, do: [{:vneutral, {:nvar, 0}}]
  defp open_depth, do: 1
  @fuel 1000

  test "termination: plus(n, Z) normalizes to the FOLDED opaque application" do
    # Generous fuel proves this is genuine termination, not fuel-capping: eager
    # expansion would need unbounded fuel to keep unfolding the recursive call.
    folded = plus(neutral_n(), @z)
    assert folded == Normalise.nf(ctx1(), folded, fuel: @fuel)
    assert folded == Normalise.whnf(ctx1(), folded, fuel: @fuel)
  end

  test "termination: nested and multi-occurrence stuck calls normalize in bounded fuel" do
    # plus(plus(n, Z), Z) and plus(n, n): each stays folded (outer scrutinee is a
    # stuck recursive call / a neutral) and completes — never `:fuel_exhausted`.
    assert plus(plus(neutral_n(), @z), @z) ==
             Normalise.nf(ctx1(), plus(plus(neutral_n(), @z), @z), fuel: @fuel)

    assert plus(neutral_n(), neutral_n()) ==
             Normalise.nf(ctx1(), plus(neutral_n(), neutral_n()), fuel: @fuel)
  end

  test "canonical form: different spellings of a stuck call converge to ONE shape" do
    # The rw08/rw09 root cause. `plus(Z, n)` reduces to `n`, so `plus(plus(Z, n), Z)`
    # is a DIFFERENT SPELLING of the stuck call `plus(n, Z)`. Both must normalize to
    # the SAME folded form, so an `Eq` goal carrying both yields structurally
    # IDENTICAL subterms and syntactic occurrence-matching stays uniform.
    folded = plus(neutral_n(), @z)
    assert folded == Normalise.nf(ctx1(), plus(plus(@z, neutral_n()), @z), fuel: @fuel)
    # (The {:eq}-carrier goal assertion retired with the primitive form —
    # group-B removal commit; the Equivalent-carrier twin below pins the same
    # canonicalization property through the goal shape real rewrites use.)
  end

  test "canonical form through the inductive Equivalent carrier (post-retirement twin)" do
    # Phase C twin of the test above (add-then-retire): the `{:eq}` carrier
    # retires with the primitive identity forms; the SAME δ-lazy-unfold
    # canonicalization property is pinned through the inductive
    # `{:data, :Equivalent, …}` goal — the shape real rewrite goals actually
    # normalize as.
    folded = plus(neutral_n(), @z)

    goal =
      {:data, :Equivalent, [@nat], [plus(plus(@z, neutral_n()), @z), plus(neutral_n(), @z)]}

    assert {:data, :Equivalent, ps, is} = Normalise.nf(ctx1(), goal, fuel: @fuel)
    assert [left, right] = Enum.take(ps ++ is, -2)
    assert left == folded
    assert right == folded
  end

  test "no over-freezing: a constructor scrutinee still ι-reduces (completeness)" do
    # plus(Z, n) -> n, and the closed plus(S Z, Z) ≡ S Z, must STILL hold — the
    # freeze fires only on neutral scrutinees, never on constructors.
    assert neutral_n() == Normalise.nf(ctx1(), plus(@z, neutral_n()), fuel: @fuel)
    assert {:ok, true} = Conv.conv_within?(plus(@z, neutral_n()), neutral_n(), open_env(), open_depth(), env(), @fuel)
    assert {:ok, true} = Conv.conv_within?(plus(s(@z), @z), s(@z), [], 0, env(), @fuel)
  end

  test "no distinct-NF collapse: plus(n, Z) is NOT equated with any distinct term" do
    # The soundness control. `plus n Z` and `n` are only PROPOSITIONALLY equal;
    # a bug that equated them definitionally would flip these to {:ok, true}.
    assert {:ok, false} = Conv.conv_within?(plus(neutral_n(), @z), neutral_n(), open_env(), open_depth(), env(), @fuel)

    assert {:ok, false} =
             Conv.conv_within?(plus(neutral_n(), @z), plus(neutral_n(), s(@z)), open_env(), open_depth(), env(), @fuel)
  end

  # f n = match n { Z -> Z ; S k -> match (f k) { Z -> Z ; S m -> Z } }
  # Structurally recursive (certifies), and `f (Sᵈ Z)` reduces to Z. Its scrutinee
  # in the recursive step is `f k` — a recursive call that DOES reduce to a
  # constructor, so `productive_unfold?` fires. This is the shape that must NOT
  # double-whnf: normalization has to stay LINEAR in the constructor depth, not
  # Θ(2ᵈ). Deciding productiveness and firing ι must share ONE whnf of `f k`.
  defp f_env do
    inner_case =
      {:case, {:app, {:global, :f}, {:var, 0}}, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat},
       [{:Z, 0, @z}, {:S, 1, @z}]}

    body =
      {:lam, Cure.Core.Grade.unrestricted(), @nat,
       {:case, {:var, 0}, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}, [{:Z, 0, @z}, {:S, 1, inner_case}]}}

    Env.empty()
    |> Inductive.declare(Inductive.family(:Nat, [], [], 0), [
      Inductive.ctor(:Z, [], []),
      Inductive.ctor(:S, [{:n, @nat}], [])
    ])
    |> Env.add_def(:f, {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}, body)
    |> Env.certify(:f)
  end

  defp nat_lit(0), do: @z
  defp nat_lit(n) when n > 0, do: s(nat_lit(n - 1))

  test "termination: a reducible recursive scrutinee normalizes in LINEAR fuel (no double-whnf blowup)" do
    # Regression guard for the double-evaluation bug: the old `productive_unfold?`
    # whnf-forced `f k` to decide productiveness, then the ι-reduction forced it
    # AGAIN — Θ(2ᵈ). At depth 14 that needs ~2¹⁶ fuel; the fixed single-whnf path
    # needs O(d) (~90). A linear budget of 500 passes the fix and exhausts the bug.
    ctx = Context.empty(f_env())
    term = {:app, {:global, :f}, nat_lit(14)}

    assert @z == Normalise.nf(ctx, term, fuel: 500)
  end

  test "reflexivity terminates: a stuck recursive call is convertible with itself, bounded" do
    # `same_neutral_no_delta?` must short-circuit identical stuck calls before δ,
    # so reflexivity resolves without unfolding the recursion forever.
    assert {:ok, true} =
             Conv.conv_within?(plus(neutral_n(), @z), plus(neutral_n(), @z), open_env(), open_depth(), env(), @fuel)

    assert {:ok, true} =
             Conv.conv_within?(
               plus(plus(neutral_n(), @z), @z),
               plus(plus(neutral_n(), @z), @z),
               open_env(),
               open_depth(),
               env(),
               @fuel
             )
  end
end
