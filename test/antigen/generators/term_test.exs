defmodule Antigen.Generators.TermTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.{Term, SigMenu}
  alias Antigen.Backend.StreamData, as: B
  alias Cure.Core.{Context, Kernel, Eval}

  @doc false
  def sample(gen, n), do: B.interp(gen) |> Enum.take(n)

  test "every intro-fragment term checks at its goal (soundness over the fragment)" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)

    for goal <- SigMenu.goal_types() do
      # gen_term's contract is check-at-goal (mode-directed inversion) — a
      # check-mode-only inhabitant (bare param-bearing `Nil`/`Cons` at a List
      # goal) is sound but has no infer path, so assert `check` at the goal value.
      goal_val = Eval.eval(goal, Context.env(ctx))

      for t <- sample(Term.gen_term(ctx, goal), 40) do
        assert Kernel.check(ctx, t, goal_val) == :ok
      end
    end
  end

  test "a Pi goal yields a lambda" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    goal = {:pi, Cure.Core.Grade.unrestricted(), SigMenu.nat(), SigMenu.nat()}
    ts = sample(Term.gen_term(ctx, goal), 40)
    assert Enum.any?(ts, &match?({:lam, _g, _, _}, &1))
    for t <- ts, do: assert({:ok, _} = Kernel.infer(ctx, t))
  end

  test "a Type 0 goal yields a menu type former (the {:type,_} intro row)" do
    # `{:type, 0}` is never drawn as a goal by `Term.typed_term/1`'s `goal_gen`
    # (Task 6) or by `Generators.Context` (Task 2) — see the goal-space note
    # after Task 6 — so this is the ONLY place the `{:type,_}` clause of
    # `intro_rules` (and its var/INDIR-only elimination companions) gets
    # exercised at all. Without this test the clause would ship with zero
    # coverage.
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    goal = {:type, 0}
    ts = sample(Term.gen_term(ctx, goal), 40)
    assert Enum.all?(ts, &(&1 in [SigMenu.nat(), SigMenu.bd(), SigMenu.vec({:ctor, :Z, []})]))
    for t <- ts, do: assert({:ok, _} = Kernel.infer(ctx, t))
  end

  test "generated terms exercise eliminations and firing redexes" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    pairs = for goal <- SigMenu.goal_types(), t <- sample(Term.gen_term(ctx, goal), 80), do: {goal, t}
    ts = Enum.map(pairs, fn {_g, t} -> t end)

    # every term still checks at its goal (soundness across the full rule set);
    # check-at-goal, not infer, since List goals yield check-mode-only inhabitants.
    for {goal, t} <- pairs do
      assert Kernel.check(ctx, t, Eval.eval(goal, Context.env(ctx))) == :ok
    end

    # at least some terms contain an elimination and some fire a redex
    assert Enum.any?(ts, &contains_tag?(&1, :app))
    assert Enum.any?(ts, &contains_tag?(&1, :case))
    assert Enum.any?(ts, fn t -> Kernel.normalize(ctx, t) != t end)
  end

  test "a stuck-indexed Vec goal is satisfied from the context (elimination path)" do
    env = SigMenu.env_of(:v1)
    ctx = SigMenu.rebuild_context(env, [SigMenu.vec({:var, 0}), SigMenu.nat()])
    goal = SigMenu.vec({:var, 1})

    for t <- sample(Term.gen_term(ctx, goal), 40) do
      assert {:ok, _} = Kernel.infer(ctx, t)
    end
  end

  defp contains_tag?(t, tag) when is_tuple(t) do
    elem(t, 0) == tag or t |> Tuple.to_list() |> tl() |> Enum.any?(&contains_tag?(&1, tag))
  end

  defp contains_tag?(l, tag) when is_list(l), do: Enum.any?(l, &contains_tag?(&1, tag))
  defp contains_tag?(_, _), do: false

  test "lazy generation lifts the depth ceiling (terms deeper than the old size-3 cap allowed)" do
    # Under the eager size-3 cap the deepest term observed was structural depth 7.
    # With lazy construction the effective size is much larger, so terms reach
    # well past that — and sampling still completes (no eager-tree explosion),
    # which is the whole point of the laziness change.
    depths =
      for id <- Term.assay_ids(),
          c <- sample(Term.typed_term(id), 200),
          do: term_depth(c.payload.term)

    assert Enum.max(depths) > 10, "deepest term was only #{Enum.max(depths)} — cap not lifted"
  end

  defp term_depth(t) when is_tuple(t) do
    case t |> Tuple.to_list() |> tl() |> Enum.filter(&(is_tuple(&1) or is_list(&1))) |> Enum.map(&term_depth/1) do
      [] -> 0
      xs -> 1 + Enum.max(xs)
    end
  end

  defp term_depth(l) when is_list(l), do: Enum.max([0 | Enum.map(l, &term_depth/1)])
  defp term_depth(_), do: 0

  test "typed_term/1 emits a well-typed :typed_term challenge for its assay id" do
    alias Antigen.Challenge

    for id <- ["term/infer_check", "term/subject_reduction", "term/normalization"] do
      for c <- sample(Term.typed_term(id), 20) do
        assert %Challenge{kind: :typed_term, assay: ^id, label: :well_typed, payload: p} = c
        assert p.sig == :v1
        # the claimed term checks in its rebuilt context
        env = SigMenu.env_of(:v1)
        ctx = SigMenu.rebuild_context(env, p.ctx)
        assert {:ok, _} = Kernel.infer(ctx, p.term)
      end
    end
  end
end
