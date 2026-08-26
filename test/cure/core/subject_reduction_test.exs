defmodule Cure.Core.SubjectReductionTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{MetaCheck, Context, Builtins, Env}

  # A context whose env seeds the `:int` builtin, needed to type int literals.
  defp seeded_ctx, do: Context.empty(Builtins.seed(Env.empty()))

  # Seed corpus of closed, well-typed, *inferable* terms, each exercising a
  # reduction (or already normal). Grows per wave. Every entry is closed and
  # global-free so it needs no def env. NB: a bare `{:ctor, :mk_pair, …}` (the
  # inductive Sigma intro, D2) is check-only like any parameterised constructor,
  # so Sigma terms are excluded until a later wave adds an inferable eliminator
  # corpus.
  @corpus [
    # beta -> {:int_type}
    {:app, {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}}, {:int_type}},
    # beta -> {:int_lit, 7}
    {:app, {:lam, Cure.Core.Grade.unrestricted(), {:data, :"Std.Int#Int", [], []}, {:var, 0}}, {:int_lit, 7}},
    # already normal
    {:type, 0}
  ]

  test "the harness rejects an ill-typed term (detection works)" do
    # applying a type to a type is ill-typed -> not type-preserved
    refute MetaCheck.type_preserved?(Context.empty(), {:app, {:type, 0}, {:type, 0}})
  end

  test "every corpus term preserves its type under normalization (#638)" do
    for term <- @corpus do
      assert MetaCheck.type_preserved?(seeded_ctx(), term), "not type-preserved: #{inspect(term)}"
    end
  end
end
