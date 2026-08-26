defmodule Cure.Core.ProgressTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{MetaCheck, Context, Builtins, Env}

  # A context whose env seeds the `:int` builtin, needed to type int literals.
  defp seeded_ctx, do: Context.empty(Builtins.seed(Env.empty()))

  # Closed, well-typed, inferable terms; each normalizes to a canonical head.
  @corpus [
    # -> {:int_type} (canonical)
    {:app, {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}}, {:int_type}},
    # -> {:int_lit, 7}
    {:app, {:lam, Cure.Core.Grade.unrestricted(), {:data, :"Std.Int#Int", [], []}, {:var, 0}}, {:int_lit, 7}},
    # already canonical (lam head)
    {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}}
  ]

  test "the harness rejects an ill-typed term (detection works)" do
    refute MetaCheck.progresses?(Context.empty(), {:app, {:type, 0}, {:type, 0}})
  end

  test "every closed well-typed corpus term reaches a canonical head (#639)" do
    for term <- @corpus do
      assert MetaCheck.progresses?(seeded_ctx(), term), "stuck / no progress: #{inspect(term)}"
    end
  end
end
