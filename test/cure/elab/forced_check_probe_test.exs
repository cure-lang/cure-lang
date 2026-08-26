defmodule Cure.Elab.ForcedCheckProbeTest do
  @moduledoc """
  Red→green for the public forced-check shim `Elaborator.forced_check_probe/7`,
  factored so the Antigen `forcing/dot` vertical (#24) can drive the exact
  forced-annotation check (named_implicit_forced_value + Conv.conv?) with a
  correct-by-construction (telescope-position, subst, written value).
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Context, Eval, Kernel}
  alias Cure.Elab.Elaborator
  alias Antigen.Generators.SigMenu

  @z {:ctor, :Z, []}
  defp s(t), do: {:ctor, :S, [t]}

  defp setup do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    # scrutinee Vec (S Z): vcons's result index S(var2) unifies var2 := Z,
    # so the forced value d pinned at telescope position of `n` is Z.
    idx = [Eval.eval(s(@z), Context.env(ctx))]
    {:solved, subst} = Kernel.branch_unify(ctx, :Vec, :vcons, idx)
    {env, ctx, subst}
  end

  test "accept: written value syntactically equals the forced value" do
    {env, ctx, subst} = setup()
    assert Elaborator.forced_check_probe(env, ctx, :vcons, [], subst, "n", @z) == :ok
  end

  test "reject: written value is a rigidly-distinct constructor" do
    {env, ctx, subst} = setup()

    assert {:forced_pattern_mismatch, _t, _d} =
             Elaborator.forced_check_probe(env, ctx, :vcons, [], subst, "n", s(@z))
  end

  test "unforced: the named position is not a pinned index" do
    {env, ctx, subst} = setup()
    # `x` is a regular (non-index) field — not in the branch-unify subst.
    assert {:named_implicit_unforced, "x"} =
             Elaborator.forced_check_probe(env, ctx, :vcons, [], subst, "x", @z)
  end
end
