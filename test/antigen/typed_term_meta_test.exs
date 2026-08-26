defmodule Antigen.TypedTermMetaTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.{Term, SigMenu}
  alias Antigen.{Runner, Corpus, Challenge}
  alias Antigen.Backend.StreamData, as: B
  alias Cure.Core.{Context, Kernel}

  test "generator soundness: a fixed sample all checks at its claimed type" do
    for id <- Term.assay_ids() do
      for c <- B.interp(Term.typed_term(id)) |> Enum.take(50) do
        env = SigMenu.env_of(:v1)
        ctx = SigMenu.rebuild_context(env, c.payload.ctx)

        assert {:ok, _} = Kernel.infer(ctx, c.payload.term),
               "unsound generated term for #{id}: #{inspect(c.payload.term)}"
      end
    end
  end

  test "canonical-fallback totality over a fixed goal matrix" do
    env = SigMenu.env_of(:v1)
    empty = Context.empty(env)
    stuck_ctx = SigMenu.rebuild_context(env, [SigMenu.vec({:var, 0}), SigMenu.nat()])

    goals = [
      {empty, SigMenu.nat()},
      {empty, SigMenu.bd()},
      {empty, SigMenu.vec({:ctor, :Z, []})},
      {empty, SigMenu.vec({:ctor, :S, [{:ctor, :Z, []}]})},
      {empty, {:pi, Cure.Core.Grade.unrestricted(), SigMenu.nat(), SigMenu.nat()}},
      {stuck_ctx, SigMenu.vec({:var, 1})}
    ]

    for {ctx, g} <- goals do
      assert SigMenu.inhabitable?(ctx, g)
      assert {:ok, _} = Kernel.infer(ctx, SigMenu.canon(ctx, g))
    end
  end

  @seeds_path "test/antigen/seeds.sexp"
  test "banked :typed_term seed corpus meets the health floors (static replay)" do
    if File.exists?(@seeds_path) do
      banked =
        Corpus.stream(@seeds_path)
        |> Enum.flat_map(fn
          {:ok, %Challenge{kind: :typed_term} = c} -> [c]
          _ -> []
        end)

      if banked != [] do
        m = Runner.health_metrics(banked)
        assert m.binder_usage >= 0.60, "banked binder-usage #{m.binder_usage} below floor"
        assert m.reduction_activity >= 0.25, "banked reduction-activity #{m.reduction_activity} below floor"
      end
    end
  end
end
