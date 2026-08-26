defmodule Antigen.Generators.DepMatchTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.{DepMatch, SigMenu}
  alias Antigen.Backend.StreamData, as: B
  alias Antigen.Challenge
  alias Cure.Core.{Context, Kernel, Normalise}

  @sample 500

  test "every sampled dependent-match challenge is a well-typed indexed Vec case" do
    for %Challenge{} = c <- B.interp(DepMatch.gen()) |> Enum.take(@sample) do
      assert c.kind == :typed_term
      assert match?({:case, _scrut, _motive, _branches}, c.payload.term)

      cx = SigMenu.rebuild_context(SigMenu.env_of(:v1), c.payload.ctx)

      case Kernel.infer(cx, c.payload.term) do
        {:ok, inferred} ->
          assert Normalise.quote(inferred, Context.length(cx)) == c.payload.type
          assert Normalise.nf(cx, c.payload.term, fuel: 500_000) != :fuel_exhausted

        other ->
          flunk("dep-match failed to infer: #{inspect(c.payload.term)} -> #{inspect(other)}")
      end
    end
  end

  test "the sample includes variable-index (both reachable), dependent motive, and impossible-branch variants" do
    sample = B.interp(DepMatch.gen()) |> Enum.take(@sample)

    # a dependent (type-former) motive: λm.λv. Vec m  → drives check_motive_wf/infer_type_value_sort
    assert Enum.any?(sample, fn c ->
             {:case, _s, motive, _b} = c.payload.term
             match?({:lam, _g1, _, {:lam, _g2, _, {:data, :Vec, _, _}}}, motive)
           end)

    # a closed-index scrutinee (Vec Z or Vec (S Z)) → forces an :impossible branch.
    # (list-head `match?` is empty-ctx-safe: some closed cases carry no ctx binder.)
    assert Enum.any?(sample, fn c ->
             match?([{:data, :Vec, _, [{:ctor, _, _}]} | _], c.payload.ctx)
           end)

    # a variable-index scrutinee (ctx carries a Nat binder) → both branches reachable
    assert Enum.any?(sample, fn c -> match?([{:data, :Vec, _, [{:var, _}]} | _], c.payload.ctx) end)

    # a two-index diagonal Sq scrutinee with DISTINCT index vars → forces a ≡ b
    # (the bind_index merge / unify_spine tail).
    assert Enum.any?(sample, fn c ->
             match?([{:data, :Sq, _, [{:var, _}, {:var, _}]} | _], c.payload.ctx)
           end)
  end
end
