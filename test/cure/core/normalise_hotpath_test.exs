defmodule Cure.Core.NormaliseHotpathTest do
  use ExUnit.Case, async: false

  alias Cure.Core.{Context, Env, Normalise}
  alias Cure.Elab.{MetaCtx, Unify}

  @grade Cure.Core.Grade.unrestricted()
  @nat {:data, :Nat, [], []}
  @z {:ctor, :Z, []}

  test "certified delta does not rescan a definition body for closedness" do
    env =
      Env.empty()
      |> Env.add_def(:id, {:pi, @grade, @nat, @nat}, {:lam, @grade, @nat, {:var, 0}})
      |> Env.certify(:id)

    term = {:app, {:global, :id}, @z}

    {_result, events} =
      Cure.Dev.Trace.calls(
        Cure.Core.Term,
        :closed?,
        fn ->
          Enum.each(1..10, fn _ ->
            assert Normalise.nf(Context.empty(env), term) == @z
          end)
        end,
        arity: 1
      )

    assert events == []
  end

  test "meta-aware whnf combines placeholder and closedness traversal" do
    env =
      Env.empty()
      |> Env.add_def(:id, {:pi, @grade, @nat, @nat}, {:lam, @grade, @nat, {:var, 0}})
      |> Env.certify(:id)

    term = {:app, {:global, :id}, {:meta, 0}}

    {_result, events} =
      Cure.Dev.Trace.calls(
        Cure.Core.Term,
        :closed?,
        fn ->
          assert Unify.whnf_meta_aware(term, MetaCtx.new(), env) == {:meta, 0}
        end,
        arity: 1
      )

    assert events == []
  end

  test "meta-aware whnf leaves open meta-free terms unreduced" do
    env =
      Env.empty()
      |> Env.add_def(:id, {:pi, @grade, @nat, @nat}, {:lam, @grade, @nat, @z})
      |> Env.certify(:id)

    term = {:app, {:global, :id}, {:var, 0}}
    assert Unify.whnf_meta_aware(term, MetaCtx.new(), env) == term
  end

  test "cached definition closedness is reused by dependent elaboration helpers" do
    env =
      Env.empty()
      |> Env.add_def(:id, {:pi, @grade, @nat, @nat}, {:lam, @grade, @nat, {:var, 0}})
      |> Env.certify(:id)

    definition = Env.get_def(env, :id)
    assert definition.closed_body == true

    {_result, events} =
      Cure.Dev.Trace.calls(
        Cure.Core.Term,
        :closed?,
        fn ->
          Enum.each(1..100, fn _ -> assert Env.closed_body?(definition) end)
        end,
        arity: 1
      )

    assert events == []
  end
end
