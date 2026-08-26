defmodule Cure.Elab.QuantityGradeTest do
  @moduledoc """
  Definition and constructor **quantities are grades** (`Cure.Core.Grade.t/0`),
  not the ad-hoc two-point `{0, ω}` pair they used to be.

  Before QTT there were two quantities and the ω one was spelled `:present`. Now
  the carrier has four inhabitants, and `Erase` / `Relevance` must speak the same
  language the binders do — otherwise `Grade.admits?/2` cannot even be called on a
  stored quantity, and `fn f(1 x: T)` has nowhere to record the `1`.

  The dangerous half is `Erase`: it decides what survives to runtime by asking
  *"is this quantity the ω one?"*. Under four grades that question is
  `Grade.present?/1` — anything but `0`. Asking `q == :unrestricted` instead would
  **silently drop** every `:linear` and `:affine` argument from the emitted term.
  `:erased` alone denotes an argument with no runtime existence.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Env, Grade, Inductive}
  alias Cure.Elab.Erase

  @nat {:data, :Nat, [], []}

  # A family `Box` with one constructor `mk` taking (erased witness, real value).
  defp env_with(quantities) do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Box, [], [], 0), [
      Inductive.ctor(:mk, [w: @nat, v: @nat], [], quantities)
    ])
  end

  describe "quantities are grades" do
    test "the default constructor quantity is a grade" do
      env =
        Env.empty()
        |> Inductive.declare(Inductive.family(:Box, [], [], 0), [
          Inductive.ctor(:mk, [w: @nat, v: @nat], [])
        ])

      qs = Inductive.ctor_quantities(env, :mk)
      assert Enum.all?(qs, &Grade.grade?/1), "stored quantities must be grades, got #{inspect(qs)}"
    end

    test "every stored quantity satisfies Grade.grade?/1 for an explicit signature" do
      env = env_with([Grade.zero(), Grade.unrestricted()])
      assert Enum.all?(Inductive.ctor_quantities(env, :mk), &Grade.grade?/1)
    end
  end

  describe "erasure speaks the grade carrier" do
    # THE bug this guards. `Erase` keeps an argument iff a runtime value exists
    # for it. Under four grades that predicate is `Grade.present?/1` — NOT
    # `q == :unrestricted`, which would drop `:linear` and `:affine`.
    test "an :unrestricted argument SURVIVES erasure" do
      env = env_with([Grade.zero(), Grade.unrestricted()])
      term = {:ctor, :mk, [{:ctor, :Z, []}, {:ctor, :S, [{:ctor, :Z, []}]}]}

      assert {:ctor, :mk, [{:ctor, :S, [{:ctor, :Z, []}]}]} = Erase.erase(env, term)
    end

    test "@erased an : argument is dropped" do
      env = env_with([Grade.zero(), Grade.unrestricted()])
      term = {:ctor, :mk, [{:ctor, :Z, []}, {:ctor, :Z, []}]}
      assert {:ctor, :mk, [_only_one]} = Erase.erase(env, term)
    end

    test "@linear a : argument survives erasure — it is used exactly once, not zero times" do
      env = env_with([Grade.zero(), Grade.one()])
      term = {:ctor, :mk, [{:ctor, :Z, []}, {:ctor, :S, [{:ctor, :Z, []}]}]}

      assert {:ctor, :mk, [{:ctor, :S, [{:ctor, :Z, []}]}]} = Erase.erase(env, term)
    end

    test "@affine an : argument survives erasure" do
      env = env_with([Grade.zero(), Grade.affine()])
      term = {:ctor, :mk, [{:ctor, :Z, []}, {:ctor, :S, [{:ctor, :Z, []}]}]}

      assert {:ctor, :mk, [{:ctor, :S, [{:ctor, :Z, []}]}]} = Erase.erase(env, term)
    end

    test "erasure keeps exactly the runtime-present arguments" do
      # All four grades on a four-argument ctor: only `:erased` disappears.
      env =
        Env.empty()
        |> Inductive.declare(Inductive.family(:Quad, [], [], 0), [
          Inductive.ctor(:q, [a: @nat, b: @nat, c: @nat, d: @nat], [], [
            :erased,
            :linear,
            :affine,
            :unrestricted
          ])
        ])

      z = {:ctor, :Z, []}
      term = {:ctor, :q, [z, z, z, z]}
      assert {:ctor, :q, kept} = Erase.erase(env, term)
      assert length(kept) == 3
    end
  end
end
