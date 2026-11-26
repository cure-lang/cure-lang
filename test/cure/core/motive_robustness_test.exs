defmodule Cure.Core.MotiveRobustnessTest do
  @moduledoc """
  A `case` whose motive is ill-typed (evaluates to a non-function) must be
  REJECTED with `{:error, :bad_motive}`, not crash the kernel. Before the fix,
  `apply_motive` drove `Eval.apply` on a non-function value, raising a
  FunctionClauseError on input the TCB is supposed to reject.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Context, Env, Inductive, Kernel}

  defp ctx do
    env =
      Env.empty()
      |> Inductive.declare(Inductive.family(:Foo, [], [], Cure.Core.Sort.finite_closed(0)), [
        Inductive.ctor(:foo, [], [])
      ])

    Context.empty(env)
  end

  test "a non-function motive is rejected, not crashed" do
    # motive {:type, 0} evaluates to {:vtype, 0} — not a function of the scrutinee.
    node =
      {:case, {:ctor, :foo, []}, {:type, {:finite, %Cure.Core.UniverseLevel{constant: 0, atoms: []}}},
       [{:foo, 0, {:type, {:finite, %Cure.Core.UniverseLevel{constant: 0, atoms: []}}}}]}

    assert {:error, :bad_motive} = Kernel.infer(ctx(), node)
  end

  test "a well-formed constant motive still type-checks" do
    # motive λ(_ : Foo). Type0 — a genuine type family; the branch body must then
    # inhabit Type0, so use Foo itself ({:data,:Foo,[],[]} : Type0).
    foo = {:data, :Foo, [], []}

    node =
      {:case, {:ctor, :foo, []},
       {:lam, Cure.Core.Grade.unrestricted(), foo,
        {:type, {:finite, %Cure.Core.UniverseLevel{constant: 0, atoms: []}}}}, [{:foo, 0, foo}]}

    assert {:ok, _} = Kernel.infer(ctx(), node)
  end
end
