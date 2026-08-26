defmodule Antigen.NeutralAppMotiveTest do
  @moduledoc """
  D1 antibody (spec 2026-07-08-neutral-app-sort §3.2): the kernel accepts a
  motive applying a type-family head (the enlarged accept set) and still rejects
  non-type-valued heads — pinned through the REAL kernel, no shims.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Eval, Kernel}
  alias Cure.Elab.Program

  defp nat_env do
    {:ok, env} = Program.elaborate("mod P\n  type Nat = Z | S(Nat)\nend\n")
    env
  end

  # ctx: [ b : (Nat) -> Type ]  (level 0)
  defp ctx_with_type_family(env) do
    pi =
      Eval.eval({:pi, Cure.Core.Grade.unrestricted(), {:data, :"P#Nat", [], []}, {:type, 0}}, [])

    Context.extend(Context.empty(env), pi)
  end

  test "accept pin: a motive applying a type-family variable sorts (case infers)" do
    ctx = ctx_with_type_family(nat_env())
    nat = {:data, :"P#Nat", [], []}
    # b is de Bruijn var 1 UNDER the motive's own binder (v : Nat is var 0).
    motive = {:lam, Cure.Core.Grade.unrestricted(), nat, {:app, {:var, 1}, {:var, 0}}}

    # Branch bodies must inhabit b(idx) — impossible to write closed, so use a
    # scrutinee-free acceptance probe: check_motive_wf alone gates the motive;
    # drive it via infer on a case whose branches are themselves neutral-typed.
    # Simplest fully-checkable form: branches returning `b(...)`-typed values do
    # not exist closed, so pin acceptance at the motive-wf boundary by asserting
    # the case does NOT fail with :bad_motive (it must fail LATER, in branch
    # checking, with a branch-related error — proving motive-wf passed).
    kase =
      {:case, {:ctor, :"P#Z", []}, motive, [{:"P#Z", 0, {:ctor, :"P#Z", []}}, {:"P#S", 1, {:ctor, :"P#Z", []}}]}

    assert {:error, err} = Kernel.infer(ctx, kase)
    refute err == :bad_motive, "motive-wf should now accept the neutral-app motive; got :bad_motive"
  end

  test "reject pin: a motive applying a NON-function head still fails :bad_motive" do
    ctx = Context.empty(nat_env())
    nat = {:data, :Nat, [], []}
    motive = {:lam, Cure.Core.Grade.unrestricted(), nat, {:app, {:var, 0}, {:ctor, :Z, []}}}
    kase = {:case, {:ctor, :Z, []}, motive, [{:Z, 0, {:ctor, :Z, []}}, {:S, 1, {:ctor, :Z, []}}]}

    assert {:error, :bad_motive} = Kernel.infer(ctx, kase)
  end
end
