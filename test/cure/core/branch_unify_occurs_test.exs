defmodule Cure.Core.BranchUnifyOccursTest do
  @moduledoc """
  Named occurs-check/cycle antibody (pre-port banking spec §4 W3; roadmap A2/#23),
  UPDATED for the Agda Cycle-rule port (Rules/LHS/Unify.hs).

  In well-formed signatures a ctor's result indices are closed over its own
  telescope (vars < arity), so a cyclic solve cannot arise from elaborator
  output — the kernel's cycle handling (`bind_index`) is exercised here only via
  an ADVERSARIAL signature reachable through the public `Kernel.branch_unify/4`:
  a ctor whose result index references a variable OUTSIDE its telescope, producing
  the equation `MkWr(x) ~ x`, i.e. the strongly-rigid cycle `x = MkWr(x)`.

  Since `x` occurs strongly rigid (under the constructor `MkWr`) in the RHS, the
  equation is absurd by acyclicity, so the kernel now discharges the branch as
  `:impossible` — the precise Agda/Idris verdict. The original soundness
  obligations still hold a fortiori: the kernel neither loops nor FABRICATES a
  solve (`:impossible` binds nothing). This supersedes the earlier conservative
  `:trivial` degrade; see `Cure.Core.CycleRuleTest` and `strongly_rigid_occurs?`.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Context, Env, Eval, Inductive, Kernel}

  @dec {:data, :Dec, [], []}
  @wr {:data, :Wr, [], []}

  test "a strongly-rigid cyclic index equation is discharged :impossible (Cycle rule), never a solve, never a loop" do
    env =
      Env.empty()
      |> Inductive.declare(Inductive.family(:Dec, [], [], 0), [
        Inductive.ctor(:Dcoupled, [], []),
        Inductive.ctor(:Causal, [], [])
      ])
      |> Inductive.declare(Inductive.family(:Wr, [], [], 0), [
        Inductive.ctor(:MkWr, [{:d, @dec}], [])
      ])
      # adversarial: result index {:ctor, :MkWr, [{:var, 1}]} references var 1,
      # OUTSIDE the 1-slot telescope (arity 1 ⇒ own vars are < 1)
      |> Inductive.declare(Inductive.family(:IW, [], [{:w, @wr}], 0), [
        Inductive.ctor(:iw, [{:p, @dec}], [{:ctor, :MkWr, [{:var, 1}]}])
      ])

    ctx = Context.empty(env) |> Context.extend(Eval.eval(@wr, []))
    # scrutinee index value: the neutral outer variable x itself
    scrut_index = {:vneutral, {:nvar, 0}}

    assert :impossible = Kernel.branch_unify(ctx, :IW, :iw, [scrut_index])
  end
end
