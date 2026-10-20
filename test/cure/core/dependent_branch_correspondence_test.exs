defmodule Cure.Core.DependentBranchCorrespondenceTest do
  @moduledoc """
  Executable selected-branch evidence for parameter-plus-field declarations.
  Whole positive cases are kernel-checked here; this does not supply the
  missing Agda theorem for whole dependent case typing or compiler refinement.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Env, Eval, Grade, Inductive, Kernel, Term}

  @g Grade.unrestricted()
  @carrier {:atom_type}
  @values [{:atom_lit, :payload}, {:float_type}, {:float_lit, 0.5}]
  @goal {:data, :BranchStaged, [@carrier], @values}
  @ctor {:ctor, :BranchStage, @values}
  @declaration_frame [{:vfloat, 0.5}, {:vfloat_type}, {:vatom, :payload}, {:vatom_type}]

  setup do
    tele = [{:x, {:var, 0}}, {:B, {:type, 0}}, {:y, {:var, 0}}]
    family = Inductive.family(:BranchStaged, [{:A, {:type, 0}}], tele, 1)

    ctor =
      Inductive.ctor(
        :BranchStage,
        tele,
        [{:var, 2}, {:var, 1}, {:var, 0}],
        [:unrestricted, :unrestricted, :unrestricted],
        [{:var, 3}]
      )

    env = Inductive.declare(Env.empty(), family, [ctor])
    assert :ok = Kernel.check_family(env, family)
    assert :ok = Kernel.check_ctor(env, family, ctor)
    ctx = Context.empty(env)
    assert {:ok, {:vtype, 1}} = Kernel.infer(ctx, @goal)
    assert :ok = Kernel.check(ctx, @ctor, Eval.eval(@goal, []))

    {:ok, ctx: ctx}
  end

  # The motive binds x, B, y and the scrutinee; parameter/result terms are
  # relative to the caller, not those fresh binders.
  defp motive(parameter, result) do
    scrutinee =
      {:data, :BranchStaged, [Term.shift(parameter, 3, 0)], [{:var, 2}, {:var, 1}, {:var, 0}]}

    {:lam, @g, parameter,
     {:lam, @g, {:type, 0}, {:lam, @g, {:var, 0}, {:lam, @g, scrutinee, Term.shift(result, 4, 0)}}}}
  end

  # Ascribe the ctor so its implicit parameter is checked. Adding that let
  # shifts ambient references but leaves the branch's field slots intact.
  defp program(goal, ctor, motive, body, arity \\ 3) do
    {:let, @g, goal, ctor,
     {:case, {:var, 0}, Term.shift(motive, 1, 0), [{:BranchStage, arity, Term.shift(body, 1, arity)}]}}
  end

  test "a specialised parameter body agrees with the full declaration frame", %{ctx: ctx} do
    term = program(@goal, @ctor, motive(@carrier, {:type, 0}), @carrier)

    assert :ok = Kernel.check(ctx, term, {:vtype, 0})
    assert {:vatom_type} = Eval.eval({:var, 3}, @declaration_frame)
    assert {:vatom_type} = Eval.eval(term, [])
  end

  test "the last dependent field stays at zero after parameter specialisation", %{ctx: ctx} do
    term = program(@goal, @ctor, motive(@carrier, {:float_type}), {:var, 0})

    assert :ok = Kernel.check(ctx, term, {:vfloat_type})
    assert {:vfloat, 0.5} = Eval.eval({:var, 0}, @declaration_frame)
    assert {:vfloat, 0.5} = Eval.eval(term, [])
  end

  test "a specialised lambda captures the first field without capturing its argument", %{ctx: ctx} do
    result = {:pi, @g, @carrier, @carrier}
    body = {:lam, @g, @carrier, {:var, 3}}
    term = program(@goal, @ctor, motive(@carrier, result), body)

    assert :ok = Kernel.check(ctx, term, Eval.eval(result, []))

    declaration = Eval.eval({:lam, @g, {:var, 3}, {:var, 3}}, @declaration_frame)
    runtime = Eval.eval(term, [])
    assert {:vatom, :payload} = Eval.apply(declaration, {:vatom, :argument})
    assert {:vatom, :payload} = Eval.apply(runtime, {:vatom, :argument})
  end

  test "a lambda's own variable remains bound after both instantiation stages", %{ctx: ctx} do
    result = {:pi, @g, @carrier, @carrier}
    term = program(@goal, @ctor, motive(@carrier, result), {:lam, @g, @carrier, {:var, 0}})

    assert :ok = Kernel.check(ctx, term, Eval.eval(result, []))
    assert {:vatom, :argument} = Eval.apply(Eval.eval(term, []), {:vatom, :argument})
  end

  test "an open caller parameter is shifted past fields then restored", %{ctx: ctx} do
    ctx = Context.extend(ctx, {:vtype, 0})
    ctx = Context.extend(ctx, Eval.eval({:var, 0}, Context.env(ctx)))
    fields = [{:var, 0}, {:float_type}, {:float_lit, 0.5}]
    goal = {:data, :BranchStaged, [{:var, 1}], fields}
    ctor = {:ctor, :BranchStage, fields}
    term = program(goal, ctor, motive({:var, 1}, {:type, 0}), {:var, 4})

    assert {:ok, {:vtype, 1}} = Kernel.infer(ctx, goal)
    assert :ok = Kernel.check(ctx, term, {:vtype, 0})
    assert {:vneutral, {:nvar, 0}} = Eval.eval(term, Context.env(ctx))
  end

  test "an open parameter in a lambda domain and a captured field keep distinct slots", %{ctx: ctx} do
    ctx = Context.extend(ctx, {:vtype, 0})
    ctx = Context.extend(ctx, Eval.eval({:var, 0}, Context.env(ctx)))
    fields = [{:var, 0}, {:float_type}, {:float_lit, 0.5}]
    goal = {:data, :BranchStaged, [{:var, 1}], fields}
    ctor = {:ctor, :BranchStage, fields}
    result = {:pi, @g, {:var, 1}, {:var, 2}}
    body = {:lam, @g, {:var, 4}, {:var, 3}}
    term = program(goal, ctor, motive({:var, 1}, result), body)

    assert :ok = Kernel.check(ctx, term, Eval.eval(result, Context.env(ctx)))

    runtime = Eval.eval(term, Context.env(ctx))
    assert {:vneutral, {:nvar, 1}} = Eval.apply(runtime, {:vneutral, {:nvar, 2}})
  end

  test "an unspecialised declaration parameter cannot masquerade as an ambient slot", %{ctx: ctx} do
    term = program(@goal, @ctor, motive(@carrier, {:type, 0}), {:var, 3})
    assert {:error, _reason} = Kernel.infer(ctx, term)
  end

  test "parameters do not contribute to the runtime branch arity", %{ctx: ctx} do
    term = program(@goal, @ctor, motive(@carrier, {:type, 0}), @carrier, 4)
    assert {:error, :branch_arity} = Kernel.infer(ctx, term)
  end
end
