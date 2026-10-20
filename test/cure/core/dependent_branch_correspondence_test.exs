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
  defp motive(parameter, result), do: motive_with_body(parameter, Term.shift(result, 4, 0))

  defp motive_with_body(parameter, body) do
    scrutinee =
      {:data, :BranchStaged, [Term.shift(parameter, 3, 0)], [{:var, 2}, {:var, 1}, {:var, 0}]}

    {:lam, @g, parameter, {:lam, @g, {:type, 0}, {:lam, @g, {:var, 0}, {:lam, @g, scrutinee, body}}}}
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

  test "a fresh branch reads an unrelated ambient value instead of the distinct first field", %{ctx: ctx} do
    ctx = Context.extend(ctx, {:vatom_type})
    term = program(@goal, @ctor, motive(@carrier, @carrier), {:var, 3})

    assert :ok = Kernel.check(ctx, term, {:vatom_type})
    assert {:vneutral, {:nvar, 0}} = Eval.eval(term, Context.env(ctx))
    assert {:vatom, :payload} = Eval.eval({:var, 2}, @declaration_frame)
  end

  test "a fresh branch lambda captures the ambient value rather than a field or its argument", %{ctx: ctx} do
    ctx = Context.extend(ctx, {:vatom_type})
    result = {:pi, @g, @carrier, @carrier}
    body = {:lam, @g, @carrier, {:var, 4}}
    term = program(@goal, @ctor, motive(@carrier, result), body)

    assert :ok = Kernel.check(ctx, term, Eval.eval(result, Context.env(ctx)))
    runtime = Eval.eval(term, Context.env(ctx))
    assert {:vneutral, {:nvar, 0}} = Eval.apply(runtime, {:vatom, :argument})
  end

  test "the same nonconstant motive returns the selected B index type", %{ctx: ctx} do
    motive = motive_with_body(@carrier, {:var, 2})

    for {type, value, expected} <- [
          {{:float_type}, {:float_lit, 0.5}, {:vfloat, 0.5}},
          {@carrier, {:atom_lit, :other}, {:vatom, :other}}
        ] do
      fields = [{:atom_lit, :payload}, type, value]
      goal = {:data, :BranchStaged, [@carrier], fields}
      term = program(goal, {:ctor, :BranchStage, fields}, motive, {:var, 0})
      expected_type = Eval.eval(type, [])

      assert {:ok, {:vtype, 1}} = Kernel.infer(ctx, goal)
      assert :ok = Kernel.check(ctx, term, expected_type)
      assert {:ok, ^expected_type} = Kernel.infer(ctx, term)
      assert ^expected = Eval.eval(term, [])
    end
  end

  test "an index-dependent motive retains an open caller parameter", %{ctx: ctx} do
    ctx = Context.extend(ctx, {:vtype, 0})
    ctx = Context.extend(ctx, Eval.eval({:var, 0}, Context.env(ctx)))
    fields = [{:var, 0}, {:float_type}, {:float_lit, 0.5}]
    goal = {:data, :BranchStaged, [{:var, 1}], fields}
    ctor = {:ctor, :BranchStage, fields}
    term = program(goal, ctor, motive_with_body({:var, 1}, {:var, 2}), {:var, 0})

    assert :ok = Kernel.check(ctx, term, {:vfloat_type})
    assert {:vfloat, 0.5} = Eval.eval(term, Context.env(ctx))
  end

  test "a motive result function can depend on B beneath its own binder", %{ctx: ctx} do
    motive = motive_with_body(@carrier, {:pi, @g, @carrier, {:var, 3}})
    body = {:lam, @g, @carrier, {:var, 1}}
    term = program(@goal, @ctor, motive, body)
    result = {:pi, @g, @carrier, {:float_type}}

    assert :ok = Kernel.check(ctx, term, Eval.eval(result, []))
    assert {:vfloat, 0.5} = Eval.apply(Eval.eval(term, []), {:vatom, :argument})
  end

  test "y and the scrutinee cannot replace the type-valued B motive binder", %{ctx: ctx} do
    for wrong_body <- [{:var, 0}, {:var, 1}] do
      term = program(@goal, @ctor, motive_with_body(@carrier, wrong_body), {:var, 0})
      assert {:error, _reason} = Kernel.infer(ctx, term)
    end
  end

  test "a registry scrutinee still requires coverage when a correct motive returns a sort", %{ctx: ctx} do
    ctx = Context.extend(ctx, Eval.eval(@goal, []))
    term = {:case, {:var, 0}, motive(@carrier, {:type, 0}), []}

    assert {:error, :coverage} = Kernel.infer(ctx, term)
  end

  test "ordinary unary motive inference is not indexed motive validation", %{ctx: ctx} do
    unary = {:lam, @g, @carrier, {:type, 0}}
    assert {:ok, {:vpi, _, _, _}} = Kernel.infer(ctx, unary)
    ctx = Context.extend(ctx, Eval.eval(@goal, []))

    assert {:error, :bad_motive} = Kernel.infer(ctx, {:case, {:var, 0}, unary, []})
  end

  test "motive validation checks fresh results rather than ordinary scrutinee-domain application", %{ctx: ctx} do
    # The last lambda's annotation is Atom rather than the scrutinee family.
    # Case motive validation applies the closure to the actual fresh values;
    # ordinary term application checks the annotated Pi domain instead.
    extensional =
      {:lam, @g, @carrier, {:lam, @g, {:type, 0}, {:lam, @g, {:var, 0}, {:lam, @g, @carrier, {:var, 2}}}}}

    term = program(@goal, @ctor, extensional, {:var, 0})
    assert :ok = Kernel.check(ctx, term, {:vfloat_type})
    assert {:vfloat, 0.5} = Eval.eval(term, [])

    ctx = Context.extend(ctx, Eval.eval(@goal, []))
    applied = Enum.reduce(@values ++ [{:var, 0}], extensional, fn arg, fun -> {:app, fun, arg} end)
    assert {:error, _reason} = Kernel.infer(ctx, applied)
  end
end
