defmodule Cure.Core.DependentResultCorrespondenceTest do
  @moduledoc """
  Executable evidence for local dependent result-declaration obligations.
  Positive declarations and result types are kernel-checked independently.
  This is not registration of dependent signatures in the Agda soundness model.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Env, Eval, Grade, Inductive, Kernel}

  @g Grade.unrestricted()
  @carrier {:atom_type}
  @fields [{:x, {:var, 0}}, {:B, {:type, 0}}, {:y, {:var, 0}}]
  @indices [{:var, 2}, {:var, 1}, {:var, 0}]
  @grades [:unrestricted, :unrestricted, :unrestricted]
  @values [{:atom_lit, :payload}, {:float_type}, {:float_lit, 0.5}]
  @goal {:data, :ResultChain, [@carrier], @values}
  @type_redex {:app, {:lam, @g, {:type, 0}, {:var, 0}}, {:float_type}}

  setup do
    family = Inductive.family(:ResultChain, [{:A, {:type, 0}}], @fields, 1)
    ctor = Inductive.ctor(:ResultMk, @fields, @indices, @grades, [{:var, 3}])
    computed_x = {:app, {:lam, @g, {:var, 3}, {:var, 0}}, {:var, 2}}

    computed =
      Inductive.ctor(
        :ResultComputed,
        @fields,
        [computed_x, {:var, 1}, {:var, 0}],
        @grades,
        [{:var, 3}]
      )

    env = Inductive.declare(Env.empty(), family, [ctor, computed])
    assert :ok = Kernel.check_family(env, family)
    assert :ok = Kernel.check_ctor(env, family, ctor)
    assert :ok = Kernel.check_ctor(env, family, computed)
    ctx = Context.empty(env)
    assert {:ok, {:vtype, 1}} = Kernel.infer(ctx, @goal)

    {:ok, ctx: ctx, env: env, family: family}
  end

  test "whole result vectors depend on parameters and preceding index values", %{ctx: ctx} do
    assert :ok = Kernel.check(ctx, {:ctor, :ResultMk, @values}, Eval.eval(@goal, []))
  end

  test "a later index must have the type supplied by an earlier index", %{ctx: ctx} do
    malformed =
      {:data, :ResultChain, [@carrier], [{:atom_lit, :payload}, @carrier, {:float_lit, 0.5}]}

    assert {:error, _reason} = Kernel.infer(ctx, malformed)
  end

  test "a well-typed but different result index does not match", %{ctx: ctx} do
    different =
      {:data, :ResultChain, [@carrier], [{:atom_lit, :different}, {:float_type}, {:float_lit, 0.5}]}

    assert {:ok, {:vtype, 1}} = Kernel.infer(ctx, different)
    assert {:error, _reason} = Kernel.check(ctx, {:ctor, :ResultMk, @values}, Eval.eval(different, []))
  end

  test "computed result indices use the full parameter and field frame", %{ctx: ctx} do
    term = {:ctor, :ResultComputed, @values}

    assert :ok = Kernel.check(ctx, term, Eval.eval(@goal, []))

    assert {:vctor, :ResultComputed, [{:vatom, :payload}, {:vfloat_type}, {:vfloat, 0.5}]} =
             Eval.eval(term, [])
  end

  test "closing an open parameter and value agrees with independently checked computed results", %{ctx: ctx} do
    open_ctx = Context.extend(ctx, {:vtype, 0})
    open_ctx = Context.extend(open_ctx, Eval.eval({:var, 0}, Context.env(open_ctx)))
    fields = [{:var, 0}, {:float_type}, {:float_lit, 0.5}]
    goal = {:data, :ResultChain, [{:var, 1}], fields}
    constructor = {:ctor, :ResultComputed, fields}

    assert {:ok, {:vtype, 1}} = Kernel.infer(open_ctx, goal)
    assert :ok = Kernel.check(open_ctx, constructor, Eval.eval(goal, Context.env(open_ctx)))

    source =
      {:lam, @g, {:type, 0}, {:lam, @g, {:var, 0}, {:let, @g, goal, constructor, {:var, 0}}}}

    source_type = {:pi, @g, {:type, 0}, {:pi, @g, {:var, 0}, goal}}
    closed = {:ctor, :ResultComputed, @values}

    assert :ok = Kernel.check(ctx, source, Eval.eval(source_type, []))
    assert :ok = Kernel.check(ctx, closed, Eval.eval(@goal, []))

    caller_closed =
      source
      |> Eval.eval([])
      |> Eval.apply({:vatom_type})
      |> Eval.apply({:vatom, :payload})

    assert {:vctor, :ResultComputed, [{:vatom, :payload}, {:vfloat_type}, {:vfloat, 0.5}]} = caller_closed
    assert ^caller_closed = Eval.eval(closed, [])
  end

  test "a complete declaration frame closes a lambda without capturing its own argument", %{ctx: ctx} do
    declaration =
      {:lam, @g, {:type, 0},
       {:lam, @g, {:var, 0}, {:lam, @g, {:type, 0}, {:lam, @g, {:var, 0}, {:lam, @g, {:var, 3}, {:var, 3}}}}}}

    declaration_type =
      {:pi, @g, {:type, 0},
       {:pi, @g, {:var, 0}, {:pi, @g, {:type, 0}, {:pi, @g, {:var, 0}, {:pi, @g, {:var, 3}, {:var, 4}}}}}}

    applied = Enum.reduce([@carrier | @values], declaration, fn arg, fun -> {:app, fun, arg} end)
    closed = {:lam, @g, @carrier, {:atom_lit, :payload}}
    expected_type = Eval.eval({:pi, @g, @carrier, @carrier}, [])

    assert :ok = Kernel.check(ctx, declaration, Eval.eval(declaration_type, []))
    assert :ok = Kernel.check(ctx, applied, expected_type)
    assert :ok = Kernel.check(ctx, closed, expected_type)
    assert {:vatom, :payload} = Eval.apply(Eval.eval(applied, []), {:vatom, :argument})
    assert {:vatom, :payload} = Eval.apply(Eval.eval(closed, []), {:vatom, :argument})
  end

  test "a registry-valued caller substitution survives a fresh lambda binder", %{env: env} do
    family = Inductive.family(:TransportWrapper, [], [{:d, @goal}], 1)
    ctor = Inductive.ctor(:TransportWrap, [{:d, @goal}], [{:var, 0}], [:unrestricted], [])
    env = Inductive.declare(env, family, [ctor])
    ctx = Context.empty(env)
    value = {:ctor, :ResultMk, @values}
    wrapped = {:ctor, :TransportWrap, [value]}
    wrapped_goal = {:data, :TransportWrapper, [], [value]}

    assert :ok = Kernel.check_family(env, family)
    assert :ok = Kernel.check_ctor(env, family, ctor)
    assert :ok = Kernel.check(ctx, value, Eval.eval(@goal, []))
    assert {:ok, {:vtype, 1}} = Kernel.infer(ctx, wrapped_goal)
    assert :ok = Kernel.check(ctx, wrapped, Eval.eval(wrapped_goal, []))

    open_ctx = Context.extend(ctx, Eval.eval(@goal, []))
    open_goal = {:data, :TransportWrapper, [], [{:var, 0}]}

    assert {:ok, {:vtype, 1}} = Kernel.infer(open_ctx, open_goal)

    assert :ok =
             Kernel.check(
               open_ctx,
               {:ctor, :TransportWrap, [{:var, 0}]},
               Eval.eval(open_goal, Context.env(open_ctx))
             )

    source =
      {:lam, @g, @goal, {:lam, @g, @carrier, {:ctor, :TransportWrap, [{:var, 1}]}}}

    source_type =
      {:pi, @g, @goal, {:pi, @g, @carrier, {:data, :TransportWrapper, [], [{:var, 1}]}}}

    target = {:lam, @g, @carrier, wrapped}
    target_type = {:pi, @g, @carrier, wrapped_goal}

    assert :ok = Kernel.check(ctx, source, Eval.eval(source_type, []))
    assert :ok = Kernel.check(ctx, {:app, source, value}, Eval.eval(target_type, []))
    assert :ok = Kernel.check(ctx, target, Eval.eval(target_type, []))

    source_value =
      source
      |> Eval.eval([])
      |> Eval.apply(Eval.eval(value, []))
      |> Eval.apply({:vatom, :unrelated_argument})

    assert ^source_value =
             target
             |> Eval.eval([])
             |> Eval.apply({:vatom, :unrelated_argument})

    assert {:vctor, :TransportWrap, [{:vctor, :ResultMk, _fields}]} = source_value

    assert {:error, _reason} =
             Kernel.check(
               ctx,
               {:ctor, :TransportWrap, [{:atom_lit, :unrelated_argument}]},
               Eval.eval(wrapped_goal, [])
             )
  end

  test "a computed constructor case selects a non-head branch at one original dependent goal", %{ctx: ctx} do
    scrutinee = {:data, :ResultChain, [@carrier], [{:var, 2}, {:var, 1}, {:var, 0}]}

    motive =
      {:lam, @g, @carrier, {:lam, @g, {:type, 0}, {:lam, @g, {:var, 0}, {:lam, @g, scrutinee, {:var, 2}}}}}

    branches = [{:ResultMk, 3, {:var, 0}}, {:ResultComputed, 3, {:var, 0}}]

    source =
      {:let, @g, @goal, {:ctor, :ResultComputed, @values},
       {:case, {:var, 0}, Cure.Core.Term.shift(motive, 1, 0), branches}}

    reduct = {:float_lit, 0.5}
    fixed_goal = {:vfloat_type}

    assert :ok = Kernel.check(ctx, source, fixed_goal)
    assert :ok = Kernel.check(ctx, reduct, fixed_goal)
    assert {:ok, ^fixed_goal} = Kernel.infer(ctx, source)
    assert {:vfloat, 0.5} = Eval.eval(source, [])
    assert {:vfloat, 0.5} = Eval.eval(reduct, [])
    assert {:error, _reason} = Kernel.check(ctx, source, {:vatom_type})
    assert {:error, _reason} = Kernel.check(ctx, reduct, {:vatom_type})
  end

  test "missing and surplus result indices fail the declaration arity check", %{env: env, family: family} do
    for indices <- [[{:var, 2}, {:var, 1}], @indices ++ [{:var, 0}]] do
      ctor = Inductive.ctor(:ResultBadArity, @fields, indices, @grades, [{:var, 3}])
      assert {:error, :index_arity} = Kernel.check_ctor(env, family, ctor)
    end
  end

  test "well-kinded fields must still fit the declared family universe", %{env: env, family: family} do
    small = %{family | level: 0}
    ctor = Inductive.ctor(:ResultTooLarge, @fields, @indices, @grades, [{:var, 3}])

    assert :ok = Kernel.check_family(env, small)
    assert {:error, :universe_level} = Kernel.check_ctor(env, small, ctor)
  end

  test "a closed well-typed result parameter is not a uniform fresh parameter", %{env: env, family: family} do
    assert {:ok, {:vtype, 0}} = Kernel.infer(Context.empty(env), @carrier)
    ctor = Inductive.ctor(:ResultNonUniform, @fields, @indices, @grades, [@carrier])

    assert {:error, {:non_uniform_parameter, %{position: 0}}} = Kernel.check_ctor(env, family, ctor)
  end

  test "a result declaration cannot reference beyond its local frame", %{env: env, family: family} do
    ctor =
      Inductive.ctor(:ResultForwardReference, @fields, [{:var, 4}, {:var, 1}, {:var, 0}], @grades, [{:var, 3}])

    assert {:error, _reason} = Kernel.check_ctor(env, family, ctor)
  end

  test "registered constructor lookup and visible family agree on result ownership", %{ctx: ctx, env: env} do
    assert %{name: :ResultChain} = Inductive.get_family(env, :ResultChain)
    assert %{name: :ResultMk} = Inductive.get_ctor(env, :ResultMk)
    assert :ResultChain == Inductive.ctor_family(env, :ResultMk)
    assert :ok = Kernel.check(ctx, {:ctor, :ResultMk, @values}, Eval.eval(@goal, []))
  end

  test "missing family and constructor registrations cannot be admitted", %{ctx: ctx, env: env} do
    assert nil == Inductive.get_family(env, :UnregisteredResult)
    assert nil == Inductive.get_ctor(env, :UnregisteredResultMk)
    assert {:error, _reason} = Kernel.infer(ctx, {:data, :UnregisteredResult, [@carrier], @values})

    assert {:error, _reason} =
             Kernel.check(ctx, {:ctor, :UnregisteredResultMk, @values}, Eval.eval(@goal, []))
  end

  test "matching telescope shapes do not change a registered constructor's owner", %{env: env} do
    other = Inductive.family(:OtherResultChain, [{:A, {:type, 0}}], @fields, 1)
    env = Inductive.declare(env, other, [])
    ctx = Context.empty(env)
    other_goal = {:data, :OtherResultChain, [@carrier], @values}

    assert :ok = Kernel.check_family(env, other)
    assert {:ok, {:vtype, 1}} = Kernel.infer(ctx, other_goal)
    assert :ResultChain == Inductive.ctor_family(env, :ResultMk)
    assert {:error, _reason} = Kernel.check(ctx, {:ctor, :ResultMk, @values}, Eval.eval(other_goal, []))
  end

  test "reducing a type-valued field preserves the later field at the same original goal", %{ctx: ctx} do
    fields = [{:atom_lit, :payload}, @type_redex, {:float_lit, 0.5}]
    goal = {:data, :ResultChain, [@carrier], fields}
    source = {:ctor, :ResultMk, fields}
    target = {:ctor, :ResultMk, @values}
    goal_value = Eval.eval(goal, [])
    expected = {:vctor, :ResultMk, [{:vatom, :payload}, {:vfloat_type}, {:vfloat, 0.5}]}

    assert {:ok, {:vtype, 1}} = Kernel.infer(ctx, goal)
    assert :ok = Kernel.check(ctx, source, goal_value)
    assert :ok = Kernel.check(ctx, target, goal_value)
    assert ^expected = Eval.eval(source, [])
    assert ^expected = Eval.eval(target, [])
  end

  test "type and value field reductions keep one fixed goal along the whole sequence", %{ctx: ctx} do
    value_redex = {:app, {:lam, @g, {:float_type}, {:var, 0}}, {:float_lit, 0.5}}
    fields = [{:atom_lit, :payload}, @type_redex, value_redex]
    goal = {:data, :ResultChain, [@carrier], fields}
    goal_value = Eval.eval(goal, [])
    expected = {:vctor, :ResultMk, [{:vatom, :payload}, {:vfloat_type}, {:vfloat, 0.5}]}

    assert {:ok, {:vtype, 1}} = Kernel.infer(ctx, goal)

    for args <- [fields, [{:atom_lit, :payload}, {:float_type}, value_redex], @values] do
      term = {:ctor, :ResultMk, args}
      assert :ok = Kernel.check(ctx, term, goal_value)
      assert ^expected = Eval.eval(term, [])
    end
  end

  test "computed result indices also preserve the original goal when a dependent field reduces", %{ctx: ctx} do
    computed_x = {:app, {:lam, @g, @carrier, {:var, 0}}, {:atom_lit, :payload}}
    goal = {:data, :ResultChain, [@carrier], [computed_x, @type_redex, {:float_lit, 0.5}]}
    goal_value = Eval.eval(goal, [])
    source = {:ctor, :ResultComputed, [{:atom_lit, :payload}, @type_redex, {:float_lit, 0.5}]}
    target = {:ctor, :ResultComputed, @values}
    expected = {:vctor, :ResultComputed, [{:vatom, :payload}, {:vfloat_type}, {:vfloat, 0.5}]}

    assert {:ok, {:vtype, 1}} = Kernel.infer(ctx, goal)
    assert :ok = Kernel.check(ctx, source, goal_value)
    assert :ok = Kernel.check(ctx, target, goal_value)
    assert ^expected = Eval.eval(source, [])
    assert ^expected = Eval.eval(target, [])
  end

  test "an unrelated type-valued field replacement is not a preserving reduction", %{ctx: ctx} do
    fields = [{:atom_lit, :payload}, @type_redex, {:float_lit, 0.5}]
    goal = {:data, :ResultChain, [@carrier], fields}
    goal_value = Eval.eval(goal, [])
    bad = {:ctor, :ResultMk, [{:atom_lit, :payload}, @carrier, {:float_lit, 0.5}]}

    assert :ok = Kernel.check(ctx, {:ctor, :ResultMk, fields}, goal_value)
    assert {:error, _reason} = Kernel.check(ctx, bad, goal_value)
  end

  test "dependent field reduction preserves an open caller variable without capture", %{ctx: ctx} do
    ctx = Context.extend(ctx, {:vatom_type})
    fields = [{:var, 0}, @type_redex, {:float_lit, 0.5}]
    goal = {:data, :ResultChain, [@carrier], fields}
    goal_value = Eval.eval(goal, Context.env(ctx))
    source = {:ctor, :ResultMk, fields}
    target = {:ctor, :ResultMk, [{:var, 0}, {:float_type}, {:float_lit, 0.5}]}
    expected = {:vctor, :ResultMk, [{:vneutral, {:nvar, 0}}, {:vfloat_type}, {:vfloat, 0.5}]}

    assert {:ok, {:vtype, 1}} = Kernel.infer(ctx, goal)
    assert :ok = Kernel.check(ctx, source, goal_value)
    assert :ok = Kernel.check(ctx, target, goal_value)
    assert ^expected = Eval.eval(source, Context.env(ctx))
    assert ^expected = Eval.eval(target, Context.env(ctx))
  end
end
