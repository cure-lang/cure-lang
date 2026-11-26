defmodule Cure.Elab.Phase5CtorPrefixConsumersTest do
  use ExUnit.Case, async: false

  alias Cure.Core.{Builtins, Context, Env, Eval, Grade, Inductive, Kernel, Sort, UniverseLevel, Validator}
  alias Cure.Elab.{Emit, Erase, Relevance}
  alias Cure.Elab.Program

  defp indices(0), do: []
  defp indices(count), do: Enum.to_list(0..(count - 1))

  defp fixture(parameter_count, quantities) do
    fields = for index <- indices(length(quantities)), do: {String.to_atom("field#{index}"), {:atom_type}}
    params = for index <- indices(parameter_count), do: {String.to_atom("parameter#{index}"), {:atom_type}}

    result_params =
      for index <- indices(parameter_count), do: {:var, length(fields) + parameter_count - 1 - index}

    env =
      Env.empty()
      |> Env.with_owner("CtorPrefixFixture")
      |> Inductive.declare(
        Inductive.family(:Carrier, params, [], Sort.finite_zero()),
        [Inductive.ctor(:Wrap, fields, [], quantities, result_params)]
      )

    family = Inductive.get_family(env, :Carrier)
    ctor = Inductive.get_ctor(env, :Wrap)
    assert :ok = Kernel.check_family(env, family)
    assert :ok = Kernel.check_ctor(env, family, ctor)
    parameters = for index <- indices(parameter_count), do: {:atom_lit, String.to_atom("p#{index}")}
    values = for index <- indices(length(fields)), do: {:atom_lit, String.to_atom("f#{index}")}
    %{env: env, family: family.name, ctor: ctor.name, parameters: parameters, values: values}
  end

  defp checked_pair(info, parameters \\ nil, values \\ nil, ctx \\ nil) do
    parameters = parameters || info.parameters
    values = values || info.values
    ctx = ctx || Context.empty(info.env)
    fields = {:ctor, info.ctor, values}
    prefixed = {:ctor, info.ctor, parameters ++ values}
    goal = {:data, info.family, parameters, []}
    expected = Eval.eval(goal, Context.env(ctx))
    assert :ok = Kernel.check(ctx, fields, expected)
    assert :ok = Kernel.check(ctx, prefixed, expected)
    {fields, prefixed, goal}
  end

  defp curried(name, arguments, head_count \\ 0) do
    {head, tail} = Enum.split(arguments, head_count)
    Enum.reduce(tail, {:ctor, name, head}, fn argument, function -> {:app, function, argument} end)
  end

  test "the shared classifier licenses only exact declared fields or a complete uniform prefix" do
    for count <- [0, 1, 2, 3] do
      info = fixture(count, [:erased, :linear, :affine, :unrestricted])
      fields = [:erased, :linear, :affine, :unrestricted]
      assert Inductive.ctor_quantities(info.env, info.ctor) == fields
      assert Inductive.ctor_application_quantities(info.env, info.ctor, 4) == fields

      assert Inductive.ctor_application_quantities(info.env, info.ctor, count + 4) ==
               List.duplicate(Grade.zero(), count) ++ fields

      assert is_nil(Inductive.ctor_application_quantities(info.env, info.ctor, 3))
      assert is_nil(Inductive.ctor_application_quantities(info.env, info.ctor, count + 5))
      assert is_nil(Inductive.ctor_application_quantities(info.env, :UnknownConstructor, 4))
      assert is_nil(Inductive.ctor_application_quantities(info.env, info.ctor, -1))

      env = info.env
      malformed = put_in(env.ctors[info.ctor].quantities, [:unrestricted])
      assert is_nil(Inductive.ctor_application_quantities(malformed, info.ctor, count + 4))
    end
  end

  test "a defensive already-shrunk constructor head retains its present survivor" do
    info = fixture(2, [:erased, :linear])
    # This invalid overapplication is not a kernel-typed ABI positive. The
    # existing defensive relevance policy must still inspect the survivor in
    # the shrunk head rather than rebranding it as the first erased field.
    term = {:app, {:ctor, info.ctor, [{:var, 0}]}, {:atom_lit, :extra}}

    assert {:error, {:erased_used_relevantly, _}} =
             Relevance.check(info.env, :shrunk_head, [:erased], term)
  end

  test "an app-only arity cannot invent a parameter prefix on an unlicensed total spine" do
    info = fixture(1, [:unrestricted])
    term = curried(info.ctor, [{:atom_lit, :constant_head}, {:var, 0}, {:atom_lit, :extra}], 1)
    assert is_nil(Inductive.ctor_application_quantities(info.env, info.ctor, 3))

    assert {:error, {:erased_used_relevantly, %{site: :present_arg}}} =
             Relevance.check(info.env, :overapplied_tail, [:erased], term)
  end

  test "independently kernel-checked flat spellings have identical present fields and erasure" do
    for count <- [1, 2, 3] do
      info = fixture(count, [:erased, :linear, :affine, :unrestricted])
      {fields, prefixed, _goal} = checked_pair(info)
      [_erased | present] = info.values
      expected = {:ctor, info.ctor, present}
      assert Erase.erase(info.env, fields) == expected
      assert Erase.erase(info.env, prefixed) == expected
      assert Erase.erase(info.env, expected) == expected

      nested = {:ctor, :DefensiveContainer, [prefixed, fields]}
      once = Erase.erase(info.env, nested)
      assert Erase.erase(info.env, once) == once
    end
  end

  test "typed flat pairs retain identical backend clauses and executed native constructors" do
    module = :"Cure.CtorPrefixRuntime"

    for count <- [1, 2, 3] do
      info = fixture(count, [:erased, :linear, :affine, :unrestricted])
      {fields, prefixed, goal} = checked_pair(info)

      env =
        info.env
        |> Env.add_def(:fields, goal, fields, [])
        |> Env.add_def(:prefixed, goal, prefixed, [])

      assert :ok = Kernel.check_def(env, :"CtorPrefixFixture#fields")
      assert :ok = Kernel.check_def(env, :"CtorPrefixFixture#prefixed")
      assert {:ok, forms} = Emit.compile_forms(env, module, [:fields, :prefixed])
      {:function, _, :fields, 0, left} = Enum.find(forms, &match?({:function, _, :fields, 0, _}, &1))
      {:function, _, :prefixed, 0, right} = Enum.find(forms, &match?({:function, _, :prefixed, 0, _}, &1))
      assert left == right

      try do
        assert {:ok, ^module} = Emit.compile_and_load(env, module: module, functions: [:fields, :prefixed])
        assert apply(module, :fields, []) == {:Wrap, :f1, :f2, :f3}
        assert apply(module, :prefixed, []) == {:Wrap, :f1, :f2, :f3}
      after
        :code.purge(module)
        :code.delete(module)
      end
    end
  end

  test "a full parameter prefix is also erased for a fieldless constructor" do
    for count <- [1, 2, 3] do
      info = fixture(count, [])
      {fields, prefixed, _goal} = checked_pair(info)
      assert Erase.erase(info.env, fields) == fields
      assert Erase.erase(info.env, prefixed) == fields
      assert Erase.erase(info.env, Erase.erase(info.env, prefixed)) == fields
    end
  end

  test "Type, Nat and closed universe-level uniform parameters share the same erased ABI" do
    env = Builtins.seed(Env.empty()) |> Env.with_owner("MixedCtorPrefix")
    nat = {:data, Inductive.builtin(env, :nat), [], []}

    family =
      Inductive.family(
        :Mixed,
        [carrier: {:type, Sort.finite_zero()}, bound: nat, level: {:level_type}],
        [],
        Sort.finite_zero()
      )

    ctor = Inductive.ctor(:MixedWrap, [evidence: {:var, 2}], [], [:unrestricted], [{:var, 3}, {:var, 2}, {:var, 1}])
    env = Inductive.declare(env, family, [ctor])
    family = Inductive.get_family(env, :Mixed)
    ctor = Inductive.get_ctor(env, :MixedWrap)
    assert :ok = Kernel.check_family(env, family)
    assert :ok = Kernel.check_ctor(env, family, ctor)
    params = [{:atom_type}, {:nat_lit, 37}, {:level_value, UniverseLevel.closed(37)}]
    expected = Eval.eval({:data, family.name, params, []}, [])
    fields = {:ctor, ctor.name, [{:atom_lit, :evidence}]}
    prefixed = {:ctor, ctor.name, params ++ [{:atom_lit, :evidence}]}
    assert :ok = Kernel.check(Context.empty(env), fields, expected)
    assert :ok = Kernel.check(Context.empty(env), prefixed, expected)
    assert :ok = Relevance.check(env, :mixed_prefix, [], prefixed)
    assert Erase.erase(env, prefixed) == fields
    assert Erase.erase(env, Erase.erase(env, prefixed)) == fields
  end

  test "defensive curried spellings classify the combined head and tail once" do
    # These are defensive representation checks, not claims that intermediate
    # curried constructor applications currently infer in the kernel.
    for count <- [1, 2, 3] do
      info = fixture(count, [:erased, :linear, :affine, :unrestricted])
      {fields, prefixed, _goal} = checked_pair(info)
      {:ctor, _, all} = prefixed
      expected = Erase.erase(info.env, fields)

      for head_count <- [0, count, count + 1] do
        term = curried(info.ctor, all, head_count)
        assert Erase.erase(info.env, term) == expected
        assert Erase.erase(info.env, Erase.erase(info.env, term)) == expected
      end
    end
  end

  test "erased uniform parameters do not consume resources but field grades remain authoritative" do
    for count <- [1, 2, 3], field_grade <- [:linear, :affine, :unrestricted] do
      info = fixture(count, [field_grade])
      quantities = List.duplicate(:erased, count) ++ [field_grade]

      ctx =
        Enum.reduce(quantities, Context.empty(info.env), fn grade, context ->
          Context.extend(context, {:vatom_type}, grade)
        end)

      params = for index <- indices(count), do: {:var, count - index}
      {fields, prefixed, _goal} = checked_pair(info, params, [{:var, 0}], ctx)
      assert :ok = Relevance.check(info.env, :fields, quantities, fields)
      assert :ok = Relevance.check(info.env, :prefixed, quantities, prefixed)
      {:ctor, _, all} = prefixed

      for head_count <- [0, count] do
        assert :ok = Relevance.check(info.env, :curried, quantities, curried(info.ctor, all, head_count))
      end
    end
  end

  test "an erased binder in a present field remains forbidden in flat and defensive curried spellings" do
    for field_grade <- [:linear, :affine, :unrestricted] do
      info = fixture(2, [field_grade])
      ctx = Context.extend(Context.empty(info.env), {:vatom_type}, :erased)
      {fields, prefixed, _goal} = checked_pair(info, nil, [{:var, 0}], ctx)
      {:ctor, _, all} = prefixed

      for term <- [fields, prefixed, curried(info.ctor, all), curried(info.ctor, all, 2)] do
        assert {:error, {:erased_used_relevantly, %{site: :present_arg}}} =
                 Relevance.check(info.env, :bad_field, [:erased], term)
      end
    end
  end

  test "linear fields do not license duplicating or dropping a linear argument" do
    info = fixture(1, [:linear, :linear])
    duplicate = {:ctor, info.ctor, info.parameters ++ [{:var, 0}, {:var, 0}]}
    dropped = {:ctor, info.ctor, info.parameters ++ info.values}

    for term <- [duplicate, dropped] do
      assert {:error, {:usage_violation, %{kind: :param, declared: :linear}}} =
               Relevance.check(info.env, :linear_field, [:linear], term)
    end
  end

  test "already-shrunk and partial arguments are not realigned onto erased field labels" do
    info = fixture(2, [:erased, :linear])
    flat = {:ctor, info.ctor, [{:var, 0}]}
    partial = curried(info.ctor, [{:var, 0}])

    for term <- [flat, partial] do
      assert is_nil(Inductive.ctor_application_quantities(info.env, info.ctor, 1))
      assert Erase.erase(info.env, term) == term
      assert Erase.erase(info.env, Erase.erase(info.env, term)) == term

      assert {:error, {:erased_used_relevantly, _}} =
               Relevance.check(info.env, :surviving_argument, [:erased], term)
    end
  end

  test "a typed opaque prefix call disappears without executing its runtime poison" do
    info = fixture(1, [:unrestricted])

    env =
      Env.add_def(
        info.env,
        :poison,
        {:pi, :unrestricted, {:atom_type}, {:atom_type}},
        {:extern, {:erlang, :error, 1}},
        [:unrestricted]
      )

    info = %{info | env: env}
    prefix = {:app, {:global, :"CtorPrefixFixture#poison"}, {:atom_lit, :prefix_must_not_run}}
    {fields, prefixed, goal} = checked_pair(info, [prefix])
    assert Erase.erase(env, prefixed) == fields
    env = Env.add_def(env, :make, goal, prefixed, [])
    assert :ok = Kernel.check_def(env, :"CtorPrefixFixture#make")
    module = :"Cure.CtorPrefixPoison"

    try do
      assert {:ok, ^module} = Emit.compile_and_load(env, module: module, functions: [:make])
      assert apply(module, :make, []) == {:Wrap, :f0}
    after
      :code.purge(module)
      :code.delete(module)
    end
  end

  test "a hole hidden in an erased uniform prefix is still refused before erasure" do
    info = fixture(1, [:unrestricted])
    hole = {:hole, "hidden_uniform_parameter"}
    {_fields, prefixed, goal} = checked_pair(info, [hole])
    assert Erase.has_hole?(prefixed)
    assert {:error, diagnostics} = Validator.validate(prefixed, Validator.release_config())
    assert Enum.any?(diagnostics, &(&1.clause == :no_hole))
    env = Env.add_def(info.env, :make, goal, prefixed, [])
    assert :ok = Kernel.check_def(env, :"CtorPrefixFixture#make")

    assert {:error, {:unfilled_hole, _}} =
             Emit.compile_forms(env, :"Cure.CtorPrefixHole", [:make])
  end

  defp effect_fixture(computation, quantities \\ [:unrestricted]) do
    family =
      Inductive.family(:EffectCarrier, [computation: {:effect_type, {:atom_type}}], [], Sort.finite_zero())

    ctor = Inductive.ctor(:EffectWrap, [evidence: {:atom_type}], [], quantities, [{:var, 1}])

    env =
      Env.empty()
      |> Env.with_owner("CtorPrefixEffect")
      |> Inductive.declare(family, [ctor])

    family = Inductive.get_family(env, :EffectCarrier)
    ctor = Inductive.get_ctor(env, :EffectWrap)
    assert :ok = Kernel.check_family(env, family)
    assert :ok = Kernel.check_ctor(env, family, ctor)
    goal = {:data, family.name, [computation], []}
    term = {:ctor, ctor.name, [computation, {:atom_lit, :evidence}]}
    assert :ok = Kernel.check(Context.empty(env), term, Eval.eval(goal, []))
    {env, goal, term, ctor.name}
  end

  test "typed effect computations in uniform prefixes are rejected on the original body before skipping" do
    pure = {:effect_pure, {:atom_lit, :parameter}}
    bind = {:effect_bind, pure, {:lam, :unrestricted, {:atom_type}, {:effect_pure, {:var, 0}}}}

    for computation <- [pure, bind] do
      {env, goal, term, name} = effect_fixture(computation)
      env = Env.add_def(env, :make, goal, term, [])
      assert :ok = Kernel.check_def(env, :"CtorPrefixEffect#make")

      # The compatibility API has no constructor metadata. It is deliberately
      # not the admission seam used by Relevance or direct emission below.
      assert {:ok, []} = Validator.validate(term, Validator.release_config())

      for original <- [term, curried(name, [computation, {:atom_lit, :evidence}])] do
        assert {:error, diagnostics} = Validator.validate(original, Validator.release_config(), env)
        assert Enum.any?(diagnostics, &(&1.clause == :no_effect_in_erased_position))

        assert {:error, {:final_core_violation, :effect_prefix, relevance_diagnostics}} =
                 Relevance.check(env, :effect_prefix, [], original)

        assert Enum.any?(relevance_diagnostics, &(&1.clause == :no_effect_in_erased_position))
        original_env = Env.add_def(env, :make, goal, original, [])

        assert {:error, {:final_core_violation, :"CtorPrefixEffect#make", release_diagnostics}} =
                 Emit.compile_forms(original_env, :"Cure.CtorPrefixEffect", [:make])

        assert Enum.any?(release_diagnostics, &(&1.clause == :no_effect_in_erased_position))
      end

      # Erasure itself is not an admission test: its result has already lost
      # the forbidden computation. Every rejection above uses the original.
      erased = Erase.erase(env, term)
      assert {:ok, []} = Validator.validate(erased, Validator.release_config(), env)
    end
  end

  test "the same effect policy protects erased declared fields but permits present fields" do
    computation = {:effect_pure, {:atom_lit, :field}}
    family = Inductive.family(:EffectFields, [], [], Sort.finite_zero())

    for grade <- [:erased, :unrestricted] do
      ctor = Inductive.ctor(:FieldWrap, [computation: {:effect_type, {:atom_type}}], [], [grade])

      env =
        Env.empty()
        |> Env.with_owner("CtorFieldEffect")
        |> Inductive.declare(family, [ctor])

      term = {:ctor, :"CtorFieldEffect#FieldWrap", [computation]}
      goal = {:data, :"CtorFieldEffect#EffectFields", [], []}
      assert :ok = Kernel.check(Context.empty(env), term, Eval.eval(goal, []))
      env = Env.add_def(env, :make, goal, term, [])

      if grade == :erased do
        assert {:error, diagnostics} = Validator.validate(term, Validator.release_config(), env)
        assert Enum.any?(diagnostics, &(&1.clause == :no_effect_in_erased_position))

        assert {:error, {:final_core_violation, :field_effect, _}} =
                 Relevance.check(env, :field_effect, [], term)

        assert {:error, {:final_core_violation, :"CtorFieldEffect#make", release_diagnostics}} =
                 Emit.compile_forms(env, :"Cure.CtorFieldEffect", [:make])

        assert Enum.any?(release_diagnostics, &(&1.clause == :no_effect_in_erased_position))
      else
        assert {:ok, []} = Validator.validate(term, Validator.release_config(), env)
        assert :ok = Relevance.check(env, :field_effect, [], term)
        assert {:ok, _forms} = Emit.compile_forms(env, :"Cure.CtorFieldEffect", [:make])
      end
    end
  end

  test "optional metadata does not weaken an inherited type-position effect restriction" do
    computation = {:effect_pure, {:atom_lit, :parameter}}
    {env, _goal, term, _name} = effect_fixture(computation)
    untrusted_type = {:pi, :unrestricted, {:atom_type}, term}

    assert {:error, diagnostics} =
             Validator.validate(untrusted_type, %{no_effect_in_type_position: :reject}, env)

    assert Enum.any?(diagnostics, &(&1.clause == :no_effect_in_type_position))
  end

  test "both emission APIs refuse original forbidden prefixes before any dry or backend erasure" do
    computation = {:effect_pure, {:atom_lit, :parameter}}
    {effect_env, effect_goal, effect_term, _ctor} = effect_fixture(computation)
    effect_env = Env.add_def(effect_env, :make, effect_goal, effect_term, [])
    info = fixture(1, [:unrestricted])
    {_fields, hole_term, hole_goal} = checked_pair(info, [{:hole, "pre_erase_order"}])
    hole_env = Env.add_def(info.env, :make, hole_goal, hole_term, [])
    mfa = {Erase, :erase, 2}

    for {env, expected} <- [{effect_env, :effect}, {hole_env, :hole}],
        operation <- [
          fn -> Emit.compile_forms(env, :"Cure.CtorPrefixFirewallOrder", [:make]) end,
          fn -> Emit.compile_and_load(env, module: :"Cure.CtorPrefixFirewallOrder", functions: [:make]) end
        ] do
      :erlang.trace_pattern(mfa, true, [:local, :call_count])

      try do
        assert {:error, reason} = operation.()

        case expected do
          :effect ->
            assert {:final_core_violation, _name, diagnostics} = reason
            assert Enum.any?(diagnostics, &(&1.clause == :no_effect_in_erased_position))

          :hole ->
            assert {:unfilled_hole, _details} = reason
        end

        assert {:call_count, 0} = :erlang.trace_info(mfa, :call_count)
      after
        :erlang.trace_pattern(mfa, false, [:local, :call_count])
      end
    end
  end

  defp raw_body(body, 0), do: body
  defp raw_body({:lam, _grade, _domain, body}, count), do: raw_body(body, count - 1)

  defp calls_unrelated?({:call, _, {:atom, _, :unrelated}, _arguments}), do: true
  defp calls_unrelated?({:call, _, {:remote, _, _, {:atom, _, :unrelated}}, _arguments}), do: true
  defp calls_unrelated?(tuple) when is_tuple(tuple), do: tuple |> Tuple.to_list() |> Enum.any?(&calls_unrelated?/1)
  defp calls_unrelated?(list) when is_list(list), do: Enum.any?(list, &calls_unrelated?/1)
  defp calls_unrelated?(_leaf), do: false

  test "paired computed with and named proof source preserve the fields-only runtime tuple" do
    module = :"Cure.CtorPrefixWithRuntime"
    functions = [:prove, :is_zero, :zero, :one, :evidence_zero, :evidence_one]

    for proof <- ["", " proof observed"], erased_other? <- [false, true] do
      source = """
      mod Std.Bounded
        type Nat = Z | S(Nat)
        @reducible
        fn is_zero(value: Nat) -> Bool = match value
          Z() -> True()
          S(rest) -> False()
        @reducible
        fn choose(value: Nat) -> Nat = match is_zero(value)
          True() -> Z()
          False() -> S(Z())
        fn unrelated(value: Nat) -> Nat = match value
          Z() -> S(Z())
          S(rest) -> Z()
        type Evidence indices (index: Nat)
          EZero : Evidence(Z())
          EOne : Evidence(S(Z()))
        type Output(other: Nat) indices (index: Nat)
          OZero : Evidence(Z()) -> Output(other, Z())
          OOne : Evidence(S(Z())) -> Output(other, S(Z()))
        fn prove(value: Nat, evidence: Evidence(choose(value))) -> Output(unrelated(value), choose(value)) = with is_zero(value)#{proof}
          True() -> OZero(evidence)
          False() -> OOne(evidence)
        fn zero() -> Nat = Z()
        fn one() -> Nat = S(Z())
        fn evidence_zero() -> Evidence(Z()) = EZero()
        fn evidence_one() -> Evidence(S(Z())) = EOne()
      end
      """

      source =
        if erased_other? do
          source
          |> String.replace("fn prove(value:", "fn prove({other: Nat}, value:")
          |> String.replace("Output(unrelated(value), choose(value))", "Output(other, choose(value))")
        else
          source
        end

      assert {:ok, env} = Program.elaborate(source)
      assert :ok = Kernel.check_def(env, :"Std.Bounded#prove")
      definition = Env.get_def(env, :"Std.Bounded#prove")

      assert :ok =
               Relevance.check(
                 env,
                 :paired_prove,
                 definition.quantities,
                 raw_body(definition.body, length(definition.quantities))
               )

      erased = Erase.erase(env, definition.body)
      assert Erase.erase(env, erased) == erased
      assert {:ok, forms} = Emit.compile_forms(env, module, functions)
      {:function, _, :prove, 2, clauses} = Enum.find(forms, &match?({:function, _, :prove, 2, _}, &1))
      refute calls_unrelated?(clauses)

      try do
        assert {:ok, ^module} = Emit.compile_and_load(env, module: module, functions: functions)
        zero = apply(module, :zero, [])
        one = apply(module, :one, [])
        evidence_zero = apply(module, :evidence_zero, [])
        evidence_one = apply(module, :evidence_one, [])
        assert apply(module, :prove, [zero, evidence_zero]) == {:OZero, evidence_zero}
        assert apply(module, :prove, [one, evidence_one]) == {:OOne, evidence_one}
      after
        :code.purge(module)
        :code.delete(module)
      end
    end
  end
end
