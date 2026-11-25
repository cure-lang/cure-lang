defmodule Cure.Elab.Phase5IndexAliasRetryTest do
  use ExUnit.Case, async: false

  alias Cure.Core.{Context, Env, Eval, Kernel, Normalise, Term}
  alias Cure.Elab.{Elaborator, Program}

  @moduletag :tmp_dir

  @tag :index_alias_retry
  test "a published field alias supports a dependent read result", %{tmp_dir: dir} do
    {env, source} = fixture(dir)
    assert :ok = Kernel.check_def(env, :"AliasConsumer#inspect")
    wrong = String.replace(source, "MkOutput(answer)", "MkOutput(Z())")
    assert {:error, _} = Program.elaborate(wrong, source_roots: [dir])
  end

  @tag :alias_exact_spines
  test "exact K6 spines preserve uniform prefixes and refuse mismatched or malformed spines", %{tmp_dir: dir} do
    {env, ctx, major, arms} = parameter_fixture(dir)
    size = {:var, 2}
    named = {:app, {:global, :"ParamAliasCarrier#named"}, {:var, 1}}
    canonical = {:app, {:global, :"ParamAliasCarrier#canonical"}, {:var, 1}}
    constructor = :"ParamAliasCarrier#C"

    goal = fn prefix, arguments ->
      index = {:ctor, constructor, arguments}
      read = {:app, {:app, {:app, {:global, :"ParamAliasCarrier#read"}, prefix}, index}, {:var, 0}}
      {:data, :"ParamAliasConsumer#Output", [], [read]}
    end

    expected = goal.(size, [size, named])
    assert Cure.Core.Inductive.ctor_application_quantities(env, constructor, 2) == [:erased, :unrestricted]
    assert {:ok, term} = Elaborator.elaborate_match(major, arms, expected, ["value", "number", "size"], ctx, env)
    assert :ok = Kernel.check(ctx, term, Eval.eval(expected, Context.env(ctx)))
    aliased_size = {:app, {:global, :"ParamAliasCarrier#identity"}, size}
    preserved = goal.(aliased_size, [aliased_size, named])
    assert {:ok, {:vtype, _}} = Kernel.infer(ctx, preserved)

    {result, events} =
      trace_aliases(fn ->
        Elaborator.elaborate_match(major, arms, preserved, ["value", "number", "size"], ctx, env)
      end)

    assert Enum.any?(events, fn
             {:trace, _, :return_from, {Elaborator, :expose_index_field_aliases, 4},
              {:ctor, ^constructor, [^aliased_size, ^canonical]}} ->
               true

             _ ->
               false
           end)

    refute Enum.any?(events, fn
             {:trace, _, :call, {Elaborator, :expose_reducible_dependency, [^aliased_size, ^size, _, _]}} -> true
             _ -> false
           end)

    assert_rejected_candidate(result, ctx, preserved)
    fields_only = goal.(size, [named])
    assert {:ok, {:vtype, _}} = Kernel.infer(ctx, fields_only)

    for unsupported <- [fields_only, goal.(size, []), goal.(size, [size, size, named])] do
      assert_rejected_candidate(
        Elaborator.elaborate_match(major, arms, unsupported, ["value", "number", "size"], ctx, env),
        ctx,
        unsupported
      )
    end
  end

  @tag :alias_authored_scope
  test "authored binders and branches inside a selected field are not traversed", %{tmp_dir: dir} do
    {env, _} = fixture(dir)
    {ctx, major, arms, goal} = match_fixture(env)
    named = {:app, {:global, :"AliasCarrier#named"}, {:var, 1}}
    zero = {:ctor, :"Std.Nat#Z", []}
    boolean = {:data, :"Std.Bool#Bool", [], []}

    fields = [
      {:app, {:lam, :unrestricted, nat(), Term.shift(named, 1, 0)}, zero},
      {:let, :unrestricted, nat(), zero, Term.shift(named, 1, 0)},
      {:case, {:ctor, :"Std.Bool#True", []}, {:lam, :unrestricted, boolean, nat()},
       [{:"Std.Bool#True", 0, named}, {:"Std.Bool#False", 0, named}]},
      {:app, {:app, {:global, :"AliasCarrier#keep_type"}, {:pi, :unrestricted, nat(), nat()}}, named}
    ]

    for field <- fields do
      {:data, output, [], [{:app, {:app, read, {:ctor, constructor, [_]}}, value}]} = goal
      wrapped = {:data, output, [], [{:app, {:app, read, {:ctor, constructor, [field]}}, value}]}
      assert {:ok, {:vtype, _}} = Kernel.infer(ctx, wrapped)
      assert_not_admitted(major, arms, wrapped, ctx, env)
    end
  end

  test "the complete public candidate retains the raw goal and rejects a different well-typed answer", %{tmp_dir: dir} do
    {env, _} = fixture(dir)
    {ctx, major, arms, goal} = match_fixture(env)
    assert {:ok, {:vtype, _}} = Kernel.infer(ctx, goal)
    assert {:ok, term} = Elaborator.elaborate_match(major, arms, goal, ["value", "number"], ctx, env)
    assert :ok = Kernel.check(ctx, term, Eval.eval(goal, Context.env(ctx)))

    other = Context.extend(ctx, Eval.eval(nat(), Context.env(ctx)))
    wrong = {:data, :"AliasConsumer#Output", [], [{:var, 0}]}
    assert {:ok, {:vtype, _}} = Kernel.infer(other, wrong)
    assert {:error, _} = Kernel.check(other, Term.shift(term, 1, 0), Eval.eval(wrong, Context.env(other)))
  end

  test "unpublished and uncertified bodies do not license alias preparation", %{tmp_dir: dir} do
    {env, _} = fixture(dir)
    {ctx, major, arms, goal} = match_fixture(env)
    opaque = Env.put_reducible(env, :"AliasCarrier#named", false)
    opaque_ctx = %{ctx | signature: opaque}
    assert {:ok, {:vtype, _}} = Kernel.infer(opaque_ctx, goal)
    assert_not_admitted(major, arms, goal, opaque_ctx, opaque)
    uncertified = %{env | certified: MapSet.delete(env.certified, :"AliasCarrier#named")}
    assert_not_admitted(major, arms, goal, %{ctx | signature: uncertified}, uncertified)
  end

  test "a malformed raw annotation cannot be erased to salvage the retry", %{tmp_dir: dir} do
    {env, _} = fixture(dir)
    {ctx, major, arms, goal} = match_fixture(env)
    malformed = {:app, {:lam, :unrestricted, nat(), Term.shift(goal, 1, 0)}, {:ctor, :"Std.Bool#True", []}}
    assert {:error, _} = Kernel.infer(ctx, malformed)
    assert_not_admitted(major, arms, malformed, ctx, env)
  end

  test "well-typed binders local definitions and case goals remain outside the bounded retry", %{tmp_dir: dir} do
    {env, _} = fixture(dir)
    {ctx, major, arms, goal} = match_fixture(env)
    zero = {:ctor, :"Std.Nat#Z", []}
    boolean = {:data, :"Std.Bool#Bool", [], []}
    universe = {:type, Cure.Core.Sort.finite_closed(0)}

    for wrapped <- [
          {:app, {:lam, :unrestricted, nat(), Term.shift(goal, 1, 0)}, zero},
          {:let, :unrestricted, nat(), zero, Term.shift(goal, 1, 0)},
          {:case, {:ctor, :"Std.Bool#True", []}, {:lam, :unrestricted, boolean, universe},
           [{:"Std.Bool#True", 0, goal}, {:"Std.Bool#False", 0, goal}]}
        ] do
      assert {:ok, {:vtype, _}} = Kernel.infer(ctx, wrapped)
      assert_not_admitted(major, arms, wrapped, ctx, env)
    end
  end

  @tag :alias_zero_slot
  test "zero-quantity constructor slots are not exposed", %{tmp_dir: dir} do
    {env, _} = fixture(dir)
    {ctx, major, arms, goal} = match_fixture(env)
    key = :"AliasCarrier#C"
    ctor = Map.fetch!(env.ctors, key)
    env = %{env | ctors: Map.put(env.ctors, key, %{ctor | quantities: [:erased]})}
    ctx = %{ctx | signature: env}
    assert {:ok, {:vtype, _}} = Kernel.infer(ctx, goal)

    {result, events} =
      trace_aliases(fn -> Elaborator.elaborate_match(major, arms, goal, ["value", "number"], ctx, env) end)

    assert Enum.any?(events, fn
             {:trace, _, :call, {Elaborator, :expose_index_field_aliases, [{:ctor, ^key, _}, _, [:erased], _]}} ->
               true

             _ ->
               false
           end)

    named = {:app, {:global, :"AliasCarrier#named"}, {:var, 1}}
    canonical = {:app, {:global, :"AliasCarrier#canonical"}, {:var, 1}}

    refute Enum.any?(events, fn
             {:trace, _, :call, {Elaborator, :expose_reducible_dependency, [^named, ^canonical, _, _]}} -> true
             _ -> false
           end)

    assert_rejected_candidate(result, ctx, goal)
  end

  test "an already checked working candidate never receives alias exposure", %{tmp_dir: dir} do
    {env, _} = fixture(dir)
    {ctx, major, _arms, _goal} = match_fixture(env)
    variable = fn name -> {:variable, [], name} end
    pattern = {:function_call, [name: "PC"], [variable.("field"), variable.("answer")]}
    arms = [{:match_arm, [pattern: pattern], [variable.("answer")]}]

    {{:ok, term}, events} =
      trace_aliases(fn -> Elaborator.elaborate_match(major, arms, nat(), ["value", "number"], ctx, env) end)

    assert :ok = Kernel.check(ctx, term, Eval.eval(nat(), []))
    refute Enum.any?(events, &match?({:trace, _, :call, {Elaborator, :expose_index_field_aliases, _}}, &1))
  end

  @tag :alias_original_candidate
  test "a late failed retry preserves its original candidate after the field check", %{tmp_dir: dir} do
    {env, _} = fixture(dir)
    {ctx, major, [{:match_arm, meta, [_]}], goal} = match_fixture(env)
    zero = {:function_call, [name: "Z"], []}
    wrong = {:function_call, [name: "MkOutput"], [zero]}
    arms = [{:match_arm, meta, [wrong]}]

    {result, events} =
      trace_aliases(
        fn -> Elaborator.elaborate_match(major, arms, goal, ["value", "number"], ctx, env) end,
        [{Elaborator, :retry_index_alias_match, 2}, {Kernel, :check, 3}]
      )

    canonical = {:app, {:global, :"AliasCarrier#canonical"}, {:var, 1}}
    expected = Eval.eval(nat(), [])

    assert Enum.any?(events, fn
             {:trace, _, :call, {Kernel, :check, [^ctx, ^canonical, ^expected]}} -> true
             _ -> false
           end)

    original =
      Enum.find_value(events, fn
        {:trace, _, :call, {Elaborator, :retry_index_alias_match, [candidate, cfg]}} ->
          if cfg.ctx == ctx and cfg.original_goal == goal, do: {:found, candidate}

        _ ->
          nil
      end)

    assert {:found, candidate} = original

    assert Enum.any?(
             events,
             &match?({:trace, _, :return_from, {Elaborator, :retry_index_alias_match, 2}, ^candidate}, &1)
           )

    assert result == candidate
    assert_rejected_candidate(result, ctx, goal)
  end

  @tag :alias_late_fuel
  test "late shared fuel exhaustion is rethrown by the optional stage after exposure", %{tmp_dir: dir} do
    {env, _} = fixture(dir)
    {ctx, major, arms, goal} = match_fixture(env)
    key = Normalise.fuel_key()

    assert Enum.any?(10..200//10, fn budget ->
             {result, events} =
               trace_aliases(
                 fn ->
                   Normalise.with_fuel(budget, fn ->
                     Elaborator.elaborate_match(major, arms, goal, ["value", "number"], ctx, env)
                   end)
                 end,
                 [{Elaborator, :retry_index_alias_match, 2}]
               )

             assert Process.get(key, :absent) == :absent

             result == :fuel_exhausted and
               Enum.any?(events, &match?({:trace, _, :call, {Elaborator, :expose_index_field_aliases, _}}, &1)) and
               Enum.any?(events, fn
                 {:trace, _, :exception_from, {Elaborator, :retry_index_alias_match, 2}, {:throw, {^key, :exhausted}}} ->
                   true

                 _ ->
                   false
               end)
           end)
  end

  test "the retry does not reset shared fuel and restores the existing fixed-index guard", %{tmp_dir: dir} do
    {env, _} = fixture(dir)
    {ctx, major, arms, goal} = match_fixture(env)
    fuel_key = Normalise.fuel_key()
    guard_key = {Elaborator, :fixed_index_motive}

    for previous <- [:absent, nil, false] do
      if previous == :absent, do: Process.delete(guard_key), else: Process.put(guard_key, previous)

      assert :fuel_exhausted =
               Normalise.with_fuel(1, fn ->
                 Elaborator.elaborate_match(major, arms, goal, ["value", "number"], ctx, env)
               end)

      assert Process.get(guard_key, :absent) == previous
      assert Process.get(fuel_key, :absent) == :absent
    end

    assert :ok =
             Normalise.with_fuel(10_000, fn ->
               before = Process.get(fuel_key)
               assert {:ok, term} = Elaborator.elaborate_match(major, arms, goal, ["value", "number"], ctx, env)
               assert Process.get(fuel_key) < before
               Kernel.check(ctx, term, Eval.eval(goal, Context.env(ctx)))
             end)

    Process.delete(guard_key)
  end

  defp assert_not_admitted(major, arms, goal, ctx, env) do
    result = Elaborator.elaborate_match(major, arms, goal, ["value", "number"], ctx, env)
    assert_rejected_candidate(result, ctx, goal)
  end

  defp assert_rejected_candidate({:ok, candidate}, ctx, goal),
    do: assert({:error, _} = Kernel.check(ctx, candidate, Eval.eval(goal, Context.env(ctx))))

  defp assert_rejected_candidate({:error, _}, _ctx, _goal), do: :ok

  defp nat, do: {:data, :"Std.Nat#Nat", [], []}

  defp parameter_fixture(dir) do
    File.write!(Path.join(dir, "param_alias_carrier.cure"), """
    mod ParamAliasCarrier
      type Index(size: Nat) indices ()
        C : (field: Nat) -> Index(size)
        Stop : Index(size)
      type Payload(size: Nat) indices (index: Index(size))
        PC : (field: Nat) -> (answer: Nat) -> Payload(size, C(field))
        PS : (answer: Nat) -> Payload(size, Stop())
      @reducible
      fn canonical(value: Nat) -> Nat = match value
        Z() -> Z()
        S(rest) -> S(rest)
      @reducible
      fn named(value: Nat) -> Nat = canonical(value)
      @reducible
      fn identity(value: Nat) -> Nat = value
      @reducible
      fn read(size: Nat, index: Index(size), value: Payload(size, index)) -> Nat = match value
        PC(_, answer) -> answer
        PS(answer) -> answer
    end
    """)

    source = """
    mod ParamAliasConsumer
      use ParamAliasCarrier
      type Output indices (answer: Nat)
        MkOutput : (answer: Nat) -> Output(answer)
      fn demand(size: Nat, number: Nat, value: Payload(size, C(canonical(number))), proof: Output(read(size, C(named(number)), value))) -> Nat = Z()
    end
    """

    assert {:ok, env} = Program.elaborate(source, source_roots: [dir])
    ctx = Context.empty(env) |> Context.extend(Eval.eval(nat(), [])) |> Context.extend(Eval.eval(nat(), []))
    canonical = {:app, {:global, :"ParamAliasCarrier#canonical"}, {:var, 0}}
    index = {:ctor, :"ParamAliasCarrier#C", [{:var, 1}, canonical]}
    payload = {:data, :"ParamAliasCarrier#Payload", [{:var, 1}], [index]}
    ctx = Context.extend(ctx, Eval.eval(payload, Context.env(ctx)))
    variable = fn name -> {:variable, [], name} end
    pattern = {:function_call, [name: "PC"], [variable.("field"), variable.("answer")]}
    body = {:function_call, [name: "MkOutput"], [variable.("answer")]}
    {env, ctx, variable.("value"), [{:match_arm, [pattern: pattern], [body]}]}
  end

  defp match_fixture(env) do
    ctx = Context.extend(Context.empty(env), Eval.eval(nat(), []))
    canonical = {:app, {:global, :"AliasCarrier#canonical"}, {:var, 0}}
    payload = {:data, :"AliasCarrier#Payload", [], [{:ctor, :"AliasCarrier#C", [canonical]}]}
    ctx = Context.extend(ctx, Eval.eval(payload, Context.env(ctx)))
    named = {:app, {:global, :"AliasCarrier#named"}, {:var, 1}}

    read =
      {:app, {:app, {:global, :"AliasCarrier#read"}, {:ctor, :"AliasCarrier#C", [named]}}, {:var, 0}}

    goal = {:data, :"AliasConsumer#Output", [], [read]}
    variable = fn name -> {:variable, [], name} end
    pattern = {:function_call, [name: "PC"], [variable.("field"), variable.("answer")]}
    body = {:function_call, [name: "MkOutput"], [variable.("answer")]}
    {ctx, variable.("value"), [{:match_arm, [pattern: pattern], [body]}], goal}
  end

  defp fixture(dir) do
    File.write!(Path.join(dir, "alias_carrier.cure"), """
    mod AliasCarrier
      type Index = C(Nat) | Stop
      type Payload indices (index: Index)
        PC : (field: Nat) -> (answer: Nat) -> Payload(C(field))
        PS : (answer: Nat) -> Payload(Stop())
      @reducible
      fn canonical(value: Nat) -> Nat = match value
        Z() -> Z()
        S(rest) -> S(rest)
      @reducible
      fn named(value: Nat) -> Nat = canonical(value)
      @reducible
      fn keep_type({carrier: Type}, value: Nat) -> Nat = value
      @reducible
      fn read(index: Index, value: Payload(index)) -> Nat = match value
        PC(_, answer) -> answer
        PS(answer) -> answer
    end
    """)

    source = """
    mod AliasConsumer
      use AliasCarrier
      type Output indices (answer: Nat)
        MkOutput : (answer: Nat) -> Output(answer)
      fn inspect(number: Nat, value: Payload(C(canonical(number)))) -> Output(read(C(named(number)), value)) = match value
        PC(field, answer) -> MkOutput(answer)
    end
    """

    assert {:ok, env} = Program.elaborate(source, source_roots: [dir])
    {env, source}
  end

  defp trace_aliases(operation, extra \\ []) do
    owner = self()
    tracer = spawn(fn -> collect_trace(owner, []) end)

    functions =
      [
        {Elaborator, :expose_index_field_aliases, 4},
        {Elaborator, :expose_reducible_dependency, 4}
      ] ++ extra

    previous =
      Enum.map(functions, fn target ->
        state = {:erlang.trace_info(target, :traced), :erlang.trace_info(target, :match_spec)}
        :erlang.trace_pattern(target, [{:_, [], [{:exception_trace}]}], [:local])
        {target, state}
      end)

    try do
      :erlang.trace(self(), true, [:call, {:tracer, tracer}])
      result = operation.()
      :erlang.trace(self(), false, [:call])
      ref = :erlang.trace_delivered(self())

      receive do
        {:trace_delivered, _, ^ref} -> :ok
      after
        5_000 -> flunk("alias trace delivery did not complete")
      end

      send(tracer, :collect)

      receive do
        {:alias_trace, ^tracer, events} -> {result, events}
      after
        5_000 -> flunk("alias trace collector did not reply")
      end
    after
      :erlang.trace(self(), false, [:call])

      Enum.each(previous, fn
        {target, {{:traced, false}, _}} -> :erlang.trace_pattern(target, false, [:local])
        {target, {{:traced, mode}, {:match_spec, spec}}} -> :erlang.trace_pattern(target, spec, [mode])
      end)

      monitor = Process.monitor(tracer)
      send(tracer, :stop)

      receive do
        {:DOWN, ^monitor, :process, ^tracer, _} -> :ok
      after
        1_000 ->
          Process.exit(tracer, :kill)
          receive do: ({:DOWN, ^monitor, :process, ^tracer, _} -> :ok)
      end
    end
  end

  defp collect_trace(owner, events) do
    receive do
      :collect ->
        send(owner, {:alias_trace, self(), Enum.reverse(events)})
        collect_trace(owner, [])

      :stop ->
        :ok

      event ->
        collect_trace(owner, [event | events])
    end
  end
end
