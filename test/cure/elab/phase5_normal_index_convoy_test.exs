defmodule Cure.Elab.Phase5NormalIndexConvoyTest do
  use ExUnit.Case, async: false

  alias Cure.Core.{Context, Env, Eval, Kernel, Normalise, Quote, Term}
  alias Cure.Elab.{Elaborator, Emit, Program}

  @tag :tmp_dir
  @tag :normal_index_prerequisites
  test "destination then machine then origin refinement retains hidden predecessors", %{tmp_dir: dir} do
    source = source_fixture(dir)
    assert {:ok, env} = Program.elaborate(source, source_roots: [dir])
    assert :ok = Kernel.check_def(env, :"NormalConvoySource#inspect")

    wrong =
      String.replace(source, "%[Active(point, regular, Z()), edge, path]", "%[Accepted(regular, Z()), edge, path]")

    assert {:error, _} = Program.elaborate(wrong, source_roots: [dir])
    assert_source_runtime(dir, source)
  end

  test "a chronological shadowed carrier case closes to a complete checked definition" do
    {env, ctx, goal, arms, domains} = core_fixture()

    for index <- 0..3 do
      assert {:ok, {:vtype, _}} = Kernel.infer(ctx, Quote.reify(Context.lookup(ctx, index), ctx.length, env))
    end

    assert {:ok, {:vtype, _}} = Kernel.infer(ctx, goal)
    assert {:ok, term} = public_match(ctx, env, arms, goal)
    assert :ok = Kernel.check(ctx, term, Eval.eval(goal, Context.env(ctx)))
    type = Enum.reduce(Enum.reverse(domains), goal, fn domain, body -> {:pi, :unrestricted, domain, body} end)
    body = Enum.reduce(Enum.reverse(domains), term, fn domain, body -> {:lam, :unrestricted, domain, body} end)
    env = Env.add_def(env, :"ShadowedConvoy#proof", type, body)
    assert :ok = Kernel.check_def(env, :"ShadowedConvoy#proof")
  end

  test "distinct same-size machines and prerequisite arguments are not interchangeable" do
    {env, ctx, goal, arms, _} = core_fixture()
    assert {:ok, term} = public_match(ctx, env, arms, goal)
    refute Enum.at(Context.env(ctx), 0) == Enum.at(Context.env(ctx), 2)
    wrong_goal = Term.subst(goal, 0, {:var, 2})
    assert {:ok, {:vtype, _}} = Kernel.infer(ctx, wrong_goal)
    assert {:error, _} = Kernel.check(ctx, term, Eval.eval(wrong_goal, Context.env(ctx)))
    {root, [{:var, 2} | rest]} = peel_applications(term, [])
    wrong = Enum.reduce([{:var, 0} | rest], root, fn argument, function -> {:app, function, argument} end)
    assert {:error, _} = Kernel.check(ctx, wrong, Eval.eval(goal, Context.env(ctx)))
  end

  @tag :normal_hidden_grade
  test "normal-index retries use the protected hidden prerequisite quantity guard" do
    {env, ctx, goal, arms, _} = core_fixture()

    for grade <- [:unrestricted, :erased, :linear, :affine] do
      frame = %{ctx | grades: List.replace_at(ctx.grades, 2, grade)}
      assert {:ok, {:vtype, _}} = Kernel.infer(frame, goal)

      {result, events} =
        trace_operation(
          fn -> public_match(frame, env, arms, goal) end,
          [{:retry_index_motivegen_prerequisites, 6}, {:fixed_index_siblings, 6}, {:close_fixed_prerequisites, 8}]
        )

      assert Enum.any?(events, &match?({:trace, _, :call, {Elaborator, :retry_index_motivegen_prerequisites, _}}, &1))

      if grade in [:linear, :affine] do
        retry = during_optional_retry(events)
        assert returned?(retry, :fixed_index_siblings, 6, :unsupported)
        assert returned?(retry, :close_fixed_prerequisites, 8, :unsupported)
        assert_not_admitted(result, frame, goal)
      else
        assert {:ok, term} = result
        assert :ok = Kernel.check(frame, term, Eval.eval(goal, Context.env(frame)))

        assert Enum.any?(events, fn
                 {:trace, _, :return_from, {Elaborator, :fixed_index_siblings, 6}, {:ok, siblings}} ->
                   Enum.any?(siblings, &(&1.index == 2 and &1.grade == grade))

                 _ ->
                   false
               end)
      end
    end
  end

  @tag :normal_working_form
  test "an already checked indexed convoy keeps its original Core form" do
    {env, ctx, goal, arms, _} = core_fixture()

    {{:ok, term}, events} =
      trace_operation(
        fn ->
          Elaborator.elaborate_match(variable("current"), arms, goal, ["current", "packed", "old", "n"], ctx, env)
        end,
        [{:build_index_motivegen_case, 2}, {:retry_index_motivegen_prerequisites, 6}, {:fixed_index_siblings, 6}]
      )

    assert :ok = Kernel.check(ctx, term, Eval.eval(goal, Context.env(ctx)))
    assert returned?(events, :build_index_motivegen_case, 2, {:ok, term})
    assert returned?(events, :retry_index_motivegen_prerequisites, 6, {:ok, term})
    refute Enum.any?(events, &match?({:trace, _, :call, {Elaborator, :fixed_index_siblings, _}}, &1))
  end

  @tag :normal_index_cycle
  test "cyclic unused sibling assumptions cannot pass the normal-index retry" do
    {env, ctx, goal, arms, _} = core_fixture()

    bad = fn level ->
      {:vdata, :"ShadowedConvoy#Bad", [{:vneutral, {:nvar, 0}}, {:vneutral, {:nvar, level}}]}
    end

    for cycle <- [:self, :mutual] do
      frame =
        case cycle do
          :self -> Context.extend(ctx, bad.(4))
          :mutual -> ctx |> Context.extend(bad.(5)) |> Context.extend(bad.(4))
        end

      extra = frame.length - ctx.length
      shifted_goal = Term.shift(goal, extra, 0)
      names = if cycle == :self, do: ["bad"], else: ["right", "left"]
      names = names ++ ["machine", "packed", "machine", "n"]
      assert {:ok, {:vtype, _}} = Kernel.infer(frame, shifted_goal)
      assert {:ok, _} = Kernel.infer(frame, {:var, extra})

      {result, events} =
        trace_operation(
          fn -> Elaborator.elaborate_match(variable("machine"), arms, shifted_goal, names, frame, env) end,
          [{:retry_index_motivegen_prerequisites, 6}, {:fixed_dependency_order, 3}]
        )

      assert Enum.any?(events, &match?({:trace, _, :call, {Elaborator, :retry_index_motivegen_prerequisites, _}}, &1))
      assert returned?(during_optional_retry(events), :fixed_dependency_order, 3, :unsupported)
      assert_not_admitted(result, frame, shifted_goal)
    end
  end

  test "raw annotations are checked before retry evaluation" do
    {env, ctx, goal, arms, _} = core_fixture()
    malformed = {:app, {:lam, :unrestricted, nat(), Term.shift(goal, 1, 0)}, {:ctor, :"Std.Bool#True", []}}
    assert {:error, _} = Kernel.infer(ctx, malformed)
    assert_not_admitted(public_match(ctx, env, arms, malformed), ctx, malformed)
  end

  @tag :normal_variable_gate
  test "constructor indices and computed majors preserve their original builder candidates" do
    {env, ctx, _goal, arms, _} = core_fixture()
    zero = {:ctor, :"Std.Nat#Z", []}
    machine = {:data, :"ShadowedConvoy#Machine", [], [zero]}

    constructor_frame =
      Context.empty(env)
      |> Context.extend(Eval.eval(nat(), []))
      |> Context.extend(Eval.eval(machine, []))

    packed = {:data, :"ShadowedConvoy#Pack", [zero, {:var, 0}], []}
    constructor_frame = Context.extend(constructor_frame, Eval.eval(packed, Context.env(constructor_frame)))
    constructor_frame = Context.extend(constructor_frame, Eval.eval(machine, []))
    constructor_goal = {:data, :"ShadowedConvoy#View", [zero, {:var, 2}, {:var, 1}], [{:var, 0}]}
    computed = {:function_call, [name: "identity"], [variable("n"), variable("machine")]}
    computed_term = {:app, {:app, {:global, :"ShadowedConvoy#identity"}, {:var, 3}}, {:var, 0}}
    computed_goal = {:data, :"ShadowedConvoy#View", [{:var, 3}, {:var, 2}, {:var, 1}], [computed_term]}

    for {major, frame, goal, gate} <- [
          {variable("machine"), constructor_frame, constructor_goal, :constructor_index},
          {computed, ctx, computed_goal, :computed_major}
        ] do
      assert {:ok, {:vtype, _}} = Kernel.infer(frame, goal)

      {_result, events} =
        trace_operation(
          fn -> Elaborator.elaborate_match(major, arms, goal, ["machine", "packed", "machine", "n"], frame, env) end,
          [{:retry_index_motivegen_prerequisites, 6}, {:fixed_index_siblings, 6}]
        )

      original =
        Enum.find_value(events, fn
          {:trace, _, :call, {Elaborator, :retry_index_motivegen_prerequisites, [candidate, _, cfg, _, _, indices]}} ->
            outside? =
              case gate do
                :constructor_index -> not Enum.all?(indices, &match?({:var, _}, &1))
                :computed_major -> not match?({:var, _}, cfg.scrut_term)
              end

            if outside?, do: {:found, candidate}

          _ ->
            nil
        end)

      assert {:found, candidate} = original
      assert returned?(events, :retry_index_motivegen_prerequisites, 6, candidate)

      start =
        Enum.find_index(events, fn
          {:trace, _, :call, {Elaborator, :retry_index_motivegen_prerequisites, [^candidate, _, _, _, _, _]}} -> true
          _ -> false
        end)

      finish =
        events
        |> Enum.drop(start + 1)
        |> Enum.find_index(
          &match?({:trace, _, :return_from, {Elaborator, :retry_index_motivegen_prerequisites, 6}, ^candidate}, &1)
        )

      assert is_integer(finish)

      refute Enum.any?(Enum.slice(events, start + 1, finish), fn
               {:trace, _, :call, {Elaborator, :fixed_index_siblings, _}} -> true
               _ -> false
             end)
    end
  end

  @tag :normal_original_candidate
  test "a failed prepared convoy returns its original candidate exactly" do
    {env, ctx, goal, [{:match_arm, meta, _}], _} = core_fixture()
    arms = [{:match_arm, meta, [{:function_call, [name: "Z"], []}]}]

    {result, events} =
      trace_operation(
        fn -> public_match(ctx, env, arms, goal) end,
        [{:retry_index_motivegen_prerequisites, 6}, {:fixed_index_siblings, 6}]
      )

    original =
      Enum.find_value(events, fn
        {:trace, _, :call, {Elaborator, :retry_index_motivegen_prerequisites, [candidate, _, cfg, _, _, _]}} ->
          if cfg.ctx == ctx and cfg.result_type_term == goal, do: {:found, candidate}

        _ ->
          nil
      end)

    assert {:found, candidate} = original
    assert Enum.any?(events, &match?({:trace, _, :call, {Elaborator, :fixed_index_siblings, _}}, &1))
    assert returned?(events, :retry_index_motivegen_prerequisites, 6, candidate)
    assert result == candidate
    assert_not_admitted(result, ctx, goal)
  end

  @tag :normal_shared_fuel
  test "shared fuel is rethrown after the normal retry enters prerequisite preparation" do
    {env, ctx, goal, arms, _} = core_fixture(true)
    key = Normalise.fuel_key()

    assert Enum.any?(5..300//5, fn budget ->
             {result, events} =
               trace_operation(
                 fn -> Normalise.with_fuel(budget, fn -> public_match(ctx, env, arms, goal) end) end,
                 [{:retry_index_motivegen_prerequisites, 6}, {:fixed_index_siblings, 6}]
               )

             assert Process.get(key, :absent) == :absent

             start =
               Enum.find_index(events, fn
                 {:trace, _, :call, {Elaborator, :retry_index_motivegen_prerequisites, _}} -> true
                 _ -> false
               end)

             finish =
               Enum.find_index(events, fn
                 {:trace, _, :exception_from, {Elaborator, :retry_index_motivegen_prerequisites, 6},
                  {:throw, {^key, :exhausted}}} ->
                   true

                 _ ->
                   false
               end)

             result == :fuel_exhausted and is_integer(start) and is_integer(finish) and start < finish and
               Enum.any?(Enum.slice(events, (start + 1)..(finish - 1)), fn
                 {:trace, _, :call, {Elaborator, :fixed_index_siblings, _}} -> true
                 _ -> false
               end)
           end)
  end

  defp public_match(ctx, env, arms, goal),
    do: Elaborator.elaborate_match(variable("machine"), arms, goal, ["machine", "packed", "machine", "n"], ctx, env)

  defp assert_not_admitted({:ok, term}, ctx, goal),
    do: assert({:error, _} = Kernel.check(ctx, term, Eval.eval(goal, Context.env(ctx))))

  defp assert_not_admitted({:error, _}, _ctx, _goal), do: :ok
  defp variable(name), do: {:variable, [], name}
  defp nat, do: {:data, :"Std.Nat#Nat", [], []}

  defp peel_applications({:app, function, argument}, arguments),
    do: peel_applications(function, [argument | arguments])

  defp peel_applications(root, arguments), do: {root, arguments}

  defp core_fixture(aliased_index \\ false) do
    source = """
    mod ShadowedConvoy
      type Machine indices (n: Nat)
        MkMachine : Machine(n)
      type Pack(n: Nat, old: Machine(n)) indices ()
        MkPack : Pack(n, old)
      type View(n: Nat, old: Machine(n), packed: Pack(n, old)) indices (current: Machine(n))
        Done : View(n, old, packed, MkMachine())
      type Bad(n: Nat) indices (token: Nat)
        B : (token: Nat) -> Bad(n, token)
      fn identity(n: Nat, current: Machine(n)) -> Machine(n) = current
    end
    """

    source =
      if aliased_index do
        source
        |> String.replace("mod ShadowedConvoy\n", "mod ShadowedConvoy\n  typealias Natural = Nat\n")
        |> String.replace("type Machine indices (n: Nat)", "type Machine indices (n: Natural)")
      else
        source
      end

    assert {:ok, env} = Program.elaborate(source)
    machine = fn n -> {:data, :"ShadowedConvoy#Machine", [], [n]} end
    packed = {:data, :"ShadowedConvoy#Pack", [{:var, 1}, {:var, 0}], []}
    domains = [nat(), machine.({:var, 0}), packed, machine.({:var, 2})]

    ctx =
      Enum.reduce(domains, Context.empty(env), fn domain, ctx ->
        Context.extend(ctx, Eval.eval(domain, Context.env(ctx)))
      end)

    goal = {:data, :"ShadowedConvoy#View", [{:var, 3}, {:var, 2}, {:var, 1}], [{:var, 0}]}
    pattern = {:function_call, [name: "MkMachine"], []}
    arms = [{:match_arm, [pattern: pattern], [{:function_call, [name: "Done"], []}]}]
    {env, ctx, goal, arms, domains}
  end

  defp returned?(events, name, arity, result),
    do: Enum.any?(events, &match?({:trace, _, :return_from, {Elaborator, ^name, ^arity}, ^result}, &1))

  defp during_optional_retry(events) do
    start =
      Enum.find_index(events, &match?({:trace, _, :call, {Elaborator, :retry_index_motivegen_prerequisites, _}}, &1))

    assert is_integer(start)
    rest = Enum.drop(events, start + 1)

    finish =
      Enum.find_index(rest, fn
        {:trace, _, event, {Elaborator, :retry_index_motivegen_prerequisites, 6}, _}
        when event in [:return_from, :exception_from] ->
          true

        _ ->
          false
      end)

    assert is_integer(finish)
    Enum.take(rest, finish)
  end

  defp trace_operation(operation, functions) do
    Code.ensure_loaded!(Elaborator)
    tracer = spawn(fn -> collect_trace([]) end)

    previous =
      Enum.map(functions, fn {name, arity} ->
        target = {Elaborator, name, arity}
        state = {:erlang.trace_info(target, :traced), :erlang.trace_info(target, :match_spec)}
        :erlang.trace_pattern(target, [{:_, [], [{:exception_trace}]}], [:local])
        {target, state}
      end)

    try do
      :erlang.trace(self(), true, [:call, {:tracer, tracer}])
      result = operation.()
      :erlang.trace(self(), false, [:call])
      delivered = :erlang.trace_delivered(self())

      receive do
        {:trace_delivered, _, ^delivered} -> :ok
      after
        5_000 -> flunk("convoy trace delivery did not complete")
      end

      send(tracer, {:collect, self()})

      receive do
        {:collected, events} -> {result, events}
      after
        5_000 -> flunk("convoy trace collector did not reply")
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

  defp collect_trace(events) do
    receive do
      {:collect, owner} ->
        send(owner, {:collected, Enum.reverse(events)})
        collect_trace([])

      :stop ->
        :ok

      event ->
        collect_trace([event | events])
    end
  end

  defp source_fixture(dir) do
    File.write!(Path.join(dir, "normal_convoy_provider.cure"), """
    mod NormalConvoyProvider
      type State indices (n: Nat)
        Active : (point: Bounded(n)) -> (regular: Nat) -> (constraints: Nat) -> State(n)
        Accepted : (regular: Nat) -> (constraints: Nat) -> State(n)
      type Machine indices (n: Nat)
        MkMachine : (starts: List(State(n))) -> Machine(n)
      type Thread indices (n: Nat)
        TActive : (point: Bounded(n)) -> Thread(n)
        TAccepted : Thread(n)
      @reducible
      fn thread_of(n: Nat, state: State(n)) -> Thread(n) = match state
        Active(point, _, _) -> TActive(point)
        Accepted(_, _) -> TAccepted()
      @reducible
      fn starts_of(n: Nat, machine: Machine(n)) -> List(State(n)) = match machine
        MkMachine(starts) -> starts
      type Edge(n: Nat, starts: List(State(n))) indices (state: State(n))
        EA : (point: Bounded(n)) -> (regular: Nat) -> Edge(n, starts, Active(point, regular, Z()))
        EC : (regular: Nat) -> Edge(n, starts, Accepted(regular, Z()))
      type Origin(n: Nat, starts: List(State(n))) indices (state: State(n))
        OA : (point: Bounded(n)) -> (regular: Nat) -> Origin(n, starts, Active(point, regular, Z()))
        OC : (regular: Nat) -> Origin(n, starts, Accepted(regular, Z()))
      fn origin(n: Nat, starts: List(State(n)), state: State(n), edge: Edge(n, starts, state)) -> Origin(n, starts, state) = match edge
        EA(point, regular) -> OA(point, regular)
        EC(regular) -> OC(regular)
      type Path(n: Nat, machine: Machine(n)) indices (thread: Thread(n))
        P : (thread: Thread(n)) -> Path(n, machine, thread)
    end
    """)

    """
    mod NormalConvoySource
      use NormalConvoyProvider
      typealias Pack(n: Nat, machine: Machine(n)) = Sigma(state: State(n), Sigma(edge: Edge(n, starts_of(n, machine), state), Path(n, machine, thread_of(n, state))))
      fn inspect(n: Nat, machine: Machine(n), packed: Pack(n, machine)) -> Pack(n, machine) = match packed
        mk_pair(destination, mk_pair(edge, path)) -> match destination
          Active(point, regular, constraints) -> match machine
            MkMachine(starts) -> match origin(n, starts, Active(point, regular, constraints), edge)
              OA(_, _) -> %[Active(point, regular, Z()), edge, path]
              OC(_) -> impossible
          Accepted(regular, constraints) -> match machine
            MkMachine(starts) -> match origin(n, starts, Accepted(regular, constraints), edge)
              OA(_, _) -> impossible
              OC(_) -> %[Accepted(regular, Z()), edge, path]
    end
    """
  end

  defp assert_source_runtime(dir, source) do
    provider = Path.join(dir, "normal_convoy_provider.cure")
    consumer = Path.join(dir, "normal_convoy_source.cure")
    File.write!(consumer, source)

    assert {:ok, provider_env} =
             Cure.Compiler.check_source(File.read!(provider), file: provider, source_roots: [dir])

    assert {:ok, env} = Cure.Compiler.check_source(source, file: consumer, source_roots: [dir])
    zero = {:ctor, :"Std.Nat#Z", []}
    regular = {:ctor, :"Std.Nat#S", [zero]}
    state_type = {:data, :"NormalConvoyProvider#State", [], [zero]}
    starts = {:ctor, :"Std.List#Nil", [state_type]}
    machine = {:ctor, :"NormalConvoyProvider#MkMachine", [zero, starts]}
    state = {:ctor, :"NormalConvoyProvider#Accepted", [zero, regular, zero]}
    edge = {:ctor, :"NormalConvoyProvider#EC", [zero, starts, regular]}
    thread = {:ctor, :"NormalConvoyProvider#TAccepted", [zero]}
    path = {:ctor, :"NormalConvoyProvider#P", [zero, machine, thread]}
    input = {:ctor, :"Std.Sigma#mk_pair", [state, {:ctor, :"Std.Sigma#mk_pair", [edge, path]}]}
    goal = {:app, {:app, {:global, :"NormalConvoySource#Pack"}, zero}, machine}
    result = {:app, {:app, {:app, {:global, :"NormalConvoySource#inspect"}, zero}, machine}, input}

    env =
      env
      |> Env.add_def(:"NormalConvoySource#runtime_input", goal, input, [])
      |> Env.add_def(:"NormalConvoySource#runtime_result", goal, result, [])

    assert :ok = Kernel.check_def(env, :"NormalConvoySource#runtime_input")
    assert :ok = Kernel.check_def(env, :"NormalConvoySource#runtime_result")
    active_type = {:data, :"NormalConvoyProvider#State", [], [regular]}
    active_starts = {:ctor, :"Std.List#Nil", [active_type]}
    active_machine = {:ctor, :"NormalConvoyProvider#MkMachine", [regular, active_starts]}
    point = {:bounded_lit, 0}
    active_state = {:ctor, :"NormalConvoyProvider#Active", [regular, point, regular, zero]}
    active_edge = {:ctor, :"NormalConvoyProvider#EA", [regular, active_starts, point, regular]}
    active_thread = {:ctor, :"NormalConvoyProvider#TActive", [regular, point]}
    active_path = {:ctor, :"NormalConvoyProvider#P", [regular, active_machine, active_thread]}

    active_input =
      {:ctor, :"Std.Sigma#mk_pair", [active_state, {:ctor, :"Std.Sigma#mk_pair", [active_edge, active_path]}]}

    active_goal = {:app, {:app, {:global, :"NormalConvoySource#Pack"}, regular}, active_machine}

    active_result =
      {:app, {:app, {:app, {:global, :"NormalConvoySource#inspect"}, regular}, active_machine}, active_input}

    env =
      env
      |> Env.add_def(:"NormalConvoySource#active_input", active_goal, active_input, [])
      |> Env.add_def(:"NormalConvoySource#active_result", active_goal, active_result, [])

    assert :ok = Kernel.check_def(env, :"NormalConvoySource#active_input")
    assert :ok = Kernel.check_def(env, :"NormalConvoySource#active_result")
    provider_module = :"Cure.NormalConvoyProvider"
    module = :"Cure.NormalConvoySource"

    try do
      assert {:ok, _} = Emit.compile_forms(provider_env, provider_module, [:thread_of, :starts_of, :origin])

      assert {:ok, ^provider_module} =
               Emit.compile_and_load(provider_env,
                 module: provider_module,
                 functions: [:thread_of, :starts_of, :origin]
               )

      functions = [:inspect, :runtime_input, :runtime_result, :active_input, :active_result]
      assert {:ok, _} = Emit.compile_forms(env, module, functions)
      assert {:ok, ^module} = Emit.compile_and_load(env, module: module, functions: functions)
      expected = {{:Accepted, 1, 0}, {{:EC, 1}, {:P, :TAccepted}}}
      assert apply(module, :runtime_input, []) == expected
      assert apply(module, :runtime_result, []) == expected
      active_expected = {{:Active, 0, 1, 0}, {{:EA, 0, 1}, {:P, {:TActive, 0}}}}
      assert apply(module, :active_input, []) == active_expected
      assert apply(module, :active_result, []) == active_expected
      assert {:inspect, 3} in module.module_info(:exports)
    after
      for loaded <- [module, provider_module] do
        :code.purge(loaded)
        :code.delete(loaded)
      end
    end
  end
end
