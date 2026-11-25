defmodule Cure.Elab.Phase5FixedIndexGuardTest do
  use ExUnit.Case, async: false

  alias Cure.Core.{Context, Eval, Kernel, Quote}
  alias Cure.Elab.{Elaborator, Program}

  @tag :tmp_dir
  @tag :hidden_prerequisite_grade_guard
  test "the new prerequisite callback preserves erased grades and refuses hidden restricted carriers", %{tmp_dir: dir} do
    source = projected_carrier_source(dir)

    {{:ok, env}, events} =
      trace_elaboration(fn -> Program.elaborate(source, source_roots: [dir]) end, [
        {:retry_fixed_index_match, 2},
        {:close_fixed_prerequisites, 8}
      ])

    assert :ok = Kernel.check_def(env, :"GuardCarrier#inspect")

    cfg =
      Enum.find_value(events, fn
        {:trace, _, :call, {Elaborator, :retry_fixed_index_match, [_, cfg]}} ->
          if cfg.family.name == :"GuardCarrier#Path" and
               Enum.any?(cfg.idx_terms, &match?({:ctor, :"GuardProvider#OffThread", _}, &1)) and
               Enum.any?(events, fn
                 {:trace, _, :call, {Elaborator, :close_fixed_prerequisites, [_, targets, _, _, _, ctx, _, _]}} ->
                   ctx == cfg.ctx and targets == cfg.idx_terms

                 _ ->
                   false
               end),
             do: cfg

        _ ->
          nil
      end)

    assert cfg != nil
    {inner_index, inner_depth} = hidden_required_carrier(events, cfg.ctx.length)
    source_index = inner_index - (inner_depth - cfg.ctx.length)
    assert source_index >= 0
    name = Enum.at(cfg.names, source_index)
    refute Enum.find_index(cfg.names, &(&1 == name)) == source_index
    {:var, major_index} = cfg.scrut_term
    major = {:variable, [], Enum.at(cfg.names, major_index)}

    for grade <- [:unrestricted, :erased, :linear, :affine] do
      ctx = %{cfg.ctx | grades: List.replace_at(cfg.ctx.grades, source_index, grade)}
      assert {:ok, {:vtype, _}} = Kernel.infer(ctx, cfg.original_goal)
      assert {:ok, _} = Kernel.infer(ctx, cfg.scrut_term)

      {result, trace} =
        trace_elaboration(
          fn -> Elaborator.elaborate_match(major, cfg.arms, cfg.original_goal, cfg.names, ctx, cfg.env) end,
          [{:fixed_index_siblings, 6}, {:close_fixed_prerequisites, 8}]
        )

      assert Enum.any?(trace, fn
               {:trace, _, :call, {Elaborator, :close_fixed_prerequisites, [siblings, _, _, visible, _, inner, _, _]}} ->
                 inner.length == inner_depth and Context.grade(inner, inner_index) == grade and
                   not Map.has_key?(visible, inner_index) and
                   not Enum.any?(siblings, &(&1.index == inner_index))

               _ ->
                 false
             end)

      if grade in [:linear, :affine] do
        assert returned?(trace, :close_fixed_prerequisites, 8, :unsupported)

        case result do
          {:ok, candidate} ->
            assert {:error, _} = Kernel.check(ctx, candidate, Eval.eval(cfg.original_goal, Context.env(ctx)))

          {:error, _} ->
            :ok
        end
      else
        assert {:ok, term} = result
        assert :ok = Kernel.check(ctx, term, Eval.eval(cfg.original_goal, Context.env(ctx)))

        assert Enum.any?(trace, fn
                 {:trace, _, :return_from, {Elaborator, :fixed_index_siblings, 6}, {:ok, siblings}} ->
                   Enum.any?(siblings, &(&1.index == inner_index and &1.grade == grade))

                 _ ->
                   false
               end)
      end
    end
  end

  @tag :dependency_cycle_guard
  test "self and mutual dependencies reach the new graph guard and cannot be admitted" do
    assert {:ok, env} = Program.elaborate(graph_source())
    field = {:data, :"GuardGraph#Field", [], []}
    ctx = Context.extend(Context.empty(env), Eval.eval(field, []))
    payload = {:data, :"GuardGraph#Payload", [], [{:ctor, :"GuardGraph#C", [{:var, 0}]}]}
    ctx = Context.extend(ctx, Eval.eval(payload, Context.env(ctx)))

    # Only the unused sibling assumptions are adversarial. The major premise
    # and original goal below are independently kind-checked in each frame.
    bad = fn level ->
      {:vdata, :"GuardGraph#Bad", [{:vctor, :"GuardGraph#C", [{:vneutral, {:nvar, 0}}]}, {:vneutral, {:nvar, level}}]}
    end

    for cycle <- [:self, :mutual] do
      frame =
        case cycle do
          :self -> Context.extend(ctx, bad.(2))
          :mutual -> ctx |> Context.extend(bad.(3)) |> Context.extend(bad.(2))
        end

      extra = frame.length - ctx.length
      goal = {:data, :"GuardGraph#View", [], [{:var, extra + 1}, {:var, extra}]}
      assert {:ok, {:vtype, _}} = Kernel.infer(frame, goal)
      assert {:ok, _} = Kernel.infer(frame, {:var, extra})
      names = if cycle == :self, do: ["bad", "value", "field"], else: ["right", "left", "value", "field"]
      variable = fn name -> {:variable, [], name} end
      pattern = {:function_call, [name: "PC"], [variable.("found")]}
      body = {:function_call, [name: "VC"], [variable.("found")]}
      arms = [{:match_arm, [pattern: pattern], [body]}]

      {result, trace} =
        trace_elaboration(
          fn -> Elaborator.elaborate_match(variable.("value"), arms, goal, names, frame, env) end,
          [{:fixed_dependency_order, 3}, {:order_fixed_dependencies, 4}]
        )

      assert returned?(trace, :fixed_dependency_order, 3, :unsupported)
      assert returned?(trace, :order_fixed_dependencies, 4, :unsupported)

      assert Enum.any?(trace, fn
               {:trace, _, :call, {Elaborator, :fixed_dependency_order, [indices, types, _]}} ->
                 MapSet.new(indices) == MapSet.new(0..(extra - 1)) and
                   Enum.all?(indices, fn index ->
                     {:data, :"GuardGraph#Bad", [], [_, {:var, dependency}]} = Map.fetch!(types, index)
                     dependency in indices
                   end)

               _ ->
                 false
             end)

      # Optional synthesis preserves its original compatibility candidate.
      # Rejection means no admission, not necessarily an {:error, _} wrapper.
      case result do
        {:ok, candidate} ->
          assert {:error, _} = Kernel.check(frame, candidate, Eval.eval(goal, Context.env(frame)))

        {:error, _} ->
          :ok
      end
    end
  end

  defp hidden_required_carrier(events, outer_depth) do
    calls =
      for {:trace, _, :call, {Elaborator, :close_fixed_prerequisites, [siblings, targets, _, visible, _, ctx, _, _]}} <-
            events,
          ctx.length > outer_depth,
          do: {siblings, targets, visible, ctx}

    Enum.find_value(Enum.chunk_every(calls, 2, 1, :discard), fn
      [{before, targets, visible, ctx}, {after_siblings, targets, _, next}] when ctx.length == next.length ->
        selected = MapSet.new(before, & &1.index)

        Enum.find_value(after_siblings, fn sibling ->
          type = Quote.reify(Context.lookup(ctx, sibling.index), ctx.length, Context.signature(ctx))

          if not MapSet.member?(selected, sibling.index) and not Map.has_key?(visible, sibling.index) and
               match?({:data, :"Std.List#List", [{:data, :"GuardProvider#State", _, _}], []}, type),
             do: {sibling.index, ctx.length}
        end)

      _ ->
        nil
    end)
  end

  defp returned?(events, name, arity, value) do
    Enum.any?(events, &match?({:trace, _, :return_from, {Elaborator, ^name, ^arity}, ^value}, &1))
  end

  defp trace_elaboration(operation, functions) do
    Code.ensure_loaded!(Elaborator)
    tracer = spawn(fn -> collect_trace([]) end)

    previous =
      Enum.map(functions, fn {name, arity} ->
        target = {Elaborator, name, arity}
        state = {:erlang.trace_info(target, :traced), :erlang.trace_info(target, :match_spec)}
        :erlang.trace_pattern(target, [{:_, [], [{:return_trace}]}], [:local])
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
        5_000 -> flunk("elaborator trace delivery did not complete")
      end

      send(tracer, {:collect, self()})

      receive do
        {:collected, events} -> {result, events}
      after
        5_000 -> flunk("elaborator trace collector did not reply")
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

  defp graph_source do
    """
    mod GuardGraph
      type Field = FZero | FNext(Field)
      type Index = C(Field) | Stop
      type Payload indices (index: Index)
        PC : (field: Field) -> Payload(C(field))
        PS : Payload(Stop())
      type Bad indices (index: Index, token: Nat)
        MkBad : (field: Field) -> (token: Nat) -> Bad(C(field), token)
      type View indices (field: Field, value: Payload(C(field)))
        VC : (field: Field) -> View(field, PC(field))
    end
    """
  end

  defp projected_carrier_source(dir) do
    File.write!(Path.join(dir, "guard_provider.cure"), """
    mod GuardProvider
      type State indices (n: Nat)
        On : State(n)
        Off : State(n)
      type Machine indices (n: Nat)
        MkMachine : (starts: List(State(n))) -> Machine(n)
      @reducible
      fn starts_of(n: Nat, machine: Machine(n)) -> List(State(n)) = match machine
        MkMachine(starts) -> starts
      type Thread indices (n: Nat)
        OnThread : Thread(n)
        OffThread : Thread(n)
      @reducible
      fn thread_of(n: Nat, state: State(n)) -> Thread(n) = match state
        On() -> OnThread()
        Off() -> OffThread()
    end
    """)

    """
    mod GuardCarrier
      use GuardProvider
      type Path(n: Nat, machine: Machine(n)) indices (input: Nat, state: Thread(n))
        Done : Path(n, machine, Z(), OffThread())
        More : (rest: Nat) -> Path(n, machine, rest, OffThread()) -> Path(n, machine, S(rest), OffThread())
        Live : (input: Nat) -> Path(n, machine, input, OnThread())
      type Edge(n: Nat, starts: List(State(n))) indices (input: Nat)
        HereEdge : Edge(n, starts, Z())
        NextEdge : (rest: Nat) -> Edge(n, starts, S(rest))
      type Pack(n: Nat, machine: Machine(n)) indices (input: Nat)
        MkPack : (state: State(n)) -> Edge(n, starts_of(n, machine), input) -> Path(n, machine, input, thread_of(n, state)) -> Pack(n, machine, input)
      type View(n: Nat, machine: Machine(n)) indices (input: Nat, packed: Pack(n, machine, input))
        WasDone : (edge: Edge(n, starts_of(n, machine), Z())) -> View(n, machine, Z(), MkPack(Off(), edge, Done()))
        WasMore : (rest: Nat) -> (edge: Edge(n, starts_of(n, machine), S(rest))) -> (path: Path(n, machine, rest, OffThread())) -> View(n, machine, S(rest), MkPack(Off(), edge, More(rest, path)))
        WasLive : (input: Nat) -> (edge: Edge(n, starts_of(n, machine), input)) -> View(n, machine, input, MkPack(On(), edge, Live(input)))
      fn inspect(n: Nat, machine: Machine(n), input: Nat, packed: Pack(n, machine, input)) -> View(n, machine, input, packed) = match machine
        MkMachine(starts) -> match packed
          MkPack(On(), edge, path) -> match path
            Live(value) -> WasLive(value, edge)
          MkPack(Off(), edge, path) -> match path
            Done() -> WasDone(edge)
            More(rest, tail) -> WasMore(rest, edge, tail)
    end
    """
  end
end
