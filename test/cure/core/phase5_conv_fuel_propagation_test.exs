defmodule Cure.Core.Phase5ConvFuelPropagationTest do
  use ExUnit.Case, async: false

  alias Cure.Core.{Context, Conv, Env, Kernel, Normalise, Term}
  alias Cure.Elab.Program

  @source """
  mod Phase5ConvFuelProbe
    @reducible
    fn flip(value: Bool) -> Bool = match value
      True() -> False()
      False() -> True()
  """

  setup_all do
    assert {:ok, signature} = Program.elaborate(@source)
    key = :"Phase5ConvFuelProbe#flip"
    assert :ok = Kernel.check_def(signature, key)
    assert Env.certified?(signature, key)
    assert Term.closed?(Env.get_def(signature, key).body)
    bool = Kernel.bool_type_value(signature)
    ctx = Context.extend(Context.empty(signature), bool)
    folded = {:app, {:global, key}, {:var, 0}}

    exposed =
      Normalise.whnf(ctx, folded,
        delta: :certified,
        delta_allow: MapSet.new([key]),
        stuck_cases: :expose,
        fuel: 128
      )

    assert {:case, {:var, 0}, _, _} = exposed
    assert :ok = Kernel.check(ctx, folded, bool)
    assert :ok = Kernel.check(ctx, exposed, bool)
    {:ok, ctx: ctx, signature: signature, folded: folded, exposed: exposed, key: key}
  end

  test "public bounded conversion reports genuine exposed-stuck exhaustion in both directions", f do
    for {left, right} <- [{f.folded, f.exposed}, {f.exposed, f.folded}] do
      assert Conv.conv?(left, right, Context.env(f.ctx), f.ctx.length, f.signature)

      assert :fuel_exhausted =
               Conv.conv_within?(left, right, Context.env(f.ctx), f.ctx.length, f.signature, 1)

      assert Process.get(Normalise.fuel_key(), :absent) == :absent
    end
  end

  test "native spend exceptions propagate through the exposed-stuck comparison instead of returning false", f do
    fuel_key = Normalise.fuel_key()

    {result, events} =
      trace(fn ->
        Conv.conv_within?(f.folded, f.exposed, Context.env(f.ctx), f.ctx.length, f.signature, 1)
      end)

    assert result == :fuel_exhausted

    assert Enum.any?(events, fn
             {:trace, _, :exception_from, {Normalise, :spend_fuel, 1}, {:throw, {^fuel_key, :exhausted}}} -> true
             _ -> false
           end)

    assert Enum.any?(events, fn
             {:trace, _, :exception_from, {Conv, :conv_exposed_stuck?, 4}, {:throw, {^fuel_key, :exhausted}}} -> true
             _ -> false
           end)

    refute Enum.any?(events, fn
             {:trace, _, :return_from, {Conv, :conv_exposed_stuck?, 4}, false} -> true
             _ -> false
           end)
  end

  test "adequately fueled folded and exposed conversions remain true", f do
    for {left, right} <- [{f.folded, f.exposed}, {f.exposed, f.folded}], fuel <- [2, 8] do
      assert {:ok, true} =
               Conv.conv_within?(left, right, Context.env(f.ctx), f.ctx.length, f.signature, fuel)
    end

    assert Process.get(Normalise.fuel_key(), :absent) == :absent
  end

  test "ordinary distinct constructors still decide false without exhausting a budget", f do
    left = {:ctor, :"Std.Bool#False", []}
    right = {:ctor, :"Std.Bool#True", []}
    assert {:ok, false} = Conv.conv_within?(left, right, Context.env(f.ctx), f.ctx.length, f.signature, 1)
    refute Conv.conv?(left, right, Context.env(f.ctx), f.ctx.length, f.signature)
  end

  test "a well-typed nonconvertible exposed case remains false with sufficient fuel", f do
    {:case, scrutinee, motive, branches} = f.exposed

    identity =
      {:case, scrutinee, motive,
       Enum.map(branches, fn {constructor, 0, _body} ->
         {constructor, 0, {:ctor, constructor, []}}
       end)}

    assert :ok = Kernel.check(f.ctx, identity, Kernel.bool_type_value(f.signature))

    assert {:ok, false} =
             Conv.conv_within?(f.folded, identity, Context.env(f.ctx), f.ctx.length, f.signature, 8)
  end

  test "uncertified bodies remain opaque rather than gaining an unfolding rule", f do
    signature = %{f.signature | certified: MapSet.delete(f.signature.certified, f.key)}

    assert {:ok, false} =
             Conv.conv_within?(f.folded, f.exposed, Context.env(f.ctx), f.ctx.length, signature, 1)
  end

  test "malformed exposed motives retain the existing defensive false refusal", f do
    {:case, scrutinee, _motive, branches} = f.exposed
    malformed = {:case, scrutinee, {:not_a_core_motive}, branches}

    assert {:ok, false} =
             Conv.conv_within?(f.folded, malformed, Context.env(f.ctx), f.ctx.length, f.signature, 8)
  end

  test "direct conversion honors the caller's shared budget and restores its absent key", f do
    key = Normalise.fuel_key()
    assert Process.get(key, :absent) == :absent

    assert :fuel_exhausted =
             Normalise.with_fuel(1, fn ->
               Conv.conv?(f.folded, f.exposed, Context.env(f.ctx), f.ctx.length, f.signature)
             end)

    assert Process.get(key, :absent) == :absent
  end

  test "explicit public conversion budgets remain independent and restore an active outer scope", f do
    key = Normalise.fuel_key()

    assert :outer_finished =
             Normalise.with_fuel(13, fn ->
               before = Process.get(key)

               assert :fuel_exhausted =
                        Conv.conv_within?(f.folded, f.exposed, Context.env(f.ctx), f.ctx.length, f.signature, 1)

               assert Process.get(key) == before

               assert {:ok, true} =
                        Conv.conv_within?(f.folded, f.exposed, Context.env(f.ctx), f.ctx.length, f.signature, 2)

               assert Process.get(key) == before
               :outer_finished
             end)

    assert Process.get(key, :absent) == :absent
  end

  test "exactly spending a budget is not itself exhaustion and zero-cost conversion may finish at zero", f do
    key = Normalise.fuel_key()
    value = {:ctor, :"Std.Bool#True", []}

    assert :exactly_spent =
             Normalise.with_fuel(2, fn ->
               assert Conv.conv?(f.folded, f.exposed, Context.env(f.ctx), f.ctx.length, f.signature)
               assert Process.get(key) == 0
               assert Conv.conv?(value, value, Context.env(f.ctx), f.ctx.length, f.signature)
               assert Process.get(key) == 0
               :exactly_spent
             end)

    assert Process.get(key, :absent) == :absent
  end

  test "nested Normalise fuel scopes retain their existing independent restoration semantics", f do
    key = Normalise.fuel_key()

    assert :outer_finished =
             Normalise.with_fuel(2, fn ->
               assert f.folded == Normalise.whnf(f.ctx, f.folded)
               assert Process.get(key) == 1

               assert :inner_finished =
                        Normalise.with_fuel(1, fn ->
                          assert f.folded == Normalise.whnf(f.ctx, f.folded)
                          assert Process.get(key) == 0
                          :inner_finished
                        end)

               assert Process.get(key) == 1
               assert f.folded == Normalise.whnf(f.ctx, f.folded)
               assert Process.get(key) == 0
               :outer_finished
             end)

    assert Process.get(key, :absent) == :absent
  end

  defp trace(operation) do
    targets = [{Conv, :conv_exposed_stuck?, 4}, {Normalise, :spend_fuel, 1}]
    tracer = spawn(fn -> collect([]) end)

    previous =
      Enum.map(targets, fn target ->
        saved = {:erlang.trace_info(target, :traced), :erlang.trace_info(target, :match_spec)}
        :erlang.trace_pattern(target, [{:_, [], [{:exception_trace}]}], [:local])
        {target, saved}
      end)

    try do
      :erlang.trace(self(), true, [:call, :arity, {:tracer, tracer}])
      result = operation.()
      :erlang.trace(self(), false, [:all])
      reference = :erlang.trace_delivered(self())

      receive do
        {:trace_delivered, _, ^reference} -> :ok
      end

      send(tracer, {:collect, self()})

      receive do
        {:collected, events} -> {result, events}
      end
    after
      :erlang.trace(self(), false, [:all])

      Enum.each(previous, fn
        {target, {{:traced, false}, _}} -> :erlang.trace_pattern(target, false, [:local])
        {target, {{:traced, mode}, {:match_spec, spec}}} -> :erlang.trace_pattern(target, spec, [mode])
      end)

      send(tracer, :stop)
    end
  end

  defp collect(events) do
    receive do
      {:collect, caller} ->
        send(caller, {:collected, Enum.reverse(events)})
        collect([])

      :stop ->
        :ok

      event ->
        collect([event | events])
    end
  end
end
