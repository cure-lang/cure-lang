defmodule Cure.Dev.TraceTest do
  use ExUnit.Case, async: false

  def echo(value), do: value

  test "calls can retain only events whose arguments match a predicate" do
    {result, events} =
      Cure.Dev.Trace.calls(
        __MODULE__,
        :echo,
        fn ->
          [echo(:discard), echo(:keep), echo(:discard_too)]
        end,
        arity: 1,
        where: fn [value] -> value == :keep end
      )

    assert result == [:discard, :keep, :discard_too]
    assert events == [%{args: [:keep], return: :keep}]
  end

  test "calls can filter in the VM with a trace match specification" do
    {_result, events} =
      Cure.Dev.Trace.calls(
        __MODULE__,
        :echo,
        fn ->
          [echo(:discard), echo(:keep)]
        end,
        arity: 1,
        match_spec: [{[:keep], [], [{:return_trace}]}]
      )

    assert events == [%{args: [:keep], return: :keep}]
  end

  test "calls stream completed matching events to a callback" do
    parent = self()

    {_result, events} =
      Cure.Dev.Trace.calls(
        __MODULE__,
        :echo,
        fn -> echo(:streamed) end,
        arity: 1,
        on_event: fn event -> send(parent, {:trace_event, event}) end
      )

    assert_receive {:trace_event, %{args: [:streamed], return: :streamed}}
    assert events == [%{args: [:streamed], return: :streamed}]
  end

  test "calls stream matching call arguments before the call returns" do
    parent = self()

    {_result, events} =
      Cure.Dev.Trace.calls(
        __MODULE__,
        :echo,
        fn -> echo(:started) end,
        arity: 1,
        on_call: fn arguments -> send(parent, {:trace_call, arguments}) end
      )

    assert_receive {:trace_call, [:started]}
    assert events == [%{args: [:started], return: :started}]
  end

  test "calls traces processes spawned by the observed thunk" do
    {_result, events} =
      Cure.Dev.Trace.calls(
        __MODULE__,
        :echo,
        fn -> Task.async(fn -> echo(:child) end) |> Task.await() end,
        arity: 1
      )

    assert events == [%{args: [:child], return: :child}]
  end
end
