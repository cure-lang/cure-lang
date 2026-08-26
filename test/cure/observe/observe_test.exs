# `Cure.Observe.TopTest` was removed with the classic pathway rip-out (#18):
# `Cure.Observe.Top` snapshotted the supervisor/actor/fsm container runtimes,
# which no longer exist. `Cure.Observe.Trace` (the typed :dbg tracer) survives.
defmodule Cure.Observe.TraceTest do
  use ExUnit.Case, async: false

  alias Cure.Observe.Trace

  setup do
    on_exit(fn -> Trace.stop() end)
    :ok
  end

  describe "signature registry" do
    test "register + lookup round-trip" do
      Trace.register_signature({Foo, :bar, 2}, ["Int", "String"], "Bool", [:io])

      assert {:ok, %{params: ["Int", "String"], return: "Bool", effects: [:io]}} =
               Trace.lookup_signature({Foo, :bar, 2})
    end

    test "missing entries return :error" do
      assert :error = Trace.lookup_signature({Foo, :unknown, 42})
    end
  end
end
