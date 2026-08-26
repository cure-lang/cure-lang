defmodule Cure.E2E.BehaviorMacroTest do
  @moduledoc """
  The `behavior` sugar (OTP integration spine, item 1): a ONE-form surface that derives a complete dependent
  gen_server. The user writes the state type, the request algebra + its per-constructor reply family `ReplyOf`,
  and a `handle` block giving only the reply VALUE per request; the macro wraps each into the OTP
  `%[:reply, value, state]` tuple, synthesises the `reply_for` helper, and emits every callback + `start_link`.
  The result is an ordinary OTP callback module whose `handle_call` answers each request at its OWN reply type —
  verified here by compiling the `behavior` block and driving it with a stock `gen_server:call`. Three requests
  resolve to three DISTINCT reply types from one server (the heterogeneity `Std.Otp.call` cannot express).
  """
  use ExUnit.Case, async: false

  # A dependent gen_server written with the `behavior` sugar. Only protocol logic — no OTP boilerplate, no
  # hand-written callbacks, no explicit reply tuples.
  @source """
  mod BehaviorDemo
    use Std.Otp
    use Std.Actor
    behavior Cure.E2E.QueryServer
      state Int
      request Req
      reply ReplyOf
      body
        type RCount = Count(Int)
        type RName  = Named
        type RAck   = Ack
        type Req = GetCount | Describe | Ping
        fn ReplyOf(r: Req) -> Type = match r
          GetCount()  -> RCount
          Describe()  -> RName
          Ping()      -> RAck
      handle
        GetCount()  -> Count(state)
        Describe()  -> Named
        Ping()      -> Ack
  """

  @mod :"Cure.E2E.QueryServer"

  setup_all do
    assert {:ok, _} = Cure.Compiler.compile_and_load(@source, emit_events: false)
    :ok
  end

  test "the behavior sugar emits a real OTP gen_server callback module" do
    assert function_exported?(@mod, :handle_call, 3)
    assert function_exported?(@mod, :init, 1)
    assert function_exported?(@mod, :start_link, 1)
    assert :gen_server in (apply(@mod, :module_info, [:attributes])[:behaviour] || [])
  end

  test "each handle arm's value is wrapped into %[:reply, value, state] at its own reply type" do
    assert apply(@mod, :handle_call, [:GetCount, :from, 7]) == {:reply, {:Count, 7}, 7}
    assert apply(@mod, :handle_call, [:Describe, :from, 7]) == {:reply, :Named, 7}
    assert apply(@mod, :handle_call, [:Ping, :from, 7]) == {:reply, :Ack, 7}
  end

  test "a live gen_server answers three requests at three distinct reply types through gen_server:call" do
    {:ok, pid} = :gen_server.start_link(@mod, 42, [])

    assert :gen_server.call(pid, :GetCount) == {:Count, 42}
    assert :gen_server.call(pid, :Describe) == :Named
    assert :gen_server.call(pid, :Ping) == :Ack

    :gen_server.stop(pid)
  end
end
