defmodule Cure.E2E.DependentGenServerTest do
  @moduledoc """
  END-TO-END: a DEPENDENT-reply gen_server written in Cure, compiled to real BEAM, driven by real OTP.

  This is the SERVER half of the OTP integration spine (the client half is `Std.Otp.call_dep`, oracle
  `dep_call_boundary`). A gen_server's `handle_call` returns `{:reply, Reply, NewState}`; here the `Reply`
  component has the request's OWN type `ReplyOf(request)` — computed per constructor by large elimination — so a
  SINGLE server answers different requests at DIFFERENT reply types, checked per branch at compile time. The
  dependent reply type is purely static: it erases, and the module lowers to an ordinary OTP callback module,
  so a stock `gen_server:call/2` drives it. The dependent tuple is built in a `reply_for` helper whose declared
  return type puts the `Sigma` in checking position (a bare tuple literal in the callback body would need an
  expected type the lift-module path does not thread — `ctor_requires_checking_mode`).

  Requests: `GetCount` -> `RCount` (a count), `SetName(Int)` / `Ping` -> `RAck`. The two distinct reply types
  from one server are the heterogeneity `Std.Otp.call` (uniform reply) cannot express.
  """
  use ExUnit.Case, async: false

  @source """
  mod DepServerDemo
    use Std.Otp
    lift module Cure.E2E.DepCounter
      use Std.Otp
      behaviour gen_server
      typealias State = Int
      type RCount = Cnt(Int)
      type RAck = Ack
      type Req = GetCount | SetName(Int) | Ping
      fn ReplyOf(r: Req) -> Type = match r
        GetCount()  -> RCount
        SetName(_)  -> RAck
        Ping()      -> RAck
      fn reply_for(request: Req, state: State) -> Tuple(Atom, ReplyOf(request), State) = match request
        GetCount()  -> %[:reply, Cnt(state), state]
        SetName(n)  -> %[:reply, Ack, n]
        Ping()      -> %[:reply, Ack, state]
      callback init(initial: State) returns Effect(Tuple(Atom, State)) = %[:ok, initial]
      callback handle_call(request: Req, from: f, state: State) returns Effect(Tuple(Atom, ReplyOf(request), State)) = reply_for(request, state)
      callback handle_cast(message: m, state: State) returns Effect(Tuple(Atom, State)) = %[:noreply, state]
      callback handle_info(message: i, state: State) returns Effect(Tuple(Atom, State)) = %[:noreply, state]
  """

  @mod :"Cure.E2E.DepCounter"

  setup_all do
    assert {:ok, _} = Cure.Compiler.compile_and_load(@source, emit_events: false)
    :ok
  end

  test "the dependent gen_server compiles to a real OTP callback module" do
    assert function_exported?(@mod, :handle_call, 3)
    assert function_exported?(@mod, :init, 1)
    assert :gen_server in (apply(@mod, :module_info, [:attributes])[:behaviour] || [])
  end

  test "handle_call answers each request at its OWN reply type (callback ABI)" do
    # GetCount -> RCount value {:Cnt, state}; Ping/SetName -> RAck value :Ack. One callback, three reply shapes.
    assert apply(@mod, :handle_call, [:GetCount, :from, 10]) == {:reply, {:Cnt, 10}, 10}
    assert apply(@mod, :handle_call, [:Ping, :from, 10]) == {:reply, :Ack, 10}
    # SetName carries a payload and updates the state to it.
    assert apply(@mod, :handle_call, [{:SetName, 99}, :from, 10]) == {:reply, :Ack, 99}
  end

  test "a live gen_server answers heterogeneous requests through gen_server:call, with state mutation" do
    {:ok, pid} = :gen_server.start_link(@mod, 10, [])

    # Two DISTINCT reply types from the SAME server, over real OTP.
    assert :gen_server.call(pid, :GetCount) == {:Cnt, 10}
    assert :gen_server.call(pid, :Ping) == :Ack

    # A payload-carrying request mutates state; the next GetCount observes it.
    assert :gen_server.call(pid, {:SetName, 99}) == :Ack
    assert :gen_server.call(pid, :GetCount) == {:Cnt, 99}

    :gen_server.stop(pid)
  end
end
