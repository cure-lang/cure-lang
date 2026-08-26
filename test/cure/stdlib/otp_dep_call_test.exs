defmodule Cure.Stdlib.OtpDepCallTest do
  @moduledoc """
  `Std.Otp.call_dep` — the DEPENDENT synchronous call. Unlike `call`, whose reply type `r` is uniform for the
  whole `GenServer(q, r)`, `call_dep` over a `DepGenServer(q, rep)` returns the request's OWN reply type
  `rep(request)`, computed per-constructor by large elimination. So a SINGLE server answers heterogeneous
  requests — different reply types checked at each call site — and asking for the wrong reply type is a compile
  error. Client half of the OTP integration spine; the reply typing's soundness is `Otp.Meta.Proof` in the
  [`cure-otp`](https://github.com/cure-lang/cure-otp) formalisation and the
  oracle probe `dep_call_boundary`. `DepGenServer` lowers to the bare pid, so this is runnable, not just
  well-typed.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  # A module that `use`s Std.Otp and declares a heterogeneous request algebra with a per-constructor ReplyOf.
  defp app(body) do
    Program.elaborate("""
    mod App
      use Std.Otp
      type RName = Nm
      type RCount = Cnt
      type RAck = Ack
      type Req = GetCount | SetName(RName) | Ping
      fn ReplyOf(r: Req) -> Type = match r
        GetCount()  -> RCount
        SetName(_)  -> RAck
        Ping()      -> RAck
    #{body}end
    """)
  end

  describe "call_dep — one server, per-request reply types" do
    test "GetCount resolves to its own reply type RCount" do
      assert {:ok, _} =
               app("  fn go(s: DepGenServer(Req, ReplyOf)) -> Effect(RCount) = call_dep(s, GetCount())\n")
    end

    test "Ping resolves to a DIFFERENT reply type RAck from the SAME server" do
      assert {:ok, _} =
               app("  fn go(s: DepGenServer(Req, ReplyOf)) -> Effect(RAck) = call_dep(s, Ping())\n")
    end

    test "asking for the wrong reply type is rejected (Ping is RAck, not RCount)" do
      assert {:error, _} =
               app("  fn go(s: DepGenServer(Req, ReplyOf)) -> Effect(RCount) = call_dep(s, Ping())\n")
    end

    test "a non-request payload is rejected" do
      assert {:error, _} =
               app("  fn go(s: DepGenServer(Req, ReplyOf)) -> Effect(RCount) = call_dep(s, 5)\n")
    end

    test "as_dep views a running gen_server under a reply family" do
      assert {:ok, _} =
               app("  fn view(s: GenServer(Req, Unit)) -> DepGenServer(Req, ReplyOf) = as_dep(s)\n")
    end
  end
end
