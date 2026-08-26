defmodule Cure.Stdlib.OtpNameTest do
  @moduledoc """
  `Std.Otp.Name(m)` — typed process registration (Gleam-style), which closes Cure's F-1: a name lookup now
  yields a TYPED, sendable `Option(Pid(m))` rather than an untyped, unsendable `BarePid`. The message type `m`
  rides on the `Name` (the sole trust point). Tests elaborate the surface (including that a looked-up handle is
  directly sendable) and RUN register / whereis / unregister on host OTP.
  """
  use ExUnit.Case, async: false

  alias Cure.Elab.Program

  test "a looked-up name yields a TYPED handle you can send to (elaborates)" do
    assert {:ok, _} =
             Program.elaborate("""
             mod App
               use Std.Otp
               use Std.Option
               type Cmd = Inc | Dec
               fn use_it(n: Name(Cmd)) -> Effect(Unit) =
                 let found = whereis_name(n)
                 match found
                   Some(pid) -> tell(pid, Inc())
                   None() -> ()
             end
             """)
  end

  test "sending the wrong message type to a looked-up named handle is a compile error" do
    assert {:error, _} =
             Program.elaborate("""
             mod App
               use Std.Otp
               use Std.Option
               type Cmd = Inc | Dec
               fn bad(n: Name(Cmd)) -> Effect(Unit) =
                 let found = whereis_name(n)
                 match found
                   Some(pid) -> tell(pid, 5)
                   None() -> ()
             end
             """)
  end

  test "register / whereis / unregister round-trip on host OTP" do
    src = """
    mod NameDemo
      use Std.Otp
      use Std.Bool
      use Std.Option
      type Cmd = Inc | Dec
      # Register the calling process under a typed name, confirm the lookup finds it, then unregister and
      # confirm the lookup is now empty. Returns %[registered?, found_after?, found_after_unregister_is_none?].
      fn run() -> Effect(Tuple(Bool, Bool, Bool)) =
        let n: Name(Cmd) = name(:cure_name_test_server)
        let me: Pid(Cmd) = self()
        let reg = register_name(n, me)
        let f1 = whereis_name(n)
        let unreg = unregister_name(n)
        let f2 = whereis_name(n)
        %[reg, is_some(f1), is_none(f2)]
    """

    {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert apply(mod, :run, []) == {true, true, true}
  end
end
