defmodule Cure.Stdlib.OtpSubjectTest do
  @moduledoc """
  `Std.Otp.Subject(m)` — a typed message address `{owner_pid, tag_ref}` in the style of Gleam's `Subject`. Unlike
  `Pid(m)` (one message type per process), a process can own SEVERAL subjects of different types; a send delivers
  a TAGGED message to the owner and a receive matches that tag, so channels never cross. These tests both
  elaborate the typed surface and RUN it on host OTP: a round-trip through one subject, and two subjects of
  DIFFERENT message types owned by one process received independently.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  defp app(body) do
    Program.elaborate("mod App\n  use Std.Otp\n#{body}end\n")
  end

  describe "typed surface elaborates" do
    test "new_subject / subject_send / subject_receive are effect-typed and message-checked" do
      assert {:ok, _} =
               app("""
                 type Cmd = Inc | Dec
                 fn mk() -> Effect(Subject(Cmd)) = new_subject()
                 fn go(s: Subject(Cmd), c: Cmd) -> Effect(Unit) = subject_send(s, c)
                 fn get(s: Subject(Cmd)) -> Effect(Option(Cmd)) = subject_receive(s, 100)
               """)
    end

    test "sending the wrong message type to a subject is a compile error" do
      assert {:error, _} =
               app("""
                 type Cmd = Inc | Dec
                 fn go(s: Subject(Cmd)) -> Effect(Unit) = subject_send(s, 5)
               """)
    end
  end

  describe "runs on host OTP" do
    test "a message round-trips through one subject" do
      src = """
      mod SubjDemo
        use Std.Otp
        type Cmd = Inc | Dec
        fn run() -> Effect(Option(Cmd)) =
          let s: Subject(Cmd) = new_subject()
          let sent = subject_send(s, Inc())
          subject_receive(s, 100)
      """

      {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)

      # run/0 performs the effects and returns the received Option(Cmd). Inc() -> :Inc; Cure Option is lowercase: Some(x) -> {:some, x}.
      assert apply(mod, :run, []) == {:some, :Inc}
    end

    test "two subjects of DIFFERENT types are received independently by one owner" do
      src = """
      mod TwoSubj
        use Std.Otp
        type Cmd = Inc | Dec
        type Note = Hello | Bye
        fn run() -> Effect(Tuple(Option(Cmd), Option(Note))) =
          let commands: Subject(Cmd) = new_subject()
          let notes: Subject(Note) = new_subject()
          let s1 = subject_send(notes, Hello())
          let s2 = subject_send(commands, Dec())
          let got_cmd = subject_receive(commands, 100)
          let got_note = subject_receive(notes, 100)
          %[got_cmd, got_note]
      """

      {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
      # Each subject's unique tag keeps the two channels separate despite arriving in the same mailbox.
      assert apply(mod, :run, []) == {{:some, :Dec}, {:some, :Hello}}
    end

    test "receive times out to None when nothing is sent" do
      src = """
      mod SubjTimeout
        use Std.Otp
        type Cmd = Inc | Dec
        fn run() -> Effect(Option(Cmd)) =
          let s: Subject(Cmd) = new_subject()
          subject_receive(s, 5)
      """

      {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
      assert apply(mod, :run, []) == :none
    end
  end
end
