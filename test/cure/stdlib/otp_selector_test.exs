defmodule Cure.Stdlib.OtpSelectorTest do
  @moduledoc """
  `Std.Otp.Selector(p)` — typed selective receive (Gleam-style). A process owns several `Subject`s of DIFFERENT
  message types; a `Selector` maps each into a common payload `p` via `select_map`, and `selector_receive`
  returns whichever arrives first, typed. This is the sanctioned multi-channel receive (Cure otherwise rejects
  raw `receive`). Tests elaborate the surface and RUN it on host OTP: two subjects merged into one sum type,
  received by tag; and timeout -> None.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "selector surface elaborates: heterogeneous subjects map into one payload" do
    assert {:ok, _} =
             Program.elaborate("""
             mod App
               use Std.Otp
               type Cmd = Inc | Dec
               type Note = Hello | Bye
               type Event = CmdEv(Cmd) | NoteEv(Note)
               fn build(c: Subject(Cmd), n: Subject(Note)) -> Selector(Event) =
                 let s0 = new_selector()
                 let s1 = select_map(s0, c, fn(x) -> CmdEv(x))
                 select_map(s1, n, fn(y) -> NoteEv(y))
               fn get(sel: Selector(Event)) -> Effect(Option(Event)) = selector_receive(sel, 100)
             end
             """)
  end

  test "one process, two subjects of different types, received via a selector into a sum payload" do
    src = """
    mod SelDemo
      use Std.Otp
      type Cmd = Inc | Dec
      type Note = Hello | Bye
      type Event = CmdEv(Cmd) | NoteEv(Note)
      fn run() -> Effect(Tuple(Option(Event), Option(Event))) =
        let commands: Subject(Cmd) = new_subject()
        let notes: Subject(Note) = new_subject()
        let s0 = new_selector()
        let s1 = select_map(s0, commands, fn(x) -> CmdEv(x))
        let sel = select_map(s1, notes, fn(y) -> NoteEv(y))
        let a = subject_send(notes, Hello())
        let b = subject_send(commands, Dec())
        let first = selector_receive(sel, 100)
        let second = selector_receive(sel, 100)
        %[first, second]
    """

    {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    # Both messages arrive in the one mailbox; the selector dispatches each by its subject's tag and maps it into
    # the Event payload. Hello was sent first, so it is received first. Ctor reps: CmdEv(Dec) -> {:CmdEv, :Dec}.
    assert apply(mod, :run, []) == {{:some, {:NoteEv, :Hello}}, {:some, {:CmdEv, :Dec}}}
  end

  test "the Gleam-style pipe pipeline builds and runs a selector (multi-line |>)" do
    # Ergonomic surface: `new_selector() |> select_map(..) |> select_map(..)` then `selector_receive`, matching
    # Gleam's pipe style. The payload annotation seeds new_selector's return-only type parameter.
    src = """
    mod SelPipe
      use Std.Otp
      type Cmd = Inc | Dec
      type Note = Hello | Bye
      type Event = CmdEv(Cmd) | NoteEv(Note)
      fn run() -> Effect(Option(Event)) =
        let commands: Subject(Cmd) = new_subject()
        let notes: Subject(Note) = new_subject()
        let a = subject_send(notes, Hello())
        let sel: Selector(Event) =
          new_selector() |>
          select_map(commands, fn(c) -> CmdEv(c)) |>
          select_map(notes, fn(n) -> NoteEv(n))
        selector_receive(sel, 100)
    """

    {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert apply(mod, :run, []) == {:some, {:NoteEv, :Hello}}
  end

  test "selector_receive times out to None when nothing selected arrives" do
    src = """
    mod SelTimeout
      use Std.Otp
      type Cmd = Inc | Dec
      fn run() -> Effect(Option(Cmd)) =
        let c: Subject(Cmd) = new_subject()
        let sel = select(new_selector(), c)
        selector_receive(sel, 5)
    """

    {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert apply(mod, :run, []) == :none
  end
end
