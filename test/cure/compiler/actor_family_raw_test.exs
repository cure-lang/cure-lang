defmodule Cure.Compiler.ActorFamilyRawTest do
  use ExUnit.Case, async: false
  @moduletag timeout: 180_000

  # §1e Mechanism A: the ActorDefinition family gains a raw-body branch — an
  # alternative to the `on_cast` Cases branch. A raw `handle_cast` body is a
  # full GenServer callback result (e.g. `%[:noreply, state]` or a `pickup`
  # dispatch) spliced verbatim, NOT a set of Cases arms wrapped in `:noreply`.
  # This lets the ONE family host both the derived (Cases) surface and the
  # Tier-0 raw surface, so the 15 positional raw templates can share the
  # family's single emitter instead of each re-spelling a full module.

  test "family actor accepts a raw handle_cast body with an explicit message type" do
    source = """
    mod M
      use Std.Actor

      actor Cure.Generated.RawFamilyCast
        state Int
        messages Atom
        handle_cast
          %[:noreply, state]
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert module == :"Cure.M"
    assert apply(:"Cure.Generated.RawFamilyCast", :handle_cast, [:ping, 7]) == {:noreply, 7}

    assert {:reply, _unit, 7} =
             apply(:"Cure.Generated.RawFamilyCast", :handle_call, [:unexpected, self(), 7])

    assert apply(:"Cure.Generated.RawFamilyCast", :init, [3]) == {:ok, 3}
    assert {:ok, pid} = apply(:"Cure.Generated.RawFamilyCast", :start_link, [5])
    assert :gen_server.cast(pid, :ping) == :ok
    :gen_server.stop(pid)
  end

  test "family raw handle_cast without a messages declaration is polymorphic in the message" do
    # No `messages` field: the family's raw branch must emit a message-polymorphic
    # `handle_cast` (an inline free type var at the callback, NOT a module-level
    # `typealias Message = m` with a free `m`, which the kernel cannot resolve).
    source = """
    mod M
      use Std.Actor

      actor Cure.Generated.RawFamilyNoMsg
        state Int
        handle_cast
          %[:noreply, state]
    """

    assert {:ok, _module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(:"Cure.Generated.RawFamilyNoMsg", :handle_cast, [:anything, 7]) == {:noreply, 7}
    assert apply(:"Cure.Generated.RawFamilyNoMsg", :handle_cast, [42, 7]) == {:noreply, 7}
  end

  test "family raw handle_cast body may branch on the message with pickup" do
    source = """
    mod M
      use Std.Actor

      actor Cure.Generated.RawFamilyPickup
        state Int
        messages Atom
        handle_cast
          pickup
            message == :inc -> %[:noreply, state + 1]
            else -> %[:noreply, state]
    """

    assert {:ok, _module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(:"Cure.Generated.RawFamilyPickup", :handle_cast, [:inc, 4]) == {:noreply, 5}
    assert apply(:"Cure.Generated.RawFamilyPickup", :handle_cast, [:other, 4]) == {:noreply, 4}
  end

  test "family raw handle_cast body may be a match with full-result arms" do
    # A raw handle_cast whose body is a `match` on the message returning full
    # `%[:noreply, _]` results must splice VERBATIM. The family raw branch must
    # NOT re-wrap the arms in another `:noreply` — doing so double-wraps to
    # `%[:noreply, %[:noreply, _]]`, which breaks the callback's
    # `Effect(Tuple(Atom, State))` type (the nested tuple is not `State`) and
    # surfaces as `:ctor_requires_checking_mode` on the inner Sigma. Regression
    # pin for the raw/Cases emitter split (§1e wall 4).
    source = """
    mod M
      use Std.Actor

      type Cmd = Inc | Dec

      actor Cure.Generated.RawFamilyMatch
        state Int
        messages Cmd
        handle_cast
          match message
            Inc -> %[:noreply, state + 1]
            Dec -> %[:noreply, state - 1]
    """

    assert {:ok, _module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(:"Cure.Generated.RawFamilyMatch", :handle_cast, [:Inc, 4]) == {:noreply, 5}
    assert apply(:"Cure.Generated.RawFamilyMatch", :handle_cast, [:Dec, 4]) == {:noreply, 3}
  end

  @tag timeout: 120_000
  test "a bare (mod-less) computed raw actor is the program's top-level module" do
    # A `becomes lift module name` template yields a bare top-level `lift_module`
    # at parse time, so `compile_and_load` returns the actor module itself. A
    # computed/family expansion instead wraps its single lifted module in a
    # `:block`, which (pre-fix) fell through to an empty `Cure.Main` wrapper. This
    # pins in-place module identity for the computed path so bare-source guards
    # (container_macro_test:186/204/213) hold once terse heads route through the
    # shared family emitter.
    source = """
    actor Cure.Generated.BareTopRawCast
      state Int
      messages Atom
      handle_cast
        %[:noreply, state]
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert module == :"Cure.Generated.BareTopRawCast"
    assert apply(module, :handle_cast, [:ping, 7]) == {:noreply, 7}
  end
end
