defmodule Cure.Elab.EmitHoleFirewallTest do
  # The emit/release boundary is the single trusted enforcement point for "no
  # unfilled obligation ships" (K3). It must validate the *pre-erase* Core body:
  # `Erase.erase` drops erased subterms (the collapsible :case transport's
  # proof scrutinee vanishes wholesale), so a hole hidden in an erased position
  # is invisible to the old erase-then-`has_hole?` gate and shipped silently (#102).
  use ExUnit.Case, async: true
  alias Cure.Core.Env
  alias Cure.Elab.Emit

  # (The primitive `{:rewrite}`-proof versions of the #102 tests were retired
  # with the form itself — group-A removal commit; the :case-transport twins
  # below were cross-checked side by side first.)

  test "emit still refuses a plain body hole" do
    env = Env.empty() |> Env.add_def(:h, {:type, 0}, {:hole, "body"}, [])
    assert {:error, {:unfilled_hole, :h}} = Emit.compile_forms(env, :M, [:h])
  end

  test "emit still accepts a hole-free def (no false positive)" do
    env = Env.empty() |> Env.add_def(:clean, {:type, 0}, {:int_lit, 42}, [])
    assert {:ok, _forms} = Emit.compile_forms(env, :M, [:clean])
  end

  # Phase C twins (add-then-retire): the `{:rewrite}` node retires; the erased
  # position a hole can hide in is now the PROOF SCRUTINEE of the J/subst
  # `:case` transport — `Erase` drops the whole collapsible case (single
  # all-erased-fields `reflexive` branch), so the pre-erase `has_hole?` gate is
  # still all that stands between an unfilled proof obligation and a shipped
  # binary. Same #102 property, new vehicle.
  defp case_transport_with_hole_proof do
    id_branch = {:reflexive, 1, {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}}}
    {:app, {:case, {:hole, "p"}, {:type, 0}, [id_branch]}, {:int_lit, 0}}
  end

  test "emit refuses a hole hiding in the erased proof scrutinee of a :case transport" do
    env = Env.empty() |> Env.add_def(:tainted3, {:type, 0}, case_transport_with_hole_proof(), [])
    assert {:error, {:unfilled_hole, :tainted3}} = Emit.compile_forms(env, :M3, [:tainted3])
  end

  test "compile_and_load refuses a :case-transport proof hole too (same gate)" do
    env = Env.empty() |> Env.add_def(:tainted4, {:type, 0}, case_transport_with_hole_proof(), [])

    assert {:error, {:unfilled_hole, :tainted4}} =
             Emit.compile_and_load(env, module: :M4, functions: [:tainted4])
  end

  # ---------------------------------------------------------------------
  # §8.1 — the firewall on the MACRO-GENERATED (`:lift_module`) path.
  #
  # docs/SOUNDNESS.md §8.1 asks for confirmation that "no emission path
  # bypasses `Emit.reject_holes/2`" plus a regression test asserting
  # `cure compile` fails on a reachable `?goal`. The tests above cover plain
  # bodies and `:case`-transport proof holes; these cover the lifted path that
  # `actor`/`sup` macros generate, which reaches emission through
  # `LiftModule.emit/1` -> `Emit.compile_forms/3`.
  #
  # Both paths end at the SAME gate (`Emit.reject_holes/2`), reached
  # differently:
  #
  #   * an ORDINARY definition goes through `Emit.compile_forms/3` directly,
  #     surfacing as `{:codegen_error, {:unfilled_hole, …}}`;
  #   * an ACTOR handler body goes through the lifted path
  #     (`LiftModule.emit/1` -> `Emit.compile_forms/3`), surfacing as
  #     `{:lift_module_error, %{cause: {:unfilled_hole, …}}}`.
  #
  # The third test is the CONTROL: a hole-free actor must still compile and
  # emit callable functions, otherwise the refusal above could be an artifact
  # of actor emission being broken rather than the firewall working.
  # ---------------------------------------------------------------------

  test "§8.1: the real compiler refuses a reachable hole in an ordinary definition" do
    source = """
    mod HoleFirewallOrdinary
      pub fn probe(x: Int) -> Int = ?probe
    """

    assert {:error, {:codegen_error, {:unfilled_hole, details}}} =
             Cure.Compiler.compile_and_load(source, emit_events: false)

    assert details.definition == :"HoleFirewallOrdinary#probe"
  end

  test "§8.1: a hole in an actor handler body is refused BY THE FIREWALL" do
    source = """
    mod HoleFirewallActor
      use Std.Actor

      actor Cure.Generated.Holed
        state Int
        messages Atom
        handle_cast
          %[:noreply, ?handler_hole]
    """

    # This is the lifted (`:lift_module`) emission path: the actor macro
    # expands to a generated module, and `LiftModule.emit/1` routes it through
    # `Emit.compile_forms/3`, which runs `reject_holes`. So an actor-body hole
    # IS caught by the firewall — not merely by macro expansion — and the
    # error carries the exact source span of the hole.
    assert {:error, {:lift_module_error, %{cause: {:unfilled_hole, details}}}} =
             Cure.Compiler.compile_and_load(source, emit_events: false)

    assert details.span.start_line == 8
    assert details.span.start_column == 19
  end

  test "§8.1: a hole-free actor still compiles and emits callable functions" do
    # The control. Without this, the test above could pass because actor
    # emission is broken rather than because the hole was refused.
    source = """
    mod HoleFirewallActorClean
      use Std.Actor

      actor Cure.Generated.Clean
        state Int
        messages Atom
        handle_cast
          %[:noreply, state]
    """

    assert {:ok, _mod} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(:"Cure.Generated.Clean", :handle_cast, [:ping, 7]) == {:noreply, 7}
  end
end
