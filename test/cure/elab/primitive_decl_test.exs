defmodule Cure.Elab.PrimitiveDeclTest do
  @moduledoc """
  `@builtin(:tag) primitive Name` elaborates by confirming the surface name maps
  to its Core node via the marker (spec 2026-07-10-primitive-type-declarations).
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program
  alias Cure.Core.Env

  test "a well-formed primitive declaration confirms its binding" do
    {:ok, env} = Program.elaborate("mod M\n  @builtin(:float) primitive Float\nend\n")
    assert Env.primitive(env, "Float") == {:float_type}
  end

  test "a primitive with no @builtin marker is rejected" do
    assert {:error,
            {:source_context, {:primitive_missing_builtin, "Widget"}, %{expectation_origin: :primitive_declaration}}} =
             Program.elaborate("mod M\n  primitive Widget\nend\n")
  end

  test "a primitive with an unknown @builtin tag is rejected" do
    assert {:error,
            {:source_context, {:unknown_primitive_tag, :sparkle}, %{expectation_origin: :primitive_declaration}}} =
             Program.elaborate("mod M\n  @builtin(:sparkle) primitive Sparkle\nend\n")
  end

  test "a primitive whose tag disagrees with the name's floor is rejected" do
    # Binary's floor is {:binary_type}; tagging it :float contradicts the floor.
    # (Int is no longer a machine primitive — it is the inductive Std.Int#Int
    # family — so the floor-disagreement is exercised on a name still on the floor.)
    assert {:error,
            {:source_context, {:primitive_floor_mismatch, "Binary", {:float_type}, {:binary_type}},
             %{expectation_origin: :primitive_declaration}}} =
             Program.elaborate("mod M\n  @builtin(:float) primitive Binary\nend\n")
  end

  test "`:int` is no longer a legal @builtin primitive tag" do
    # Before the inductive-Int surface flip, `@builtin(:int) primitive Int` was
    # the canonical (and only sanctioned) primitive declaration for Int, and it
    # matched the seeded floor exactly. Now that Int has moved off the primitive
    # floor onto the inductive Std.Int#Int family, `Env.primitive(env, "Int")` is
    # nil, so `confirm_primitive_floor/3` has no floor entry to disagree with —
    # without an explicit rejection here, this declaration would silently
    # succeed and create an incoherent local `Int` binding that only fails much
    # later, at codegen, with a cryptic conversion_failure against the family
    # type. It must be rejected cleanly at the declaration site instead.
    assert {:error, {:source_context, {:unknown_primitive_tag, :int}, %{expectation_origin: :primitive_declaration}}} =
             Program.elaborate("mod M\n  @builtin(:int) primitive Int\nend\n")
  end
end
