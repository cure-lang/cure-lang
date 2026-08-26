defmodule Cure.Stdlib.DependentRegexCaptureDecisionTest do
  use ExUnit.Case, async: false

  setup_all do
    source = ~S'''
    mod RegexCaptureDecisions
      use Std.Regex.Syntax.Model
      use Std.Regex.Core
      use Std.Regex.Runtime

      fn compatible_layout() -> Bool = match literal_capture_layout_decision(
        [LiteralCaptureSlotInfo(Z(), Some("word"))],
        [LiteralCaptureSlotInfo(Z(), Some("word"))]
      )
        LiteralCaptureLayoutsCompatible() -> true
        LiteralCaptureLayoutsIncompatible() -> false

      fn incompatible_layout() -> Bool = match literal_capture_layout_decision(
        [LiteralCaptureSlotInfo(Z(), Some("word"))],
        [LiteralCaptureSlotInfo(S(Z()), Some("word"))]
      )
        LiteralCaptureLayoutsCompatible() -> false
        LiteralCaptureLayoutsIncompatible() -> true

      fn participated_slot() -> Bool = match capture_participation_decision(
        Z(),
        [EndCaptureSlot(Z())]
      )
        CaptureParticipatedByRoutine() -> true
        CaptureAbsentByRoutine() -> false

      fn absent_slot() -> Bool = match capture_participation_decision(
        Z(),
        [EndCaptureSlot(S(Z()))]
      )
        CaptureParticipatedByRoutine() -> false
        CaptureAbsentByRoutine() -> true
    end
    '''

    assert {:ok, runtime_module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    {:ok, runtime_module: runtime_module}
  end

  test "layout decisions carry checked compatible and incompatible cases", %{runtime_module: module} do
    assert apply(module, :compatible_layout, [])
    assert apply(module, :incompatible_layout, [])
  end

  test "participation decisions distinguish a closed slot from another slot", %{runtime_module: module} do
    assert apply(module, :participated_slot, [])
    assert apply(module, :absent_slot, [])
  end
end
