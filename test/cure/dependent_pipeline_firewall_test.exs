defmodule Cure.DependentPipelineFirewallTest do
  @moduledoc """
  Firewall: the dependent pipeline (`lib/cure/elab/*` + `lib/cure/core/*`) must
  NEVER reference the classic pathway (Types.*, Codegen, PatternCompiler, the
  fsm/actor/sup/app runtimes, optimizer/PGO, ProtocolRegistry). The classic
  pathway is slated for deletion once the dependent pipeline reaches full
  value-surface parity (2026-07-09 rip-out program); until then, any new
  kernel-founded feature that wires into classic code re-couples the pipelines
  and must be caught here — not at rip-out time.

  Legitimate front-end deps (Lexer/Parser/BeamWriter) are NOT matched.
  """
  use ExUnit.Case, async: true

  @forbidden ~r/Cure\.(Types|FSM|Actor|Sup\.|App\.|Optimizer|PGO)|Cure\.Compiler\.(Codegen|PatternCompiler)|ProtocolRegistry/

  test "lib/cure/elab and lib/cure/core never reference the classic pathway" do
    offenders =
      (Path.wildcard("lib/cure/elab/**/*.ex") ++ Path.wildcard("lib/cure/core/**/*.ex"))
      |> Enum.filter(fn path -> File.read!(path) =~ @forbidden end)

    assert offenders == [],
           "dependent-pipeline files reference the classic pathway (wire to " <>
             "lib/cure/elab / lib/cure/core equivalents instead): #{inspect(offenders)}"
  end
end
