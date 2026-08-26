defmodule Cure.Compiler.DependentCodegenTest do
  @moduledoc """
  End-to-end through the *real* compiler (`Cure.Compiler.compile_and_load`): a
  dependent `.cure` module is kernel-checked, {0,ω}-erased, and emitted as real
  BEAM. The Slice-1 `step` then executes as bytecode loaded into the VM — the
  dependent types are surfaced in the Cure language, not a side channel.
  """
  use ExUnit.Case, async: false

  @src """
  mod Slice1Cg
    type Dec = Dcoupled | Causal
    type Sig = CSig | ESig
    type SVDesc = SVNil | SVCons(Sig, SVDesc)
    fn andd(x: Dec, y: Dec) -> Dec = x
    type SF indices (as: SVDesc, bs: SVDesc, d: Dec)
      prim : SF(as, bs, Causal)
      seq : SF(as, bs, d1) -> SF(bs, cs, d2) -> SF(as, cs, andd(d1, d2))
    fn compose({as: SVDesc}, {bs: SVDesc}, {cs: SVDesc}, {d1: Dec}, {d2: Dec}, l: SF(as, bs, d1), r: SF(bs, cs, d2)) -> SF(as, cs, andd(d1, d2)) = seq(l, r)
    fn run({as: SVDesc}, {bs: SVDesc}, {d: Dec}, s: SF(as, bs, d)) -> Dec = match s
      prim() -> Causal
      seq(l, r) -> Dcoupled
  end
  """

  test "the real compiler emits and loads a dependent module; step runs as BEAM" do
    assert {:ok, mod} = Cure.Compiler.compile_and_load(@src, emit_events: false)
    assert mod == :"Cure.Slice1Cg"

    assert apply(mod, :compose, [:prim, :prim]) == {:seq, :prim, :prim}
    assert apply(mod, :run, [:prim]) == :Causal
    assert apply(mod, :run, [{:seq, :prim, :prim}]) == :Dcoupled

    composed = apply(mod, :compose, [:prim, :prim])
    assert apply(mod, :run, [composed]) == :Dcoupled
  end

  @holed """
  mod Slice1Hole
    type Dec = Dcoupled | Causal
    type Sig = CSig | ESig
    type SVDesc = SVNil | SVCons(Sig, SVDesc)
    fn andd(x: Dec, y: Dec) -> Dec = x
    type SF indices (as: SVDesc, bs: SVDesc, d: Dec)
      prim : SF(as, bs, Causal)
      seq : SF(as, bs, d1) -> SF(bs, cs, d2) -> SF(as, cs, andd(d1, d2))
    fn sketch({as: SVDesc}, {bs: SVDesc}, s: SF(as, bs, Causal)) -> Dec = ?todo
  end
  """

  test "a dependent module with an unfilled hole is refused by the compiler" do
    assert {:error, {:codegen_error, {:unfilled_hole, details}}} =
             Cure.Compiler.compile_and_load(@holed, emit_events: false)

    assert details.definition == :"Slice1Hole#sketch"

    assert binary_part(@holed, details.span.start_byte, details.span.end_byte - details.span.start_byte) ==
             "?todo"
  end
end
