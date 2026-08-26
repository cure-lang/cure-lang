defmodule Cure.Elab.EmitTest do
  @moduledoc """
  M9.3 — real BEAM emission (design spec §8). The elaborated, totality-certified,
  erased Core is lowered to Erlang abstract forms, compiled with `:compile.forms`,
  loaded into the VM, and executed. This is the honest end of the pipeline: the
  Slice-1 `step` runs as actual BEAM bytecode, not an interpreter walk.
  """
  use ExUnit.Case, async: false
  alias Cure.Elab.{Emit, Program}

  @src """
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
  """

  test "erased constructors and functions compile to a loadable BEAM module" do
    {:ok, env} = Program.elaborate(@src)

    {:ok, mod} =
      Emit.compile_and_load(env, module: :"Cure.Slice1Emit", functions: [:run, :compose])

    # compose erases its five index arguments: compose(L, R) = {seq, L, R}
    assert apply(mod, :compose, [:prim, :prim]) == {:seq, :prim, :prim}

    # run is the operational-semantics step, executing as real bytecode
    assert apply(mod, :run, [:prim]) == :Causal
    assert apply(mod, :run, [{:seq, :prim, :prim}]) == :Dcoupled

    # construct + run one step, end-to-end, on the BEAM
    composed = apply(mod, :compose, [:prim, :prim])
    assert apply(mod, :run, [composed]) == :Dcoupled
  end

  test "emission refuses a function whose body still contains a hole" do
    src = @src <> "\nfn sketch({as: SVDesc}, s: SF(as, as, Causal)) -> Dec = ?todo\n"
    {:ok, env} = Program.elaborate(src)

    assert {:error, {:unfilled_hole, details}} =
             Emit.compile_and_load(env, module: :"Cure.Slice1Hole", functions: [:run, :sketch])

    assert details.definition == :"Main#sketch"
    assert binary_part(src, details.span.start_byte, details.span.end_byte - details.span.start_byte) == "?todo"
  end
end
