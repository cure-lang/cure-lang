defmodule Cure.Elab.Slice1RunTest do
  @moduledoc """
  Slice-1 acceptance (design spec §6): construct a sequential composition and run
  one evaluation step end-to-end — from `.cure` source, through elaboration +
  totality certification, to evaluating the dependent `match` (the operational
  semantics step) on a constructed dependent value.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Eval}
  alias Cure.Elab.Program

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

  # nullary constructor value
  defp c(name), do: {:ctor, Cure.Elab.Name.qualify("Main", name), []}

  defp apply_all(fun, args), do: Enum.reduce(args, fun, fn a, acc -> Eval.apply(acc, a) end)

  test "the whole §6 program elaborates and certifies from source" do
    assert {:ok, env} = Program.elaborate(@src)
    assert Env.get_def(env, :compose)
    assert Env.get_def(env, :run)
  end

  test "running the match on seq(prim, prim) evaluates to the seq branch" do
    {:ok, env} = Program.elaborate(@src)

    prim = {:ctor, :"Main#prim", [c(:SVNil), c(:SVNil)]}
    # seq(prim, prim) : SF(SVNil, SVNil, andd(Causal, Causal)) — full (unerased) form
    seq =
      {:ctor, :"Main#seq", [c(:SVNil), c(:SVNil), c(:Causal), c(:SVNil), c(:Causal), prim, prim]}

    run = Eval.eval(Env.get_def(env, :run).body, [])
    indices = [Eval.eval(c(:SVNil), []), Eval.eval(c(:SVNil), []), Eval.eval(c(:Causal), [])]
    result = apply_all(run, indices ++ [Eval.eval(seq, [])])

    assert {:vctor, :"Main#Dcoupled", []} = result
  end

  test "running the match on a prim value evaluates to the prim branch" do
    {:ok, env} = Program.elaborate(@src)

    prim = {:ctor, :"Main#prim", [c(:SVNil), c(:SVNil)]}
    run = Eval.eval(Env.get_def(env, :run).body, [])
    indices = [Eval.eval(c(:SVNil), []), Eval.eval(c(:SVNil), []), Eval.eval(c(:Causal), [])]
    result = apply_all(run, indices ++ [Eval.eval(prim, [])])

    assert {:vctor, :"Main#Causal", []} = result
  end
end
