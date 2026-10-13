defmodule Cure.Elab.ProgramCodegenGateTest do
  # The codegen gate must have ONE Final-Core enforcement mechanism
  # (Validator.release_config) — not a second, hand-maintained hole walker that
  # can drift. The live gate is `Emit.reject_holes/2`, reached through the public
  # `Emit.compile_forms/2` entry; the former `Program.check_codegen_ready/1`
  # duplicated that invariant and was removed (audit §4.2). These tests now
  # exercise the real emit boundary, so they pin the gate that production uses.
  # (K2 re-spell: the carrier is a builtin-op global spine — the validator
  # descends into app args, catching the same leak the emit boundary catches;
  # K3 single enforcement point.)
  use ExUnit.Case, async: true
  alias Cure.Core.Env
  alias Cure.Elab.Emit

  test "codegen gate refuses a hole hidden in a builtin-op spine argument" do
    body = {:app, {:app, {:global, :int_add}, {:hole, "x"}}, {:int_lit, 1}}
    env = Env.empty() |> Env.add_def(:tainted, {:type, 0}, body, [])
    assert {:error, {:unfilled_hole, :tainted}} = Emit.compile_forms(env, :GateTainted)
  end

  test "codegen gate still refuses a plain body hole" do
    env = Env.empty() |> Env.add_def(:h, {:type, 0}, {:hole, "body"}, [])
    assert {:error, {:unfilled_hole, :h}} = Emit.compile_forms(env, :GateH)
  end

  test "codegen gate accepts a hole-free program" do
    env = Env.empty() |> Env.add_def(:clean, {:type, 0}, {:int_lit, 42}, [])
    assert {:ok, _forms} = Emit.compile_forms(env, :GateClean)
  end
end
