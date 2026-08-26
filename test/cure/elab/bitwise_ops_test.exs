defmodule Cure.Elab.BitwiseOpsTest do
  @moduledoc """
  #2 (Int bitwise delta-globals, spec batch 2026-07-10): the Erlang-faithful
  keyword operators `band`/`bor`/`bxor`/`bsl`/`bsr` (infix) and `bnot` (prefix)
  lower to the Int-only builtin-op globals `int_band`/… (the `int_add` δ-global
  pattern) and evaluate to the BEAM bitwise BIFs. Int-only: there is no float
  twin, so a Float operand rejects at elaboration. Precedence follows Erlang —
  `band` at multiplicative level, `bor`/`bxor`/`bsl`/`bsr` additive, `bnot`
  prefix like `not`.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.Env
  alias Cure.Elab.{Emit, Program}

  defp body(src, name) do
    {:ok, env} = Program.elaborate("mod M\n" <> src <> "end\n")
    Env.get_def(env, name).body
  end

  defp app2(g, a, b), do: {:app, {:app, {:global, g}, a}, b}

  # Builtin ops lower to owner-qualified globals (`Std.Builtin#int_band`), matching
  # both `Builtins.seed`'s registration key and the elaborator's emission.
  defp bop(op), do: Cure.Elab.Name.qualify("Std.Builtin", op)

  # Elaborate a one-def module and RUN the def on the BEAM (end-to-end: surface
  # → Core → Erlang → evaluation). Unique module name so repeated loads never
  # clash.
  defp run(src, name) do
    {:ok, env} = Program.elaborate("mod M\n" <> src <> "end\n")
    modname = :"Cure.BitwiseT#{:erlang.unique_integer([:positive])}"
    {:ok, mod} = Emit.compile_and_load(env, module: modname, functions: [name])
    apply(mod, name, [])
  end

  test "`band` lowers to an int_band global spine (Int-directed)" do
    b = body("  fn f(x: Int) -> Int = x band 6\n", :f)

    assert {:lam, Cure.Core.Grade.unrestricted(), {:data, :"Std.Int#Int", [], []},
            app2(bop(:int_band), {:var, 0}, {:int_lit, 6})} ==
             b
  end

  test "infix bitwise binops evaluate to the BEAM bitwise BIFs" do
    assert run("  fn f() -> Int = 5 band 3\n", :f) == 1
    assert run("  fn f() -> Int = 6 bor 1\n", :f) == 7
    assert run("  fn f() -> Int = 6 bxor 3\n", :f) == 5
    assert run("  fn f() -> Int = 1 bsl 4\n", :f) == 16
    assert run("  fn f() -> Int = 12 bsr 2\n", :f) == 3
  end

  test "`bnot` (prefix) lowers and evaluates (two's-complement)" do
    assert run("  fn f() -> Int = bnot 0\n", :f) == -1
    assert run("  fn f() -> Int = bnot 5\n", :f) == -6
  end

  test "a register-style expression composes with precedence + parens" do
    # `reg bor (1 bsl pin)` — the shape hardware/board code will use.
    assert run("  fn f() -> Int = 4 bor (1 bsl 1)\n", :f) == 6
  end

  test "bitwise is Int-only: a Float operand rejects at elaboration" do
    assert {:error, _} =
             Program.elaborate("mod M\n  fn t(a: Float, b: Float) -> Float = a band b\nend\n")
  end
end
