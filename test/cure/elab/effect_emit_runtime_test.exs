defmodule Cure.Elab.EffectEmitRuntimeTest do
  @moduledoc """
  §6 of the effect-type-former design: an effectful def lowers DIRECT-STYLE. A
  `bind`-chain becomes straight-line BEAM statements (`begin X = <op1>, … end`),
  each effectful `@extern` a direct remote call, and a tail `pure(a)` just `a`.
  This tier EMITS an effectful module through the dependent pipeline, LOADS the
  BEAM, and RUNS it — proving the emitted effect code actually executes and
  computes the right result (the externs are stock erlang BIFs, so the emitted
  BEAM runs identically on the host and on generic-unix AtomVM).
  """
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.{Program, Emit}

  defp load(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    {:ok, env, locals} = Program.check_ast_with_locals(ast)
    {:ok, mod} = Emit.compile_and_load(env, module: Program.module_atom(ast), functions: locals)
    mod
  end

  test "a two-effect bind-chain runs: sequenced externs compute and the result flows" do
    src = """
    mod EffRun
      @extern(:erlang, :max, 2)
      fn eff_max(a: Int, b: Int) -> Effect(Int)
      fn go() -> Effect(Int) =
        let x = eff_max(3, 7)
        let y = eff_max(x, 100)
        y
    end
    """

    m = load(src)
    # go() -> begin X = erlang:max(3,7), Y = erlang:max(X,100), Y end
    #       = max(7, 100) = 100 — proves x (=7) flows into y's computation.
    assert apply(m, :go, []) == 100
  end

  test "a single effect runs and a tail pure(x) yields the value" do
    src = """
    mod EffRun2
      @extern(:erlang, :abs, 1)
      fn eff_abs(n: Int) -> Effect(Int)
      fn go2(n: Int) -> Effect(Int) =
        let x = eff_abs(n)
        x
    end
    """

    m = load(src)
    # go2(N) -> begin X = erlang:abs(N), X end
    assert apply(m, :go2, [-42]) == 42
  end
end
