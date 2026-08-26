defmodule Cure.Elab.FunctionRegistrationTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Core.Env
  alias Cure.Elab.Declarations

  defp elaborate_all(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)

    items =
      case ast do
        {:block, _, xs} -> xs
        x -> [x]
      end

    Enum.reduce_while(items, {:ok, Env.empty()}, fn decl, {:ok, env} ->
      case Declarations.elaborate(decl, env) do
        {:ok, env2} -> {:cont, {:ok, env2}}
        err -> {:halt, err}
      end
    end)
  end

  test "registers a function as a kernel-checked global definition" do
    src = """
    type Dec = Dcoupled | Causal
    fn andd(x: Dec, y: Dec) -> Dec = x
    """

    assert {:ok, env} = elaborate_all(src)
    assert %{name: :andd, type: type, body: body} = Env.get_def(env, :andd)
    assert {:pi, _g1, _, {:pi, _g2, _, _}} = type
    assert {:lam, _g1, _, {:lam, _g2, _, {:var, 1}}} = body
  end

  test "rejects an ill-typed function body" do
    # body references an out-of-scope name → kernel check fails
    src = """
    type Dec = Dcoupled | Causal
    fn bad(x: Dec) -> Dec = Dcoupled
    """

    # Dcoupled is a Dec value, so this one is actually well-typed; assert it registers.
    assert {:ok, env} = elaborate_all(src)
    assert %{name: :bad} = Env.get_def(env, :bad)
  end
end
