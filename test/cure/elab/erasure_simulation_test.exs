defmodule Cure.Elab.ErasureSimulationTest do
  @moduledoc """
  Bounded §8.3 evidence: kernel-check source definitions, evaluate their original
  Core bodies, and independently emit and execute BEAM. The source oracle never
  calls erasure. These tests are not a general simulation or divergence proof.
  """
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Core.{Env, Eval, Kernel, Normalise}
  alias Cure.Elab.{Emit, Program}

  @source """
  mod SoundnessErasureSimulation
    type Duo = Both(Int, Int)
    type Tag = Only
    fn left(d: Duo) -> Int = match d
      Both(x, y) -> x
    fn right(d: Duo) -> Int = match d
      Both(x, y) -> y
    pub fn select_left() -> Int = left(Both(11, 22))
    pub fn select_right() -> Int = right(Both(11, 22))
    pub fn identity_let(x: Int) -> Int =
      let y = x
      y
    pub fn nested_let(x: Int) -> Int =
      let y = x
      let z = y
      z
    pub fn drop(@erased witness: Tag, x: Int) -> Int = x
    pub fn call_drop(x: Int) -> Int = drop(Only(), x)
  """

  setup_all do
    assert {:ok, tokens} = Lexer.tokenize(@source, emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, emit_events: false)
    assert {:ok, env, locals} = Program.check_ast_with_locals(ast)

    for name <- locals do
      assert :ok = Kernel.check_def(env, name)
    end

    module = Program.module_atom(ast)
    assert {:ok, ^module} = Emit.compile_and_load(env, module: module, functions: locals)

    on_exit(fn ->
      :code.purge(module)
      :code.delete(module)
    end)

    {:ok, env: env, emitted_module: module}
  end

  defp source_integer(env, name, arguments) do
    %{body: body} = Env.get_def(env, name)

    assert {:vint, value} =
             body
             |> Eval.eval([])
             |> Eval.apply_spine(Enum.map(arguments, &{:vint, &1}))
             |> Normalise.whnf_value(env)

    value
  end

  test "multi-field cases preserve first and last field order through global calls", context do
    for {name, expected} <- [select_left: 11, select_right: 22] do
      assert source_integer(context.env, name, []) == expected
      assert apply(context.emitted_module, name, []) == expected
    end
  end

  test "direct and nested administrative identities preserve results", context do
    for name <- [:identity_let, :nested_let], input <- [-42, 0, 73] do
      source = source_integer(context.env, name, [input])
      assert source == input
      assert apply(context.emitted_module, name, [input]) == source
    end
  end

  test "an erased argument is absent from runtime arity but its checked call still agrees", context do
    %{quantities: quantities} = Env.get_def(context.env, :drop)
    assert [:erased, :unrestricted] = quantities
    assert function_exported?(context.emitted_module, :drop, 1)
    refute function_exported?(context.emitted_module, :drop, 2)

    for input <- [-42, 0, 73] do
      source = source_integer(context.env, :call_drop, [input])
      assert source == input
      assert apply(context.emitted_module, :call_drop, [input]) == source
      assert apply(context.emitted_module, :drop, [input]) == source
    end
  end
end
