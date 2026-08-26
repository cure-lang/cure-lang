defmodule Cure.Elab.DoBlockTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.Program

  test "do accepts newline-indented effect binds with <-" do
    source = """
    mod M
      @extern(:erlang, :abs, 1)
      fn effect_abs(n: Int) -> Effect(Int)
      fn value(n: Int) -> Int = unsafe run do
        result <- effect_abs(n)
        result
    end
    """

    assert {:ok, tokens} = Lexer.tokenize(source)
    assert {:ok, ast} = Parser.parse(tokens, emit_events: false)
    assert {:ok, env} = Program.elaborate(source)
    assert %{body: body} = Cure.Core.Env.get_def(env, :value)
    assert body != nil
    assert has_do_bind?(ast)
  end

  test "a do block supports multiple effect binds" do
    source = """
    mod M
      @extern(:erlang, :abs, 1)
      fn effect_abs(n: Int) -> Effect(Int)
      fn value(n: Int) -> Int = unsafe run do
        result <- effect_abs(n)
        doubled <- effect_abs(result)
        doubled
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    assert %{body: body} = Cure.Core.Env.get_def(env, :value)
    assert body != nil
  end

  defp has_do_bind?({:assignment, meta, _children}), do: Keyword.get(meta, :do_bind) == true

  defp has_do_bind?({_tag, _meta, children}) when is_list(children),
    do: Enum.any?(children, &has_do_bind?/1)

  defp has_do_bind?(_), do: false
end
