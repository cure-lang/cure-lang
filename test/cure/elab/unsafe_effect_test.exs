defmodule Cure.Elab.UnsafeEffectTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.{Emit, Program}

  defp ast!(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false, file: "unsafe_effect.cure")
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  test "unsafe is lexed and attached to the call" do
    ast = ast!("mod M\n  fn f() -> Int = unsafe run(x)\nend\n")
    assert {:function_call, meta, _args} = find_call(ast, "run")
    assert Keyword.get(meta, :unsafe) == true
  end

  test "run is an ordinary function and needs no unsafe marker" do
    source = """
    mod UnsafeRunMissing
      @extern(:erlang, :abs, 1)
      fn effect(n: Int) -> Effect(Int)
      fn value(n: Int) -> Int = run(effect(n))
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "@unsafe declarations require unsafe at every call site" do
    source = """
    mod UnsafeDeclaration
      @unsafe
      fn danger(n: Int) -> Int = n
      fn value(n: Int) -> Int = danger(n)
    end
    """

    assert {:error, {:source_context, {:unsafe_call_required, details}, _context}} = Program.elaborate(source)
    assert details.callee == "danger"
  end

  test "run unwraps Effect without a runtime wrapper" do
    source = """
    mod UnsafeRunRuntime
      @extern(:erlang, :abs, 1)
      fn effect(n: Int) -> Effect(Int)
      fn value(n: Int) -> Int = run(effect(n))
    end
    """

    {:ok, env, functions} = Program.check_ast_with_locals(ast!(source))

    assert {:ok, UnsafeRunRuntimeCompiled} =
             Emit.compile_and_load(env, module: UnsafeRunRuntimeCompiled, functions: functions)

    assert apply(UnsafeRunRuntimeCompiled, :value, [-42]) == 42
  end

  test "run still type-checks its effect payload" do
    source = """
    mod UnsafeRunType
      @extern(:erlang, :abs, 1)
      fn effect(n: Int) -> Effect(Int)
      fn value(n: Int) -> Bool = run(effect(n))
    end
    """

    assert {:error, _} = Program.elaborate(source)
  end

  defp find_call({:function_call, meta, args}, name) do
    if Keyword.get(meta, :name) == name do
      {:function_call, meta, args}
    else
      Enum.find_value(args, &find_call(&1, name))
    end
  end

  defp find_call({_tag, _meta, children}, name) when is_list(children),
    do: Enum.find_value(children, &find_call(&1, name))

  defp find_call(_other, _name), do: nil
end
