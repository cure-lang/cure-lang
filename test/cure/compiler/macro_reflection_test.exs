defmodule Cure.Compiler.MacroReflectionTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.MacroReflection
  alias Cure.Elab.Program

  test "resolves definitions and enumerates constructors from a real environment" do
    source = """
    mod M
      type Flag = Off | On
      fn id(x: Int) -> Int = x
    """

    assert {:ok, env} = Program.elaborate(source)
    assert {:ok, %{kind: :definition, name: :"M#id", type: _}} = MacroReflection.resolve(env, "id")
    assert {:ok, constructors} = MacroReflection.constructors(env, "Flag")
    assert Enum.map(constructors, & &1.name) |> Enum.sort() == [:"M#Off", :"M#On"]
    assert {:error, :not_found} = MacroReflection.resolve(env, "missing")
  end

  test "infers quoted expressions through the dependent elaborator" do
    assert {:ok, env} = Program.elaborate("mod M\n  fn id(x: Int) -> Int = x\n")
    quoted = {:literal, [subtype: :integer], 1}

    assert {:ok, {:data, :"Std.Int#Int", [], []}} = MacroReflection.infer(quoted, env)
  end

  test "expands quoted ASTs and lifts declarations append-only" do
    assert {:ok, env} = Program.elaborate("mod M\n  fn id(x: Int) -> Int = x\n")
    quoted = {:literal, [subtype: :integer], 1}

    assert {:ok, ^quoted} = MacroReflection.expand(quoted, env)

    first = {:function_def, [name: "first"], []}
    second = {:function_def, [name: "second"], []}
    assert {:ok, [^first, ^second]} = MacroReflection.lift([first, second])
    assert {:error, :invalid_lift_declaration} = MacroReflection.lift([first, 42])
    assert env == env
  end
end
