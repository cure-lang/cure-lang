defmodule Cure.Elab.StructuralPatternTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.{Emit, Program}

  test "open records and repeated tuple variables share the typed pattern path" do
    source = """
    mod StructuralPatterns
      rec Person
        name: String
        age: Int

      fn adult(p: Person) -> Bool =
        match p
          Person{age: age} when age >= 18 -> true
          _ -> false

      fn diagonal(t: Tuple(Int, Int)) -> Bool =
        match t
          %[x, x] -> true
          _ -> false

      fn main() -> Int =
        pickup
          adult(Person{name: "Ada", age: 36}) -> 1
          else -> 0
    end
    """

    assert {:ok, env} = Program.elaborate(source)

    assert {:ok, module} =
             Emit.compile_and_load(env,
               module: :"Cure.StructuralPatterns",
               functions: [:adult, :diagonal, :main]
             )

    assert module.main() == 1
  end
end
