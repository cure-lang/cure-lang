defmodule Cure.Elab.PatternLetTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.{Emit, Program}

  test "pattern-valued let uses the ordinary typed pattern path" do
    source = """
    mod PatternLet
      fn pair_sum() -> Int =
        let %[a, b] = %[3, 4]
        a + b

      fn main() -> Int = pair_sum() + 5
    end
    """

    assert {:ok, env} = Program.elaborate(source)

    assert {:ok, module} =
             Emit.compile_and_load(env,
               module: :"Cure.PatternLet",
               functions: [:pair_sum, :main]
             )

    assert module.main() == 12
  end
end
