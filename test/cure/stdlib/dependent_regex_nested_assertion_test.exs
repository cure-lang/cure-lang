defmodule Cure.Stdlib.DependentRegexNestedAssertionTest do
  use ExUnit.Case, async: false

  test "nested capture-free positive lookahead composes without consuming input" do
    source = """
    mod NestedRegexAssertion
      use Std.Regex
      fn accepted() -> Bool = matches(/a(?=b(?=c))bc/, "abc")
      fn rejected() -> Bool = matches(/a(?=b(?=c))bc/, "abd")
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :accepted, [])
    refute apply(module, :rejected, [])
  end
end
