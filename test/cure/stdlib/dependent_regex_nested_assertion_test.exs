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

  test "nested assertion observations do not extend the surrounding capture" do
    source = """
    mod NestedAssertionCaptureScope
      use Std.Regex

      fn assertion_outer_capture(input: String) -> Option(String) =
        match search_named(/(?<outer>a(?=b))b/, input)
          None() -> None()
          Some(found) -> named_capture("outer", found)

      fn nested_captures(input: String) -> Option(List(NamedCapture)) =
        match search_named(/(?=(?<outer>a(?=(?<inner>b))))ab/, input)
          None() -> None()
          Some(NamedMatch(_, captures)) -> Some(captures)

    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)

    assert apply(module, :assertion_outer_capture, [{:String, ~c"ab"}]) ==
             {:some, {:String, ~c"a"}}

    assert apply(module, :nested_captures, [{:String, ~c"ab"}]) ==
             {:some,
              [
                {:NamedCapture, {:String, ~c"outer"}, {:some, {:String, ~c"a"}}},
                {:NamedCapture, {:String, ~c"inner"}, {:some, {:String, ~c"b"}}}
              ]}
  end
end
