defmodule Cure.Stdlib.DependentRegexAbsoluteBoundaryTest do
  use ExUnit.Case, async: false

  # `String` is nominal -- `rec String { characters: List(Char) }` -- so it
  # erases to the tagged pair `{:String, code_points}`. These functions take a
  # `String` subject and return `Match(Unit)`, whose three partitions are
  # `String`s, so every string crossing the BEAM boundary here carries the tag.
  defp cure_string(chars), do: {:String, chars}

  setup_all do
    source = """
    mod RegexAbsoluteBoundaryRuntime
      use Std.Regex
      fn absolute_start_search(input: String) -> Option(Match(Unit)) = search(/\\Aabc/m, input)
      fn strict_end_search(input: String) -> Option(Match(Unit)) = search(/abc\\z/, input)
      fn final_end_search(input: String) -> Option(Match(Unit)) = search(/abc\\Z/, input)
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    {:ok, runtime_module: module}
  end

  test "\\A, \\z, and \\Z retain absolute subject semantics", %{runtime_module: module} do
    assert apply(module, :absolute_start_search, [cure_string(~c"x\nabc")]) == :none
    assert apply(module, :strict_end_search, [cure_string(~c"abc\n")]) == :none

    assert apply(module, :final_end_search, [cure_string(~c"abc\n")]) ==
             {:some, {:Match, :unit, cure_string(~c""), cure_string(~c"abc"), cure_string(~c"\n"), 0, 3}}
  end
end
