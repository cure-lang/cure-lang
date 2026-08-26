defmodule Cure.Stdlib.DependentRegexClassBoundaryTest do
  use ExUnit.Case, async: false

  # `String` is nominal -- `rec String { characters: List(Char) }` -- so it
  # erases to the tagged pair `{:String, code_points}`. Every function here takes
  # a `String` subject; the `Option(Char)` results stay bare code points, since
  # `Char` erases to its integer.
  defp cure_string(chars), do: {:String, chars}

  setup_all do
    source = """
    mod RegexClassBoundaryRuntime
      use Std.Regex
      fn mixed_class(input: String) -> Option(Char) = parse_full(/[A-F\\d_]/i, input)
      fn unicode_class_digit(input: String) -> Option(Char) = parse_full(/[\\d]/u, input)
      fn class_not_digit(input: String) -> Option(Char) = parse_full(/[\\D]/, input)
      fn negated_class_digit(input: String) -> Option(Char) = parse_full(/[^\\d]/, input)
      fn class_horizontal_or_vertical(input: String) -> Option(Char) = parse_full(/[\\h\\v]/, input)
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    {:ok, runtime_module: module}
  end

  test "escaped classes compose inside bracket classes with options and negation", %{runtime_module: module} do
    assert apply(module, :mixed_class, [cure_string([?b])]) == {:some, ?b}
    assert apply(module, :mixed_class, [cure_string([?7])]) == {:some, ?7}
    assert apply(module, :mixed_class, [cure_string([?_])]) == {:some, ?_}
    assert apply(module, :mixed_class, [cure_string([?z])]) == :none
    assert apply(module, :unicode_class_digit, [cure_string([?١])]) == {:some, ?١}
    assert apply(module, :class_not_digit, [cure_string([?a])]) == {:some, ?a}
    assert apply(module, :class_not_digit, [cure_string([?1])]) == :none
    assert apply(module, :negated_class_digit, [cure_string([?a])]) == {:some, ?a}
    assert apply(module, :negated_class_digit, [cure_string([?1])]) == :none
    assert apply(module, :class_horizontal_or_vertical, [cure_string([?\t])]) == {:some, ?\t}
    assert apply(module, :class_horizontal_or_vertical, [cure_string([?\n])]) == {:some, ?\n}
  end
end
