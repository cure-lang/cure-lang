defmodule Cure.Stdlib.DependentRegexCollectionApiTest do
  use ExUnit.Case, async: false

  setup_all do
    source = ~S'''
    mod RegexCollectionApi
      use Std.Regex

      fn scanned(input: String) -> List(Match(String)) = scan(/(a+)/, input)
      fn scanned_empty(input: String) -> List(Match(Unit)) = scan(empty(), input)
      fn scanned_multiline(input: String) -> List(Match(Unit)) = scan(/^a/m, input)
    end
    '''

    assert {:ok, runtime_module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    {:ok, runtime_module: runtime_module}
  end

  defp string(chars), do: {:String, chars}

  test "scan returns non-overlapping typed matches with absolute partitions", %{runtime_module: module} do
    assert apply(module, :scanned, [string(~c"xaaayzaa")]) == [
             {:Match, string(~c"aaa"), string(~c"x"), string(~c"aaa"), string(~c"yzaa"), 1, 3},
             {:Match, string(~c"aa"), string(~c"xaaayz"), string(~c"aa"), string(~c""), 6, 2}
           ]
  end

  test "scan advances one Unicode scalar after empty matches and emits the terminal match once", %{runtime_module: module} do
    assert apply(module, :scanned_empty, [string(~c"βx")]) == [
             {:Match, :unit, string(~c""), string(~c""), string(~c"βx"), 0, 0},
             {:Match, :unit, string(~c"β"), string(~c""), string(~c"x"), 1, 0},
             {:Match, :unit, string(~c"βx"), string(~c""), string(~c""), 2, 0}
           ]
  end

  test "scan preserves subject and multiline boundary state between matches", %{runtime_module: module} do
    assert apply(module, :scanned_multiline, [string(~c"a\nab")]) == [
             {:Match, :unit, string(~c""), string(~c"a"), string(~c"\nab"), 0, 1},
             {:Match, :unit, string(~c"a\n"), string(~c"a"), string(~c"b"), 2, 1}
           ]
  end
end
