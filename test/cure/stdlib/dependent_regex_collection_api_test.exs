defmodule Cure.Stdlib.DependentRegexCollectionApiTest do
  use ExUnit.Case, async: false

  alias Antigen.Backend.StreamData, as: Property
  alias Antigen.Gen

  @runs [max_runs: 300, max_run_time: :infinity]

  setup_all do
    source = ~S'''
    mod RegexCollectionApi
      use Std.Regex

      fn scanned(input: String) -> List(Match(String)) = scan(/(a+)/, input)
      fn scanned_empty(input: String) -> List(Match(Unit)) = scan(empty(), input)
      fn scanned_multiline(input: String) -> List(Match(Unit)) = scan(/^a/m, input)
      fn scanned_a(input: String) -> List(Match(Unit)) = scan(/a/, input)

      fn split_basic(input: String) -> List(String) = split_default(/,+/, input)
      fn split_including(input: String) -> List(String) =
        split(/,+/, input, SplitOptions(IncludeSeparators, KeepEmptyParts, UnlimitedSplit))
      fn split_trimmed(input: String) -> List(String) =
        split(/,/, input, SplitOptions(ExcludeSeparators, TrimEmptyParts, UnlimitedSplit))
      fn split_limited(input: String) -> List(String) =
        split(/,/, input, SplitOptions(ExcludeSeparators, KeepEmptyParts, AtMostSplitParts(2)))
      fn split_commas(input: String) -> List(String) = split_default(/,/, input)

      fn bracket(found: Match(String)) -> String = match found
        Match(value, _, _, _, _, _) -> Std.String.concat(Std.String.concat("[", value), "]")

      fn replaced_typed(input: String) -> String = replace(/(\d+)/u, input, bracket)
      fn replaced_literal(input: String) -> String = replace_literal(/\d+/u, input, "X")
      fn replaced_empty(input: String) -> String = replace_literal(empty(), input, "-")
      fn replaced_a(input: String) -> String = replace_literal(/a/, input, "X")
    end
    '''

    assert {:ok, runtime_module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    {:ok, runtime_module: runtime_module}
  end

  defp string(chars), do: {:String, chars}

  defp chars_gen(0), do: Gen.return([])

  defp chars_gen(size) do
    Gen.bind(Gen.member_of([?a, ?b, ?,, ?β]), fn head ->
      Gen.bind(chars_gen(size - 1), fn tail -> Gen.return([head | tail]) end)
    end)
  end

  defp subject_gen do
    Gen.bind(Gen.integer(0, 8), &chars_gen/1)
  end

  test "scan returns non-overlapping typed matches with absolute partitions", %{runtime_module: module} do
    assert apply(module, :scanned, [string(~c"xaaayzaa")]) == [
             {:Match, string(~c"aaa"), string(~c"x"), string(~c"aaa"), string(~c"yzaa"), 1, 3},
             {:Match, string(~c"aa"), string(~c"xaaayz"), string(~c"aa"), string(~c""), 6, 2}
           ]
  end

  test "scan advances one Unicode scalar after empty matches and emits the terminal match once", %{
    runtime_module: module
  } do
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

  test "split exposes inclusion, trimming, and part limits as typed options", %{runtime_module: module} do
    assert apply(module, :split_basic, [string(~c"a,,b,c")]) ==
             Enum.map([~c"a", ~c"b", ~c"c"], &string/1)

    assert apply(module, :split_including, [string(~c"a,,b,c")]) ==
             Enum.map([~c"a", ~c",,", ~c"b", ~c",", ~c"c"], &string/1)

    assert apply(module, :split_trimmed, [string(~c",a,,")]) == [string(~c"a")]
    assert apply(module, :split_limited, [string(~c"a,b,c")]) == [string(~c"a"), string(~c"b,c")]
  end

  test "replacement supports typed callbacks, literals, and empty-match progress", %{runtime_module: module} do
    assert apply(module, :replaced_typed, [string(~c"a12b3")]) == string(~c"a[12]b[3]")
    assert apply(module, :replaced_literal, [string(~c"a12b3")]) == string(~c"aXbX")
    assert apply(module, :replaced_empty, [string(~c"βx")]) == string(~c"-β-x-")
  end

  test "generated scan partitions, split, and replacement obey their collection laws", %{runtime_module: module} do
    assert :ok =
             Property.check_all(subject_gen(), @runs, fn input ->
               subject = string(input)
               scanned = apply(module, :scanned_a, [subject])

               scan_law =
                 Enum.all?(scanned, fn
                   {:Match, :unit, {:String, prefix}, {:String, [?a]}, {:String, suffix}, start, 1} ->
                     prefix ++ [?a] ++ suffix == input and start == length(prefix)

                   _other ->
                     false
                 end)

               starts = Enum.map(scanned, &elem(&1, 5))

               split_expected =
                 input
                 |> List.to_string()
                 |> String.split(",", trim: false)
                 |> Enum.map(&(String.to_charlist(&1) |> string()))

               replaced_expected =
                 input
                 |> List.to_string()
                 |> String.replace("a", "X")
                 |> String.to_charlist()
                 |> string()

               scan_law and starts == Enum.sort(starts) and length(starts) == length(Enum.uniq(starts)) and
                 apply(module, :split_commas, [subject]) == split_expected and
                 apply(module, :replaced_a, [subject]) == replaced_expected
             end)
  end
end
