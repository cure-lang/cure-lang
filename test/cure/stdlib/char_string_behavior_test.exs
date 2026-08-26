defmodule Cure.Stdlib.CharStringBehaviorTest do
  use ExUnit.Case, async: false

  alias Antigen.Backend.StreamData, as: Property
  alias Antigen.Gen

  @char :"Cure.Std.Char"
  @string :"Cure.Std.String"
  @runs [max_runs: 500, max_run_time: :infinity]

  defp char(name, args), do: apply(@char, name, args)
  defp string(name, args), do: apply(@string, name, args)

  # `String` is nominal -- `rec String { characters: List(Char) }` -- so it erases
  # to the tagged pair `{:String, code_points}`. `Char` still erases to a bare
  # code-point integer, so character arguments and `Option(Char)` results below
  # stay unwrapped; only the string-shaped ones carry the tag.
  defp cure_string(chars) when is_list(chars), do: {:String, chars}

  defp scalar_gen do
    Gen.bind(Gen.integer(0, 0x10FFFF), fn cp ->
      Gen.return(if cp in 0xD800..0xDFFF, do: 0xFFFD, else: cp)
    end)
  end

  defp chars_gen(0), do: Gen.return([])

  defp chars_gen(size) do
    Gen.bind(Gen.member_of(~c"aBéß٣ _-"), fn head ->
      Gen.bind(chars_gen(size - 1), fn tail -> Gen.return([head | tail]) end)
    end)
  end

  defp string_case_gen do
    Gen.bind(Gen.integer(0, 12), fn size ->
      Gen.bind(chars_gen(size), fn chars ->
        Gen.bind(Gen.integer(-2, 15), fn count -> Gen.return({chars, count}) end)
      end)
    end)
  end

  test "character classification covers Unicode category families" do
    assert char(:is_ascii, [?A])
    refute char(:is_ascii, [?é])
    assert char(:ascii_value, [?A]) == {:some, 65}
    assert char(:ascii_value, [?é]) == :none

    assert char(:is_letter, [?é])
    assert char(:is_punctuation, [?!])
    assert char(:is_newline, [0x2028])
    assert char(:is_whitespace, [0xA0])
    assert char(:is_symbol, [?©])
    assert char(:is_math_symbol, [?+])
    assert char(:is_currency_symbol, [?€])
    assert char(:is_cased, [?ǅ])
    assert char(:is_uppercase, [?É])
    assert char(:is_lowercase, [?é])
  end

  test "character casing is Unicode-aware and permits expansion" do
    # `Std.Char` answers in code points, because one scalar may expand into
    # several and `Std.Char` sits below `Std.String`.
    assert char(:lowercased_characters, [?É]) == ~c"é"
    assert char(:uppercased_characters, [?ß]) == ~c"SS"
    # `Std.String` assembles the same mapping into a nominal, tagged `String`.
    assert string(:lowercased_character, [?É]) == cure_string(~c"é")
    assert string(:uppercased_character, [?ß]) == cure_string(~c"SS")
    # `ascii_lowercased` is the one-to-one ASCII fold, so it stays at `Char`.
    assert char(:ascii_lowercased, [?A]) == ?a
    assert char(:ascii_lowercased, [?É]) == ?É
  end

  test "numbers, hexadecimal values, equality, and scalar ordering" do
    assert char(:is_number, [?½])
    refute char(:is_whole_number, [?½])
    assert char(:whole_number_value, [?½]) == :none
    assert char(:is_whole_number, [?Ⅻ])
    assert char(:whole_number_value, [?Ⅻ]) == {:some, 12}
    assert char(:whole_number_value, [?٣]) == {:some, 3}

    assert char(:is_hex_digit, [?Ｆ])
    assert char(:hex_digit_value, [?Ｆ]) == {:some, 15}
    assert char(:hex_digit_value, [?g]) == :none

    assert char(:same, [?a, ?a])
    refute char(:same, [?a, ?b])
    assert char(:less_than, [?a, ?b])
    assert char(:between, [?m, ?a, ?z])
    refute char(:between, [?A, ?a, ?z])
  end

  test "Swift-style string conveniences handle boundaries and Unicode" do
    cure = cure_string(~c"cure")

    assert string(:lowercased, [cure_string(~c"CAFÉ")]) == cure_string(~c"café")
    assert string(:uppercased, [cure_string(~c"straße")]) == cure_string(~c"STRASSE")
    assert string(:has_prefix, [cure, cure_string(~c"cu")])
    assert string(:has_suffix, [cure, cure_string(~c"re")])
    assert string(:contains, [cure_string(~c"café"), ?é])
    assert string(:first, [cure]) == {:some, ?c}
    assert string(:last, [cure]) == {:some, ?e}
    assert string(:first, [cure_string([])]) == :none
    assert string(:last, [cure_string([])]) == :none
    assert string(:prefix, [cure, 2]) == cure_string(~c"cu")
    assert string(:suffix, [cure, 2]) == cure_string(~c"re")
    assert string(:drop_first, [cure, 2]) == cure_string(~c"re")
    assert string(:drop_last, [cure, 2]) == cure_string(~c"cu")
    assert string(:prefix, [cure, -1]) == cure_string([])
    assert string(:drop_first, [cure, -1]) == cure
    # `split_on/2` answers a `List(String)`, so each element carries the tag.
    assert string(:split_on, [cure_string(~c",a,,b,"), ?,]) ==
             [cure_string(~c"a"), cure_string(~c"b")]
  end

  test "character functions agree with the Unicode reference over generated scalars" do
    assert :ok =
             Property.check_all(scalar_gen(), @runs, fn cp ->
               properties = Unicode.properties(cp)
               category = Unicode.category(cp)
               ascii_value = char(:ascii_value, [cp])
               whole_value = char(:whole_number_value, [cp])
               hex_value = char(:hex_digit_value, [cp])
               expected_space = cp in [9, 10, 11, 12, 13, 0x85] or category in [:Zs, :Zl, :Zp]

               char(:same, [cp, cp]) and
                 char(:is_ascii, [cp]) == cp <= 0x7F and
                 ascii_value == if(cp <= 0x7F, do: {:some, cp}, else: :none) and
                 char(:less_than, [cp, 0x10FFFF]) == cp < 0x10FFFF and
                 char(:between, [cp, 0, 0x10FFFF]) and
                 char(:lowercased_characters, [cp]) == :string.lowercase([cp]) and
                 char(:uppercased_characters, [cp]) == :string.uppercase([cp]) and
                 string(:lowercased_character, [cp]) == cure_string(:string.lowercase([cp])) and
                 string(:uppercased_character, [cp]) == cure_string(:string.uppercase([cp])) and
                 char(:is_letter, [cp]) == :alphabetic in properties and
                 char(:is_punctuation, [cp]) == category in [:Pc, :Pd, :Pe, :Pf, :Pi, :Po, :Ps] and
                 char(:is_newline, [cp]) == cp in [10, 11, 12, 13, 0x85, 0x2028, 0x2029] and
                 char(:is_whitespace, [cp]) == expected_space and
                 char(:is_symbol, [cp]) == category in [:Sc, :Sk, :Sm, :So] and
                 char(:is_math_symbol, [cp]) == :math in properties and
                 char(:is_currency_symbol, [cp]) == (category == :Sc) and
                 char(:is_cased, [cp]) == :cased in properties and
                 char(:is_uppercase, [cp]) == :uppercase in properties and
                 char(:is_lowercase, [cp]) == :lowercase in properties and
                 char(:is_number, [cp]) == category in [:Nd, :Nl, :No] and
                 char(:is_whole_number, [cp]) == match?({:some, _}, whole_value) and
                 char(:is_hex_digit, [cp]) == :hex_digit in properties and
                 match?({:some, value} when value in 0..15, hex_value) == :hex_digit in properties
             end)
  end

  test "string slicing obeys prefix/drop and suffix/drop decomposition laws" do
    assert :ok =
             Property.check_all(string_case_gen(), @runs, fn {chars, count} ->
               s = cure_string(chars)
               prefix = string(:prefix, [s, count])
               suffix = string(:suffix, [s, count])
               first_rest = string(:drop_first, [s, count])
               last_rest = string(:drop_last, [s, count])
               expected_first = if(chars == [], do: :none, else: {:some, hd(chars)})
               expected_last = if(chars == [], do: :none, else: {:some, List.last(chars)})

               string(:concat, [prefix, first_rest]) == s and
                 string(:concat, [last_rest, suffix]) == s and
                 string(:has_prefix, [s, prefix]) and
                 string(:has_suffix, [s, suffix]) and
                 string(:first, [s]) == expected_first and
                 string(:last, [s]) == expected_last and
                 string(:lowercased, [s]) == cure_string(:string.lowercase(chars)) and
                 string(:uppercased, [s]) == cure_string(:string.uppercase(chars))
             end)
  end
end
