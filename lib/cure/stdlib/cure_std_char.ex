defmodule :cure_std_char do
  @moduledoc """
  Runtime helper for `Std.Char`.

  Target of the `@extern` bridge in `lib/std/char.cure`. `Char` is a nominal
  opaque carrier declared with `@erases(:integer)`, so it erases to its native
  Unicode code-point integer and exposing that code point as an `Int` is the
  identity at run time.
  The bridge exists purely to give that type-level `Char -> Int` coercion a
  name (`Std.Char.code_point`, the Lean `Fin.val` analog), which `Std.Comparable`'s
  `Char`/`String` instances use to compare code points. The name is
  `code_point`, not `to_int`, because `Std.String` also exposes a `to_int`
  (parse) and the dependent pipeline resolves globals by bare name.
  """

  @unicode_data Path.join(Unicode.data_dir(), "unicode_data.txt")
  @external_resource @unicode_data
  @script_extensions_data Path.expand("../../std_deps/regex/data/ScriptExtensions-17.0.0.txt", __DIR__)
  @external_resource @script_extensions_data
  @bidi_brackets_data Path.expand("../../std_deps/regex/data/BidiBrackets-17.0.0.txt", __DIR__)
  @external_resource @bidi_brackets_data
  @unicode_name_values @unicode_data
                       |> File.stream!()
                       |> Enum.reduce(%{}, fn line, values ->
                         case String.split(String.trim(line), ";") do
                           [hex, name | fields] ->
                             with {code_point, ""} <- Integer.parse(hex, 16),
                                  true <- code_point >= 0 and code_point <= 0x10FFFF,
                                  false <- code_point >= 0xD800 and code_point <= 0xDFFF do
                               names =
                                 if String.starts_with?(name, "<") do
                                   case Enum.at(fields, 8) do
                                     alias when is_binary(alias) and alias != "" -> [alias]
                                     _ -> []
                                   end
                                 else
                                   [name]
                                 end

                               Enum.reduce(names, values, fn candidate, acc ->
                                 normalized =
                                   candidate
                                   |> String.trim()
                                   |> String.split(" (", parts: 2)
                                   |> hd()
                                   |> String.upcase()
                                   |> String.replace("_", " ")
                                   |> String.replace("-", " ")
                                   |> String.split()
                                   |> Enum.join(" ")

                                 Map.put(acc, normalized, code_point)
                               end)
                             else
                               _ -> values
                             end

                           _ ->
                             values
                         end
                       end)
  @whole_number_values @unicode_data
                       |> File.stream!()
                       |> Enum.reduce(%{}, fn line, values ->
                         fields = String.split(String.trim(line), ";")

                         with [hex | _] <- fields,
                              numeric when numeric != "" <- Enum.at(fields, 8),
                              {value, ""} <- Integer.parse(numeric),
                              true <- value >= 0 do
                           Map.put(values, String.to_integer(hex, 16), value)
                         else
                           _ -> values
                         end
                       end)
  @bidi_class_values @unicode_data
                     |> File.stream!()
                     |> Enum.reduce(%{}, fn line, values ->
                       fields = String.split(String.trim(line), ";")

                       with hex when is_binary(hex) <- Enum.at(fields, 0),
                            bidi when is_binary(bidi) <- Enum.at(fields, 4),
                            true <- String.trim(bidi) != "",
                            {code_point, ""} <- Integer.parse(String.trim(hex), 16) do
                         Map.put(values, code_point, String.to_atom(String.trim(bidi)))
                       else
                         _ -> values
                       end
                     end)

  @bidi_class_name_values %{
    "l" => :L,
    "lefttoright" => :L,
    "r" => :R,
    "righttoleft" => :R,
    "al" => :AL,
    "arabicletter" => :AL,
    "en" => :EN,
    "europeannumber" => :EN,
    "es" => :ES,
    "europeanseparator" => :ES,
    "et" => :ET,
    "europeanterminator" => :ET,
    "an" => :AN,
    "arabicnumber" => :AN,
    "cs" => :CS,
    "commonseparator" => :CS,
    "b" => :B,
    "paragraphseparator" => :B,
    "s" => :S,
    "segmentseparator" => :S,
    "ws" => :WS,
    "whitespace" => :WS,
    "on" => :ON,
    "otherneutral" => :ON,
    "lre" => :LRE,
    "lefttorightembedding" => :LRE,
    "lro" => :LRO,
    "lefttorightoverride" => :LRO,
    "rle" => :RLE,
    "righttoleftembedding" => :RLE,
    "rlo" => :RLO,
    "righttoleftoverride" => :RLO,
    "pdf" => :PDF,
    "popdirectionalformat" => :PDF,
    "lri" => :LRI,
    "lefttorightisolate" => :LRI,
    "rli" => :RLI,
    "righttoleftisolate" => :RLI,
    "fsi" => :FSI,
    "firststrongisolate" => :FSI,
    "pdi" => :PDI,
    "popdirectionalisolate" => :PDI,
    "bn" => :BN,
    "boundaryneutral" => :BN,
    "nsm" => :NSM,
    "nonspacingmark" => :NSM
  }

  @bidi_mirrored_values @unicode_data
                        |> File.stream!()
                        |> Enum.reduce(%{}, fn line, values ->
                          fields = String.split(String.trim(line), ";")

                          with hex when is_binary(hex) <- Enum.at(fields, 0),
                               mirrored when is_binary(mirrored) <- Enum.at(fields, 9),
                               true <- String.trim(mirrored) == "Y",
                               {code_point, ""} <- Integer.parse(String.trim(hex), 16) do
                            Map.put(values, code_point, true)
                          else
                            _ -> values
                          end
                        end)

  @bidi_paired_bracket_type_values @bidi_brackets_data
                                             |> File.stream!()
                                             |> Enum.reduce(%{}, fn line, values ->
                                               line = String.trim(line)

                                               if line == "" or String.starts_with?(line, "#") do
                                                 values
                                               else
                                                 case String.split(line, ";") do
                                                   [hex, _paired, type | _] ->
                                                     bpt_value = type |> String.split("#", parts: 2) |> hd() |> String.trim()

                                                     with {code_point, ""} <- Integer.parse(String.trim(hex), 16),
                                                          bpt when bpt in ["o", "c"] <- bpt_value do
                                                       Map.put(values, code_point, if(bpt == "o", do: :open, else: :close))
                                                     else
                                                       _ -> values
                                                     end

                                                   _ ->
                                                     values
                                                 end
                                               end
                                             end)

  # `Bidi_Paired_Bracket` is the Boolean membership projection of the
  # paired-bracket mapping.  Keep the mapping value (`open`/`close`) separate:
  # the regex property asks whether a code point participates in a pair, while
  # `unicode_bidi_paired_bracket_type?/2` answers which side of that pair it is.
  @bidi_paired_bracket_values @bidi_paired_bracket_type_values
                              |> Map.keys()
                              |> Map.new(&{&1, true})

  @bidi_paired_bracket_type_name_values %{
    "o" => :open,
    "open" => :open,
    "c" => :close,
    "close" => :close,
    "n" => :none,
    "none" => :none
  }

  @script_extension_values @script_extensions_data
                           |> File.stream!()
                           |> Enum.reduce(%{}, fn line, values ->
                             line = String.trim(line)

                             if line == "" or String.starts_with?(line, "#") do
                               values
                             else
                               case String.split(line, ";") do
                                 [range, scripts | _] ->
                                   script_aliases =
                                     Unicode.Script.aliases()
                                     |> Enum.map(fn {name, script} ->
                                       normalized =
                                         name
                                         |> String.downcase()
                                         |> String.replace("_", "")
                                         |> String.replace("-", "")
                                         |> String.replace(" ", "")

                                       {normalized, script}
                                     end)
                                     |> Map.new()

                                   script_names =
                                     scripts
                                     |> String.trim()
                                     |> String.split()
                                     |> Enum.flat_map(fn name ->
                                       normalized =
                                         name
                                         |> String.downcase()
                                         |> String.replace("_", "")
                                         |> String.replace("-", "")
                                         |> String.replace(" ", "")

                                       case Map.fetch(script_aliases, normalized) do
                                         {:ok, script} -> [script]
                                         :error -> []
                                       end
                                     end)

                                   codepoints =
                                     case String.split(String.trim(range), "..") do
                                       [first, last] ->
                                         with {first_value, ""} <- Integer.parse(first, 16),
                                              {last_value, ""} <- Integer.parse(last, 16) do
                                           first_value..last_value
                                         else
                                           _ -> []
                                         end

                                       [single] ->
                                         case Integer.parse(single, 16) do
                                           {value, ""} -> value..value
                                           _ -> []
                                         end

                                       _ ->
                                         []
                                     end

                                   Enum.reduce(codepoints, values, fn code_point, acc ->
                                     Map.put(acc, code_point, script_names)
                                   end)

                                 _ ->
                                   values
                               end
                             end
                           end)

  @doc "Code point of a Char. Char erases to its integer code point, so this is `id`."
  def code_point(cp) when is_integer(cp), do: cp

  @doc "Construct a Char from a valid Unicode scalar value."
  def from_code_point(cp) when is_integer(cp) do
    if unicode_scalar_code_point?(cp), do: {:some, cp}, else: :none
  end

  def from_code_point(_cp), do: :none

  @doc "Returns the Unicode scalar named by a compile-time character name."
  def from_unicode_name(chars) when is_list(chars) do
    case Map.fetch(@unicode_name_values, normalize_unicode_name(List.to_string(chars))) do
      {:ok, code_point} -> {:some, code_point}
      :error -> :none
    end
  end

  def from_unicode_name(_chars), do: :none

  defp normalize_unicode_name(name) when is_binary(name) do
    name
    |> String.trim()
    |> String.split(" (", parts: 2)
    |> hd()
    |> String.upcase()
    |> String.replace("_", " ")
    |> String.replace("-", " ")
    |> String.split()
    |> Enum.join(" ")
  end

  def unicode_code_point?(cp) when is_integer(cp), do: cp >= 0 and cp <= 0x10FFFF
  def unicode_code_point?(_cp), do: false

  def utf16_surrogate_code_point?(cp) when is_integer(cp), do: cp >= 0xD800 and cp <= 0xDFFF
  def utf16_surrogate_code_point?(_cp), do: false

  def unicode_scalar_code_point?(cp),
    do: unicode_code_point?(cp) and not utf16_surrogate_code_point?(cp)

  def same?(left, right) when is_integer(left) and is_integer(right), do: left == right
  def less_than?(left, right) when is_integer(left) and is_integer(right), do: left < right
  def between?(cp, first, last), do: not less_than?(cp, first) and not less_than?(last, cp)

  def ascii?(cp) when is_integer(cp), do: cp in 0..0x7F
  def ascii_value(cp) when cp in 0..0x7F, do: {:some, cp}
  def ascii_value(cp) when is_integer(cp), do: :none

  def letter?(cp), do: :alphabetic in Unicode.properties(cp)
  def punctuation?(cp), do: Unicode.category(cp) in [:Pc, :Pd, :Pe, :Pf, :Pi, :Po, :Ps]
  def newline?(cp), do: cp in [10, 11, 12, 13, 0x85, 0x2028, 0x2029]
  def whitespace?(cp), do: unicode_space?(cp)
  def symbol?(cp), do: Unicode.category(cp) in [:Sc, :Sk, :Sm, :So]
  def math_symbol?(cp), do: :math in Unicode.properties(cp)
  def currency_symbol?(cp), do: Unicode.category(cp) == :Sc
  def cased?(cp), do: :cased in Unicode.properties(cp)
  def uppercase?(cp), do: :uppercase in Unicode.properties(cp)
  def lowercase?(cp), do: :lowercase in Unicode.properties(cp)

  def lowercased(cp) when is_integer(cp), do: :string.lowercase([cp])
  def uppercased(cp) when is_integer(cp), do: :string.uppercase([cp])

  def ascii_lowercased(cp) when cp in ?A..?Z, do: cp + 32
  def ascii_lowercased(cp) when is_integer(cp), do: cp

  def number?(cp), do: Unicode.category(cp) in [:Nd, :Nl, :No]
  def unicode_category(cp) when is_integer(cp), do: Unicode.category(cp)
  def unicode_script(cp) when is_integer(cp), do: Unicode.script(cp)

  def unicode_bidi_class(cp) when is_integer(cp), do: Map.get(@bidi_class_values, cp, :unknown)

  def unicode_bidi_paired_bracket_type?(cp, bpt) when is_integer(cp) and is_atom(bpt),
    do: Map.get(@bidi_paired_bracket_type_values, cp, :none) == bpt

  def unicode_script_extensions?(cp, script) when is_integer(cp) and is_atom(script) do
    case Map.fetch(@script_extension_values, cp) do
      {:ok, scripts} -> script in scripts
      :error -> Unicode.script(cp) == script
    end
  end

  def unicode_general_category?(cp, category) when is_integer(cp) and is_atom(category) do
    case Unicode.GeneralCategory.get(category) do
      ranges when is_list(ranges) ->
        Enum.any?(ranges, fn {first, last} -> cp >= first and cp <= last end)

      _ ->
        false
    end
  end

  def unicode_binary_property?(cp, property) when is_integer(cp) and is_atom(property) do
    case property do
      :bidi_mirrored ->
        Map.has_key?(@bidi_mirrored_values, cp)

      :bidi_paired_bracket ->
        Map.has_key?(@bidi_paired_bracket_values, cp)

      _ ->
        case Unicode.Property.get(property) do
          ranges when is_list(ranges) ->
            Enum.any?(ranges, fn {first, last} -> cp >= first and cp <= last end)

          _ ->
            false
        end
    end
  end

  def unicode_script_name(chars) when is_list(chars) do
    name = List.to_string(chars)

    value =
      case String.split(name, "=", parts: 2) do
        [property, value] ->
          if normalize_script_name(property) in ["script", "sc"], do: value, else: ""

        [_] ->
          case String.split(name, ":", parts: 2) do
            [property, value] ->
              if normalize_script_name(property) in ["script", "sc"], do: value, else: ""

            [_] ->
              name
          end
      end

    normalized = normalize_script_name(value)

    known =
      Unicode.Script.known_scripts()
      |> Map.new(fn script -> {normalize_script_name(Atom.to_string(script)), script} end)

    aliases =
      Unicode.Script.aliases()
      |> Enum.map(fn {alias_name, script} -> {normalize_script_name(alias_name), script} end)
      |> Map.new()

    case Map.fetch(Map.merge(known, aliases), normalized) do
      {:ok, script} -> {:some, script}
      :error -> :none
    end
  end

  def unicode_script_extensions_name(chars) when is_list(chars) do
    name = List.to_string(chars)

    value =
      case String.split(name, "=", parts: 2) do
        [property, value] ->
          if normalize_script_name(property) in ["scriptextensions", "scx"], do: value, else: ""

        [_] ->
          case String.split(name, ":", parts: 2) do
            [property, value] ->
              if normalize_script_name(property) in ["scriptextensions", "scx"], do: value, else: ""

            [_] ->
              ""
          end
      end

    normalized = normalize_script_name(value)

    known =
      Unicode.Script.known_scripts()
      |> Map.new(fn script -> {normalize_script_name(Atom.to_string(script)), script} end)

    aliases =
      Unicode.Script.aliases()
      |> Enum.map(fn {alias_name, script} -> {normalize_script_name(alias_name), script} end)
      |> Map.new()

    case Map.fetch(Map.merge(known, aliases), normalized) do
      {:ok, script} -> {:some, script}
      :error -> :none
    end
  end

  def unicode_bidi_class_name(chars) when is_list(chars) do
    name = List.to_string(chars)

    value =
      case String.split(name, "=", parts: 2) do
        [property, value] ->
          if normalize_bidi_name(property) in ["bidiclass", "bc"], do: value, else: ""

        [_] ->
          case String.split(name, ":", parts: 2) do
            [property, value] ->
              if normalize_bidi_name(property) in ["bidiclass", "bc"], do: value, else: ""

            [_] ->
              name
          end
      end

    case Map.fetch(@bidi_class_name_values, normalize_bidi_name(value)) do
      {:ok, bidi_class} -> {:some, bidi_class}
      :error -> :none
    end
  end

  def unicode_bidi_paired_bracket_type_name(chars) when is_list(chars) do
    name = List.to_string(chars)

    value =
      case String.split(name, "=", parts: 2) do
        [property, value] ->
          if normalize_bidi_name(property) in ["bidipairedbrackettype", "bpt"], do: value, else: ""

        [_] ->
          case String.split(name, ":", parts: 2) do
            [property, value] ->
              if normalize_bidi_name(property) in ["bidipairedbrackettype", "bpt"], do: value, else: ""

            [_] ->
              ""
          end
      end

    case Map.fetch(@bidi_paired_bracket_type_name_values, normalize_bidi_name(value)) do
      {:ok, bpt} -> {:some, bpt}
      :error -> :none
    end
  end

  def unicode_general_category_name(chars) when is_list(chars) do
    name = List.to_string(chars)

    value =
      case String.split(name, "=", parts: 2) do
        [property, value] ->
          if normalize_category_name(property) in ["generalcategory", "gc"], do: value, else: ""

        [_] ->
          case String.split(name, ":", parts: 2) do
            [property, value] ->
              if normalize_category_name(property) in ["generalcategory", "gc"], do: value, else: ""

            [_] ->
              name
          end
      end

    normalized = normalize_category_name(value)

    known =
      Unicode.GeneralCategory.known_categories()
      |> Map.new(fn category -> {normalize_category_name(Atom.to_string(category)), category} end)

    aliases =
      Unicode.GeneralCategory.aliases()
      |> Enum.map(fn {name, category} -> {normalize_category_name(name), category} end)
      |> Map.new()

    case Map.fetch(Map.merge(known, aliases), normalized) do
      {:ok, category} -> {:some, category}
      :error -> :none
    end
  end

  def unicode_binary_property_name(chars) when is_list(chars) do
    normalized = normalize_binary_property_name(List.to_string(chars))

    known =
      Unicode.Property.known_properties()
      |> Map.new(fn property ->
        {normalize_binary_property_name(Atom.to_string(property)), property}
      end)

    aliases =
      Unicode.Property.aliases()
      |> Enum.map(fn {name, property} ->
        {normalize_binary_property_name(name), property}
      end)
      |> Map.new()

    special = %{
      "bidimirrored" => :bidi_mirrored,
      "bidim" => :bidi_mirrored,
      "bidipairedbracket" => :bidi_paired_bracket,
      "bpb" => :bidi_paired_bracket
    }

    case Map.fetch(Map.merge(Map.merge(known, aliases), special), normalized) do
      {:ok, property} -> {:some, property}
      :error -> :none
    end
  end

  defp normalize_script_name(name) do
    name
    |> String.downcase()
    |> String.replace("_", "")
    |> String.replace("-", "")
    |> String.replace(" ", "")
  end

  defp normalize_bidi_name(name) do
    name
    |> String.downcase()
    |> String.replace("_", "")
    |> String.replace("-", "")
    |> String.replace(" ", "")
  end

  defp normalize_category_name(name) do
    name
    |> String.downcase()
    |> String.replace("_", "")
    |> String.replace("-", "")
    |> String.replace(" ", "")
  end

  defp normalize_binary_property_name(name) do
    name
    |> String.downcase()
    |> String.replace("_", "")
    |> String.replace("-", "")
    |> String.replace(" ", "")
  end

  def whole_number?(cp), do: Map.has_key?(@whole_number_values, cp)

  def whole_number_value(cp) when is_integer(cp) do
    case @whole_number_values do
      %{^cp => value} -> {:some, value}
      _ -> :none
    end
  end

  def hex_digit?(cp), do: :hex_digit in Unicode.properties(cp)

  def hex_digit_value(cp) when cp in ?0..?9, do: {:some, cp - ?0}
  def hex_digit_value(cp) when cp in ?A..?F, do: {:some, cp - ?A + 10}
  def hex_digit_value(cp) when cp in ?a..?f, do: {:some, cp - ?a + 10}
  def hex_digit_value(cp) when cp in 0xFF10..0xFF19, do: {:some, cp - 0xFF10}
  def hex_digit_value(cp) when cp in 0xFF21..0xFF26, do: {:some, cp - 0xFF21 + 10}
  def hex_digit_value(cp) when cp in 0xFF41..0xFF46, do: {:some, cp - 0xFF41 + 10}
  def hex_digit_value(cp) when is_integer(cp), do: :none

  @doc "Whether a code point belongs to PCRE's Unicode decimal-digit class."
  def unicode_digit?(cp) when is_integer(cp), do: Unicode.category(cp) == :Nd

  @doc "Whether a code point belongs to PCRE's Unicode word class."
  def unicode_word?(?_), do: true

  def unicode_word?(cp) when is_integer(cp) do
    Unicode.category(cp) in [:Lu, :Ll, :Lt, :Lm, :Lo, :Mn, :Mc, :Nd, :Pc]
  end

  @doc "Whether a code point belongs to PCRE's Unicode whitespace class."
  def unicode_space?(cp) when cp in [9, 10, 11, 12, 13, 0x85], do: true
  def unicode_space?(cp) when is_integer(cp), do: Unicode.category(cp) in [:Zs, :Zl, :Zp]

  @doc "Whether a code point belongs to PCRE's horizontal-whitespace class."
  def horizontal_space?(cp) when is_integer(cp) do
    cp in [0x0009, 0x0020, 0x00A0, 0x1680, 0x180E, 0x202F, 0x205F, 0x3000] or
      cp in 0x2000..0x200A
  end

  @doc "Whether a code point belongs to PCRE's vertical-whitespace class."
  def vertical_space?(cp) when is_integer(cp),
    do: cp in [0x000A, 0x000B, 0x000C, 0x000D, 0x0085, 0x2028, 0x2029]
end
