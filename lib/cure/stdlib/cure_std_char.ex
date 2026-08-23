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

  def unicode_script_name(chars) when is_list(chars) do
    normalized = normalize_script_name(List.to_string(chars))

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

  defp normalize_script_name(name) do
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
