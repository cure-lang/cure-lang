defmodule Antigen.CorpusAtomsTest do
  use ExUnit.Case, async: true

  @corpora ~w(seeds.sexp corpus.sexp reach.sexp reach_reify_split.sexp)
           |> Enum.map(&Path.join("test/antigen", &1))

  # every hazard-string (a name from_pieces/decode_record feeds to
  # String.to_existing_atom) in every committed record must be pre-interned via
  # @known_atoms — otherwise a bare-process decode raises ArgumentError.
  # Hazard strings = the record's kind/label + every VALUE string (never a map
  # KEY) inside the decoded Base64 scaffold. Pieces atoms (Serialize mints) and
  # the fault= field (decode_fault mints) and assay (never atomized) are NOT
  # hazards and are deliberately excluded.
  defp scaffold_value_strings(b) when is_binary(b), do: [b]

  defp scaffold_value_strings(m) when is_map(m),
    do: Enum.flat_map(m, fn {_k, v} -> scaffold_value_strings(v) end)

  defp scaffold_value_strings(l) when is_list(l), do: Enum.flat_map(l, &scaffold_value_strings/1)

  defp scaffold_value_strings(t) when is_tuple(t),
    do: t |> Tuple.to_list() |> Enum.flat_map(&scaffold_value_strings/1)

  defp scaffold_value_strings(_), do: []

  defp hazard_strings(line) do
    fields = line |> String.trim_trailing("\n") |> String.split("\t") |> tl()

    m =
      Map.new(fields, fn f ->
        case String.split(f, "=", parts: 2) do
          [k, v] -> {k, v}
          [k] -> {k, ""}
        end
      end)

    scaffold =
      case m["scaffold"] do
        s when s in [nil, "-"] -> %{}
        b64 -> :erlang.binary_to_term(Base.decode64!(b64))
      end

    [m["kind"], m["label"] | scaffold_value_strings(scaffold)]
    |> Enum.reject(&(&1 in [nil, "", "-"]))
  end

  test "every hazard-string in every committed corpus is a member of @known_atoms" do
    known = Antigen.Challenge.__known_atoms__() |> MapSet.new(&Atom.to_string/1)

    missing =
      for path <- @corpora,
          File.exists?(path),
          line <- File.stream!(path),
          name <- hazard_strings(line),
          not MapSet.member?(known, name),
          uniq: true,
          do: name

    assert missing == [], "hazard-strings absent from @known_atoms: #{inspect(Enum.sort(missing))}"
  end

  alias Antigen.Corpus

  test "every committed corpus is in the readable format and fully decodes" do
    for path <- @corpora, File.exists?(path), line <- File.stream!(path) do
      trimmed = String.trim_trailing(line, "\n")

      pieces_field =
        trimmed
        |> String.split("\t")
        |> Enum.find_value(fn f ->
          case String.split(f, "=", parts: 2) do
            ["pieces", v] -> v
            _ -> nil
          end
        end)

      for piece <- String.split(pieces_field || "", ";;", trim: true) do
        [_id, body] = String.split(piece, "::", parts: 2)

        assert String.starts_with?(body, "("),
               "#{Path.basename(path)}: non-readable (Base64) piece: #{String.slice(body, 0, 24)}…"
      end

      assert {:ok, _} = Corpus.decode_record(trimmed), "#{Path.basename(path)}: record failed to decode"
    end
  end
end
