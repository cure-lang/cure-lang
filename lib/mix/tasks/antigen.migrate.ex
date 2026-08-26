defmodule Mix.Tasks.Antigen.Migrate do
  use Mix.Task
  alias Antigen.Corpus

  @shortdoc "Rewrite banked Antigen corpora into the human-readable format (idempotent)."
  @moduledoc """
  Rewrites each given `.sexp` corpus file in place from any format (legacy Base64
  or already-new) into the readable format — s-expr term pieces, plaintext note,
  readable `fault=` field — preserving the byte-exact stored dedup key and record
  order. Idempotent: a new-format file re-migrates to byte-identical output.

      mix antigen.migrate test/antigen/seeds.sexp test/antigen/corpus.sexp test/antigen/reach.sexp
  """

  @impl true
  def run(paths) do
    Enum.each(paths, &migrate_file/1)
  end

  defp migrate_file(path) do
    lines = path |> File.stream!() |> Enum.to_list()

    out =
      lines
      |> Enum.map(fn line ->
        trimmed = String.trim_trailing(line, "\n")

        case Corpus.decode_record(trimmed) do
          {:ok, c} -> Corpus.encode_record(c, Corpus.raw_key(trimmed))
          # leave undecodable lines (e.g. blank) untouched
          _ -> trimmed
        end
      end)

    tmp = path <> ".migrating"
    File.write!(tmp, Enum.map_join(out, "\n", & &1) <> "\n")
    File.rename!(tmp, path)
    Mix.shell().info("migrated #{path} (#{length(lines)} records)")
  end
end
