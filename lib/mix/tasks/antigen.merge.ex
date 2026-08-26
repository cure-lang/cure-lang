defmodule Mix.Tasks.Antigen.Merge do
  use Mix.Task

  @shortdoc "Merge Antigen record files into a destination corpus/seeds file (dedup by stored key)"

  @moduledoc """
  Fold one or more Antigen record files into a destination, deduplicating by each
  record's embedded `key=` field. Byte-preserving — records are copied verbatim, never
  decoded/re-encoded — so it is safe across corpus and seeds files alike and cannot
  mint atoms.

      mix antigen.merge <dest> <source>...

  The git-tracked masters live alongside Antigen at `test/antigen/corpus.sexp`,
  `test/antigen/seeds.sexp`, and `test/antigen/reach.sexp`. Use this to recover replay
  values that were banked to a scratch / tmp directory back into the master, e.g.:

      mix antigen.merge test/antigen/seeds.sexp /tmp/run-a/seeds.sexp /tmp/run-b/seeds.sexp

  Prints an added / duplicate / keyless tally. `dest` is required explicitly (there is
  no default) so a merge can never write the wrong master by accident.
  """

  @impl Mix.Task
  def run(args) do
    case args do
      [dest | [_ | _] = sources] ->
        tally = Antigen.Corpus.merge(dest, sources)

        Mix.shell().info(
          "merged into #{dest}: +#{tally.added} new, #{tally.duplicate} duplicate, " <>
            "#{tally.keyless} keyless (#{length(sources)} source(s))"
        )

      _ ->
        Mix.raise("usage: mix antigen.merge <dest> <source>...")
    end
  end
end
