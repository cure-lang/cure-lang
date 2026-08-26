defmodule Mix.Tasks.Antigen.Prune do
  use Mix.Task

  @shortdoc "Prune stale antibodies from the Antigen corpus (retire the ones that no longer replay :ok)"

  @moduledoc """
  Re-check every record in the antibody corpus against the LIVE kernel. Records that
  still decode and replay `:ok` stay; the rest move to a retirement store, annotated
  with the reason (`:unknown_node` decode error, `unknown_assay`, a label-drift
  verdict, …). Never rewrites a term; never silently deletes. A run that retires
  nothing leaves the corpus byte-identical.

      mix antigen.prune [--corpus PATH] [--retired PATH]

  Defaults: corpus `test/antigen/corpus.sexp`, retired `test/antigen/retired.sexp`.
  Run after a kernel shape change, review the diff (what retired and why — for any
  retired guard that still matters, add or confirm a generator cell for its
  shape-class), then commit.
  """

  @switches [corpus: :string, retired: :string]

  @impl Mix.Task
  def run(argv) do
    {opts, _, _} = OptionParser.parse(argv, strict: @switches)
    corpus = opts[:corpus] || "test/antigen/corpus.sexp"
    retired = opts[:retired] || "test/antigen/retired.sexp"

    tally = Antigen.Prune.prune(corpus, retired)

    detail =
      if tally.retired == 0 do
        ""
      else
        kinds =
          tally.reasons
          |> Enum.frequencies_by(&elem(&1, 0))
          |> Enum.map_join(", ", fn {kind, n} -> "#{kind}×#{n}" end)

        " (#{kinds} → #{retired})"
      end

    Mix.shell().info("antigen prune: #{tally.kept} kept, #{tally.retired} retired#{detail}")
  end
end
