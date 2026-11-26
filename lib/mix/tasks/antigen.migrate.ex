defmodule Mix.Tasks.Antigen.Migrate do
  use Mix.Task
  alias Antigen.Corpus.Migration

  @shortdoc "Explicit offline Antigen import/rekey audit; publication requires --write."
  @moduledoc """
  Audit historical corpora without modifying input files:

      mix antigen.migrate --from fixed-ceiling-v1 test/antigen/corpus.sexp test/antigen/seeds.sexp test/antigen/coverage.sexp

  Archive verbatim preimages, stage outputs and write a complete per-row inventory:

      mix antigen.migrate --from fixed-ceiling-v1 --archive-dir /tmp/antigen-before --out-dir /tmp/antigen-after --inventory /tmp/antigen-inventory.json PATHS...

  Add `--write` only to explicitly publish a fully successful staged migration.
  Publication verifies original hashes and retains a per-file recovery journal;
  it is not an atomic multi-file transaction. A pre-existing journal requires
  inspection/recovery before another publication attempt.

  Failed imports and non-`:ok` real assay verdicts fail the task. Staging retains
  their evidence but never reports completion or publishes partial results.
  """

  @impl true
  def run(args) do
    {opts, paths} =
      OptionParser.parse!(args,
        strict: [from: :string, archive_dir: :string, out_dir: :string, inventory: :string, write: :boolean]
      )

    unless opts[:from] == "fixed-ceiling-v1", do: Mix.raise("--from fixed-ceiling-v1 is required")
    if paths == [], do: Mix.raise("provide input corpus paths")
    staging = Enum.map(~w(archive_dir out_dir inventory)a, &Keyword.has_key?(opts, &1))

    if Enum.any?(staging) and not Enum.all?(staging),
      do: Mix.raise("--archive-dir, --out-dir and --inventory must be supplied together")

    if opts[:write] == true and not Enum.all?(staging), do: Mix.raise("--write requires complete staging options")
    opts = Keyword.put(opts, :from, :fixed_ceiling_v1)
    result = if Enum.all?(staging), do: Migration.stage(paths, opts), else: Migration.audit(paths, opts)
    {status, report, _state} = result

    for file <- report["files"] do
      Mix.shell().info(
        "#{file["name"]}: #{file["physical_lines"]} input lines, #{file["output_records"]} staged output rows"
      )
    end

    unless status == :ok do
      Mix.raise(
        "migration incomplete: #{length(report["failures"])} import/conservation errors, #{length(report["replay_failures"])} replay failures"
      )
    end

    action =
      cond do
        opts[:write] -> "published with recovery journal"
        Enum.all?(staging) -> "staged; inputs unchanged"
        true -> "audited; no files written"
      end

    Mix.shell().info("migration #{action}")
  end
end
