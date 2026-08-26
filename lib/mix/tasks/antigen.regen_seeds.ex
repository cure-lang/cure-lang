defmodule Mix.Tasks.Antigen.RegenSeeds do
  use Mix.Task

  @shortdoc "Regenerate the Antigen seed pool from the current generators (replace, not append)"

  @moduledoc """
  Drop the stale seed pool and re-harvest coverage-novel seeds from the CURRENT
  generators into a fresh `seeds.sexp`, atomically replacing the old file. Stale /
  undecodable seeds are re-derived, never translated. Run after a kernel shape
  change; the replay gate (`corpus_replay_test`) then verifies the fresh pool decodes
  and replays clean.

      mix antigen.regen_seeds [--count N] [--seeds PATH]

  Defaults: count 20000, seeds `test/antigen/seeds.sexp`.
  """

  @switches [count: :integer, seeds: :string]

  @impl Mix.Task
  def run(argv) do
    {opts, _, _} = OptionParser.parse(argv, strict: @switches)

    regen_opts =
      []
      |> put_opt(:seeds_path, opts[:seeds])
      |> put_opt(:count, opts[:count])

    %{seeds_banked: banked, dest: dest} = Antigen.Regen.regenerate_seeds(regen_opts)
    Mix.shell().info("antigen regen_seeds: #{banked} seed(s) harvested → #{dest}")
  end

  defp put_opt(kw, _key, nil), do: kw
  defp put_opt(kw, key, val), do: Keyword.put(kw, key, val)
end
