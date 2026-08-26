defmodule Antigen.Regen do
  @moduledoc """
  Seed-pool regeneration across kernel shape changes (migration design, C1). Drops
  the stale seed pool and re-harvests coverage-novel seeds from the CURRENT
  generators into a fresh file, then atomically swaps it over the canonical store —
  "replace, not append". Undecodable old seeds are re-derived, never translated.
  Zero term-rewriting. Reuses the existing harvest path (`Runner.generate/1`) and
  explorer pool (`Mix.Tasks.Antigen.default_gen/0`).
  """
  alias Antigen.Runner

  @type result :: %{seeds_banked: non_neg_integer(), dest: String.t()}

  @spec regenerate_seeds(keyword()) :: result()
  def regenerate_seeds(opts \\ []) do
    dest = Keyword.get(opts, :seeds_path, "test/antigen/seeds.sexp")
    count = Keyword.get(opts, :count, 20_000)
    gen = Keyword.get(opts, :gen, Mix.Tasks.Antigen.default_gen())

    tmp = dest <> ".regen"
    File.rm(tmp)

    # Harvest into the fresh (empty) tmp with an inert filler pool loaded from it, so
    # the new pool is derived from the current generators — not primed by the stale
    # store we are about to discard.
    Process.put(:antigen_seed_pool, Antigen.Generators.SeedPool.load(tmp))
    %{seeds_banked: banked} = Runner.generate(gen: gen, count: count, seeds_path: tmp)

    # generate only creates the file once a seed banks; guarantee a file to swap so a
    # zero-yield run still produces a (correctly empty) fresh pool.
    File.exists?(tmp) || File.write!(tmp, "")
    File.rename!(tmp, dest)

    %{seeds_banked: banked, dest: dest}
  end
end
