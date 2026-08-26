defmodule Mix.Tasks.Cure.Oracle do
  @shortdoc "Regenerate differential-oracle fixtures (live mode; needs idris2)"
  @moduledoc """
  Live mode of the differential oracle (design spec §7). For every cluster under
  `test/oracle/`, run each `.cure` through Cure and each `.idr` through
  `idris2 --check`, then rewrite that cluster's `verdicts.json`.

  Binary: `$IDRIS2_BIN`, else `~/Develop/Idris2/build/exec/idris2`.

  Regeneration PRESERVES prior `relation`/`reason` fields. A brand-new pair gets
  `relation: "same"` deliberately, so if its verdicts diverge, `replay` fails
  loudly and forces a human to triage (never hand-edit a verdict).

  Usage:
      mix cure.oracle            # all clusters
      mix cure.oracle rewrite    # one cluster
  """
  use Mix.Task
  alias Cure.Oracle

  @impl Mix.Task
  def run(argv) do
    Mix.Task.run("app.start")
    bin = Oracle.default_idris_bin()

    unless File.exists?(bin) do
      Mix.raise("idris2 not found at #{bin} — build it (plan Task 2) or set $IDRIS2_BIN")
    end

    clusters = if argv == [], do: Oracle.clusters(), else: argv

    for cluster <- clusters do
      prior = Oracle.read_fixture(cluster)

      # Fan out with a CONCURRENCY CAP: at most `max_conc` probes run at once, and
      # inside each the Cure and Idris checks run concurrently. Unbounded fan-out
      # (one task per probe) spawns ~2×#probes CPU-bound subprocesses — each Idris
      # `--check` pegs a core for ~2 min — which saturates the machine as the probe
      # count grows and inflates *every* Cure verdict past its timeout (false
      # `timeout` verdicts). The cap keeps total in-flight subprocesses ≈ core
      # count. Default: half the schedulers (so cure+idris per probe ≈ one core
      # each); override with `ORACLE_MAX_CONCURRENCY`. Each check is still bound by
      # its own timeout, so a non-terminating elaboration surfaces as `timeout`.
      max_conc =
        case System.get_env("ORACLE_MAX_CONCURRENCY") do
          nil -> max(1, div(System.schedulers_online(), 2))
          s -> max(1, String.to_integer(String.trim(s)))
        end

      results =
        Oracle.pairs(cluster)
        |> Task.async_stream(
          fn %{name: name, cure_path: cp, idr_path: ip} ->
            cure = Task.async(fn -> Oracle.cure_verdict_timed(cp) end)
            idris = Task.async(fn -> Oracle.idris_verdict_timed(bin, ip) end)
            {name, {Task.await(cure, :infinity), Task.await(idris, :infinity)}}
          end,
          max_concurrency: max_conc,
          timeout: :infinity,
          ordered: false
        )
        |> Enum.map(fn {:ok, res} -> res end)

      fixture =
        for {name, {{cure_v, cure_ms}, {idris_v, idris_ms}}} <- results, into: %{} do
          base = Map.get(prior, name, %{"relation" => "same", "reason" => ""})

          entry = %{
            "cure" => Atom.to_string(cure_v),
            "idris" => Atom.to_string(idris_v),
            "relation" => Map.get(base, "relation", "same"),
            "reason" => Map.get(base, "reason", "")
          }

          Mix.shell().info(
            "#{cluster}/#{name}: cure=#{entry["cure"]} (#{cure_ms}ms) " <>
              "idris=#{entry["idris"]} (#{idris_ms}ms) rel=#{entry["relation"]}" <>
              if(Oracle.consistent(entry) == :ok, do: "", else: "  <-- TRIAGE")
          )

          {name, entry}
        end

      Oracle.write_fixture(cluster, fixture)
      Mix.shell().info("wrote #{Path.join(["test/oracle", cluster, "verdicts.json"])}")
    end
  end
end
