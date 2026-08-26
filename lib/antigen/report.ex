defmodule Antigen.Report do
  @moduledoc "Ephemeral full failure reports; never lose a failure to a filtered pipe (spec §10, umbrella §8.1)."
  alias Antigen.{Challenge, Corpus}

  @spec write_infection(String.t(), Challenge.t(), term(), map(), :infection | :immune_response) ::
          {:ok, String.t()}
  def write_infection(dir, c, detail, health, kind \\ :infection)

  def write_infection(dir, %Challenge{} = c, detail, health, kind) do
    File.mkdir_p!(dir)
    slug = slug(c.assay)
    n = next_index(dir, c.seed, slug)
    path = Path.join(dir, "failure-#{c.seed}-#{slug}-#{n}.txt")
    File.write!(path, render(c, detail, health, kind))
    File.write!(Path.join(dir, "latest.txt"), Path.basename(path))
    {:ok, path}
  end

  @counter_key {__MODULE__, :immune_responses}

  @doc """
  Tally one deliberately-injected (immune-response) violation instead of printing
  a per-occurrence breadcrumb. A normal suite triggers hundreds of these — each is
  the immune system working as designed, so flooding stdout with them buries the
  one line that matters (a real `ANTIGEN INFECTION`). The count is surfaced once,
  at suite end, by `immune_response_count/0`.
  """
  @spec tally_immune_response() :: :ok
  def tally_immune_response do
    :counters.add(counter_ref(), 1, 1)
    :ok
  end

  @doc "Total immune responses tallied so far (0 if none / counter never created)."
  @spec immune_response_count() :: non_neg_integer()
  def immune_response_count do
    case :persistent_term.get(@counter_key, nil) do
      nil -> 0
      ref -> :counters.get(ref, 1)
    end
  end

  # Write-once atomic counter: the ref lives in persistent_term (read-many,
  # write-once — the intended use), the count in a concurrency-safe `:counters`.
  defp counter_ref do
    case :persistent_term.get(@counter_key, nil) do
      nil ->
        ref = :counters.new(1, [:write_concurrency])
        :persistent_term.put(@counter_key, ref)
        ref

      ref ->
        ref
    end
  end

  @doc """
  One-line stdout marker. `:infection` (default) is a REAL soundness violation
  the assay caught in the system under test — the engine's whole point, and it
  should read alarmingly. `:immune_response` is a DELIBERATELY-injected violation
  (test scaffolding such as a forced-violation assay): the immune system working
  as designed, so it reads calmly and must NOT be mistaken for a defect.
  """
  @spec breadcrumb(Challenge.t(), String.t(), :infection | :immune_response) :: String.t()
  def breadcrumb(c, path, kind \\ :infection)

  def breadcrumb(%Challenge{} = c, path, :infection),
    do: "ANTIGEN INFECTION [#{c.assay}] seed=#{c.seed} → #{path}"

  def breadcrumb(%Challenge{} = c, path, :immune_response),
    do: "antigen immune response — expected, deliberately injected (not a defect) [#{c.assay}] seed=#{c.seed} → #{path}"

  defp render(c, detail, health, :immune_response) do
    """
    ANTIGEN IMMUNE RESPONSE (expected)
    This violation was DELIBERATELY injected — test scaffolding exercising the
    detection/shrink/banking machinery. It is NOT a defect in the system under test.
    """ <> render_body(c, detail, health)
  end

  defp render(c, detail, health, :infection) do
    "ANTIGEN INFECTION\n" <> render_body(c, detail, health)
  end

  defp render_body(c, detail, health) do
    """
    assay:      #{c.assay}
    label:      #{c.label}  (ground truth)
    seed:       #{c.seed}
    detail:     #{inspect(detail)}
    health:     #{inspect(health)}#{triage_line(health)}
    note:       #{c.note}

    -- antigen (C2 record, generator-independent repro) --
    #{Corpus.encode_record(c)}

    -- repro --
    decode the record above and run Antigen.Runner.replay_one/1
    """
  end

  defp triage_line(%{triage: %{orig_size: o, min_size: m, bisect_drops: b, shrink_rewrites: s}}),
    do: "\ntriage:     size #{o}→#{m} · bisect −#{b} elems · shrink −#{s} rewrites"

  defp triage_line(_), do: ""

  defp slug(assay), do: String.replace(assay, ~r/[^a-zA-Z0-9]+/, "_")

  defp next_index(dir, seed, slug) do
    existing = Path.wildcard(Path.join(dir, "failure-#{seed}-#{slug}-*.txt"))
    length(existing) + 1
  end
end
