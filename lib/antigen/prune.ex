defmodule Antigen.Prune do
  @moduledoc """
  Antibody-corpus pruning across kernel shape changes (migration design, C2). Walks
  a corpus file, re-checks each record against the LIVE kernel via the shared replay
  registry, keeps the ones that still decode and replay `:ok`, and moves the rest
  **verbatim** to a retirement store, annotated with the reason. Never rewrites a
  term; never silently deletes. A run that retires nothing leaves the corpus
  byte-identical (idempotent).
  """
  alias Antigen.{Corpus, Runner}

  @type reason ::
          {:decode_error, term()}
          | {:unknown_assay, String.t()}
          | {:label_drift, term()}
          | {:replay_error, String.t()}
          | {:unexpected, term()}

  @type tally :: %{kept: non_neg_integer(), retired: non_neg_integer(), reasons: [reason()]}

  @doc """
  Prune `corpus_path`. Kept records (decode AND replay `:ok`) are rewritten back
  byte-identically; retired records are appended to `retired_path` with their reason.
  `registry` defaults to the full `Runner.replay_registry/0`.
  """
  @spec prune(String.t(), String.t(), %{String.t() => module()}) :: tally()
  def prune(corpus_path, retired_path, registry \\ Runner.replay_registry()) do
    {kept, retired} =
      corpus_path
      |> Corpus.record_lines()
      |> Enum.reduce({[], []}, fn line, {keep, ret} ->
        case classify(line, registry) do
          :keep -> {[line | keep], ret}
          {:retire, reason} -> {keep, [{line, reason} | ret]}
        end
      end)

    kept = Enum.reverse(kept)
    retired = Enum.reverse(retired)

    # Only rewrite when something was retired, so an all-green corpus is left
    # byte-identical (no spurious diff on a no-op run).
    unless retired == [], do: rewrite(corpus_path, kept)
    append_retired(retired_path, retired)

    %{kept: length(kept), retired: length(retired), reasons: Enum.map(retired, &elem(&1, 1))}
  end

  # decodes AND replays :ok → keep; anything else → retire with a reason.
  defp classify(line, registry) do
    case Corpus.decode_record(line) do
      {:error, reason} ->
        {:retire, {:decode_error, reason}}

      {:ok, c} ->
        case Map.fetch(registry, c.assay) do
          :error -> {:retire, {:unknown_assay, c.assay}}
          {:ok, mod} -> replay(mod, c)
        end
    end
  end

  defp replay(mod, c) do
    case apply(mod, :run, [c]) do
      :ok -> :keep
      {:violation, v} -> {:retire, {:label_drift, v}}
      other -> {:retire, {:unexpected, other}}
    end
  rescue
    e -> {:retire, {:replay_error, Exception.message(e)}}
  end

  # Atomically rewrite the corpus with only the kept (verbatim) lines.
  defp rewrite(path, kept) do
    tmp = path <> ".pruning"
    content = if kept == [], do: "", else: Enum.join(kept, "\n") <> "\n"
    File.write!(tmp, content)
    File.rename!(tmp, path)
  end

  defp append_retired(_path, []), do: :ok

  defp append_retired(path, retired) do
    File.mkdir_p!(Path.dirname(path))

    chunk =
      Enum.map_join(retired, "\n", fn {line, reason} ->
        "# retired: #{inspect(reason)}\n#{line}"
      end)

    File.write!(path, newline_guard(path) <> chunk <> "\n", [:append])
  end

  # A leading "\n" iff the file is non-empty and does not already end in one, so an
  # appended block can never glue onto a hand-edited last line.
  defp newline_guard(path) do
    case File.read(path) do
      {:ok, ""} -> ""
      {:ok, content} -> if String.ends_with?(content, "\n"), do: "", else: "\n"
      _ -> ""
    end
  end
end
