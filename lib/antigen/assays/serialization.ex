defmodule Antigen.Assays.Serialization do
  @moduledoc """
  `serialize/roundtrip` — a metamorphic vertical. `Cure.Core.Serialize` must be
  LOSSLESS: `decode(encode(t)) == {:ok, t}` for every well-formed term. A mismatch
  (or a decode error) is an infection — the corpus/replay pipeline would silently
  corrupt or drop that term. Exercises the full encode AND decode path in-process
  (the coverage campaign banks but never replays, so decode is otherwise cold).
  """
  alias Antigen.Challenge
  alias Cure.Core.Serialize

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :serialize, payload: %{term: t}}) do
    encoded = Serialize.encode(t)

    case Serialize.decode(encoded) do
      {:ok, ^t} -> :ok
      {:ok, other} -> {:violation, {:roundtrip_mismatch, t, other}}
      {:error, reason} -> {:violation, {:decode_failed, t, reason}}
    end
  end

  # Decode robustness: `decode` must be total — malformed input errors cleanly (never
  # crashes/loops); well-formed input decodes to a Core TERM (never a bare scalar), and that
  # term must re-encode and roundtrip. This exercises enc's hole/absurd clauses, which the
  # well_formed? gate keeps out of the term-roundtrip vertical.
  def run(%Challenge{kind: :decode_probe, label: :invalid_sexp, payload: %{input: s}}) do
    case Serialize.decode(s) do
      {:error, _} -> :ok
      got -> {:violation, {:decode_probe, :invalid_sexp, s, got}}
    end
  end

  def run(%Challenge{kind: :decode_probe, label: :valid_sexp, payload: %{input: s}}) do
    case Serialize.decode(s) do
      {:ok, t} when is_tuple(t) ->
        case Serialize.decode(Serialize.encode(t)) do
          {:ok, ^t} -> :ok
          got -> {:violation, {:reencode_mismatch, s, t, got}}
        end

      got ->
        {:violation, {:decode_probe, :valid_sexp, s, got}}
    end
  end
end
