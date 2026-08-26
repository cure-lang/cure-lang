defmodule Cure.Project.Proof do
  @moduledoc """
  Proof-certificate collection, serialization, and offline verification
  for Cure packages (v0.32.0).

  A `.cureproof` artifact embeds the type-checker's proof certificates
  into the published tarball so consumers can re-verify the publisher's
  claims offline without re-running the full SMT solver from scratch.

  ## File format

      "CUREPROOF\\0" <> <<0x01>> <> gzip(term_to_binary(certificates))

  where `certificates` is a list of `%{module, kind, statement, witness}`
  maps (see `t:certificate/0`).

  ## Certificate kinds

    * `:equality`   -- an `Eq(T, a, b)` proof checked by definitional
      equality; the witness is `:cure_refl` or an equivalent term.
    * `:smt`        -- an SMT-discharged obligation; the witness is the
      serialized Z3 model that satisfies the negation of the goal.
    * `:totality`   -- a structural-decrease argument; the witness is
      the SCC map and the decreasing parameter index.
  """

  @magic "CUREPROOF\0"
  @vsn <<0x01>>

  @type kind :: :equality | :smt | :totality

  @type certificate :: %{
          module: String.t(),
          kind: kind(),
          statement: term(),
          witness: term()
        }

  @ets_table :cure_proof_certs

  # -- Collection ----------------------------------------------------------------

  @doc """
  Compile every `.cure` source under `root` in `proof_collect` mode,
  accumulating proof certificates emitted by the type-checker.

  Returns `{:ok, [certificate()]}` on success. Parse or type errors in
  individual files are silently skipped (they would already have been
  reported by `cure publish`'s prior compile step).
  """
  @spec collect(String.t()) :: {:ok, [certificate()]}
  def collect(root \\ ".") when is_binary(root) do
    cure_files =
      root
      |> Path.join("lib/**/*.cure")
      |> Path.wildcard()
      |> Enum.sort()

    # Create (or reset) the collection ETS table.
    try_create_ets()

    Enum.each(cure_files, fn file ->
      _ = Cure.Compiler.compile_file(file, proof_collect: true, emit_events: false)
    end)

    certs = drain_ets()
    {:ok, certs}
  end

  # -- Serialization -------------------------------------------------------------

  @doc """
  Serialize a list of certificates to the `.cureproof` binary format.
  """
  @spec serialize([certificate()]) :: binary()
  def serialize(certificates) when is_list(certificates) do
    body = :zlib.gzip(:erlang.term_to_binary(certificates))
    @magic <> @vsn <> body
  end

  @doc """
  Deserialize a `.cureproof` binary.

  Returns `{:ok, [certificate()]}` or `{:error, :E067}` on schema
  mismatch, `{:error, :corrupt}` on malformed data.
  """
  @spec deserialize(binary()) :: {:ok, [certificate()]} | {:error, :E067 | :corrupt}
  def deserialize(<<@magic, version::binary-size(1), rest::binary>>) do
    if version == @vsn do
      try do
        certs = rest |> :zlib.gunzip() |> :erlang.binary_to_term([:safe])
        {:ok, certs}
      rescue
        _ -> {:error, :corrupt}
      end
    else
      {:error, :E067}
    end
  end

  def deserialize(_), do: {:error, :corrupt}

  # -- Verification --------------------------------------------------------------

  @doc """
  Verify a list of certificates offline.

  Returns `{:ok, count}` where `count` is the number of certificates
  verified, or `{:error, [{module, statement, reason}]}` listing every
  failing certificate.
  """
  @spec verify([certificate()]) :: {:ok, non_neg_integer()} | {:error, list()}
  def verify(certificates) when is_list(certificates) do
    failures =
      Enum.flat_map(certificates, fn cert ->
        case Cure.Project.Proof.Verifier.verify_one(cert) do
          :ok -> []
          {:error, reason} -> [{cert.module, cert.statement, reason}]
        end
      end)

    case failures do
      [] -> {:ok, length(certificates)}
      _ -> {:error, failures}
    end
  end

  # -- ETS helpers ---------------------------------------------------------------

  @doc false
  # Called by the compiler's proof_collect hook to deposit a certificate.
  @spec deposit(certificate()) :: true
  def deposit(cert) do
    try_create_ets()
    :ets.insert(@ets_table, {make_ref(), cert})
  end

  defp try_create_ets do
    case :ets.info(@ets_table) do
      :undefined ->
        :ets.new(@ets_table, [:named_table, :public, :bag])

      _ ->
        :ets.delete_all_objects(@ets_table)
    end
  end

  defp drain_ets do
    certs =
      @ets_table
      |> :ets.tab2list()
      |> Enum.map(fn {_ref, cert} -> cert end)

    :ets.delete_all_objects(@ets_table)
    certs
  end
end
