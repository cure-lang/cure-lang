defmodule Cure.Core.ProofSnapshotWire do
  @moduledoc """
  Render the existing bounded `ProofSnapshot.capture/1` view to the complete
  source format formalised in `Core.WireSnapshot`.

  This is not registry extraction refinement, admission or certification.
  Capture's exclusions remain in force; no unvalidated captured-map API is
  exposed. Every captured declaration, layout, optional raw body and both
  certification flags are retained. Native typing is checked independently.

  Record tags 15/16/17/18 denote constructor/family/global/source inputs.
  A record is `[tag, payload]`, with its fields as right-nested two-child
  products. Lists are node lists, optionals empty/singleton lists, and scalar
  booleans/grades/levels exact unary atoms. Names are table indices; terms
  reuse `ProofWire`'s canonical producer. Tables are supplied identities,
  not authenticated registries.
  """
  alias Cure.Core.{Env, ProofSnapshot, ProofWire, Term}

  @spec encode(Env.t(), ProofWire.table()) ::
          {:ok, String.t()} | {:error, ProofSnapshot.error() | ProofWire.error()}
  def encode(env, table) do
    if valid_table?(table) do
      with {:ok, snapshot} <- ProofSnapshot.capture(env) do
        # Capture currently rejects builtin registries. Assert the audited
        # field rather than silently dropping it if that contract changes.
        [] = snapshot["builtins"]

        record(18, [
          vector(snapshot["families"], &family(&1, table)),
          vector(snapshot["globals"], &global(&1, table)),
          {:ok, list([])}
        ])
      end
    else
      {:error, {:malformed_table, table}}
    end
  end

  defp family(entry, table) do
    record(16, [
      name(entry["name"], table),
      telescope(entry["params"], table),
      telescope(entry["indices"], table),
      {:ok, atom(entry["level"])},
      vector(entry["constructors"], &constructor(&1, table)),
      boolean(entry["opaque"])
    ])
  end

  defp constructor(entry, table) do
    declaration =
      product([
        name(entry["name"], table),
        telescope(entry["args"], table),
        vector(entry["result_params"], &term(&1, table)),
        vector(entry["result_indices"], &term(&1, table))
      ])

    record(15, [declaration, vector(entry["quantities"], &grade/1), vector(entry["explicit"], &boolean/1)])
  end

  defp global(entry, table) do
    record(17, [
      name(entry["name"], table),
      term(entry["type"], table),
      optional(entry["body"], &term(&1, table)),
      optional(entry["quantities"], &vector(&1, fn q -> grade(q) end)),
      optional(entry["explicit"], &vector(&1, fn b -> boolean(b) end)),
      boolean(entry["certified"]),
      boolean(entry["totality_certified"])
    ])
  end

  defp telescope(entries, table),
    do: vector(entries, &product([name(&1["name"], table), term(&1["type"], table)]))

  defp term(external, table), do: ProofWire.encode_term(Term.from_external(external), table)

  defp name(value, table) do
    case ProofWire.index_of(value, table) do
      {:ok, index} -> {:ok, atom(index)}
      :error -> {:error, {:unknown_name, value}}
    end
  end

  defp boolean(false), do: {:ok, atom(0)}
  defp boolean(true), do: {:ok, atom(1)}
  defp grade("erased"), do: {:ok, atom(0)}
  defp grade("linear"), do: {:ok, atom(1)}
  defp grade("affine"), do: {:ok, atom(2)}
  defp grade("unrestricted"), do: {:ok, atom(3)}

  defp optional(nil, _encode), do: {:ok, list([])}

  defp optional(value, encode) do
    with {:ok, characters} <- encode.(value), do: {:ok, list([characters])}
  end

  defp vector(values, encode) do
    with {:ok, characters} <- values |> Enum.map(encode) |> collect(), do: {:ok, list(characters)}
  end

  defp product(values) do
    with {:ok, characters} <- collect(values), do: {:ok, nested(characters)}
  end

  defp record(tag, values) do
    with {:ok, characters} <- product(values), do: {:ok, list([atom(tag), characters])}
  end

  defp nested([last]), do: last
  defp nested([first | rest]), do: list([first, nested(rest)])
  defp collect([]), do: {:ok, []}

  defp collect([{:ok, value} | rest]) do
    with {:ok, tail} <- collect(rest), do: {:ok, [value | tail]}
  end

  defp collect([{:error, _reason} = error | _rest]), do: error
  defp atom(number), do: String.duplicate("1", number) <> ";"
  defp list(children), do: "(" <> Enum.join(children) <> ")"
  defp valid_table?([]), do: true
  defp valid_table?([name | rest]), do: valid_name?(name) and valid_table?(rest)
  defp valid_table?(_table), do: false
  defp valid_name?(name) when is_atom(name), do: true
  defp valid_name?(name) when is_binary(name), do: String.valid?(name)
  defp valid_name?(_name), do: false
end
