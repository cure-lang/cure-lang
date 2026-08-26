defmodule Cure.Elab.Name do
  @moduledoc """
  Canonical identities for elaborated global names.

  Core keeps globals as `{:global, atom()}`. This module owns the elaborator's
  spelling convention for module-owned names so registration and every later
  consumer agree on the same identity without open-coded string parsing.
  """

  @separator "#"
  @overload_separator "~"
  @split_cache_key {__MODULE__, :split_cache}
  @split_cache_limit 4_096

  @type owner :: String.t() | atom()
  @type base :: String.t() | atom()

  @doc "Return the canonical atom for a module-owned global name."
  @spec qualify(owner(), base()) :: atom()
  def qualify(owner, base) do
    String.to_atom(normalize_owner(owner) <> @separator <> normalize_base(base))
  end

  @doc """
  Split a canonical name into `{owner, base}` in a single pass.

  The owner is `nil` for a bare name, and for a name whose text before the
  separator is not a valid owner — a content-derived identity like
  `Union<Int|Std.Bool#Bool>` is its own base, not `Bool` owned by
  `Union<Int|Std.Bool`.

  Callers that need both halves should prefer this over `owner/1` and `base/1`:
  it decides the split once rather than twice, and name resolution asks this
  question for every key in a table on every unresolved lookup.
  """
  @spec split(atom() | String.t()) :: {String.t() | nil, String.t()}
  def split(name) when is_atom(name) do
    cache = Process.get(@split_cache_key, %{})

    case Map.fetch(cache, name) do
      {:ok, split} ->
        split

      :error ->
        split = split(Atom.to_string(name))

        if map_size(cache) < @split_cache_limit do
          Process.put(@split_cache_key, Map.put(cache, name, split))
        end

        split
    end
  end

  def split(name) when is_binary(name) do
    case :binary.split(name, @separator) do
      [owner, base] -> if valid_owner?(owner), do: {owner, base}, else: {nil, name}
      [bare] -> {nil, bare}
    end
  end

  @doc "Return the module owner encoded in a canonical name, or nil for a bare atom."
  @spec owner(atom() | String.t()) :: String.t() | nil
  def owner(name) when is_atom(name) or is_binary(name), do: split(name) |> elem(0)

  def owner(_name), do: nil

  @doc "Return the basename encoded in a canonical name, or the original bare name."
  @spec base(atom() | String.t()) :: String.t() | nil
  def base(name) when is_atom(name) or is_binary(name), do: split(name) |> elem(1)

  def base(_name), do: nil

  @doc "Whether a global identity carries an owner qualifier."
  @spec qualified?(atom() | String.t()) :: boolean()
  def qualified?(name), do: owner(name) != nil

  @doc "Append an overload discriminator (`~<ordinal>`) to the base of a key."
  @spec overload_key(atom() | String.t(), non_neg_integer()) :: atom()
  def overload_key(base_key, ordinal) when is_integer(ordinal) and ordinal >= 0 do
    String.to_atom(normalize_base(base_key) <> @overload_separator <> Integer.to_string(ordinal))
  end

  @doc "Whether a key's base part carries an overload discriminator."
  @spec overload_member?(atom() | String.t()) :: boolean()
  def overload_member?(key) do
    key |> base() |> to_string() |> String.contains?(@overload_separator)
  end

  @doc "The base name with any `~<ordinal>` overload discriminator removed."
  @spec overload_base(atom() | String.t()) :: String.t()
  def overload_base(key) do
    key |> base() |> to_string() |> String.split(@overload_separator, parts: 2) |> hd()
  end

  defp normalize_owner(owner) when is_atom(owner), do: Atom.to_string(owner)
  defp normalize_owner(owner) when is_binary(owner), do: owner

  defp normalize_base(base) when is_atom(base), do: Atom.to_string(base)
  defp normalize_base(base) when is_binary(base), do: base

  # `[A-Za-z_][A-Za-z0-9_.]*`, anchored at both ends, as a byte scan rather than
  # a regex. `owner/1` and `base/1` sit under the elaborator's name resolution,
  # which asks this question millions of times per elaboration; a `Regex.match?/2`
  # here cost roughly a quarter of a cold compile in `re:run`/`re:import` alone.
  defp valid_owner?(<<c, rest::binary>>) when c in ?A..?Z or c in ?a..?z or c == ?_,
    do: owner_rest?(rest)

  defp valid_owner?(_owner), do: false

  defp owner_rest?(<<>>), do: true

  defp owner_rest?(<<c, rest::binary>>)
       when c in ?A..?Z or c in ?a..?z or c in ?0..?9 or c == ?_ or c == ?.,
       do: owner_rest?(rest)

  defp owner_rest?(_rest), do: false
end
