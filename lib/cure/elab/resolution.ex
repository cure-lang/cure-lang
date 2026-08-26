defmodule Cure.Elab.Resolution do
  @moduledoc """
  Surface-name resolution over canonical owner-qualified identities.

  Declaration identity is established by `Cure.Core.Env` and
  `Cure.Core.Inductive` while each module is elaborated. This module never
  rewrites Core terms or reconstructs binding identity after elaboration; it
  only maps a surface spelling to an already-registered canonical key.
  """

  alias Cure.Core.{Env, Inductive}

  @doc """
  Resolve a flattened dotted surface path to an already-canonical registry key.

  Qualified paths are exact. A missing qualified declaration is an error; the
  resolver deliberately does not fall back to a bare key, since doing so would
  make a qualified escape hatch depend on the importing environment.
  """
  @spec resolve_qualified(Env.t(), String.t(), :type | :value) :: {:ok, atom()} | :error
  def resolve_qualified(%Env{} = env, dotted, :value) do
    case Env.qualified_alias(env, dotted, :value) do
      {:ok, key} ->
        {:ok, key}

      :error ->
        env
        |> spellings(dotted)
        |> Enum.map(fn spelling ->
          segs = String.split(spelling, ".")
          {mod_segs, [last]} = Enum.split(segs, length(segs) - 1)
          {Cure.Elab.Name.qualify(Enum.join(mod_segs, "."), String.to_atom(last)), Enum.join(mod_segs, ".")}
        end)
        |> available_keys(env)
        |> try_keys(env, :value)
    end
  end

  def resolve_qualified(%Env{} = env, dotted, :type) do
    case Env.qualified_alias(env, dotted, :type) do
      {:ok, key} ->
        {:ok, key}

      :error ->
        env
        |> spellings(dotted)
        |> Enum.flat_map(fn spelling ->
          segs = String.split(spelling, ".")
          last = List.last(segs)
          {mod_segs, [explicit_last]} = Enum.split(segs, length(segs) - 1)
          mod = Enum.join(mod_segs, ".")

          [
            # Module==typename collapse: `Std.Nat` means `Std.Nat#Nat`.
            {Cure.Elab.Name.qualify(spelling, String.to_atom(last)), spelling},
            # Explicit `Mod.Type` spelling.
            {Cure.Elab.Name.qualify(mod, String.to_atom(explicit_last)), mod}
          ]
        end)
        |> available_keys(env)
        |> try_keys(env, :type)
    end
  end

  # The spellings a dotted path may denote, most specific first. The absolute
  # reading always wins; the owner-relative ones exist for a module nested
  # inside the current one, which its members have no other way to name. A
  # `fsm Machine` inside `mod Demo` lifts to the separate module `Demo.Machine`,
  # so `Demo` naming its own machine's `Event` writes `Machine.Event`.
  #
  # The path may already repeat part of the owner, because `LiftModule` inlines
  # the enclosing unit's declarations into the lifted module: the very same
  # `Machine.Event` is re-checked with owner `Demo.Machine`, where it means the
  # current module. So splice at every overlap -- the longest proper prefix of
  # the path that is also a suffix of the owner -- longest overlap first, with
  # the zero overlap (plain prepend) last.
  defp spellings(%Env{module_owner: owner}, dotted) when is_binary(owner) do
    owner_segs = String.split(owner, ".")
    segs = String.split(dotted, ".")

    relative =
      for k <- (length(segs) - 1)..0//-1,
          Enum.take(segs, k) == Enum.take(owner_segs, -k),
          do: Enum.join(owner_segs ++ Enum.drop(segs, k), ".")

    Enum.uniq([dotted | relative])
  end

  defp spellings(%Env{}, dotted), do: [dotted]

  defp available_keys(candidates, env) do
    candidates
    |> Enum.filter(fn {_key, owner} -> Env.qualified_module_available?(env, owner) end)
    |> Enum.map(&elem(&1, 0))
    |> Enum.uniq()
  end

  @doc """
  Resolve a bare spelling against canonical identities.

  The current module wins first. Otherwise an actual bare key is accepted for
  compatibility with ownerless synthetic environments. Finally, exactly one
  canonical suffix may resolve; multiple direct providers are ambiguous.
  """
  @spec resolve_bare(Env.t(), atom()) :: {:ok, atom()} | :none | {:ambiguous, [String.t()]}
  def resolve_bare(%Env{} = env, bare) do
    case local_or_bare_key(env, bare) do
      {:ok, key} -> {:ok, key}
      :none -> resolve_canonical_suffix(env, bare)
    end
  end

  defp local_or_bare_key(%Env{module_owner: owner} = env, bare) do
    candidates =
      if is_binary(owner),
        do: [Cure.Elab.Name.qualify(owner, bare), bare],
        else: [bare]

    case Enum.find(candidates, &present_in_any_namespace?(env, &1)) do
      nil -> :none
      key -> {:ok, key}
    end
  end

  defp resolve_canonical_suffix(env, bare) do
    matches =
      [env.ctors, env.families, env.defs]
      |> Enum.flat_map(&Env.provider_keys(&1, bare))
      |> Enum.uniq()
      |> Enum.map(fn key -> {Cure.Elab.Name.owner(key), key} end)
      |> Enum.filter(fn {_owner, key} -> Env.bare_key_available?(env, key) end)
      |> prefer_direct(env.import_modules)

    case matches do
      [{_owner, key}] -> {:ok, key}
      [] -> :none
      many -> {:ambiguous, Enum.map(many, &elem(&1, 0)) |> Enum.uniq()}
    end
  end

  @doc """
  Every in-scope canonical def key that provides `bare`. The local module's
  members win first (a local set shadows same-named imports entirely, and a
  single local def collapses the result to one); only when none are local do
  `prefer_direct`-scoped import providers remain. Returns `[]` (unknown),
  `[key]` (single provider — not an overload set), or `[k0, k1, …]` (an
  overload set). Used by the applied call site to prune by argument type.

  Ordering matters: `prefer_local` precedes `prefer_direct` so a module's own
  overload members are never dropped for not appearing in its own
  `import_modules`, which would otherwise let a prelude provider (e.g.
  `Std.Nat#plus`) masquerade as the sole candidate for a locally-overloaded name.
  """
  @spec overload_candidates(Env.t(), atom()) :: [atom()]
  def overload_candidates(%Env{} = env, bare) do
    env.defs
    |> Env.provider_keys(bare)
    |> Enum.map(fn key -> {Cure.Elab.Name.owner(key), key} end)
    |> prefer_local(env.module_owner)
    |> Enum.filter(fn {_owner, key} -> Env.bare_key_available?(env, key) end)
    |> prefer_direct(env.import_modules)
    |> Enum.map(&elem(&1, 1))
    |> Enum.uniq()
  end

  # A member owned by the current module shadows same-named imports entirely.
  defp prefer_local(matches, owner) when is_binary(owner) do
    case Enum.filter(matches, fn {o, _key} -> o == owner end) do
      [] -> matches
      locals -> locals
    end
  end

  defp prefer_local(matches, _owner), do: matches

  defp present_in_any_namespace?(env, key) do
    Map.has_key?(env.families, key) or Map.has_key?(env.ctors, key) or Map.has_key?(env.defs, key)
  end

  # A direct import shadows a transitive re-export. If two direct providers
  # remain, the spelling is genuinely ambiguous.
  defp prefer_direct(matches, direct_modules) do
    case Enum.filter(matches, fn {owner, _key} -> MapSet.member?(direct_modules, owner) end) do
      [] -> matches
      directs -> directs
    end
  end

  @doc "Return the origin and canonical key of a shadowed bare spelling, if any."
  @spec shadowed_origin(Env.t(), atom()) :: {:ok, String.t(), atom()} | :error
  def shadowed_origin(%Env{} = env, bare) do
    case local_or_bare_key(env, bare) do
      {:ok, _key} ->
        :error

      :none ->
        Enum.find_value([env.ctors, env.families, env.defs], fn table ->
          Enum.find_value(Env.provider_keys(table, bare), fn key ->
            owner = Cure.Elab.Name.owner(key)
            if Env.bare_key_available?(env, key), do: {:ok, owner, key}
          end)
        end) || :error
    end
  end

  # Surface type spellings the language has withdrawn. `Pid` and `Ref` named the
  # unrestricted process surface; the formal OTP API replaced them with the
  # indexed `Std.Otp.Pid(m)`, `MonitorRef` and `TimerRef`. They are deliberately
  # NOT registered anywhere, so a stale declaration is caught instead of quietly
  # believed — but "resolves to nothing" is exactly what a free type variable
  # looks like, so every consumer that classifies an unresolved uppercase name
  # has to be told these two are withdrawn names rather than variables.
  @retired_type_names ~w(Pid Ref)

  @doc """
  Surface type names the language has withdrawn, with no registered declaration.

  One list, because two consumers must agree: the elaborator's name cascade
  reports `:retired_process_type` for these, and the `cure migrate` lint has to
  leave them spelled as authored so that diagnostic is what the porter sees.
  If the lint decided independently it would lowercase them into fresh type
  variables and erase the very error that tells the author what to write.
  """
  @spec retired_type_names() :: [String.t()]
  def retired_type_names, do: @retired_type_names

  @doc "Whether `name` is a withdrawn surface type spelling."
  @spec retired_type_name?(atom() | String.t()) :: boolean()
  def retired_type_name?(name) when is_atom(name), do: retired_type_name?(Atom.to_string(name))
  def retired_type_name?(name) when is_binary(name), do: name in @retired_type_names
  def retired_type_name?(_name), do: false

  @doc """
  Return all canonical providers of a bare spelling when no local or bare
  winner exists. This is used to produce the targeted ambiguity diagnostic.
  """
  @spec ambiguous_modules(Env.t(), atom()) :: [String.t()]
  def ambiguous_modules(%Env{} = env, bare) do
    case local_or_bare_key(env, bare) do
      {:ok, _key} ->
        []

      :none ->
        owners =
          [env.ctors, env.families, env.defs]
          |> Enum.flat_map(&Env.provider_keys(&1, bare))
          |> Enum.filter(&Env.bare_key_available?(env, &1))
          |> Enum.map(&Cure.Elab.Name.owner/1)
          |> Enum.uniq()

        case Enum.filter(owners, &MapSet.member?(env.import_modules, &1)) do
          [] -> owners
          direct -> direct
        end
    end
  end

  defp try_keys(keys, env, slot) do
    present? =
      case slot do
        :type -> fn key -> Inductive.family?(env, key) or type_definition?(env, key) end
        :value -> fn key -> not is_nil(Inductive.get_ctor(env, key)) or Map.has_key?(env.defs, key) end
      end

    case Enum.find(keys, present?) do
      nil -> :error
      key -> {:ok, key}
    end
  end

  defp type_definition?(%Env{defs: defs}, key),
    do: match?(%{type: {:type, _level}}, Map.get(defs, key))
end
