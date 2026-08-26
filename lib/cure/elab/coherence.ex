defmodule Cure.Elab.Coherence do
  @moduledoc """
  The coherence registry: the compile-time table of typeclass instances.

  Anonymous instances are keyed on `(interface, head type constructor)` and must
  be globally unique — a second instance for the same pair is an overlap error
  (this is what "global coherence" means). Named instances (`... as strictInt`)
  are keyed on their name, are exempt from the global-uniqueness rule, and are
  selected explicitly rather than by resolution.

  A registered value (`ref`) is an elaborator-level descriptor of the instance:
  `%{iface, head, methods: %{method_atom => mangled_global_atom}, as}`. Method
  bodies live as ordinary (mangled) global defs; `Cure.Elab.Resolve` reads this
  table to inline them at concrete sites or thread a runtime dictionary at
  abstract sites.
  """

  defstruct anon: %{}, named: %{}, anon_origins: %{}, named_origins: %{}

  @type t :: %__MODULE__{
          anon: %{{atom(), atom()} => map()},
          named: %{atom() => map()},
          anon_origins: %{{atom(), atom()} => map()},
          named_origins: %{atom() => map()}
        }

  @doc "An empty registry."
  @spec new() :: t()
  def new, do: %__MODULE__{}

  @doc """
  Register an anonymous instance for `(iface, head)`. A pre-existing entry for
  the same pair is an overlap error.
  """
  @spec register_anon(t(), atom(), atom(), map()) :: {:ok, t()} | {:error, term()}
  def register_anon(%__MODULE__{} = c, iface, head, ref) do
    register_anon(c, iface, head, ref, %{})
  end

  @doc "Register an anonymous instance while retaining inert source context for overlap diagnostics."
  @spec register_anon(t(), atom(), atom(), map(), map()) :: {:ok, t()} | {:error, term()}
  def register_anon(%__MODULE__{anon: anon, anon_origins: origins} = c, iface, head, ref, origin) do
    key = {iface, head}

    if Map.has_key?(anon, key) do
      first =
        Cure.Elab.SourceMetadata.instance_origins(:anonymous, key)
        |> List.first()
        |> then(&(&1 || Map.get(origins, key, %{})))

      {:error,
       {:overlapping_instance,
        %{
          interface: iface,
          head: head,
          first_span: Map.get(first, :span),
          second_span: Map.get(origin, :span),
          first_for: Map.get(first, :for),
          second_for: Map.get(origin, :for)
        }}}
    else
      :ok = Cure.Elab.SourceMetadata.put_instance_origin(:anonymous, key, origin)

      {:ok,
       %{
         c
         | anon: Map.put(anon, key, ref),
           anon_origins: Map.put(origins, key, Map.drop(origin, [:span]))
       }}
    end
  end

  @doc """
  Register a named instance under `name`. A pre-existing name is an overlap
  error (`iface`/`head` are carried for a descriptive message).
  """
  @spec register_named(t(), atom(), {atom(), atom()}, map()) :: {:ok, t()} | {:error, term()}
  def register_named(%__MODULE__{} = c, name, {iface, head}, ref) do
    register_named(c, name, {iface, head}, ref, %{})
  end

  @doc "Register a named instance while retaining inert source context for duplicate-name diagnostics."
  @spec register_named(t(), atom(), {atom(), atom()}, map(), map()) :: {:ok, t()} | {:error, term()}
  def register_named(
        %__MODULE__{named: named, named_origins: origins} = c,
        name,
        {iface, head},
        ref,
        origin
      ) do
    if Map.has_key?(named, name) do
      first =
        Cure.Elab.SourceMetadata.instance_origins(:named, name)
        |> List.first()
        |> then(&(&1 || Map.get(origins, name, %{})))

      {:error,
       {:overlapping_named_instance,
        %{
          name: name,
          interface: iface,
          head: head,
          first_interface: Map.get(first, :interface),
          first_head: Map.get(first, :head),
          first_span: Map.get(first, :span),
          second_span: Map.get(origin, :span),
          first_for: Map.get(first, :for),
          second_for: Map.get(origin, :for)
        }}}
    else
      :ok = Cure.Elab.SourceMetadata.put_instance_origin(:named, name, origin)

      {:ok,
       %{
         c
         | named: Map.put(named, name, ref),
           named_origins: Map.put(origins, name, Map.drop(origin, [:span]))
       }}
    end
  end

  @doc "Look up the anonymous instance for `(iface, head)`."
  @spec lookup_anon(t() | nil, atom(), atom()) :: {:ok, map()} | {:error, term()}
  def lookup_anon(%__MODULE__{anon: anon}, iface, head) do
    case Map.fetch(anon, {iface, head}) do
      {:ok, ref} -> {:ok, ref}
      :error -> {:error, {:no_instance, iface, head}}
    end
  end

  def lookup_anon(nil, iface, head), do: {:error, {:no_instance, iface, head}}

  @doc "Look up a named instance by name."
  @spec lookup_named(t() | nil, atom()) :: {:ok, map()} | {:error, term()}
  def lookup_named(%__MODULE__{named: named}, name) do
    case Map.fetch(named, name) do
      {:ok, ref} -> {:ok, ref}
      :error -> {:error, {:no_named_instance, name}}
    end
  end

  def lookup_named(nil, name), do: {:error, {:no_named_instance, name}}

  @doc """
  Union two coherence registries — used when an importing module merges an
  imported module's instances into its own env. A `nil` registry is the empty
  registry. Later (right) registrations win on key collision; genuine
  cross-module overlap is a global-coherence concern surfaced at registration,
  not here (v1 keeps the merge total so imports never fail to combine).
  """
  @spec merge(t() | nil, t() | nil) :: t() | nil
  def merge(nil, other), do: other
  def merge(other, nil), do: other

  def merge(
        %__MODULE__{anon: a1, named: n1, anon_origins: o1, named_origins: no1},
        %__MODULE__{anon: a2, named: n2, anon_origins: o2, named_origins: no2}
      ),
      do: %__MODULE__{
        anon: Map.merge(a1, a2),
        named: Map.merge(n1, n2),
        anon_origins: Map.merge(o1, o2),
        named_origins: Map.merge(no1, no2)
      }
end
