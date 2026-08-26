defmodule Cure.Compiler.ModulePipeline.Cache do
  @moduledoc """
  Reuse of previously checked interfaces.

  The cache is nothing but the interfaces a previous run published. That is what
  makes invalidation follow the checked semantic graph rather than the order
  files were discovered in: a module may be reused exactly when its own source
  is unchanged *and* every dependency still has the interface hash that was
  recorded when it was last checked. A body-only change to a provider therefore
  rebuilds the provider alone, because its interface hash is unchanged by
  construction.
  """

  alias Cure.Compiler.ModuleInterface
  alias Cure.Compiler.ModulePipeline.Interface

  @doc "Every interface a previous run left in `root`, keyed by module name."
  @spec load(Path.t() | nil) :: %{String.t() => ModuleInterface.t()}
  def load(nil), do: %{}

  def load(root) do
    case Interface.load_roots([root]) do
      {:ok, interfaces} -> interfaces
      # A cache that cannot be read is a cache miss, never an error: the run
      # still has the sources, and the worst outcome is doing the work again.
      {:error, _reason} -> %{}
    end
  end

  @doc "Persist this run's interfaces for the next one."
  @spec store(Path.t() | nil, %{term() => ModuleInterface.t()}) :: :ok
  def store(nil, _interfaces), do: :ok

  def store(root, interfaces) do
    File.rm_rf(root)

    interfaces
    |> Map.values()
    |> Enum.uniq_by(& &1.module_name)
    |> Enum.each(&Interface.write(&1, root))

    :ok
  end

  @doc """
  Whether every module in `component` can be taken from the cache unchecked.

  A component is reused as a unit: its members' interfaces were frozen together
  and cannot be reasoned about one at a time.
  """
  @spec reusable(%{String.t() => ModuleInterface.t()}, [tuple()], map(), map()) ::
          {:ok, %{tuple() => ModuleInterface.t()}} | :stale
  def reusable(cached, component, entries, published) do
    members = MapSet.new(component, &elem(&1, 1))

    Enum.reduce_while(component, {:ok, %{}}, fn identity, {:ok, reused} ->
      entry = Map.fetch!(entries, identity)

      case Map.fetch(cached, entry.module_name) do
        {:ok, interface} ->
          if interface.source_hash == entry.source_hash and
               dependencies_unchanged?(interface, published, members) do
            {:cont, {:ok, Map.put(reused, identity, interface)}}
          else
            {:halt, :stale}
          end

        :error ->
          {:halt, :stale}
      end
    end)
  end

  # The recorded hashes are the module's own statement of what it was checked
  # against. A dependency inside the same component is not compared: it is being
  # decided in the same breath.
  defp dependencies_unchanged?(interface, published, members) do
    Enum.all?(interface.dependency_interface_hashes, fn {module_name, hash} ->
      MapSet.member?(members, module_name) or published[module_name] == hash
    end)
  end
end
