defmodule Cure.Compiler.ModulePipeline.Conformance do
  @moduledoc """
  Reading the coherence table back out of checked interfaces.

  A conformance belongs to exactly one module — the one whose published
  interface carries it — and every consumer that can see it selects that same
  one. Both questions are answered from the published interfaces alone, never
  from a live environment, so the answer cannot depend on the order the modules
  happened to be checked in.
  """

  alias Cure.Elab.Name

  @type entry :: {String.t(), map()}

  @doc "The module that publishes the conformance of `type_name` to `interface_name`."
  @spec owner(map(), String.t(), String.t()) :: String.t() | nil
  def owner(interfaces, interface_name, type_name) do
    case entries(interfaces, interface_name, type_name) do
      [{owner, _reference}] -> owner
      _ -> nil
    end
  end

  @doc """
  How many modules publish that conformance.

  Anything other than one is an incoherent universe; reporting the count rather
  than a boolean keeps the distinction between "absent" and "overlapping".
  """
  @spec count(map(), String.t(), String.t()) :: non_neg_integer()
  def count(interfaces, interface_name, type_name),
    do: length(entries(interfaces, interface_name, type_name))

  @doc """
  What a consumer selects for `interface_name`/`type_name`, as canonical data.

  The descriptor deliberately drops the instance's source syntax: two runs that
  agree on the instance must compare equal even though their spans differ.
  """
  @spec selected(map(), [String.t()], String.t(), String.t()) :: {:ok, map()} | {:error, term()}
  def selected(interfaces, visible, interface_name, type_name) do
    interfaces
    |> entries(interface_name, type_name)
    |> Enum.filter(fn {owner, _reference} -> owner in visible end)
    |> case do
      [{owner, reference}] -> {:ok, descriptor(owner, reference)}
      [] -> {:error, {:no_visible_conformance, interface_name, type_name}}
      several -> {:error, {:overlapping_conformance, several |> Enum.map(&elem(&1, 0)) |> Enum.sort()}}
    end
  end

  defp descriptor(owner, reference) do
    %{
      owner: owner,
      interface: Map.get(reference, :iface),
      head: Map.get(reference, :head),
      name: Map.get(reference, :as),
      methods: reference |> Map.get(:methods, %{}) |> Enum.sort()
    }
  end

  defp entries(interfaces, interface_name, type_name) do
    key = {String.to_atom(interface_name), head(type_name)}

    interfaces
    |> Enum.flat_map(fn {_identity, interface} ->
      case anonymous_instances(interface) do
        %{^key => reference} -> [{interface.module_name, reference}]
        _ -> []
      end
    end)
    |> Enum.sort_by(&elem(&1, 0))
  end

  defp anonymous_instances(interface) do
    case Map.get(interface.extension_payloads, :coherence) do
      %{anon: anon} -> anon
      _ -> %{}
    end
  end

  # A conformance head is a canonical family key, so the written `Owner.Box` and
  # the stored `Owner#Box` are the same head spelled two ways. The written form
  # separates owner from base with a dot; only the last segment is the type.
  defp head(type_name) do
    case String.split(type_name, ".") do
      [base] -> String.to_atom(base)
      parts -> Name.qualify(parts |> Enum.drop(-1) |> Enum.join("."), List.last(parts))
    end
  end
end
