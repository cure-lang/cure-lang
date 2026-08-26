defmodule Cure.Elab.ProofDisplay do
  @moduledoc "Small source-oriented renderer for proof diagnostics and editor help."

  alias Cure.Elab.Name

  def format(term, names \\ [])
  def format({:var, index}, names), do: Enum.at(names, index, "_#{index}")
  def format({:type, 0}, _names), do: "Type"
  def format({:type, level}, _names), do: "Type #{level}"
  def format({:global, name}, _names), do: Name.base(name)
  def format({:int_lit, value}, _names), do: Integer.to_string(value)
  def format({:nat_lit, value}, _names), do: Integer.to_string(value)
  def format({:atom_lit, value}, _names), do: inspect(value)

  def format({:data, name, params, indices}, names),
    do: call(Name.base(name), Enum.map(params ++ indices, &format(&1, names)))

  def format({:ctor, name, args}, names), do: call(Name.base(name), Enum.map(args, &format(&1, names)))

  def format({:app, _, _} = application, names) do
    {head, args} = flatten_app(application, [])
    format(head, names) <> "(" <> Enum.map_join(args, ", ", &format(&1, names)) <> ")"
  end

  def format(other, _names), do: inspect(other, limit: 8)

  defp flatten_app({:app, function, argument}, args), do: flatten_app(function, [argument | args])
  defp flatten_app(head, args), do: {head, args}
  defp call(name, []), do: name
  defp call(name, args), do: name <> "(" <> Enum.join(args, ", ") <> ")"
end
