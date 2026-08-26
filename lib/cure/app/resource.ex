defmodule Cure.App.Resource do
  @moduledoc """
  Emits OTP `.app` resource files for a compiled Cure application.

  The application module is emitted through the ordinary Cure compiler; this
  module only writes the project metadata resource consumed by OTP tooling.
  """

  @spec write(map() | nil, [module()], Cure.Project.t(), keyword()) :: :ok | {:error, term()}
  def write(nil, _modules, _project, _opts), do: :ok

  def write(%{name: name, meta: meta}, modules, project, opts) when is_binary(name) do
    output_dir = Keyword.fetch!(opts, :output_dir)
    File.mkdir_p!(output_dir)

    app_atom = app_resource_atom(project, name)
    props = build_props(name, meta, modules, project)
    path = Path.join(output_dir, "#{app_atom}.app")
    contents = :io_lib.format(~c"~p.~n", [{:application, app_atom, props}])

    case File.write(path, IO.iodata_to_binary(contents)) do
      :ok -> :ok
      {:error, reason} -> {:error, {:app_resource_write_failed, path, reason}}
    end
  end

  def write(_app_info, _modules, _project, _opts), do: :ok

  @doc false
  def build_props(container_name, meta, modules, project) do
    app = project.application || %{}
    description = Map.get(app, :description, "") |> to_string()
    vsn = pick_vsn(app, meta, project)
    mod_atom = String.to_atom("Cure.App." <> container_name)

    applications =
      (normalize_atoms(Map.get(app, :applications, [])) ++
         extract_atom_list(meta, :applications) ++ [:kernel, :stdlib])
      |> Enum.uniq()

    env =
      [extract_env_pairs(meta), atomize_env(Map.get(app, :env, %{}))]
      |> Enum.reduce(%{}, fn pairs, acc -> Map.merge(acc, Enum.into(pairs, %{})) end)

    base = [
      {:description, to_charlist_safe(description)},
      {:vsn, to_charlist_safe(vsn)},
      {:modules, filter_app_modules(modules)},
      {:registered, normalize_atoms(Map.get(app, :registered, []))},
      {:applications, applications},
      {:included_applications, normalize_atoms(Map.get(app, :included_applications, []))},
      {:env, Enum.into(env, [])},
      {:mod, {mod_atom, []}}
    ]

    case normalize_atoms(Map.get(app, :start_phases, [])) do
      [] -> base
      phases -> base ++ [{:start_phases, Enum.map(phases, &{&1, []})}]
    end
  end

  defp app_resource_atom(project, container_name) do
    case Cure.Project.app_name_for(project) do
      "" -> String.to_atom(Macro.underscore(container_name))
      normalized -> String.to_atom(normalized)
    end
  end

  defp pick_vsn(app, meta, project) do
    case Map.get(app, :vsn) do
      vsn when is_binary(vsn) and vsn != "" -> vsn
      _ -> extract_string(meta, :vsn) || project.version || "0.1.0"
    end
  end

  defp extract_string(meta, key) do
    case Keyword.get(meta, key) do
      {:literal, _, value} when is_binary(value) -> value
      _ -> nil
    end
  end

  defp extract_atom_list(meta, key) do
    case Keyword.get(meta, key) do
      {:list, _, items} -> Enum.flat_map(items, &extract_atom/1)
      _ -> []
    end
  end

  defp extract_atom({:literal, _, value}) when is_atom(value), do: [value]
  defp extract_atom({:literal, _, value}) when is_binary(value), do: [String.to_atom(value)]
  defp extract_atom(_), do: []

  defp extract_env_pairs(meta) do
    case Keyword.get(meta, :env) do
      {:map, _, pairs} -> Enum.flat_map(pairs, &extract_env_pair/1)
      _ -> []
    end
  end

  defp extract_env_pair({:pair, _, [key_ast, value_ast]}) do
    case extract_atom(key_ast) do
      [key] -> [{key, extract_value(value_ast)}]
      _ -> []
    end
  end

  defp extract_env_pair(_), do: []
  defp extract_value({:literal, _, value}), do: value
  defp extract_value({:list, _, items}), do: Enum.map(items, &extract_value/1)
  defp extract_value({:tuple, _, items}), do: List.to_tuple(Enum.map(items, &extract_value/1))
  defp extract_value({:map, _, pairs}), do: pairs |> Enum.flat_map(&extract_env_pair/1) |> Enum.into(%{})
  defp extract_value(other), do: other

  defp normalize_atoms(list) when is_list(list) do
    list
    |> Enum.map(fn
      atom when is_atom(atom) -> atom
      string when is_binary(string) -> String.to_atom(string)
      _ -> nil
    end)
    |> Enum.reject(&is_nil/1)
  end

  defp normalize_atoms(_), do: []

  defp atomize_env(map) when is_map(map) do
    Enum.map(map, fn {key, value} ->
      key = if is_binary(key), do: String.to_atom(key), else: key
      {key, value}
    end)
  end

  defp atomize_env(_), do: []
  defp to_charlist_safe(value) when is_binary(value), do: String.to_charlist(value)
  defp to_charlist_safe(value), do: value |> to_string() |> String.to_charlist()

  defp filter_app_modules(modules) do
    modules
    |> Enum.uniq()
    |> Enum.filter(&is_atom/1)
    |> Enum.reject(&match?(:erlang, &1))
  end
end
