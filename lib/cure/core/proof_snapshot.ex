defmodule Cure.Core.ProofSnapshot do
  @moduledoc """
  Capture a narrow canonical Core snapshot for independent proof replay.

  This is an opt-in representation audit, not kernel admission, declaration
  validation, certificate verification, or a release gate. It never certifies
  a definition or changes the supplied environment. Every registered family,
  constructor, global type and raw body is inspected, including hidden bodies.

  The initial slice requires printable ASCII identities, direct owner-qualified
  references, ordinary non-opaque families, explicit unrestricted constructor
  fields, and no builtins or primitive/extern definitions. Unknown declaration
  metadata is rejected. Source binders retain their grades; erasure/usage
  soundness is not established by capture.

  Global certification flags are recorded as claims, not proved. The formal
  projection exposes raw bodies only when certified; totality without body
  visibility remains distinct. `to_agda/2` renders data, never proof callbacks.
  """

  alias Cure.Core.{Env, Grade, Term}
  alias Cure.Elab.Name

  @family_keys [:name, :params, :indices, :level, :ctor_order, :opaque]
  @ctor_keys [:name, :args, :result_params, :result_indices, :quantities, :plicities]
  @global_keys [:name, :type, :body, :quantities, :plicities]

  @type error :: %{reason: atom(), path: list()}

  @doc "Capture the entire supplied Core registry or return an explicit boundary exclusion."
  @spec capture(Env.t()) :: {:ok, map()} | {:error, error()}
  def capture(%Env{} = env) do
    try do
      validate_tables!(env)
      families = Enum.map(sorted(env.families), &family!(&1, env))
      globals = Enum.map(sorted(env.defs), &global!(&1, env))
      {:ok, %{"version" => 1, "families" => families, "globals" => globals, "builtins" => []}}
    catch
      {__MODULE__, reason, path} -> {:error, %{reason: reason, path: path}}
    end
  end

  def capture(_env), do: {:error, %{reason: :malformed_environment, path: []}}

  @doc "Render a captured environment as an Agda input module; no declarations are executed."
  @spec to_agda(Env.t(), String.t()) :: {:ok, String.t()} | {:error, error()}
  def to_agda(env, module_name) when is_binary(module_name) do
    if Regex.match?(~r/\A[A-Z][A-Za-z0-9_]*(?:\.[A-Z][A-Za-z0-9_]*)*\z/, module_name) do
      with {:ok, snapshot} <- capture(env), do: {:ok, render(snapshot, module_name)}
    else
      {:error, %{reason: :invalid_module_name, path: []}}
    end
  end

  def to_agda(_env, _module_name), do: {:error, %{reason: :invalid_module_name, path: []}}

  defp validate_tables!(env) do
    for {table, path} <- [
          {env.families, [:families]},
          {env.ctors, [:constructors]},
          {env.ctor_to_family, [:owners]},
          {env.defs, [:globals]},
          {env.builtins, [:builtins]},
          {env.primitives, [:primitives]},
          {env.qualified_aliases, [:qualified_aliases]}
        ] do
      ensure!(is_map(table) and not is_struct(table), :malformed_table, path)
    end

    ensure!(env.builtins == %{}, :unsupported_builtins, [:builtins])
    ensure!(env.primitives == %{}, :unsupported_primitives, [:primitives])
    ensure!(env.qualified_aliases == %{}, :unsupported_aliases, [:qualified_aliases])

    for {table, path} <- [{env.families, [:families]}, {env.ctors, [:constructors]}, {env.defs, [:globals]}],
        key <- Map.keys(table) do
      canonical!(key, path ++ [key])
    end

    ensure!(
      MapSet.new(Map.keys(env.ctors)) == MapSet.new(Map.keys(env.ctor_to_family)),
      :inconsistent_owner_keys,
      [:owners]
    )

    for {ctor, owner} <- env.ctor_to_family do
      ensure!(Map.has_key?(env.families, owner), :unknown_owner, [:owners, ctor])
    end

    for {set, path} <- [
          {env.certified, [:certified]},
          {env.totality_certified, [:totality_certified]}
        ] do
      ensure!(match?(%MapSet{}, set), :malformed_certificate_set, path)
      ensure!(MapSet.subset?(set, MapSet.new(Map.keys(env.defs))), :unknown_certified_global, path)
    end

    ensure!(
      MapSet.subset?(env.certified, env.totality_certified),
      :inconsistent_certification,
      [:certified]
    )
  end

  defp family!({key, family}, env) do
    path = [:families, key]
    ensure!(is_map(family) and not is_struct(family), :malformed_entry, path)
    ensure!(Map.get(family, :opaque, false) == false, :unsupported_opaque_family, path)
    keys!(family, @family_keys, [:name, :params, :indices, :level, :ctor_order], path)
    ensure!(family.name == key, :key_name_mismatch, path)
    ensure!(is_integer(family.level) and family.level in 0..2, :invalid_universe, path ++ [:level])
    parameters = telescope!(family.params, 0, env, path ++ [:params])
    indices = telescope!(family.indices, length(parameters), env, path ++ [:indices])
    order = family.ctor_order
    ensure!(is_list(order), :invalid_constructor_order, path ++ [:ctor_order])
    owned = for {ctor, ^key} <- env.ctor_to_family, do: ctor

    ensure!(
      length(order) == MapSet.size(MapSet.new(order)) and MapSet.new(order) == MapSet.new(owned),
      :inconsistent_constructor_order,
      path ++ [:ctor_order]
    )

    constructors = Enum.map(order, &constructor!(&1, family, env, path ++ [:constructors, &1]))

    %{
      "name" => text!(key, path),
      "params" => parameters,
      "indices" => indices,
      "level" => family.level,
      "opaque" => false,
      "constructors" => constructors
    }
  end

  defp constructor!(name, family, env, path) do
    ctor = Map.fetch!(env.ctors, name)
    keys!(ctor, @ctor_keys, @ctor_keys, path)
    ensure!(ctor.name == name, :key_name_mismatch, path)
    arguments = telescope!(ctor.args, length(family.params), env, path ++ [:args])
    count = length(arguments)
    layout!(ctor.quantities, count, &(&1 == Grade.unrestricted()), path ++ [:quantities])
    layout!(ctor.plicities, count, &(&1 == :explicit), path ++ [:plicities])
    depth = count + length(family.params)
    params = terms!(ctor.result_params, depth, env, path ++ [:result_params])
    indices = terms!(ctor.result_indices, depth, env, path ++ [:result_indices])
    ensure!(length(params) == length(family.params), :result_parameter_arity, path)
    ensure!(length(indices) == length(family.indices), :result_index_arity, path)

    %{
      "name" => text!(name, path),
      "args" => arguments,
      "result_params" => params,
      "result_indices" => indices,
      "quantities" => Enum.map(ctor.quantities, &Atom.to_string/1),
      "explicit" => Enum.map(ctor.plicities, &(&1 == :explicit))
    }
  end

  defp global!({key, definition}, env) do
    path = [:globals, key]
    keys!(definition, @global_keys, @global_keys, path)
    ensure!(definition.name == key, :key_name_mismatch, path)
    type = term!(definition.type, 0, env, path ++ [:type])
    body = if is_nil(definition.body), do: nil, else: term!(definition.body, 0, env, path ++ [:body])
    count = pi_arity(definition.type)
    optional_layout!(definition.quantities, count, &(&1 == Grade.unrestricted()), path ++ [:quantities])
    optional_layout!(definition.plicities, count, &(&1 == :explicit), path ++ [:plicities])
    certified = MapSet.member?(env.certified, key)
    ensure!(not certified or not is_nil(body), :certified_body_missing, path ++ [:body])

    %{
      "name" => text!(key, path),
      "type" => type,
      "body" => body,
      "quantities" =>
        if(is_nil(definition.quantities), do: nil, else: Enum.map(definition.quantities, &Atom.to_string/1)),
      "explicit" => if(is_nil(definition.plicities), do: nil, else: Enum.map(definition.plicities, &(&1 == :explicit))),
      "certified" => certified,
      "totality_certified" => MapSet.member?(env.totality_certified, key)
    }
  end

  defp telescope!(entries, depth, env, path) when is_list(entries) do
    entries
    |> Enum.with_index()
    |> Enum.map(fn
      {{name, type}, index} when is_atom(name) ->
        %{"name" => text!(name, path ++ [index]), "type" => term!(type, depth + index, env, path ++ [index])}

      {_entry, index} ->
        reject!(:malformed_telescope, path ++ [index])
    end)
  end

  defp telescope!(_entries, _depth, _env, path), do: reject!(:malformed_telescope, path)

  defp terms!(terms, depth, env, path) when is_list(terms) do
    terms |> Enum.with_index() |> Enum.map(fn {term, index} -> term!(term, depth, env, path ++ [index]) end)
  end

  defp terms!(_terms, _depth, _env, path), do: reject!(:malformed_spine, path)

  defp term!(term, depth, env, path) do
    ensure!(Term.term?(term), :malformed_term, path)
    scan!(term, depth, env, path)
    Term.to_external(term)
  end

  defp scan!({:type, _level}, _depth, _env, _path), do: :ok
  defp scan!({node}, _depth, _env, _path) when node in [:atom_type, :float_type, :binary_type], do: :ok
  defp scan!({:atom_lit, atom}, _depth, _env, path), do: text!(atom, path)
  defp scan!({:var, index}, depth, _env, path), do: ensure!(index < depth, :escaped_variable, path)

  defp scan!({node, _grade, domain, body}, depth, env, path) when node in [:pi, :lam] do
    scan!(domain, depth, env, path ++ [:domain])
    scan!(body, depth + 1, env, path ++ [:body])
  end

  defp scan!({:let, _grade, type, value, body}, depth, env, path) do
    scan!(type, depth, env, path ++ [:type])
    scan!(value, depth, env, path ++ [:value])
    scan!(body, depth + 1, env, path ++ [:body])
  end

  defp scan!({:app, function, argument}, depth, env, path) do
    scan!(function, depth, env, path ++ [:function])
    scan!(argument, depth, env, path ++ [:argument])
  end

  defp scan!({:global, name}, _depth, env, path), do: registered!(env.defs, name, path)

  defp scan!({:data, name, params, indices}, depth, env, path) do
    registered!(env.families, name, path)
    family = Map.fetch!(env.families, name)

    ensure!(
      is_map(family) and not is_struct(family) and is_list(family[:params]) and is_list(family[:indices]),
      :malformed_family,
      path
    )

    ensure!(length(params) == length(family.params) and length(indices) == length(family.indices), :data_arity, path)
    terms!(params, depth, env, path ++ [:params])
    terms!(indices, depth, env, path ++ [:indices])
  end

  defp scan!({:ctor, name, args}, depth, env, path) do
    registered!(env.ctors, name, path)
    ctor = Map.fetch!(env.ctors, name)
    ensure!(is_map(ctor) and not is_struct(ctor) and is_list(ctor[:args]), :malformed_constructor, path)
    ensure!(length(args) == length(ctor.args), :unsupported_constructor_spine, path)
    terms!(args, depth, env, path ++ [:args])
  end

  defp scan!({:case, scrutinee, motive, branches}, depth, env, path) do
    scan!(scrutinee, depth, env, path ++ [:scrutinee])
    scan!(motive, depth, env, path ++ [:motive])

    for {name, arity, body} <- branches do
      registered!(env.ctors, name, path ++ [:branches])
      ctor = Map.fetch!(env.ctors, name)
      ensure!(is_map(ctor) and not is_struct(ctor) and is_list(ctor[:args]), :malformed_constructor, path)
      ensure!(arity == length(ctor.args), :branch_arity, path ++ [:branches, name])
      scan!(body, depth + arity, env, path ++ [:branches, name])
    end
  end

  defp scan!(_term, _depth, _env, path), do: reject!(:unsupported_term, path)

  defp registered!(table, name, path) do
    canonical!(name, path)
    ensure!(Map.has_key?(table, name), :unknown_reference, path)
  end

  defp canonical!(name, path) do
    text = text!(name, path)
    ensure!(Name.qualified?(text) and Name.base(text) != "", :noncanonical_name, path)
  end

  defp text!(name, path) when is_atom(name) do
    text = Atom.to_string(name)
    ensure!(text != "" and Enum.all?(:binary.bin_to_list(text), &(&1 in 32..126)), :unsupported_name_encoding, path)
    text
  end

  defp text!(_name, path), do: reject!(:malformed_name, path)

  defp keys!(entry, allowed, required, path) do
    ensure!(is_map(entry) and not is_struct(entry), :malformed_entry, path)
    ensure!(Enum.all?(required, &Map.has_key?(entry, &1)), :missing_metadata, path)
    ensure!(Map.keys(entry) -- allowed == [], :unsupported_metadata, path)
  end

  defp layout!(values, count, predicate, path) do
    ensure!(is_list(values) and length(values) == count, :layout_arity, path)
    ensure!(Enum.all?(values, predicate), :unsupported_layout, path)
  end

  defp optional_layout!(nil, _count, _predicate, _path), do: :ok
  defp optional_layout!(values, count, predicate, path), do: layout!(values, count, predicate, path)
  defp pi_arity({:pi, _grade, _domain, codomain}), do: 1 + pi_arity(codomain)
  defp pi_arity(_type), do: 0
  defp sorted(table), do: Enum.sort_by(table, fn {name, _entry} -> Atom.to_string(name) end)
  defp ensure!(true, _reason, _path), do: :ok
  defp ensure!(false, reason, path), do: reject!(reason, path)
  defp reject!(reason, path), do: throw({__MODULE__, reason, path})

  defp render(snapshot, module_name) do
    """
    -- Generated by Cure.Core.ProofSnapshot; checked data, not a proof of extraction.
    module #{module_name} where
    open import Data.Bool using (true; false)
    open import Data.List using ([]; _∷_)
    open import Data.Maybe using (just; nothing)
    open import Data.Product using (_,_)
    open import Core.Syntax
    open import Core.Grade using (erased; linear; affine; unrestricted)
    open import Core.Universe using (l0; l1; l2)
    open import Core.ExecutableSnapshot

    source : Input
    source = input
      #{list(snapshot["families"], &render_family/1)}
      #{list(snapshot["globals"], &render_global/1)}
      []
    """
  end

  defp render_family(family) do
    "(family-input #{quote_name(family["name"])} #{tele(family["params"])} #{tele(family["indices"])} " <>
      "l#{family["level"]} #{list(family["constructors"], &render_ctor/1)} false)"
  end

  defp render_ctor(ctor) do
    "(constructor-input (record { ctor-name = #{quote_name(ctor["name"])}; " <>
      "ctor-args = #{tele(ctor["args"])}; ctor-params = #{list(ctor["result_params"], &render_term/1)}; " <>
      "ctor-indices = #{list(ctor["result_indices"], &render_term/1)} }) " <>
      "#{list(ctor["quantities"], & &1)} #{list(ctor["explicit"], &to_string/1)})"
  end

  defp render_global(global) do
    "(global-input #{quote_name(global["name"])} #{render_term(global["type"])} " <>
      "#{optional(global["body"], &render_term/1)} " <>
      "#{optional(global["quantities"], &list(&1, fn grade -> grade end))} " <>
      "#{optional(global["explicit"], &list(&1, fn flag -> to_string(flag) end))} " <>
      "#{global["certified"]} #{global["totality_certified"]})"
  end

  defp render_term(%{"node" => "type", "level" => level}), do: "(tm-type l#{level})"
  defp render_term(%{"node" => "var", "index" => index}), do: "(tm-var #{index})"
  defp render_term(%{"node" => "global", "name" => name}), do: "(tm-global #{quote_name(name)})"
  defp render_term(%{"node" => "atom_lit", "value" => value}), do: "(tm-atom_lit #{quote_name(value)})"
  defp render_term(%{"node" => node}) when node in ["atom_type", "float_type", "binary_type"], do: "tm-#{node}"

  defp render_term(%{"node" => node, "grade" => grade, "dom" => dom} = term) when node in ["pi", "lam"] do
    body = if node == "pi", do: term["cod"], else: term["body"]
    "(tm-#{node} #{grade} #{render_term(dom)} #{render_term(body)})"
  end

  defp render_term(%{"node" => "let", "grade" => grade, "type" => type, "value" => value, "body" => body}),
    do: "(tm-let #{grade} #{render_term(type)} #{render_term(value)} #{render_term(body)})"

  defp render_term(%{"node" => "app", "fun" => function, "arg" => argument}),
    do: "(tm-app #{render_term(function)} #{render_term(argument)})"

  defp render_term(%{"node" => "data", "name" => name, "params" => params, "indices" => indices}),
    do: "(tm-data #{quote_name(name)} #{list(params, &render_term/1)} #{list(indices, &render_term/1)})"

  defp render_term(%{"node" => "ctor", "name" => name, "args" => args}),
    do: "(tm-ctor #{quote_name(name)} #{list(args, &render_term/1)})"

  defp render_term(%{"node" => "case", "scrut" => scrutinee, "motive" => motive, "branches" => branches}) do
    branch = fn b -> "(#{quote_name(b["ctor"])} , #{b["arity"]} , #{render_term(b["body"])})" end
    "(tm-case #{render_term(scrutinee)} #{render_term(motive)} #{list(branches, branch)})"
  end

  defp tele(entries), do: list(entries, fn e -> "(#{quote_name(e["name"])} , #{render_term(e["type"])})" end)
  defp list([], _render), do: "[]"
  defp list(entries, render), do: "(" <> Enum.map_join(entries, " ∷ ", render) <> " ∷ [])"
  defp optional(nil, _render), do: "nothing"
  defp optional(value, render), do: "(just #{render.(value)})"
  defp quote_name(text), do: "\"" <> (text |> String.replace("\\", "\\\\") |> String.replace("\"", "\\\"")) <> "\""
end
