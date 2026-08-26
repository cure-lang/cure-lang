defmodule Cure.Compiler.MacroFamily do
  @moduledoc """
  Generic lowering for the structured macro surface.

  A `syntax family` describes the shape of a reusable macro body. A macro that
  `accepts` that family and `expands with` an ordinary Cure function is lowered
  to the existing deferred computed-rule protocol. The compiler therefore owns
  only syntax shape and staging; the expander still owns all domain semantics.
  """

  @type family :: map()

  @doc """
  Validate a structured macro declaration when both halves of the surface are
  present. Legacy `syntax ... becomes/computed by ...` rules are unaffected.
  """
  @spec validate([map()]) :: :ok | {:error, term()}
  def validate(rules) when is_list(rules) do
    if valid_structured_rules?(rules), do: validate_structured_rules(rules), else: {:error, :invalid_macro_rules}
  end

  def validate(_rules), do: {:error, :invalid_macro_rules}

  defp validate_structured_rules(rules) do
    families = Enum.filter(rules, &(&1[:kind] == :syntax_family))
    accepts = Enum.filter(rules, &(&1[:kind] == :accepts))
    expanders = Enum.filter(rules, &(&1[:kind] == :expands_with))

    with :ok <- validate_families(families),
         :ok <- validate_family_composition(families),
         :ok <- validate_structured_parts(families, accepts, expanders) do
      :ok
    end
  end

  @doc "Build the ordinary computed rule represented by a structured macro."
  @spec computed_rule(keyword(), [map()]) :: {:ok, map()} | :none | {:error, term()}
  def computed_rule(meta, rules) when is_list(meta) and is_list(rules) do
    if valid_structured_rules?(rules), do: build_computed_rule(meta, rules), else: {:error, :invalid_macro_rules}
  end

  def computed_rule(_meta, _rules), do: :none

  defp build_computed_rule(meta, rules) do
    families = Enum.filter(rules, &(&1[:kind] == :syntax_family))
    accepts = Enum.filter(rules, &(&1[:kind] == :accepts))
    expanders = Enum.filter(rules, &(&1[:kind] == :expands_with))

    case {families, accepts, expanders} do
      {[], [], []} ->
        :none

      {families, [accepts_entry], [expands_entry]} when families != [] ->
        case Enum.find(families, &(&1.name == accepts_entry.family)) do
          nil ->
            {:error, {:unknown_syntax_family, accepts_entry.family}}

          family ->
            with {:ok, family} <- effective_family(family, families) do
              family = attach_nested_grammars(family, families)
              leading_segments = Keyword.get(meta, :leading_segments, [])
              leading_fields = leading_segments |> Enum.flat_map(&hole_names/1) |> Enum.uniq()
              fields = leading_fields ++ ["definition"]

              {:ok,
               %{
                 kind: :computed,
                 keyword: Keyword.get(meta, :name),
                 segments:
                   leading_segments ++
                     [
                       {:family,
                        %{
                          name: "definition",
                          family: family.name,
                          fields: family.fields,
                          line: accepts_entry.line
                        }}
                     ],
                 syntax_type: syntax_type("#{family.name}Input"),
                 syntax_fields: fields,
                 syntax_repeated_fields: [],
                 direct_inputs: true,
                 obligations: family_obligations(family.fields),
                 syntax_field_types:
                   Map.put(leading_field_types(leading_segments), "definition", {
                     :record,
                     syntax_type(family.name),
                     family.fields
                   }),
                 syntax_family: family,
                 elab: expands_entry.expander,
                 examples: [],
                 category: nil,
                 contextual: false,
                 module_rule: false,
                 progress: nil,
                 line: Keyword.get(meta, :line, 0),
                 lexical_imports: Map.get(expands_entry, :lexical_imports, Map.get(accepts_entry, :lexical_imports, []))
               }}
            else
              {:error, reason} -> {:error, reason}
            end
        end

      _ ->
        :none
    end
  end

  defp valid_structured_rules?(rules), do: Enum.all?(rules, &valid_structured_rule?/1)

  defp valid_structured_rule?(%{kind: :syntax_family, name: name, fields: fields} = family)
       when (is_atom(name) or is_binary(name)) and is_list(fields) do
    includes = Map.get(family, :includes, [])

    is_list(includes) and
      Enum.all?(fields, fn
        %{name: field_name} when is_atom(field_name) or is_binary(field_name) -> true
        _ -> false
      end)
  end

  defp valid_structured_rule?(%{kind: :accepts, family: family}) when is_atom(family) or is_binary(family), do: true
  defp valid_structured_rule?(%{kind: :expands_with, expander: _expander}), do: true
  defp valid_structured_rule?(%{kind: kind}) when kind in [:syntax_family, :accepts, :expands_with], do: false
  defp valid_structured_rule?(%{}), do: true
  defp valid_structured_rule?(_rule), do: false

  defp family_obligations(fields) do
    Enum.flat_map(fields, fn field ->
      Enum.map(Map.get(field, :obligations, []), &Map.put(&1, :field, field.name))
    end)
  end

  @doc "Add the computed-rule view without changing the source AST."
  @spec lowered_rules(keyword(), [map()]) :: [map()]
  def lowered_rules(meta, rules) when is_list(meta) and is_list(rules) do
    case computed_rule(meta, rules) do
      {:ok, rule} -> [rule | rules]
      _ -> rules
    end
  end

  def lowered_rules(_meta, rules), do: rules

  @doc "The generated record name for a source-level family or macro."
  @spec syntax_type(String.t() | nil) :: String.t()
  def syntax_type(nil), do: "MacroSyntax"

  def syntax_type(name) do
    name = to_string(name)

    cond do
      name != "" and String.ends_with?(name, "Syntax") ->
        name

      name == "" ->
        "MacroSyntax"

      true ->
        <<first::utf8, rest::binary>> = name
        String.upcase(<<first::utf8>>) <> rest <> "Syntax"
    end
  end

  @doc "Return a field's declared category and cardinality metadata."
  @spec field_shape(map()) :: String.t()
  def field_shape(%{shape: shape}), do: shape
  def field_shape(_), do: "Syntax"

  @doc "Return a field's cardinality, defaulting to required."
  @spec field_cardinality(map()) :: atom()
  def field_cardinality(%{cardinality: cardinality}), do: cardinality
  def field_cardinality(_), do: :required

  @doc "Build the ordinary record declarations needed by a structured rule."
  @spec generated_record_declarations(keyword(), map()) :: [tuple()]
  def generated_record_declarations(meta, rule)
      when is_list(meta) and is_map(rule) and is_map_key(rule, :syntax_type) do
    family_declarations =
      case Map.get(rule, :syntax_family) do
        %{name: name, fields: fields} ->
          repeated_fields =
            fields
            |> Enum.filter(&(field_cardinality(&1) in [:repeated, :one_or_more]))
            |> Enum.map(& &1.name)

          nested =
            fields
            |> Enum.flat_map(fn
              %{grammar: %{name: nested_name, fields: nested_fields}} ->
                [
                  record_declaration(syntax_type(nested_name), Enum.map(nested_fields, & &1.name), meta, %{}, %{
                    syntax_repeated_fields: [],
                    syntax_family: %{fields: nested_fields}
                  })
                ]

              _ ->
                []
            end)

          nested ++
            [
              record_declaration(
                syntax_type(name),
                Enum.map(fields, & &1.name),
                meta,
                %{},
                %{syntax_repeated_fields: repeated_fields, syntax_family: %{fields: fields}}
              )
            ]

        _ ->
          []
      end

    family_declarations ++
      [
        record_declaration(
          Map.fetch!(rule, :syntax_type),
          Map.get(rule, :syntax_fields, []),
          meta,
          Map.get(rule, :syntax_field_types, %{}),
          rule
        )
      ]
  end

  def generated_record_declarations(_meta, _rule), do: []

  defp record_declaration(name, fields, meta, field_types, rule) do
    fields =
      Enum.map(fields, fn field ->
        {:param, [type: field_type(field, field_types, rule)], field}
      end)

    {:container,
     [
       container_type: :struct,
       name: name,
       macro_generated: true,
       line: Keyword.get(meta, :line, 0),
       col: Keyword.get(meta, :col, 0)
     ], fields}
  end

  defp field_type(field, field_types, rule) when is_binary(field) do
    base_type =
      case Map.get(field_types, field) do
        {:record, name, _fields} -> {:variable, [scope: :local], name}
        {:primitive, shape} -> {:variable, [scope: :local], shape}
        _ -> nil
      end

    if base_type do
      if field in Map.get(rule, :syntax_repeated_fields, []) do
        {:function_call, [name: "List"], [base_type]}
      else
        base_type
      end
    else
      syntax_field_type(field, rule)
    end
  end

  defp field_type(field, _field_types, _rule), do: syntax_field_type(field, %{})

  defp syntax_field_type(field_name, rule) do
    field =
      rule
      |> Map.get(:syntax_family, %{})
      |> Map.get(:fields, [])
      |> Enum.find_value(%{shape: "Syntax", cardinality: :required}, fn family_field ->
        if family_field.name == field_name, do: family_field, else: nil
      end)

    base_type =
      case Map.get(field, :grammar) do
        %{name: name} -> {:variable, [scope: :local], syntax_type(name)}
        _ -> shape_type_ast(family_field_shape(field))
      end

    base_type =
      if field_name in Map.get(rule, :syntax_repeated_fields, []),
        do: {:function_call, [name: "List"], [base_type]},
        else: base_type

    if family_field_cardinality(field) == :optional,
      do: {:function_call, [name: "Std.Option.Option"], [base_type]},
      else: base_type
  end

  defp shape_type("Syntax"), do: "Syntax"
  defp shape_type(shape) when shape in ["Int", "Float", "Atom", "Bool"], do: shape

  defp shape_type(shape)
       when shape in [
              "Name",
              "ModuleName",
              "Type",
              "Pattern",
              "Expression",
              "Statement",
              "Code",
              "Cases",
              "Fields",
              "Declarations",
              "ModuleBody",
              "Token"
            ],
       do: shape <> "Syntax"

  defp shape_type(_shape), do: "Syntax"

  defp shape_type_ast("Parameters"),
    do: {:function_call, [name: "List"], [{:variable, [scope: :local], "Syntax"}]}

  defp shape_type_ast(shape), do: {:variable, [scope: :local], shape_type(shape)}

  defp family_field_shape(%{shape: shape}), do: shape
  defp family_field_shape(_field), do: "Syntax"

  defp family_field_cardinality(%{cardinality: cardinality}), do: cardinality
  defp family_field_cardinality(_field), do: :required

  defp validate_families(families) do
    duplicate_names = duplicate_values(Enum.map(families, & &1.name))

    duplicate_fields =
      families
      |> Enum.flat_map(fn family ->
        family.fields
        |> Enum.map(& &1.name)
        |> duplicate_values()
        |> Enum.map(&{family.name, &1})
      end)

    cond do
      duplicate_names != [] -> {:error, {:duplicate_syntax_family, duplicate_names}}
      duplicate_fields != [] -> {:error, {:duplicate_syntax_family_field, duplicate_fields}}
      true -> :ok
    end
  end

  defp validate_family_composition(families) do
    case Enum.find_value(families, fn family ->
           case effective_family(family, families) do
             {:ok, _family} -> nil
             {:error, reason} -> {:error, reason}
           end
         end) do
      nil -> :ok
      {:error, reason} -> {:error, reason}
    end
  end

  defp effective_family(family, families) do
    family_map = Map.new(families, &{&1.name, &1})

    with {:ok, fields} <- resolve_family_fields(family, family_map, []) do
      {:ok, Map.put(family, :fields, fields)}
    end
  end

  defp attach_nested_grammars(family, families) do
    family_map = Map.new(families, &{&1.name, &1})

    fields =
      Enum.map(family.fields, fn field ->
        case Map.get(family_map, field.shape) do
          %{productions: [_ | _]} = nested ->
            nested_fields = production_fields(nested.productions) ++ Map.get(nested, :fields, [])

            nested =
              nested
              |> Map.put(:fields, nested_fields)
              |> Map.put(:name, field.shape)
              |> Map.put(:family, field.shape)

            Map.put(field, :grammar, nested)

          _ ->
            field
        end
      end)

    Map.put(family, :fields, fields)
  end

  defp production_fields(productions) do
    names = productions |> Enum.flat_map(& &1.fields) |> Enum.uniq()

    Enum.map(names, fn name ->
      %{
        name: name,
        shape: production_field_shape(productions, name),
        cardinality: production_field_cardinality(productions, name),
        obligations: []
      }
    end)
  end

  defp production_field_shape(productions, name) do
    Enum.find_value(productions, "Syntax", fn production ->
      Enum.find_value(production.segments, fn
        {:hole, %{name: ^name, kind: kind}} -> kind
        _ -> nil
      end)
    end)
  end

  defp production_field_cardinality(productions, name) do
    if Enum.all?(productions, &(name in &1.fields)), do: :required, else: :optional
  end

  defp resolve_family_fields(family, families, stack) do
    name = family.name

    if name in stack do
      {:error, {:syntax_family_cycle, Enum.reverse([name | stack])}}
    else
      with {:ok, included_fields} <- resolve_included_fields(family, families, [name | stack]),
           :ok <- reject_duplicate_fields(included_fields, family.fields, name) do
        {:ok, included_fields ++ family.fields}
      end
    end
  end

  defp resolve_included_fields(family, families, stack) do
    family
    |> Map.get(:includes, [])
    |> Enum.reduce_while({:ok, []}, fn include, {:ok, fields} ->
      include_name = include_name(include)

      case Map.get(families, include_name) do
        nil ->
          {:halt, {:error, {:unknown_syntax_family, include_name}}}

        included ->
          case resolve_family_fields(included, families, stack) do
            {:ok, included_fields} -> {:cont, {:ok, fields ++ included_fields}}
            {:error, reason} -> {:halt, {:error, reason}}
          end
      end
    end)
  end

  defp reject_duplicate_fields(included_fields, own_fields, family_name) do
    duplicates =
      (included_fields ++ own_fields)
      |> Enum.map(& &1.name)
      |> duplicate_values()

    case duplicates do
      [] -> :ok
      names -> {:error, {:duplicate_syntax_family_field, Enum.map(names, &{family_name, &1})}}
    end
  end

  defp include_name({name, _line, _col}), do: name
  defp include_name(name), do: name

  defp validate_structured_parts([], [], []), do: :ok

  defp validate_structured_parts(families, accepts, expanders) do
    cond do
      families != [] and accepts == [] and expanders != [] -> {:error, :expander_without_accepts}
      accepts != [] and families == [] -> {:error, :accepts_without_syntax_family}
      accepts != [] and expanders == [] -> {:error, :accepts_without_expander}
      length(accepts) > 1 -> {:error, :multiple_accepts_declarations}
      length(expanders) > 1 -> {:error, :multiple_expands_declarations}
      true -> :ok
    end
  end

  defp duplicate_values(values) do
    values
    |> Enum.frequencies()
    |> Enum.filter(fn {_value, count} -> count > 1 end)
    |> Enum.map(&elem(&1, 0))
  end

  defp hole_names({:hole, %{name: name}}), do: [name]
  defp hole_names({:optional, segments}), do: Enum.flat_map(segments, &hole_names/1)
  defp hole_names({:repeat, segment}), do: hole_names(segment)
  defp hole_names(_), do: []

  defp leading_field_types(segments) do
    segments
    |> Enum.flat_map(&segment_field_types/1)
    |> Map.new()
  end

  defp segment_field_types({:hole, %{name: name, kind: kind}}) when kind in ["Int", "Float", "Atom", "Bool"],
    do: [{name, {:primitive, kind}}]

  defp segment_field_types({:repeat, segment}), do: segment_field_types(segment)

  defp segment_field_types({:optional, segments}),
    do: Enum.flat_map(segments, &segment_field_types/1)

  defp segment_field_types(_segment), do: []
end
