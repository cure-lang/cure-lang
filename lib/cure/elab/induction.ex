defmodule Cure.Elab.Induction do
  @moduledoc false

  alias Cure.Core.{Env, Inductive}
  alias Cure.Diagnostic.InductionProblem
  alias Cure.MetaAST.{Metadata, SourceInfo}

  @doc "Lift non-parameter induction subjects into private ordinary declarations."
  @spec lift_declarations([term()]) :: {:ok, [term()]} | {:error, term()}
  def lift_declarations(items) when is_list(items) do
    signatures = signature_index(items)
    constructors = constructor_index(items)

    {rewritten, helpers, _counter} =
      Enum.reduce(items, {[], [], 0}, fn
        {:function_def, meta, [body]}, {decls, helpers, counter} ->
          params = Keyword.get(meta, :params, [])
          types = parameter_types(params)

          case lift_expr(body, meta, types, signatures, constructors, counter) do
            {:ok, lifted_body, new_helpers, next_counter} ->
              {[{:function_def, meta, [lifted_body]} | decls], helpers ++ new_helpers, next_counter}

            {:error, _} = error ->
              throw({:induction_lift_error, error})
          end

        item, {decls, helpers, counter} ->
          {[item | decls], helpers, counter}
      end)

    {:ok, Enum.reverse(rewritten) ++ helpers}
  catch
    {:induction_lift_error, error} -> error
  end

  def lift_declarations(other), do: {:ok, other}

  defp lift_expr(
         {:induction, _meta, [{:variable, _, name} | _]} = node,
         function_meta,
         types,
         signatures,
         constructors,
         counter
       ) do
    if Enum.any?(Keyword.get(function_meta, :params, []), fn {:param, _meta, param_name} -> param_name == name end) do
      {:ok, annotate_induction_cases(node, constructors), [], counter}
    else
      lift_nonparameter_induction(node, function_meta, types, signatures, constructors, counter)
    end
  end

  defp lift_expr({:induction, meta, [subject | cases]}, function_meta, types, signatures, constructors, counter) do
    lift_nonparameter_induction(
      {:induction, meta, [subject | cases]},
      function_meta,
      types,
      signatures,
      constructors,
      counter
    )
  end

  defp lift_expr({:block, meta, children}, function_meta, types, signatures, constructors, counter) do
    lift_children(children, function_meta, types, signatures, constructors, counter, [], [])
    |> case do
      {:ok, children, helpers, next_counter, _types} -> {:ok, {:block, meta, children}, helpers, next_counter}
      error -> error
    end
  end

  defp lift_expr({tag, meta, children}, function_meta, types, signatures, constructors, counter)
       when is_atom(tag) and is_list(meta) and is_list(children) do
    lift_children(children, function_meta, types, signatures, constructors, counter, [], [])
    |> case do
      {:ok, children, helpers, next_counter, _types} -> {:ok, {tag, meta, children}, helpers, next_counter}
      error -> error
    end
  end

  defp lift_expr(other, _function_meta, _types, _signatures, _constructors, counter),
    do: {:ok, other, [], counter}

  defp lift_nonparameter_induction(
         {:induction, meta, [subject | cases]},
         function_meta,
         types,
         signatures,
         constructors,
         counter
       ) do
    with {:ok, subject_type} <- surface_type(subject, types, signatures, constructors),
         return_type when not is_nil(return_type) <- Keyword.get(function_meta, :return_type) do
      helper_name = "__induction_#{Keyword.fetch!(function_meta, :name)}_#{counter + 1}"
      subject_name = "__subject"
      captures = ordered_captures(function_meta, types, subject)

      helper_params =
        Enum.map(captures, fn {name, type} -> {:param, [type: type], name} end) ++
          [{:param, [type: subject_type], subject_name}]

      helper_return = replace_surface(return_type, subject, {:variable, [scope: :local], subject_name})

      helper_induction =
        annotate_induction_cases(
          {:induction, meta, [{:variable, [scope: :local], subject_name} | cases]},
          constructors
        )

      helper_meta = [
        name: helper_name,
        params: helper_params,
        return_type: helper_return,
        visibility: :private,
        arity: length(helper_params),
        line: Keyword.get(meta, :line, Keyword.get(function_meta, :line, 0)),
        col: Keyword.get(meta, :col, Keyword.get(function_meta, :col, 0)),
        generated_induction_helper: true,
        induction_origin: source_whole(meta)
      ]

      call_args =
        Enum.map(captures, fn {name, _type} -> {:variable, [scope: :local], name} end) ++ [subject]

      call = {:function_call, [name: helper_name, generated_induction_call: true], call_args}
      helper = {:function_def, helper_meta, [helper_induction]}
      {:ok, call, [helper], counter + 1}
    else
      nil ->
        {:error,
         induction_error(:local_subject_requires_return_annotation, meta,
           subject: subject,
           cause: :inferred_enclosing_return
         )}

      {:error, _} = error ->
        error
    end
  end

  defp lift_children([], _fm, types, _sigs, _ctors, counter, children, helpers),
    do: {:ok, Enum.reverse(children), helpers, counter, types}

  defp lift_children([child | rest], fm, types, sigs, ctors, counter, children, helpers) do
    with {:ok, child, new_helpers, next_counter} <- lift_expr(child, fm, types, sigs, ctors, counter) do
      next_types = extend_local_type(types, child)
      lift_children(rest, fm, next_types, sigs, ctors, next_counter, [child | children], helpers ++ new_helpers)
    end
  end

  defp extend_local_type(types, {:assignment, meta, [{:variable, _, name}, _value]}) do
    case Keyword.get(meta, :type_annotation) do
      nil -> types
      type -> Map.put(types, name, type)
    end
  end

  defp extend_local_type(types, _child), do: types

  defp signature_index(items) do
    Enum.reduce(items, %{}, fn
      {:function_def, meta, _}, acc ->
        Map.put(acc, Keyword.get(meta, :name), %{
          params: Keyword.get(meta, :params, []),
          return: Keyword.get(meta, :return_type)
        })

      _other, acc ->
        acc
    end)
  end

  defp constructor_index(items) do
    Enum.reduce(items, %{}, fn
      {:container, meta, variants}, acc when is_list(meta) ->
        family = Keyword.get(meta, :name)

        Enum.reduce(variants, acc, fn variant, inner ->
          Map.put(inner, variant_name(variant), %{family: family, span: variant_span(variant)})
        end)

      _other, acc ->
        acc
    end)
  end

  defp variant_name({:variable, _meta, name}), do: name
  defp variant_name({:function_def, meta, _body}), do: Keyword.get(meta, :name)
  defp variant_name(_), do: nil

  defp variant_span({_tag, meta, _children}) when is_list(meta) do
    case Metadata.source_info(meta) do
      %{whole: span} -> span
      _ -> nil
    end
  end

  defp variant_span(_), do: nil

  defp annotate_induction_cases({:induction, meta, [subject | cases]}, constructors) do
    declarations = Map.new(constructors, fn {name, info} -> {name, info.span} end)

    cases =
      Enum.map(cases, fn {:induction_case, case_meta, [pattern, body]} ->
        name = pattern_constructor_name(pattern) |> Cure.Elab.Name.base()
        info = Map.get(constructors, name)
        case_meta = if info && info.span, do: put_constructor_range(case_meta, info.span), else: case_meta
        {:induction_case, case_meta, [pattern, body]}
      end)

    {:induction, Keyword.put(meta, :constructor_declarations, declarations), [subject | cases]}
  end

  defp parameter_types(params) do
    Map.new(params, fn {:param, meta, name} -> {name, Keyword.get(meta, :type)} end)
  end

  defp ordered_captures(function_meta, types, subject) do
    params =
      function_meta
      |> Keyword.get(:params, [])
      |> Enum.reject(fn {:param, meta, _name} -> Keyword.get(meta, :implicit, false) end)
      |> Enum.map(fn {:param, _meta, name} -> {name, Map.fetch!(types, name)} end)

    parameter_names = MapSet.new(Enum.map(params, &elem(&1, 0)))
    subject_name = if match?({:variable, _, _}, subject), do: elem(subject, 2), else: nil

    locals =
      types
      |> Enum.reject(fn {name, type} ->
        is_nil(type) or name == subject_name or MapSet.member?(parameter_names, name)
      end)
      |> Enum.sort_by(&elem(&1, 0))

    params ++ locals
  end

  defp surface_type({:variable, _meta, name}, types, _signatures, _constructors) do
    case Map.fetch(types, name) do
      {:ok, nil} -> {:error, induction_error(:unknown_subject_type, [], subject: name)}
      {:ok, type} -> {:ok, type}
      :error -> {:error, induction_error(:unknown_subject_type, [], subject: name)}
    end
  end

  defp surface_type({:function_call, meta, args}, _types, signatures, constructors) do
    name = Keyword.get(meta, :name)

    cond do
      signature = Map.get(signatures, name) ->
        case signature.return do
          nil -> {:error, induction_error(:unknown_subject_type, meta, subject: name)}
          return -> {:ok, substitute_surface_params(return, signature.params, args)}
        end

      is_map(Map.get(constructors, name)) ->
        {:ok, {:variable, [], Map.fetch!(Map.fetch!(constructors, name), :family)}}

      true ->
        {:error, induction_error(:unknown_subject_type, meta, subject: {:function_call, name, args})}
    end
  end

  defp surface_type({:literal, meta, value}, _types, _signatures, _constructors) when is_integer(value),
    do: {:ok, {:variable, meta, "Int"}}

  defp surface_type(subject, _types, _signatures, _constructors),
    do: {:error, induction_error(:unknown_subject_type, [], subject: subject)}

  defp substitute_surface_params(return, params, args) do
    replacements =
      params
      |> Enum.reject(fn {:param, meta, _name} -> Keyword.get(meta, :implicit, false) end)
      |> Enum.map(fn {:param, _meta, name} -> name end)
      |> Enum.zip(args)
      |> Map.new()

    transform_surface(return, fn
      {:variable, _meta, name} = node -> Map.get(replacements, name, node)
      node -> node
    end)
  end

  defp replace_surface(tree, needle, replacement) do
    needle_key = Metadata.semantic_key(needle)

    transform_surface(tree, fn node ->
      if Metadata.semantic_key(node) == needle_key, do: replacement, else: node
    end)
  end

  defp transform_surface({tag, meta, children} = node, fun)
       when is_atom(tag) and is_list(meta) and is_list(children) do
    replaced = fun.(node)

    if replaced == node do
      {tag, meta, Enum.map(children, &transform_surface(&1, fun))}
    else
      replaced
    end
  end

  defp transform_surface(list, fun) when is_list(list), do: Enum.map(list, &transform_surface(&1, fun))
  defp transform_surface(other, fun), do: fun.(other)

  defp induction_error(kind, meta, fields) do
    attrs =
      Map.merge(
        %{kind: kind, construct: source_whole(meta), subject_range: source_subject(meta)},
        Map.new(fields)
      )

    {:induction_failed, struct!(InductionProblem, attrs)}
  end

  @spec expand(term(), map(), Env.t()) :: {:ok, term()} | {:error, term()}
  def expand({:induction, meta, [subject | cases]}, sig, env) do
    with {:ok, subject_name, family} <- parameter_subject(subject, sig, meta),
         :ok <- validate_case_set(cases, family, meta, env),
         {:ok, arms} <- expand_cases(cases, subject_name, family, sig, env) do
      {:ok, {:pattern_match, Keyword.put(meta, :induction, true), [subject | arms]}}
    end
  end

  def expand(other, _sig, _env), do: {:ok, other}

  @doc false
  def wrap_match_error({:error, {:reachable_impossible, constructor}}, meta, arms) do
    case_range =
      Enum.find_value(arms, fn
        {:match_arm, arm_meta, _body} ->
          pattern = Keyword.get(arm_meta, :pattern)

          if pattern_constructor_name(pattern) |> Cure.Elab.Name.base() == Cure.Elab.Name.base(constructor),
            do: source_pattern(arm_meta)

        _ ->
          nil
      end)

    {:error,
     induction_error(:impossible_case, meta,
       constructor: constructor,
       case_range: case_range
     )}
  end

  def wrap_match_error({:error, {:missing_branch, constructor}}, meta, _arms) do
    {:error,
     induction_error(:missing_case, meta,
       missing: [constructor],
       constructor: constructor,
       constructor_range: constructor_declaration(meta, constructor)
     )}
  end

  def wrap_match_error(error, _meta, _arms), do: error

  defp validate_case_set(cases, family, meta, env) do
    names =
      Enum.map(cases, fn {:induction_case, _case_meta, [pattern, _body]} ->
        name = pattern_constructor_name(pattern)
        if name, do: Env.resolve_key(env, env.ctors, name), else: nil
      end)

    duplicate = names -- Enum.uniq(names)
    known = family_constructors(env, family)
    family_info = Inductive.get_family(env, family)
    unknown = Enum.find(names, &(Inductive.ctor_family(env, &1) != family))

    cond do
      duplicate != [] ->
        name = hd(duplicate)

        {:error,
         induction_error(:duplicate_case, meta,
           duplicate: name,
           known: known,
           case_range: duplicate_case_range(cases, name)
         )}

      unknown ->
        {:error,
         induction_error(:unknown_case, meta,
           constructor: unknown,
           required: family,
           known: known,
           pattern_range: duplicate_case_range(cases, unknown)
         )}

      family_info && family_info.indices == [] && known -- names != [] ->
        missing = known -- names

        {:error,
         induction_error(:missing_case, meta,
           missing: missing,
           missing_case_skeletons: Enum.map(missing, &case_skeleton(env, &1, family)),
           insertion: insertion_span(meta),
           case_indent: case_indent(cases, meta),
           known: known,
           constructor_range: constructor_declaration(meta, hd(missing))
         )}

      true ->
        :ok
    end
  end

  defp case_indent([{:induction_case, case_meta, _} | _], _meta) do
    case source_pattern(case_meta) do
      %Cure.Diagnostic.Span{start_column: column} -> max(column - 6, 0)
      _ -> 0
    end
  end

  defp case_indent([], meta) do
    case source_whole(meta) do
      %Cure.Diagnostic.Span{start_column: column} -> max(column + 1, 0)
      _ -> 0
    end
  end

  defp insertion_span(meta) do
    case source_whole(meta) do
      %Cure.Diagnostic.Span{} = span ->
        %{span | start_byte: span.end_byte, start_line: span.end_line, start_column: span.end_column}

      _ ->
        nil
    end
  end

  defp case_skeleton(env, constructor, family) do
    %{args: args} = Inductive.get_ctor(env, constructor)
    recursive = recursive_positions(args, family)
    recursive_count = length(recursive)

    ordinary =
      args
      |> Enum.with_index()
      |> Enum.map(fn {{name, _type}, index} -> descriptive_field_name(name, index, recursive, recursive_count) end)

    hypotheses =
      recursive
      |> Enum.with_index()
      |> Enum.map(fn {_field_index, hypothesis_index} ->
        if recursive_count == 1,
          do: "induction_hypothesis",
          else: "#{induction_side(hypothesis_index)}_induction_hypothesis"
      end)

    bindings = ordinary ++ hypotheses
    name = Cure.Elab.Name.base(constructor)
    pattern = if bindings == [], do: name, else: "#{name}(#{Enum.join(bindings, ", ")})"
    "case #{pattern} => ???"
  end

  defp descriptive_field_name(name, index, recursive, recursive_count) do
    source_name = name |> Cure.Elab.Name.base() |> to_string()

    cond do
      index in recursive and recursive_count == 1 -> "previous"
      index in recursive -> induction_side(Enum.find_index(recursive, &(&1 == index)))
      source_name not in ["", "_", "arg#{index}", "arg#{index + 1}"] -> source_name
      index == 0 -> "value"
      true -> "value#{index + 1}"
    end
  end

  defp induction_side(0), do: "left"
  defp induction_side(1), do: "right"
  defp induction_side(index), do: "recursive#{index + 1}"

  defp constructor_declaration(meta, constructor) do
    declarations = Keyword.get(meta, :constructor_declarations, %{})
    Map.get(declarations, Cure.Elab.Name.base(constructor))
  end

  defp family_constructors(env, family) do
    env.ctor_to_family
    |> Enum.flat_map(fn {ctor, owner} -> if owner == family, do: [ctor], else: [] end)
    |> Enum.sort()
  end

  defp pattern_constructor_name({:variable, _meta, name}), do: String.to_atom(name)
  defp pattern_constructor_name({:function_call, meta, _args}), do: meta |> Keyword.fetch!(:name) |> String.to_atom()
  defp pattern_constructor_name(_pattern), do: nil

  defp duplicate_case_range(cases, name) do
    cases
    |> Enum.filter(fn {:induction_case, _meta, [pattern, _body]} ->
      pattern_constructor_name(pattern) |> Cure.Elab.Name.base() == Cure.Elab.Name.base(name)
    end)
    |> List.last()
    |> case do
      {:induction_case, case_meta, _} -> source_pattern(case_meta)
      _ -> nil
    end
  end

  defp parameter_subject({:variable, _meta, name}, sig, induction_meta) do
    case Enum.find(sig.telescope, fn {param_name, _type} -> Atom.to_string(param_name) == name end) do
      {_param_name, {:data, family, _params, _indices}} ->
        {:ok, name, family}

      {_param_name, type} ->
        {:error, induction_error(:non_inductive_subject, induction_meta, subject: name, type: type)}

      nil ->
        {:error, induction_error(:local_subject_requires_lift, induction_meta, subject: name)}
    end
  end

  defp parameter_subject(subject, _sig, induction_meta),
    do: {:error, induction_error(:local_subject_requires_lift, induction_meta, subject: subject)}

  defp expand_cases(cases, subject_name, family, sig, env) do
    Enum.reduce_while(cases, {:ok, []}, fn case_ast, {:ok, acc} ->
      case expand_case(case_ast, subject_name, family, sig, env) do
        {:ok, arm} -> {:cont, {:ok, [arm | acc]}}
        {:error, _} = error -> {:halt, error}
      end
    end)
    |> case do
      {:ok, reversed} -> {:ok, Enum.reverse(reversed)}
      error -> error
    end
  end

  defp expand_case({:induction_case, meta, [pattern, body]}, subject_name, family, sig, env) do
    with {:ok, ctor_name, fields, rebuild} <- constructor_pattern(pattern),
         ^family <- Inductive.ctor_family(env, ctor_name),
         %{args: ctor_args} = ctor <- Inductive.get_ctor(env, ctor_name),
         recursive_positions <- recursive_positions(ctor_args, family),
         expected_count = length(ctor_args) + length(recursive_positions),
         :ok <- check_field_count(ctor_name, fields, expected_count, recursive_positions, meta),
         {ordinary_fields, hypotheses} <- Enum.split(fields, length(ctor_args)),
         {:ok, hypothesis_names} <- hypothesis_names(hypotheses, ctor_name),
         assignments <-
           hypothesis_assignments(hypothesis_names, recursive_positions, ordinary_fields, subject_name, sig),
         body <- annotate_hypothesis_uses(body, hypothesis_names, recursive_positions),
         pattern_fields <- ordinary_pattern_fields(ctor_args, Inductive.plicities_of(ctor), ordinary_fields),
         pattern <- rebuild.(pattern_fields),
         body <- induction_case_body(body, assignments, meta),
         {:ok, body} <- expand_nested(body, sig, env) do
      arm_meta = meta |> Keyword.put(:pattern, pattern) |> Keyword.put(:induction, true)
      {:ok, {:match_arm, arm_meta, [body]}}
    else
      nil ->
        {:error,
         induction_error(:unknown_case, meta,
           subject: pattern,
           pattern_range: source_pattern(meta),
           constructor_range: constructor_range(meta)
         )}

      actual when is_atom(actual) ->
        {:error,
         induction_error(:unknown_case, meta,
           constructor: actual,
           required: family,
           pattern_range: source_pattern(meta),
           constructor_range: constructor_range(meta)
         )}

      {:error, _} = error ->
        error
    end
  end

  defp induction_case_body(nil, _assignments, _meta), do: nil
  defp induction_case_body(body, [], _meta), do: body

  defp induction_case_body(body, assignments, meta),
    do: {:block, Keyword.put(meta, :induction_case_body, true), assignments ++ [body]}

  defp expand_nested({:induction, _meta, _children} = induction, sig, env), do: expand(induction, sig, env)

  defp expand_nested({tag, meta, children}, sig, env) when is_atom(tag) and is_list(meta) and is_list(children) do
    with {:ok, children} <- expand_nested(children, sig, env) do
      {:ok, {tag, meta, children}}
    end
  end

  defp expand_nested(list, sig, env) when is_list(list) do
    Enum.reduce_while(list, {:ok, []}, fn child, {:ok, acc} ->
      case expand_nested(child, sig, env) do
        {:ok, expanded} -> {:cont, {:ok, [expanded | acc]}}
        {:error, _} = error -> {:halt, error}
      end
    end)
    |> case do
      {:ok, reversed} -> {:ok, Enum.reverse(reversed)}
      error -> error
    end
  end

  defp expand_nested(other, _sig, _env), do: {:ok, other}

  defp constructor_pattern({:variable, meta, name}) do
    {:ok, String.to_atom(name), [], fn [] -> {:variable, meta, name} end}
  end

  defp constructor_pattern({:function_call, meta, fields}) do
    name = Keyword.fetch!(meta, :name)
    {:ok, String.to_atom(name), fields, fn kept -> {:function_call, meta, kept} end}
  end

  defp constructor_pattern(pattern),
    do: {:error, induction_error(:unknown_case, [], subject: pattern)}

  defp recursive_positions(args, family) do
    args
    |> Enum.with_index()
    |> Enum.flat_map(fn {{_name, type}, index} -> if recursive_type?(type, family), do: [index], else: [] end)
  end

  defp recursive_type?({:data, family, _params, _indices}, family), do: true
  defp recursive_type?(_type, _family), do: false

  defp ordinary_pattern_fields(ctor_args, plicities, fields) do
    [ctor_args, plicities, fields]
    |> Enum.zip()
    |> Enum.map(fn
      {{_name, _type}, :implicit, {:named_implicit_pat, _meta, _children} = field} ->
        field

      {{name, _type}, :implicit, field} ->
        {:named_implicit_pat, [name: to_string(name)], [field]}

      {{_name, _type}, :explicit, field} ->
        field
    end)
  end

  defp check_field_count(_ctor, fields, expected, _positions, _meta) when length(fields) == expected, do: :ok

  defp check_field_count(ctor, fields, expected, positions, meta) do
    ordinary_count = expected - length(positions)

    kind =
      if positions != [] and length(fields) == ordinary_count, do: :unavailable_hypothesis, else: :wrong_case_fields

    {:error,
     induction_error(kind, meta,
       constructor: ctor,
       expected_fields: expected,
       observed_fields: length(fields),
       recursive_fields: positions,
       pattern_range: source_pattern(meta),
       constructor_range: constructor_range(meta)
     )}
  end

  defp hypothesis_names(hypotheses, ctor) do
    Enum.reduce_while(hypotheses, {:ok, []}, fn
      {:variable, _meta, name}, {:ok, acc} when name != "_" ->
        {:cont, {:ok, [name | acc]}}

      {:variable, _meta, "_"}, {:ok, acc} ->
        {:cont, {:ok, [nil | acc]}}

      hypothesis, _ ->
        {:halt, {:error, induction_error(:unavailable_hypothesis, [], constructor: ctor, hypothesis: hypothesis)}}
    end)
    |> case do
      {:ok, reversed} -> {:ok, Enum.reverse(reversed)}
      error -> error
    end
  end

  defp hypothesis_assignments(names, positions, fields, subject_name, sig) do
    Enum.zip(names, positions)
    |> Enum.flat_map(fn
      {nil, _position} ->
        []

      {hypothesis, position} ->
        {:variable, _meta, recursive_name} = Enum.at(fields, position)

        args =
          sig.params
          |> Enum.reject(fn {:param, meta, _name} -> Keyword.get(meta, :implicit, false) end)
          |> Enum.map(fn {:param, _meta, name} ->
            value = if name == subject_name, do: recursive_name, else: name
            {:variable, [scope: :local], value}
          end)

        call = {:function_call, [name: Atom.to_string(sig.name)], args}
        binder = {:variable, [scope: :local], hypothesis}
        [{:assignment, [let: true, have: true, generated_induction_hypothesis: true], [binder, call]}]
    end)
  end

  defp annotate_hypothesis_uses(body, names, recursive_positions) do
    names = names |> Enum.reject(&is_nil/1) |> MapSet.new()

    transform_surface(body, fn
      {:variable, meta, name} = variable ->
        if MapSet.member?(names, name) do
          {:variable, Keyword.put(meta, :induction_hypothesis, %{recursive_fields: recursive_positions}), name}
        else
          variable
        end

      node ->
        node
    end)
  end

  defp source_whole(meta) do
    case Metadata.source_info(meta) do
      %SourceInfo{whole: span} -> span
      _ -> nil
    end
  end

  defp source_subject(meta) do
    case Metadata.source_info(meta) do
      %SourceInfo{operands: [span | _]} -> span
      _ -> nil
    end
  end

  defp source_pattern(meta) do
    case Metadata.source_info(meta) do
      %SourceInfo{pattern: span} -> span
      _ -> nil
    end
  end

  defp put_constructor_range(meta, span) do
    info = Metadata.source_info(meta) || %SourceInfo{}
    Metadata.put_source_info(meta, %{info | fields: Map.put(info.fields, :constructor_declaration, span)})
  end

  defp constructor_range(meta) do
    case Metadata.source_info(meta) do
      %SourceInfo{fields: fields} -> Map.get(fields, :constructor_declaration)
      _ -> nil
    end
  end
end
