defmodule Cure.Elab.Equation do
  @moduledoc "Generates kernel-checked defining equations from certified decision trees."

  alias Cure.Core.{Context, Env, Eval, Grade, Inductive, Kernel, Quote, Term}
  alias Cure.Elab.{Name, Rewrite, SourceMetadata, Subst}
  alias Cure.MetaAST.Metadata

  @type descriptor :: %{
          owner: atom(),
          theorem: atom(),
          constructor_path: [atom()],
          pattern_key: String.t(),
          telescope: [term()],
          left_core: term(),
          right_core: term(),
          visibility: atom()
        }

  def generate(%Env{} = env, owner, meta, body_ast \\ nil) do
    owner = Env.resolve_key(env, env.defs, owner)

    with [] <- Map.get(env.equations, owner, []),
         true <- Env.certified?(env, owner),
         %{type: type, body: body, quantities: quantities} <- Env.get_def(env, owner),
         {telescope, result} <- peel(type, :pi),
         {_lambda_telescope, decision_tree} <- peel(body, :lam) do
      {surfaces, surface_order} = surface_equations(owner, meta, body_ast)

      decision_tree
      |> decision_equations(length(telescope), 0, [])
      |> order_equations(surface_order)
      |> Enum.reduce(env, fn equation, current ->
        {:ok, next} = install(current, owner, telescope, result, quantities, equation, meta, surfaces)
        next
      end)
      |> then(&{:ok, &1})
    else
      _ -> {:ok, env}
    end
  end

  def generate_all(%Env{} = env, ast) do
    ast
    |> functions()
    |> Enum.reduce(env, fn {meta, body}, current ->
      {:ok, next} = generate(current, Keyword.fetch!(meta, :name), meta, single_body(body))
      next
    end)
    |> then(&{:ok, &1})
  end

  def resolve_member(%Env{} = env, function_name, member_name) do
    resolve_path(env, function_name, [member_name])
  end

  def resolve_path(%Env{} = env, function_name, member_path) when is_list(member_path) do
    owners =
      env.equations
      |> Map.keys()
      |> Enum.filter(&(Name.overload_base(&1) == function_name))

    all_candidates =
      owners
      |> Enum.flat_map(&Map.get(env.equations, &1, []))

    diagnostic_candidates = Enum.map(all_candidates, &with_source_metadata/1)

    candidates = matching_candidates(diagnostic_candidates, member_path)
    accessible = Enum.filter(candidates, &accessible?(&1, env))

    case accessible do
      [descriptor] ->
        {:ok, descriptor}

      [] when candidates != [] ->
        {:error,
         {:defining_equation_unavailable, :inaccessible_equation, function_name, Enum.join(member_path, "."),
          candidates}}

      [] when owners == [] ->
        :not_equation

      [] ->
        {:error,
         {:defining_equation_unavailable, :unknown_equation, function_name, Enum.join(member_path, "."),
          diagnostic_candidates}}

      many ->
        {:error,
         {:defining_equation_unavailable, :friendly_name_collision, function_name, Enum.join(member_path, "."), many}}
    end
  end

  defp matching_candidates(candidates, [member]) do
    Enum.filter(candidates, fn descriptor ->
      descriptor.constructor_path |> List.last() |> Name.base() == member
    end)
  end

  defp matching_candidates(candidates, members) do
    Enum.filter(candidates, fn descriptor ->
      Enum.map(descriptor.constructor_path, &Name.base/1) == members
    end)
  end

  defp accessible?(%{visibility: :private, owner: owner}, env), do: Name.owner(owner) == env.module_owner
  defp accessible?(_descriptor, _env), do: true

  defp decision_equations({:case, {:var, scrutinee}, _motive, branches}, parameter_count, depth, steps)
       when scrutinee >= depth and scrutinee - depth < parameter_count do
    original_index = scrutinee - depth

    Enum.flat_map(branches, fn {constructor, arity, right} ->
      step = %{scrutinee: original_index, constructor: constructor, arity: arity, offset: depth}
      decision_equations(right, parameter_count, depth + arity, steps ++ [step])
    end)
  end

  defp decision_equations({:case, _scrutinee, _motive, _branches}, _parameter_count, _depth, _steps), do: []
  defp decision_equations(_right, _parameter_count, _depth, []), do: []
  defp decision_equations(right, _parameter_count, depth, steps), do: [%{steps: steps, arity: depth, right: right}]

  defp order_equations(equations, surface_order) do
    ranks = surface_order |> Enum.with_index() |> Map.new()

    Enum.sort_by(equations, fn equation ->
      path = Enum.map(equation.steps, &Name.base(&1.constructor))
      {Map.get(ranks, path, map_size(ranks)), path}
    end)
  end

  defp install(env, owner, telescope, result, quantities, equation, meta, surfaces) do
    arity = equation.arity
    parameter_count = length(telescope)
    {field_telescope, field_quantities} = equation_fields(env, telescope, equation.steps, parameter_count)

    scrutinee_replacements =
      Map.new(equation.steps, fn step ->
        later_fields = arity - step.offset - step.arity
        field_args = for index <- (step.arity - 1)..0//-1, step.arity > 0, do: {:var, later_fields + index}
        {step.scrutinee, {:ctor, step.constructor, field_args}}
      end)

    replacements =
      Map.merge(
        refinement_replacements(env, telescope, equation.steps, parameter_count, arity),
        scrutinee_replacements
      )
      |> normalize_replacements(arity)

    field_telescope = refine_field_telescope(field_telescope, replacements, arity)

    arguments =
      for parameter_position <- 0..(parameter_count - 1) do
        original_index = parameter_count - 1 - parameter_position
        Map.get(replacements, original_index, {:var, arity + original_index})
      end

    left = Enum.reduce(arguments, {:global, owner}, fn argument, call -> {:app, call, argument} end)
    right = apply_original_replacements(equation.right, replacements, arity)

    carrier =
      result
      |> Subst.shift(arity, 0)
      |> then(fn shifted ->
        Enum.reduce(replacements, shifted, fn {key, replacement}, current ->
          Term.subst(current, replacement_index(key, arity), replacement)
        end)
      end)

    {copies, copy_map} = dependent_copies(telescope, replacements, arity)
    copy_count = length(copies)
    left = install_copies(left, copy_map, arity, copy_count)
    right = install_copies(right, copy_map, arity, copy_count)
    carrier = install_copies(carrier, copy_map, arity, copy_count)

    theorem_telescope =
      telescope ++
        Enum.map(field_telescope, fn {_name, type} -> {Grade.unrestricted(), type} end) ++
        Enum.map(copies, fn %{grade: grade, type: type} -> {grade, type} end)

    theorem_ctx = context_for(env, theorem_telescope)

    carrier =
      case Kernel.infer(theorem_ctx, left) do
        {:ok, inferred} -> Quote.reify(inferred, Context.length(theorem_ctx), env)
        {:error, _} -> carrier
      end

    right =
      case Kernel.normalize(theorem_ctx, left) do
        :fuel_exhausted -> right
        normal -> normal
      end

    {proposition, reflexivity} = equality_terms(env, carrier, left, right)
    theorem_type = wrap(:pi, theorem_telescope, proposition)
    theorem_body = wrap(:lam, theorem_telescope, reflexivity)
    constructor_path = Enum.map(equation.steps, & &1.constructor)
    theorem = theorem_name(owner, constructor_path)

    original_quantities = quantities || List.duplicate(:unrestricted, parameter_count)

    original_quantities =
      Enum.reduce(Map.keys(replacements), original_quantities, fn
        original_index, current when is_integer(original_index) ->
          List.replace_at(current, parameter_count - 1 - original_index, :erased)

        _field, current ->
          current
      end)

    copy_quantities = Enum.map(copies, & &1.quantity)

    installed =
      Env.add_def(env, theorem, theorem_type, theorem_body, original_quantities ++ field_quantities ++ copy_quantities)

    canonical_theorem = Env.resolve_key(installed, installed.defs, theorem)
    installed = put_in(installed.defs[canonical_theorem][:generated_equation], true)

    with :ok <- Kernel.check_def(installed, canonical_theorem),
         certified = Cure.Elab.TotalityClosure.certify_available(installed, canonical_theorem),
         true <- Env.total?(certified, canonical_theorem) do
      info = Metadata.source_info(meta)
      surface = Map.get(surfaces, Enum.map(constructor_path, &Name.base/1), %{})

      source_metadata = %{
        left_surface:
          Map.get(surface, :left, {:defining_equation_call, Name.base(owner), Enum.map(constructor_path, &Name.base/1)}),
        right_surface: Map.get(surface, :right, {:compiled_branch, Enum.map(constructor_path, &Name.base/1)}),
        definition_span: Map.get(surface, :span, info && info.whole),
        provenance: %{kind: :generated_defining_equation, owner: owner, constructor_path: constructor_path}
      }

      descriptor = %{
        owner: owner,
        theorem: canonical_theorem,
        constructor_path: constructor_path,
        pattern_key: structural_key(owner, constructor_path),
        telescope: theorem_telescope,
        left_core: left,
        right_core: right,
        visibility: Keyword.get(meta, :visibility, :public),
        application_parameter_count: parameter_count,
        application_field_count: arity,
        application_replacements: replacements,
        application_copy_map: copy_map
      }

      :ok = SourceMetadata.put_equation(canonical_theorem, source_metadata)
      {:ok, Env.put_equation(certified, owner, descriptor)}
    else
      # Some compiled decision-tree branches carry convoy refinements that
      # cannot yet be re-abstracted as a closed standalone theorem. Never
      # publish an unchecked approximation; leave that branch unavailable.
      false -> {:ok, env}
      {:error, _reason} -> {:ok, env}
    end
  end

  def source_metadata(%{theorem: theorem}), do: SourceMetadata.equation(theorem)

  defp with_source_metadata(descriptor), do: Map.merge(descriptor, source_metadata(descriptor))

  defp theorem_name(owner, constructor_path) do
    owner_module = Name.owner(owner)
    base = Name.base(owner)
    suffix = Enum.map_join(constructor_path, "$", &Name.base/1)
    Name.qualify(owner_module || "Main", "#{base}$equation$#{suffix}")
  end

  defp structural_key(owner, path),
    do: Name.base(owner) <> "/" <> Enum.map_join(path, "/", &Name.base/1)

  defp data_params({:data, _family, params, _indices}), do: params
  defp data_params(_other), do: []

  defp specialize_fields(fields, params, base_shift) do
    fields
    |> Enum.with_index()
    |> Enum.map(fn {{name, type}, index} ->
      prior_fields = for field <- (index - 1)..0//-1, index > 0, do: {:var, field}
      # A Pi domain is scoped only over the binders preceding it. Generated
      # constructor fields sit after the complete owner telescope, so move its
      # datatype parameters across the scrutinised binder, every later owner
      # binder, earlier path fields, and earlier fields of this constructor.
      shifted_params = Enum.map(params, &Subst.shift(&1, base_shift + index, 0))
      {name, Subst.instantiate(type, shifted_params ++ prior_fields)}
    end)
  end

  defp equation_fields(env, telescope, steps, parameter_count) do
    Enum.reduce(steps, {[], []}, fn step, {fields, quantities} ->
      constructor = Inductive.get_ctor(env, step.constructor)
      position = parameter_count - 1 - step.scrutinee
      {_grade, scrutinee_domain} = Enum.at(telescope, position)
      params = data_params(scrutinee_domain)

      specialized =
        specialize_fields(
          (constructor && constructor.args) || [],
          params,
          parameter_count - position + length(fields)
        )

      field_quantities = (constructor && constructor.quantities) || List.duplicate(:unrestricted, step.arity)
      {fields ++ specialized, quantities ++ field_quantities}
    end)
  end

  defp dependent_copies(telescope, replacements, total_fields) do
    parameter_count = length(telescope)

    telescope
    |> Enum.with_index()
    |> Enum.reduce({[], %{}}, fn {{grade, domain}, position}, {copies, copy_map} ->
      original_index = parameter_count - 1 - position
      base_domain = Subst.shift(domain, total_fields + parameter_count - position, 0)
      refined_domain = apply_original_replacements(base_domain, replacements, total_fields)

      if Map.has_key?(replacements, original_index) or refined_domain == base_domain do
        {copies, copy_map}
      else
        prior_count = length(copies)
        shifted = Subst.shift(refined_domain, prior_count, 0)

        shifted =
          Enum.reduce(copy_map, shifted, fn {copied_original, copied_index}, current ->
            Term.subst(current, total_fields + copied_original + prior_count, {:var, copied_index + 1})
          end)

        copy = %{original: original_index, grade: grade, quantity: grade, type: shifted}

        next_map =
          copy_map
          |> Enum.map(fn {key, index} -> {key, index + 1} end)
          |> Map.new()
          |> Map.put(original_index, 0)

        {copies ++ [copy], next_map}
      end
    end)
  end

  defp install_copies(term, copy_map, total_fields, copy_count) do
    shifted = Subst.shift(term, copy_count, 0)

    Enum.reduce(copy_map, shifted, fn {original_index, copy_index}, current ->
      Term.subst(current, copy_count + total_fields + original_index, {:var, copy_index})
    end)
  end

  # Constructor result indices refine owner parameters in dependent matches.
  # Keep the owner's original telescope (refined binders simply become unused),
  # but replace those arguments in the defining call and result carrier. This
  # yields, for example, `sym(A, w, w, reflexive(w)) == reflexive(w)` without
  # needing a bespoke dependent telescope or trusting anything beyond the
  # constructor declaration the kernel already checks.
  defp refinement_replacements(env, telescope, steps, parameter_count, total_fields) do
    Enum.reduce(steps, %{}, fn step, replacements ->
      constructor = Inductive.get_ctor(env, step.constructor)
      position = parameter_count - 1 - step.scrutinee
      later_fields = total_fields - step.offset - step.arity

      constructor_value =
        {:ctor, step.constructor,
         for(index <- (step.arity - 1)..0//-1, step.arity > 0, do: {:var, later_fields + index})}

      replacements =
        case Map.get(replacements, step.scrutinee) do
          nil ->
            replacements

          prior_value ->
            collect_index_refinements(
              prior_value,
              constructor_value,
              replacements,
              total_fields,
              parameter_count
            )
        end

      {_grade, domain} = Enum.at(telescope, position)
      shifted_domain = Subst.shift(domain, total_fields + parameter_count - position, 0)
      shifted_domain = apply_original_replacements(shifted_domain, replacements, total_fields)

      case shifted_domain do
        {:data, _family, scrutinee_params, scrutinee_indices} ->
          constructor_indices =
            Enum.map((constructor && constructor.result_indices) || [], fn index ->
              specialize_constructor_result(
                index,
                scrutinee_params,
                step,
                total_fields,
                length((constructor && constructor.args) || [])
              )
            end)

          Enum.zip(scrutinee_indices, constructor_indices)
          |> Enum.reduce(replacements, fn {scrutinee_index, constructor_index}, current ->
            collect_index_refinements(scrutinee_index, constructor_index, current, total_fields, parameter_count)
          end)

        _ ->
          replacements
      end
    end)
  end

  defp specialize_constructor_result(term, scrutinee_params, step, total_fields, constructor_arity) do
    later_fields = total_fields - step.offset - step.arity
    parameter_count = length(scrutinee_params)

    mapping =
      Enum.reduce(0..(constructor_arity - 1)//1, %{}, fn index, acc ->
        Map.put(acc, index, {:var, later_fields + index})
      end)

    mapping =
      scrutinee_params
      |> Enum.with_index()
      |> Enum.reduce(mapping, fn {parameter, index}, acc ->
        slot = constructor_arity + parameter_count - 1 - index
        Map.put(acc, slot, parameter)
      end)

    replace_frame_vars(term, mapping, 0)
  end

  defp collect_index_refinements({:var, full_index}, replacement, current, total_fields, parameter_count)
       when full_index >= total_fields and full_index < total_fields + parameter_count do
    Map.put_new(current, full_index - total_fields, replacement)
  end

  defp collect_index_refinements({:var, left}, {:var, right}, current, total_fields, _parameter_count)
       when left < total_fields and right < total_fields and left != right do
    {later, earlier} = if left < right, do: {left, right}, else: {right, left}
    Map.put_new(current, {:field, later}, {:var, earlier})
  end

  defp collect_index_refinements(replacement, {:var, full_index}, current, total_fields, parameter_count)
       when full_index >= total_fields and full_index < total_fields + parameter_count do
    Map.put_new(current, full_index - total_fields, replacement)
  end

  defp collect_index_refinements({:var, field}, replacement, current, total_fields, _parameter_count)
       when field < total_fields do
    Map.put_new(current, {:field, field}, replacement)
  end

  defp collect_index_refinements(replacement, {:var, field}, current, total_fields, _parameter_count)
       when field < total_fields do
    Map.put_new(current, {:field, field}, replacement)
  end

  defp collect_index_refinements(left, right, current, total_fields, parameter_count)
       when is_tuple(left) and is_tuple(right) and tuple_size(left) == tuple_size(right) and
              elem(left, 0) == elem(right, 0) do
    left
    |> Tuple.to_list()
    |> Enum.zip(Tuple.to_list(right))
    |> Enum.reduce(current, fn {l, r}, acc ->
      collect_index_refinements(l, r, acc, total_fields, parameter_count)
    end)
  end

  defp collect_index_refinements(left, right, current, total_fields, parameter_count)
       when is_list(left) and is_list(right) do
    Enum.zip(left, right)
    |> Enum.reduce(current, fn {l, r}, acc ->
      collect_index_refinements(l, r, acc, total_fields, parameter_count)
    end)
  end

  defp collect_index_refinements(_left, _right, current, _total_fields, _parameter_count), do: current

  defp apply_original_replacements(term, replacements, total_fields) do
    Enum.reduce(replacements, term, fn {key, replacement}, current ->
      Term.subst(current, replacement_index(key, total_fields), replacement)
    end)
  end

  defp replacement_index({:field, index}, _total_fields), do: index

  defp replacement_index(original_index, total_fields) when is_integer(original_index),
    do: total_fields + original_index

  defp normalize_replacements(replacements, total_fields) do
    Map.new(replacements, fn {key, replacement} ->
      without_self = Map.delete(replacements, key)
      {key, apply_original_replacements(replacement, without_self, total_fields)}
    end)
  end

  defp refine_field_telescope(fields, replacements, total_fields) do
    fields
    |> Enum.with_index()
    |> Enum.map(fn {{name, type}, position} ->
      remaining = total_fields - position

      # A constructor-field domain is scoped only over fields introduced
      # before it.  Refinements learned by later nested matches may mention
      # binders that do not exist yet; applying those here would shift them
      # through zero and manufacture negative de Bruijn indices.
      aliases =
        Map.filter(replacements, fn
          {{:field, index}, replacement} ->
            index >= remaining and accessible_field_refs?(replacement, remaining, total_fields)

          _other ->
            false
        end)

      refined =
        type
        |> Subst.shift(remaining, 0)
        |> apply_original_replacements(aliases, total_fields)
        |> Subst.shift(-remaining, 0)

      {name, refined}
    end)
  end

  defp accessible_field_refs?({:var, index}, remaining, total_fields),
    do: index >= remaining or index >= total_fields

  defp accessible_field_refs?(term, remaining, total_fields) when is_tuple(term),
    do: term |> Tuple.to_list() |> Enum.all?(&accessible_field_refs?(&1, remaining, total_fields))

  defp accessible_field_refs?(terms, remaining, total_fields) when is_list(terms),
    do: Enum.all?(terms, &accessible_field_refs?(&1, remaining, total_fields))

  defp accessible_field_refs?(_leaf, _remaining, _total_fields), do: true

  defp replace_frame_vars({:var, index}, mapping, depth) do
    case Map.fetch(mapping, index - depth) do
      {:ok, replacement} -> Subst.shift(replacement, depth, 0)
      :error -> {:var, index}
    end
  end

  defp replace_frame_vars({tag, grade, domain, body}, mapping, depth) when tag in [:pi, :lam],
    do: {tag, grade, replace_frame_vars(domain, mapping, depth), replace_frame_vars(body, mapping, depth + 1)}

  defp replace_frame_vars({:app, function, argument}, mapping, depth),
    do: {:app, replace_frame_vars(function, mapping, depth), replace_frame_vars(argument, mapping, depth)}

  defp replace_frame_vars({:data, name, params, indices}, mapping, depth),
    do:
      {:data, name, Enum.map(params, &replace_frame_vars(&1, mapping, depth)),
       Enum.map(indices, &replace_frame_vars(&1, mapping, depth))}

  defp replace_frame_vars({:ctor, name, args}, mapping, depth),
    do: {:ctor, name, Enum.map(args, &replace_frame_vars(&1, mapping, depth))}

  defp replace_frame_vars(other, _mapping, _depth), do: other

  defp peel(term, tag), do: peel(term, tag, [])
  defp peel({tag, grade, domain, body}, tag, acc), do: peel(body, tag, acc ++ [{grade, domain}])
  defp peel(body, _tag, acc), do: {acc, body}

  defp wrap(tag, telescope, body) do
    Enum.reduce(Enum.reverse(telescope), body, fn {grade, domain}, inner -> {tag, grade, domain, inner} end)
  end

  defp context_for(env, telescope) do
    Enum.reduce(telescope, Context.empty(env), fn {_grade, domain}, ctx ->
      Context.extend(ctx, Eval.eval(domain, Context.env(ctx)))
    end)
  end

  defp equality_terms(_env, {:type, 0}, left, right) do
    family = Name.qualify("Std.Equivalent", :TypeEquivalent)
    constructor = Name.qualify("Std.Equivalent", :type_reflexive)
    {{:data, family, [], [left, right]}, {:ctor, constructor, [right]}}
  end

  defp equality_terms(_env, carrier, left, right),
    do: {Rewrite.mk_eq(carrier, left, right), Rewrite.mk_refl(right)}

  defp surface_equations(_owner, _meta, nil), do: {%{}, []}

  defp surface_equations(owner, meta, body) do
    params =
      meta
      |> Keyword.get(:params, [])
      |> Enum.map(fn {:param, _param_meta, name} -> name end)

    entries = collect_surfaces(body, owner, params, %{}, [])

    surfaces =
      Map.new(entries, fn {path, replacements, right, span} ->
        arguments =
          Enum.map(params, fn name ->
            Map.get(replacements, name, {:variable, [scope: :local], name})
          end)

        left = {:function_call, [name: Name.base(owner)], arguments}
        {path, %{left: left, right: right, span: span}}
      end)

    {surfaces, Enum.map(entries, &elem(&1, 0))}
  end

  defp collect_surfaces(
         {:pattern_match, _meta, [{:variable, _scrutinee_meta, name} | arms]},
         owner,
         params,
         replacements,
         path
       )
       when is_list(arms) do
    Enum.flat_map(arms, fn
      {:match_arm, arm_meta, body} ->
        pattern = Keyword.fetch!(arm_meta, :pattern)

        case pattern_constructor(pattern) do
          nil ->
            []

          constructor ->
            next_path = path ++ [constructor]
            next_replacements = Map.put(replacements, name, pattern)
            right = single_body(body)
            nested = collect_surfaces(right, owner, params, next_replacements, next_path)

            if nested == [] do
              info = Metadata.source_info(arm_meta)
              [{next_path, next_replacements, right, info && info.whole}]
            else
              nested
            end
        end
    end)
  end

  defp collect_surfaces(_body, _owner, _params, _replacements, _path), do: []

  defp pattern_constructor({:function_call, meta, _args}), do: meta |> Keyword.get(:name) |> Name.base()

  defp pattern_constructor({:variable, _meta, name}) do
    if String.match?(to_string(name), ~r/^[A-Z]/), do: Name.base(name)
  end

  defp pattern_constructor(_pattern), do: nil

  defp single_body([body]), do: body
  defp single_body(body), do: body

  defp functions(list) when is_list(list), do: Enum.flat_map(list, &functions/1)
  # Enum constructors with fields share the parser's `:function_def` shape but
  # are marked `variant: true`; they are declarations, not executable function
  # bodies. Treating `Value.String(String)` as a function made equation
  # generation interpret its field-type AST as formal parameters and crash.
  defp functions({:function_def, meta, body}) when is_list(meta) do
    if Keyword.get(meta, :variant, false), do: [], else: [{meta, body}]
  end

  defp functions({_tag, _meta, children}) when is_list(children),
    do: Enum.flat_map(children, &functions/1)

  defp functions(_other), do: []
end
