# lib/cure/compiler/macro_validate.ex
defmodule Cure.Compiler.MacroValidate do
  @moduledoc """
  Frontend validation of `macro` definitions against the self-proving
  obligations (design 2026-07-11 §3). TCB delta zero — pure analysis over the
  parsed `{:macro_def, …}` AST, upstream of the elaborator.
  """

  alias Cure.Compiler.{MacroFuzz, MacroSyntax}
  alias Cure.MetaAST.Metadata

  @type point :: {:hole_kind, String.t()} | {:keyword, String.t()} | {:failure, String.t()}

  @doc """
  Check a macro's `explain` block covers every structural failure point derived
  from its `syntax`/`literal` rules (design §3.2). Returns `:ok` or
  `{:error, {:missing_diagnosis, uncovered_points}}`.
  """
  @spec check_explain_exhaustive(tuple()) :: :ok | {:error, {:missing_diagnosis, [point]}}
  def check_explain_exhaustive({:macro_def, _meta, rules}) do
    points = derive_points(rules)
    covered = covered_points(rules)

    case Enum.reject(points, &covered?(&1, covered)) do
      [] -> :ok
      uncovered -> {:error, {:missing_diagnosis, uncovered}}
    end
  end

  @doc """
  Enforce all self-proving obligations for the macro definitions in a parsed
  program. The environment is supplied after declaration elaboration so
  computed examples can execute against the module's real signatures.
  """
  @spec check_program(tuple() | list(), Cure.Core.Env.t()) :: :ok | {:error, term()}
  def check_program(ast, env) do
    ast
    |> collect_macro_defs()
    |> Enum.reduce_while(:ok, fn macro_def, :ok ->
      with :ok <- check_reserved_fields(macro_def),
           :ok <- check_explain_if_declared(macro_def),
           :ok <- check_pins_if_explainable(macro_def),
           :ok <- check_examples(macro_def, env),
           :ok <- check_computed_examples(macro_def, env),
           :ok <- check_expansion_proof(macro_def, env) do
        {:cont, :ok}
      else
        {:error, _} = error -> {:halt, contextualize_validation(error, macro_def)}
      end
    end)
  end

  # A handwritten macro may intentionally use the lightweight compatibility
  # surface without an `explain` block. When the author declares that block,
  # enforce the complete self-proving contract; all macros still receive the
  # expansion soundness gate below.
  defp check_explain_if_declared({:macro_def, _meta, rules} = macro_def) do
    if Enum.any?(rules, &(&1[:kind] == :explain)) do
      contextualize_validation(check_explain_exhaustive(macro_def), macro_def)
    else
      :ok
    end
  end

  defp check_pins_if_explainable({:macro_def, _meta, rules} = macro_def) do
    if Enum.any?(rules, &(&1[:kind] == :explain)) do
      contextualize_validation(check_rules_pinned(macro_def), macro_def)
    else
      :ok
    end
  end

  defp contextualize_validation(:ok, _macro_def), do: :ok

  defp contextualize_validation({:error, {:source_context, _reason, _context}} = error, _macro_def), do: error

  defp contextualize_validation({:error, {kind, _details} = reason}, {:macro_def, meta, rules})
       when kind in [
              :missing_diagnosis,
              :rule_unpinned,
              :example_mismatch,
              :example_type_mismatch,
              :computed_example_error,
              :expansion_ill_typed,
              :unsupported_hole_type,
              :generated_hole_not_well_typed,
              :invalid_macro_segment,
              :unsupported_surface_filler,
              :missing_hole_filler,
              :invalid_repeated_hole_filler
            ] do
    {:error, {:source_context, reason, validation_source_context(reason, meta, rules)}}
  end

  defp contextualize_validation(
         {:error, {:reserved_syntax_field, _field, _keywords} = reason},
         {:macro_def, meta, rules}
       ) do
    {:error, {:source_context, reason, validation_source_context(reason, meta, rules)}}
  end

  defp contextualize_validation({:error, _reason} = error, _macro_def), do: error

  defp validation_source_context({:missing_diagnosis, points}, meta, rules) do
    explain_span =
      rules
      |> Enum.find(&(&1[:kind] == :explain))
      |> then(&(&1 && Map.get(&1, :source_span)))

    rule_spans =
      rules
      |> Enum.filter(fn rule -> Enum.any?(points, &(&1 in rule_points(rule))) end)
      |> Enum.map(&Map.get(&1, :source_span))
      |> Enum.reject(&is_nil/1)
      |> Enum.uniq()

    macro_span = macro_source_span(meta)

    %{
      span: explain_span || List.first(rule_spans) || macro_span,
      macro_span: macro_span,
      explain_span: explain_span,
      rule_spans: rule_spans,
      related_spans: rule_spans,
      macro: Keyword.get(meta, :name),
      expression_category: :macro_validation
    }
  end

  defp validation_source_context({:rule_unpinned, keywords}, meta, rules) do
    rule_spans =
      rules
      |> Enum.filter(&(&1[:kind] in [:syntax, :computed] and &1.keyword in keywords))
      |> Enum.map(&Map.get(&1, :source_span))
      |> Enum.reject(&is_nil/1)
      |> Enum.uniq()

    macro_span = macro_source_span(meta)

    %{
      span: List.first(rule_spans) || macro_span,
      macro_span: macro_span,
      rule_spans: rule_spans,
      related_spans: Enum.drop(rule_spans, 1),
      macro: Keyword.get(meta, :name),
      expression_category: :macro_validation
    }
  end

  defp validation_source_context({kind, details}, meta, _rules)
       when kind in [:example_mismatch, :example_type_mismatch, :computed_example_error] and is_list(details) do
    example_spans = details |> Enum.map(&Map.get(&1, :source_span)) |> Enum.reject(&is_nil/1) |> Enum.uniq()
    rule_spans = details |> Enum.map(&Map.get(&1, :rule_span)) |> Enum.reject(&is_nil/1) |> Enum.uniq()
    macro_span = macro_source_span(meta)

    %{
      span: List.first(example_spans) || List.first(rule_spans) || macro_span,
      macro_span: macro_span,
      example_spans: example_spans,
      rule_spans: rule_spans,
      related_spans: rule_spans ++ Enum.drop(example_spans, 1),
      macro: Keyword.get(meta, :name),
      expression_category: :macro_example_validation
    }
  end

  defp validation_source_context({:reserved_syntax_field, field, keywords}, meta, rules) do
    offending =
      for rule <- rules,
          rule[:kind] == :computed,
          rule.keyword in keywords,
          hole_span <- List.wrap(get_in(rule, [:field_spans, field])) do
        %{hole_span: hole_span, rule_span: rule[:head_span] || rule[:source_span]}
      end

    hole_spans = offending |> Enum.map(& &1.hole_span) |> Enum.reject(&is_nil/1) |> Enum.uniq()
    rule_spans = offending |> Enum.map(& &1.rule_span) |> Enum.reject(&is_nil/1) |> Enum.uniq()
    macro_span = macro_source_span(meta)

    %{
      span: List.first(hole_spans) || List.first(rule_spans) || macro_span,
      macro_span: macro_span,
      hole_spans: hole_spans,
      rule_spans: rule_spans,
      related_spans: rule_spans ++ Enum.drop(hole_spans, 1),
      macro: Keyword.get(meta, :name),
      expression_category: :macro_validation
    }
  end

  defp validation_source_context({:expansion_ill_typed, details}, meta, rules) do
    keyword = Map.get(details, :keyword)
    rule = Enum.find(rules, &(&1[:kind] in [:syntax, :computed] and &1[:keyword] == keyword))
    macro_span = macro_source_span(meta)
    rule_span = rule && (rule[:head_span] || rule[:source_span])
    authored_span = rule && (rule[:body_span] || rule_span)

    %{
      span: authored_span || rule_span || macro_span,
      macro_span: macro_span,
      rule_span: rule_span,
      related_spans: Enum.reject([rule_span], &is_nil/1),
      macro: Keyword.get(meta, :name),
      rule_kind: rule && rule[:kind],
      keyword: keyword,
      expression_category: :macro_expansion_proof
    }
  end

  defp validation_source_context({:unsupported_hole_type, category}, meta, rules) do
    offenders =
      for rule <- rules,
          rule[:kind] in [:syntax, :computed],
          field <- fields_with_category(rule[:segments] || [], category),
          span <- List.wrap(get_in(rule, [:field_spans, field])) do
        %{field: field, keyword: rule[:keyword], span: span}
      end

    spans = offenders |> Enum.map(& &1.span) |> Enum.uniq()
    macro_span = macro_source_span(meta)

    %{
      span: List.first(spans) || macro_span,
      hole_spans: spans,
      offenders: offenders,
      related_spans: Enum.drop(spans, 1),
      macro_span: macro_span,
      macro: Keyword.get(meta, :name),
      category: category,
      expression_category: :macro_expansion_proof
    }
  end

  defp validation_source_context({:generated_hole_not_well_typed, details}, meta, rules) do
    category = if is_map(details), do: Map.get(details, :category), else: nil
    hole = if is_map(details), do: Map.get(details, :hole), else: nil

    spans =
      for rule <- rules,
          rule[:kind] in [:syntax, :computed],
          field <- fields_with_category(rule[:segments] || [], category),
          is_nil(hole) or field == hole,
          span <- List.wrap(get_in(rule, [:field_spans, field])) do
        span
      end
      |> Enum.uniq()

    macro_span = macro_source_span(meta)

    %{
      span: List.first(spans) || macro_span,
      hole_spans: spans,
      related_spans: Enum.drop(spans, 1),
      macro_span: macro_span,
      macro: Keyword.get(meta, :name),
      category: category,
      hole: hole,
      expression_category: :macro_proof_generator_invariant
    }
  end

  defp validation_source_context({kind, detail}, meta, rules)
       when kind in [
              :invalid_macro_segment,
              :unsupported_surface_filler,
              :missing_hole_filler,
              :invalid_repeated_hole_filler
            ] do
    rule_span =
      rules
      |> Enum.find_value(fn rule ->
        if rule[:kind] in [:syntax, :computed], do: Map.get(rule, :source_span)
      end)

    %{
      span: rule_span || macro_source_span(meta),
      macro: Keyword.get(meta, :name),
      hole: if(kind in [:missing_hole_filler, :invalid_repeated_hole_filler], do: detail),
      expectation_origin: :macro_proof_input,
      expression_category: :macro_rule
    }
  end

  defp fields_with_category(segments, category) when is_list(segments),
    do: Enum.flat_map(segments, &fields_with_category(&1, category))

  defp fields_with_category({:hole, %{name: name, kind: category}}, category), do: [name]
  defp fields_with_category({:repeat, segment}, category), do: fields_with_category(segment, category)
  defp fields_with_category({:optional, segments}, category), do: fields_with_category(segments, category)
  defp fields_with_category(_segment, _category), do: []

  defp macro_source_span(meta) do
    case Metadata.source_info(meta) do
      %{whole: span} -> span
      _ -> nil
    end
  end

  # StreamData is a test-only dependency. Structural macro validation remains
  # active in development/release builds; the generative gate runs whenever
  # the optional backend is present (the test environment and CI).
  defp check_expansion_proof(macro_def, env) do
    if Code.ensure_loaded?(StreamData), do: MacroFuzz.check_expansion_proof(macro_def, env), else: :ok
  end

  @doc "Run only the generated expansion gate for transitional classic compiles."
  @spec check_expansion_proofs(tuple() | list(), Cure.Core.Env.t()) :: :ok | {:error, term()}
  def check_expansion_proofs(ast, env) do
    collect_macro_defs(ast)
    |> Enum.reduce_while(:ok, fn macro_def, :ok ->
      case MacroFuzz.check_expansion_proof(macro_def, env) do
        :ok -> {:cont, :ok}
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  @doc """
  Check no `computed by` rule declares a hole named `context`.

  A computed rule's derived record carries the reflected expansion context in a
  trailing `context` field, so a hole of that name would take the field's place
  and leave the elab silently blind to where it was invoked. Reserve the name
  and say so, rather than let the hole win in silence.
  """
  @spec check_reserved_fields(tuple()) :: :ok | {:error, {:reserved_syntax_field, String.t(), [String.t()]}}
  def check_reserved_fields({:macro_def, _meta, rules}) do
    field = MacroSyntax.context_field()

    rules
    |> Enum.filter(&(&1[:kind] == :computed))
    |> Enum.filter(&(field in Map.get(&1, :syntax_fields, [])))
    |> Enum.map(& &1.keyword)
    |> case do
      [] -> :ok
      keywords -> {:error, {:reserved_syntax_field, field, keywords}}
    end
  end

  @doc """
  Check every `syntax` rule, including `computed by` rules, carries at least one
  worked example (design §5.1).
  Returns `:ok` or `{:error, {:rule_unpinned, unpinned_keywords}}`.
  """
  @spec check_rules_pinned(tuple()) :: :ok | {:error, {:rule_unpinned, [String.t()]}}
  def check_rules_pinned({:macro_def, _meta, rules}) do
    unpinned =
      rules
      |> Enum.filter(&(&1[:kind] in [:syntax, :computed]))
      |> Enum.filter(&(Map.get(&1, :examples, []) == []))
      |> Enum.map(& &1.keyword)

    case unpinned do
      [] -> :ok
      kws -> {:error, {:rule_unpinned, kws}}
    end
  end

  # Structural Diagnosis: one point per typed hole, per literal segment, AND
  # (for `:syntax` rules) the rule's own dispatch keyword — across all
  # syntax/literal rules, deduped and order-stable.
  #
  # NOTE: a `:syntax` rule's dispatch keyword lives in `rule.keyword`, NOT in
  # `rule.segments` (`segments` is only what follows it). Omitting it would mean
  # the single most common macro-use failure (typing the wrong keyword) could
  # never be required to have an `explain` clause — the plan's own headline
  # example (`syntax every <t: Duration> becomes …`) has NO literal `segments`.
  defp derive_points(rules) do
    rules
    |> Enum.filter(&(&1[:kind] in [:syntax, :literal, :fail]))
    |> Enum.flat_map(fn rule ->
      failure_points =
        case rule do
          %{kind: :fail, name: name} when is_binary(name) -> [{:failure, name}]
          _ -> []
        end

      keyword_points =
        case rule do
          %{kind: :syntax, keyword: kw} when is_binary(kw) -> [{:keyword, kw}]
          _ -> []
        end

      failure_points ++ keyword_points ++ Enum.map(Map.get(rule, :segments, []), &segment_point/1)
    end)
    |> Enum.reject(&is_nil/1)
    |> Enum.uniq()
  end

  defp rule_points(rule) do
    failure_points =
      case rule do
        %{kind: :fail, name: name} when is_binary(name) -> [{:failure, name}]
        _ -> []
      end

    keyword_points =
      case rule do
        %{kind: :syntax, keyword: keyword} when is_binary(keyword) -> [{:keyword, keyword}]
        _ -> []
      end

    failure_points ++ keyword_points ++ Enum.map(Map.get(rule, :segments, []), &segment_point/1)
  end

  defp segment_point({:hole, %{kind: k}}), do: {:hole_kind, k}
  defp segment_point({:lit, w}), do: {:keyword, w}
  defp segment_point(_), do: nil

  # What the explain block covers, as a set of clause points.
  defp covered_points(rules) do
    rules
    |> Enum.filter(&(&1[:kind] == :explain))
    |> Enum.flat_map(& &1.clauses)
    |> Enum.map(& &1.point)
    |> MapSet.new()
  end

  # A `{:category, c}` clause covers a `{:hole_kind, c}` point; a `{:keyword, w}`
  # clause covers a `{:keyword, w}` point.
  defp covered?({:hole_kind, k}, covered), do: MapSet.member?(covered, {:category, k})
  defp covered?({:keyword, w}, covered), do: MapSet.member?(covered, {:keyword, w})
  defp covered?({:failure, name}, covered), do: MapSet.member?(covered, {:category, name})

  defp collect_macro_defs({:macro_def, _meta, _rules} = macro_def), do: [macro_def]

  defp collect_macro_defs({_, _, children}) when is_list(children),
    do: Enum.flat_map(children, &collect_macro_defs/1)

  defp collect_macro_defs(list) when is_list(list),
    do: Enum.flat_map(list, &collect_macro_defs/1)

  defp collect_macro_defs(_other), do: []

  alias Cure.Compiler.Parser
  alias Cure.Elab.MacroExpand

  @doc """
  Check every `syntax` rule's `{:expansion, _}` example actually expands to its
  pinned result, up to α-renaming (design §5.1). `{:type, _}` pins are skipped
  (deferred). Returns `:ok` or `{:error, {:example_mismatch, mismatches}}`.
  """
  @spec check_examples(tuple()) :: :ok | {:error, {:example_mismatch, [map()]}}
  def check_examples(macro_def), do: check_examples(macro_def, nil)

  @doc """
  Check exact and type-only example pins in a module environment.

  Exact pins compare α-normalized surface ASTs. Type-only pins lower their
  expected type and check the expanded expression through the ordinary
  expression elaborator, preserving the module's imports and declarations.
  """
  @spec check_examples(tuple(), Cure.Core.Env.t() | nil) ::
          :ok
          | {:error, {:example_mismatch, [map()]}}
          | {:error, {:example_type_mismatch, [map()]}}
  def check_examples({:macro_def, _meta, rules}, env) do
    results =
      rules
      |> Enum.filter(&(&1[:kind] == :syntax))
      |> Enum.flat_map(fn rule ->
        Enum.map(Map.get(rule, :examples, []), fn %{use_site: use_site, expected: expected} = example ->
          actual = Parser.expand_example(rules, use_site)

          rule.keyword
          |> check_example_pin(actual, expected, env)
          |> attach_example_source(example, rule)
        end)
      end)

    mismatches = for {:mismatch, details} <- results, do: details
    type_failures = for {:type_failure, details} <- results, do: details

    cond do
      type_failures != [] -> {:error, {:example_type_mismatch, type_failures}}
      mismatches != [] -> {:error, {:example_mismatch, mismatches}}
      true -> :ok
    end
  end

  defp check_example_pin(keyword, actual, {:expansion, expected}, _env) do
    if normalize_for_comparison(actual) == normalize_for_comparison(expected) do
      :ok
    else
      {:mismatch, %{keyword: keyword, expected: expected, actual: actual}}
    end
  end

  defp check_example_pin(_keyword, _actual, {:type, _expected}, nil), do: :ok

  defp check_example_pin(keyword, actual, {:type, expected}, env) do
    alias Cure.Core.Context
    alias Cure.Elab.{Declarations, Elaborator}

    case Declarations.lower_type(expected, [], env) do
      {:ok, expected_core} ->
        case Elaborator.elaborate_expr_checked(actual, expected_core, [], Context.empty(env), env) do
          {:ok, _term} -> :ok
          {:error, reason} -> {:type_failure, %{keyword: keyword, expected: expected, actual: actual, reason: reason}}
        end

      {:error, reason} ->
        {:type_failure, %{keyword: keyword, expected: expected, actual: actual, reason: reason}}
    end
  end

  defp attach_example_source(:ok, _example, _rule), do: :ok

  defp attach_example_source({status, details}, example, rule) when status in [:mismatch, :type_failure, :failure] do
    {status,
     details
     |> Map.put(:source_span, Map.get(example, :source_span))
     |> Map.put(:use_site_span, Map.get(example, :use_site_span))
     |> Map.put(:expected_span, Map.get(example, :expected_span))
     |> Map.put(:rule_span, Map.get(rule, :head_span) || Map.get(rule, :source_span))}
  end

  @doc """
  Execute expansion pins attached to `computed by` rules in a module environment.

  The parser deliberately leaves computed uses deferred. This check supplies the
  environment needed by the compile-time executor and reports either a pin
  mismatch or an execution failure without collapsing the latter into a false
  success.
  """
  @spec check_computed_examples(tuple(), Cure.Core.Env.t()) ::
          :ok
          | {:error, {:computed_example_error, [map()]}}
          | {:error, {:example_mismatch, [map()]}}
  def check_computed_examples({:macro_def, _meta, rules}, env) do
    results =
      rules
      |> Enum.filter(&(&1[:kind] == :computed))
      |> Enum.flat_map(fn rule ->
        for %{use_site: use_site, expected: {:expansion, expected}} = example <- Map.get(rule, :examples, []) do
          actual = Parser.expand_example(rules, use_site)

          result =
            case MacroExpand.expand(actual, env) do
              {:ok, expanded} ->
                if normalize_for_comparison(expanded) == normalize_for_comparison(expected) do
                  :ok
                else
                  {:mismatch, %{keyword: rule.keyword, expected: expected, actual: expanded}}
                end

              {:error, reason} ->
                {:failure, %{keyword: rule.keyword, reason: reason}}
            end

          attach_example_source(result, example, rule)
        end
      end)

    failures = for {:failure, details} <- results, do: details
    mismatches = for {:mismatch, details} <- results, do: details

    cond do
      failures != [] -> {:error, {:computed_example_error, failures}}
      mismatches != [] -> {:error, {:example_mismatch, mismatches}}
      true -> :ok
    end
  end

  # α-normalise for example comparison: drop source positions, then collapse
  # `<fresh>` gensym suffixes (`x$0` → `x`) so a template binder and its pin
  # compare equal.
  #
  # A `:variable` node's meta is dropped ENTIRELY (not just line/col): it is
  # provenance about how the identifier was parsed (`scope: :local`,
  # `variant: true`, ...), not part of what the reference denotes. This
  # matters because a `<fresh Name>` marker in BINDER position parses to
  # `{:fresh_name, [line:, col:], name}` (no `scope` key -- that key is only
  # ever attached by the ordinary-identifier parse path) and `freshen/2`'s
  # `apply_freshening` reuses that meta verbatim when rewriting the marker to
  # `{:variable, meta, gensym}`. A hand-written pin's ordinary `h` always
  # carries `scope: :local`. Comparing full meta made every correctly-pinned
  # `<fresh>`-as-binder example spuriously mismatch; the only content that
  # participates in α-equivalence for a variable reference is its (degensym'd)
  # name.
  defp normalize_for_comparison(ast), do: ast |> Metadata.semantic_key() |> normalize()

  defp normalize({:variable, _meta, name}) when is_binary(name) do
    {:variable, [], degensym(name)}
  end

  defp normalize({t, meta, children}) when is_list(children) do
    {t, strip_pos(meta), Enum.map(children, &normalize/1)}
  end

  # An integer literal's `:exact_integer` is the author's own digits, kept
  # because the literal protocols hand them to `from_natural_literal` verbatim.
  # A literal a macro BUILDS has no source text and so no spelling — but it is
  # the same literal as the pin's `0`, since a missing spelling resolves to the
  # value's decimal rendering. Canonicalize the key on both sides before
  # comparing, or every computed expansion pinned against a plain numeral
  # mismatches on metadata that denotes exactly what the pin denotes.
  # `Metadata.integer_spelling/2` is the same resolution the elaborator uses to
  # pick the protocol payload, so `0x10` and a computed `16` still differ.
  defp normalize({:literal, meta, value}) when is_list(meta) and is_integer(value) do
    spelling = Metadata.integer_spelling(Keyword.get(meta, :exact_integer), value)
    {:literal, meta |> strip_pos() |> Keyword.put(:exact_integer, spelling), value}
  end

  # A scalar-valued node (`:literal`'s {subtype, value} shape — `value` is a raw
  # integer/float/string/bool/atom/char, NOT a list of children) still carries
  # `:line`/`:col` in its meta that must be stripped, exactly like any other node.
  # Without this clause every `:literal` falls through to the catch-all UNCHANGED,
  # so its source position never gets stripped and check_examples rejects almost
  # every real macro example.
  defp normalize({t, meta, value}) when is_list(meta) do
    {t, strip_pos(meta), normalize(value)}
  end

  defp normalize(values) when is_list(values), do: Enum.map(values, &normalize/1)

  defp normalize(values) when is_map(values) and not is_struct(values) do
    Map.new(values, fn {key, value} -> {normalize(key), normalize(value)} end)
  end

  defp normalize(value) when is_tuple(value) do
    value |> Tuple.to_list() |> Enum.map(&normalize/1) |> List.to_tuple()
  end

  defp normalize(other), do: other

  defp strip_pos(meta) when is_list(meta) do
    meta
    |> Enum.reject(fn {k, _} -> Metadata.diagnostic_key?(k) end)
    |> Enum.map(fn
      {k, v} -> {k, normalize_meta_value(v)}
      other -> other
    end)
  end

  defp strip_pos(meta), do: meta

  defp normalize_meta_value(v) when is_tuple(v), do: normalize(v)
  defp normalize_meta_value(v) when is_list(v), do: Enum.map(v, &normalize_meta_value/1)

  defp normalize_meta_value(v) when is_map(v) and not is_struct(v),
    do: Map.new(v, fn {k, value} -> {k, normalize(value)} end)

  defp normalize_meta_value(v), do: v

  defp degensym(name) do
    case Regex.run(~r/^(.+)\$\d+$/, name) do
      [_, base] -> base
      _ -> name
    end
  end
end
