defmodule Cure.Diagnostic.Adapter.StaticAnalysis do
  @moduledoc "Converts whole-definition static-analysis rejections with authored source context."

  alias Cure.Diagnostic
  alias Cure.Diagnostic.{Doc, Label, Span, Suggestion}

  @spec from_error(term(), keyword()) :: Diagnostic.t()
  def from_error(error, opts \\ [])

  def from_error({:pickup_no_else, details}, opts) when is_map(details) do
    clauses = pickup_spans(details.clauses)
    span = List.last(clauses) || details.pickup || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E076",
      key: :pickup_missing_else,
      severity: :error,
      title: "Pickup needs a fallback",
      body:
        Doc.paragraph(
          "A `pickup` must finish with a fallback branch so it has a result when no earlier condition is true."
        ),
      primary: pickup_label(span, :primary, "this is the final branch, but it is not a fallback"),
      suggestions: [
        %Suggestion{
          message: "Add `else -> ...` after this branch, or change the final condition to `true`",
          applicability: :manual
        }
      ],
      payload: Map.put(details, :repair_alternatives, [:append_else_branch, :use_trailing_true])
    )
  end

  def from_error({:pickup_else_not_last, details}, opts) when is_map(details) do
    clauses = pickup_spans(details.clauses)
    index = details.terminator_index
    else_span = details.else_clauses |> Enum.find_value(fn {idx, span} -> if idx == index, do: span end)
    primary_span = else_span || Enum.at(clauses, index) || Keyword.get(opts, :span)

    secondary =
      clauses
      |> Enum.drop(index + 1)
      |> Enum.map(&pickup_label(&1, :secondary, "this branch can never be reached after `else`"))
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E077",
      key: :pickup_else_not_last,
      severity: :error,
      title: "Fallback branch is not last",
      body: Doc.paragraph("An `else` branch matches every remaining case, so no branch may follow it."),
      primary: pickup_label(primary_span, :primary, "this fallback matches everything that reaches it"),
      secondary: secondary,
      suggestions: [
        %Suggestion{message: "Move the `else` branch after every conditional branch", applicability: :manual}
      ],
      payload: details
    )
  end

  def from_error({:pickup_multiple_else, details}, opts) when is_map(details) do
    else_spans = details.else_clauses |> Enum.map(&elem(&1, 1)) |> pickup_spans()
    primary_span = Enum.at(else_spans, 1) || List.first(else_spans) || Keyword.get(opts, :span)

    secondary =
      else_spans
      |> List.delete_at(1)
      |> Enum.map(&pickup_label(&1, :secondary, "another fallback branch is here"))
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E078",
      key: :pickup_multiple_else,
      severity: :error,
      title: "Pickup has more than one fallback",
      body:
        Doc.paragraph(
          "Only one `else` branch is allowed because the first fallback already matches every remaining case."
        ),
      primary: pickup_label(primary_span, :primary, "this second fallback is redundant"),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Keep one `else` branch and remove or give conditions to the others",
          applicability: :manual
        }
      ],
      payload: details
    )
  end

  def from_error({kind, message, meta}, opts)
      when kind in [:pickup_no_else, :pickup_else_not_last, :pickup_multiple_else] and
             is_binary(message) and is_list(meta) do
    {code, key, title, hint} =
      case kind do
        :pickup_no_else ->
          {"E076", :pickup_missing_else, "pickup without else", "add a final `else -> ...` clause"}

        :pickup_else_not_last ->
          {"E077", :pickup_else_not_last, "pickup else is not last", "move `else -> ...` to the final clause"}

        :pickup_multiple_else ->
          {"E078", :pickup_multiple_else, "pickup has multiple else clauses", "keep exactly one `else -> ...` clause"}
      end

    Diagnostic.new(
      code: code,
      key: key,
      severity: :error,
      title: title,
      message: message,
      primary: primary(opts, hint),
      payload: %{line: Keyword.get(meta, :line), column: Keyword.get(meta, :col)}
    )
  end

  def from_error({:erased_used_relevantly, details}, opts) when is_map(details),
    do: relevance_failure(details, %{}, opts)

  def from_error({:source_context, {:erased_used_relevantly, details}, context}, opts)
      when is_map(details) and is_map(context) do
    opts =
      case Map.get(context, :span) do
        %Span{} = span -> Keyword.put_new(opts, :span, span)
        _ -> opts
      end

    relevance_failure(details, context, opts)
  end

  def from_error({:usage_violation, details}, opts) when is_map(details),
    do: usage_failure(details, %{}, opts)

  def from_error({:source_context, {:usage_violation, details}, context}, opts)
      when is_map(details) and is_map(context) do
    opts =
      case Map.get(context, :span) do
        %Span{} = span -> Keyword.put_new(opts, :span, span)
        _ -> opts
      end

    usage_failure(details, context, opts)
  end

  def from_error({:totality_required, name}, opts),
    do: totality_failure(name, %{}, opts)

  def from_error({:compile_time_totality, name, reason}, opts),
    do: totality_failure(name, %{totality_reason: reason}, opts)

  def from_error({:totality_closure_unresolved, details}, opts) when is_map(details),
    do: totality_closure_failure(details, opts)

  def from_error({kind, details}, opts)
      when kind in [
             :totality_summary_stale,
             :totality_scc_incomplete,
             :totality_scc_invalid,
             :totality_matrix_invalid,
             :totality_derivation_invalid,
             :totality_dependency_not_total,
             :totality_unknown_callee
           ] and is_map(details),
      do: totality_certificate_failure(kind, details, opts)

  def from_error({:source_context, {:totality_required, name}, context}, opts)
      when is_map(context),
      do: totality_failure(name, context, opts)

  def from_error({:source_context, {:compile_time_totality, name, reason}, context}, opts)
      when is_map(context),
      do: totality_failure(name, Map.put(context, :totality_reason, reason), opts)

  def from_error({:source_context, {:missing_branch, branch}, context}, opts)
      when is_map(context),
      do: coverage_failure(:missing_branch, branch, context, opts)

  def from_error(
        {:source_context, {:tuple_missing_branch, %{branch: branch} = details}, context},
        opts
      )
      when is_map(context),
      do: coverage_failure(:missing_branch, branch, Map.merge(context, Map.delete(details, :branch)), opts)

  def from_error({:source_context, {:reachable_impossible, branch}, context}, opts)
      when is_map(context),
      do: coverage_failure(:reachable_impossible, branch, context, opts)

  def from_error({:source_context, {:duplicate_branch, branch}, context}, opts)
      when is_map(context),
      do: coverage_failure(:duplicate_branch, branch, context, opts)

  def from_error({:source_context, {kind, detail}, context}, opts)
      when kind in [
             :nonlinear_pattern,
             :duplicate_default_pattern,
             :impossible_default_pattern,
             :unreachable_after_default_pattern
           ] and is_map(context),
      do: pattern_structure_failure(kind, detail, context, opts)

  def from_error({:source_context, {kind}, context}, opts)
      when kind in [:binary_match_needs_default, :map_match_needs_default] and is_map(context),
      do: pattern_structure_failure(kind, nil, context, opts)

  def from_error({kind, detail}, opts)
      when kind in [
             :nonlinear_pattern,
             :duplicate_default_pattern,
             :impossible_default_pattern,
             :unreachable_after_default_pattern
           ],
      do: pattern_structure_failure(kind, detail, %{}, opts)

  def from_error({kind}, opts) when kind in [:binary_match_needs_default, :map_match_needs_default],
    do: pattern_structure_failure(kind, nil, %{}, opts)

  def from_error({:unknown_erasure_class, name, class}, opts),
    do: erasure_failure(:unknown_erasure_class, %{name: name, class: class}, %{}, opts)

  def from_error({:erases_on_non_opaque, name}, opts),
    do: erasure_failure(:erases_on_non_opaque, %{name: name}, %{}, opts)

  def from_error({:source_context, {:unknown_erasure_class, name, class}, context}, opts)
      when is_map(context),
      do: erasure_failure(:unknown_erasure_class, %{name: name, class: class}, context, opts)

  def from_error({:source_context, {:erases_on_non_opaque, name}, context}, opts)
      when is_map(context),
      do: erasure_failure(:erases_on_non_opaque, %{name: name}, context, opts)

  def from_error(error, _opts), do: raise(Cure.Diagnostic.UnhandledError, error: error)

  defp erasure_failure(kind, details, context, opts) do
    {title, body, primary_message} = erasure_copy(kind, details)
    decorator_span = Map.get(context, :decorator_span) || Keyword.get(opts, :span)
    arguments = Map.get(context, :argument_spans, [])
    name_span = Map.get(context, :name_span)

    primary_span =
      case {kind, arguments} do
        {:unknown_erasure_class, [argument]} -> argument
        _ -> decorator_span
      end

    secondary =
      [
        if(decorator_span != primary_span,
          do: label(decorator_span, :secondary, "this is the complete erasure declaration")
        ),
        if(name_span != primary_span, do: label(name_span, :secondary, "this type receives the erasure declaration"))
      ]
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E102",
      key: :erasure_violation,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary: label(primary_span, :primary, primary_message),
      secondary: secondary,
      suggestions: erasure_suggestions(kind, details),
      payload: Map.put(details, :kind, kind)
    )
  end

  defp erasure_copy(:unknown_erasure_class, %{name: name, class: :missing_argument}) do
    {
      "Erasure class is missing",
      "`@erases` on `#{name_to_string(name)}` needs exactly one atom naming the runtime class of this opaque carrier.",
      "add one supported erasure class inside these parentheses"
    }
  end

  defp erasure_copy(:unknown_erasure_class, %{name: name, class: {:too_many_arguments, count}}) do
    {
      "Erasure declaration has too many classes",
      "`@erases` on `#{name_to_string(name)}` accepts one runtime class, but this declaration supplies #{count}. One opaque carrier must have one unambiguous runtime representation.",
      "keep exactly one erasure class"
    }
  end

  defp erasure_copy(:unknown_erasure_class, %{name: name, class: :not_an_atom_literal}) do
    {
      "Erasure class must be an atom",
      "`@erases` on `#{name_to_string(name)}` expects an atom such as `:pid`; a bare name is not an erasure-class declaration.",
      "write the runtime class as an atom"
    }
  end

  defp erasure_copy(:unknown_erasure_class, %{name: name, class: class}) do
    {
      "Unknown erasure class `#{name_to_string(class)}`",
      "`#{name_to_string(class)}` is not a supported runtime class for opaque type `#{name_to_string(name)}`. Supported classes: #{erasure_classes()}.",
      "this runtime class is not supported"
    }
  end

  defp erasure_copy(:erases_on_non_opaque, %{name: name}) do
    {
      "Constructed type cannot declare an erasure class",
      "`#{name_to_string(name)}` has constructors, so its runtime representation is already determined by those constructors. `@erases` is only valid on a constructor-less `opaque type`.",
      "remove this erasure declaration"
    }
  end

  defp erasure_suggestions(:unknown_erasure_class, %{class: :missing_argument}),
    do: [%Suggestion{message: "Add one of #{erasure_classes()}", applicability: :manual}]

  defp erasure_suggestions(:unknown_erasure_class, %{class: {:too_many_arguments, _}}),
    do: [%Suggestion{message: "Keep exactly one of #{erasure_classes()}", applicability: :manual}]

  defp erasure_suggestions(:unknown_erasure_class, %{class: :not_an_atom_literal}),
    do: [%Suggestion{message: "Write the class as an atom, for example `:pid`", applicability: :manual}]

  defp erasure_suggestions(:unknown_erasure_class, _details),
    do: [%Suggestion{message: "Choose one of #{erasure_classes()}", applicability: :manual}]

  defp erasure_suggestions(:erases_on_non_opaque, _details),
    do: [
      %Suggestion{message: "Remove `@erases`, or make this a constructor-less `opaque type`", applicability: :manual}
    ]

  defp erasure_classes do
    [:pid, :reference, :integer, :float, :binary, :atom, :boolean, :list]
    |> Enum.map_join(", ", &Atom.to_string/1)
  end

  defp pattern_structure_failure(kind, detail, context, opts) do
    {title, body, primary, secondary, hint} = pattern_structure_copy(kind, detail, context, opts)
    name = if is_map(detail), do: Map.get(detail, :name), else: detail

    Diagnostic.new(
      code: "E119",
      key: :pattern_structure,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary: primary || primary(opts, "fix this pattern"),
      secondary: secondary,
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{kind: kind, name: name, checking: Map.get(context, :checking)}
    )
  end

  defp pattern_structure_copy(:nonlinear_pattern, name, context, opts) do
    spelling = name_to_string(name)

    spans =
      context
      |> Map.get(:branch_patterns, [])
      |> Enum.flat_map(&(Map.get(&1, :variable_spans, %{}) |> Map.get(spelling, [])))

    secondary =
      case label(List.first(spans), :secondary, "`#{spelling}` is first bound here") do
        nil -> []
        first -> [first]
      end

    {
      "Pattern binds `#{spelling}` more than once",
      "Each name may bind only one field in a pattern. Repeating `#{spelling}` would imply an equality check that the pattern has not proved.",
      label(List.last(spans) || Keyword.get(opts, :span), :primary, "this repeats the earlier `#{spelling}` binding"),
      secondary,
      "Use a fresh name here, then compare the two values explicitly if they must be equal"
    }
  end

  defp pattern_structure_copy(:duplicate_default_pattern, _name, context, opts) do
    defaults = Enum.filter(Map.get(context, :branch_patterns, []), &(Map.get(&1, :kind) == :variable))
    first = List.first(defaults)
    duplicate = List.last(defaults)

    secondary =
      case label(branch_span(first), :secondary, "this earlier pattern already matches every remaining value") do
        nil -> []
        first_label -> [first_label]
      end

    {
      "Pattern match has more than one catch-all",
      "A variable or `_` pattern matches every value not handled above it, so a later catch-all can never be reached.",
      label(branch_span(duplicate) || Keyword.get(opts, :span), :primary, "this catch-all is unreachable"),
      secondary,
      "Keep one final catch-all branch and remove or narrow the others"
    }
  end

  defp pattern_structure_copy(:impossible_default_pattern, _name, context, opts) do
    default = Enum.find(Map.get(context, :branch_patterns, []), &(Map.get(&1, :kind) == :variable))

    {
      "Catch-all branch cannot be impossible",
      "A variable or `_` pattern accepts every remaining value, so it cannot justify an `impossible` branch.",
      label(branch_span(default) || Keyword.get(opts, :span), :primary, "this pattern is always reachable"),
      [],
      "Use constructor patterns whose indices prove impossibility, or provide a result for this catch-all"
    }
  end

  defp pattern_structure_copy(:unreachable_after_default_pattern, details, _context, opts) do
    name = details |> Map.get(:name) |> name_to_string()

    secondary =
      case label(
             Map.get(details, :default_span),
             :secondary,
             "this catch-all already accepts every remaining value as `#{name}`"
           ) do
        nil -> []
        default -> [default]
      end

    {
      "Branch appears after a catch-all",
      "No value can reach this branch because the preceding catch-all pattern already accepts every value not handled above it.",
      label(Map.get(details, :span) || Keyword.get(opts, :span), :primary, "this branch can never be reached"),
      secondary,
      "Move the catch-all to the end of the match, or narrow it to a constructor pattern"
    }
  end

  defp pattern_structure_copy(kind, _detail, context, opts)
       when kind in [:binary_match_needs_default, :map_match_needs_default] do
    subject = if kind == :binary_match_needs_default, do: "binary", else: "map"

    body =
      case kind do
        :binary_match_needs_default ->
          "Binary patterns only cover the byte and segment shapes written in their branches; other binary values can still arrive."

        :map_match_needs_default ->
          "Map patterns only constrain the entries written in their branches; maps with other key sets can still arrive."
      end

    {
      "#{String.capitalize(subject)} match needs a catch-all",
      body,
      label(insertion_span(context) || Keyword.get(opts, :span), :primary, "add a catch-all branch here"),
      [],
      "Add `_ -> ...` to handle every remaining #{subject} value"
    }
  end

  defp coverage_failure(kind, branch, context, opts) do
    branch_name = surface_name(branch)
    matching = Enum.filter(Map.get(context, :branch_patterns, []), &(Map.get(&1, :name) == branch_name))

    {title, body, primary, secondary, hint} =
      coverage_copy(kind, branch_name, matching, context, opts)

    payload =
      %{kind: kind, branch: branch, checking: Map.get(context, :checking)}
      |> maybe_put(:position, Map.get(context, :tuple_pattern_position))

    Diagnostic.new(
      code: "E118",
      key: :pattern_coverage,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary: primary || primary(opts, "fix this pattern match"),
      secondary: secondary,
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: payload
    )
  end

  defp coverage_copy(:missing_branch, branch, _matching, %{tuple_pattern_position: position} = context, _opts)
       when is_integer(position) do
    arity = Map.get(context, :tuple_pattern_arity, position)
    insertion = Map.get(context, :tuple_pattern_insertion_span) || insertion_span(context)

    secondary =
      context
      |> Map.get(:tuple_pattern_element_spans, [])
      |> Enum.map(&label(&1, :secondary, "this tuple position handles another constructor here"))
      |> Enum.reject(&is_nil/1)

    shape =
      1..arity
      |> Enum.map_join(", ", fn index -> if index == position, do: "#{branch}(...)", else: "_" end)

    {
      "Tuple pattern is missing `#{branch}` in position #{position}",
      "The value in tuple position #{position} can be `#{branch}`, but no tuple branch handles that constructor there.",
      label(
        insertion || Map.get(context, :span),
        :primary,
        "add a tuple branch with `#{branch}` in position #{position}"
      ),
      secondary,
      "Add `%[#{shape}] -> ...`, or a tuple catch-all branch"
    }
  end

  defp coverage_copy(:missing_branch, branch, _matching, context, _opts) do
    {
      "Pattern match is missing `#{branch}`",
      "This match can receive `#{branch}`, but no branch handles that constructor.",
      label(insertion_span(context) || Map.get(context, :span), :primary, "add a `#{branch}` branch here"),
      [],
      "Add a `#{branch}(...) -> ...` branch, or a catch-all branch"
    }
  end

  defp coverage_copy(:reachable_impossible, branch, matching, context, _opts) do
    {
      "`#{branch}` is reachable here",
      "This branch is marked `impossible`, but `#{branch}` can occur for the matched type and indices.",
      label(branch_span(List.first(matching)) || Map.get(context, :span), :primary, "this constructor is reachable"),
      [],
      "Replace `impossible` with a result for the `#{branch}` case"
    }
  end

  defp coverage_copy(:duplicate_branch, branch, matching, context, _opts) do
    first = List.first(matching)
    duplicate = List.last(matching)

    secondary =
      case label(branch_span(first), :secondary, "`#{branch}` is first handled here") do
        nil -> []
        first_label -> [first_label]
      end

    {
      "`#{branch}` has more than one branch",
      "Only one branch may handle each constructor. The later `#{branch}` branch can never be selected independently.",
      label(
        branch_span(duplicate) || Map.get(context, :span),
        :primary,
        "this repeats the earlier `#{branch}` branch"
      ),
      secondary,
      "Combine these `#{branch}` cases or remove the duplicate branch"
    }
  end

  defp insertion_span(context) do
    case context |> Map.get(:branch_patterns, []) |> List.last() do
      %{span: %Span{} = span} ->
        %{span | start_byte: span.end_byte, start_line: span.end_line, start_column: span.end_column}

      _ ->
        nil
    end
  end

  defp branch_span(%{pattern_span: %Span{} = span}), do: span
  defp branch_span(%{span: %Span{} = span}), do: span
  defp branch_span(_pattern), do: nil

  defp surface_name(name), do: name |> name_to_string() |> String.split("#") |> List.last()

  defp maybe_put(map, _key, value) when not is_integer(value), do: map
  defp maybe_put(map, key, value), do: Map.put(map, key, value)

  defp totality_failure(name, context, opts) do
    calls = Map.get(context, :recursive_call_spans, [])
    definition = Map.get(context, :definition_span)
    {primary, secondary} = totality_labels(calls, definition, opts)

    Diagnostic.new(
      code: "E013",
      key: :totality_failure,
      severity: :error,
      title: "Function must be total",
      body:
        Doc.paragraph(
          "`#{name_to_string(name)}` is evaluated while checking types, but the compiler cannot prove that every call to it terminates."
        ),
      primary: primary,
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Make each recursive call use a structurally smaller argument, or keep this function out of types",
          applicability: :manual
        }
      ],
      notes: totality_notes(Map.get(context, :totality_reason)),
      payload: %{
        name: name,
        checking: Map.get(context, :checking, Keyword.get(opts, :checking)),
        reason: Map.get(context, :totality_reason)
      }
    )
  end

  defp totality_notes(reason) do
    base = ["Runtime-only functions may remain partial; only compile-time computation requires a total definition."]

    case reason do
      %{reason: :not_decreasing, members: members, offending_edge: edge} ->
        path =
          edge
          |> Map.get(:source_call_path, [])
          |> Enum.map_join("; ", fn {source, target} ->
            "#{name_to_string(source)} -> #{name_to_string(target)}"
          end)

        (base ++
           [
             "Totality SCC: " <> Enum.map_join(members, ", ", &name_to_string/1),
             "Offending idempotent loop: #{name_to_string(edge.source)} -> #{name_to_string(edge.target)}; diagonal #{inspect(Map.get(edge, :diagonal, []))}",
             if(path == "", do: nil, else: "Source-call path: " <> path)
           ])
        |> Enum.reject(&is_nil/1)

      _ ->
        base
    end
  end

  defp totality_certificate_failure(kind, details, opts) do
    {title, explanation} =
      case kind do
        :totality_summary_stale ->
          {"Totality summary is stale",
           "The cached direct-call summary does not match the checked Core body or checker version."}

        :totality_scc_incomplete ->
          {"Totality component is incomplete",
           "The proposed component omitted a definition reached by a trusted direct call."}

        :totality_scc_invalid ->
          {"Totality component certificate is invalid",
           "The submitted SCC partition, rank, or connectivity witness does not match the trusted direct-call graph."}

        :totality_matrix_invalid ->
          {"Totality call matrix is invalid",
           "The submitted size-change matrix overstates or otherwise disagrees with the relation extracted from the checked Core call."}

        :totality_derivation_invalid ->
          {"Totality derivation is invalid",
           "A Base or Compose step does not replay to the submitted size-change edge, or the exact closure is incomplete."}

        :totality_dependency_not_total ->
          {"Totality dependency is not certified",
           "This component depends on another component that was not proved total, so it cannot be published as total."}

        :totality_unknown_callee ->
          {"Totality call target is unresolved",
           "A trusted direct call does not resolve to a canonical definition, builtin, or extern."}
      end

    opts =
      case Map.get(details, :source_span) do
        %Span{} = span -> Keyword.put_new(opts, :span, span)
        _ -> opts
      end

    Diagnostic.new(
      code: "E013",
      key: kind,
      severity: :error,
      title: title,
      body: Doc.paragraph(explanation),
      primary: primary(opts, "the totality certificate cannot be accepted here"),
      notes: totality_detail_notes(details),
      suggestions: [
        %Suggestion{
          message:
            "Rebuild the changed module and its totality dependencies; report this if a clean build reproduces it",
          applicability: :manual
        }
      ],
      provenance: Map.get(details, :provenance, []) |> diagnostic_provenance(),
      payload: details
    )
  end

  defp diagnostic_provenance(%{macro_expansion: frames}) when is_list(frames), do: frames
  defp diagnostic_provenance(frames) when is_list(frames), do: frames
  defp diagnostic_provenance(_other), do: []

  defp totality_detail_notes(details) do
    details
    |> Enum.sort_by(fn {key, _value} -> key end)
    |> Enum.map(fn {key, value} -> "#{key}: #{inspect(value, limit: 20, printable_limit: 200)}" end)
  end

  defp totality_closure_failure(details, opts) do
    definition = Map.fetch!(details, :definition)
    root = Map.fetch!(details, :root)
    closure_path = Map.fetch!(details, :closure_path)

    Diagnostic.new(
      code: "E013",
      key: :totality_closure_unresolved,
      severity: :error,
      title: "Totality dependency does not resolve",
      body:
        Doc.paragraph(
          "`#{name_to_string(root)}` must be certified for compile-time evaluation, but its dependency `#{name_to_string(definition)}` does not resolve to a definition, builtin, or extern."
        ),
      primary: primary(opts, "this compile-time dependency cannot be certified"),
      notes: [
        "Closure path: " <> Enum.map_join(closure_path, " -> ", &name_to_string/1)
      ],
      suggestions: [
        %Suggestion{
          message: "Define or import the missing function, and keep every compile-time dependency canonical",
          applicability: :manual
        }
      ],
      payload: %{
        definition: definition,
        root: root,
        closure_path: closure_path
      }
    )
  end

  defp totality_labels([first | rest], definition, _opts) do
    primary =
      label(first, :primary, "this recursive call participates in an unproven termination cycle")

    calls =
      Enum.map(rest, &label(&1, :secondary, "another recursive call in this cycle is here"))

    owner =
      label(definition, :secondary, "this type-level function must terminate on every input")

    {primary, Enum.reject(calls ++ [owner], &is_nil/1)}
  end

  defp totality_labels([], _definition, opts) do
    {primary(opts, "this definition is used in a type and must always terminate"), []}
  end

  defp relevance_failure(details, context, opts) do
    site = Map.get(details, :site, :runtime)
    binder = Map.get(details, :binder)
    binder_name = Map.get(context, :binder_name)

    subject =
      cond do
        is_binary(binder_name) -> "The erased parameter `#{binder_name}`"
        is_atom(binder_name) and not is_nil(binder_name) -> "The erased parameter `#{binder_name}`"
        is_nil(binder) -> "An erased value"
        true -> "Erased binder #{binder}"
      end

    secondary =
      case label(
             Map.get(context, :binder_span),
             :secondary,
             "`#{binder_name || "this value"}` is erased here"
           ) do
        nil -> []
        label -> [label]
      end

    Diagnostic.new(
      code: "E104",
      key: :erased_value_used_relevantly,
      severity: :error,
      title: "Erased value used relevantly",
      body:
        Doc.paragraph("#{subject} is used as #{site_description(site)}, but erased parameters do not exist at runtime."),
      primary: primary(opts, primary_message(site)),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: suggestion(binder_name),
          applicability: :manual
        }
      ],
      payload: details
    )
  end

  defp usage_failure(details, context, opts) do
    declared = Map.get(details, :declared, :unknown)
    used = Map.get(details, :used, :unknown)
    binder = Map.get(details, :binder)
    binder_name = Map.get(context, :binder_name)
    display_name = if binder_name, do: "`#{binder_name}`", else: "A binding"

    {title, body, primary_message, hint} =
      usage_copy(display_name, binder_name, declared, used, Map.get(context, :use_spans, []))

    primary_span = Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E117",
      key: :resource_usage_violation,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary: primary(opts, primary_message),
      secondary: usage_secondary_labels(context, primary_span, declared, used),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: Map.put(details, :binder_name, binder_name || binder)
    )
  end

  defp usage_copy(name, binder_name, :linear, :erased, _uses) do
    action_name = usage_action_name(name, binder_name)

    {
      "Linear value is not used",
      "#{name} is linear, so every path through this function must use it exactly once. This function does not use it.",
      "this linear parameter must be used exactly once",
      "Use #{action_name} once on every path, or declare it `@affine` if it may be dropped"
    }
  end

  defp usage_copy(name, binder_name, :linear, :unrestricted, uses) do
    action_name = usage_action_name(name, binder_name)

    body =
      if length(uses) > 1 do
        "#{name} is linear, but this path can use it more than once. A linear value must be consumed exactly once."
      else
        "#{name} is linear, but this use passes it to a context that may consume it any number of times."
      end

    {
      "Linear value may be used more than once",
      body,
      "this use does not preserve linear ownership",
      "Pass #{action_name} only to linear parameters, and consume it exactly once on every path"
    }
  end

  defp usage_copy(name, binder_name, :affine, :unrestricted, uses) do
    action_name = usage_action_name(name, binder_name)

    body =
      if length(uses) > 1 do
        "#{name} is affine, but this path can use it more than once. An affine value may be used once or not at all."
      else
        "#{name} is affine, but this use passes it to a context that may consume it any number of times."
      end

    {
      "Affine value may be used more than once",
      body,
      "this use does not preserve affine ownership",
      "Pass #{action_name} only to affine or linear parameters, and use it at most once"
    }
  end

  defp usage_copy(name, binder_name, declared, used, _uses) do
    action_name = usage_action_name(name, binder_name)

    {
      "Resource usage violates its grade",
      "#{name} is declared `#{declared}` but its inferred usage is `#{used}`.",
      "this use is incompatible with the declared resource grade",
      "Use #{action_name} according to its declared `#{declared}` grade"
    }
  end

  defp usage_action_name(name, binder_name) when not is_nil(binder_name), do: name
  defp usage_action_name(_name, _binder_name), do: "the binding"

  defp usage_secondary_labels(context, primary_span, declared, :erased) do
    [
      label(
        Map.get(context, :grade_span),
        :secondary,
        "this parameter is declared `#{declared}` here"
      )
    ]
    |> Enum.reject(&is_nil/1)
    |> Enum.reject(&same_span?(&1.span, primary_span))
  end

  defp usage_secondary_labels(context, primary_span, declared, _used) do
    binder =
      label(
        Map.get(context, :binder_span),
        :secondary,
        "this parameter is declared `#{declared}` here"
      )

    earlier_uses =
      context
      |> Map.get(:use_spans, [])
      |> Enum.reject(&same_span?(&1, primary_span))
      |> Enum.map(&label(&1, :secondary, "another use on this path is here"))

    [binder | earlier_uses] |> Enum.reject(&is_nil/1)
  end

  defp same_span?(%Span{} = left, %Span{} = right) do
    left.start_byte == right.start_byte and left.end_byte == right.end_byte and
      left.start_line == right.start_line and left.end_line == right.end_line
  end

  defp same_span?(_left, _right), do: false

  defp primary_message(:returned), do: "this returns an erased value at runtime"
  defp primary_message(:present_arg), do: "this passes an erased value to a runtime argument"
  defp primary_message(:scrutinee), do: "this match inspects an erased value at runtime"
  defp primary_message(:applied), do: "this applies an erased value as a runtime function"
  defp primary_message(_site), do: "this uses an erased value at runtime"

  defp site_description(:returned), do: "the function's runtime result"
  defp site_description(:present_arg), do: "an argument that exists at runtime"
  defp site_description(:scrutinee), do: "the value inspected by a runtime match"
  defp site_description(:applied), do: "a function called at runtime"
  defp site_description(_site), do: "a value needed at runtime"

  defp suggestion(name) when is_binary(name) or (is_atom(name) and not is_nil(name)),
    do: "Declare `#{name}` as a runtime parameter, or keep it out of runtime expressions"

  defp suggestion(_name),
    do: "Use a runtime parameter here, or keep the erased value out of runtime expressions"

  defp primary(opts, message) do
    case Keyword.get(opts, :span) do
      %Span{} = span -> %Label{span: span, style: :primary, message: Keyword.get(opts, :label, message)}
      _ -> nil
    end
  end

  defp pickup_spans(spans), do: Enum.filter(spans, &match?(%Span{}, &1))

  defp pickup_label(%Span{} = span, style, message), do: %Label{span: span, style: style, message: message}
  defp pickup_label(_, _style, _message), do: nil

  defp label(%Span{} = span, style, message), do: %Label{span: span, style: style, message: message}
  defp label(_, _style, _message), do: nil

  defp name_to_string(name) when is_atom(name), do: Atom.to_string(name)
  defp name_to_string(name) when is_binary(name), do: name
  defp name_to_string(name), do: inspect(name)
end
