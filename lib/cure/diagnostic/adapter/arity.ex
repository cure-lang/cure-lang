defmodule Cure.Diagnostic.Adapter.Arity do
  @moduledoc "Owns arity diagnostics for calls, constructors, patterns, and tuples."

  alias Cure.Diagnostic
  alias Cure.Diagnostic.{Doc, Label, Span, Suggestion}

  @spec from_error(term(), keyword()) :: Diagnostic.t()
  def from_error(error, opts \\ [])

  def from_error({:arity_mismatch, message, meta}, opts) when is_binary(message) and is_list(meta) do
    Diagnostic.new(
      code: "E003",
      key: :arity_mismatch,
      severity: :error,
      title: "Arity mismatch",
      message: message,
      primary: primary_label(opts, "the number of arguments does not match"),
      payload: %{line: Keyword.get(meta, :line), column: Keyword.get(meta, :col)}
    )
  end

  def from_error({:extern_arity_mismatch, name, declared, present}, opts)
      when is_integer(declared) and is_integer(present),
      do: from_error({:extern_arity_mismatch, %{name: name, declared: declared, present: present}}, opts)

  def from_error({:call_arity_mismatch, %{name: name, expected: expected, actual: actual} = details}, opts)
      when is_integer(expected) and is_integer(actual) do
    difference = abs(expected - actual)

    {label, hint} =
      if actual < expected do
        {"add #{argument_count(difference)} to this call",
         "Supply the remaining #{argument_count(difference)}, or use this partial application where a function is expected."}
      else
        {"remove #{argument_count(difference)} from this call",
         "Remove the extra #{argument_count(difference)}, or call the returned function separately if that was intended."}
      end

    Diagnostic.new(
      code: "E003",
      key: :arity_mismatch,
      severity: :error,
      title: "Function arity mismatch",
      body:
        Doc.paragraph(
          "`#{name_to_string(name)}` accepts #{argument_count(expected)}, but this call supplies #{argument_count(actual)}."
        ),
      primary: primary_label(opts, label),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: Map.put(details, :kind, :function)
    )
  end

  def from_error({:extern_arity_mismatch, %{name: name, declared: declared, present: present} = details}, opts)
      when is_integer(declared) and is_integer(present) do
    opts = Keyword.put_new(opts, :span, Map.get(details, :span))

    Diagnostic.new(
      code: "E003",
      key: :arity_mismatch,
      severity: :error,
      title: "Arity mismatch",
      body:
        Doc.paragraph(
          "Extern `#{name_to_string(name)}` declares target arity #{declared}, but its present Cure arity is #{present}."
        ),
      primary:
        primary_label(
          opts,
          "change this target arity to #{present} so it matches the values present at runtime"
        ),
      suggestions: [
        %Suggestion{
          message: "Use target arity #{present}; erased parameters do not cross the FFI boundary.",
          applicability: :manual
        }
      ],
      payload:
        details
        |> Map.put(:name, name_to_string(name))
        |> Map.put(:kind, :extern)
    )
  end

  def from_error({:constructor_arity_mismatch, %{name: name} = details}, opts) do
    expected = Map.get(details, :expected)
    actual = Map.get(details, :actual)
    display_name = Map.get(details, :display_name) || name_to_string(name)

    Diagnostic.new(
      code: "E003",
      key: :arity_mismatch,
      severity: :error,
      title: "Constructor arity mismatch",
      body:
        Doc.paragraph(
          "Constructor `#{display_name}` requires #{argument_count(expected)}, but this call supplies #{argument_count(actual)}."
        ),
      primary: primary_label(opts, constructor_arity_label(expected, actual)),
      payload: Map.put(details, :kind, :constructor) |> Map.put(:constructor, display_name)
    )
  end

  def from_error({:constructor_arity_mismatch, name}, opts),
    do: from_error({:constructor_arity_mismatch, %{name: name}}, opts)

  def from_error(
        {:pattern_arity_mismatch, %{constructor: constructor, expected: expected, actual: actual} = details},
        opts
      ) do
    opts = Keyword.put(opts, :span, Map.get(details, :span))
    difference = abs(expected - actual)
    display_name = Map.get(details, :display_name) || name_to_string(constructor)

    {label, hint} =
      if actual < expected do
        {"add #{argument_count(difference)} to this pattern",
         "Bind the remaining constructor field#{if difference == 1, do: "", else: "s"}, or use `_` for fields you do not need."}
      else
        {"remove #{argument_count(difference)} from this pattern",
         "Remove the extra pattern field#{if difference == 1, do: "", else: "s"}; this constructor does not contain them."}
      end

    Diagnostic.new(
      code: "E003",
      key: :arity_mismatch,
      severity: :error,
      title: "Pattern arity mismatch",
      body:
        Doc.paragraph(
          "Constructor `#{display_name}` has #{argument_count(expected)}, but this pattern matches #{argument_count(actual)}."
        ),
      primary: primary_label(opts, label),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: Map.put(details, :kind, :pattern)
    )
  end

  def from_error({:tuple_arity_mismatch, expected, actual}, opts)
      when is_integer(expected) and is_integer(actual) do
    difference = abs(expected - actual)

    {label, hint} =
      if actual < expected do
        {"add #{argument_count(difference)} to this tuple pattern",
         "Add #{argument_count(difference)} to match all #{expected} tuple elements; use `_` for values you do not need."}
      else
        {"remove #{argument_count(difference)} from this tuple pattern",
         "Remove #{argument_count(difference)}; this value has only #{argument_count(expected)}."}
      end

    Diagnostic.new(
      code: "E003",
      key: :arity_mismatch,
      severity: :error,
      title: "Tuple pattern has the wrong size",
      body:
        Doc.paragraph("This value has #{argument_count(expected)}, but the pattern contains #{argument_count(actual)}."),
      primary: primary_label(opts, label),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{kind: :tuple_pattern, expected: expected, actual: actual}
    )
  end

  def from_error({:tuple_arity_mismatch, direction, details}, opts) do
    Diagnostic.new(
      code: "E003",
      key: :arity_mismatch,
      severity: :error,
      title: "Tuple arity mismatch",
      body: Doc.paragraph("This tuple pattern has the wrong number of elements (#{direction})."),
      primary: primary_label(opts, "make the tuple pattern match the value's arity"),
      payload: %{kind: :tuple, direction: direction, details: details}
    )
  end

  def from_error({:with_rematch_arity_mismatch, expected, actual}, opts) do
    Diagnostic.new(
      code: "E003",
      key: :arity_mismatch,
      severity: :error,
      title: "With-pattern arity mismatch",
      body: Doc.paragraph("The original `with` match has #{expected} pattern(s), but its rematch has #{actual}."),
      primary: primary_label(opts, "keep the rematched patterns aligned with the original values"),
      payload: %{kind: :with_rematch, expected: expected, actual: actual}
    )
  end

  def from_error({:typed_pattern_arity, position}, opts),
    do: typed_pattern_arity_legacy_failure(position, opts)

  @doc false
  def typed_pattern_arity_failure(context, opts) do
    constructor = surface_declaration_name(Map.get(context, :constructor, :constructor))
    binder = name_to_string(Map.get(context, :binder, "field"))
    supplied = Map.get(context, :supplied_arity, 0)
    accepted = Map.get(context, :visible_arity, 0)
    argument_index = Map.get(context, :argument_index, accepted)
    primary_span = Map.get(context, :typed_pattern_span) || Map.get(context, :span) || Keyword.get(opts, :span)

    secondary =
      case Map.get(context, :constructor_name_span) do
        %Span{} = span when span != primary_span ->
          [
            %Label{
              span: span,
              style: :secondary,
              message: "`#{constructor}` accepts #{count_phrase(accepted, "visible field")}"
            }
          ]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E003",
      key: :arity_mismatch,
      severity: :error,
      title: "`#{constructor}` pattern has #{count_phrase(supplied, "field")}, but the constructor has #{accepted}",
      body:
        Doc.paragraph(
          "`#{binder}` is field #{argument_index + 1} in this pattern, but `#{constructor}` exposes only #{count_phrase(accepted, "field")} to match. The pattern cannot bind a field that the constructor does not contain."
        ),
      primary: label(primary_span, :primary, "this extra field has no matching position in `#{constructor}`"),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Remove the extra field, or use a constructor with #{count_phrase(supplied, "visible field")}",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :typed_pattern_arity,
        constructor: constructor,
        binder: binder,
        argument_index: argument_index,
        supplied_arity: supplied,
        visible_arity: accepted,
        checking: Map.get(context, :checking, :pattern)
      }
    )
  end

  defp typed_pattern_arity_legacy_failure(position, opts) do
    Diagnostic.new(
      code: "E003",
      key: :arity_mismatch,
      severity: :error,
      title: "Pattern arity mismatch",
      body: Doc.paragraph("This typed pattern has the wrong number of elements at position #{position}."),
      primary: primary_label(opts, "make the pattern arity match the value"),
      payload: %{kind: :typed_pattern, position: position}
    )
  end

  defp primary_label(opts, default_message) do
    case Keyword.get(opts, :span) do
      %Span{} = span -> %Label{span: span, style: :primary, message: Keyword.get(opts, :label, default_message)}
      nil -> nil
    end
  end

  defp argument_count(1), do: "1 argument"
  defp argument_count(count) when is_integer(count), do: "#{count} arguments"
  defp argument_count(_count), do: "a different number of arguments"

  defp constructor_arity_label(expected, actual) when is_integer(expected) and is_integer(actual) and actual < expected,
    do: "add #{argument_count(expected - actual)} to this constructor call"

  defp constructor_arity_label(expected, actual) when is_integer(expected) and is_integer(actual) and actual > expected,
    do: "remove #{argument_count(actual - expected)} from this constructor call"

  defp constructor_arity_label(_expected, _actual), do: "provide the arguments required by this constructor"

  defp surface_declaration_name(name), do: name |> name_to_string() |> String.split("#") |> List.last()

  defp plural(1, singular), do: singular
  defp plural(_count, singular), do: singular <> "s"
  defp count_phrase(count, singular), do: "#{count} #{plural(count, singular)}"

  defp label(%Span{} = span, style, message), do: %Label{span: span, style: style, message: message}
  defp label(_span, _style, _message), do: nil

  defp name_to_string(name) when is_atom(name), do: Atom.to_string(name)
  defp name_to_string(name) when is_binary(name), do: name
  defp name_to_string(name), do: inspect(name)
end
