defmodule Cure.Diagnostic.Adapter.Pattern do
  @moduledoc "Owns contextual unsupported-pattern diagnostics."

  alias Cure.Diagnostic
  alias Cure.Diagnostic.{Doc, Label, Span, Suggestion}

  def named_default_nonvariable_failure(details, context, opts) do
    name = name_to_string(details.name)
    pattern_span = Map.get(details, :span)
    scrutinee_span = Map.get(details, :type_span) || Map.get(context, :scrutinee_span)
    primary_span = pattern_span || Map.get(context, :span) || Keyword.get(opts, :span)

    secondary =
      case label(scrutinee_span, :secondary, "this expression has no existing name for the catch-all to bind") do
        nil -> []
        related -> [related]
      end

    Diagnostic.new(
      code: "E090",
      key: :unrecognized_pattern,
      severity: :error,
      title: "Catch-all `#{name}` needs a stable value",
      body:
        Doc.paragraph(
          "This named catch-all must refer to the complete matched value, but the match scrutinizes an expression directly. Bind that expression once before matching so `#{name}` has an unambiguous value."
        ),
      primary: label(primary_span, :primary, "this catch-all needs the complete matched value"),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Bind the matched expression with `let`, then match the new name",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :unsupported_pattern,
        reason: :named_default_nonvariable,
        name: name,
        checking: Map.get(context, :checking)
      }
    )
  end

  def with_default_pattern_failure(details, context, opts) do
    name = name_to_string(details.name)
    branches = Map.get(context, :branch_patterns, [])

    default =
      Enum.find(branches, fn branch ->
        Map.get(branch, :kind) == :variable and Map.get(branch, :name) == name
      end)

    span =
      Map.get(details, :span) ||
        (default && (Map.get(default, :pattern_span) || Map.get(default, :span))) ||
        Map.get(context, :span) || Keyword.get(opts, :span)

    constructor_labels =
      branches
      |> Enum.filter(&(Map.get(&1, :kind) == :constructor))
      |> Enum.map(&(Map.get(&1, :pattern_span) || Map.get(&1, :span)))
      |> Enum.map(&label(&1, :secondary, "this branch refines a constructor"))
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E090",
      key: :unrecognized_pattern,
      severity: :error,
      title: "`with` needs constructor branches",
      body:
        Doc.paragraph(
          "The catch-all pattern `#{name}` does not identify a constructor, so it cannot refine the matched value or any dependent types. A `with` branch must restate one concrete constructor."
        ),
      primary: label(span, :primary, "replace this catch-all with a constructor pattern"),
      secondary: constructor_labels,
      suggestions: [
        %Suggestion{
          message: "Add the remaining constructor branches explicitly, or use `match` when no refinement is needed",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :unsupported_pattern,
        reason: :default_in_with,
        name: name,
        checking: Map.get(context, :checking)
      }
    )
  end

  def unlowered_nested_constructor_failure(details, context, opts) do
    shape = details |> Map.get(:shape, :pattern) |> name_to_string()
    span = Map.get(details, :span) || Map.get(context, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E090",
      key: :unrecognized_pattern,
      severity: :error,
      title: "Nested constructor pattern could not be lowered",
      body:
        Doc.paragraph(
          "This nested `#{shape}` pattern reached a context that only accepts direct constructor binders. Split the nested test into a second match so each constructor is checked at its own level."
        ),
      primary: label(span, :primary, "move this nested pattern into a second match"),
      suggestions: [
        %Suggestion{
          message: "Bind this constructor field to a name, then match that name in the branch body",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :unsupported_pattern,
        reason: :unlowered_nested_constructor_argument,
        shape: shape,
        checking: Map.get(context, :checking)
      }
    )
  end

  defp label(%Span{} = span, style, message), do: %Label{span: span, style: style, message: message}
  defp label(_span, _style, _message), do: nil
  defp name_to_string(name) when is_atom(name), do: Atom.to_string(name)
  defp name_to_string(name) when is_binary(name), do: name
  defp name_to_string(name), do: inspect(name)
end
