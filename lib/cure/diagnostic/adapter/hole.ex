defmodule Cure.Diagnostic.Adapter.Hole do
  @moduledoc "Owns ordinary hole and hole-inference-position diagnostics."

  alias Cure.Diagnostic
  alias Cure.Diagnostic.{Doc, Label, Span, Suggestion}
  alias Cure.Elab.Name

  @spec from_error(term(), keyword()) :: Diagnostic.t()
  def from_error(error, opts \\ [])

  def from_error({:unfilled_hole, details}, opts) when is_map(details) do
    opts = Keyword.put_new(opts, :span, Map.get(details, :span))
    primary = primary_label(opts, "replace this hole with an expression")

    secondary =
      case {Map.get(details, :annotation_span), primary} do
        {%Span{} = span, %Label{span: primary_span}} when span != primary_span ->
          [%Label{span: span, style: :secondary, message: "this function's result type is declared here"}]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E014",
      key: :unfilled_hole,
      severity: :error,
      title: "Unfilled hole",
      body: Doc.paragraph("The definition `#{name_to_string(details.definition)}` still contains an unfinished hole."),
      primary: primary,
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Replace the hole with an expression that satisfies its surrounding type",
          applicability: :manual
        }
      ],
      payload: details
    )
  end

  def from_error({:unfilled_hole, name}, opts) do
    Diagnostic.new(
      code: "E014",
      key: :unfilled_hole,
      severity: :error,
      title: "Unfilled hole",
      body: Doc.paragraph("The compiler reached the unfinished hole `?#{name}`."),
      primary: primary_label(opts, "replace this hole with an expression"),
      payload: %{name: name}
    )
  end

  def inferred_failure(name, context, opts) do
    opts =
      case Map.get(context, :span) do
        %Span{} = span -> Keyword.put_new(opts, :span, span)
        _ -> opts
      end

    Diagnostic.new(
      code: "E014",
      key: :unfilled_hole,
      severity: :error,
      title: "Hole needs a type annotation",
      body:
        Doc.paragraph(
          "Cure cannot infer what this hole should contain because the surrounding definition has no declared result type."
        ),
      primary: primary_label(opts, "this hole has no expected type"),
      suggestions: [
        %Suggestion{
          message: "Declare the result type after `->`, then replace the hole with an expression of that type",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :inference_position,
        name: name,
        checking: Map.get(context, :checking, Keyword.get(opts, :checking))
      }
    )
  end

  defp primary_label(opts, default_message) do
    case Keyword.get(opts, :span) do
      %Span{} = span -> %Label{span: span, style: :primary, message: Keyword.get(opts, :label, default_message)}
      nil -> nil
    end
  end

  defp name_to_string(name) when is_atom(name), do: Name.base(name) || Atom.to_string(name)
  defp name_to_string(name) when is_binary(name), do: name
  defp name_to_string(name), do: inspect(name)
end
