defmodule Cure.Diagnostic.Adapter.Declaration do
  @moduledoc "Owns declaration-shape diagnostics for foreign declarations."

  alias Cure.Diagnostic
  alias Cure.Diagnostic.{Doc, Label, Span, Suggestion, TextEdit}

  @spec from_error(term(), keyword()) :: Diagnostic.t()
  def from_error(error, opts \\ [])

  def from_error({:extern_untyped_head, message, meta}, opts) when is_binary(message) and is_list(meta) do
    Diagnostic.new(
      code: "E056",
      key: :extern_untyped_head,
      severity: :error,
      title: "@extern declaration missing a typed head",
      message: message,
      primary: primary_label(opts, "add parameter and return type annotations"),
      payload: %{line: Keyword.get(meta, :line), column: Keyword.get(meta, :col)}
    )
  end

  def from_error({:extern_has_body, message, meta}, opts) when is_binary(message) and is_list(meta) do
    Diagnostic.new(
      code: "E057",
      key: :extern_has_body,
      severity: :error,
      title: "@extern declaration has a body",
      message: message,
      primary: primary_label(opts, "remove the body from this extern declaration"),
      payload: %{line: Keyword.get(meta, :line), column: Keyword.get(meta, :col)}
    )
  end

  def primitive_declaration_failure(kind, details, context, opts) do
    name = Map.get(details, :name) || Map.get(context, :primitive)
    tag = Map.get(details, :tag) || Map.get(context, :builtin_tag)
    {title, body, primary_message, hint} = primitive_content(kind, name, tag, details)
    primary_span = Map.get(context, :span) || Keyword.get(opts, :span)

    secondary =
      case {kind, Map.get(context, :name_span)} do
        {kind, %Span{} = span} when kind in [:unknown_builtin, :floor_mismatch] and span != primary_span ->
          [%Label{span: span, style: :secondary, message: "this is the primitive declaration being validated"}]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E120",
      key: :primitive_declaration,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary: primary(Keyword.put(opts, :span, primary_span), primary_message),
      secondary: secondary,
      suggestions: primitive_suggestions(kind, details, context, hint),
      payload: %{
        kind: kind,
        name: name,
        tag: tag,
        declared: Map.get(details, :declared),
        expected: Map.get(details, :expected),
        shape: Map.get(details, :shape)
      }
    )
  end

  defp primitive_content(:missing_builtin, name, _tag, _details) do
    {"Primitive declaration needs a builtin tag",
     "`#{name_to_string(name)}` is declared as a primitive, but it has no `@builtin(...)` marker. The marker tells the compiler which runtime primitive representation this name denotes.",
     "add a `@builtin(...)` marker for this primitive",
     "Add one of `@builtin(:float)`, `@builtin(:binary)`, or `@builtin(:atom)` before this declaration"}
  end

  defp primitive_content(:unknown_builtin, _name, tag, _details) do
    {"`#{primitive_tag(tag)}` is not a primitive builtin",
     "The compiler has no primitive representation named `#{primitive_tag(tag)}`. Primitive declarations may currently use only `:float`, `:binary`, or `:atom`.",
     "this builtin tag is not recognized",
     "Use `:float`, `:binary`, or `:atom`, or declare an ordinary Cure type instead"}
  end

  defp primitive_content(:floor_mismatch, name, _tag, details) do
    declared = primitive_tag(Map.get(details, :declared))
    expected = primitive_tag(Map.get(details, :expected))

    {"`#{name_to_string(name)}` has the wrong primitive builtin",
     "`#{name_to_string(name)}` is part of the compiler's primitive floor and denotes `#{expected}`, but this declaration marks it as `#{declared}`. Those representations are not interchangeable.",
     "replace this tag with `#{expected}`", "Change the marker to `@builtin(#{expected})`"}
  end

  defp primitive_content(:unsupported_declaration, _name, _tag, details) do
    shape = details |> Map.get(:shape) |> name_to_string()

    {"Declaration form is not supported",
     "The elaborator received a `#{shape}` declaration form that this compiler does not support. If a macro generated this declaration, its expansion must use a supported declaration node.",
     "this declaration cannot be elaborated",
     "Rewrite this as a supported function, type, interface, implementation, or primitive declaration"}
  end

  defp primitive_suggestions(:floor_mismatch, details, context, hint) do
    case {Map.get(context, :builtin_argument_span), Map.get(details, :expected)} do
      {%Span{} = span, tag} when is_atom(tag) ->
        [
          %Suggestion{
            message: hint,
            applicability: :machine_applicable,
            edits: [%TextEdit{span: span, replacement: primitive_tag(tag)}]
          }
        ]

      _ ->
        [%Suggestion{message: hint, applicability: :manual}]
    end
  end

  defp primitive_suggestions(_kind, _details, _context, hint), do: [%Suggestion{message: hint, applicability: :manual}]

  defp primitive_tag({:float_type}), do: ":float"
  defp primitive_tag({:binary_type}), do: ":binary"
  defp primitive_tag({:atom_type}), do: ":atom"
  defp primitive_tag(tag) when is_atom(tag), do: ":#{tag}"
  defp primitive_tag(tag), do: name_to_string(tag)

  defp primary(opts, message) do
    case Keyword.get(opts, :span) do
      %Span{} = span -> %Label{span: span, style: :primary, message: Keyword.get(opts, :label, message)}
      nil -> nil
    end
  end

  defp name_to_string(name) when is_atom(name), do: Atom.to_string(name)
  defp name_to_string(name) when is_binary(name), do: name
  defp name_to_string(name), do: inspect(name)

  defp primary_label(opts, default_message) do
    case Keyword.get(opts, :span) do
      %Span{} = span -> %Label{span: span, style: :primary, message: Keyword.get(opts, :label, default_message)}
      nil -> nil
    end
  end
end
