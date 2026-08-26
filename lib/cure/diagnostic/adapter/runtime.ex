defmodule Cure.Diagnostic.Adapter.Runtime do
  @moduledoc "Converts runtime-capability failures found while elaborating dependent code."

  alias Cure.Diagnostic
  alias Cure.Diagnostic.{Doc, Label, Span, Suggestion}

  @spec from_error(term(), keyword()) :: Diagnostic.t()
  def from_error({:unsupported_async, message, _meta}, opts) when is_binary(message) do
    Diagnostic.new(
      code: "E107",
      key: :unsupported_async,
      severity: :error,
      title: "Unsupported asynchronous primitive",
      body: Doc.paragraph(message),
      primary: primary(opts, "use a supported asynchronous boundary"),
      payload: %{primitive: :unknown, stage: :runtime}
    )
  end

  def from_error({:unsupported_async, %{primitive: primitive} = details}, opts) do
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E107",
      key: :unsupported_async,
      severity: :error,
      title: "`#{name(primitive)}` is unavailable in dependent code",
      body:
        Doc.paragraph(
          "The dependent runtime cannot lower `#{name(primitive)}` while preserving Cure's checked process and message types. This is a runtime capability boundary, not a type error in the spawned expression."
        ),
      primary: label(span, "this asynchronous operation has no dependent-runtime lowering"),
      suggestions: [
        %Suggestion{
          message: "Use an actor, FSM, or supervisor declaration for managed concurrency",
          applicability: :manual
        }
      ],
      payload: %{
        primitive: primitive,
        stage: Map.get(details, :stage, :dependent_runtime),
        capability: :managed_concurrency
      }
    )
  end

  defp primary(opts, message), do: label(Keyword.get(opts, :span), message)

  defp label(%Span{} = span, message), do: %Label{span: span, style: :primary, message: message}
  defp label(_span, _message), do: nil

  defp name(value) when is_atom(value), do: Atom.to_string(value)
  defp name(value) when is_binary(value), do: value
  defp name(value), do: inspect(value)
end
