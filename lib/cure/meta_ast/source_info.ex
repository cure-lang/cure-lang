defmodule Cure.MetaAST.SourceInfo do
  @moduledoc "Canonical authored source roles carried by a MetaAST node."

  alias Cure.Diagnostic.{ProvenanceFrame, Span}

  defstruct whole: nil,
            name: nil,
            callee: nil,
            operator: nil,
            operands: [],
            arguments: [],
            argument_labels: [],
            annotation: nil,
            body: nil,
            condition: nil,
            then_branch: nil,
            else_branch: nil,
            pattern: nil,
            guard: nil,
            branches: [],
            fields: %{},
            decorators: %{},
            opener: nil,
            closer: nil,
            provenance: []

  @type span_or_nil :: Span.t() | nil
  @type t :: %__MODULE__{
          whole: span_or_nil(),
          name: span_or_nil(),
          callee: span_or_nil(),
          operator: span_or_nil(),
          operands: [Span.t()],
          arguments: [Span.t()],
          argument_labels: [Span.t() | nil],
          annotation: span_or_nil(),
          body: span_or_nil(),
          condition: span_or_nil(),
          then_branch: span_or_nil(),
          else_branch: span_or_nil(),
          pattern: span_or_nil(),
          guard: span_or_nil(),
          branches: [Span.t()],
          fields: %{optional(term()) => Span.t()},
          decorators: %{
            optional(String.t()) => %{whole: span_or_nil(), name: span_or_nil(), arguments: [Span.t()]}
          },
          opener: span_or_nil(),
          closer: span_or_nil(),
          provenance: [ProvenanceFrame.t()]
        }
end
