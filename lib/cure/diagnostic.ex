defmodule Cure.Diagnostic.Span do
  @moduledoc "A half-open UTF-8 source range. Byte offsets are authoritative."

  @enforce_keys [:source_id, :start_byte, :end_byte, :start_line, :start_column, :end_line, :end_column]
  defstruct [:source_id, :path, :start_byte, :end_byte, :start_line, :start_column, :end_line, :end_column]

  @type t :: %__MODULE__{
          source_id: term(),
          path: String.t() | nil,
          start_byte: non_neg_integer(),
          end_byte: non_neg_integer(),
          start_line: pos_integer(),
          start_column: pos_integer(),
          end_line: pos_integer(),
          end_column: pos_integer()
        }

  @spec new(keyword()) :: t()
  def new(attrs) do
    span = struct!(__MODULE__, attrs)

    if span.end_byte < span.start_byte do
      raise ArgumentError, "diagnostic span ends before it starts"
    end

    span
  end
end

defmodule Cure.Diagnostic.Label do
  @moduledoc false
  @enforce_keys [:span, :style]
  defstruct [:span, :message, :style]
  @type t :: %__MODULE__{span: Cure.Diagnostic.Span.t(), message: String.t() | nil, style: :primary | :secondary}
end

defmodule Cure.Diagnostic.ProvenanceFrame do
  @moduledoc "One step in the expansion/desugaring origin chain."
  @enforce_keys [:kind, :name]
  defstruct [:kind, :name, :invocation, :definition, :generated, :parent]

  @type t :: %__MODULE__{
          kind: :source | :desugaring | :macro_expansion | :generated_declaration,
          name: String.t() | atom(),
          invocation: Cure.Diagnostic.Span.t() | nil,
          definition: Cure.Diagnostic.Span.t() | nil,
          generated: Cure.Diagnostic.Span.t() | String.t() | nil,
          parent: term() | nil
        }
end

defmodule Cure.Diagnostic.TextEdit do
  @moduledoc false
  @enforce_keys [:span, :replacement]
  defstruct [:span, :replacement]
  @type t :: %__MODULE__{span: Cure.Diagnostic.Span.t(), replacement: String.t()}
end

defmodule Cure.Diagnostic.Suggestion do
  @moduledoc false
  @enforce_keys [:message, :applicability]
  defstruct [:message, :applicability, edits: []]

  @type t :: %__MODULE__{
          message: String.t(),
          applicability: :machine_applicable | :maybe_incorrect | :manual,
          edits: [Cure.Diagnostic.TextEdit.t()]
        }
end

defmodule Cure.Diagnostic.UnhandledError do
  @moduledoc "Raised in development when a domain error lacks an explicit diagnostic converter."
  defexception [:error]

  @impl true
  def message(%__MODULE__{error: error}) do
    "domain error has no registered diagnostic conversion: #{inspect(error)}"
  end
end

defmodule Cure.Diagnostic do
  @moduledoc """
  Shared compiler diagnostic consumed by terminal, JSON, and editor adapters.

  Compiler algorithms may retain phase-specific error values. They cross a
  presentation boundary by being converted to this structure; rendering never
  reconstructs semantic information from prose.
  """

  alias Cure.Diagnostic.{Doc, Label, ProvenanceFrame, Suggestion}

  @enforce_keys [:code, :key, :severity, :title, :body]
  defstruct [
    :code,
    :key,
    :severity,
    :title,
    :body,
    :primary,
    secondary: [],
    notes: [],
    suggestions: [],
    provenance: [],
    payload: %{}
  ]

  @type severity :: :error | :warning | :information | :hint
  @type t :: %__MODULE__{
          code: String.t(),
          key: atom(),
          severity: severity(),
          title: String.t(),
          body: Doc.t(),
          primary: Label.t() | nil,
          secondary: [Label.t()],
          notes: [Doc.t()],
          suggestions: [Suggestion.t()],
          provenance: [ProvenanceFrame.t()],
          payload: map()
        }

  @spec new(keyword()) :: t()
  def new(attrs) do
    {legacy_message, attrs} = Keyword.pop(attrs, :message)

    attrs =
      Keyword.put_new_lazy(attrs, :body, fn ->
        case legacy_message do
          nil -> Doc.empty()
          message -> Doc.paragraph(message)
        end
      end)

    attrs = Keyword.update(attrs, :notes, [], &Enum.map(&1, fn note -> normalize_doc(note) end))
    diagnostic = struct!(__MODULE__, attrs)

    unless diagnostic.severity in [:error, :warning, :information, :hint] do
      raise ArgumentError, "invalid diagnostic severity: #{inspect(diagnostic.severity)}"
    end

    unless Regex.match?(~r/^[EWIH][0-9]{3,}$/, diagnostic.code) do
      raise ArgumentError, "invalid diagnostic code: #{inspect(diagnostic.code)}"
    end

    diagnostic
  end

  @doc "Derive the host-compatible plain message from the structured body."
  @spec message(t()) :: String.t()
  def message(%__MODULE__{body: body}), do: Doc.plain(body, width: 1_000_000)

  defp normalize_doc(:empty), do: Doc.empty()

  defp normalize_doc({kind, _} = doc)
       when kind in [:text, :concat, :paragraph, :stack, :code, :note, :hint, :bullet_list],
       do: doc

  defp normalize_doc({kind, _, _} = doc) when kind in [:indent, :emphasis], do: doc
  defp normalize_doc(value), do: Doc.paragraph(value)

  @doc "Extract the stable key from a new diagnostic or a legacy error value."
  @spec key(term()) :: atom() | nil
  def key(%__MODULE__{key: key}), do: key
  def key({:error, reason}), do: key(reason)
  def key({key, _rest}) when is_atom(key), do: key
  def key(tuple) when is_tuple(tuple) and tuple_size(tuple) > 0 and is_atom(elem(tuple, 0)), do: elem(tuple, 0)
  def key(key) when is_atom(key), do: key
  def key(_), do: nil

  @doc "Extract a stable public code when the value already carries one."
  @spec code(term()) :: String.t() | nil
  def code(%__MODULE__{code: code}), do: code
  def code({:error, reason}), do: code(reason)
  def code(tuple) when is_tuple(tuple), do: tuple |> Tuple.to_list() |> Enum.find_value(&embedded_code/1)
  def code(value), do: embedded_code(value)

  defp embedded_code(value) when is_binary(value) do
    case Regex.run(~r/\b([EWIH][0-9]{3,})\b/, value, capture: :all_but_first) do
      [code] -> code
      _ -> nil
    end
  end

  defp embedded_code(_), do: nil
end
