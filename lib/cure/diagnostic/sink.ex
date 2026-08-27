defmodule Cure.Diagnostic.Sink do
  @moduledoc "Collects and projects diagnostics through one host-output boundary."

  alias Cure.Diagnostic
  alias Cure.Diagnostic.{Renderer, SourceRegistry}

  defstruct diagnostics: [],
            registry: nil,
            format: :terminal,
            output_device: :standard_error,
            color: :auto,
            width: 80,
            position_encoding: :utf16

  @type format :: :terminal | :plain | :json | :code | :lsp
  @type t :: %__MODULE__{
          diagnostics: [Diagnostic.t()],
          registry: SourceRegistry.t() | nil,
          format: format(),
          output_device: atom() | pid(),
          color: :auto | :always | :never | boolean(),
          width: pos_integer(),
          position_encoding: :utf8 | :utf16 | :utf32
        }

  @spec new(keyword()) :: t()
  def new(opts \\ []) do
    %__MODULE__{
      registry: Keyword.get(opts, :registry),
      format: Keyword.get(opts, :format, :terminal),
      output_device: Keyword.get(opts, :output_device, :standard_error),
      color: Keyword.get(opts, :color, :auto),
      width: Keyword.get(opts, :width, 80),
      position_encoding: Keyword.get(opts, :position_encoding, :utf16)
    }
  end

  @spec put_registry(t(), SourceRegistry.t() | nil) :: t()
  def put_registry(%__MODULE__{} = sink, registry), do: %{sink | registry: registry}

  @spec emit(t(), Diagnostic.t()) :: t()
  def emit(%__MODULE__{} = sink, %Diagnostic{} = diagnostic),
    do: %{sink | diagnostics: sink.diagnostics ++ [diagnostic]}

  @spec emit_all(t(), [Diagnostic.t()]) :: t()
  def emit_all(%__MODULE__{} = sink, diagnostics),
    do: Enum.reduce(diagnostics, sink, &emit(&2, &1))

  @spec render(t(), Diagnostic.t()) :: iodata() | String.t() | map()
  def render(%__MODULE__{} = sink, %Diagnostic{} = diagnostic) do
    opts = [color: sink.color, width: sink.width, output_device: sink.output_device]

    case sink.format do
      :terminal -> Renderer.terminal(diagnostic, sink.registry, opts)
      :plain -> Renderer.plain(diagnostic, sink.registry, width: sink.width)
      :json -> Renderer.to_map(diagnostic)
      :code -> Renderer.code_diagnostic(diagnostic)
      :lsp -> Renderer.lsp(diagnostic, sink.registry, sink.position_encoding)
    end
  end

  @spec render_all(t()) :: [iodata() | String.t() | map()]
  def render_all(%__MODULE__{} = sink), do: Enum.map(sink.diagnostics, &render(sink, &1))

  @spec flush(t()) :: {:ok, t()} | {:error, term()}
  def flush(%__MODULE__{format: format} = sink) when format in [:terminal, :plain] do
    output =
      sink
      |> render_all()
      |> Enum.map_join("\n\n", &IO.iodata_to_binary/1)

    :ok = IO.write(sink.output_device, if(output == "", do: "", else: output <> "\n"))
    {:ok, %{sink | diagnostics: []}}
  end

  def flush(%__MODULE__{format: :json} = sink), do: flush_serialized(sink, Jason.encode!(render_all(sink)))

  def flush(%__MODULE__{format: :lsp} = sink),
    do: flush_serialized(sink, Jason.encode!(render_all(sink)))

  def flush(%__MODULE__{format: :code} = sink),
    do: flush_serialized(sink, Jason.encode!(Enum.map(sink.diagnostics, &Renderer.code_map/1)))

  defp flush_serialized(sink, output) do
    :ok = IO.write(sink.output_device, output <> "\n")
    {:ok, %{sink | diagnostics: []}}
  end
end
