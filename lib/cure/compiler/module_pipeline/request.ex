defmodule Cure.Compiler.ModulePipeline.Request do
  @moduledoc false

  alias Cure.Compiler.ModulePipeline.Selection

  @fields [
    :entry_point,
    :kind,
    :package,
    :package_dependencies,
    :package_exports,
    :sources,
    :virtual_sources,
    :source_roots,
    :interface_roots,
    :artifact_roots,
    :stdlib,
    :prelude_set,
    :compiler_providers,
    :edition,
    :compiler_options,
    :macro_execution,
    :requested_roots,
    :products,
    :output_root,
    :output,
    :generation,
    :publication,
    :diagnostic_sink,
    :event_sink,
    :incremental,
    :cache,
    :collect_diagnostics,
    :discovery_concurrency,
    :forbid_source_fallback,
    :forbid_beam_resolution,
    :fresh_environment
  ]

  @allowed_options [:module_pipeline | @fields]

  @enforce_keys [:selection]
  defstruct selection: nil,
            entry_point: nil,
            kind: nil,
            package: nil,
            package_dependencies: [],
            package_exports: %{},
            sources: [],
            virtual_sources: [],
            source_roots: [],
            interface_roots: [],
            artifact_roots: [],
            stdlib: nil,
            prelude_set: nil,
            compiler_providers: [],
            edition: nil,
            compiler_options: [],
            macro_execution: nil,
            requested_roots: [],
            products: [],
            output_root: nil,
            output: nil,
            generation: nil,
            publication: nil,
            diagnostic_sink: nil,
            event_sink: nil,
            incremental: nil,
            cache: nil,
            collect_diagnostics: false,
            discovery_concurrency: 1,
            forbid_source_fallback: false,
            forbid_beam_resolution: false,
            fresh_environment: false

  @type t :: %__MODULE__{selection: Selection.t()}

  @spec new(keyword()) :: {:ok, t()} | {:error, term()}
  def new(opts) when is_list(opts) do
    with :ok <- validate_options(opts),
         {:ok, selection} <- Selection.normalize(opts) do
      attrs = opts |> Keyword.take(@fields) |> Map.new() |> Map.put(:selection, selection)
      {:ok, struct!(__MODULE__, attrs)}
    end
  end

  @spec child(t(), keyword()) :: {:ok, t()} | {:error, term()}
  def child(%__MODULE__{} = parent, opts) when is_list(opts) do
    with :ok <- validate_options(opts),
         :ok <- validate_child_selection(parent.selection, opts) do
      attrs =
        parent
        |> Map.from_struct()
        |> Map.merge(opts |> Keyword.delete(:module_pipeline) |> Map.new())
        |> Map.put(:selection, parent.selection)

      {:ok, struct!(__MODULE__, attrs)}
    end
  end

  defp validate_options(opts) do
    unknown = opts |> Keyword.keys() |> Enum.uniq() |> Kernel.--(@allowed_options) |> Enum.sort()
    if unknown == [], do: :ok, else: {:error, {:unknown_module_pipeline_options, unknown}}
  end

  defp validate_child_selection(parent, opts) do
    if Keyword.has_key?(opts, :module_pipeline) do
      with {:ok, child} <- Selection.normalize(opts) do
        if child == parent, do: :ok, else: {:error, {:module_pipeline_mismatch, parent, child}}
      end
    else
      :ok
    end
  end
end
