defmodule Cure.Elab.SourceContext do
  @moduledoc """
  Immutable, ephemeral presentation context for one canonical source check.

  This is not an environment, interface or proof artifact. Observations belong
  to this exact text and file, never to a process's last checked hole identity.
  Failed checks retain the observations reached before refusal.
  """

  alias Cure.Elab.{Program, ProofState}

  @enforce_keys [:file, :text, :hash]
  defstruct [:file, :text, :hash, :version, :status, observations: []]

  @doc "Check through the canonical compiler and capture source-local observations."
  def analyze(text, opts \\ []) when is_binary(text) do
    file = Keyword.get(opts, :file, "nofile")
    {result, observations} = ProofState.capture(fn -> Cure.Compiler.check_source(text, opts) end)

    observations =
      observations
      |> Enum.filter(&(from_file?(&1.span, file) or from_file?(&1.scope, file)))
      |> surviving(result)

    context = %__MODULE__{
      file: file,
      text: text,
      hash: :crypto.hash(:sha256, text),
      version: Keyword.get(opts, :version),
      status: if(match?({:ok, _}, result), do: :checked, else: :failed),
      observations: observations
    }

    {result, context}
  end

  @doc "Source occurrences, separate from logical-goal deduplication."
  def hole_goals(%__MODULE__{observations: observations}) do
    observations
    |> Enum.filter(&(&1.kind == :hole))
    |> Enum.uniq_by(&{&1.id, &1.span})
    |> Enum.with_index()
    |> Enum.flat_map(fn {state, index} ->
      Enum.map(state.goals, &Map.merge(&1, %{span: state.span, occurrence_index: index}))
    end)
  end

  @doc "Remaining source-local goals after logical identity deduplication."
  def remaining(%__MODULE__{observations: observations}), do: ProofState.remaining(observations)

  @doc "Select source-local goals at a negotiated LSP position."
  def at(%__MODULE__{} = context, position, encoding \\ :utf16),
    do: ProofState.at(context.observations, context.text, position, encoding)

  defp surviving(observations, {:ok, env}) do
    owned = Program.program_owned_definitions(env)

    Enum.filter(observations, fn
      %{kind: :hole, id: {:hole, id}, goals: [%{function: function}]} ->
        case Map.get(owned, function) do
          %{body: body} -> has_hole?(body, id)
          _ -> false
        end

      state ->
        Enum.all?(state.goals, &Map.has_key?(owned, &1.function))
    end)
  end

  defp surviving(observations, {:error, _reason}), do: observations

  defp has_hole?({:hole, id}, id), do: true

  defp has_hole?(term, id) when is_tuple(term),
    do: term |> Tuple.to_list() |> Enum.any?(&has_hole?(&1, id))

  defp has_hole?(terms, id) when is_list(terms), do: Enum.any?(terms, &has_hole?(&1, id))
  defp has_hole?(_term, _id), do: false

  defp from_file?(%Cure.Diagnostic.Span{source_id: file}, file), do: true
  defp from_file?(%Cure.Diagnostic.Span{path: file}, file), do: true
  defp from_file?(_span, _file), do: false
end
