defmodule Cure.Compiler.MacroReducer do
  @moduledoc """
  Pure reducer-style AST construction on top of advisory macro reflection.

  The builder only uses constructor signatures to shape patterns. The returned
  AST is ordinary untrusted surface syntax and must still be elaborated by the
  dependent pipeline before it can run.
  """

  alias Cure.Compiler.MacroReflection
  alias Cure.Core.Env

  @type arm_spec :: %{
          required(:constructor) => atom(),
          optional(:bindings) => [String.t()],
          required(:body) => term()
        }

  @spec build_match(String.t() | atom(), term(), [arm_spec()], Env.t()) ::
          {:ok, term()} | {:error, term()}
  def build_match(type_name, scrutinee, arm_specs, %Env{} = env) when is_list(arm_specs),
    do: build_dispatch(:macro_reducer, type_name, scrutinee, arm_specs, env)

  def build_match(_type_name, _scrutinee, _arm_specs, %Env{}), do: {:error, :invalid_reducer_arms}

  @doc "Build exhaustive constructor dispatch for a view-style macro."
  @spec build_view(String.t() | atom(), term(), [arm_spec()], Env.t()) ::
          {:ok, term()} | {:error, term()}
  def build_view(type_name, scrutinee, arm_specs, %Env{} = env) when is_list(arm_specs),
    do: build_dispatch(:macro_view, type_name, scrutinee, arm_specs, env)

  def build_view(_type_name, _scrutinee, _arm_specs, %Env{}), do: {:error, :invalid_reducer_arms}

  @doc "Build exhaustive constructor dispatch for a flow-style macro."
  @spec build_flow(String.t() | atom(), term(), [arm_spec()], Env.t()) ::
          {:ok, term()} | {:error, term()}
  def build_flow(type_name, scrutinee, arm_specs, %Env{} = env) when is_list(arm_specs),
    do: build_dispatch(:macro_flow, type_name, scrutinee, arm_specs, env)

  def build_flow(_type_name, _scrutinee, _arm_specs, %Env{}), do: {:error, :invalid_reducer_arms}

  @doc "Build the reducer/view/flow dispatch bundle used by declaration macros."
  @spec build_bundle(String.t() | atom(), term(), [arm_spec()], Env.t()) ::
          {:ok, map()} | {:error, term()}
  def build_bundle(type_name, scrutinee, arm_specs, %Env{} = env) when is_list(arm_specs) do
    with {:ok, reducer} <- build_match(type_name, scrutinee, arm_specs, env),
         {:ok, view} <- build_view(type_name, scrutinee, arm_specs, env),
         {:ok, flow} <- build_flow(type_name, scrutinee, arm_specs, env) do
      {:ok, %{kind: :macro_dispatch_bundle, type: type_name, reducer: reducer, view: view, flow: flow}}
    end
  end

  def build_bundle(_type_name, _scrutinee, _arm_specs, %Env{}), do: {:error, :invalid_reducer_arms}

  defp build_dispatch(generated_by, type_name, scrutinee, arm_specs, env) do
    with :ok <- validate_arm_specs(arm_specs),
         {:ok, constructors} <- MacroReflection.constructors(env, type_name),
         arm_specs <- canonicalize_arm_specs(arm_specs, env),
         :ok <- validate_arm_set(constructors, arm_specs),
         {:ok, arms} <- build_arms(constructors, arm_specs) do
      {:ok, {:pattern_match, [generated_by: generated_by], [scrutinee | arms]}}
    end
  end

  defp validate_arm_specs(arm_specs) do
    if Enum.all?(arm_specs, &valid_arm_spec?/1), do: :ok, else: {:error, :invalid_reducer_arm}
  end

  defp valid_arm_spec?(%{constructor: constructor, body: _body} = spec)
       when is_atom(constructor) or is_binary(constructor) do
    case Map.fetch(spec, :bindings) do
      :error -> true
      {:ok, bindings} -> is_list(bindings) and Enum.all?(bindings, &is_binary/1)
    end
  end

  defp valid_arm_spec?(_spec), do: false

  defp canonicalize_arm_specs(arm_specs, env) do
    Enum.map(arm_specs, fn spec ->
      %{spec | constructor: Env.resolve_key(env, env.ctors, spec.constructor)}
    end)
  end

  defp validate_arm_set(constructors, arm_specs) do
    expected = constructors |> Enum.map(& &1.name) |> MapSet.new()
    actual = arm_specs |> Enum.map(& &1.constructor) |> MapSet.new()

    cond do
      MapSet.size(actual) != length(arm_specs) ->
        {:error, :duplicate_reducer_constructor}

      not MapSet.subset?(actual, expected) ->
        {:error, {:unknown_reducer_constructor, MapSet.difference(actual, expected) |> MapSet.to_list()}}

      actual != expected ->
        {:error, {:incomplete_reducer, MapSet.difference(expected, actual) |> MapSet.to_list()}}

      true ->
        :ok
    end
  end

  defp build_arms(constructors, arm_specs) do
    by_name = Map.new(arm_specs, &{&1.constructor, &1})

    Enum.reduce_while(constructors, {:ok, []}, fn ctor, {:ok, acc} ->
      spec = Map.fetch!(by_name, ctor.name)
      bindings = Map.get(spec, :bindings, [])

      if length(bindings) != length(ctor.args) do
        {:halt, {:error, {:reducer_arity, ctor.name, length(bindings), length(ctor.args)}}}
      else
        pattern_name = Cure.Elab.Name.base(ctor.name)
        pattern = {:function_call, [name: pattern_name], Enum.map(bindings, &variable/1)}
        {:cont, {:ok, acc ++ [{:match_arm, [pattern: pattern], [spec.body]}]}}
      end
    end)
  end

  defp variable(name), do: {:variable, [scope: :local], name}
end
