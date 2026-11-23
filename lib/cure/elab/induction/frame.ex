defmodule Cure.Elab.Induction.Frame do
  @moduledoc false

  alias Cure.Core.{Context, Conv, Env}

  @key {__MODULE__, :current}
  @enforce_keys [:signature, :context, :owner, :module_owner]
  defstruct [:signature, :context, :owner, :module_owner]

  @type t :: %__MODULE__{signature: map(), context: Context.t(), owner: atom(), module_owner: String.t() | nil}

  def new(signature, context, env) do
    %__MODULE__{
      signature: signature,
      context: context,
      owner: Env.owned_name(env, signature.name),
      module_owner: Env.owner(env)
    }
  end

  def current, do: Process.get(@key)

  def within(frame, operation) do
    previous = current()
    Process.put(@key, frame)

    try do
      operation.()
    after
      if is_nil(previous), do: Process.delete(@key), else: Process.put(@key, previous)
    end
  end

  def validate(%__MODULE__{} = frame, goal) do
    signature = frame.signature
    declaration = Map.get(goal.env.defs, frame.owner)

    cond do
      Env.owner(goal.env) != frame.module_owner or
          (Env.current_def(goal.env) != nil and
             Env.owned_name(goal.env, Env.current_def(goal.env)) != frame.owner) ->
        {:error, :foreign_declaration_frame}

      is_nil(declaration) or declaration.type != signature.pi or
        frame.owner != Env.owned_name(goal.env, signature.name) or not canonical_signature?(signature) ->
        {:error, :invalid_declaration_frame}

      goal.context != frame.context or goal.names != signature.scope or signature.inferred_return ->
        {:error, :unsupported_induction_motive}

      not Conv.conv?(
        goal.expected,
        signature.return_core,
        Context.env(goal.context),
        Context.length(goal.context),
        Context.signature(goal.context)
      ) ->
        {:error, :unsupported_induction_motive}

      true ->
        :ok
    end
  end

  def validate(_frame, _goal), do: {:error, :missing_declaration_frame}

  defp canonical_signature?(signature) do
    pi =
      signature.telescope
      |> Enum.zip(signature.quantities)
      |> Enum.reverse()
      |> Enum.reduce(signature.return_core, fn {{_name, domain}, grade}, codomain ->
        {:pi, grade, domain, codomain}
      end)

    names = Enum.map(signature.telescope, fn {name, _type} -> to_string(name) end)
    params = Enum.map(signature.params, fn {:param, _meta, name} -> name end)

    pi == signature.pi and Enum.reverse(names) == signature.scope and names == params and
      length(signature.telescope) == length(signature.quantities)
  end
end
