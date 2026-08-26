defmodule Cure.Compiler.MacroProtocol do
  @moduledoc "Pure two-party protocol validation for the concrete macro library."

  @spec build(String.t() | atom(), [atom()], [map()], keyword()) :: {:ok, map()} | {:error, term()}
  def build(name, roles, steps, opts \\ [])

  def build(name, roles, steps, opts)
      when (is_atom(name) or is_binary(name)) and is_list(roles) and is_list(steps) and is_list(opts) do
    if Keyword.keyword?(opts) do
      with :ok <- validate_roles(roles),
           :ok <- validate_steps(roles, steps),
           :ok <- validate_choices(roles, Keyword.get(opts, :choices, [])) do
        messages =
          steps
          |> Enum.map(&Map.fetch!(&1, :message))
          |> Enum.uniq_by(&message_identity/1)

        {:ok,
         %{
           kind: :quoted_protocol,
           name: name,
           roles: roles,
           steps: steps,
           messages: messages,
           timeout: Keyword.get(opts, :timeout),
           declaration_hash: :erlang.phash2({name, roles, steps, opts}),
           declarations: [{:protocol_def, [name: name], %{roles: roles, steps: steps}}]
         }}
      end
    else
      {:error, :invalid_protocol_options}
    end
  end

  def build(name, _roles, _steps, _opts) when not is_atom(name) and not is_binary(name),
    do: {:error, {:invalid_protocol_name, name}}

  def build(_name, roles, _steps, _opts) when not is_list(roles),
    do: {:error, :invalid_protocol_roles}

  def build(_name, _roles, steps, _opts) when not is_list(steps),
    do: {:error, :invalid_protocol_steps}

  def build(_name, _roles, _steps, _opts), do: {:error, :invalid_protocol_options}

  defp validate_roles(roles) do
    cond do
      length(roles) != 2 -> {:error, {:protocol_role_count, length(roles)}}
      Enum.any?(roles, fn role -> not is_atom(role) end) -> {:error, :invalid_protocol_role}
      length(Enum.uniq(roles)) != 2 -> {:error, :duplicate_protocol_role}
      true -> :ok
    end
  end

  defp validate_steps(roles, steps) do
    Enum.reduce_while(steps, :ok, fn step, :ok ->
      case step do
        %{sender: sender, receiver: receiver} = step ->
          message = Map.get(step, :message)

          cond do
            sender not in roles or receiver not in roles -> {:halt, {:unknown_protocol_role, sender, receiver}}
            sender == receiver -> {:halt, {:self_protocol_step, sender}}
            is_nil(message) -> {:halt, :invalid_protocol_message}
            true -> {:cont, :ok}
          end

        _other ->
          {:halt, :invalid_protocol_step}
      end
    end)
    |> normalize_result()
  end

  defp validate_choices(_roles, choices) when not is_list(choices), do: {:error, :invalid_protocol_choices}

  defp validate_choices(roles, choices) do
    Enum.reduce_while(choices, :ok, fn choice, :ok ->
      case choice do
        %{decider: decider} = choice ->
          branches = Map.get(choice, :branches, [])

          cond do
            decider not in roles ->
              {:halt, {:unknown_choice_decider, decider}}

            not is_list(branches) or branches == [] ->
              {:halt, {:invalid_protocol_branches, decider}}

            Enum.any?(branches, fn branch -> not branch_starts_with?(branch, decider) end) ->
              {:halt, {:unprojectable_choice, decider}}

            true ->
              {:cont, :ok}
          end

        _other ->
          {:halt, :invalid_protocol_choice}
      end
    end)
    |> normalize_result()
  end

  defp branch_starts_with?([%{sender: sender} | _], decider), do: sender == decider
  defp branch_starts_with?(_, _decider), do: false

  defp message_identity(%{} = message), do: Map.get(message, :name, message)
  defp message_identity(message), do: message

  defp normalize_result(:ok), do: :ok
  defp normalize_result(error), do: {:error, error}
end
