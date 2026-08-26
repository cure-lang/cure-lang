defmodule Cure.Compiler.MacroReflection do
  @moduledoc """
  Advisory Tier-4 reflection for macro elaborators.

  The functions in this module expose observations and append-only plans. They
  never mutate a Core environment and every eventual result still goes through
  ordinary dependent elaboration and kernel checking.
  """

  alias Cure.Core.{Context, Env, Inductive, Quote}
  alias Cure.Elab.{Elaborator, MacroExpand}

  @spec resolve(Env.t(), String.t() | atom()) :: {:ok, map()} | {:error, :not_found}
  def resolve(%Env{} = env, name) do
    atom = name_atom(name)

    case Env.get_def(env, atom) do
      nil ->
        case Inductive.get_family(env, atom) do
          nil -> {:error, :not_found}
          family -> {:ok, %{kind: :type, name: atom, signature: family}}
        end

      definition ->
        {:ok, Map.put(definition, :kind, :definition)}
    end
  end

  @spec constructors(Env.t(), String.t() | atom()) :: {:ok, [map()]} | {:error, :not_found}
  def constructors(%Env{} = env, name) do
    atom = name_atom(name)

    if Inductive.family?(env, atom) do
      {:ok, Inductive.ctors_of(env, atom)}
    else
      {:error, :not_found}
    end
  end

  @spec infer(tuple(), Env.t()) :: {:ok, tuple()} | {:error, term()}
  def infer(quoted, %Env{} = env) do
    case Elaborator.elaborate_expr_typed(quoted, [], Context.empty(env), env) do
      {:ok, _term, type} -> {:ok, Quote.reify(type, 0, env)}
      {:error, _} = error -> error
    end
  end

  @spec expand(term(), Env.t()) :: {:ok, term()} | {:error, term()}
  def expand(quoted, %Env{} = env), do: MacroExpand.expand(quoted, env)

  @spec lift(tuple() | [tuple()]) :: {:ok, [tuple()]} | {:error, term()}
  def lift(declaration) when is_tuple(declaration), do: {:ok, [declaration]}

  def lift(declarations) when is_list(declarations) do
    if Enum.all?(declarations, &is_tuple/1), do: {:ok, declarations}, else: {:error, :invalid_lift_declaration}
  end

  defp name_atom(name) when is_atom(name), do: name
  defp name_atom(name) when is_binary(name), do: String.to_atom(name)
end
