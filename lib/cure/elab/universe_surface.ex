defmodule Cure.Elab.UniverseSurface do
  @moduledoc """
  Surface universe syntax recognition and Core lowering (Phase 5 U4).

  Handles `Type`, `TypeN`, `Type(level)`, `TypeLimit`, `TypeLimitN`,
  `UniverseLevel`, `universe_zero`, `universe_succ(level)`, and
  `universe_max(l1, l2)`. Arbitrary-precision decimal indices are bounded by
  an input-size guard (spec §14.4) before integer conversion.
  """

  alias Cure.Core.{Context, Eval, Sort, UniverseLevel}

  @max_decimal_digits 64

  @doc "True iff `name` is a reserved surface universe or level primitive name."
  @spec universe_name?(String.t()) :: boolean()
  def universe_name?(name) when is_binary(name) do
    name in ["Type", "UniverseLevel", "TypeLimit", "universe_zero", "universe_succ", "universe_max"] or
      match?({:ok, _}, parse_prefixed_nat(name, "Type")) or
      match?({:ok, _}, parse_prefixed_nat(name, "TypeLimit"))
  end

  def universe_name?(_), do: false

  @doc "Lower a surface variable name if it denotes a universe sort, `UniverseLevel`, or `universe_zero`."
  @spec lower_variable(String.t()) :: {:ok, Cure.Core.Term.t()} | {:error, term()} | :not_universe
  def lower_variable("Type"), do: {:ok, {:type, Sort.finite_zero()}}
  def lower_variable("UniverseLevel"), do: {:ok, {:level_type}}
  def lower_variable("TypeLimit"), do: {:ok, {:type, Sort.omega(0)}}
  def lower_variable("universe_zero"), do: {:ok, {:level_value, UniverseLevel.zero()}}

  def lower_variable(name) when is_binary(name) do
    case parse_prefixed_nat(name, "TypeLimit") do
      {:ok, n} ->
        {:ok, {:type, Sort.omega(n)}}

      {:error, _} = err ->
        err

      :no_match ->
        case parse_prefixed_nat(name, "Type") do
          {:ok, n} -> {:ok, {:type, Sort.finite_closed(n)}}
          {:error, _} = err -> err
          :no_match -> :not_universe
        end
    end
  end

  def lower_variable(_), do: :not_universe

  @doc """
  Lower a surface call if its head is `Type`, `universe_zero`, `universe_succ`,
  or `universe_max`. Returns `:not_universe` for ordinary calls.
  """
  @spec lower_call(String.t(), [term()], (term() -> {:ok, Cure.Core.Term.t()} | {:error, term()})) ::
          {:ok, Cure.Core.Term.t()} | {:error, term()} | :not_universe
  def lower_call("universe_zero", [], _lower_arg),
    do: {:ok, {:level_value, UniverseLevel.zero()}}

  def lower_call("universe_zero", args, _lower_arg),
    do: {:error, {:invalid_level_arity, :universe_zero, length(args), 0}}

  def lower_call("universe_succ", [arg], lower_arg) do
    with {:ok, core} <- lower_arg.(arg),
         {:ok, level} <- core_to_level(core) do
      {:ok, {:level_value, UniverseLevel.succ(level)}}
    end
  end

  def lower_call("universe_succ", args, _lower_arg),
    do: {:error, {:invalid_level_arity, :universe_succ, length(args), 1}}

  def lower_call("universe_max", [left, right], lower_arg) do
    with {:ok, left_core} <- lower_arg.(left),
         {:ok, right_core} <- lower_arg.(right),
         {:ok, left_level} <- core_to_level(left_core),
         {:ok, right_level} <- core_to_level(right_core) do
      {:ok, {:level_value, UniverseLevel.max(left_level, right_level)}}
    end
  end

  def lower_call("universe_max", args, _lower_arg),
    do: {:error, {:invalid_level_arity, :universe_max, length(args), 2}}

  def lower_call("Type", [arg], lower_arg) do
    with {:ok, core} <- lower_arg.(arg),
         {:ok, level} <- core_to_level(core) do
      {:ok, {:type, Sort.finite(level)}}
    end
  end

  def lower_call("Type", args, _lower_arg),
    do: {:error, {:invalid_level_arity, :Type, length(args), 1}}

  def lower_call(_name, _args, _lower_arg), do: :not_universe

  @doc "Lift a Core term into a `UniverseLevel`, rejecting non-level literals and type formers."
  @spec core_to_level(Cure.Core.Term.t()) :: {:ok, UniverseLevel.t()} | {:error, term()}
  def core_to_level({:level_value, %UniverseLevel{} = level}), do: {:ok, level}

  def core_to_level(term)
      when is_tuple(term) and
             elem(term, 0) in [
               :nat_lit,
               :int_lit,
               :float_lit,
               :atom_lit,
               :bounded_lit,
               :int_type,
               :float_type,
               :binary_type,
               :atom_type,
               :type,
               :level_type,
               :data,
               :ctor,
               :pi,
               :lam,
               :effect_type,
               :effect_pure,
               :effect_bind
             ],
      do: {:error, {:invalid_level_term, term, :not_universe_level}}

  def core_to_level(term), do: {:ok, UniverseLevel.atom(term)}

  @doc "Infer the semantic type value of a lowered universe/level Core term in `ctx`."
  @spec type_of_core(Cure.Core.Term.t(), Context.t()) :: {:ok, Cure.Core.Value.t()} | {:error, term()}
  def type_of_core({:type, sort}, ctx) do
    with :ok <- Sort.validate(sort, ctx) do
      {:ok, Eval.eval({:type, Sort.successor(sort)}, Context.env(ctx))}
    end
  end

  def type_of_core({:level_type}, _ctx),
    do: {:ok, Eval.eval({:type, Sort.finite_zero()}, [])}

  def type_of_core({:level_value, level}, ctx) do
    with :ok <- UniverseLevel.validate(level, ctx) do
      {:ok, {:vlevel_type}}
    end
  end

  defp parse_prefixed_nat(name, prefix) do
    prefix_size = byte_size(prefix)

    case name do
      <<^prefix::binary-size(^prefix_size), digits::binary>> when byte_size(digits) > 0 ->
        if ascii_digits?(digits) do
          if byte_size(digits) <= @max_decimal_digits do
            {:ok, String.to_integer(digits)}
          else
            {:error, {:universe_index_too_large, name}}
          end
        else
          :no_match
        end

      _ ->
        :no_match
    end
  end

  defp ascii_digits?(<<>>), do: true
  defp ascii_digits?(<<c, rest::binary>>) when c >= ?0 and c <= ?9, do: ascii_digits?(rest)
  defp ascii_digits?(_), do: false
end
