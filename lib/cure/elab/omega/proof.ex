defmodule Cure.Elab.Omega.Proof do
  @moduledoc """
  Bounded reconstruction of ordinary Core evidence for integer order goals.

  This is not a Farkas soundness theorem. A validated arithmetic certificate
  alone cannot inhabit the original goal. This untrusted module independently
  reconstructs a small fragment using actual locals and qualified IntOrder
  lemmas: reflexivity, transitive paths through local inequalities, addition,
  and scaling by a literal natural. Every candidate, including intermediate
  evidence, is checked by the existing kernel against its actual proposition.

  No registered `@lemma` search is consulted. Strict inequalities, equality,
  nonlinear expressions, algebraic rearrangement, and exhausted search bounds
  return `:unknown`; they are not silently replaced with trivial truth.

  Search uses at most 128 original local slots, depth 12 and 512 reconstruction
  steps. Term recognition has depth 64; literal natural scalars are at most
  1024 and emitted as compact Core literals. These are incompleteness bounds,
  not assumptions added to the goal.
  """

  alias Cure.Core.{Context, Env, Eval, Kernel, Normalise, Quote}

  @order :"Std.Proof.IntOrder#IsLessThanOrEqual"
  @int :"Std.Int#Int"
  @add :"Std.Proof.IntOrder#add_int"
  @scale :"Std.Proof.IntOrder#scale_nat_int"
  @depth 12
  @max_locals 128
  @max_scalar 1_024
  @budget 512
  @lemmas %{
    "is_less_than_or_equal_is_reflexive" => :"Std.Proof.IntOrder#is_less_than_or_equal_is_reflexive",
    "is_less_than_or_equal_is_transitive" => :"Std.Proof.IntOrder#is_less_than_or_equal_is_transitive",
    "adding_the_same_number_preserves_less_than_or_equal" =>
      :"Std.Proof.IntOrder#adding_the_same_number_preserves_less_than_or_equal",
    "adding_preserves_less_than_or_equal" => :"Std.Proof.IntOrder#adding_preserves_less_than_or_equal",
    "scale_nat_int_is_monotone" => :"Std.Proof.IntOrder#scale_nat_int_is_monotone"
  }

  @spec solve(term(), Context.t(), Env.t()) :: {:ok, term()} | :unknown
  def solve(expected, ctx, env) do
    with {:ok, left, right} <- comparison(expected, ctx),
         true <- linear?(left, ctx, 64) and linear?(right, ctx, 64) do
      facts = local_facts(ctx)
      {result, _remaining} = prove(left, right, facts, ctx, env, @depth, @budget)

      case result do
        {:ok, evidence} -> checked(evidence, expected, ctx)
        :unknown -> :unknown
      end
    else
      _ -> :unknown
    end
  end

  # Enumerate the original telescope, never a filtered-and-renumbered version.
  defp local_facts(ctx) do
    ctx.types
    |> Enum.with_index()
    |> Enum.take(@max_locals)
    |> Enum.flat_map(fn {type, index} ->
      type = Quote.reify(type, Context.length(ctx), Context.signature(ctx))

      with {:ok, left, right} <- comparison(type, ctx),
           true <- linear?(left, ctx, 64) and linear?(right, ctx, 64),
           {:ok, evidence} <- checked({:var, index}, type, ctx) do
        [{left, right, evidence}]
      else
        _ -> []
      end
    end)
  end

  defp prove(_left, _right, _facts, _ctx, _env, depth, budget)
       when depth <= 0 or budget <= 0,
       do: {:unknown, budget}

  defp prove(left, right, facts, ctx, env, depth, budget) do
    case Enum.find_value(facts, fn {_a, _b, evidence} ->
           case checked(evidence, order(left, right), ctx) do
             {:ok, _} = result -> result
             :unknown -> nil
           end
         end) do
      {:ok, _} = result ->
        {result, budget - 1}

      nil ->
        {reflexive, budget} =
          lemma("is_less_than_or_equal_is_reflexive", [left], left, right, ctx, env, budget)

        case reflexive do
          {:ok, _} -> {reflexive, budget}
          :unknown -> structural(left, right, facts, ctx, env, depth, budget)
        end
    end
  end

  defp structural(left, right, facts, ctx, env, depth, budget) do
    case {binary(left, @add), binary(right, @add), binary(left, @scale), binary(right, @scale)} do
      {{:ok, a, c}, {:ok, b, d}, _, _} ->
        {result, budget} =
          if a == b do
            with {{:ok, proof}, budget} <- prove(c, d, facts, ctx, env, depth - 1, budget) do
              lemma(
                "adding_the_same_number_preserves_less_than_or_equal",
                [a, c, d, proof],
                left,
                right,
                ctx,
                env,
                budget
              )
            end
          else
            {:unknown, budget}
          end

        case result do
          {:ok, _} ->
            {result, budget}

          :unknown ->
            with {{:ok, ab}, budget} <- prove(a, b, facts, ctx, env, depth - 1, budget),
                 {{:ok, cd}, budget} <- prove(c, d, facts, ctx, env, depth - 1, budget) do
              lemma("adding_preserves_less_than_or_equal", [a, b, c, d, ab, cd], left, right, ctx, env, budget)
            else
              {:unknown, budget} -> path(left, right, facts, ctx, env, depth, budget, [])
            end
        end

      {_, _, {:ok, scalar, a}, {:ok, scalar2, b}} ->
        with {:ok, n} <- natural(scalar, 64),
             {:ok, ^n} <- natural(scalar2, 64),
             {{:ok, proof}, budget} <- prove(a, b, facts, ctx, env, depth - 1, budget) do
          lemma("scale_nat_int_is_monotone", [{:nat_lit, n}, a, b, proof], left, right, ctx, env, budget)
        else
          {:unknown, budget} -> path(left, right, facts, ctx, env, depth, budget, [])
          _ -> path(left, right, facts, ctx, env, depth, budget, [])
        end

      _ ->
        path(left, right, facts, ctx, env, depth, budget, [])
    end
  end

  defp path(_left, _right, _facts, _ctx, _env, depth, budget, _seen)
       when depth <= 0 or budget <= 0,
       do: {:unknown, budget}

  defp path(left, right, facts, ctx, env, depth, budget, seen) do
    if left in seen do
      {:unknown, budget}
    else
      walk_path(left, right, facts, ctx, env, depth, budget, seen)
    end
  end

  defp walk_path(left, right, facts, ctx, env, depth, budget, seen) do
    Enum.reduce_while(facts, {:unknown, budget}, fn
      _, {_result, remaining} when remaining <= 0 ->
        {:halt, {:unknown, remaining}}

      {^left, ^right, evidence}, {_result, remaining} ->
        {:halt, {checked(evidence, order(left, right), ctx), remaining - 1}}

      {^left, middle, first}, {_result, remaining} ->
        case path(middle, right, facts, ctx, env, depth - 1, remaining - 1, [left | seen]) do
          {{:ok, second}, remaining} ->
            result =
              lemma(
                "is_less_than_or_equal_is_transitive",
                [left, middle, right, first, second],
                left,
                right,
                ctx,
                env,
                remaining
              )

            case result do
              {{:ok, _}, _} -> {:halt, result}
              _ -> {:cont, result}
            end

          result ->
            {:cont, result}
        end

      _, result ->
        {:cont, result}
    end)
  end

  defp lemma(_name, _args, _left, _right, _ctx, _env, budget) when budget <= 0,
    do: {:unknown, budget}

  defp lemma(name, args, left, right, ctx, env, budget) do
    # Only this fixed module's explicitly selected lemmas may construct evidence.
    key = Map.fetch!(@lemmas, name)

    result =
      if Map.has_key?(env.defs, key) do
        args
        |> Enum.reduce({:global, key}, fn argument, function -> {:app, function, argument} end)
        |> checked(order(left, right), ctx)
      else
        :unknown
      end

    {result, budget - 1}
  end

  defp checked(evidence, expected, ctx) do
    case Kernel.check(ctx, evidence, Eval.eval(expected, Context.env(ctx))) do
      :ok -> {:ok, evidence}
      {:error, _} -> :unknown
    end
  end

  defp comparison(term, ctx) do
    case Normalise.whnf(ctx, term) do
      {:data, @order, [], [left, right]} -> {:ok, left, right}
      _ -> :unknown
    end
  end

  defp order(left, right), do: {:data, @order, [], [left, right]}

  defp binary({:app, {:app, {:global, name}, a}, b}, name), do: {:ok, a, b}
  defp binary(_, _), do: :unknown

  defp linear?(_term, _ctx, fuel) when fuel <= 0, do: false
  defp linear?({:int_lit, n}, _ctx, _fuel), do: is_integer(n)

  defp linear?({:var, _} = term, ctx, _fuel),
    do: Kernel.check(ctx, term, Eval.eval({:data, @int, [], []}, [])) == :ok

  defp linear?({:global, name}, _ctx, _fuel)
       when name in [
              :"Std.Proof.IntOrder#int_zero",
              :"Std.Proof.IntOrder#int_one",
              :"Std.Proof.IntOrder#int_negative_one"
            ],
       do: true

  defp linear?({:ctor, name, [n]}, _ctx, fuel)
       when name in [:"Std.Int#FromNat", :"Std.Int#NegativeSuccessor"],
       do: match?({:ok, _}, natural(n, fuel - 1))

  defp linear?({:app, {:app, {:global, @add}, a}, b}, ctx, fuel),
    do: linear?(a, ctx, fuel - 1) and linear?(b, ctx, fuel - 1)

  defp linear?({:app, {:app, {:global, @scale}, scalar}, value}, ctx, fuel),
    do: match?({:ok, _}, natural(scalar, fuel - 1)) and linear?(value, ctx, fuel - 1)

  defp linear?({:app, {:global, name}, value}, ctx, fuel)
       when name in [
              :"Std.Int#negate",
              :"Std.Proof.IntOrder#succ_int",
              :"Std.Proof.IntOrder#pred_int"
            ],
       do: linear?(value, ctx, fuel - 1)

  defp linear?(_, _, _), do: false

  defp natural(_, fuel) when fuel <= 0, do: :unknown

  defp natural({:nat_lit, n}, _fuel) when is_integer(n) and n >= 0 and n <= @max_scalar,
    do: {:ok, n}

  defp natural({:ctor, :"Std.Nat#Z", []}, _fuel), do: {:ok, 0}

  defp natural({:ctor, :"Std.Nat#S", [n]}, fuel) do
    with {:ok, k} when k < @max_scalar <- natural(n, fuel - 1) do
      {:ok, k + 1}
    else
      _ -> :unknown
    end
  end

  defp natural(_, _), do: :unknown
end
