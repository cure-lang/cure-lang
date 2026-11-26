defmodule Cure.Elab.Omega.Linear do
  @moduledoc """
  Read Core goals into linear integer atoms for `by omega`.

  This is the recognition half of the omega tactic: it decides whether a goal is
  inside the linear-integer fragment, and if so renders it and its relevant
  hypotheses as `Cure.Elab.Omega` atoms. It builds no evidence — the witness it
  helps produce is checked by `check_lia_candidate` in the kernel. That Boolean
  verdict is not itself evidence of the original proposition.

  ## Fragment

  Recognised propositions (after head normalization):

    * `IsLessThanOrEqual(lhs, rhs)` — `lhs ≤ rhs`
    * `IsLessThan(lhs, rhs)` — `lhs < rhs`
    * `Equivalent(Int, lhs, rhs)` — split into `lhs ≤ rhs` and `rhs ≤ lhs`

  Recognised integer terms:

    * integer literals (`{:int_lit, n}` and the `FromNat`/`NegativeSuccessor`
      constructor forms the surface elaborates to)
    * local variables of type `Int`
    * `add_int`, `negate`, `pred_int`, `succ_int`, and `scale_nat_int` by a
      literal, applied to recognised terms

  Anything else — a `Nat` index, a multiplication of two variables, an
  unreduced call — is outside the fragment, and `by omega` says so instead of
  guessing.
  """

  alias Cure.Core.{Context, Env, Normalise, Quote}
  alias Cure.Elab.Omega

  @equivalent :"Std.Equivalent#Equivalent"
  @int :"Std.Int#Int"
  @le :"Std.Proof.IntOrder#IsLessThanOrEqual"
  @lt :"Std.Proof.IntOrder#IsLessThan"

  @doc """
  The linear atoms of `hypotheses` and the negated goal, in the checker's own
  order (`hyps ++ [negate(goal)]`), or `:outside_fragment`.

  `hypotheses` is the list of `{name, core_type}` pairs in scope; only those
  whose type is a recognised comparison contribute.
  """
  @spec atoms([{String.t(), term()}], term(), Context.t(), Env.t()) ::
          {:ok, [Omega.linear_atom()]} | :outside_fragment
  def atoms(hypotheses, goal, ctx, env) do
    case obligations(hypotheses, goal, ctx, env) do
      {:ok, [{atoms, _goal}]} -> {:ok, atoms}
      _ -> :outside_fragment
    end
  end

  @doc "One independent contradiction problem per conjunct of the goal."
  def obligations(hypotheses, goal, ctx, env) do
    with {:ok, goal_atoms} <- comparisons(goal, ctx, env),
         {:ok, hypothesis_atoms} <- collect_hypotheses(hypotheses, ctx, env) do
      hypotheses = Enum.map(hypothesis_atoms, &Omega.normalize/1)

      {:ok,
       Enum.map(goal_atoms, fn atom ->
         goal = Omega.normalize(atom)
         {hypotheses ++ [goal |> Omega.negate() |> Omega.normalize()], goal}
       end)}
    end
  end

  @doc """
  The goal's own comparison as one atom, or `:outside_fragment`.

  `atoms/4` returns `hyps ++ [negate(goal)]`, so the last entry is the NEGATED
  goal. The checker takes the goal positively, so recover it directly from the
  original proposition; double integer negation is not a substitute for reification.
  """
  @spec goal_atom(term(), Context.t(), Env.t()) :: {:ok, Omega.linear_atom()} | :outside_fragment
  def goal_atom(goal, ctx, env) do
    case comparisons(goal, ctx, env) do
      {:ok, [atom]} -> {:ok, Omega.normalize(atom)}
      _ -> :outside_fragment
    end
  end

  defp collect_hypotheses(hypotheses, ctx, env) do
    Enum.reduce_while(hypotheses, {:ok, []}, fn {_name, type}, {:ok, acc} ->
      case comparisons(type, ctx, env) do
        {:ok, atoms} -> {:cont, {:ok, acc ++ atoms}}
        # A hypothesis outside the fragment is simply not an omega input; it is
        # not an error, because the goal may still be provable from the rest.
        :outside_fragment -> {:cont, {:ok, acc}}
      end
    end)
  end

  # Split a proposition into its conjunctive atoms.
  defp comparisons(term, ctx, env) do
    case Normalise.whnf(ctx, term) do
      {:data, family, [], [left, right]} -> comparison(family, left, right, ctx, env)
      {:data, @equivalent, [carrier], [left, right]} -> equivalence(carrier, left, right, ctx, env)
      _ -> :outside_fragment
    end
  end

  defp comparison(family, left, right, ctx, env) do
    cond do
      family == @le ->
        with {:ok, left_form} <- linear(left, ctx, env),
             {:ok, right_form} <- linear(right, ctx, env) do
          {:ok, [Omega.atom_le(subtract(left_form, right_form))]}
        end

      family == @lt ->
        with {:ok, left_form} <- linear(left, ctx, env),
             {:ok, right_form} <- linear(right, ctx, env) do
          {:ok, [Omega.atom_lt(subtract(left_form, right_form))]}
        end

      true ->
        :outside_fragment
    end
  end

  defp equivalence(carrier, left, right, ctx, env) do
    if Normalise.whnf(ctx, carrier) == {:data, @int, [], []} do
      with {:ok, left_form} <- linear(left, ctx, env),
           {:ok, right_form} <- linear(right, ctx, env) do
        {:ok,
         [
           Omega.atom_le(subtract(left_form, right_form)),
           Omega.atom_le(subtract(right_form, left_form))
         ]}
      end
    else
      :outside_fragment
    end
  end

  # -- Linear forms ----------------------------------------------------------

  defp linear({:int_lit, n}, _ctx, _env), do: {:ok, {n, %{}}}

  defp linear({:global, :"Std.Proof.IntOrder#int_zero"}, _ctx, _env), do: {:ok, {0, %{}}}
  defp linear({:global, :"Std.Proof.IntOrder#int_one"}, _ctx, _env), do: {:ok, {1, %{}}}
  defp linear({:global, :"Std.Proof.IntOrder#int_negative_one"}, _ctx, _env), do: {:ok, {-1, %{}}}

  defp linear({:var, index}, ctx, _env) do
    case Context.lookup(ctx, index) do
      nil ->
        :outside_fragment

      value ->
        case Normalise.whnf_value(value, Context.signature(ctx)) do
          {:vdata, @int, []} -> {:ok, {0, %{index => 1}}}
          _ -> :outside_fragment
        end
    end
  end

  defp linear({:ctor, name, args}, ctx, env) do
    case {name, args} do
      {:"Std.Int#FromNat", [{:nat_lit, n}]} -> {:ok, {n, %{}}}
      {:"Std.Int#NegativeSuccessor", [{:nat_lit, n}]} -> {:ok, {-(n + 1), %{}}}
      {:"Std.Int#FromNat", [{:ctor, _, _} = nat]} -> nat_literal(nat, ctx, env)
      {:"Std.Int#NegativeSuccessor", [{:ctor, _, _} = nat]} -> negated_nat_literal(nat, ctx, env)
      _ -> :outside_fragment
    end
  end

  defp linear({:app, {:app, {:global, name}, left}, right}, ctx, env) do
    case name do
      :"Std.Proof.IntOrder#add_int" ->
        with {:ok, left_form} <- linear(left, ctx, env),
             {:ok, right_form} <- linear(right, ctx, env) do
          {:ok, add(left_form, right_form)}
        end

      :"Std.Proof.IntOrder#multiply_int" ->
        scale(left, right, ctx, env)

      # `scale_nat_int(scalar, value)` -- scaling by a LITERAL natural. This arm
      # belongs to the two-argument application clause, not to a separate clause
      # after it: a later clause with the same head pattern is unreachable, which
      # is how `scale_nat_int` was silently outside the fragment. Merging it here
      # makes the term reachable and keeps the fragment description honest.
      :"Std.Proof.IntOrder#scale_nat_int" ->
        with {:ok, factor} <- nat_literal_value(left, ctx, env),
             {:ok, form} <- linear(right, ctx, env) do
          {:ok, scale_form(form, factor)}
        end

      _ ->
        :outside_fragment
    end
  end

  defp linear({:app, {:global, name}, argument}, ctx, env) do
    case name do
      base when base in [:"Std.Int#negate", :"Std.Proof.IntOrder#pred_int", :"Std.Proof.IntOrder#succ_int"] ->
        with {:ok, form} <- linear(argument, ctx, env) do
          case base do
            :"Std.Int#negate" -> {:ok, negate(form)}
            :"Std.Proof.IntOrder#pred_int" -> {:ok, add(form, {-1, %{}})}
            :"Std.Proof.IntOrder#succ_int" -> {:ok, add(form, {1, %{}})}
          end
        end

      _ ->
        :outside_fragment
    end
  end

  defp linear(_term, _ctx, _env), do: :outside_fragment

  # `multiply_int(c, v)`: linear only when one side is a literal.
  defp scale(left, right, ctx, env) do
    with :outside_fragment <- literal_value(left, ctx, env) do
      case literal_value(right, ctx, env) do
        {:ok, factor} ->
          with {:ok, form} <- linear(left, ctx, env), do: {:ok, scale_form(form, factor)}

        :outside_fragment ->
          :outside_fragment
      end
    else
      {:ok, factor} ->
        with {:ok, form} <- linear(right, ctx, env), do: {:ok, scale_form(form, factor)}
    end
  end

  defp literal_value(term, ctx, env) do
    case linear(term, ctx, env) do
      {:ok, {constant, coefficients}} when map_size(coefficients) == 0 -> {:ok, constant}
      _ -> :outside_fragment
    end
  end

  defp nat_literal({:ctor, name, args}, ctx, env) do
    with {:ok, value} <- nat_literal_value({:ctor, name, args}, ctx, env), do: {:ok, {value, %{}}}
  end

  defp nat_literal_value({:nat_lit, n}, _ctx, _env), do: {:ok, n}

  defp nat_literal_value({:ctor, name, args}, ctx, env) do
    case {name, args} do
      {:"Std.Nat#Z", []} -> {:ok, 0}
      {:"Std.Nat#S", [inner]} -> with {:ok, n} <- nat_literal_value(inner, ctx, env), do: {:ok, n + 1}
      _ -> :outside_fragment
    end
  end

  defp nat_literal_value(_other, _ctx, _env), do: :outside_fragment

  defp negated_nat_literal(nat, ctx, env) do
    with {:ok, n} <- nat_literal_value(nat, ctx, env), do: {:ok, {-(n + 1), %{}}}
  end

  # -- Form arithmetic -------------------------------------------------------

  defp add({constant_a, coefficients_a}, {constant_b, coefficients_b}) do
    coefficients =
      Map.merge(coefficients_a, coefficients_b, fn _k, a, b -> a + b end)
      |> Enum.reject(fn {_k, v} -> v == 0 end)
      |> Map.new()

    {constant_a + constant_b, coefficients}
  end

  defp subtract(left, right), do: add(left, negate(right))

  defp negate({constant, coefficients}),
    do: {-constant, Map.new(coefficients, fn {k, v} -> {k, -v} end)}

  defp scale_form({constant, coefficients}, factor),
    do:
      {constant * factor,
       coefficients |> Map.new(fn {k, v} -> {k, v * factor} end) |> Map.reject(fn {_k, v} -> v == 0 end)}

  @doc false
  def print_form({constant, coefficients}) do
    terms =
      coefficients
      |> Enum.sort()
      |> Enum.map(fn {index, coefficient} -> "#{coefficient}*x#{index}" end)

    Enum.join(terms ++ [Integer.to_string(constant)], " + ")
  end

  @doc false
  def reify_hypotheses(ctx, names) do
    depth = Context.length(ctx)
    signature = Context.signature(ctx)

    names
    |> Enum.with_index()
    |> Enum.flat_map(fn {name, index} ->
      case Context.lookup(ctx, index) do
        nil -> []
        value -> [{name, Quote.reify(value, depth, signature)}]
      end
    end)
  end
end
