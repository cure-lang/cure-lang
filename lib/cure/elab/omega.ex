defmodule Cure.Elab.Omega do
  @moduledoc """
  The untrusted linear-arithmetic producer behind `by omega`.

  This module only finds candidate Farkas multipliers. A checked Boolean
  candidate test is not a proof of a user's proposition: admitting a goal also
  requires separately reconstructed Core evidence checked at that original goal.

  ## Candidate input

  The reifier supplies a conjunction of linear integer comparisons:

    * hypotheses of the form `IsLessThanOrEqual(lhs, rhs)` and
      `IsLessThan(lhs, rhs)`, where `lhs`/`rhs` are integer linear forms;
    * the negated goal, exactly once. An equality requires two independent
      contradiction problems, not a conjunction of both negated directions.

  A linear form is a sum of integer literals and variables with integer
  coefficients. Anything else — multiplication of two variables, `Nat` goals,
  non-linear terms or unsupported families is refused by the reifier. Actual
  admission is narrower still: `Omega.Proof` must reconstruct checked evidence
  using its documented order-lemma subset.

  ## Why the producer is deterministic

  Fourier–Motzkin elimination is run over a fixed variable order with a fixed
  combination rule, and the search is bounded by a step ceiling. The same goal
  always produces the same witness, which is what lets a corpus pin a specific
  answer and lets a reviewer replay it.

  ## Completeness boundary

  The search works on the rational relaxation of normalized integer rows.
  Integer-only unsatisfiable instances (for example `2n = 1`) need not have a
  Farkas witness. Resource bounds can also stop the search; `:unknown` does not
  certify a model. Successful candidate checking does not replace the missing
  general checker-to-goal theorem or the separate evidence reconstruction.
  """

  @max_steps 4_096

  @typedoc "A linear form: `{constant, %{variable_index => coefficient}}`."
  @type form :: {integer(), %{non_neg_integer() => integer()}}

  @typedoc "An atom: `sum(coefficients * x) <= bound` (or `< bound`)."
  @type linear_atom :: {form(), :le | :lt}

  @typedoc "A candidate contradiction witness, or an inconclusive search."
  @type result ::
          {:prf, [non_neg_integer()]}
          | :unknown

  @doc """
  Find nonnegative multipliers deriving a contradiction from the supplied rows.

  Returns `{:prf, multipliers}` where the multipliers are one non-negative
  natural per atom in `hyps ++ [negate(goal)]` (the checker's own order), or
  `:unknown` when the input is unsupported or no witness was found
  within the step ceiling.
  """
  @spec solve([linear_atom()]) :: result()
  def solve(atoms) when is_list(atoms) do
    if length(atoms) <= @max_steps and Enum.all?(atoms, &valid_atom?/1) do
      indexed =
        atoms
        |> Enum.map(&normalize/1)
        |> Enum.with_index()
        |> Enum.map(fn {atom, index} -> {atom, %{index => 1}} end)

      case Enum.find(indexed, fn {atom, _} -> manifest_contradiction?(atom) end) do
        {_atom, witness} -> {:prf, dense(witness, length(atoms))}
        nil -> eliminate(indexed, variables(indexed), 0, length(atoms))
      end
    else
      :unknown
    end
  end

  @doc "Normalize strict integer rows and remove zero coefficients."
  def normalize({{bound, coefficients}, relation}) do
    bound = if relation == :lt, do: bound - 1, else: bound
    coefficients = Map.reject(coefficients, fn {_index, coefficient} -> coefficient == 0 end)
    {{bound, coefficients}, :le}
  end

  @doc "Independently recompute a candidate's nonnegative combination; this is not goal evidence."
  def valid_witness?(atoms, multipliers) when is_list(atoms) and is_list(multipliers) do
    length(atoms) == length(multipliers) and Enum.all?(atoms, &valid_atom?/1) and
      Enum.all?(multipliers, &(is_integer(&1) and &1 >= 0)) and
      Enum.zip(atoms, multipliers)
      |> Enum.reduce({{0, %{}}, :le}, fn {atom, multiplier}, acc ->
        add(acc, scale(normalize(atom), multiplier))
      end)
      |> manifest_contradiction?()
  end

  def valid_witness?(_atoms, _multipliers), do: false

  defp valid_atom?({{bound, coefficients}, relation}) when is_integer(bound) and is_map(coefficients) do
    relation in [:le, :lt] and
      Enum.all?(coefficients, fn {index, coefficient} ->
        is_integer(index) and index >= 0 and is_integer(coefficient)
      end)
  end

  defp valid_atom?(_atom), do: false

  @doc "Negate an atom: `not (lhs ≤ rhs)` is `rhs < lhs`, and dually."
  @spec negate(linear_atom()) :: linear_atom()
  def negate({{constant, coefficients}, :le}), do: {{-constant - 1, negate_map(coefficients)}, :le}
  def negate({{constant, coefficients}, :lt}), do: {{-constant, negate_map(coefficients)}, :le}

  @doc "True when an atom is `0 ≤ c` with `c < 0`, i.e. a manifest contradiction."
  @spec manifest_contradiction?(linear_atom()) :: boolean()
  def manifest_contradiction?({{constant, coefficients}, :le}) do
    map_size(coefficients) == 0 and constant < 0
  end

  def manifest_contradiction?(_atom), do: false

  @doc "Build `form ≤ 0` from an affine form `{constant, coefficients}`."
  @spec atom_le(form()) :: linear_atom()
  def atom_le({constant, coefficients}), do: {{-constant, coefficients}, :le}

  @doc "An atom asserting `form < 0`."
  @spec atom_lt(form()) :: linear_atom()
  def atom_lt({constant, coefficients}), do: {{-constant, coefficients}, :lt}

  # -- Fourier–Motzkin -------------------------------------------------------
  #
  # Eliminate one variable at a time. Each step keeps the atoms that do not
  # mention the variable and adds one combination per (lower, upper) pair, which
  # is the standard Fourier–Motzkin rule.
  #
  # The witness is carried alongside each atom as a sparse
  # `%{original_index => multiplier}` map, so a chain of combinations stays
  # positionally aligned with the checker's own atom list (`hyps ++ [negate(goal)]`)
  # no matter how many synthetic atoms the elimination introduced.
  defp eliminate(atoms, [], _steps, size) do
    case Enum.find(atoms, fn {atom, _witness} -> manifest_contradiction?(atom) end) do
      {_atom, witness} -> {:prf, dense(witness, size)}
      nil -> :unknown
    end
  end

  defp eliminate(atoms, [variable | rest], steps, size) when steps <= @max_steps do
    {lowers, uppers, others} = partition(atoms, variable)

    pairs = length(lowers) * length(uppers)

    if steps + pairs + 1 > @max_steps or length(others) + pairs > @max_steps do
      :unknown
    else
      combined =
        for {lower, lower_witness} <- lowers,
            {upper, upper_witness} <- uppers do
          combine(lower, lower_witness, upper, upper_witness, variable)
        end

      next = others ++ combined

      if Enum.any?(next, fn {atom, _} -> manifest_contradiction?(atom) end),
        do: eliminate(next, [], steps + pairs + 1, size),
        else: eliminate(next, rest, steps + pairs + 1, size)
    end
  end

  defp eliminate(_atoms, _variables, _steps, _size), do: :unknown

  # Witness maps are initialized once, at solve/1. Replacing a combined map
  # with a fresh singleton on later elimination rounds loses its provenance.
  defp partition(indexed_atoms, variable) do
    Enum.reduce(indexed_atoms, {[], [], []}, fn {atom, witness}, {lowers, uppers, others} ->
      case Map.get(elem(atom, 0) |> elem(1), variable, 0) do
        coefficient when coefficient > 0 -> {[{atom, witness} | lowers], uppers, others}
        coefficient when coefficient < 0 -> {lowers, [{atom, witness} | uppers], others}
        0 -> {lowers, uppers, [{atom, witness} | others]}
      end
    end)
  end

  # Combine a lower bound (`c_lower * x + rest_lower <= 0` with `c_lower > 0`)
  # with an upper bound (`c_upper * x + rest_upper <= 0` with `c_upper < 0`):
  # multiply the lower by `-c_upper` and the upper by `c_lower`, then add. The
  # variable cancels, and both multipliers are positive, which is exactly the
  # non-negative combination a Farkas witness requires.
  defp combine(lower, lower_witness, upper, upper_witness, variable) do
    lower_coefficient = Map.fetch!(coefficients(lower), variable)
    upper_coefficient = Map.fetch!(coefficients(upper), variable)
    lower_scale = -upper_coefficient
    upper_scale = lower_coefficient

    combined = add(scale(lower, lower_scale), scale(upper, upper_scale))
    witness = merge_witness(scale_witness(lower_witness, lower_scale), scale_witness(upper_witness, upper_scale))
    {drop_variable(combined, variable), witness}
  end

  defp coefficients({{_constant, coefficients}, _relation}), do: coefficients

  defp scale({{constant, coefficients}, relation}, factor) do
    {{constant * factor, Map.new(coefficients, fn {k, v} -> {k, v * factor} end)}, relation}
  end

  defp scale_witness(witness, factor),
    do: Map.new(witness, fn {index, multiplier} -> {index, multiplier * factor} end)

  defp merge_witness(left, right),
    do: Map.merge(left, right, fn _index, a, b -> a + b end)

  # Render the sparse witness as the dense positional list the checker indexes.
  defp dense(witness, size) do
    Enum.map(0..(size - 1)//1, fn index -> Map.get(witness, index, 0) end)
  end

  defp add({{constant_a, coefficients_a}, relation_a}, {{constant_b, coefficients_b}, relation_b}) do
    coefficients =
      Map.merge(coefficients_a, coefficients_b, fn _k, a, b -> a + b end)
      |> Enum.reject(fn {_k, v} -> v == 0 end)
      |> Map.new()

    {{constant_a + constant_b, coefficients}, strictest(relation_a, relation_b)}
  end

  defp strictest(:lt, _other), do: :lt
  defp strictest(_other, :lt), do: :lt
  defp strictest(_a, _b), do: :le

  defp drop_variable({{constant, coefficients}, relation}, variable) do
    {{constant, Map.delete(coefficients, variable)}, relation}
  end

  # `solve/1` receives the atoms already in the checker's own order
  # (`hyps ++ [negate(goal)]`); the elimination below carries each atom with its
  # ORIGINAL position so the multipliers stay aligned with that list.
  defp variables(indexed_atoms) do
    indexed_atoms
    |> Enum.flat_map(fn {atom, _index} -> Map.keys(coefficients(atom)) end)
    |> Enum.uniq()
    |> Enum.sort()
  end

  defp negate_map(coefficients), do: Map.new(coefficients, fn {k, v} -> {k, -v} end)
end
