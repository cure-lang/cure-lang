defmodule Cure.Elab.Solver do
  @moduledoc "Untrusted goal closers; every result is checked against the original goal."

  alias Cure.Core.{Context, Env, Eval, Inductive, Kernel, Normalise}
  alias Cure.Diagnostic.ProofChainMismatchProblem
  alias Cure.Elab.{Elaborator, Omega, ProofSearch}
  alias Cure.Elab.Omega.{Certificate, Linear, Proof}
  alias Cure.MetaAST.Metadata

  @decision :"Std.Decision#Decision"
  @yes :"Std.Decision#Yes"
  @no :"Std.Decision#No"
  @bool_decider :"Std.Decision#equivalent?"

  @check_lia :"Std.Proof.LinearArithmetic#check_lia_candidate"

  def solve({:solver_command, meta, arguments}, expected, names, ctx, env) do
    mode = Keyword.fetch!(meta, :solver)

    result =
      case {mode, arguments} do
        {strategy, []} when strategy in [:search, :positivity, :assumption] ->
          ProofSearch.resolve_strategy(expected, ctx, env, strategy)

        {:decide, arguments} ->
          decide(arguments, expected, names, ctx, env)

        {:omega, []} ->
          omega(expected, names, ctx, env)

        _ ->
          {:error, :invalid_solver_arguments}
      end

    with {:ok, evidence} <- result,
         :ok <- Kernel.check(ctx, evidence, Eval.eval(expected, Context.env(ctx))) do
      {:ok, evidence}
    else
      :none -> failure(meta, expected, mode, :no_evidence)
      {:error, cause} -> failure(meta, expected, mode, cause)
    end
  end

  # -- omega -----------------------------------------------------------------

  # A candidate Boolean check is necessary for this producer's output, but it
  # does not supply premise evidence or imply the source goal. Admission also
  # requires a separately reconstructed, kernel-checked IntOrder proof.
  defp omega(expected, names, ctx, env) do
    with :ok <- checker_available(ctx),
         hypotheses = Linear.reify_hypotheses(ctx, names),
         {:ok, problems} <- Linear.obligations(hypotheses, expected, ctx, env),
         :ok <- validate_candidates(problems, ctx),
         {:ok, evidence} <- Proof.solve(expected, ctx, env) do
      {:ok, evidence}
    else
      :outside_fragment -> {:error, {:omega_outside_fragment, expected}}
      :unknown -> {:error, :omega_no_checked_reconstruction}
      {:error, _} = error -> error
    end
  end

  # Use the signature of the actual judgment. Do not silently rehydrate or
  # certify another environment and then check evidence against the old one.
  defp checker_available(ctx) do
    signature = Context.signature(ctx)

    cond do
      not Map.has_key?(signature.defs, @check_lia) ->
        {:error, :omega_not_in_scope}

      not Env.certified?(signature, @check_lia) ->
        {:error, :omega_checker_uncertified}

      true ->
        case Kernel.check_def(signature, @check_lia) do
          :ok -> :ok
          {:error, reason} -> {:error, {:omega_checker_rejected, reason}}
        end
    end
  end

  defp validate_candidates(problems, ctx) do
    Enum.reduce_while(problems, :ok, fn {atoms, goal}, :ok ->
      {hypotheses, [_negated_goal]} = Enum.split(atoms, -1)

      result =
        with {:ok, multipliers} <- find_witness(atoms),
             {:ok, candidate} <- Certificate.term(hypotheses, goal, multipliers),
             :ok <- Kernel.check(ctx, candidate, Kernel.bool_type_value(Context.signature(ctx))) do
          case Normalise.whnf(ctx, candidate, delta: :certified, fuel: 16_384) do
            {:ctor, :"Std.Bool#True", []} -> :ok
            {:ctor, :"Std.Bool#False", []} -> {:error, :omega_invalid_candidate}
            :fuel_exhausted -> {:error, :omega_checker_resource_guard}
            _ -> {:error, :omega_checker_stuck}
          end
        end

      case result do
        :ok -> {:cont, :ok}
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  defp find_witness(atoms) do
    case Omega.solve(atoms) do
      {:prf, multipliers} ->
        if Omega.valid_witness?(atoms, multipliers),
          do: {:ok, multipliers},
          else: {:error, :omega_producer_invalid_witness}

      :unknown ->
        {:error, :omega_no_witness}
    end
  end

  # -- decide ----------------------------------------------------------------

  defp decide(arguments, expected, names, ctx, env) do
    decision_type = {:data, @decision, [expected], []}
    expected_value = Eval.eval(decision_type, Context.env(ctx))

    with true <- Map.has_key?(env.families, @decision),
         {:ok, decision} <- decision_term(arguments, expected, decision_type, names, ctx, env),
         :ok <- Kernel.check(ctx, decision, expected_value) do
      # Only certified Core reduction can expose Yes. A host Bool is never evidence.
      case Normalise.whnf(ctx, decision, delta: :certified, fuel: 4096) do
        {:ctor, @yes, [evidence]} -> {:ok, evidence}
        {:ctor, @no, _arguments} -> {:error, :decision_no}
        :fuel_exhausted -> {:error, :decision_resource_guard}
        _ -> {:error, :decision_stuck}
      end
    else
      false -> {:error, :decision_not_in_scope}
      {:error, _} = error -> error
    end
  end

  defp decision_term([expression], _expected, decision_type, names, ctx, env),
    do: Elaborator.elaborate_expr_checked(expression, decision_type, names, ctx, env)

  defp decision_term([], expected, _decision_type, _names, ctx, env) do
    with {:data, equality, [carrier], [left, right]} <- Normalise.whnf(ctx, expected),
         true <- equality == Inductive.builtin(env, :eq),
         true <- carrier == {:data, Inductive.builtin(env, :bool), [], []},
         true <- Map.has_key?(env.defs, @bool_decider) and Env.certified?(env, @bool_decider) do
      {:ok, {:app, {:app, {:global, @bool_decider}, left}, right}}
    else
      _ -> {:error, :no_decision_inferred}
    end
  end

  defp decision_term(_arguments, _expected, _decision_type, _names, _ctx, _env),
    do: {:error, :invalid_solver_arguments}

  defp failure(meta, expected, mode, cause) do
    info = Metadata.source_info(meta)

    {:error,
     {:proof_chain_mismatch,
      %ProofChainMismatchProblem{
        kind: :solver_failed,
        step_index: 0,
        justification: info && info.whole,
        expected: expected,
        residual_goal: expected,
        cause: {:solver_failed, mode, cause}
      }}}
  end
end
