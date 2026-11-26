defmodule Cure.Elab.Solver do
  @moduledoc "Untrusted goal closers; every result is checked against the original goal."

  alias Cure.Core.{Context, Env, Eval, Inductive, Kernel, Normalise}
  alias Cure.Diagnostic.ProofChainMismatchProblem
  alias Cure.Elab.{Elaborator, ProofSearch}
  alias Cure.MetaAST.Metadata

  @decision :"Std.Decision#Decision"
  @yes :"Std.Decision#Yes"
  @no :"Std.Decision#No"
  @bool_decider :"Std.Decision#equivalent?"

  def solve({:solver_command, meta, arguments}, expected, names, ctx, env) do
    mode = Keyword.fetch!(meta, :solver)

    result =
      case {mode, arguments} do
        {strategy, []} when strategy in [:search, :positivity] ->
          ProofSearch.resolve_strategy(expected, ctx, env, strategy)

        {:decide, arguments} ->
          decide(arguments, expected, names, ctx, env)

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
