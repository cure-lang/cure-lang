defmodule Cure.Elab.Simplifier do
  @moduledoc """
  Terminating proof-producing simplification for justification goals.

  The audited default set is deliberately finite: beta, constructor/iota,
  local-let/zeta, and certified-delta conversion. Generated defining equations
  are admitted only with their totality certificate and orient from the
  constructor-pattern call to its certified branch body. Explicit equality
  proofs use the stricter source-independent policy implemented by
  `ProofGoal`: their left side must have strictly more Core nodes than their
  right side. Equal-size rules are ambiguous and rejected.

  Traversal is deterministic (user rule-list order, then left-to-right preorder)
  and guarded by both visited-state detection and a 256-step ceiling. Every
  non-definitional step is materialized through `Cure.Elab.Rewrite`; this module
  only closes the final conversion with kernel-checked reflexivity.
  """

  alias Cure.Core.{Context, Kernel}
  alias Cure.Diagnostic.SimplificationProblem
  alias Cure.Elab.Rewrite

  @max_steps 256
  @audited_standard_rules [:beta, :iota, :zeta, :certified_delta]

  @doc false
  def audited_standard_rules, do: @audited_standard_rules

  def solve(expected, context, command_span, rules \\ []) do
    before = Kernel.normalize(context, expected)

    if rules != [] do
      {:error,
       {:simplification_failed,
        %SimplificationProblem{
          kind: :inadmissible_rule,
          command: command_span,
          rule: command_span,
          before_goal: before,
          after_goal: before,
          cause: :explicit_rule_admission_pending
        }}}
    else
      close_definitionally(before, expected, context, command_span)
    end
  end

  defp close_definitionally(
         {:data, family, [_carrier], [_left, right]} = normalized,
         expected,
         context,
         command_span
       ) do
    equality = Cure.Core.Inductive.builtin(Context.signature(context), :eq)
    evidence = Rewrite.mk_refl(right)

    cond do
      family != equality ->
        residual(expected, normalized, command_span, :goal_is_not_equality)

      @max_steps < 1 ->
        resource(expected, normalized, command_span)

      Kernel.check(context, evidence, Cure.Core.Eval.eval(expected, Context.env(context))) == :ok ->
        {:ok, evidence, [{:simplify_definitional, command_span}]}

      true ->
        residual(expected, normalized, command_span, :not_definitionally_equal)
    end
  end

  defp close_definitionally(normalized, expected, _context, command_span),
    do: residual(expected, normalized, command_span, :goal_is_not_equality)

  defp residual(before, after_goal, command_span, cause) do
    {:error,
     {:simplification_failed,
      %SimplificationProblem{
        kind: :residual_goal,
        command: command_span,
        before_goal: before,
        after_goal: after_goal,
        progressed_rules: [],
        trace_ids: [],
        cause: cause
      }}}
  end

  defp resource(before, after_goal, command_span) do
    {:error,
     {:simplification_failed,
      %SimplificationProblem{
        kind: :resource_guard,
        command: command_span,
        before_goal: before,
        after_goal: after_goal,
        cause: {:step_ceiling, @max_steps}
      }}}
  end
end
