defmodule Cure.Diagnostic.ProofGoalStateTest do
  @moduledoc """
  Phase 1 of `docs/PATH_TO_LEAN4_PLAN.md`: goal-state introspection.

  Before this phase, `E110` (an unfinished `because` block) reported only that
  the block ended open. The author had to re-derive the residual goal by hand
  from the chain's last endpoint.

  These tests pin that the diagnostic now states the **obligation**: the goal
  type that remains, and the local facts available to close it.

  The assertions are deliberately on the RENDERED diagnostic text rather than on
  the problem struct. A struct-level assertion would pass even if the adapter
  dropped the goal on the floor -- which is exactly the bug this phase fixes.
  """

  use ExUnit.Case, async: true

  alias Cure.Diagnostic.{Adapter, ProofChainMismatchProblem, Span}

  @span %Span{
    source_id: "Test.cure",
    path: "Test.cure",
    start_byte: 0,
    end_byte: 1,
    start_line: 1,
    start_column: 1,
    end_line: 1,
    end_column: 2
  }

  defp render(problem) do
    Adapter.Proof.from_error({:proof_chain_mismatch, problem}, [])
  end

  defp flatten(%{body: body}), do: body |> inspect() |> to_string()

  describe "unfinished justification reports the remaining goal" do
    test "the residual goal type appears in the diagnostic body" do
      problem = %ProofChainMismatchProblem{
        kind: :unfinished_justification,
        step_index: 0,
        justification: @span,
        residual_goal: {:int_type},
        cause: {:open_goal, []}
      }

      text = flatten(render(problem))

      assert text =~ "Remaining goal",
             "the diagnostic must name the remaining goal, got: #{text}"

      assert text =~ "Int",
             "the residual goal TYPE must be rendered, got: #{text}"
    end

    test "local facts in scope are listed by name" do
      problem = %ProofChainMismatchProblem{
        kind: :unfinished_justification,
        step_index: 0,
        justification: @span,
        residual_goal: {:int_type},
        cause: {:open_goal, ["ih", "hypothesis"]}
      }

      text = flatten(render(problem))

      assert text =~ "Local facts in scope"
      assert text =~ "ih"
      assert text =~ "hypothesis"
    end

    test "an empty local context says so explicitly rather than listing nothing" do
      problem = %ProofChainMismatchProblem{
        kind: :unfinished_justification,
        step_index: 0,
        justification: @span,
        residual_goal: {:int_type},
        cause: {:open_goal, []}
      }

      text = flatten(render(problem))

      assert text =~ "No local facts are in scope"
    end

    test "a missing residual goal degrades without crashing" do
      problem = %ProofChainMismatchProblem{
        kind: :unfinished_justification,
        step_index: 0,
        justification: @span,
        residual_goal: nil,
        cause: {:open_goal, []}
      }

      text = flatten(render(problem))

      refute text =~ "Remaining goal",
             "with no residual goal there is nothing to claim, got: #{text}"
    end
  end

  describe "other E110 kinds are unchanged" do
    test "an adjacent-endpoint mismatch does not claim a remaining goal" do
      problem = %ProofChainMismatchProblem{
        kind: :adjacent_endpoints,
        step_index: 1,
        justification: @span,
        residual_goal: {:int_type},
        cause: :carrier_mismatch
      }

      text = flatten(render(problem))

      refute text =~ "Remaining goal",
             "only an unfinished justification has a remaining goal, got: #{text}"
    end
  end
end
