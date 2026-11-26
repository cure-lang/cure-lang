defmodule Cure.Elab.TacticTest do
  @moduledoc """
  Phase 2 of `docs/PATH_TO_LEAN4_PLAN.md`: the tactic monad.

  These tests exercise the combinators against SYNTHETIC goals rather than real
  proofs. That is deliberate: the combinators are pure control flow over the
  `{:ok, goals} | {:error, reason}` shape, and testing them against real
  elaboration would couple this suite to the elaborator's reach -- so a
  combinator bug could hide behind an unrelated elaboration failure.

  The real commands are pinned separately by
  `test/cure/compiler/dependent_proof_surface_test.exs` and
  `test/cure/elab/proof_ergonomics_test.exs`.
  """

  use ExUnit.Case, async: true

  alias Cure.Elab.Tactic

  # A goal is opaque to the combinators; only its identity matters here.
  defp goal(id), do: %{id: id}

  # A tactic that closes the goal.
  defp closes, do: fn _goal -> {:ok, []} end

  # A tactic that leaves the goal open, unchanged.
  defp keeps, do: fn goal -> {:ok, [goal]} end

  # A tactic that replaces the goal with a marked one.
  defp marks(label) do
    fn goal -> {:ok, [Map.update!(goal, :id, &"#{label}:#{&1}")]} end
  end

  # A tactic that always fails.
  defp fails(reason), do: fn _goal -> {:error, reason} end

  describe "of_command_result/2" do
    test "a closed command result closes the goal" do
      assert {:ok, []} = Tactic.of_command_result({:closed, :evidence, [:trace]}, goal(:a))
    end

    test "an open command result returns the transformed goal" do
      next = goal(:b)
      assert {:ok, [^next]} = Tactic.of_command_result({:open, next}, goal(:a))
    end

    test "an error passes through" do
      assert {:error, :boom} = Tactic.of_command_result({:error, :boom}, goal(:a))
    end
  end

  describe "seq/2" do
    test "runs the second tactic on the goal the first leaves open" do
      # Both marks apply, in order: the second sees the first's output.
      assert {:ok, [%{id: "c:b:a"}]} = Tactic.seq(marks("b"), marks("c")).(goal("a"))
    end

    test "does NOT run the second tactic once the first closes the goal" do
      # This is what makes "a command after the goal is closed" unreachable
      # rather than a silent no-op.
      assert {:ok, []} = Tactic.seq(closes(), fails(:should_not_run)).(goal(:a))
    end

    test "a failure in the first tactic short-circuits" do
      assert {:error, :first} = Tactic.seq(fails(:first), fails(:second)).(goal(:a))
    end

    test "a failure in the second tactic surfaces" do
      assert {:error, :second} = Tactic.seq(keeps(), fails(:second)).(goal(:a))
    end
  end

  describe "or_else/2" do
    test "uses the second tactic when the first fails" do
      assert {:ok, [%{id: "b:a"}]} = Tactic.or_else(fails(:nope), marks("b")).(goal("a"))
    end

    test "does not run the second tactic when the first succeeds" do
      assert {:ok, []} = Tactic.or_else(closes(), fails(:should_not_run)).(goal(:a))
    end

    test "backtracks to the ORIGINAL goal, never a half-transformed one" do
      # A failed tactic must not leave the goal partially applied, or failure
      # would be order-dependent and the proof state unsound to inspect.
      half_then_fail = fn goal ->
        _ = Map.update!(goal, :id, &"half:#{&1}")
        {:error, :failed_after_mutation}
      end

      assert {:ok, [%{id: "b:a"}]} = Tactic.or_else(half_then_fail, marks("b")).(goal("a"))
    end
  end

  describe "run_all/2" do
    test "an empty goal list is already closed" do
      assert {:ok, []} = Tactic.run_all(keeps(), [])
    end

    test "threads over every goal" do
      assert {:ok, [%{id: "x:a"}, %{id: "x:b"}]} = Tactic.run_all(marks("x"), [goal("a"), goal("b")])
    end

    test "stops at the first failure and preserves THAT error" do
      # Masking the first error with a later one would hide the real cause.
      flaky = fn
        %{id: "a"} -> {:ok, [%{id: "a"}]}
        _ -> {:error, :second_failed}
      end

      assert {:error, :second_failed} = Tactic.run_all(flaky, [goal("a"), goal("b"), goal("c")])
    end
  end

  describe "repeat/2" do
    test "closing on the first pass yields closed" do
      assert {:ok, []} = Tactic.repeat(closes()).(goal(:a))
    end

    test "a tactic that makes no progress terminates rather than looping" do
      assert {:ok, [%{id: :a}]} = Tactic.repeat(keeps()).(goal(:a))
    end

    test "repeats until the goal closes" do
      # Closes only once the id has been marked twice.
      two_steps = fn
        %{id: "x:x:a"} -> {:ok, []}
        %{id: id} -> {:ok, [%{id: "x:#{id}"}]}
      end

      assert {:ok, []} = Tactic.repeat(two_steps).(goal("a"))
    end

    test "respects the step bound instead of diverging" do
      always_progresses = fn goal -> {:ok, [Map.update!(goal, :id, &"x:#{&1}")]} end

      assert {:ok, [open]} = Tactic.repeat(always_progresses, 3).(goal("a"))
      assert open.id == "x:x:x:a"
    end
  end

  describe "try_/1" do
    test "a failure becomes no change" do
      assert {:ok, [%{id: :a}]} = Tactic.try_(fails(:nope)).(goal(:a))
    end

    test "a success passes through" do
      assert {:ok, []} = Tactic.try_(closes()).(goal(:a))
    end
  end

  describe "closed?/1 and open_goals/1" do
    test "an empty goal list is closed" do
      assert Tactic.closed?({:ok, []})
      refute Tactic.closed?({:ok, [goal(:a)]})
      refute Tactic.closed?({:error, :boom})
    end

    test "open_goals extracts the remaining goals, and nothing from an error" do
      assert Tactic.open_goals({:ok, [goal(:a)]}) == [goal(:a)]
      assert Tactic.open_goals({:ok, []}) == []
      assert Tactic.open_goals({:error, :boom}) == []
    end
  end
end
