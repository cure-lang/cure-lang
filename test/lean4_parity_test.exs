# The parity corpus is plain data, not a test module. It must be loaded BEFORE
# `defmodule` so the `for` comprehension that generates one test per case can run
# at compile time -- `Code.require_file` inside the module body would execute at
# runtime, after the tests were already expanded.
Code.require_file("lean4_parity/parity_case.exs", __DIR__)
Code.require_file("lean4_parity/corpus.exs", __DIR__)

defmodule Cure.Lean4ParityTest do
  @moduledoc """
  Runs the Lean-4-parity corpus (`test/lean4_parity/corpus.exs`).

  Each case pins the CURRENT accept/reject behaviour of a Cure program. A
  failure here means **behaviour changed**, and that is exactly the signal we
  want: when a plan phase widens reach, the corresponding pin flips in the same
  commit, so the diff records the semantic change for review.

  When a pin fails, do NOT "fix" the test by relaxing it. Either:

    * the change was intended — flip `:expect` in `corpus.exs` and update
      `docs/LEAN4_PARITY_STATUS.md` in the same commit; or
    * the change was a regression — revert the change that caused it.

  See `docs/PATH_TO_LEAN4_PLAN.md` §10 invariant 8.
  """

  use ExUnit.Case, async: false

  alias Cure.Lean4Parity.{Case, Corpus}

  describe "corpus integrity" do
    test "every case has a unique id" do
      ids = Enum.map(Corpus.all(), & &1.id)
      duplicates = ids -- Enum.uniq(ids)

      assert duplicates == [],
             "duplicate parity case ids: #{inspect(duplicates)}"
    end

    test "every :reject pin carries a reason" do
      missing =
        Corpus.all()
        |> Enum.filter(&(&1.expect == :reject and is_nil(&1.reason)))
        |> Enum.map(& &1.id)

      assert missing == [],
             "these :reject pins have no :reason: #{inspect(missing)}"
    end

    test "every :accept pin names the module it defines" do
      missing =
        Corpus.all()
        |> Enum.filter(&(&1.expect == :accept and is_nil(&1.module)))
        |> Enum.map(& &1.id)

      assert missing == [],
             "these :accept pins name no :module: #{inspect(missing)}"
    end

    test "every case names a gap from the plan's register (G1-G11)" do
      known = MapSet.new([:g1, :g2, :g3, :g4, :g5, :g6, :g7, :g8, :g9, :g10, :g11])

      unknown =
        Corpus.all()
        |> Enum.reject(&MapSet.member?(known, &1.gap))
        |> Enum.map(&{&1.id, &1.gap})

      assert unknown == [], "unknown gap ids: #{inspect(unknown)}"
    end

    test "every case names a Lean-parity axis (L1-L7)" do
      known = MapSet.new([:l1, :l2, :l3, :l4, :l5, :l6, :l7])

      unknown =
        Corpus.all()
        |> Enum.reject(&MapSet.member?(known, &1.axis))
        |> Enum.map(&{&1.id, &1.axis})

      assert unknown == [], "unknown axis ids: #{inspect(unknown)}"
    end
  end

  describe "parity pins" do
    # Embed only the ID, never the struct. Embedding the struct (`@case_ c`)
    # lets the compiler narrow `c.expect` to a literal atom per generated test,
    # which makes the opposite branch statically unreachable -- silently
    # disabling half the assertions and failing `--warnings-as-errors`.
    # Looking the case up at runtime keeps both branches live.
    for %Case{} = c <- Corpus.all() do
      @case_id c.id

      test "#{c.id} — #{c.title}" do
        c = Enum.find(Corpus.all(), fn case_ -> case_.id == @case_id end)
        expect = c.expect
        result = Case.run(c)

        case {expect, result} do
          {:accept, {:accepted, module}} ->
            assert Atom.to_string(module) == c.module,
                   "#{c.id}: expected module #{c.module}, compiled #{inspect(module)}"

          {:accept, {:rejected, reason}} ->
            flunk("""
            #{c.id} is pinned :accept but Cure REJECTED it.

            #{c.title}

            This is a REGRESSION: the program was accepted when the pin was
            recorded. Revert the change that caused it, or -- if the rejection
            is intended -- flip the pin to :reject with a :reason in
            test/lean4_parity/corpus.exs.

            Reason: #{inspect(reason, pretty: true, limit: 20)}
            """)

          {:reject, {:rejected, _reason}} ->
            # Expected. The pin records a measured reach gap.
            :ok

          {:reject, {:accepted, module}} ->
            flunk("""
            #{c.id} is pinned :reject but Cure ACCEPTED it as #{inspect(module)}.

            #{c.title}

            Recorded reason for the rejection:
              #{c.reason}

            If a plan phase intentionally closed this gap, flip the pin to
            :accept with a :module in test/lean4_parity/corpus.exs and update
            docs/LEAN4_PARITY_STATUS.md in the SAME commit -- that diff is the
            review of the semantic change.
            """)
        end
      end
    end
  end

  describe "corpus coverage" do
    test "the corpus pins at least one case per gap it claims to cover" do
      covered = Corpus.all() |> Enum.map(& &1.gap) |> Enum.uniq() |> Enum.sort()

      # G6, G7, G8 and G11 are proof-side/runtime-side obligations with no
      # Cure-source witness; they are tracked in docs/LEAN4_PARITY_STATUS.md
      # instead. Assert that split explicitly so a silently-dropped gap is loud.
      source_pinnable = [:g1, :g2, :g3, :g4, :g5, :g9, :g10]
      proof_side = [:g6, :g7, :g8, :g11]

      assert covered == Enum.sort(source_pinnable)

      assert Enum.all?(proof_side, fn g -> Corpus.for_gap(g) == [] end),
             "G6/G7/G8/G11 must have no Cure-source pins (no source witness exists)"
    end

    test "the corpus spans every Lean-parity axis it can observe" do
      axes = Corpus.all() |> Enum.map(& &1.axis) |> Enum.uniq() |> Enum.sort()

      # L5 (trusted kernel) and L7 (mechanised metatheory) are proof-side
      # properties; L1, L2, L3, L4 and L6 have observable Cure-source witnesses.
      assert axes == [:l1, :l2, :l3, :l4, :l6]
    end
  end
end
