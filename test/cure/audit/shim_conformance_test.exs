defmodule Cure.Audit.ShimConformanceTest do
  use ExUnit.Case, async: false
  alias Cure.Audit.ShimConformance, as: SC

  # Phase 1 of the axiom-surface program. The ledger (Phase 0) counts what a
  # module assumes without proof; this checks the `CURE RUNTIME` axioms against
  # the Elixir that implements them, for as long as that Elixir exists.
  #
  # The output that matters is not pass/fail but the PARTITION (spec §5.3):
  # which axioms are true, which are repairable by changing a Cure signature,
  # and which cannot be discharged at all without the `Effect` former.

  test "the harness executes every CURE RUNTIME axiom except Std.Http's four" do
    executed = length(SC.axioms())
    excluded = length(SC.excluded())

    assert executed == 34
    assert excluded == 4

    # Std.Regex is now a pure Cure value and no longer contributes seven shim
    # axioms to this transitional runtime audit. `Std.Json` went the same way in
    # `8643613b` — rebuilt on the exact literal protocols, so `encode/decode/
    # num_of_int` stopped being externs and left the table with them.
    assert executed + excluded == 38

    for {_mfa, reason} <- SC.excluded(), do: assert(reason == "network I/O")
  end

  describe "the partition" do
    setup do
      %{partition: SC.classify()}
    end

    test "time.now and time.utc_now are effectful and cannot be repaired by rewriting",
         %{partition: p} do
      assert {:effectful, failures} = p[{:cure_std_time, :now, 0}]
      assert {:effectful, _} = p[{:cure_std_time, :utc_now, 0}]

      # Referential transparency is precisely the property that detects a clock.
      assert Keyword.has_key?(failures, :referential_transparency)
    end

    test "crdt.lww_value now inhabits its declared type", %{partition: p} do
      # It used to be declared `fn lww_value(r: LWWRegister) -> t` and return the
      # atom `:empty` for an unset register — at `t = Int`, not an integer. The
      # harness found it; the repair changed the signature to `-> Option(t)`, so
      # an empty register reads as `None()` (the one-tuple `{:none}`) and every
      # sample now conforms.
      assert {:conformant, []} = p[{:cure_std_crdt, :lww_value, 1}]
    end

    test "every other executed axiom is conformant on all four properties", %{partition: p} do
      known = [
        {:cure_std_time, :now, 0},
        {:cure_std_time, :utc_now, 0}
      ]

      offenders =
        for {mfa, {verdict, failures}} <- p,
            mfa not in known,
            verdict != :conformant,
            do: {mfa, verdict, failures}

      assert offenders == [], """
      Axioms that failed a property without a recorded expectation:

      #{Enum.map_join(offenders, "\n", fn {mfa, v, f} -> "  #{inspect(mfa)} => #{v}: #{inspect(f)}" end)}
      """
    end

    test "no axiom is unexpectedly pure or unexpectedly conformant", %{partition: p} do
      # If a `:effectful` or `:type_defect` axiom starts passing, someone fixed
      # it and this table is stale. That is good news that must not pass silently.
      stale =
        for {mfa, {v, _}} <- p, v in [:unexpectedly_pure, :unexpectedly_conformant], do: {mfa, v}

      assert stale == [], "stale expectations (the axiom was repaired): #{inspect(stale)}"
    end
  end

  describe "the properties themselves" do
    test "or_add is referentially transparent and touches no hidden state" do
      # The bug that motivated the harness. Before 0377252 it minted ORSet tags
      # from a process-dictionary counter: two calls with equal arguments
      # returned unequal sets, and the counter was per-process while tags are
      # per-node.
      axiom = Enum.find(SC.axioms(), &(&1.mfa == {:cure_std_crdt, :or_add, 4}))
      results = SC.check(axiom)

      assert results[:referential_transparency] == :ok
      assert results[:no_hidden_state] == :ok
    end

    test "forall_shrunk is total — a failing property is a value, not a raise" do
      axiom = Enum.find(SC.axioms(), &(&1.mfa == {:cure_std_test, :forall_shrunk, 3}))
      results = SC.check(axiom)

      assert results[:totality] == :ok
      assert results[:type_conformance] == :ok
    end
  end
end
