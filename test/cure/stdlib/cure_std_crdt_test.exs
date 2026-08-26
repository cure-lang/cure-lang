defmodule :cure_std_crdt_test do
  use ExUnit.Case, async: true

  # Shared helper: assert commutativity, associativity, and idempotence
  # of the named merge function given three sample CRDT states.
  defp assert_merge_laws(merge, [a, b, c]) do
    # Commutativity.
    assert merge.(a, b) == merge.(b, a), "merge not commutative"

    # Associativity.
    left = merge.(merge.(a, b), c)
    right = merge.(a, merge.(b, c))
    assert left == right, "merge not associative"

    # Idempotence.
    assert merge.(a, a) == a, "merge not idempotent"
  end

  describe "GCounter" do
    test "increments, reads, and merges" do
      a = :cure_std_crdt.g_increment(:cure_std_crdt.g_empty(), :n1, 3)
      b = :cure_std_crdt.g_increment(:cure_std_crdt.g_empty(), :n2, 4)
      assert :cure_std_crdt.g_value(a) == 3
      assert :cure_std_crdt.g_value(b) == 4

      merged = :cure_std_crdt.g_merge(a, b)
      assert :cure_std_crdt.g_value(merged) == 7
    end

    test "merge picks the per-node max" do
      a = :cure_std_crdt.g_increment(:cure_std_crdt.g_empty(), :n1, 5)
      b = :cure_std_crdt.g_increment(:cure_std_crdt.g_empty(), :n1, 2)
      merged = :cure_std_crdt.g_merge(a, b)
      assert :cure_std_crdt.g_value(merged) == 5
    end

    test "obeys the CRDT merge laws" do
      a = :cure_std_crdt.g_increment(:cure_std_crdt.g_empty(), :n1, 2)
      b = :cure_std_crdt.g_increment(:cure_std_crdt.g_empty(), :n2, 3)
      c = :cure_std_crdt.g_increment(a, :n3, 4)
      assert_merge_laws(&:cure_std_crdt.g_merge/2, [a, b, c])
    end
  end

  describe "PNCounter" do
    test "supports increments and decrements" do
      c = :cure_std_crdt.pn_empty()
      c = :cure_std_crdt.pn_increment(c, :n1, 10)
      c = :cure_std_crdt.pn_decrement(c, :n1, 3)
      assert :cure_std_crdt.pn_value(c) == 7
    end

    test "merges component-wise" do
      a = :cure_std_crdt.pn_increment(:cure_std_crdt.pn_empty(), :n1, 5)
      b = :cure_std_crdt.pn_decrement(:cure_std_crdt.pn_empty(), :n2, 2)
      merged = :cure_std_crdt.pn_merge(a, b)
      assert :cure_std_crdt.pn_value(merged) == 3
    end

    test "obeys the CRDT merge laws" do
      a = :cure_std_crdt.pn_increment(:cure_std_crdt.pn_empty(), :n1, 4)
      b = :cure_std_crdt.pn_decrement(:cure_std_crdt.pn_empty(), :n2, 2)
      c = :cure_std_crdt.pn_increment(b, :n1, 7)
      assert_merge_laws(&:cure_std_crdt.pn_merge/2, [a, b, c])
    end
  end

  describe "ORSet" do
    test "add, remove, read" do
      s = :cure_std_crdt.or_empty()
      s = :cure_std_crdt.or_add(s, :n1, 1, :apple)
      s = :cure_std_crdt.or_add(s, :n1, 2, :banana)
      assert :cure_std_crdt.or_value(s) == [:apple, :banana]

      s = :cure_std_crdt.or_remove(s, :apple)
      assert :cure_std_crdt.or_value(s) == [:banana]
    end

    test "add wins over a concurrent remove that did not observe it" do
      # n1 adds :apple
      a = :cure_std_crdt.or_add(:cure_std_crdt.or_empty(), :n1, 1, :apple)
      # n2 adds :apple too, then removes it
      b = :cure_std_crdt.or_add(:cure_std_crdt.or_empty(), :n2, 1, :apple)
      b = :cure_std_crdt.or_remove(b, :apple)

      merged = :cure_std_crdt.or_merge(a, b)
      # n2's remove only tombstoned its own tag; n1's add is still live.
      assert :cure_std_crdt.or_value(merged) == [:apple]
    end

    test "obeys the CRDT merge laws" do
      a = :cure_std_crdt.or_add(:cure_std_crdt.or_empty(), :n1, 1, :apple)
      b = :cure_std_crdt.or_add(:cure_std_crdt.or_empty(), :n2, 1, :banana)
      c = :cure_std_crdt.or_remove(a, :apple)
      assert_merge_laws(&:cure_std_crdt.or_merge/2, [a, b, c])
    end

    test "or_add is referentially transparent" do
      s = :cure_std_crdt.or_empty()
      assert :cure_std_crdt.or_add(s, :n1, 1, :apple) == :cure_std_crdt.or_add(s, :n1, 1, :apple)
    end

    test "or_add leaves the process dictionary untouched" do
      before = Process.get()
      :cure_std_crdt.or_add(:cure_std_crdt.or_empty(), :n1, 1, :apple)
      assert Process.get() == before
    end

    test "adds from one replica in different processes do not collide" do
      # Both tasks act as logical replica :n1 — a replica is a node id, not
      # an OS process. Distinct tags must stay distinct across processes.
      add = fn tag, elem ->
        Task.async(fn -> :cure_std_crdt.or_add(:cure_std_crdt.or_empty(), :n1, tag, elem) end)
        |> Task.await()
      end

      apples = add.(1, :apple)
      bananas = add.(2, :banana)

      merged = :cure_std_crdt.or_merge(apples, bananas)
      assert Enum.sort(:cure_std_crdt.or_value(merged)) == [:apple, :banana]

      # Removing :apple must not disturb :banana, even after :banana's
      # originating replica state is merged back in.
      pruned = :cure_std_crdt.or_remove(merged, :apple)
      final = :cure_std_crdt.or_merge(pruned, bananas)
      assert :cure_std_crdt.or_value(final) == [:banana]
    end
  end

  describe "LWWRegister" do
    test "later stamp wins" do
      a = :cure_std_crdt.lww_set(:cure_std_crdt.lww_empty(:n1), :v1, 10, :n1)
      b = :cure_std_crdt.lww_set(:cure_std_crdt.lww_empty(:n2), :v2, 20, :n2)
      merged = :cure_std_crdt.lww_merge(a, b)
      assert :cure_std_crdt.lww_value(merged) == {:some, :v2}
    end

    test "ties break on node ordering" do
      a = :cure_std_crdt.lww_set(:cure_std_crdt.lww_empty(:alpha), :from_alpha, 5, :alpha)
      b = :cure_std_crdt.lww_set(:cure_std_crdt.lww_empty(:beta), :from_beta, 5, :beta)
      merged = :cure_std_crdt.lww_merge(a, b)
      # alpha < beta lexicographically; beta wins because na >= nb in the merge.
      assert :cure_std_crdt.lww_value(merged) == {:some, :from_beta}
    end

    test "obeys the CRDT merge laws" do
      a = :cure_std_crdt.lww_set(:cure_std_crdt.lww_empty(:n1), :v1, 10, :n1)
      b = :cure_std_crdt.lww_set(:cure_std_crdt.lww_empty(:n2), :v2, 5, :n2)
      c = :cure_std_crdt.lww_set(:cure_std_crdt.lww_empty(:n3), :v3, 10, :n3)
      assert_merge_laws(&:cure_std_crdt.lww_merge/2, [a, b, c])
    end

    test "an unset register reads as None(), not as a bare :empty" do
      # `lww_value` is declared `LWWRegister -> Option(t)`. It used to be
      # declared `-> t` and return the atom `:empty`, so at `t = Int` a caller
      # was promised an integer and handed `:empty`. The canonical erasure of
      # the nullary constructor `None()` is the OTP-compatible atom `:none`.
      assert :cure_std_crdt.lww_value(:cure_std_crdt.lww_empty(:n1)) == :none
    end
  end

  describe "MVRegister" do
    test "retains writes from concurrent nodes" do
      a = :cure_std_crdt.mv_write(:cure_std_crdt.mv_empty(), :from_a, 1, :n1)
      b = :cure_std_crdt.mv_write(:cure_std_crdt.mv_empty(), :from_b, 1, :n2)
      merged = :cure_std_crdt.mv_merge(a, b)
      assert Enum.sort(:cure_std_crdt.mv_values(merged)) == [:from_a, :from_b]
    end

    test "later stamp shadows earlier from same node" do
      r = :cure_std_crdt.mv_write(:cure_std_crdt.mv_empty(), :old, 1, :n1)
      r = :cure_std_crdt.mv_write(r, :new, 2, :n1)
      assert :cure_std_crdt.mv_values(r) == [:new]
    end

    test "obeys the CRDT merge laws" do
      a = :cure_std_crdt.mv_write(:cure_std_crdt.mv_empty(), :va, 1, :n1)
      b = :cure_std_crdt.mv_write(:cure_std_crdt.mv_empty(), :vb, 2, :n2)
      c = :cure_std_crdt.mv_write(a, :va2, 3, :n1)
      assert_merge_laws(&:cure_std_crdt.mv_merge/2, [a, b, c])
    end
  end
end
