defmodule Cure.Stdlib.StalePascalCaseShimsRedTest do
  @moduledoc """
  RED tests for cluster 7 of the "ripout-tail" stdlib-shim audit: four
  `@extern` Elixir shims still hand-encode Option/Result with PascalCase tags
  (`:None`, `{:Some, _}`, `{:Ok, _}`, `{:Error, _}`) left over from before the
  migration flipped the canonical wire tags to lowercase OTP atoms
  (`:none`, `{:some, _}`, `{:ok, _}`, `{:error, _}`), as already done correctly
  in `lib/cure/stdlib/cure_std_char.ex`.

  Every assertion below encodes the DESIRED post-fix behavior. Each currently
  fails because the production shim still returns the stale PascalCase tag —
  see the verbatim `mix test` output attached to each finding for proof.
  """
  use ExUnit.Case, async: true

  describe "cure_std_crdt.lww_value/1 (lib/cure/stdlib/cure_std_crdt.ex:158-159)" do
    test "an empty (never-set) register returns the lowercase :none, not :None" do
      empty = :cure_std_crdt.lww_empty(:n1)
      assert :cure_std_crdt.lww_value(empty) == :none
    end

    test "a set register returns {:some, value}, not {:Some, value}" do
      empty = :cure_std_crdt.lww_empty(:n1)
      set = :cure_std_crdt.lww_set(empty, :hello, 1, :n1)
      assert :cure_std_crdt.lww_value(set) == {:some, :hello}
    end
  end

  describe "cure_std_time.parse_iso8601/1" do
    # `String` is nominal and erases to `{:String, chars}`; the shim is an
    # `@extern` target, so it receives that shape and never a bare binary.
    test "a valid ISO 8601 timestamp returns {:ok, instant}, not {:Ok, instant}" do
      assert {:ok, %{__struct__: :instant, micros: _}} =
               :cure_std_time.parse_iso8601({:String, ~c"2026-04-21T15:11:46Z"})
    end

    test "an invalid string returns {:error, _}, not {:Error, _}" do
      assert {:error, _reason} = :cure_std_time.parse_iso8601({:String, ~c"not-a-date"})
    end

    test "a non-binary argument returns {:error, _}, not {:Error, _}" do
      assert {:error, _reason} = :cure_std_time.parse_iso8601(42)
    end
  end

  describe "cure_std_test.forall_shrunk/3 (lib/cure/stdlib/cure_std_test.ex:21-29)" do
    test "a property that always holds returns {:ok, :unit}, not {:Ok, :unit}" do
      gen = fn _ -> 7 end
      property = fn _ -> true end
      assert {:ok, :unit} = :cure_std_test.forall_shrunk(gen, property, 5)
    end

    test "a property that never holds returns {:error, minimal}, not {:Error, minimal}" do
      gen = fn _ -> 100 end
      property = fn _ -> false end
      assert {:error, _minimal} = :cure_std_test.forall_shrunk(gen, property, 5)
    end
  end
end
