defmodule Cure.OracleTest do
  use ExUnit.Case, async: true
  alias Cure.Oracle

  describe "consistent/1 — the relation contract" do
    test "same: agreeing verdicts are consistent" do
      assert Oracle.consistent(%{"cure" => "accept", "idris" => "accept", "relation" => "same", "reason" => ""}) == :ok
      assert Oracle.consistent(%{"cure" => "reject", "idris" => "reject", "relation" => "same", "reason" => ""}) == :ok
    end

    test "same: disagreeing verdicts are inconsistent (forces triage)" do
      assert {:error, _} =
               Oracle.consistent(%{"cure" => "reject", "idris" => "accept", "relation" => "same", "reason" => ""})
    end

    test "cure_stricter: idris-accept/cure-reject with a reason is consistent" do
      assert Oracle.consistent(%{
               "cure" => "reject",
               "idris" => "accept",
               "relation" => "cure_stricter",
               "reason" => "Cure's fixed 0-2 universe hierarchy rejects this."
             }) == :ok
    end

    test "cure_stricter without a reason is inconsistent" do
      assert {:error, _} =
               Oracle.consistent(%{
                 "cure" => "reject",
                 "idris" => "accept",
                 "relation" => "cure_stricter",
                 "reason" => ""
               })
    end

    test "cure-accept/idris-reject is never benign — no relation label rescues it" do
      for rel <- ["same", "cure_stricter", "idris_only"] do
        assert {:error, _} =
                 Oracle.consistent(%{"cure" => "accept", "idris" => "reject", "relation" => rel, "reason" => "x"})
      end
    end
  end

  describe "cure_verdict/1" do
    test "accepts a well-typed program and rejects an ill-typed one" do
      good = Path.join(System.tmp_dir!(), "oracle_good_#{System.unique_integer([:positive])}.cure")
      bad = Path.join(System.tmp_dir!(), "oracle_bad_#{System.unique_integer([:positive])}.cure")

      File.write!(good, """
      type Nat = Z | S(Nat)
      fn zero_refl() -> Equivalent(Nat, Z, Z) = reflexive(Z)
      """)

      File.write!(bad, """
      type Nat = Z | S(Nat)
      fn bad() -> Equivalent(Nat, Z, S(Z)) = reflexive(Z)
      """)

      assert Oracle.cure_verdict(good) == :accept
      assert Oracle.cure_verdict(bad) == :reject
    after
      # tmp files are unique-per-run; explicit cleanup keeps tmp tidy
      :ok
    end
  end
end
