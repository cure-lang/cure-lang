defmodule Cure.Core.CompactNatTest do
  # Compact Nat literals: `Nat` stays a real inductive (ctors :Z / :S) but a
  # literal is a machine-integer value `{:vnat, n}` / term `{:nat_lit, n}`,
  # definitionally equal to the n-fold `S`-tower over `Z` (Lean kernel Nat / Agda
  # BUILTIN NATURAL). Peeling (`Eval.nat_to_ctor`) is the single literal→ctor
  # rule, reused at every eliminator. These tests pin the representation contract:
  # typing, conversion in BOTH directions, eliminator peeling, read-back, and that
  # a huge codepoint stays O(1) — one integer, never a tower.
  use ExUnit.Case, async: true
  alias Cure.Core.{Builtins, Env, Kernel, Context, Eval, Conv, Normalise, Serialize, Term, Value}
  alias Cure.Elab.{Elaborator, Declarations}

  @nat {:data, :"Std.Nat#Nat", [], []}

  defp ctx, do: Context.empty(Builtins.seed(Env.empty()))
  defp sig, do: Builtins.seed(Env.empty())
  defp nat_val, do: Kernel.nat_type_value(sig())

  # S(S(... Z)) as a Core term of the given depth (the tower form).
  defp tower(0), do: {:ctor, :Z, []}
  defp tower(n) when n > 0, do: {:ctor, :S, [tower(n - 1)]}

  describe "shape + typing" do
    test "term? / value? accept non-negative literals and reject negatives" do
      assert Term.term?({:nat_lit, 0})
      assert Term.term?({:nat_lit, 128_512})
      refute Term.term?({:nat_lit, -1})
      assert Value.value?({:vnat, 7})
      refute Value.value?({:vnat, -3})
    end

    test "a Nat literal infers the canonical Nat family type" do
      assert {:ok, nat} = Kernel.infer(ctx(), {:nat_lit, 5})
      assert nat == nat_val()
    end

    test "check accepts a Nat literal against Nat" do
      assert :ok == Kernel.check(ctx(), {:nat_lit, 5}, nat_val())
    end

    test "a Nat literal is NOT an Int (no primitive-type confusion)" do
      assert {:error, _} = Kernel.check(ctx(), {:nat_lit, 5}, {:vdata, :"Std.Int#Int", []})
      # and a bare Int literal still infers Int, unchanged
      assert {:ok, {:vdata, :"Std.Int#Int", []}} = Kernel.infer(ctx(), {:int_lit, 5})
    end
  end

  describe "conversion: literal ⇄ tower are interconvertible in both directions" do
    test "lit n ≡ the n-fold S-tower (both directions)" do
      s = sig()
      assert Conv.conv?({:nat_lit, 0}, tower(0), [], 0, s)
      assert Conv.conv?(tower(0), {:nat_lit, 0}, [], 0, s)
      assert Conv.conv?({:nat_lit, 3}, tower(3), [], 0, s)
      assert Conv.conv?(tower(3), {:nat_lit, 3}, [], 0, s)
    end

    test "compact Nat is convertible with owner-qualified constructor towers" do
      qualified =
        {:ctor, :"Std.Nat#S", [{:ctor, :"Std.Nat#S", [{:ctor, :"Std.Nat#Z", []}]}]}

      assert Conv.conv?({:nat_lit, 2}, qualified, [], 0, sig())
      assert Conv.conv?(qualified, {:nat_lit, 2}, [], 0, sig())
    end

    test "constructor basename matching never equates different qualified owners" do
      left = {:ctor, :"Left#S", [{:nat_lit, 0}]}
      right = {:ctor, :"Right#S", [{:nat_lit, 0}]}

      refute Conv.conv?(left, right, [], 0, sig())
    end

    test "lit n ≡ lit n by O(1) equality; distinct literals differ" do
      s = sig()
      assert Conv.conv?({:nat_lit, 9}, {:nat_lit, 9}, [], 0, s)
      refute Conv.conv?({:nat_lit, 9}, {:nat_lit, 10}, [], 0, s)
    end

    test "a literal is NOT convertible with a tower of a different height" do
      s = sig()
      refute Conv.conv?({:nat_lit, 2}, tower(3), [], 0, s)
      refute Conv.conv?(tower(3), {:nat_lit, 2}, [], 0, s)
    end
  end

  describe "eliminator peeling" do
    # case n of { Z -> lit 42 ; S k -> k }  — a predecessor / is-succ probe.
    defp pred_case(scrut),
      do: {:case, scrut, {:type, 0}, [{:Z, 0, {:nat_lit, 42}}, {:S, 1, {:var, 0}}]}

    test "case on lit 0 selects the Z branch" do
      assert {:vnat, 42} == Eval.eval(pred_case({:nat_lit, 0}), [])
    end

    test "case on lit (n+1) selects the S branch and binds the COMPACT predecessor" do
      assert {:vnat, 4} == Eval.eval(pred_case({:nat_lit, 5}), [])
    end

    test "compact literals select owner-qualified Nat branches" do
      qualified =
        {:case, {:nat_lit, 2}, {:type, 0}, [{:"Std.Nat#Z", 0, {:nat_lit, 42}}, {:"Std.Nat#S", 1, {:var, 0}}]}

      assert {:vnat, 1} == Eval.eval(qualified, [])
    end

    test "peeling agrees (up to conversion) with the same case run on the S/Z tower" do
      # The literal peel binds a COMPACT predecessor {:vnat, 2}; the tower peel
      # binds a tower predecessor. Both denote 2 — definitionally equal, though
      # not structurally identical. That representation-independence is the point.
      from_lit = Eval.eval(pred_case({:nat_lit, 3}), [])
      from_tower = Eval.eval(pred_case(tower(3)), [])
      assert from_lit == {:vnat, 2}
      assert Conv.conv_values?(from_lit, from_tower, 0, sig())
    end
  end

  describe "read-back keeps it compact" do
    test "nf of a Nat literal reads back to a compact literal, not a tower" do
      assert {:nat_lit, 6} == Normalise.nf(ctx(), {:nat_lit, 6})
    end

    test "nf reduces a case on a Nat literal" do
      c = {:case, {:nat_lit, 5}, {:type, 0}, [{:Z, 0, {:nat_lit, 42}}, {:S, 1, {:var, 0}}]}
      assert {:nat_lit, 4} == Normalise.nf(ctx(), c)
    end
  end

  describe "serialization round-trips" do
    test "encode/decode preserves a Nat literal" do
      assert {:ok, {:nat_lit, 128_512}} == Serialize.decode(Serialize.encode({:nat_lit, 128_512}))
    end

    test "external (JSON-able) round-trip" do
      assert {:nat_lit, 7} == Term.from_external(Term.to_external({:nat_lit, 7}))
    end
  end

  describe "elaborator: type-directed literal lowering" do
    test "an integer literal CHECKED against Nat lowers to a compact nat_lit" do
      s = sig()
      c = Context.empty(s)
      lit = {:literal, [subtype: :integer], 5}
      assert {:ok, {:nat_lit, 5}} = Elaborator.elaborate_expr_checked(lit, @nat, [], c, s)
    end

    test "the same literal checked against Int stays an int_lit (Int is the default)" do
      s = sig()
      c = Context.empty(s)
      lit = {:literal, [subtype: :integer], 5}
      assert {:ok, {:int_lit, 5}} = Elaborator.elaborate_expr_checked(lit, {:data, :"Std.Int#Int", [], []}, [], c, s)
    end

    test "a negative literal is not lowered to Nat (rejected at Nat)" do
      s = sig()
      c = Context.empty(s)
      lit = {:literal, [subtype: :integer], -1}
      assert {:error, _} = Elaborator.elaborate_expr_checked(lit, @nat, [], c, s)
    end
  end

  describe "type-index position: a numeric literal lowers to a compact nat_lit" do
    # A number written in a dependent type index — e.g. the `5` in `Bounded(5)`,
    # or the `0x110000` Char bound in `Bounded(1114112)` — parses as a NAME node
    # `{:variable, [scope: :local], "5"}` (the lexer's integer token stringified).
    # The single type→Core lowering (`Declarations.lower_type/3`, the live path
    # `idx_to_core`) must resolve that to `{:nat_lit, n}`, NOT a phantom
    # `{:global, :"5"}`. Without this the compact-Nat surface payoff never reaches
    # type-index position (the position the Char/Bounded footprint argument needs).
    defp num(n), do: {:variable, [scope: :local], Integer.to_string(n)}

    test "a bare numeric index name lowers to a compact nat_lit" do
      env = Env.empty()
      assert {:ok, {:nat_lit, 5}} = Declarations.lower_type(num(5), [], env)
      # the full-plane Char bound is ONE integer, not a 1.1M-node tower
      assert {:ok, {:nat_lit, 1_114_112}} = Declarations.lower_type(num(1_114_112), [], env)
      assert {:ok, {:nat_lit, 0}} = Declarations.lower_type(num(0), [], env)
    end

    test "the index of an applied type `Bounded(5)` is a compact nat_lit" do
      env = Env.empty()
      # `Bounded` is unregistered here, so the head falls to a global spine — the
      # point is the ARGUMENT: it is `{:nat_lit, 5}`, not the old `{:global, :\"5\"}`.
      ast = {:function_call, [name: "Bounded"], [num(5)]}

      assert {:ok, {:app, {:global, :Bounded}, {:nat_lit, 5}}} =
               Declarations.lower_type(ast, [], env)
    end

    test "a genuine type variable in scope still resolves to its de Bruijn index" do
      # Regression guard: the numeric rule must not shadow real (non-numeric) names.
      env = Env.empty()
      assert {:ok, {:var, 0}} = Declarations.lower_type({:variable, [scope: :local], "n"}, ["n"], env)
    end
  end

  describe "the payoff: a full-plane codepoint stays O(1)" do
    test "the '😀' codepoint is one compact integer, typed/converted instantly" do
      cp = ?😀
      assert cp == 128_512
      c = ctx()

      {micros, _} =
        :timer.tc(fn ->
          assert {:ok, _} = Kernel.infer(c, {:nat_lit, cp})
          assert Conv.conv?({:nat_lit, cp}, {:nat_lit, cp}, [], 0, sig())
          assert {:nat_lit, ^cp} = Normalise.nf(c, {:nat_lit, cp})
        end)

      # No tower is ever built: the value is a single {:vnat, n}. Comfortably sub-ms.
      assert micros < 100_000
    end
  end
end
