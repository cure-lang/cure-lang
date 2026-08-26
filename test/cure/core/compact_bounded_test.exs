defmodule Cure.Core.CompactBoundedTest do
  # Compact Bounded literals: `Bounded(n)` stays a real INDEXED inductive (ctors
  # :First / :Next, each carrying an erased implicit index `{m : Nat}`) but a
  # literal value is a machine-integer `{:vbounded, k}` / term `{:bounded_lit, k}`,
  # definitionally equal to the k-fold `Next`-tower over `First` (Lean's `Fin n` =
  # a compact `Nat` + a `< n` witness). Peeling (`Eval.bounded_to_ctor`) is the
  # single literal→ctor rule, the exact analogue of Nat's `First`≙`Z`/`Next`≙`S`.
  # These tests pin the representation contract added to the TCB: typing (with the
  # `0 <= k < n` bound check), conversion in BOTH directions, eliminator peeling,
  # read-back, serialization, and that a full-plane codepoint stays O(1) — one
  # integer, never a 1.1M-node tower. This is the antibody for the kernel change.
  use ExUnit.Case, async: true

  alias Cure.Core.{Kernel, Context, Eval, Conv, Normalise, Serialize, Term, Value, Inductive}
  alias Cure.Elab.Program

  # A sig/context in which the canonical `Bounded` family is registered (it is not
  # part of `Builtins.seed/1`; only the `@builtin(:bounded)` decl in Std.Bounded
  # introduces it), obtained by elaborating a one-line module that uses it.
  defp sig do
    {:ok, env} =
      Program.elaborate("mod M\n  use Std.Bounded\n  fn f(x: Bounded(10)) -> Bounded(10) = x\nend\n")

    env
  end

  defp ctx, do: Context.empty(sig())

  # The kernel's inferred type for `{:bounded_lit, k}` is `Bounded(k+1)` (the
  # minimal bound), i.e. the value `{:vdata, :Bounded, [{:vnat, k+1}]}`.
  defp bounded_val(bound), do: {:vdata, Inductive.builtin(sig(), :bounded), [{:vnat, bound}]}

  describe "shape + typing" do
    test "term? / value? accept non-negative literals and reject negatives" do
      assert Term.term?({:bounded_lit, 0})
      assert Term.term?({:bounded_lit, 128_512})
      refute Term.term?({:bounded_lit, -1})
      assert Value.value?({:vbounded, 7})
      refute Value.value?({:vbounded, -3})
    end

    test "a Bounded literal infers the minimal Bounded(k+1) family type" do
      assert {:ok, ty} = Kernel.infer(ctx(), {:bounded_lit, 96})
      assert ty == bounded_val(97)
    end

    test "check accepts an in-range literal and rejects an out-of-range one" do
      assert :ok == Kernel.check(ctx(), {:bounded_lit, 9}, bounded_val(10))
      assert {:error, _} = Kernel.check(ctx(), {:bounded_lit, 10}, bounded_val(10))
      assert {:error, _} = Kernel.check(ctx(), {:bounded_lit, 20}, bounded_val(10))
    end

    test "a Bounded literal is NOT an Int (no primitive-type confusion)" do
      assert {:error, _} = Kernel.check(ctx(), {:bounded_lit, 5}, {:vint_type})
    end
  end

  describe "conversion: literal ⇄ First/Next tower are interconvertible both ways" do
    test "eval peels one layer: vbounded k ⇄ its First/Next ctor value" do
      # Declaration-arity peel: the erased implicit index `m` is the leading field
      # (First: m=0; Next over {:vbounded,3}: m=3), the predecessor stays compact.
      assert {:vctor, :First, [{:vnat, 0}]} == Eval.bounded_to_ctor({:vbounded, 0})
      assert {:vctor, :Next, [{:vnat, 3}, {:vbounded, 2}]} == Eval.bounded_to_ctor({:vbounded, 3})
    end

    test "vbounded k ≡ its k-fold Next-tower value, both directions" do
      s = sig()
      assert Conv.conv_values?({:vbounded, 0}, Eval.bounded_to_ctor({:vbounded, 0}), 0, s)
      assert Conv.conv_values?(Eval.bounded_to_ctor({:vbounded, 0}), {:vbounded, 0}, 0, s)
      assert Conv.conv_values?({:vbounded, 3}, Eval.bounded_to_ctor({:vbounded, 3}), 0, s)
      assert Conv.conv_values?(Eval.bounded_to_ctor({:vbounded, 3}), {:vbounded, 3}, 0, s)
    end

    test "lit n ≡ lit n by O(1) equality; distinct literals differ" do
      s = sig()
      assert Conv.conv?({:bounded_lit, 9}, {:bounded_lit, 9}, [], 0, s)
      refute Conv.conv?({:bounded_lit, 9}, {:bounded_lit, 10}, [], 0, s)
    end

    test "a literal is NOT convertible with a tower of a different height" do
      s = sig()
      refute Conv.conv_values?({:vbounded, 2}, Eval.bounded_to_ctor({:vbounded, 3}), 0, s)
      refute Conv.conv_values?(Eval.bounded_to_ctor({:vbounded, 3}), {:vbounded, 2}, 0, s)
    end
  end

  describe "eliminator peeling" do
    # case b of { First -> lit 42 ; Next k -> k }  — a predecessor / is-succ probe.
    # First binds only the erased index (arity 1); Next binds {m}, pred (arity 2),
    # its present predecessor at de Bruijn index 0.
    defp pred_case(scrut),
      do: {:case, scrut, {:type, 0}, [{:First, 1, {:bounded_lit, 42}}, {:Next, 2, {:var, 0}}]}

    test "case on lit 0 selects the First branch" do
      assert {:vbounded, 42} == Eval.eval(pred_case({:bounded_lit, 0}), [])
    end

    test "case on lit (k+1) selects the Next branch and binds the COMPACT predecessor" do
      assert {:vbounded, 4} == Eval.eval(pred_case({:bounded_lit, 5}), [])
    end
  end

  describe "read-back keeps it compact" do
    test "nf of a Bounded literal reads back to a compact literal, not a tower" do
      assert {:bounded_lit, 6} == Normalise.nf(ctx(), {:bounded_lit, 6})
    end

    test "nf reduces a case on a Bounded literal" do
      c = {:case, {:bounded_lit, 5}, {:type, 0}, [{:First, 1, {:bounded_lit, 42}}, {:Next, 2, {:var, 0}}]}
      assert {:bounded_lit, 4} == Normalise.nf(ctx(), c)
    end
  end

  describe "serialization round-trips" do
    test "encode/decode preserves a Bounded literal" do
      assert {:ok, {:bounded_lit, 128_512}} == Serialize.decode(Serialize.encode({:bounded_lit, 128_512}))
    end

    test "external (JSON-able) round-trip" do
      assert {:bounded_lit, 7} == Term.from_external(Term.to_external({:bounded_lit, 7}))
    end
  end

  describe "the payoff: a full-plane codepoint stays O(1)" do
    test "the '😀' codepoint is one compact integer, typed/converted instantly" do
      cp = ?😀
      assert cp == 128_512
      # Elaborate the module ONCE up front (that cost is not what we are timing);
      # the timed block exercises only the kernel operations on the compact literal.
      s = sig()
      c = Context.empty(s)
      char_ty = bounded_val(1_114_112)

      {micros, _} =
        :timer.tc(fn ->
          assert {:ok, _} = Kernel.infer(c, {:bounded_lit, cp})
          assert :ok == Kernel.check(c, {:bounded_lit, cp}, char_ty)
          assert Conv.conv?({:bounded_lit, cp}, {:bounded_lit, cp}, [], 0, s)
          assert {:bounded_lit, ^cp} = Normalise.nf(c, {:bounded_lit, cp})
        end)

      # No tower is ever built: the value is a single {:vbounded, n}. A 1.1M-node
      # `Next`-tower would take seconds / OOM; the generous 500ms bound stays true
      # even under full-suite parallel CPU contention while still catching a tower.
      assert micros < 500_000
    end
  end
end
