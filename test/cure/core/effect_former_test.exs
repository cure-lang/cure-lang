defmodule Cure.Core.EffectFormerTest do
  @moduledoc """
  The inert `Effect` type former and its two term formers `pure`/`bind`
  (design `2026-07-09-effect-type-former-design.md` §3, §3.1, §3.2).

  Three new Core nodes — `{:effect_type, t}` (`Effect(T)`),
  `{:effect_pure, a}` (`pure(a)`) and `{:effect_bind, e, k}` (`bind(e, k)`) —
  are added as an **uninterpreted signature**: the kernel learns to *type*
  them and `Conv`/`Normalise` compare them by structural congruence, but
  **nothing reduces them**. In particular there is NO left-identity monad law:
  `bind(pure(a), k)` is NOT definitionally equal to `k(a)` (or to anything the
  effect would produce), because `{:veffect_*}` are distinct value
  constructors and `Eval` never applies `k`.

  None of the three nodes binds a variable itself; `k` is an ordinary function
  term (a `{:lam, …}`), so the `bind` node's own de Bruijn depth is flat.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Builtins, Context, Conv, Env, Kernel, MetaCheck, Serialize, Term}
  alias Cure.Elab.{Erase, Subst}

  @omega Cure.Core.Grade.unrestricted()

  # Effect(Int) as a term and as its type-value.
  defp effect_int, do: {:effect_type, {:data, :"Std.Int#Int", [], []}}
  defp effect_int_val, do: {:veffect_type, {:vdata, :"Std.Int#Int", []}}

  # pure(3) : Effect(Int)
  defp pure3, do: {:effect_pure, {:int_lit, 3}}

  # A well-typed continuation `λ x:Int. pure(x)` and an ill-typed one
  # `λ x:Int. x` (returns Int, not Effect(Int)).
  defp k_ok, do: {:lam, @omega, {:data, :"Std.Int#Int", [], []}, {:effect_pure, {:var, 0}}}
  defp k_bad, do: {:lam, @omega, {:data, :"Std.Int#Int", [], []}, {:var, 0}}

  # bind(pure(3), k)
  defp bind_ok, do: {:effect_bind, pure3(), k_ok()}
  defp bind_bad, do: {:effect_bind, pure3(), k_bad()}

  # The env seeds the `:int` builtin (to type int literals) and registers the
  # canonical `Std.Int#Int` family (payload of Effect(Int)).
  defp empty, do: Context.empty(Builtins.seed(Env.empty()))

  describe "formation — Effect : Type ℓ → Type ℓ" do
    test "Effect(Int) infers at Type 0 (level-preserving)" do
      assert {:ok, {:vtype, 0}} = Kernel.infer(empty(), effect_int())
    end

    test "Effect(Int) checks at Type 0" do
      assert :ok = Kernel.check(empty(), effect_int(), {:vtype, 0})
    end

    test "Effect over a non-type is rejected" do
      assert {:error, _} = Kernel.infer(empty(), {:effect_type, {:int_lit, 3}})
    end
  end

  describe "introduction — pure(a) : Effect(A)" do
    test "pure(3) infers at Effect(Int)" do
      assert {:ok, {:veffect_type, {:vdata, :"Std.Int#Int", []}}} = Kernel.infer(empty(), pure3())
    end

    test "pure(3) checks at Effect(Int)" do
      assert :ok = Kernel.check(empty(), pure3(), effect_int_val())
    end

    test "pure(3) does NOT check at Effect(Float)" do
      assert {:error, _} = Kernel.check(empty(), pure3(), {:veffect_type, {:vfloat_type}})
    end
  end

  describe "sequencing — bind(e, k) : Effect(B)" do
    test "bind(pure(3), λx:Int. pure(x)) infers at Effect(Int)" do
      assert {:ok, {:veffect_type, {:vdata, :"Std.Int#Int", []}}} = Kernel.infer(empty(), bind_ok())
    end

    test "bind(pure(3), λx:Int. pure(x)) checks at Effect(Int)" do
      assert :ok = Kernel.check(empty(), bind_ok(), effect_int_val())
    end

    test "an ill-typed continuation (k returns Int, not Effect) is rejected in infer mode" do
      assert {:error, _} = Kernel.infer(empty(), bind_bad())
    end

    test "an ill-typed continuation is rejected in check mode too" do
      assert {:error, _} = Kernel.check(empty(), bind_bad(), effect_int_val())
    end
  end

  describe "inertness — no monad laws (the load-bearing property)" do
    test "bind(pure(3), λx. pure(x)) is NOT definitionally equal to pure(3)" do
      # Left identity `bind(pure a, k) ≡ k(a)` must NOT hold: distinct value
      # constructors, no reduction. Direct conversion:
      refute Conv.conv?(bind_ok(), pure3(), [], 0)

      # …and on their FULL normal forms — inertness must survive normalization.
      nf_bind = Kernel.normalize(empty(), bind_ok())
      nf_pure = Kernel.normalize(empty(), pure3())
      refute nf_bind == nf_pure
      refute Conv.conv?(nf_bind, nf_pure, [], 0)
    end

    test "bind never applies its continuation — pure's payload is not substituted" do
      # If `bind` reduced, the nf would mention `3` where `k` uses its arg; it
      # must instead keep `bind`/`pure`/`λ` structurally intact.
      assert {:effect_bind, {:effect_pure, {:int_lit, 3}},
              {:lam, @omega, {:data, :"Std.Int#Int", [], []}, {:effect_pure, {:var, 0}}}} =
               Kernel.normalize(empty(), bind_ok())
    end
  end

  describe "congruence — same node, pointwise-convertible children" do
    test "structurally equal effect terms are convertible" do
      assert Conv.conv?(pure3(), {:effect_pure, {:int_lit, 3}}, [], 0)
      assert Conv.conv?(effect_int(), {:effect_type, {:data, :"Std.Int#Int", [], []}}, [], 0)
      assert Conv.conv?(bind_ok(), bind_ok(), [], 0)
    end

    test "a differing subterm makes two effect terms non-convertible" do
      refute Conv.conv?(pure3(), {:effect_pure, {:int_lit, 4}}, [], 0)
      refute Conv.conv?(effect_int(), {:effect_type, {:float_type}}, [], 0)
      refute Conv.conv?(bind_ok(), {:effect_bind, {:effect_pure, {:int_lit, 4}}, k_ok()}, [], 0)
    end

    test "an effect term is not convertible with a non-effect term of the same shape" do
      refute Conv.conv?(pure3(), {:int_lit, 3}, [], 0)
    end
  end

  describe "shape — term?/1" do
    test "accepts the three well-formed effect nodes" do
      assert Term.term?(effect_int())
      assert Term.term?(pure3())
      assert Term.term?(bind_ok())
    end

    test "rejects wrong-arity malformations" do
      refute Term.term?({:effect_type})
      refute Term.term?({:effect_pure})
      refute Term.term?({:effect_bind, pure3()})
      # A non-term child is rejected recursively.
      refute Term.term?({:effect_type, {:var, -1}})
      refute Term.term?({:effect_bind, pure3(), {:var, -1}})
    end
  end

  describe "nf idempotence" do
    test "nf(nf(t)) == nf(t) on effect terms" do
      for t <- [effect_int(), pure3(), bind_ok()] do
        once = Kernel.normalize(empty(), t)
        assert Kernel.normalize(empty(), once) == once
      end
    end
  end

  # A new Core node must be threaded through EVERY structural pass, not just the
  # kernel typing path — Elixir does not raise on a stale catch-all, so a walker
  # that silently skips effect nodes is the recorded migration hazard. The deep
  # walkers (Conv/Normalise/Quote/Validator/Certificate/positivity) use fail-
  # closed generic descent and were already safe; these two did not.
  describe "structural completeness — S-expr serialization and the progress harness" do
    test "the S-expression serializer round-trips every effect node" do
      for t <- [effect_int(), pure3(), bind_ok()] do
        assert {:ok, ^t} = Serialize.decode(Serialize.encode(t))
      end
    end

    test "the progress harness treats a normalized effect term as canonical" do
      # `pure(3) : Effect(Int)` is well-typed and is its own normal form, whose
      # head is the canonical `pure` — `canonical_head?` must recognise it, else
      # a sound effectful term is misreported as stuck.
      assert MetaCheck.progresses?(empty(), pure3())
      assert MetaCheck.type_preserved?(empty(), pure3())
    end
  end

  describe "elaborator walkers" do
    test "substitution and shifting recurse through pure and bind" do
      term = {:effect_bind, {:effect_pure, {:var, 0}}, {:lam, @omega, {:data, :"Std.Int#Int", [], []}, {:var, 1}}}

      assert {:effect_bind, {:effect_pure, {:var, 1}}, {:lam, @omega, {:data, :"Std.Int#Int", [], []}, {:var, 2}}} =
               Subst.shift(term, 1, 0)

      assert {:effect_bind, {:effect_pure, {:int_lit, 7}},
              {:lam, @omega, {:data, :"Std.Int#Int", [], []}, {:int_lit, 7}}} =
               Subst.instantiate(term, [{:int_lit, 7}])
    end

    test "hole detection does not stop at an effect node" do
      refute Erase.has_hole?(pure3())
      assert Erase.has_hole?({:effect_type, {:hole, :under_type}})
      assert Erase.has_hole?({:effect_bind, {:effect_pure, {:int_lit, 1}}, {:hole, :continuation}})
    end
  end
end
