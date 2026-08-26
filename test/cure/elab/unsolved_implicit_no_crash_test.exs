defmodule Cure.Elab.UnsolvedImplicitNoCrashTest do
  use ExUnit.Case, async: true

  # A higher-order implicit (`{P : Nat -> Type}`) that first-order unification
  # cannot solve leaves `P` as an unsolved `{:meta, _}` in the expected type
  # `P(y)`. The elaborator must REJECT cleanly (Cure lacks Miller/pattern
  # unification) — it must NOT hand the `{:meta, _}`-bearing type to the trusted
  # `Eval.eval`, which has no `{:meta, _}` clause and crashes the kernel.
  #
  # (When higher-order pattern unification lands, ledger #10, this flips to accept
  # and moves to the oracle as a `cure_stricter → same` graduation.)
  @src """
  mod HoUnsolved
    type Nat = Zero | Suc(Nat)
    fn subst({P: (Nat) -> Type}, {x: Nat}, {y: Nat}, e: Eq(Nat, x, y), px: P(x)) -> P(y) =
      rewrite e in px
    type Vec(a: Type) indices (n: Nat)
      vnil : Vec(a, Zero)
      vcons : a -> Vec(a, n) -> Vec(a, Suc(n))
    fn use(v: Vec(Nat, Suc(Zero)), e: Eq(Nat, Suc(Zero), Suc(Zero))) -> Vec(Nat, Suc(Zero)) =
      subst(e, v)
  end
  """

  test "an unsolvable higher-order implicit rejects cleanly instead of crashing the kernel" do
    result =
      try do
        Cure.Elab.Program.elaborate(@src)
      rescue
        e -> {:raised, Exception.message(e)}
      end

    assert match?({:error, _}, result),
           "expected a clean elaboration error, got: #{inspect(result, limit: 8)}"
  end
end
