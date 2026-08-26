defmodule Cure.Elab.PinPatternTest do
  @moduledoc """
  Pin patterns `^x` on a primitive scrutinee in the dependent pipeline. A pin arm
  matches when the scrutinee EQUALS the current value of `x` — the same shape as a
  literal arm, only the compared value is a bound variable instead of a constant.
  It reuses the literal-chain lowering: `match n | ^x -> a | _ -> b` becomes
  `bool_elim (n == x) a b`, choosing the type-directed equality twin
  (`int_eq`/`float_eq`, or `struct_eq` for a `Bounded`/`Char` scrutinee) exactly
  like a literal arm. A trailing catch-all is required (a pin is never known to be
  exhaustive), matching the classic pin+guard, which always needs a fallback.

  Part of the pre-#18 surface-construct port batch (see
  memory pre18-surface-construct-gaps): every construct the classic codegen
  supports must work through the sole dependent pipeline before classic is ripped
  out, or deleting classic silently removes a live language feature.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Emit, Program}

  test "integer pin arm matches on equality, else falls through" do
    src = """
    mod M
      fn is_it(x: Int, n: Int) -> Int = match n
        ^x -> 1
        _ -> 0
    end
    """

    assert {:ok, env} = Program.elaborate(src)

    assert {:ok, mod} =
             Emit.compile_and_load(env, module: :"Cure.Test.PinInt", functions: [:is_it])

    assert apply(mod, :is_it, [5, 5]) == 1
    assert apply(mod, :is_it, [5, 7]) == 0
    assert apply(mod, :is_it, [-3, -3]) == 1
  end

  test "a char/bounded pin arm uses the polymorphic equality path" do
    src = """
    mod M
      fn same(c: Char, d: Char) -> Int = match d
        ^c -> 1
        _ -> 0
    end
    """

    assert {:ok, env} = Program.elaborate(src)

    assert {:ok, mod} =
             Emit.compile_and_load(env, module: :"Cure.Test.PinChar", functions: [:same])

    # Char erases to its code point; ?a = 97, ?b = 98.
    assert apply(mod, :same, [?a, ?a]) == 1
    assert apply(mod, :same, [?a, ?b]) == 0
  end
end
