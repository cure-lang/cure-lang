defmodule Cure.Core.CoverageIndexNormalizationTest do
  @moduledoc """
  Kernel coverage is up to DEFINITIONAL EQUALITY: a branch whose constructor
  index cannot unify with the *normal form* of the scrutinee's index must be
  discharged as impossible, even when the scrutinee index arrives stuck.

  The motivating shape is `Vector.take`. Written with `with n` (Idris-style
  convoy) so the sibling `xs : Vector(a, plus(n, m))` refines per branch, the
  `S(k)` branch gives `xs : Vector(a, plus(S(k), m))`. The inner `match xs` must
  drop the `empty` case — `empty : Vector(a, Z)` and `plus(S(k), m)` reduces to
  `S(plus(k, m))`, whose `S` head refutes `Z`. But the index reached the kernel's
  `check_coverage` STUCK as `plus(S(k), m)` (a neutral application), so `unify`
  compared `Z` against a stuck `plus(...)`, could not refute it, kept `empty`, and
  the kernel rejected the eliminator as non-exhaustive (`:coverage`, surfaced as
  `:branch_type` from the enclosing `with`).

  The fix normalizes the scrutinee index inside `unify_indices` before unifying.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  test "take on Vector(a, plus(n,m)) via `with` elaborates — impossible `empty` discharged under a reducible index" do
    src = """
    mod M
      use Std.Nat
      use Std.Vector

      fn take({a: Type}, n: Nat, {m: Nat}, xs: Vector(a, plus(n, m))) -> Vector(a, n) =
        with n
          Z() -> empty()
          S(k) ->
            match xs
              prepend(x, rest) -> prepend(x, take(k, rest))
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end
