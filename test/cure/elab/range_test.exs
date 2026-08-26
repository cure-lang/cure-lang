defmodule Cure.Elab.RangeTest do
  @moduledoc """
  Integer ranges `a..b` (exclusive) and `a..=b` (inclusive) in the dependent
  pipeline. The classic codegen lowered them to `lists:seq/2`; here they desugar
  to a call to a REAL total structurally-recursive helper — `Std.Nat.range_upto`
  / `range_upto_incl`, which recurses on a `Nat` fuel — so a range is an ordinary
  `List(Int)` value with no opaque `lists:seq` postulate. This mirrors Idris's
  `enumFromTo` (a total recursive Prelude function). The only trusted primitive is
  the `Int -> Nat` count cast (`Std.Nat.of_int`, clamped `max(0, ·)`), exactly
  where Idris marks `integerToNat` total.

  Coverage split:

    * The SHIPPED helpers (`Std.Nat.of_int`/`range_from`/`range_upto{,_incl}`) are
      proven to dependent-elaborate and emit cleanly by `dependent_emit_parity_test`
      / `dependent_elaboration_parity_test` (`nat` is `@green`).

    * Runtime behaviour is proven HERE against an all-dependent module. `Nat`
      erases differently in the two codegens (classic = tagged constructors,
      dependent = a machine integer), and the auto-prelude `Std.Nat` currently
      ships CLASSIC-compiled, so a dependent caller cannot yet reach the shipped
      `range_upto` at run time — that seam closes when the stdlib goes
      dependent-compiled at the #18 rip-out. Until then the desugar + recursion +
      `of_int` boundary + `Nat` erasure are exercised end-to-end by inlining the
      helpers as locals in one dependent compilation unit (`of_int` stays the real
      `Std.Nat` extern), which is exactly the post-#18 single-pipeline shape.

  Part of the pre-#18 surface-construct port batch (see
  memory pre18-surface-construct-gaps).
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.{Emit, Program}

  # A single dependent compilation unit: the `Std.Nat` range helpers inlined as
  # locals (so the whole chain is dependent-erased and self-consistent) plus a
  # caller `r` that uses the range surface, driving the elaborator's desugar.
  @helpers """
    @extern(:cure_std_nat, :of_int, 1)
    fn of_int(i: Int) -> Nat

    fn range_from(start: Int, count: Nat) -> List(Int) =
      match count
        Z() -> []
        S(k) -> [start | range_from(start + 1, k)]

    fn range_upto(from: Int, to: Int) -> List(Int) =
      range_from(from, of_int(to - from))

    fn range_upto_incl(from: Int, to: Int) -> List(Int) =
      range_from(from, of_int(to - from + 1))
  """

  defp compile!(caller, mod) do
    src = "mod M\n" <> @helpers <> "\n" <> caller <> "\nend\n"
    assert {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, emit_events: false)
    assert {:ok, env} = Program.elaborate(src)
    origins = Program.import_origins(ast)

    fns = [:r, :range_upto, :range_upto_incl, :range_from, :of_int]

    assert {:ok, m} =
             Emit.compile_and_load(env, module: mod, functions: fns, origins: origins)

    m
  end

  test "exclusive range a..b builds [a, .., b-1]" do
    m = compile!("fn r(a: Int, b: Int) -> List(Int) = a..b", :"Cure.Test.RangeExcl")
    assert apply(m, :r, [1, 4]) == [1, 2, 3]
    assert apply(m, :r, [0, 1]) == [0]
  end

  test "exclusive range with a >= b is empty (no runtime crash on negative gap)" do
    m = compile!("fn r(a: Int, b: Int) -> List(Int) = a..b", :"Cure.Test.RangeEmpty")
    assert apply(m, :r, [5, 5]) == []
    assert apply(m, :r, [7, 2]) == []
  end

  test "inclusive range a..=b builds [a, .., b]" do
    m = compile!("fn r(a: Int, b: Int) -> List(Int) = a..=b", :"Cure.Test.RangeIncl")
    assert apply(m, :r, [1, 4]) == [1, 2, 3, 4]
    assert apply(m, :r, [3, 3]) == [3]
    assert apply(m, :r, [3, 2]) == []
  end
end
