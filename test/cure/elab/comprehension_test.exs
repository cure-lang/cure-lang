defmodule Cure.Elab.ComprehensionTest do
  @moduledoc """
  List comprehensions `[e for x <- xs, cond, y <- ys]` in the dependent pipeline.
  The classic codegen lowered them to Erlang list comprehensions; here they
  desugar (in the elaborator, before Core) to the textbook Wadler translation
  over already-supported constructs:

      [e]                         (no qualifiers left — a singleton list)
      flat_map(src, fn(x) -> …)   (a generator `x <- src`)
      if cond then … else []      (a filter)

  so the only library dependency is `flat_map`. Nothing new reaches Core: the
  desugar is pure surface AST → surface AST, then re-elaborated.

  Runtime behaviour is proven HERE against an all-dependent module (the
  established seam-avoiding pattern — see `range_test.exs`): `flat_map`/`append`
  are inlined as locals so the whole unit is dependent-erased and self-consistent,
  which is exactly the post-#18 single-pipeline shape. Cross-module use of the
  shipped `Std.List.flat_map` lights up when the stdlib goes dependent-compiled at
  the #18 rip-out.

  Part of the pre-#18 surface-construct port batch (see
  memory pre18-surface-construct-gaps).
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.{Emit, Program}

  # Monomorphic (Int) `flat_map` + `append` inlined as locals so the desugar's
  # `flat_map` call resolves within one dependent compilation unit.
  @helpers """
    fn append(a: List(Int), b: List(Int)) -> List(Int) =
      match a
        [] -> b
        [h | t] -> [h | append(t, b)]

    fn flat_map(xs: List(Int), f: Int -> List(Int)) -> List(Int) =
      match xs
        [] -> []
        [h | t] -> append(f(h), flat_map(t, f))
  """

  defp compile!(caller, mod) do
    src = "mod M\n" <> @helpers <> "\n" <> caller <> "\nend\n"
    assert {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, emit_events: false)
    assert {:ok, env} = Program.elaborate(src)
    origins = Program.import_origins(ast)

    fns = [:r, :flat_map, :append]

    assert {:ok, m} =
             Emit.compile_and_load(env, module: mod, functions: fns, origins: origins)

    m
  end

  test "map-style comprehension applies the body to each element" do
    m = compile!("fn r(xs: List(Int)) -> List(Int) = [x + 1 for x <- xs]", :"Cure.Test.ComprMap")
    assert apply(m, :r, [[1, 2, 3]]) == [2, 3, 4]
    assert apply(m, :r, [[]]) == []
  end

  test "a filter qualifier drops non-matching elements" do
    m =
      compile!(
        "fn r(xs: List(Int)) -> List(Int) = [x for x <- xs, x > 2]",
        :"Cure.Test.ComprFilter"
      )

    assert apply(m, :r, [[1, 2, 3, 4]]) == [3, 4]
    assert apply(m, :r, [[1, 2]]) == []
  end

  test "two generators form the cartesian product" do
    m =
      compile!(
        "fn r(xs: List(Int), ys: List(Int)) -> List(Int) = [x + y for x <- xs, y <- ys]",
        :"Cure.Test.ComprCartesian"
      )

    assert apply(m, :r, [[0, 10], [1, 2]]) == [1, 2, 11, 12]
    assert apply(m, :r, [[1], []]) == []
  end
end
