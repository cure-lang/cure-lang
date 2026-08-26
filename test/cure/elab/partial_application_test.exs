defmodule Cure.Elab.PartialApplicationTest do
  @moduledoc """
  HOLE 2: partial application of a function that carries IMPLICIT (erased)
  parameters. `konst : {a} -> a -> Int -> a` applied to a single explicit
  argument (`konst(7)`) is under-saturated by one explicit slot. The implicit
  paths refused under-saturation with `:too_few_arguments` (the annotated case)
  or mis-aligned the explicit arg to the leading implicit slot with
  `{:conversion_failure, {:int_type}, {:type, 0}}` (the higher-order case).

  Both configurations reach CHECKED elaboration against a Π expected type — the
  annotated `let f : (Int) -> Int = konst(7)` directly, and `ap(konst(7))` via
  the bidirectional-application retry that checks the argument against `ap`'s
  domain. The fix eta-expands an under-saturated implicit-carrying call in
  checking mode: `konst(7)` becomes `fn(x) -> konst(7, x)`, whose residual binder
  domains come from the expected Π, reducing partial application to the ordinary
  saturated path. The kernel re-checks the synthesized lambda, so nothing here is
  trusted.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  @konst "  fn konst({a: Type}, x: a, y: Int) -> a = x\n"
  @ap "  fn ap(g: (Int) -> Int) -> Int = g(5)\n"

  test "under-saturated implicit call checked against an annotated function type runs" do
    src =
      "mod M\n" <>
        @konst <>
        @ap <>
        "  fn use_annot() -> Int =\n" <>
        "    let f: (Int) -> Int = konst(7)\n" <>
        "    ap(f)\n" <>
        "end\n"

    assert {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.M", functions: [:use_annot, :ap, :konst])
    # konst(7) ignores its argument and returns 7; ap feeds it 5.
    assert apply(mod, :use_annot, []) == 7
  end

  test "under-saturated implicit call passed to a higher-order function runs" do
    src =
      "mod M\n" <>
        @konst <>
        @ap <>
        "  fn use_hof() -> Int = ap(konst(7))\n" <>
        "end\n"

    assert {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.M", functions: [:use_hof, :ap, :konst])
    assert apply(mod, :use_hof, []) == 7
  end

  test "under-saturated by TWO explicit slots eta-expands to a nested lambda and runs" do
    src =
      "mod M\n" <>
        "  fn first({a: Type}, w: a, x: Int, y: Int) -> a = w\n" <>
        "  fn use_two() -> Int =\n" <>
        "    let g: (Int) -> (Int) -> Int = first(7)\n" <>
        "    g(1)(2)\n" <>
        "end\n"

    assert {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.M", functions: [:use_two, :first])
    assert apply(mod, :use_two, []) == 7
  end

  test "REGRESSION GUARD — a fully saturated implicit call is unchanged" do
    src =
      "mod M\n" <>
        @konst <>
        "  fn top() -> Int = konst(42, 3)\n" <>
        "end\n"

    assert {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.M", functions: [:top, :konst])
    assert apply(mod, :top, []) == 42
  end
end
