defmodule Cure.Stdlib.OpticDependentRunTest do
  @moduledoc """
  End-to-end run of the SHIPPING `lib/std/optic.cure` through the dependent
  pipeline. `Std.Optic` is the statically-typed replacement for the deleted,
  `believe_me`-based `Std.Access`: a single GADT family `Optic(s, a, k)` whose
  kind `k : OpticKind` is a constructor index, so `match`ing an optic refines the
  kind and the eliminators (`view`/`preview`/`over`/`set`) are written once,
  kind-polymorphically, yet stay precisely typed.

  `dependent_elaboration_parity_test.exs` guards that the file *elaborates*
  (`optic` is in `@green`). This pins its *runtime* behaviour: a lens built with
  `lens(get, put)` reads, replaces, and modifies its focus, rebuilding the real
  surrounding structure — so a regression in the cross-module lowering surfaces
  as a wrong answer, not just a type error.

  Implicit type/kind arguments erase, so the runtime arities are `lens/2`,
  `view/2`, `over/3`, `set/3`, `preview/2`. A nullary constructor erases to a
  bare PascalCase atom and a unary one to a tagged tuple, so `preview` yields
  `{:some, focus}` / `:none` (the OTP-lowercase Option representation).
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.{Program, Emit}

  setup_all do
    src = File.read!("lib/std/optic.cure")
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    {:ok, env} = Program.elaborate(src)
    origins = Program.import_origins(ast)

    fns = Program.reachable_def_names(env, [:lens, :view, :set, :over, :preview])

    {:ok, m} =
      Emit.compile_and_load(env, module: :"Cure.Test.OpticShip", functions: fns, origins: origins)

    # A `fst` lens into the first component of a 2-tuple {a, b}: reading returns
    # `a`, writing rebuilds `{new, b}` keeping the untouched second component.
    get = fn {a, _b} -> a end
    put = fn new -> fn {_a, b} -> {new, b} end end
    fst = apply(m, :lens, [get, put])

    {:ok, m: m, fst: fst}
  end

  test "view reads the focus (total on a lens)", %{m: m, fst: fst} do
    assert apply(m, :view, [fst, {1, 2}]) == 1
  end

  test "set replaces the focus and rebuilds the rest of the structure", %{m: m, fst: fst} do
    assert apply(m, :set, [fst, 9, {1, 2}]) == {9, 2}
  end

  test "over modifies the focus in place, keeping the untouched component", %{m: m, fst: fst} do
    assert apply(m, :over, [fst, fn n -> n + 1 end, {1, 2}]) == {2, 2}
  end

  test "preview on a lens is always Some(focus)", %{m: m, fst: fst} do
    assert apply(m, :preview, [fst, {41, 0}]) == {:some, 41}
  end
end
