defmodule Cure.Stdlib.MapParameterizedTest do
  @moduledoc """
  `Std.Map` carries its key/value types: the carrier is `Map(k, v)`, not a
  nullary opaque `Map`. This is the Idris (`SortedMap k v`) / Haskell (`Map k v`)
  design, and it is what removes the return-polymorphism wall: `get(key, map) -> v`
  can recover `v` from the map's own type argument instead of leaving it a free,
  uninferable variable.

  The decisive case is `get` in a pure *inference* position — a `let`-binding
  whose type must be synthesized, with no expected type flowing in. Under the old
  nullary `Map` this failed with `:let_needs_annotation`; under `Map(k, v)` it
  synthesizes cleanly. That is exactly the shape a map-pattern desugar
  (`%{k: v} -> …`) produces, so this parameterization is the prerequisite for map
  patterns without an opaque-`Any` coerce workaround.

  Runtime is unchanged — `Map(k, v)` still erases to a raw BEAM map and the
  `:maps.*` externs are untouched; the index is purely type-level.

  Part of the pre-#18 surface-construct port batch (see
  memory pre18-surface-construct-gaps).
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.{Emit, Program}

  defp compile!(caller, mod, fns) do
    src = "mod M\n  use Std.Map\n" <> caller <> "\nend\n"
    assert {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, emit_events: false)
    assert {:ok, env} = Program.elaborate(src)
    origins = Program.import_origins(ast)

    assert {:ok, m} = Emit.compile_and_load(env, module: mod, functions: fns, origins: origins)
    m
  end

  test "get on a typed map synthesizes its value type in inference position" do
    m =
      compile!(
        """
          fn lookup(m: Map(Atom, Int)) -> Int =
            let v = get(:a, m)
            v + 1
        """,
        :"Cure.Test.MapInfer",
        [:lookup]
      )

    assert apply(m, :lookup, [%{a: 41}]) == 42
  end

  test "put then get round-trips through the typed map" do
    m =
      compile!(
        "  fn build(x: Int) -> Map(Atom, Int) = put(:a, x, new())",
        :"Cure.Test.MapBuild",
        [:build]
      )

    assert apply(m, :build, [7]) == %{a: 7}
  end
end
