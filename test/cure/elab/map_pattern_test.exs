defmodule Cure.Elab.MapPatternTest do
  @moduledoc """
  Map patterns `%{k: v} ->` in the dependent pipeline. The classic pattern
  compiler destructured Erlang maps directly; here a `match` whose arms are map
  patterns desugars (in the elaborator, before Core) to `has_key`-guarded
  conditionals that bind each field via `Std.Map.get` — nothing new reaches the
  kernel. This is now possible without a coerce workaround because `Std.Map` is
  parameterized `Map(k, v)`: `get(k, map: Map(k, v)) -> v` recovers the bound
  value's type from the scrutinee's map type.

  Map matching is OPEN (keys not named in the pattern are ignored) and therefore
  non-exhaustive, so a trailing wildcard/variable default arm is required. Value
  positions may be variable binders, `_`, or literals (an equality guard). The
  module must `use Std.Map` so `has_key`/`get` resolve, exactly like map literals.

  Part of the pre-#18 surface-construct port batch (see
  memory pre18-surface-construct-gaps).
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.{Emit, Program}

  defp compile!(fn_name, fn_src, mod) do
    src = "mod M\n  use Std.Map\n" <> fn_src <> "\nend\n"
    assert {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, emit_events: false)
    assert {:ok, env} = Program.elaborate(src)
    origins = Program.import_origins(ast)

    assert {:ok, m} =
             Emit.compile_and_load(env, module: mod, functions: [fn_name], origins: origins)

    m
  end

  test "a variable map pattern binds the field via get, with a wildcard fallthrough" do
    m =
      compile!(
        :lookup,
        """
          fn lookup(m: Map(Atom, Int)) -> Int =
            match m
              %{a: v} -> v
              _ -> 0
        """,
        :"Cure.Test.MapPatVar"
      )

    assert apply(m, :lookup, [%{a: 7}]) == 7
    assert apply(m, :lookup, [%{b: 9}]) == 0
    assert apply(m, :lookup, [%{}]) == 0
  end

  test "a literal value position becomes an equality guard" do
    m =
      compile!(
        :classify,
        """
          fn classify(m: Map(Atom, Atom)) -> Int =
            match m
              %{tag: :hit} -> 1
              %{tag: :miss} -> 2
              _ -> 0
        """,
        :"Cure.Test.MapPatLit"
      )

    assert apply(m, :classify, [%{tag: :hit}]) == 1
    assert apply(m, :classify, [%{tag: :miss}]) == 2
    assert apply(m, :classify, [%{tag: :other}]) == 0
    assert apply(m, :classify, [%{}]) == 0
  end

  test "multiple keys via field-punning are conjoined and both bound" do
    m =
      compile!(
        :point_sum,
        """
          fn point_sum(m: Map(Atom, Int)) -> Int =
            match m
              %{x, y} -> x + y
              _ -> 0
        """,
        :"Cure.Test.MapPatPun"
      )

    assert apply(m, :point_sum, [%{x: 3, y: 4}]) == 7
    # `y` absent → the conjoined guard fails → fallthrough
    assert apply(m, :point_sum, [%{x: 3}]) == 0
    assert apply(m, :point_sum, [%{}]) == 0
  end

  test "a map match with no default arm is rejected (open matching is non-exhaustive)" do
    src = """
    mod M
      use Std.Map
      fn f(m: Map(Atom, Int)) -> Int =
        match m
          %{a: v} -> v
    end
    """

    assert {:error, {:source_context, {:map_match_needs_default}, _}} = Program.elaborate(src)
  end
end
