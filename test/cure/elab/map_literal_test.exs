defmodule Cure.Elab.MapLiteralTest do
  @moduledoc """
  Map literals `%{a: 1, b: 2}` in the dependent pipeline. The classic codegen
  lowered them to an Erlang map; here they desugar (in the elaborator, before
  Core) to nested `Std.Map.put` calls over `Std.Map.new()` — nothing new reaches
  the kernel.

  Unlike ranges/comprehensions this port is SEAM-FREE: `Std.Map` is a thin
  `@extern` wrapper over Erlang `:maps`, so the runtime value is always a raw
  Erlang map regardless of pipeline — there is no classic-vs-dependent
  representation divergence to bridge. The test therefore uses `Std.Map` directly
  across the module boundary (remote-call externs) and compares the emitted value
  to a plain Elixir map.

  Map *patterns* (`%{a: v} ->`) are a separate, harder port (non-constructor
  destructuring, shared with binary patterns) and are NOT covered here.

  Part of the pre-#18 surface-construct port batch (see
  memory pre18-surface-construct-gaps).
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.{Emit, Program}

  defp compile!(caller, mod) do
    src = "mod M\n  use Std.Map\n" <> caller <> "\nend\n"
    assert {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, emit_events: false)
    assert {:ok, env} = Program.elaborate(src)
    origins = Program.import_origins(ast)

    assert {:ok, m} =
             Emit.compile_and_load(env, module: mod, functions: [:build], origins: origins)

    m
  end

  test "a map literal builds the corresponding Erlang map" do
    m = compile!("  fn build() -> Map(Atom, Int) = %{a: 1, b: 2}", :"Cure.Test.MapLit")
    assert apply(m, :build, []) == %{a: 1, b: 2}
  end

  # `%{}` is a bare `new()` with no arguments to pin its key/value types, so it
  # needs an expected type from context (check mode) — here, `merge`'s parameter.
  test "an empty map literal solves its type from a checked position" do
    m =
      compile!(
        "  fn build(base: Map(Atom, Int)) -> Map(Atom, Int) = merge(%{}, base)",
        :"Cure.Test.MapEmpty"
      )

    assert apply(m, :build, [%{a: 5}]) == %{a: 5}
    assert apply(m, :build, [%{}]) == %{}
  end
end
