defmodule Cure.Migrate.MonotonePropertyTest do
  use ExUnit.Case, async: true
  # Stdlib-scale: parses, migrates-to-fixpoint, and reprints every lib/std/*.cure
  # file twice (117 files). Genuinely whole-stdlib work, so per test_helper.exs it
  # is excluded from the default run (where async contention pushes its ~5s of CPU
  # past the 60s per-test wall) and runs in CI via `mix test --include slow`.
  @moduletag :slow
  alias Cure.Compiler.{Lexer, Parser, Trivia, Printer}
  alias Cure.Migrate

  defp fixpoint_string(src) do
    # `emit_events: false` matches every batch caller (Migrate's re-lexing, the
    # Parser). Without it this one tokenization fires a pipeline event PER TOKEN
    # into a subscriber-less registry — an ETS dispatch + clock read per token,
    # ~45% of this test's CPU across 117 files ×2 passes — which is what pushed
    # it past the 60s per-test wall under async contention.
    {:ok, toks, trivia} = Lexer.tokenize(src, trivia: true, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)
    {:ok, out, _} = Migrate.run_to_fixpoint(Trivia.attach(ast, trivia))
    Printer.quoted_to_string(out)
  end

  test "migrating a fixpoint output again is byte-identical (monotone law) across the stdlib" do
    for path <- Path.wildcard("lib/std/*.cure") do
      once = fixpoint_string(File.read!(path))
      twice = fixpoint_string(once)
      assert once == twice, "non-monotone on #{path}"
    end
  end
end
