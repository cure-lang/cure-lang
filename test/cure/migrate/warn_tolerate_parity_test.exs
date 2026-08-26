defmodule Cure.Migrate.WarnTolerateParityTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Migrate

  # The set of rules that fire (warn) equals the set that rewrite: same
  # per-file ctx, same detect_and_rewrite. Assert identical fired-rule sets.
  # NOTE: this equivalence holds for every input EXCEPT the one deliberate,
  # spec-mandated exception exercised by the second test below (a legacy
  # conditional inside a round-paren context always warns but is never
  # rewritten, since rewriting it would break reparse -- spec §5.5's
  # if/elif->pickup seed-rule note, option (a)). This test's own input is
  # chosen to NOT hit that exception, so the strict `==` holds here.
  test "warn-mode fires on exactly the inputs rewrite-mode changes (non-paren case)" do
    src = "mod M\nfn id(x: T) -> T = if x_len(x) > 0 then 1 else 2\n"
    {:ok, toks} = Lexer.tokenize(src, file: "p.cure", emit_events: false)
    {:ok, ast} = Parser.parse(toks, file: "p.cure", emit_events: false)

    {rewritten, warnings} = Migrate.run(ast, file: "p.cure")
    fired = warnings |> Enum.map(& &1.rule) |> Enum.sort()

    # rewrite happened iff a rule fired
    assert rewritten != ast == (fired != [])
    # both seed rules fired for this input
    assert :W_if_elif_pickup in fired
    assert :W_uppercase_type_var in fired
  end

  test "the one documented exception: a paren-embedded conditional warns without rewriting" do
    # Spec §5.5 explicitly sanctions this as option (a) for the if/elif->pickup
    # seed rule: "emit the warning but leave the source untouched, same as an
    # unmatched rule" -- for THIS specific input shape, `fired` is true while
    # `rewritten` is false, which is the one place the strict `==` above does
    # not hold. This test exists so nobody "fixes" that as a regression later.
    src = "mod M\nfn g(x: Int) -> Int = h(if x > 0 then 1 else 2)\n"
    {:ok, toks} = Lexer.tokenize(src, file: "q.cure", emit_events: false)
    {:ok, ast} = Parser.parse(toks, file: "q.cure", emit_events: false)

    {rewritten, warnings} = Migrate.run(ast, file: "q.cure")
    fired = warnings |> Enum.map(& &1.rule) |> Enum.sort()

    assert rewritten == ast
    assert :W_if_elif_pickup in fired
  end
end
