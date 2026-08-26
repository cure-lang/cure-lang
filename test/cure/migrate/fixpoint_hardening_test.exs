# Hardening tests for run_to_fixpoint/2 — audit findings F2 (warning duplication
# across passes), F3b (crash on unprintable output instead of a clean error), and
# F-culprit (verify blames a warner, not the rewriter that broke verify).
defmodule Cure.Migrate.FixpointHardeningTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Migrate
  alias Cure.Migrate.Rule

  defp parse!(src) do
    {:ok, toks} = Lexer.tokenize(src, file: "t.cure", emit_events: false)
    {:ok, ast} = Parser.parse(toks, file: "t.cure", emit_events: false)
    ast
  end

  defp rule(id, tier, fun),
    do: %Rule{
      id: id,
      description: "t",
      phase: :syntactic,
      tier: tier,
      since: "2026",
      warning_template: "m",
      detect_and_rewrite: fun
    }

  # A machine rewrite that toggles a printable meta flag on the module container
  # exactly once (idempotent after), forcing one changing pass then convergence.
  defp toggle_once(id),
    do:
      rule(id, :machine, fn {:container, meta, kids}, _ctx ->
        if Keyword.get(meta, :audit_touched),
          do: :no_change,
          else: {:rewrite, {:container, [{:audit_touched, true} | meta], kids}, [1]}
      end)

  # A pure warn rule that fires on every pass (never converges away).
  defp warn_always(id), do: rule(id, :manual, fn _ast, _ctx -> {:warn, [1]} end)

  # A rewrite that injects a node the Printer has no clause for — models a
  # rule-author bug that yields unrenderable output.
  defp emit_unprintable(id),
    do:
      rule(id, :machine, fn {:container, meta, kids}, _ctx ->
        if Enum.any?(kids, &match?({:audit_bogus, _, _}, &1)),
          do: :no_change,
          else: {:rewrite, {:container, meta, kids ++ [{:audit_bogus, [], []}]}, [1]}
      end)

  test "F2: a warn rule firing every pass is not duplicated in the returned warnings" do
    ast = parse!("mod M\n  fn f() -> Int = 1\n")
    {:ok, _ast, warns} = Migrate.run_to_fixpoint(ast, rules: [toggle_once(:tog), warn_always(:noise)])
    ids = Enum.map(warns, & &1.rule)
    assert Enum.count(ids, &(&1 == :noise)) == 1
    assert :tog in ids
  end

  test "F3b: a rule emitting unprintable output yields a clean verify_failed, not a crash" do
    ast = parse!("mod M\n  fn f() -> Int = 1\n")
    assert {:error, {:verify_failed, _}} = Migrate.run_to_fixpoint(ast, rules: [emit_unprintable(:boom)])
  end

  test "F-culprit: verify_failed blames the rewriter, not a pure-warn rule that fired later" do
    ast = parse!("mod M\n  fn f() -> Int = 1\n")
    # :boom rewrites (and breaks verify); :noise only warns, and warns "last".
    assert {:error, {:verify_failed, :boom}} =
             Migrate.run_to_fixpoint(ast, rules: [emit_unprintable(:boom), warn_always(:noise)])
  end
end
