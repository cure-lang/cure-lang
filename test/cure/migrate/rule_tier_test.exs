defmodule Cure.Migrate.RuleTierTest do
  use ExUnit.Case, async: true
  alias Cure.Migrate
  alias Cure.Migrate.Rule

  # A rewrite rule at a given tier that appends a marker to a top-level block.
  defp marker_rule(tier) do
    %Rule{
      id: :W_test_tier,
      description: "test tier rule",
      phase: :syntactic,
      tier: tier,
      since: "2026",
      detect_and_rewrite: fn {:block, m, ex}, _ctx ->
        {:rewrite, {:block, m, ex ++ [{:literal, [subtype: :string], "M"}]}}
      end,
      warning_template: "marker appended"
    }
  end

  defp parse!(src) do
    {:ok, toks} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Cure.Compiler.Parser.parse(toks, emit_events: false)
    ast
  end

  test "in :safe_only (build) mode, a :machine rewrite is normalized in-memory" do
    ast = parse!("mod M\nfn f(x: Int) -> Int = 1\n")
    {new_ast, warns} = Migrate.run(ast, rules: [marker_rule(:machine)], apply: :safe_only)
    assert new_ast != ast
    assert [warning] = warns
    assert warning.tier == :machine
    assert warning.preview =~ ~s/"M"/
    assert warning.message =~ "semantics-preserving"
    assert warning.message =~ "applied automatically"
  end

  test "in :safe_only mode, a :review rewrite warns but is NOT normalized" do
    ast = parse!("mod M\nfn f(x: Int) -> Int = 1\n")
    {new_ast, warns} = Migrate.run(ast, rules: [marker_rule(:review)], apply: :safe_only)
    assert new_ast == ast
    assert [warning] = warns
    assert warning.tier == :review
    assert warning.preview =~ ~s/"M"/
    assert warning.message =~ "Review the proposed result"
  end

  test "in :all (migrate) mode, every tier's rewrite is applied" do
    ast = parse!("mod M\nfn f(x: Int) -> Int = 1\n")
    {new_ast, _} = Migrate.run(ast, rules: [marker_rule(:review)], apply: :all)
    assert new_ast != ast
  end

  test "a proposed whole-file preview retains source comments" do
    source = "mod M\n  # keep this explanation\n  use Std.Eq\n"
    {:ok, tokens, trivia} = Cure.Compiler.Lexer.tokenize(source, trivia: true, emit_events: false)
    {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)
    ast = Cure.Compiler.Trivia.attach(ast, trivia)

    {_new_ast, warnings} = Migrate.run(ast, apply: :safe_only)
    warning = Enum.find(warnings, &(&1.rule == :W_module_rename))

    assert warning.tier == :machine
    assert warning.preview =~ "# keep this explanation"
    assert warning.preview =~ "use Std.Equatable"
  end

  describe "registry rule tags (spec §5.3)" do
    setup do
      by_id = for r <- Cure.Migrate.rules(), into: %{}, do: {r.id, r}
      {:ok, rules: by_id}
    end

    test "each rule has the tier and provenance the spec fixes", %{rules: r} do
      assert r[:W_if_elif_pickup].tier == :machine
      assert r[:W_uppercase_type_var].tier == :review
      assert r[:W_group_hoist].tier == :machine
      assert r[:W_module_rename].tier == :machine
      assert r[:W_module_rename].enforced_in == "2026"
      assert r[:W_removed_module].tier == :manual
      assert r[:W_removed_module].enforced_in == "2026"
      for {_id, rule} <- r, do: assert(rule.since == "2026")
    end

    test "cure build normalizes the three :machine rewrite rules that were previously never normalized" do
      # module rename is :machine → :safe_only mode now folds it in-memory.
      src = "mod M\n  use Std.Eq\n  fn f(x: Int) -> Bool = eq(x, x)\n"
      {:ok, toks} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
      {:ok, ast} = Cure.Compiler.Parser.parse(toks, emit_events: false)
      {new_ast, _} = Cure.Migrate.run(ast, apply: :safe_only)
      refute new_ast == ast, "module rename (:machine) must normalize under :safe_only"
    end

    test "cure build does NOT normalize the :review uppercase-type-var rule" do
      src = "mod M\n  fn id(x: T) -> T = x\n"
      {:ok, toks} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
      {:ok, ast} = Cure.Compiler.Parser.parse(toks, emit_events: false)
      {new_ast, warns} = Cure.Migrate.run(ast, apply: :safe_only)
      assert new_ast == ast, ":review must not normalize under :safe_only"
      assert Enum.any?(warns, &(&1.rule == :W_uppercase_type_var))
    end
  end
end
