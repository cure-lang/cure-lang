defmodule Cure.Elab.GuardLintTest do
  @moduledoc """
  Spec 2026-07-08-guard-coverage-lint: the untrusted Z3 coverage lint. Unit
  describe drives GuardLint directly on hand-built Core; the integration
  describe (Task 2) drives it through Program.elaborate/1.
  """
  use ExUnit.Case, async: false

  alias Cure.Compiler.Errors
  alias Cure.Core.{Builtins, Context, Env}
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.GuardLint

  # Context with two machine-Int vars: index 0 and index 1, over a builtins-
  # seeded signature (K2: the lint resolves comparison SPINES through the
  # def-record registry, so the ctx must carry the op defs).
  defp int_ctx do
    Context.empty(Builtins.seed(Env.empty()))
    |> Context.extend({:vint_type})
    |> Context.extend({:vint_type})
  end

  # Builtin-op comparison spine (K2: was the {:prim, op, [a, b]} node).
  @op_globals %{lt: :int_lt, le: :int_le, gt: :int_gt, ge: :int_ge, eq: :int_eq, ne: :int_ne}
  defp p(op, a, b), do: {:app, {:app, {:global, Map.fetch!(@op_globals, op)}, a}, b}
  @x {:var, 0}
  @y {:var, 1}

  describe "prove_exhaustive/2 (§2.2 fragment, §2.3a recovery oracle)" do
    test "trichotomy over Int is proven" do
      assert :proven =
               GuardLint.prove_exhaustive([p(:lt, @x, @y), p(:eq, @x, @y), p(:gt, @x, @y)], int_ctx())
    end

    test "a complement pair is proven" do
      assert :proven = GuardLint.prove_exhaustive([p(:lt, @x, @y), p(:ge, @x, @y)], int_ctx())
    end

    test "an Int-only cover is proven over Int (documents the fragment's Int semantics)" do
      # x <= 0 | x >= 1 — exhaustive over Int, NOT over Float; translatable only
      # because the vars are Int-typed in ctx (a Float var falls out at int_form).
      assert :proven =
               GuardLint.prove_exhaustive(
                 [p(:le, @x, {:int_lit, 0}), p(:ge, @x, {:int_lit, 1})],
                 int_ctx()
               )
    end

    test "a genuine gap is not proven" do
      assert :not_proven = GuardLint.prove_exhaustive([p(:lt, @x, @y), p(:gt, @x, @y)], int_ctx())
    end

    test "a Float-typed variable makes its guard untranslatable (not proven)" do
      ctx = Context.empty() |> Context.extend({:vfloat_type}) |> Context.extend({:vfloat_type})
      assert :not_proven = GuardLint.prove_exhaustive([p(:le, @x, {:int_lit, 0}), p(:ge, @x, {:int_lit, 1})], ctx)
    end

    test "an untranslatable guard can never help prove exhaustiveness (K13)" do
      mystery = {:ctor, :Mystery, [@x]}
      assert :not_proven = GuardLint.prove_exhaustive([mystery], int_ctx())
      assert :not_proven = GuardLint.prove_exhaustive([p(:lt, @x, @y), mystery], int_ctx())
    end

    test "the empty guard list is not proven" do
      assert :not_proven = GuardLint.prove_exhaustive([], int_ctx())
    end
  end

  describe "shadowed?/3" do
    test "a literally repeated translatable guard is shadowed" do
      assert GuardLint.shadowed?(p(:lt, @x, @y), [p(:lt, @x, @y)], int_ctx())
    end

    test "an implied guard is shadowed" do
      # x < y implies x <= y
      assert GuardLint.shadowed?(p(:lt, @x, @y), [p(:le, @x, @y)], int_ctx())
    end

    test "a non-implied guard is not shadowed" do
      refute GuardLint.shadowed?(p(:gt, @x, @y), [p(:lt, @x, @y)], int_ctx())
    end

    test "no priors -> never shadowed" do
      refute GuardLint.shadowed?(p(:lt, @x, @y), [], int_ctx())
    end

    test "a literally repeated UNtranslatable guard is shadowed via atom interning (§2.2)" do
      g = {:ctor, :Mystery, [@x]}
      assert GuardLint.shadowed?(g, [g], int_ctx())
    end

    test "distinct untranslatable guards are not shadowed (distinct constants)" do
      refute GuardLint.shadowed?({:ctor, :MysteryB, [@x]}, [{:ctor, :MysteryA, [@x]}], int_ctx())
    end
  end

  describe "warnings channel (§2.5)" do
    test "record/read/reset round-trip in insertion order" do
      GuardLint.reset_warnings()
      assert GuardLint.warnings() == []
      GuardLint.record_warning({:guard_shadowed, 1})
      GuardLint.record_warning({:guard_shadowed, 2})
      assert GuardLint.warnings() == [{:guard_shadowed, 1}, {:guard_shadowed, 2}]
      GuardLint.reset_warnings()
      assert GuardLint.warnings() == []
    end
  end

  describe "elaboration integration (§6): recovery + warnings through Program.elaborate/1" do
    alias Cure.Elab.{Emit, Program}

    @nat "mod M\n  type Nat = Z | S(Nat)\n"

    test "trichotomy without a catch-all is accepted and runs correctly on all three regions" do
      src =
        @nat <>
          "  fn cmp(a: Int, b: Int) -> Nat = match a\n" <>
          "    x when x < b -> Z()\n" <>
          "    x when x == b -> S(Z())\n" <>
          "    x when x > b -> S(S(Z()))\n" <>
          "  fn lo() -> Nat = cmp(1, 5)\n" <>
          "  fn mid() -> Nat = cmp(5, 5)\n" <>
          "  fn hi() -> Nat = cmp(9, 5)\nend\n"

      {:ok, env} = Program.elaborate(src)

      {:ok, mod} =
        Emit.compile_and_load(env, module: :"Cure.GuardLintTri", functions: [:cmp, :lo, :mid, :hi])

      assert apply(mod, :lo, []) == :Z
      assert apply(mod, :mid, []) == {:S, :Z}
      assert apply(mod, :hi, []) == {:S, {:S, :Z}}
    end

    test "a two-guard complement without a catch-all is accepted" do
      src =
        @nat <>
          "  fn cmp(a: Int, b: Int) -> Nat = match a\n" <>
          "    x when x < b -> Z()\n" <>
          "    x when x >= b -> S(Z())\nend\n"

      assert {:ok, _env} = Program.elaborate(src)
    end

    test "a genuine gap still rejects with the pinned error shape" do
      src =
        @nat <>
          "  fn cmp(a: Int, b: Int) -> Nat = match a\n" <>
          "    x when x < b -> Z()\n" <>
          "    x when x > b -> S(Z())\nend\n"

      assert {:error, {:source_context, {:unsupported_guard, :non_exhaustive}, _} = error} =
               Program.elaborate(src)

      {diagnostic, registry} = Errors.to_diagnostic(error, "guard_gap.cure", src)

      assert Renderer.plain(diagnostic, registry, width: 80) ==
               String.trim_trailing("""
               -- GUARDED BRANCHES LEAVE A GAP [E093] -------------------------- guard_gap.cure

               Cure cannot prove that these guard conditions cover every value accepted by
               their patterns. If every condition is false, this match has no result.

               at guard_gap.cure:5:27
               4 |     x when x < b -> Z()
                 |            ----- this condition does not cover every remaining value
               5 |     x when x > b -> S(Z())
                 |            -----          ^ this condition does not cover every remaining value; add an unguarded fallback branch here

               Hint: Add an unguarded `_ -> ...` branch, or make the final guards exact complements
               """)

      lsp = Renderer.lsp(diagnostic, registry)

      assert lsp["range"] == %{
               "start" => %{"line" => 4, "character" => 26},
               "end" => %{"line" => 4, "character" => 26}
             }

      assert Enum.map(lsp["relatedInformation"], & &1["location"]["range"]) == [
               %{
                 "start" => %{"line" => 3, "character" => 11},
                 "end" => %{"line" => 3, "character" => 16}
               },
               %{
                 "start" => %{"line" => 4, "character" => 11},
                 "end" => %{"line" => 4, "character" => 16}
               }
             ]

      assert lsp["data"]["payload"] == %{
               "checking" => "cmp",
               "guard_count" => 2,
               "kind" => "unsupported_guard",
               "reason" => "non_exhaustive"
             }

      fixed = String.replace(src, "    x when x > b -> S(Z())\n", "    x when x > b -> S(Z())\n    _ -> Z()\n")
      assert {:ok, _environment} = Program.elaborate(fixed, file: "guard_gap_fixed.cure")
    end

    test "semantically exhaustive but untranslatable guards still reject (K13 observable)" do
      src =
        @nat <>
          "  fn pos(i: Int) -> Bool = i > 0\n" <>
          "  fn nonpos(i: Int) -> Bool = i <= 0\n" <>
          "  fn cls(n: Int) -> Nat = match n\n" <>
          "    x when pos(x) -> Z()\n" <>
          "    x when nonpos(x) -> S(Z())\nend\n"

      assert {:error, {:source_context, {:unsupported_guard, :non_exhaustive}, _}} = Program.elaborate(src)
    end

    test "a shadowed guard warns; the program still elaborates" do
      src =
        @nat <>
          "  fn cls(n: Int, b: Int) -> Nat = match n\n" <>
          "    x when x < b -> Z()\n" <>
          "    x when x < b -> S(Z())\n" <>
          "    x -> S(S(Z()))\nend\n"

      assert {:ok, _env} = Program.elaborate(src)
      assert [{:guard_shadowed, 1}] = GuardLint.warnings()
    end

    # With only one shadowed arm the order is unobservable. With two, it was reversed:
    # `guard_chain/7` recursed into every LATER arm — each recording its own warning — before
    # checking the CURRENT arm's shadow status. `record_warning/1` prepends and `warnings/0`
    # reverses, a scheme that restores insertion order only when the caller inserts in source
    # order. Here the caller inserted bottom-up, so the reversal handed back descending indices.
    test "two shadowed guards warn in source order, not reversed" do
      src =
        @nat <>
          "  fn cls(n: Int, b: Int) -> Nat = match n\n" <>
          "    x when x < b -> Z()\n" <>
          "    x when x < b -> S(Z())\n" <>
          "    x when x < b -> S(S(Z()))\n" <>
          "    x -> S(S(S(Z())))\nend\n"

      assert {:ok, _env} = Program.elaborate(src)
      assert GuardLint.warnings() == [{:guard_shadowed, 1}, {:guard_shadowed, 2}]
    end

    test "an unshadowed chain leaves no warnings (and elaborate/1 resets stale ones)" do
      GuardLint.record_warning({:guard_shadowed, 99})

      src =
        @nat <>
          "  fn cls(n: Int, b: Int) -> Nat = match n\n" <>
          "    x when x < b -> Z()\n" <>
          "    x when x > b -> S(Z())\n" <>
          "    x -> S(S(Z()))\nend\n"

      assert {:ok, _env} = Program.elaborate(src)
      assert GuardLint.warnings() == []
    end
  end
end
