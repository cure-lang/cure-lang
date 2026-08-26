defmodule Cure.Elab.NestedPatternTest do
  @moduledoc """
  Parity row #3 (nested/deep patterns) — the single-nested-column slice. A match
  arm may carry a nested constructor sub-pattern (`S(S(m))`, `A(Z())`); it is
  lowered to nested *single-level* matches (`elaborate_match`'s
  `desugar_nested_arms`) so every level reuses the dependent match machinery
  (motives, index refinement, catch-all) and the kernel's own nesting `:case`.
  Oracle `match/mt07_nested_patterns` pins accept/accept parity.

  Scope: arms grouped by outer constructor, at most ONE nested argument column
  per group (others must be variables, substituted by their fresh binder).
  Multi-column nesting and a top-level catch-all mixed with nesting are rejected
  cleanly; deeper nesting is lowered on re-entry. No TCB change — pure surface
  lowering.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.{Program, Emit}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  test "a two-deep nested pattern elaborates" do
    src =
      @nat <>
        "  fn f(n: Nat) -> Nat = match n\n    S(S(m)) -> m\n    S(Z()) -> Z()\n    Z() -> Z()\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end

  test "nested pattern lowers to a correct runtime match on the BEAM" do
    src =
      @nat <>
        "  fn f(n: Nat) -> Nat = match n\n    S(S(m)) -> m\n    S(Z()) -> Z()\n    Z() -> Z()\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.NestedPatternE2E", functions: [:f])

    # S(S(m)) strips two successors: f(S(S(S(Z)))) = S(Z).
    assert apply(mod, :f, [{:S, {:S, {:S, :Z}}}]) == {:S, :Z}
    # S(S(m)) with m = Z: f(S(S(Z))) = Z.
    assert apply(mod, :f, [{:S, {:S, :Z}}]) == :Z
    # S(Z) branch and Z branch both yield Z.
    assert apply(mod, :f, [{:S, :Z}]) == :Z
    assert apply(mod, :f, [:Z]) == :Z
  end

  test "a variable sub-pattern in the nested column becomes an inner catch-all" do
    src =
      @nat <>
        "  fn f(n: Nat) -> Nat = match n\n    S(S(m)) -> m\n    S(k) -> k\n    Z() -> Z()\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end

  test "single nested column with a sibling variable column (A(Z()) / A(S(k)) / B(y))" do
    src =
      @nat <>
        "  type T = A(Nat) | B(Nat)\n  fn g(t: T) -> Nat = match t\n    A(Z()) -> Z()\n    A(S(k)) -> k\n    B(y) -> y\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end

  test "triple nesting is handled by re-entry" do
    src =
      @nat <>
        "  fn f(n: Nat) -> Nat = match n\n    S(S(S(m))) -> m\n    S(S(Z())) -> Z()\n    S(Z()) -> Z()\n    Z() -> Z()\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end

  test "COVERAGE (#17): a non-exhaustive nested match is rejected with a missing branch" do
    src = @nat <> "  fn f(n: Nat) -> Nat = match n\n    S(S(m)) -> m\n    Z() -> Z()\nend\n"

    # The S(Z()) case is uncovered — reported through the lowered inner match.
    assert {:error, {:source_context, {:missing_branch, :"M#Z"}, _}} = Program.elaborate(src)
  end

  test "COVERAGE (#17): a depth-3 nested match missing an inner case is rejected" do
    src =
      @nat <>
        "  fn f(n: Nat) -> Nat = match n\n    S(S(S(m))) -> m\n    S(S(Z())) -> Z()\n    S(Z()) -> Z()\nend\n"

    # Missing outer Z() (and nothing covers it) — coverage is enforced at every
    # nesting level, not just the top.
    assert {:error, {:source_context, {:missing_branch, :"M#Z"}, _}} = Program.elaborate(src)
  end

  test "multi-column nesting elaborates and runs (pattern-matrix compilation)" do
    src =
      @nat <>
        "  type P = MkP(Nat, Nat) | Nil\n  fn h(p: P) -> Nat = match p\n    MkP(Z(), Z()) -> Z()\n    MkP(Z(), S(b)) -> b\n    MkP(S(a), y) -> a\n    Nil() -> Z()\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.NestedMultiColE2E", functions: [:h])

    assert apply(mod, :h, [{:MkP, :Z, :Z}]) == :Z
    assert apply(mod, :h, [{:MkP, :Z, {:S, {:S, :Z}}}]) == {:S, :Z}
    assert apply(mod, :h, [{:MkP, {:S, :Z}, :Z}]) == :Z
    assert apply(mod, :h, [:Nil]) == :Z
  end

  test "a top-level catch-all mixed with nesting is woven in as a fallback" do
    # `_` completes the S(S(_)) hole (S(Z) and Z both fall through to Z()).
    src = @nat <> "  fn f(n: Nat) -> Nat = match n\n    S(S(m)) -> m\n    _ -> Z()\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.NestedOuterCatchallE2E", functions: [:f])

    assert apply(mod, :f, [{:S, {:S, {:S, :Z}}}]) == {:S, :Z}
    assert apply(mod, :f, [{:S, :Z}]) == :Z
    assert apply(mod, :f, [:Z]) == :Z
  end

  test "a named catch-all binds the scrutinee across the nesting fallback" do
    src = @nat <> "  fn f(n: Nat) -> Nat = match n\n    S(S(m)) -> m\n    other -> other\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.NestedNamedCatchallE2E", functions: [:f])

    assert apply(mod, :f, [{:S, :Z}]) == {:S, :Z}
    assert apply(mod, :f, [:Z]) == :Z
  end

  test "a branch after a nested match catch-all labels both unreachable roles" do
    src =
      @nat <>
        "  fn f(n: Nat) -> Nat = match n\n" <>
        "    S(S(x)) -> x\n" <>
        "    rest -> rest\n" <>
        "    Z() -> Z()\n" <>
        "end\n"

    assert {:error,
            {:source_context,
             {:unreachable_after_default_pattern, %{name: "rest", span: branch_span, default_span: default_span}}, _} =
              error} =
             Program.elaborate(src)

    assert {branch_span.start_line, branch_span.start_column} == {6, 5}
    assert {default_span.start_line, default_span.start_column} == {5, 5}

    {diagnostic, registry} = Errors.to_diagnostic(error, "nested_after_default.cure", src)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- BRANCH APPEARS AFTER A CATCH-ALL [E119] ----------- nested_after_default.cure

             No value can reach this branch because the preceding catch-all pattern already
             accepts every value not handled above it.

             at nested_after_default.cure:6:5
             5 |     rest -> rest
               |     ---- this catch-all already accepts every remaining value as `rest`
             6 |     Z() -> Z()
               |     ^^^ this branch can never be reached

             Hint: Move the catch-all to the end of the match, or narrow it to a constructor pattern
             """)

    lsp = Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 5, "character" => 4},
             "end" => %{"line" => 5, "character" => 7}
           }

    assert [related] = lsp["relatedInformation"]

    assert related["location"]["range"] == %{
             "start" => %{"line" => 4, "character" => 4},
             "end" => %{"line" => 4, "character" => 8}
           }

    assert lsp["data"]["payload"] == %{
             "checking" => "f",
             "kind" => "unreachable_after_default_pattern",
             "name" => "rest"
           }

    fixed =
      src
      |> String.replace("    rest -> rest\n", "")
      |> String.replace("    Z() -> Z()\n", "    Z() -> Z()\n    rest -> rest\n")

    assert {:ok, _environment} = Program.elaborate(fixed, file: "nested_after_default_fixed.cure")
  end

  test "a NAMED catch-all with nesting over a non-variable scrutinee hoists and binds once" do
    # `S(n)` is not a variable, so there is nothing to bind the named catch-all
    # to directly; `elaborate_match` hoists the scrutinee into a fresh
    # `let $s = S(n) in match $s | …`, so `other` binds `$s` (evaluated once),
    # matching Idris' `case … of other =>`. Oracle
    # `match/mt22_nested_named_default_nonvar` pins accept/accept parity.
    src =
      @nat <>
        "  fn f(n: Nat) -> Nat = match S(n)\n    S(S(m)) -> m\n    other -> other\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.NestedNamedCatchallNonVarE2E", functions: [:f])

    # f(Z): scrut S(Z) misses S(S(m)) → `other` = S(Z).
    assert apply(mod, :f, [:Z]) == {:S, :Z}
    # f(S(Z)): scrut S(S(Z)) matches S(S(m)) with m = Z → Z.
    assert apply(mod, :f, [{:S, :Z}]) == :Z
    # f(S(S(Z))): scrut S(S(S(Z))) matches S(S(m)) with m = S(Z) → S(Z).
    assert apply(mod, :f, [{:S, {:S, :Z}}]) == {:S, :Z}
  end
end
