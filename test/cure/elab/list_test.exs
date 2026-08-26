defmodule Cure.Elab.ListTest do
  @moduledoc """
  `List` value surface in the dependent pipeline (Wave 2). `[]`/`[h|t]`/`[a,b,c]`
  elaborate through the canonical list-literal path to `Nil`/`Cons` Core and
  emit as native BEAM cons cells. Tests use Int/Nat elements.

  Scope (revised mid-execution, spec §2 revision):
    * Nested list PATTERNS (`[a,b] ->`) are IN scope — the matrix compiler
      `desugar_nested_arms/2` lowers them before `constructor_pattern/1`.
    * A BARE top-level `[]` body (`fn e() -> List(Int) = []`) now elaborates in
      CHECKED mode (Wave 4 added `:list`/`:pickup` to the `elaborate_body`
      whitelist), pinning the element type from the declared return type. The
      former "infer-only-rejected ledger guard" for this shape was superseded by
      Wave 4's own goal and flipped to `{:ok, _}` below.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  # An empty-list VALUE in a goal-bearing (cons-tail) position — always pinned by
  # the surrounding `[h | _]`, independent of the body-dispatch whitelist.
  test "an empty-list value elaborates in a goal-bearing position" do
    src = "mod M\n  fn single(h: Int) -> List(Int) = [h | []]\nend\n"
    assert {:ok, _} = Program.elaborate(src)
  end

  # WAVE 4 (was a ledger guard): a bare top-level `[]` body now elaborates in
  # CHECKED mode. Wave 4 added `:list` to the `elaborate_body` whitelist
  # (declarations.ex), so the declared return type `List(Int)` pins `Nil`'s
  # element metavariable. This test previously encoded a since-superseded scope
  # decision (not a bug) asserting `{:error, {:unsolved_metavariables, :Nil}}`;
  # the wave's own goal proved it wrong, so the assertion is flipped to `{:ok, _}`.
  test "a bare top-level [] body elaborates in checked mode (Wave 4)" do
    src = "mod M\n  fn e() -> List(Int) = []\nend\n"
    assert {:ok, _} = Program.elaborate(src)
  end

  test "a multi-element list literal elaborates" do
    src = "mod M\n  fn xs() -> List(Int) = [1, 2, 3]\nend\n"
    assert {:ok, _} = Program.elaborate(src)
  end

  test "list sugar and explicit constructors produce identical Core" do
    literal = "mod M\n  fn xs() -> List(Int) = [1, 2, 3]\nend\n"
    explicit = "mod M\n  fn xs() -> List(Int) = Cons(1, Cons(2, Cons(3, Nil())))\nend\n"

    assert {:ok, literal_env} = Program.elaborate(literal)
    assert {:ok, explicit_env} = Program.elaborate(explicit)

    assert Cure.Core.Env.get_def(literal_env, :xs).body == Cure.Core.Env.get_def(explicit_env, :xs).body
  end

  test "list elements inherit a dependent Bounded element goal" do
    src = "mod M\n  use Std.Bounded\n  fn xs() -> List(Bounded(3)) = [0, 1, 2]\nend\n"
    assert {:ok, _} = Program.elaborate(src)
  end

  test "a cons literal elaborates" do
    src = "mod M\n  fn c(h: Int, t: List(Int)) -> List(Int) = [h | t]\nend\n"
    assert {:ok, _} = Program.elaborate(src)
  end

  test "a multi-head cons literal elaborates" do
    # Distinct parser path from both the plain [1,2,3] literal and the single
    # [h|t] cons above: `build_multi_head_cons/3` (parser.ex:837-843) desugars
    # [a, b | rest] right-associatively to [a | [b | rest]] BEFORE this node
    # ever reaches `:list` handling, so this exercises a genuinely different
    # AST shape than either other test (spec §3 antibody 3).
    src =
      "mod M\n  fn c(a: Int, b: Int, rest: List(Int)) -> List(Int) = [a, b | rest]\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end

  test "a one-deep list pattern match elaborates" do
    src =
      @nat <>
        "  fn is_empty(xs: List(Nat)) -> Bool =\n" <>
        "    match xs\n" <>
        "      [] -> true\n" <>
        "      [h | t] -> false\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end

  test "a mismatched-element list is rejected in checked position" do
    src = "mod M\n  fn bad() -> List(Int) = [1, true]\nend\n"
    assert {:error, _} = Program.elaborate(src)
  end

  # SCOPE REVISION (mid-execution): nested list patterns WORK on HEAD via the
  # matrix compiler `desugar_nested_arms/2` (elaborator.ex:2974), invoked by
  # elaborate_match/6 BEFORE constructor_pattern/1 could reject them. The
  # original plan wrongly expected `[a,b]` to be rejected via
  # nested_constructor_arg — that path never fires for list arms. This is now a
  # POSITIVE test (spec §2 revision + antibody 7). Runtime coverage is in Task 3.
  test "a nested list pattern elaborates" do
    src =
      @nat <>
        "  fn f(xs: List(Nat)) -> Bool =\n" <>
        "    match xs\n" <>
        "      [a, b] -> true\n" <>
        "      other -> false\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end

  test "a list literal emits a NATIVE BEAM list" do
    src = "mod M\n  fn xs() -> List(Int) = [1, 2, 3]\nend\n"
    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.List1", functions: [:xs])

    result = apply(mod, :xs, [])
    assert result == [1, 2, 3]
    assert is_list(result)
  end

  # The empty-list VALUE (goal-bearing: a recursion whose base yields []). The
  # bare top-level `fn e() -> List(Int) = []` shape now also elaborates in checked
  # mode (Wave 4, tested above) — this test covers the recursion-base variant.
  test "a recursion base yields the native empty list []" do
    src =
      "mod M\n" <>
        "  fn drop_all(xs: List(Int)) -> List(Int) =\n" <>
        "    match xs\n" <>
        "      [] -> xs\n" <>
        "      [h | t] -> drop_all(t)\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.List2", functions: [:drop_all])
    assert apply(mod, :drop_all, [[1, 2, 3]]) == []
    assert apply(mod, :drop_all, [[]]) == []
  end

  test "[h | t] builds the expected native list" do
    src = "mod M\n  fn c(h: Int, t: List(Int)) -> List(Int) = [h | t]\nend\n"
    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.List3", functions: [:c])
    assert apply(mod, :c, [1, [2, 3]]) == [1, 2, 3]
  end

  test "[a, b | rest] builds the expected native list (multi-head cons)" do
    # Cross-checks against the classic-pipeline oracle
    # test/cure/compiler/multi_head_cons_test.exs (Task 4 Step 3) — this is the
    # only directed test in this suite that exercises build_multi_head_cons/3.
    src =
      "mod M\n  fn c(a: Int, b: Int, rest: List(Int)) -> List(Int) = [a, b | rest]\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.List3b", functions: [:c])
    assert apply(mod, :c, [1, 2, [3, 4]]) == [1, 2, 3, 4]
  end

  test "a one-deep list match selects the arm at runtime" do
    src =
      @nat <>
        "  fn is_empty(xs: List(Nat)) -> Bool =\n" <>
        "    match xs\n" <>
        "      [] -> true\n" <>
        "      [h | t] -> false\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.List4", functions: [:is_empty])
    assert apply(mod, :is_empty, [[]]) == true
    assert apply(mod, :is_empty, [[:Z]]) == false
  end

  # SCOPE REVISION: nested list patterns work (matrix compiler). This proves
  # NATIVE emit preserves nested matching at runtime — the matrix compiler lowers
  # `[a, b]` to a chain of single-level `[H|T]` matches, each hitting
  # list_branch_clause, so native cons cells must select correctly at every level.
  test "a nested list pattern selects the arm at runtime (native emit)" do
    src =
      @nat <>
        "  fn exactly_two(xs: List(Nat)) -> Bool =\n" <>
        "    match xs\n" <>
        "      [a, b] -> true\n" <>
        "      other -> false\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.List5", functions: [:exactly_two])
    assert apply(mod, :exactly_two, [[:Z, :Z]]) == true
    assert apply(mod, :exactly_two, [[:Z]]) == false
    assert apply(mod, :exactly_two, [[]]) == false
    assert apply(mod, :exactly_two, [[:Z, :Z, :Z]]) == false
  end

  # Std.List smoke (Task 4 Step 2): inline a real, confirmed-one-deep Std.List
  # function VERBATIM (cons/2, lib/std/list.cure:84 after Task 1's edit —
  # `fn cons(elem: T, list: List(T)) -> List(T) = [elem | list]`) and run it
  # through the dependent pipeline. Proves the desugar+emit machinery against
  # real stdlib logic and real `List(T)` type-parameter polymorphism, WITHOUT a
  # `use Std.List` (the whole module stays blocked on the bodyless `@extern`
  # length/1 FFI declaration — out of scope this wave, spec §6 — which halts the
  # module before any list function; not a List-surface gap).
  test "a real Std.List one-deep function (cons/2) runs through the dependent pipeline" do
    src = "mod M\n  fn cons(elem: T, list: List(T)) -> List(T) = [elem | list]\nend\n"
    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.ListCons", functions: [:cons])
    assert apply(mod, :cons, [1, [2, 3]]) == [1, 2, 3]
  end
end
