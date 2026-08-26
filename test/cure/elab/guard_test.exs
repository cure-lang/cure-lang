defmodule Cure.Elab.GuardTest do
  @moduledoc """
  Boolean `when` guards on a variable/catch-all pattern desugar to a chain of
  `bool_elim`: `match n | x when g -> a | x -> b` becomes `bool_elim g a b`,
  with each guard test its own Boolean elimination and the final unguarded
  catch-all closing the chain (the fall-through when every guard is false).

  Guards need surface comparison operators to elaborate, so `{:binary_op}`
  lowers to a builtin-op global spine (K2, spec 2026-07-09; e.g. `x == 0` ->
  `int_eq x 0`). Both build on the committed `bool_elim`; no kernel change.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.{Program, Emit}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  test "a surface comparison operator elaborates and runs on the BEAM" do
    src =
      "mod M\n" <>
        "  fn eq0(n: Int) -> Bool = n == 0\n" <>
        "  fn t() -> Bool = eq0(0)\n  fn f() -> Bool = eq0(7)\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Guard0", functions: [:eq0, :t, :f])

    assert apply(mod, :t, []) == true
    assert apply(mod, :f, []) == false
  end

  test "a single guard with a catch-all fallback runs on the BEAM" do
    src =
      @nat <>
        "  fn classify(n: Int) -> Nat = match n\n" <>
        "    x when x == 0 -> Z()\n" <>
        "    x -> S(Z())\n" <>
        "  fn a() -> Nat = classify(0)\n" <>
        "  fn b() -> Nat = classify(1)\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Guard1", functions: [:classify, :a, :b])

    assert apply(mod, :a, []) == :Z
    assert apply(mod, :b, []) == {:S, :Z}
  end

  test "a chain of guards falls through to the correct arm on the BEAM" do
    src =
      @nat <>
        "  fn classify(n: Int) -> Nat = match n\n" <>
        "    x when x == 0 -> Z()\n" <>
        "    x when x == 1 -> S(Z())\n" <>
        "    x -> S(S(Z()))\n" <>
        "  fn a() -> Nat = classify(0)\n" <>
        "  fn b() -> Nat = classify(1)\n" <>
        "  fn c() -> Nat = classify(9)\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Guard2", functions: [:classify, :a, :b, :c])

    assert apply(mod, :a, []) == :Z
    assert apply(mod, :b, []) == {:S, :Z}
    assert apply(mod, :c, []) == {:S, {:S, :Z}}
  end

  test "multi-parameter function clauses bind tuple leaves in guards and bodies" do
    src = """
    mod M
      fn choose(char: Char, fallback: Char) -> Char
        | char, fallback when char == '.' -> char
        | _, fallback -> fallback

      fn hit() -> Char = choose('.', 'x')
      fn miss() -> Char = choose('a', 'x')
    end
    """

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.GuardMulti", functions: [:choose, :hit, :miss])

    assert apply(mod, :hit, []) == ?.
    assert apply(mod, :miss, []) == ?x
  end

  test "guarded tuple matrices bind constructor payloads and preserve ordered fallthrough" do
    src = """
    mod M
      type State = Counting | Done
      type Event = Tick(Int) | Finish

      fn decide(state: State, event: Event, data: Int) -> Int
        | Counting(), Tick(amount), data when amount > 0 -> data + amount
        | Counting(), Tick(_), data -> data
        | _, _, _ -> 0

      fn positive() -> Int = decide(Counting(), Tick(3), 10)
      fn guarded_fallthrough() -> Int = decide(Counting(), Tick(0), 10)
      fn pattern_fallthrough() -> Int = decide(Done(), Finish(), 10)
    end
    """

    {:ok, env} = Program.elaborate(src)

    {:ok, mod} =
      Emit.compile_and_load(env,
        module: :"Cure.GuardedTupleMatrix",
        functions: [:decide, :positive, :guarded_fallthrough, :pattern_fallthrough]
      )

    assert apply(mod, :positive, []) == 13
    assert apply(mod, :guarded_fallthrough, []) == 10
    assert apply(mod, :pattern_fallthrough, []) == 0
  end

  test "a let-bound tuple supports ordered constructor rows" do
    src = """
    mod M
      type State = Open | Closed
      type Event = Shut | OpenDoor

      fn responds(state: State, event: Event) -> Bool =
        let key = %[state, event]
        match key
          %[Open(), Shut()] -> true
          %[_, _] -> false

      fn hit() -> Bool = responds(Open(), Shut())
      fn miss() -> Bool = responds(Closed(), OpenDoor())
    end
    """

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.LetBoundTupleMatrix", functions: [:responds, :hit, :miss])

    assert apply(mod, :hit, [])
    refute apply(mod, :miss, [])
  end

  test "where helpers support one structural parameter column across arities 2 through 6" do
    src = """
    mod M
      use Std.List

      fn arity2(values: List(Int), a: Int) -> Int = classify2(values, a)
      where
        fn classify2(values: List(Int), a: Int) -> Int
          | [], a -> a
          | _, _ -> 20

      fn arity3(a: Int, values: List(Int), b: Int) -> Int = classify3(a, values, b)
      where
        fn classify3(a: Int, values: List(Int), b: Int) -> Int
          | a, [], b -> a + b
          | _, _, _ -> 30

      fn arity4(a: Int, b: Int, c: Int, values: List(Int)) -> Int = classify4(a, b, c, values)
      where
        fn classify4(a: Int, b: Int, c: Int, values: List(Int)) -> Int
          | a, b, c, [] -> a + b + c
          | _, _, _, _ -> 40

      fn arity5(a: Int, values: List(Int), b: Int, c: Int, d: Int) -> Int = classify5(a, values, b, c, d)
      where
        fn classify5(a: Int, values: List(Int), b: Int, c: Int, d: Int) -> Int
          | a, [], b, c, d -> a + b + c + d
          | _, _, _, _, _ -> 50

      fn arity6(values: List(Int), a: Int, b: Int, c: Int, d: Int, e: Int) -> Int = classify6(values, a, b, c, d, e)
      where
        fn classify6(values: List(Int), a: Int, b: Int, c: Int, d: Int, e: Int) -> Int
          | [], a, b, c, d, e -> a + b + c + d + e
          | _, _, _, _, _, _ -> 60

      fn a2_empty() -> Int = arity2([], 7)
      fn a2_present() -> Int = arity2([1], 7)
      fn a3_empty() -> Int = arity3(2, [], 3)
      fn a3_present() -> Int = arity3(2, [1], 3)
      fn a4_empty() -> Int = arity4(1, 2, 3, [])
      fn a4_present() -> Int = arity4(1, 2, 3, [1])
      fn a5_empty() -> Int = arity5(1, [], 2, 3, 4)
      fn a5_present() -> Int = arity5(1, [1], 2, 3, 4)
      fn a6_empty() -> Int = arity6([], 1, 2, 3, 4, 5)
      fn a6_present() -> Int = arity6([1], 1, 2, 3, 4, 5)
    end
    """

    {:ok, env} = Program.elaborate(src)

    roots = [
      :a2_empty,
      :a2_present,
      :a3_empty,
      :a3_present,
      :a4_empty,
      :a4_present,
      :a5_empty,
      :a5_present,
      :a6_empty,
      :a6_present
    ]

    functions = Program.reachable_def_names(env, roots)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.WhereStructuralColumn", functions: functions)

    assert apply(mod, :a2_empty, []) == 7
    assert apply(mod, :a2_present, []) == 20
    assert apply(mod, :a3_empty, []) == 5
    assert apply(mod, :a3_present, []) == 30
    assert apply(mod, :a4_empty, []) == 6
    assert apply(mod, :a4_present, []) == 40
    assert apply(mod, :a5_empty, []) == 10
    assert apply(mod, :a5_present, []) == 50
    assert apply(mod, :a6_empty, []) == 15
    assert apply(mod, :a6_present, []) == 60
  end

  test "a guard whose test is false and has no fallback is rejected (non-exhaustive)" do
    src =
      @nat <>
        "  fn classify(n: Int) -> Nat = match n\n" <>
        "    x when x == 0 -> Z()\n" <>
        "    x when x == 1 -> S(Z())\nend\n"

    assert {:error, _} = Program.elaborate(src)
  end

  test "a fallback binder shadowed inside its branch labels both bindings" do
    src =
      @nat <>
        "  fn f(n: Int) -> Nat = match n\n" <>
        "    x when x == 0 -> Z()\n" <>
        "    x ->\n" <>
        "      let g : (Int) -> Nat = fn(x) -> Z()\n" <>
        "      g(x)\n" <>
        "end\n"

    assert {:error,
            {:source_context,
             {:unsupported_guard,
              %{reason: :shadowed, name: "x", site: :body, span: outer_span, shadow_span: shadow_span}}, _} =
              error} = Program.elaborate(src)

    assert {outer_span.start_line, outer_span.start_column} == {5, 5}
    assert {shadow_span.start_line, shadow_span.start_column} == {6, 33}

    {diagnostic, registry} = Errors.to_diagnostic(error, "guard_shadow.cure", src)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- FALLBACK BRANCH SHADOWS `X` [E090] ------------------------ guard_shadow.cure

             This fallback branch substitutes the matched value for `x`, but a binder inside
             the branch uses the same name. That substitution could capture the inner value.

             at guard_shadow.cure:6:33
             5 |     x ->
               |     - this guard pattern binds `x`
             6 |       let g : (Int) -> Nat = fn(x) -> Z()
               |                                 ^ rename this inner binder so it does not shadow `x`

             Hint: Give the nested binder a different name and update its branch expression
             """)

    lsp = Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 5, "character" => 32},
             "end" => %{"line" => 5, "character" => 33}
           }

    assert [related] = lsp["relatedInformation"]

    assert related["location"]["range"] == %{
             "start" => %{"line" => 4, "character" => 4},
             "end" => %{"line" => 4, "character" => 5}
           }

    assert lsp["data"]["payload"] == %{
             "checking" => "f",
             "kind" => "unsupported_guard",
             "name" => "x",
             "reason" => "shadowed",
             "site" => "body"
           }

    fixed = String.replace(src, "fn(x) -> Z()", "fn(value) -> Z()")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "guard_shadow_fixed.cure")
  end

  test "a refutable literal guard points at the pattern and condition" do
    src =
      @nat <>
        "  fn f(n: Int) -> Nat = match n\n" <>
        "    0 when true -> Z()\n" <>
        "    _ -> S(Z())\n" <>
        "end\n"

    assert {:error,
            {:source_context, {:unsupported_guard, %{reason: :refutable_pattern, shape: :literal, span: pattern_span}},
             _} = error} =
             Program.elaborate(src)

    assert {pattern_span.start_line, pattern_span.start_column} == {4, 5}

    {diagnostic, registry} = Errors.to_diagnostic(error, "literal_guard.cure", src)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- LITERAL PATTERN CANNOT CARRY THIS GUARD [E093] ----------- literal_guard.cure

             This literal pattern can fail before its `when` condition is considered. The
             current guard chain only accepts variable, wildcard, or irrefutable tuple
             patterns.

             at literal_guard.cure:4:5
             4 |     0 when true -> Z()
               |     ^      ---- this refutable pattern cannot enter the guard chain; this condition is attached to the refutable pattern

             Hint: Match this pattern first, then test the condition inside its branch and keep an explicit fallback
             """)

    lsp = Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 3, "character" => 4},
             "end" => %{"line" => 3, "character" => 5}
           }

    assert [related] = lsp["relatedInformation"]

    assert related["location"]["range"] == %{
             "start" => %{"line" => 3, "character" => 11},
             "end" => %{"line" => 3, "character" => 15}
           }

    assert lsp["data"]["payload"] == %{
             "checking" => "f",
             "kind" => "unsupported_guard",
             "reason" => "refutable_pattern",
             "shape" => "literal"
           }

    fixed = String.replace(src, "    0 when true -> Z()\n", "    0 -> Z()\n")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "literal_guard_fixed.cure")
  end

  test "a guarded non-variable scrutinee with a named fallback is evaluated once" do
    src =
      @nat <>
        "  fn f(n: Nat) -> Nat = match S(n)\n" <>
        "    S(x) when true -> x\n" <>
        "    other -> other\n" <>
        "end\n"

    {:ok, environment} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(environment, module: :"Cure.GuardStableScrutinee", functions: [:f])

    assert apply(mod, :f, [:Z]) == :Z
    assert apply(mod, :f, [{:S, :Z}]) == {:S, :Z}
  end

  test "guard lowering preserves the duplicate catch-all diagnostic" do
    src =
      @nat <>
        "  fn f(n: Nat) -> Nat = match n\n" <>
        "    S(x) when true -> x\n" <>
        "    a -> a\n" <>
        "    b -> b\n" <>
        "end\n"

    assert {:error, {:source_context, {:duplicate_default_pattern, "b"}, _} = error} =
             Program.elaborate(src)

    {diagnostic, registry} = Errors.to_diagnostic(error, "guard_defaults.cure", src)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- PATTERN MATCH HAS MORE THAN ONE CATCH-ALL [E119] -------- guard_defaults.cure

             A variable or `_` pattern matches every value not handled above it, so a later
             catch-all can never be reached.

             at guard_defaults.cure:6:5
             5 |     a -> a
               |     - this earlier pattern already matches every remaining value
             6 |     b -> b
               |     ^ this catch-all is unreachable

             Hint: Keep one final catch-all branch and remove or narrow the others
             """)

    lsp = Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 5, "character" => 4},
             "end" => %{"line" => 5, "character" => 5}
           }

    assert [related] = lsp["relatedInformation"]

    assert related["location"]["range"] == %{
             "start" => %{"line" => 4, "character" => 4},
             "end" => %{"line" => 4, "character" => 5}
           }

    assert lsp["data"]["payload"] == %{
             "checking" => "f",
             "kind" => "duplicate_default_pattern",
             "name" => "b"
           }

    fixed = String.replace(src, "    b -> b\n", "")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "guard_defaults_fixed.cure")
  end
end
