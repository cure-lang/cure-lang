defmodule Cure.Elab.LiteralPatternTest do
  @moduledoc """
  Literal patterns on a primitive scrutinee (Int/Bool/Float) desugar to a chain
  of `bool_elim` — there is no inductive `:vdata` to dispatch on. `match n | 0 ->
  a | _ -> b` becomes `bool_elim (n == 0) a b`; `match b | true -> t | false -> f`
  becomes `bool_elim b t f`. Built on the committed `bool_elim` + the
  type-directed equality globals (`int_eq`/`float_eq`, K2 spec 2026-07-09);
  no kernel change.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.{Program, Emit}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  test "integer literal pattern with a catch-all runs on the BEAM" do
    src =
      @nat <>
        "  fn classify(n: Int) -> Nat = match n\n" <>
        "    0 -> Z()\n" <>
        "    1 -> S(Z())\n" <>
        "    m -> S(S(Z()))\n" <>
        "  fn a() -> Nat = classify(0)\n" <>
        "  fn b() -> Nat = classify(1)\n" <>
        "  fn c() -> Nat = classify(9)\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Lit1", functions: [:classify, :a, :b, :c])

    assert apply(mod, :a, []) == :Z
    assert apply(mod, :b, []) == {:S, :Z}
    assert apply(mod, :c, []) == {:S, {:S, :Z}}
  end

  test "negative integer literals stay in the primitive pattern chain" do
    src =
      @nat <>
        "  fn classify(n: Int) -> Nat = match n\n" <>
        "    0 -> Z()\n" <>
        "    -1 -> S(Z())\n" <>
        "    _ -> Z()\n" <>
        "  fn yes() -> Nat = classify(-1)\n" <>
        "  fn no() -> Nat = classify(1)\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.LitNegative", functions: [:classify, :yes, :no])

    assert apply(mod, :yes, []) == {:S, :Z}
    assert apply(mod, :no, []) == :Z
  end

  test "boolean literal pattern (exhaustive, no catch-all) runs on the BEAM" do
    src =
      @nat <>
        "  fn toNat(b: Bool) -> Nat = match b\n    true -> S(Z())\n    false -> Z()\n" <>
        "  fn t() -> Nat = toNat(true)\n  fn f() -> Nat = toNat(false)\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Lit2", functions: [:toNat, :t, :f])

    assert apply(mod, :t, []) == {:S, :Z}
    assert apply(mod, :f, []) == :Z
  end

  test "atom literal patterns dispatch through structural equality" do
    src =
      @nat <>
        "  fn classify(a: Atom) -> Nat = match a\n" <>
        "    :ok -> S(Z())\n" <>
        "    _ -> Z()\n" <>
        "  fn yes() -> Nat = classify(:ok)\n" <>
        "  fn no() -> Nat = classify(:error)\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.LitAtom", functions: [:classify, :yes, :no])

    assert apply(mod, :yes, []) == {:S, :Z}
    assert apply(mod, :no, []) == :Z
  end

  test "= is an ordinary character literal pattern" do
    src = """
    mod CharacterEqualsPattern
      fn classify(value: Char) -> Bool = match value
        '=' -> true
        _ -> false

      fn hit() -> Bool = classify('=')
      fn miss() -> Bool = classify('x')
    end
    """

    {:ok, env} = Program.elaborate(src)

    {:ok, mod} =
      Emit.compile_and_load(env,
        module: :"Cure.CharacterEqualsPattern",
        functions: [:classify, :hit, :miss]
      )

    assert apply(mod, :hit, [])
    refute apply(mod, :miss, [])
  end

  test "string literal patterns reuse nested list-pattern lowering" do
    src =
      @nat <>
        "  fn classify(s: String) -> Nat = match s\n" <>
        "    \"ok\" -> S(Z())\n" <>
        "    _ -> Z()\n" <>
        "  fn yes() -> Nat = classify(\"ok\")\n" <>
        "  fn no() -> Nat = classify(\"error\")\nend\n"

    {:ok, env} = Program.elaborate(src)

    {:ok, mod} =
      Emit.compile_and_load(env,
        module: :"Cure.LitString",
        functions: [:classify, :yes, :no]
      )

    assert apply(mod, :yes, []) == {:S, :Z}
    assert apply(mod, :no, []) == :Z
  end

  test "a named catch-all binds the scrutinee" do
    src =
      @nat <>
        "  fn pred(n: Int) -> Int = match n\n    0 -> 0\n    m -> m\n" <>
        "  fn z() -> Int = pred(0)\n  fn nz() -> Int = pred(7)\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Lit3", functions: [:pred, :z, :nz])

    assert apply(mod, :z, []) == 0
    assert apply(mod, :nz, []) == 7
  end

  test "a binder shadowing a literal catch-all gets exact source roles and a repair" do
    src =
      "mod M\n" <>
        "  fn f(n: Int) -> Int = match n\n" <>
        "    0 -> 0\n" <>
        "    value ->\n" <>
        "      let g : (Int) -> Int = fn(value) -> value\n" <>
        "      g(n)\n" <>
        "end\n"

    assert {:error,
            {:source_context,
             {:unsupported_pattern,
              %{reason: :shadowed_literal_catchall, name: "value", span: outer_span, shadow_span: shadow_span}}, _} =
              error} = Program.elaborate(src)

    assert {outer_span.start_line, outer_span.start_column} == {4, 5}
    assert {shadow_span.start_line, shadow_span.start_column} == {5, 33}

    {diagnostic, registry} = Errors.to_diagnostic(error, "literal_catchall_shadow.cure", src)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- NESTED PATTERN SHADOWS `VALUE` [E090] ---------- literal_catchall_shadow.cure

             After the preceding literal patterns fail, this catch-all binds the remaining
             value as `value`. A binder inside the branch uses the same name, so substituting
             the scrutinee could capture the inner value.

             at literal_catchall_shadow.cure:5:33
             2 |   fn f(n: Int) -> Int = match n
               |                               - this is the value tested by the literal patterns
             3 |     0 -> 0
             4 |     value ->
               |     ----- this outer pattern binds `value`
             5 |       let g : (Int) -> Int = fn(value) -> value
               |                                 ^^^^^ rename this inner binder so it does not shadow `value`

             Hint: Give the nested binder a different name and update its branch body
             """)

    lsp = Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 4, "character" => 32},
             "end" => %{"line" => 4, "character" => 37}
           }

    assert Enum.map(lsp["relatedInformation"], & &1["location"]["range"]) == [
             %{
               "start" => %{"line" => 3, "character" => 4},
               "end" => %{"line" => 3, "character" => 9}
             },
             %{
               "start" => %{"line" => 1, "character" => 30},
               "end" => %{"line" => 1, "character" => 31}
             }
           ]

    assert lsp["data"]["payload"] == %{
             "checking" => "f",
             "kind" => "unsupported_pattern",
             "name" => "value",
             "reason" => "shadowed_literal_catchall"
           }

    fixed = String.replace(src, "fn(value) -> value", "fn(other) -> other")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "literal_catchall_shadow_fixed.cure")
  end
end
