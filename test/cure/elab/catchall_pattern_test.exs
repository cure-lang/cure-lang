defmodule Cure.Elab.CatchallPatternTest do
  @moduledoc """
  Parity row #4 (non-constructor patterns in dependent position) — the
  variable/wildcard **catch-all** slice. A `match` arm whose pattern is a bare
  variable (`x -> …`) or wildcard (`_ -> …`) covers every constructor not
  explicitly matched, binding the scrutinee (Idris/Lean variable-pattern
  coverage). Oracle `match/mt06_var_catchall` pins accept/accept parity.

  Implemented purely in the elaborator (E): each un-matched constructor is
  reconstructed as `cname(fresh…)`, the catch-all's name is substituted by that
  reconstruction, and the branch routes through the ordinary matched-branch path
  — so index inversion and goal refinement still apply and an unsound catch-all
  body is still rejected by the kernel. No TCB change.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.{Program, Emit}

  @dep_hdr "mod M\n  type Dec = DDec | DCau\n  type G indices (d: Dec)\n    mkd : G(DDec)\n    seqg : G(d1) -> G(d2) -> G(DCau)\n"

  test "non-dependent variable catch-all covers all un-matched constructors" do
    src =
      "mod M\n  type Color = Red | Green | Blue\n  fn f(c: Color) -> Color = match c\n    Red() -> Blue()\n    other -> other\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end

  test "wildcard catch-all elaborates" do
    src =
      "mod M\n  type Color = Red | Green | Blue\n  fn f(c: Color) -> Color = match c\n    Red() -> Blue()\n    _ -> Red()\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end

  test "catch-all alone (no explicit constructor arms) binds the scrutinee" do
    src = "mod M\n  type Color = Red | Green | Blue\n  fn id2(c: Color) -> Color = match c\n    x -> x\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end

  test "a binder shadowing a lone catch-all gets exact source roles and a repair" do
    src =
      "mod M\n" <>
        "  type Nat = Z | S(Nat)\n" <>
        "  fn f(n: Nat) -> Nat = match n\n" <>
        "    value ->\n" <>
        "      let g : (Nat) -> Nat = fn(value) -> value\n" <>
        "      g(n)\n" <>
        "end\n"

    assert {:error,
            {:source_context,
             {:unsupported_pattern,
              %{reason: :shadowed_catchall, name: "value", span: outer_span, shadow_span: shadow_span}}, _} =
              error} = Program.elaborate(src)

    assert {outer_span.start_line, outer_span.start_column} == {4, 5}
    assert {shadow_span.start_line, shadow_span.start_column} == {5, 33}

    {diagnostic, registry} = Errors.to_diagnostic(error, "catchall_shadow.cure", src)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- NESTED PATTERN SHADOWS `VALUE` [E090] ------------------ catchall_shadow.cure

             This catch-all pattern binds the complete matched value as `value`. A binder
             inside the branch uses the same name, so substituting the scrutinee could
             capture the inner value.

             at catchall_shadow.cure:5:33
             3 |   fn f(n: Nat) -> Nat = match n
               |                               - this is the value bound by the catch-all
             4 |     value ->
               |     ----- this outer pattern binds `value`
             5 |       let g : (Nat) -> Nat = fn(value) -> value
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
               "start" => %{"line" => 2, "character" => 30},
               "end" => %{"line" => 2, "character" => 31}
             }
           ]

    assert lsp["data"]["payload"] == %{
             "checking" => "f",
             "kind" => "unsupported_pattern",
             "name" => "value",
             "reason" => "shadowed_catchall"
           }

    fixed = String.replace(src, "fn(value) -> value", "fn(other) -> other")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "catchall_shadow_fixed.cure")
  end

  test "fallback shadowing is rejected before join sharing and labels both binders" do
    src =
      "mod M\n" <>
        "  type Color = Red | Green | Blue | Gold\n" <>
        "  fn f(c: Color) -> Color = match c\n" <>
        "    Red() -> Red()\n" <>
        "    rest ->\n" <>
        "      let g : (Color) -> Color = fn(rest) -> rest\n" <>
        "      g(c)\n" <>
        "end\n"

    assert {:error,
            {:source_context,
             {:unsupported_pattern,
              %{reason: :shadowed_default, name: "rest", span: outer_span, shadow_span: shadow_span}}, _} =
              error} = Program.elaborate(src)

    assert {outer_span.start_line, outer_span.start_column} == {5, 5}
    assert {shadow_span.start_line, shadow_span.start_column} == {6, 37}

    {diagnostic, registry} = Errors.to_diagnostic(error, "default_shadow.cure", src)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- NESTED PATTERN SHADOWS `REST` [E090] -------------------- default_shadow.cure

             This fallback pattern binds every constructor not handled above as `rest`. A
             binder inside the fallback branch uses the same name, so reconstructing an
             omitted constructor could capture the inner value.

             at default_shadow.cure:6:37
             5 |     rest ->
               |     ---- this outer pattern binds `rest`
             6 |       let g : (Color) -> Color = fn(rest) -> rest
               |                                     ^^^^ rename this inner binder so it does not shadow `rest`

             Hint: Give the nested binder a different name and update its branch body
             """)

    lsp = Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 5, "character" => 36},
             "end" => %{"line" => 5, "character" => 40}
           }

    assert Enum.map(lsp["relatedInformation"], & &1["location"]["range"]) == [
             %{
               "start" => %{"line" => 4, "character" => 4},
               "end" => %{"line" => 4, "character" => 8}
             }
           ]

    assert lsp["data"]["payload"] == %{
             "checking" => "f",
             "kind" => "unsupported_pattern",
             "name" => "rest",
             "reason" => "shadowed_default"
           }

    fixed = String.replace(src, "fn(rest) -> rest", "fn(other) -> other")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "default_shadow_fixed.cure")
  end

  test "dependent catch-all reconstructs each constructor at its refined index" do
    # `x -> x`: the seqg branch refines `d := DCau`, and the reconstructed `x`
    # (= seqg(…) : G(DCau)) must match the branch-refined goal G(DCau).
    src = @dep_hdr <> "  fn f({d: Dec}, s: G(d)) -> G(d) = match s\n    mkd() -> mkd()\n    x -> x\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end

  test "SOUNDNESS: catch-all covering a reachable constructor at the wrong index is rejected" do
    # Goal is the CONCRETE G(DDec). The catch-all covers the reachable `seqg`
    # branch, where the reconstructed value has type G(DCau). DCau ≢ DDec, so the
    # branch's conversion must reject — the catch-all does not bypass the kernel.
    src = @dep_hdr <> "  fn f({d: Dec}, s: G(d)) -> G(DDec) = match s\n    mkd() -> mkd()\n    x -> x\nend\n"

    assert {:error, _} = Program.elaborate(src)
  end

  test "two catch-alls in one match are rejected" do
    src =
      "mod M\n  type Color = Red | Green | Blue\n  fn f(c: Color) -> Color = match c\n    x -> x\n    y -> y\nend\n"

    assert {:error, {:source_context, {:duplicate_default_pattern, _}, _}} = Program.elaborate(src)
  end

  test "the catch-all runs on the BEAM, covering every un-matched constructor" do
    src =
      "mod M\n  type Color = Red | Green | Blue\n  type Nat = Z | S(Nat)\n  fn tag(c: Color) -> Nat = match c\n    Red() -> Z()\n    other -> S(Z())\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.CatchAllPatternE2E", functions: [:tag])

    assert apply(mod, :tag, [:Red]) == :Z
    assert apply(mod, :tag, [:Green]) == {:S, :Z}
    assert apply(mod, :tag, [:Blue]) == {:S, :Z}
  end

  # Row #4 residual: a *named* default over a *non-variable* scrutinee combined
  # with a *nested* arm (`match S(n) | S(Z()) -> … | other -> …`). There is no
  # variable to bind `other` to, so the match path hoists the scrutinee into a
  # fresh `let $s = S(n) in match $s | …`, letting the whole variable-scrutinee
  # machinery apply and binding `other` to `$s` (evaluated once, as Idris'
  # `case … of other =>`). Oracle `match/mt22_nested_named_default_nonvar` pins
  # accept/accept parity.
  test "named default over a non-variable scrutinee with nesting elaborates" do
    src =
      "mod M\n  type Nat = Z | S(Nat)\n  fn f(n: Nat) -> Nat = match S(n)\n    S(Z()) -> Z()\n    other -> other\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end

  test "the hoisted named default binds the whole scrutinee, once, on the BEAM" do
    src =
      "mod M\n  type Nat = Z | S(Nat)\n  fn f(n: Nat) -> Nat = match S(n)\n    S(Z()) -> Z()\n    other -> other\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.NestedNamedDefaultE2E", functions: [:f])

    # f(Z): scrutinee S(Z) matches S(Z()) → Z.
    assert apply(mod, :f, [:Z]) == :Z
    # f(S(Z)): scrutinee S(S(Z)) misses S(Z()) → falls to `other` = the whole
    # scrutinee S(S(Z)), proving the named default binds the hoisted value.
    assert apply(mod, :f, [{:S, :Z}]) == {:S, {:S, :Z}}
  end
end
