defmodule Cure.Elab.PolymorphicFunctionTest do
  @moduledoc """
  Polymorphic functions via implicit type parameters (Idris parity). A bare
  implicit parameter `{a}` (Cure's `{name}` erased-argument syntax) carried no
  kind, so `elaborate_param_telescope` rejected it with `{:untyped_parameter, …}`.
  A bare implicit type variable ranges over `Type`, so its kind now defaults to
  `Type` (erased) — exactly like `{a: Type}`. The implicit is then solved from the
  present arguments by the existing metavariable machinery (`elaborate_global_app`
  / `solve_arg`), so `id`, `const`, and polymorphic higher-order functions type
  and run.

  Oracle `func/fn05_poly_id` + `func/fn06_poly_const` pin accept/accept.

  Not covered here: solving a constructor's implicit parameter from an *expected*
  type (`fn g() -> List(Nat) = Nil()` — the return annotation is not propagated
  into constructor implicit-solving). That is checking-mode constructor
  elaboration, a separate reach.
  """
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.{Emit, Program}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  test "the polymorphic identity function types and runs" do
    src = @nat <> "  fn id({a}, x: a) -> a = x\n  fn g() -> Nat = id(S(Z()))\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.PfId", functions: [:id, :g])

    assert apply(mod, :g, []) == {:S, :Z}
  end

  test "a two-type-parameter const function selects the first argument" do
    src =
      @nat <>
        "  fn const({a}, {b}, x: a, y: b) -> a = x\n  fn g() -> Nat = const(S(Z()), Z())\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.PfConst", functions: [:const, :g])

    assert apply(mod, :g, []) == {:S, :Z}
  end

  test "a polymorphic higher-order function applies its function argument" do
    src =
      @nat <>
        "  fn ap({a}, {b}, f: (a) -> b, x: a) -> b = f(x)\n  fn inc(n: Nat) -> Nat = S(n)\n" <>
        "  fn g() -> Nat = ap(inc, S(Z()))\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.PfAp", functions: [:ap, :inc, :g])

    # ap(inc, S(Z)) = inc(S(Z)) = S(S(Z)).
    assert apply(mod, :g, []) == {:S, {:S, :Z}}
  end

  test "an untyped explicit (non-implicit) parameter is still rejected" do
    # The Type-default applies ONLY to implicit `{a}`; a bare value parameter with
    # no type annotation remains an error.
    source = @nat <> "  fn f(x) -> Nat = Z()\nend\n"

    assert {:error, {:untyped_parameter, %{name: "x"}} = error} = Program.elaborate(source)

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic(error, "untyped_parameter.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- I NEED A TYPE FOR `X` [E093] ------------------------- untyped_parameter.cure

             Cure cannot tell what values `x` may receive from its name alone. Every ordinary
             function parameter needs a type annotation.

             at untyped_parameter.cure:3:8
             3 |   fn f(x) -> Nat = Z()
               |        ^ this parameter needs a type after its name

             Hint: Add a type annotation, such as `x: Int`; write `{x}` only for an implicit type parameter
             """)

    lsp = Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 2, "character" => 7},
             "end" => %{"line" => 2, "character" => 8}
           }

    assert lsp["data"]["payload"] == %{
             "kind" => "untyped_parameter",
             "name" => "x"
           }

    assert [%{"applicability" => "manual", "edits" => []}] = lsp["data"]["suggestions"]

    assert {:ok, _environment} =
             source
             |> String.replace("f(x)", "f(x: Nat)")
             |> Program.elaborate(file: "fixed_parameter.cure")
  end

  @lst "mod M\n  type Nat = Z | S(Nat)\n  type Lst(a) = Nil | Cons(a, Lst(a))\n"

  test "an implicit solved from an early argument lets a later underdetermined argument check" do
    # `firstOr(Z(), Cons(S(Z()), Nil()))`: the list argument is underdetermined in
    # isolation (its inner `Nil()` has no parameter), so up-front inference fails.
    # The bidirectional fallback solves `a = Nat` from the first argument `Z()`,
    # then checks `Cons(S(Z()), Nil())` against `Lst(Nat)`. Oracle
    # `poly/pl05_implicit_solved_arg`.
    src =
      @lst <>
        "  fn firstOr({a}, d: a, l: Lst(a)) -> a = match l\n    Cons(x, xs) -> x\n    Nil() -> d\n" <>
        "  fn g() -> Nat = firstOr(Z(), Cons(S(Z()), Nil()))\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.FirstOr", functions: [:firstOr, :g])

    assert apply(mod, :g, []) == {:S, :Z}
  end

  test "a wrongly-typed underdetermined argument is still rejected" do
    assert {:error, _} =
             Program.elaborate(
               @lst <>
                 "  type Bool = T | F\n" <>
                 "  fn firstOr({a}, d: a, l: Lst(a)) -> a = d\n" <>
                 "  fn g() -> Nat = firstOr(Z(), Cons(T(), Nil()))\nend\n"
             )
  end
end
