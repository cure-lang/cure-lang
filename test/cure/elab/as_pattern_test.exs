defmodule Cure.Elab.AsPatternTest do
  @moduledoc """
  Parity row #4 (non-constructor patterns) — as-patterns. `name @ <pattern>`
  binds the whole matched value to `name` in addition to destructuring it. Since
  a pattern and its value-reconstruction share the same surface shape, the arm
  lowers (parser `:at` → arm meta `:as_bind`; elaborator `desugar_as_binds`) to
  `<pattern> -> body[name ↦ <pattern>]`, which then flows through nested-pattern
  lowering unchanged. Oracle `match/mt11_as_pattern` pins accept/accept parity.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Emit}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  test "an as-pattern binds the whole value and runs on the BEAM" do
    src =
      @nat <>
        "  fn f(n: Nat) -> Nat = match n\n    w@S(m) -> w\n    Z() -> Z()\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.AsPatternE2E", functions: [:f])

    # `w` is the entire S(...) value, not just its field.
    assert apply(mod, :f, [{:S, {:S, :Z}}]) == {:S, {:S, :Z}}
    assert apply(mod, :f, [:Z]) == :Z
  end

  test "an as-pattern composes with a nested inner pattern and an outer catch-all" do
    src =
      @nat <>
        "  fn f(n: Nat) -> Nat = match n\n    w@S(S(m)) -> w\n    _ -> Z()\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.AsPatternNestedE2E", functions: [:f])

    assert apply(mod, :f, [{:S, {:S, :Z}}]) == {:S, {:S, :Z}}
    assert apply(mod, :f, [{:S, :Z}]) == :Z
  end

  test "a plain match with no as-pattern is unaffected" do
    src = @nat <> "  fn f(n: Nat) -> Nat = match n\n    S(m) -> m\n    Z() -> Z()\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end

  test "a nested as-pattern inside a constructor argument binds the sub-value" do
    src =
      "mod M\n  type Nat = Z | S(Nat)\n  type Lst = Nil | Cons(Nat, Lst)\n" <>
        "  fn f(xs: Lst) -> Lst = match xs\n    Cons(h, t@Cons(y, r)) -> t\n    Cons(h, r) -> r\n    Nil() -> Nil()\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.NestedAsE2E", functions: [:f])

    # `t` is the entire tail Cons(...) sub-value.
    assert apply(mod, :f, [{:Cons, :Z, {:Cons, {:S, :Z}, :Nil}}]) == {:Cons, {:S, :Z}, :Nil}
    # Single-element list falls to the second arm.
    assert apply(mod, :f, [{:Cons, :Z, :Nil}]) == :Nil
  end
end
