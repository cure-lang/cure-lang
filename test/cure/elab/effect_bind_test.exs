defmodule Cure.Elab.EffectBindTest do
  @moduledoc """
  Effectful `let`-sequencing lowers to the kernel's inert `bind`
  (design 2026-07-09-effect-type-former §5.1). A `let x = eff()` whose rhs is
  `Effect(T)` must NOT bind `x : Effect(T)` via the Core `:let`; it desugars to
  `bind(eff, λ x:T. rest)`, so the continuation binds the UNWRAPPED payload
  `x : T` (Idris's `x <- eff; rest` desugars to `eff >>= (fn x => rest)`). The final
  expression of an `Effect(R)`-typed block is `pure`-wrapped when it is a plain
  value. The kernel re-checks every emitted `effect_bind`/`effect_pure`.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program
  alias Cure.Core.Env

  @omega Cure.Core.Grade.unrestricted()

  defp body(env, name), do: Env.get_def(env, name).body

  @externs """
    @extern(:erlang, :make_ref, 0)
    fn mkref() -> Effect(Int)
    @extern(:erlang, :abs, 1)
    fn eff_abs(n: Int) -> Effect(Int)
    @extern(:erlang, :max, 2)
    fn eff_add(a: Int, b: Int) -> Effect(Int)
  """

  describe "let x = eff() ⏎ rest  ⟶  bind(eff, λ x:T. rest)" do
    test "sequencing with an effectful final expression" do
      src =
        "mod M\n" <>
          @externs <>
          "  fn f() -> Effect(Int) =\n    let x = mkref()\n    eff_abs(x)\n" <>
          "end\n"

      assert {:ok, env} = Program.elaborate(src)

      # The continuation binds x : Int (NOT Effect(Int)); the body is the
      # effectful `eff_abs(x)` call, so it is NOT a pure-wrap.
      assert {:effect_bind, _mkref, {:lam, @omega, {:data, :"Std.Int#Int", [], []}, inner}} = body(env, :f)
      refute match?({:effect_pure, _}, inner)
    end

    test "pure insertion: a plain-value final is wrapped in pure" do
      src =
        "mod M\n" <>
          @externs <>
          "  fn g() -> Effect(Int) =\n    let x = mkref()\n    x\n" <>
          "end\n"

      assert {:ok, env} = Program.elaborate(src)

      assert {:effect_bind, _mkref, {:lam, @omega, {:data, :"Std.Int#Int", [], []}, {:effect_pure, {:var, 0}}}} =
               body(env, :g)
    end

    test "two binds nest into two effect_binds" do
      src =
        "mod M\n" <>
          @externs <>
          "  fn h() -> Effect(Int) =\n    let x = mkref()\n    let y = mkref()\n    eff_add(x, y)\n" <>
          "end\n"

      assert {:ok, env} = Program.elaborate(src)

      assert {:effect_bind, _mkref1,
              {:lam, @omega, {:data, :"Std.Int#Int", [], []},
               {:effect_bind, _mkref2, {:lam, @omega, {:data, :"Std.Int#Int", [], []}, _inner}}}} = body(env, :h)
    end
  end

  describe "no silent escape" do
    test "an effectful let in a pure-typed (-> Int) function is rejected" do
      # The block elaborates to `bind(mkref, λ x:Int. x) : Effect(Int)`, which the
      # kernel checks against the declared `Int` and rejects.
      src =
        "mod M\n" <>
          @externs <>
          "  fn bad() -> Int =\n    let x = mkref()\n    x\n" <>
          "end\n"

      assert {:error, _} = Program.elaborate(src)
    end
  end
end
