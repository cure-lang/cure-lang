defmodule Cure.Elab.TotalDecoratorTest do
  @moduledoc """
  `@total true` — a per-declaration opt-in to the compile-time totality proof
  (`docs/LANGUAGE_SPEC.md` §Totality, §4.3).

  The decorator is attached generically by the parser to the `function_def` meta;
  `Declarations` turns it into an obligation on the environment, and the program
  pipeline rejects the module unless the kernel certifies every required def
  total. `@total false` is an explicit opt-out and registers nothing. A malformed
  `@total` is a compile error, never a silently-absent declaration.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  # A structurally-total function: the recursive call shrinks its argument.
  @total_fn """
  fn count(n: Nat) -> Nat = match n
    Z() -> Z()
    S(k) -> S(count(k))
  """
  # A non-terminating function: the recursive call GROWS its argument. It is not
  # referenced from any type, so only an explicit `@total true` can force a proof.
  @diverging_fn """
  fn down(n: Nat) -> Nat = match n
    Z() -> Z()
    S(k) -> down(S(k))
  """

  # Indent every non-empty line of `body` by two spaces so it sits inside `mod M`.
  defp in_module(decorator, body) do
    "mod M\n" <> decorator <> indent(body) <> "end\n"
  end

  defp indent(text) do
    text
    |> String.split("\n", trim: false)
    |> Enum.map_join("\n", fn
      "" -> ""
      line -> "  " <> line
    end)
  end

  test "a total function marked @total true elaborates" do
    src = in_module("  @total true\n", @total_fn)
    assert {:ok, env} = Program.elaborate(src)
    assert Cure.Core.Env.total_required?(env, :count)
    assert Cure.Core.Env.total?(env, :count)
  end

  test "@total true on a non-terminating function is rejected" do
    src = in_module("  @total true\n", @diverging_fn)

    assert {:error, error} = Program.elaborate(src, file: "total.cure")
    assert {:total_required_by_decorator, :"M#down"} = Program.semantic_error(error)
  end

  test "the same non-terminating function without @total is allowed" do
    # Runtime-only partial functions may remain partial; only the explicit
    # opt-in (or a type-level use) forces a proof.
    src = in_module("", @diverging_fn)
    assert {:ok, env} = Program.elaborate(src)
    refute Cure.Core.Env.total_required?(env, :down)
  end

  test "@total false is an explicit opt-out and registers no obligation" do
    src = in_module("  @total false\n", @diverging_fn)
    assert {:ok, env} = Program.elaborate(src)
    refute Cure.Core.Env.total_required?(env, :down)
  end

  test "a bare @total is a compile error, not a silently-absent declaration" do
    src = in_module("  @total\n", @total_fn)

    assert {:error, error} = Program.elaborate(src, file: "bare.cure")
    assert {:total_bad_argument, :count, :missing_argument} = Program.semantic_error(error)
  end

  test "@total with a non-boolean argument is a compile error" do
    src = in_module("  @total 5\n", @total_fn)

    assert {:error, error} = Program.elaborate(src, file: "nonbool.cure")
    assert {:total_bad_argument, :count, {:not_boolean, 5}} = Program.semantic_error(error)
  end

  test "@total with too many arguments is a compile error" do
    src = in_module("  @total(true, false)\n", @total_fn)

    assert {:error, error} = Program.elaborate(src, file: "many.cure")
    assert {:total_bad_argument, :count, {:too_many_arguments, 2}} = Program.semantic_error(error)
  end

  test "the unproven @total renders the E013 totality diagnostic" do
    src = in_module("  @total true\n", @diverging_fn)

    assert {:error, error} = Program.elaborate(src, file: "total.cure")
    {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(error, "total.cure", src)
    rendered = Cure.Diagnostic.Renderer.plain(diagnostic, registry, width: 80)

    assert diagnostic.code == "E013"
    assert diagnostic.key == :total_decorator_unproven
    assert rendered =~ "marked `@total true`"
    assert rendered =~ "down"
  end

  test "the malformed-@total diagnostic names the mistake" do
    src = in_module("  @total\n", @total_fn)

    assert {:error, error} = Program.elaborate(src, file: "bare.cure")
    {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(error, "bare.cure", src)
    rendered = Cure.Diagnostic.Renderer.plain(diagnostic, registry, width: 80)

    assert diagnostic.code == "E013"
    assert diagnostic.key == :total_bad_argument
    assert rendered =~ "`@total true`"
  end

  test "an unproven @total is rejected in a type-level position too" do
    # A function that is BOTH `@total true` and used in a type is caught by the
    # type-level closure first, but the requirement set still records it.
    src = """
    mod M
      type Dec = Dcoupled | Causal
      type Sig = CSig | ESig
      type SVDesc = SVNil | SVCons(Sig, SVDesc)

      @total true
      fn andd(x: Dec, y: Dec) -> Dec = andd(x, y)

      type SF indices (as: SVDesc, bs: SVDesc, d: Dec)
        prim : SF(as, bs, Causal)
        seq : SF(as, bs, d1) -> SF(bs, cs, d2) -> SF(as, cs, andd(d1, d2))
    end
    """

    assert {:error, error} = Program.elaborate(src, file: "total_type.cure")
    # The type-level closure reports the same unproven function.
    assert {:totality_required, :"M#andd"} = Program.semantic_error(error)
  end
end
