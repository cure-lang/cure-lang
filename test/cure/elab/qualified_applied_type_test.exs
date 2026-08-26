defmodule Cure.Elab.QualifiedAppliedTypeTest do
  @moduledoc """
  A qualified applied type constructor (`Std.Map(k, v)`, from the `Mod.Name(args)`
  grammar production) must lower to the SAME core term as its unqualified spelling.

  The parser now produces `{:function_call, name: "Std.Map", …}` for the qualified
  form. `idx_to_core` first offers that dotted head to the module-aware type
  resolver; when the resolver can't place it as a registered `:type`, the name must
  DEGRADE to its bare tail (`Std.Map` → `Map`) so every downstream check — family,
  ctor, global — resolves it exactly as the unqualified spelling would.

  Without the degrade the qualified form lowered to an opaque `{:global, :"Std.Map"}`
  carrying the whole dotted string, which never converts against the unqualified
  `{:global, :Map}` — a silent qualified-vs-unqualified type split. These tests pin
  the convergence at the lowering layer, where it is exact.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Declarations

  # Lower the RHS of `typealias Q = <name>` in an empty core env, so any head the
  # env doesn't register falls to the neutral `{:global, …}` / `{:app, …}` form —
  # precisely the path the degrade must normalize.
  defp lower(name) do
    src = "typealias Q = #{name}\n"
    {:ok, toks} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
    {:ok, {:type_annotation, _, [rhs]}} = Cure.Compiler.Parser.parse(toks, emit_events: false)
    Declarations.lower_type(rhs, [], %Cure.Core.Env{})
  end

  test "a qualified applied type lowers identically to its unqualified spelling" do
    assert lower("Std.Option(Int)") == lower("Option(Int)")
    assert lower("Std.Map(k, v)") == lower("Map(k, v)")
  end

  test "the qualified head degrades to its bare tail, not the dotted atom" do
    # The neutral global carries `:Option`, never `:\"Std.Option\"`.
    assert {:ok, {:app, {:global, :Option}, {:global, :Int}}} = lower("Std.Option(Int)")
  end

  test "a deeper qualification (A.B.C(x)) degrades to the final segment" do
    assert {:ok, {:app, {:global, :C}, {:global, :x}}} = lower("A.B.C(x)")
  end

  test "an unqualified applied type is unaffected (String.split no-op on a bare name)" do
    assert {:ok, {:app, {:global, :Option}, {:global, :Int}}} = lower("Option(Int)")
  end
end
