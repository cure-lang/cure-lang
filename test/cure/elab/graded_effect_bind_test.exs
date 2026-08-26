defmodule Cure.Elab.GradedEffectBindTest do
  @moduledoc """
  Graded effect binders — the linear-channel enabler. `let @linear r = eff()`
  binds the effect's RESULT `r` at a grade via the `effect_bind` continuation lam
  (`{:effect_bind, e, {:lam, :linear, T, body}}`). The kernel's `bind` rule accepts
  the continuation's own grade (no longer hardcodes ω), and `Relevance` walks
  `effect_bind` as a one-shot graded `let` — the continuation runs exactly once, so
  its captures are counted once and the binder's grade obligation is enforced:
  `linear` exactly-once, `affine` at-most-once.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @prelude "  @extern(:erlang, :make_ref, 0)\n  fn open_res() -> Effect(Int)\n"

  defp elab(body), do: Program.elaborate("mod GEB\n#{@prelude}#{body}end\n")

  test "linear effect result used exactly once — accept" do
    assert {:ok, _} =
             elab("""
               fn ok() -> Effect(Int) =
                 let @linear r = open_res()
                 r
             """)
  end

  test "linear effect result dropped (unused) — reject (must be used exactly once)" do
    assert {:error, _} =
             elab("""
               fn bad() -> Effect(Int) =
                 let @linear r = open_res()
                 open_res()
             """)
  end

  test "affine effect result dropped (unused) — accept (may be dropped)" do
    assert {:ok, _} =
             elab("""
               fn ok_aff() -> Effect(Int) =
                 let @affine r = open_res()
                 open_res()
             """)
  end

  test "affine effect result used once — accept" do
    assert {:ok, _} =
             elab("""
               fn ok_aff1() -> Effect(Int) =
                 let @affine r = open_res()
                 r
             """)
  end

  test "an unrestricted (ungraded) effect binder is unaffected" do
    assert {:ok, _} =
             elab("""
               fn plain() -> Effect(Int) =
                 let r = open_res()
                 r
             """)
  end
end
