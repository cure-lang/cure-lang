defmodule Cure.Elab.InlineMatchTest do
  @moduledoc """
  Nested `match` in expression position, checking mode (task: inline-match P0).

  A `match` whose arm body is itself a `match` must elaborate: the inner match
  is a nested expression in *checking* mode (the outer arm supplies its expected
  type). Programs go through the real pipeline via `Cure.Elab.Program.elaborate/1`.

  Scope: nested-expression (arm-body / rewrite-body) matches only. Let-blocks and
  inference-position inline match remain unimplemented (documented reach).
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  @nat "type Nat = Z | S(Nat)\n"

  # RED (pre-impl): {:error, {:unsupported_expression, {:pattern_match, ...}}} —
  # the inner match falls through to inference and is unsupported.
  # GREEN (post-impl): {:ok, _} — the nested match elaborates in checking mode.
  test "a nested-arm match (arm body is itself a match) elaborates in checking mode" do
    src =
      @nat <>
        """
        fn combine(n: Nat, m: Nat) -> Nat = match n
          Z() -> m
          S(k) -> match m
            Z() -> k
            S(j) -> S(j)
        """

    assert {:ok, _env} = Program.elaborate(src)
  end
end
