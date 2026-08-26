defmodule Cure.Elab.GadtDuplicateConstructorRedTest do
  @moduledoc """
  RED — `constructor_bindings/1` (`lib/cure/elab/program.ex:587`), which feeds
  the per-module `:duplicate_constructor` check, has clauses for `:container`
  and `:type_annotation` but falls to `constructor_bindings(_decl) -> []` for
  `:indexed_type` (GADT) declarations. Its sibling `ctor_names/1`
  (`lib/cure/elab/program.ex:952`) DOES have an `:indexed_type` clause
  (`gadt_ctor_names/1`), so the two functions disagree.

  Consequence: two indexed-type (GADT) declarations that share a constructor
  name elaborate with NO `:duplicate_constructor` error at all, and
  `env.ctor_to_family` silently binds the shared name to whichever family is
  processed last — the earlier family's constructor becomes unreachable by
  that name with no diagnostic.

  This test declares two `indices` families both with a `leaf` constructor
  and asserts the module is rejected with `{:duplicate_constructor, %{name:
  :leaf, ...}}`, mirroring the shape already used for the enum/struct case in
  `test/cure/elab/type_declaration_test.exs` and
  `test/cure/elab/decl_hygiene_test.exs`. It currently elaborates `{:ok, _}`
  (bug); it will fail here until `constructor_bindings/1` grows an
  `:indexed_type` clause paralleling `ctor_names/1`.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "two GADT families sharing a constructor name are rejected as a duplicate constructor" do
    src = """
    mod M
      type Nat = Z | S(Nat)
      type F indices (xs: Nat)
        leaf : F(Z())
        mk : F(n) -> F(S(n))
      type G indices (xs: Nat)
        leaf : G(Z())
    end
    """

    assert {:error, {:duplicate_constructor, %{name: :leaf, spans: [_first, _second]}}} =
             Program.elaborate(src)
  end
end
