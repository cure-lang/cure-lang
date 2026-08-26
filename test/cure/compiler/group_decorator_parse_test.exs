defmodule Cure.Compiler.GroupDecoratorParseTest do
  @moduledoc """
  `@group` inside the mod body is the DEPRECATED placement (spec
  2026-07-10-group-decorator-placement). It is tolerated at parse time — a hard
  error would make an old-form file unparseable and therefore un-migratable — and
  emits an `E-GROUP-PLACEMENT` deprecation instead, so `cure migrate`'s @group-hoist
  rule can relocate it. The canonical placement — above `mod`, attached to the
  module container — is covered by `Cure.Compiler.GroupDecoratorTest`.
  """
  use ExUnit.Case, async: true

  test "@group in the mod body parses (deprecated, not a hard error)" do
    src = "mod X\n  @group(:core)\n  fn f() -> Int = 1\n"

    assert {:ok, _ast} = Cure.Compiler.parse_source(src),
           "in-body @group must be tolerated so the @group-hoist migration can relocate it"
  end
end
