defmodule Cure.Stdlib.PreludeImportNonleakTest do
  use ExUnit.Case, async: false

  alias Cure.Elab.Program

  @moduledoc """
  Imports used to implement an item-granular prelude provider must not be
  re-exported through that provider's ambient slice.

  `Std.String` uses `Std.Option` internally for `first/1` and `last/1`. That
  implementation detail must not compete with a consumer's explicit
  `use Std.Option`, especially during derived `Equatable(Option(Int))`
  resolution.
  """

  test "Std.String's internal Std.Option import does not break Some equality" do
    source = """
    mod PreludeImportNonleak
      use Std.Option

      fn same_some() -> Bool = Some(1) == Some(1)
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end
end
