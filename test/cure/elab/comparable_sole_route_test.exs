defmodule Cure.Elab.ComparableSoleRouteTest do
  @moduledoc """
  `<` (and its siblings `<=`/`>`/`>=`) desugar solely to the `Comparable`
  interface method — `build_binop` no longer carries an ordering fast path for
  abstract or ADT operands. An ordering comparison at a type with no `Comparable`
  instance is therefore an elaboration error, not a silent lowering.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "`<` on an ADT with no Comparable instance is rejected" do
    src = """
    mod NC
      type Color = Red | Blue
      fn lt(a: Color, b: Color) -> Bool = a < b
    end
    """

    assert {:error, {:source_context, {:no_instance, :Comparable, :"NC#Color"}, _}} = Program.elaborate(src)
  end

  test "`<` on an unconstrained abstract type variable is rejected" do
    src = """
    mod NC2
      fn lt(a: t, b: t) -> Bool = a < b
    end
    """

    assert {:error, {:source_context, {:no_instance, :Comparable, {:rigid, 0}}, _}} = Program.elaborate(src)
  end

  test "`<` on a `where Comparable(t)`-constrained variable elaborates" do
    src = """
    mod OK
      fn lt(a: t, b: t) -> Bool where Comparable(t) = a < b
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end
