defmodule Cure.Core.ValidatorUnknownNodeTest do
  @moduledoc """
  `Validator.children/1` must not treat an UNRECOGNIZED tuple node as a childless
  leaf: doing so blinds the pre-order walker to any forbidden node nested inside
  it. The `children/1` comment claims the walker "survives the later grade
  reshape", but only the graded λ/Π 4-tuples were covered — a graded `:app`
  4-tuple hid its subterms, so a `{:hole, …}` buried in one escaped the
  release-config `no_hole: :reject` gate entirely (a fail-open).
  """
  use ExUnit.Case, async: true
  alias Cure.Core.Validator

  test "a hole hidden inside an unrecognized (graded-app) node is still rejected" do
    # A hypothetical graded application 4-tuple — NOT in children/1's explicit
    # list — carrying a hole in argument position.
    node = {:app, :one, {:global, :f}, {:hole, :arg}}

    assert {:error, diags} = Validator.validate(node, Validator.release_config())

    assert Enum.any?(diags, &(&1.clause == :no_hole)),
           "the nested hole must be discovered and rejected; got #{inspect(diags)}"
  end

  test "the walker still descends known nodes (no false negatives on plain terms)" do
    node = {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:app, {:var, 0}, {:hole, :b}}}
    assert {:error, diags} = Validator.validate(node, Validator.release_config())
    assert Enum.any?(diags, &(&1.clause == :no_hole))
  end
end
