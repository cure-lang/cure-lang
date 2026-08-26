defmodule Antigen.Assays.RewriteTest do
  use ExUnit.Case, async: true
  alias Antigen.{Assays, Generators}

  test "run/1: :ok on correctly-labelled, {:violation,_} on mislabelled" do
    wt = Generators.Rewrite.eq_formation(:well_typed)
    it = Generators.Rewrite.eq_formation(:ill_typed)
    assert :ok == Assays.Rewrite.run(wt)
    assert :ok == Assays.Rewrite.run(it)
    # deliberately mislabel: an ill-typed def wearing a :well_typed label must infect
    mislabelled = %{it | label: :well_typed}
    assert {:violation, {:wrongly_rejected, _}} = Assays.Rewrite.run(mislabelled)
  end

  test "rewrite_eq round-trips through Challenge encode/decode and Coverage" do
    c = Generators.Rewrite.eq_formation(:well_typed)
    {scaffold, pieces} = Antigen.Challenge.to_pieces(c)
    rebuilt = Antigen.Challenge.from_pieces(:rewrite_eq, c.assay, c.label, nil, c.note, scaffold, pieces)
    assert rebuilt.kind == :rewrite_eq
    assert :ok == Assays.Rewrite.run(rebuilt)
    assert is_list(Antigen.Coverage.terms_of(c)) and Antigen.Coverage.terms_of(c) != []
  end
end
