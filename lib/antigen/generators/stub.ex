defmodule Antigen.Generators.Stub do
  @moduledoc "A trivial generator to exercise the harness end-to-end (Phase 1 only)."
  alias Antigen.{Gen, Challenge}

  def gen do
    Gen.frequency([
      {1, Gen.return(Challenge.new(kind: :stub, assay: "stub", label: :none, payload: %{term: {:global, :boom}}))},
      {9,
       Gen.bind(Gen.int(0, 3), fn n ->
         Gen.return(Challenge.new(kind: :stub, assay: "stub", label: :none, payload: %{term: {:var, n}}))
       end)}
    ])
  end
end
