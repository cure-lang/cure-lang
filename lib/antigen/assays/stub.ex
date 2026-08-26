defmodule Antigen.Assays.Stub do
  @moduledoc "Fake assay: {:global, :boom} is the planted infection (Phase 1 only)."
  alias Antigen.Challenge
  # `{:expected, _}`-tagged: this is a DELIBERATELY planted violation (machinery
  # test), so the Runner renders it as a calm immune response, not an alarming
  # "ANTIGEN INFECTION" — nothing is actually wrong with the system under test.
  def run(%Challenge{payload: %{term: {:global, :boom}}}), do: {:violation, {:expected, :boom}}
  def run(%Challenge{}), do: :ok
end
