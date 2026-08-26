defmodule Antigen.Backend do
  @moduledoc "Behaviour: interpret a Gen program in a concrete PBT backend (umbrella §4.1)."
  alias Antigen.Gen
  @callback interp(Gen.t()) :: term()
  @callback sample(native :: term(), count :: non_neg_integer()) :: [term()]
end
