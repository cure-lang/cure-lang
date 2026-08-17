defmodule Cure.Elab.PreparedDeclarations do
  @moduledoc false

  @enforce_keys [:owner, :items]
  defstruct [:owner, :items, :declaration_count]

  @type t :: %__MODULE__{
          owner: String.t(),
          items: [tuple()],
          declaration_count: non_neg_integer()
        }
end
