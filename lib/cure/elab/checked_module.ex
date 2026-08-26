defmodule Cure.Elab.CheckedModule do
  @moduledoc """
  Reusable result of checking one Cure module.

  A checked module is the semantic hand-off between elaboration and its
  consumers. Code generation uses `env` and `local_defs`; incremental builds
  use `interface`; diagnostics and tooling retain the checked `ast` and source
  identity. Keeping these projections together prevents consumers from
  reparsing and re-elaborating the same source to recover information that was
  already available at the checking boundary.
  """

  alias Cure.Compiler.ModuleInterface
  alias Cure.Core.Env

  @enforce_keys [:ast, :env, :local_defs, :module, :module_name]
  defstruct [
    :ast,
    :env,
    :interface,
    :module,
    :module_name,
    :source_hash,
    :source_path,
    local_defs: []
  ]

  @type t :: %__MODULE__{
          ast: tuple() | list(),
          env: Env.t(),
          interface: ModuleInterface.t() | nil,
          module: module(),
          module_name: String.t(),
          source_hash: binary() | nil,
          source_path: Path.t() | nil,
          local_defs: [atom()]
        }
end
