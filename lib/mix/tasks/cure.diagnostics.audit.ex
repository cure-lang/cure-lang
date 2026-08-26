defmodule Mix.Tasks.Cure.Diagnostics.Audit do
  use Mix.Task

  @shortdoc "Print every registered diagnostic fixture with source context"

  @moduledoc """
  Runs the complete diagnostic exerciser in audit mode:

      mix cure.diagnostics.audit --color=never --width=100

  The output is a deterministic numbered list. Each entry identifies the
  registry code, stable key, producer fixture, and rendered terminal/plain
  diagnostic so diagnostic wording and source labels can be reviewed in one
  pass.
  """

  @impl true
  def run(args) do
    Mix.Tasks.Cure.Diagnostics.run(["--audit" | args])
  end
end
