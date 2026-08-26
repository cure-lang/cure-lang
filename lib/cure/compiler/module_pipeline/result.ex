defmodule Cure.Compiler.ModulePipeline.Result do
  @moduledoc false

  @enforce_keys [:request, :manifest]
  defstruct request: nil,
            manifest: nil,
            skeletons: %{},
            asts: %{},
            interfaces: %{},
            beams: %{},
            checked_envs: %{},
            body_envs: %{},
            components: [],
            semantic_graph: nil,
            # Not semantic-graph edges: the graph's vocabulary is the twelve
            # *dependency* kinds fixed by the design (§7.2), and "checking A's
            # bodies elaborated B's bodies" is not a dependency of A on B — it is
            # a record of how this run behaved. Keeping it beside the graph is
            # what lets the vocabulary stay closed and still be measurable.
            body_elaborations: [],
            diagnostics: [],
            rebuilt_modules: [],
            expansion_rounds: 1,
            alternate_paths: %{}

  @type t :: %__MODULE__{}
end
