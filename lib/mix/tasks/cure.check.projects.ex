defmodule Mix.Tasks.Cure.Check.Projects do
  @moduledoc """
  Runs every nested example project through its real Cure compiler and ExUnit suite.

  The projects are deliberately executed in separate VMs: several examples own
  generated modules with the same lexical names, and testing them in the root VM
  would let loaded modules leak between projects.
  """

  use Mix.Task

  @shortdoc "Compile and test every nested Cure example project"

  @projects ~w(
    cure_atelier
    cure_brainloop
    cure_colony
    cure_example
    cure_forge
    cure_moneta
    cure_motif
    cure_spline
    cure_turnstile
  )

  @impl Mix.Task
  def run([]) do
    root = project_root()

    Enum.each(@projects, fn name ->
      Mix.shell().info("\n==> examples/#{name}")

      {output, status} =
        System.cmd("mix", ["test", "--no-color", "--warnings-as-errors"],
          cd: Path.join([root, "examples", name]),
          env: [
            {"MIX_ENV", "test"},
            {"MIX_DEPS_PATH", Path.join(root, "deps")},
            {"MIX_BUILD_PATH", Path.join(root, "_build/project_examples")}
          ],
          stderr_to_stdout: true
        )

      IO.write(output)

      if status != 0 do
        Mix.raise("examples/#{name} failed with exit status #{status}")
      end
    end)

    Mix.shell().info("\n#{length(@projects)} nested example projects passed")
  end

  def run(_args), do: Mix.raise("Usage: mix cure.check.projects")

  defp project_root do
    Mix.Project.project_file()
    |> Path.dirname()
    |> Path.expand()
  end
end
