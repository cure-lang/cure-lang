defmodule Mix.Tasks.Cure.Check.Projects do
  @moduledoc """
  Runs every nested example project through its real Cure compiler and ExUnit suite.

  The projects are deliberately executed in separate VMs: several examples own
  generated modules with the same lexical names, and testing them in the root VM
  would let loaded modules leak between projects.

  Two kinds of nested project are covered:

  - **Mix projects** (`@mix_projects`) -- have their own `mix.exs`; checked
    with `mix test` in a subprocess whose `MIX_DEPS_PATH`/`MIX_BUILD_PATH`
    point back at this project's own `deps`/`_build`, so the shared `:cure`
    path dependency is compiled once and reused across every one of them.
  - **Pure Cure projects** (`@pure_projects`) -- have a `Cure.toml` and no
    `mix.exs`; checked with `cure test` via the escript this task builds
    itself first (`mix cure.escript`), the same binary a real user would run.
  """

  use Mix.Task

  @shortdoc "Compile and test every nested Cure example project"

  @mix_projects ~w(
    cure_atelier
    cure_brainloop
    cure_colony
    cure_example
    cure_exchange/elixir
    cure_forge
    cure_moneta
    cure_motif
    cure_spline
    cure_turnstile
  )

  @pure_projects ~w(
    cure_calc
    cure_exchange/cure
  )

  @impl Mix.Task
  def run([]) do
    root = project_root()

    Enum.each(@mix_projects, &run_mix_project(&1, root))

    escript_path = build_escript(root)
    Enum.each(@pure_projects, &run_pure_project(&1, root, escript_path))

    total = length(@mix_projects) + length(@pure_projects)
    Mix.shell().info("\n#{total} nested example projects passed")
  end

  def run(_args), do: Mix.raise("Usage: mix cure.check.projects")

  defp run_mix_project(name, root) do
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
  end

  # Built once, up front, and reused for every pure-Cure project below --
  # mirrors how the mix projects above share one compiled `:cure` dependency
  # rather than each project rebuilding it.
  defp build_escript(root) do
    Mix.shell().info("\n==> building the cure escript for pure-Cure project checks")
    Mix.Task.run("cure.escript")
    Path.join(root, Atom.to_string(Mix.Project.config()[:app]))
  end

  defp run_pure_project(name, root, escript_path) do
    Mix.shell().info("\n==> examples/#{name} (pure Cure)")

    {output, status} =
      System.cmd(escript_path, ["test"],
        cd: Path.join([root, "examples", name]),
        stderr_to_stdout: true
      )

    IO.write(output)

    if status != 0 do
      Mix.raise("examples/#{name} failed with exit status #{status}")
    end
  end

  defp project_root do
    Mix.Project.project_file()
    |> Path.dirname()
    |> Path.expand()
  end
end
