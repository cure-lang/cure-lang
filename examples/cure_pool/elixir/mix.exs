defmodule CurePool.MixProject do
  use Mix.Project

  def project do
    [
      app: :cure_pool,
      version: "0.1.0",
      elixir: "~> 1.18",
      lockfile: "../../../mix.lock",
      start_permanent: Mix.env() == :prod,
      deps: deps(),
      aliases: aliases()
    ]
  end

  def application do
    [
      extra_applications: [:logger],
      mod: {CurePool.Application, []}
    ]
  end

  defp deps do
    [
      # The Cure compiler itself, used by the `compile_cure` Mix task to turn
      # `cure_src/*.cure` into BEAM modules at build time.
      {:cure, path: "../../.."}
    ]
  end

  defp aliases do
    # Compile the Cure sources before Elixir, so the facade can reference the
    # generated modules by their raw BEAM atoms.
    [
      compile: ["compile_cure", "compile"],
      test: ["compile_cure", "test"]
    ]
  end
end
