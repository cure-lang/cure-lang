defmodule CureForge.MixProject do
  use Mix.Project

  def project do
    [
      app: :cure_forge,
      version: "0.1.0",
      elixir: "~> 1.18",
      lockfile: "../../mix.lock",
      start_permanent: Mix.env() == :prod,
      deps: deps(),
      aliases: aliases()
    ]
  end

  def application do
    [
      extra_applications: [:logger],
      mod: {CureForge.Application, []},
      env: [
        greeting: "forge ready",
        idle_timeout_ms: 5000,
        max_log_lines: 16
      ],
      start_phases: [warm_cache: []]
    ]
  end

  defp deps do
    [
      {:cure, path: "../.."}
    ]
  end

  defp aliases do
    [
      compile: ["compile_cure", "compile"],
      test: ["compile_cure", "test"]
    ]
  end
end
