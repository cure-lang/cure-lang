defmodule CureSpline.MixProject do
  use Mix.Project

  def project do
    [
      app: :cure_spline,
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
      mod: {CureSpline.Application, []}
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
