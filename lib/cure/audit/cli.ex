defmodule Cure.Audit.CLI do
  @moduledoc """
  `cure audit trust <Module>` — print the unproved assumptions reachable from a
  module. Never wired into `cure build`: a compiler that refuses to build over an
  audit trains people to hate the audit.

  `run/2` is pure: it returns the report text and whether `--strict` should fail.
  The escript clause in `Cure.CLI` is what calls `System.halt/1`.
  """

  alias Cure.Audit.{Format, Ledger, Source}

  @spec run(String.t(), keyword()) ::
          {:ok, String.t()} | {:strict_failure, String.t()} | {:error, :not_found}
  def run(module, opts) do
    with {:ok, path} <- Source.locate(module) do
      report = Ledger.audit_source(File.read!(path), module)
      text = Format.render(report, opts)

      if Keyword.get(opts, :strict, false) and report.unaudited != [] do
        {:strict_failure, text}
      else
        {:ok, text}
      end
    end
  end
end
