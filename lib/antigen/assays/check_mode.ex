defmodule Antigen.Assays.CheckMode do
  @moduledoc """
  `check/verdict` — the known-label oracle for `Cure.Core.Kernel.check/3`. Builds
  a v1-menu context, evaluates the expected type to a value, and asks the kernel
  to CHECK the term against it; the outcome category (`:accept` for `:ok`,
  `:reject` for `{:error, _}`) must match the correct-by-construction label. A
  disagreement is a checking-mode soundness/completeness infection.

  Generality: covers the checking-mode-only introduction forms (parameter-bearing
  constructors, holes, Σ-introduction) and their rejection paths (a Σ second
  component that mismatches, a constructor index/param clash). It does NOT re-test
  inference (the `term/*` verticals) — only the `check`-direction decisions.
  """
  alias Antigen.{Challenge, Generators}
  alias Cure.Core.{Context, Eval, Kernel}

  @nat_type {:vdata, :Nat, []}

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :check_mode, label: expected, payload: p}) do
    ctx =
      Enum.reduce(1..p.ctx_vars//1, Context.empty(Generators.SigMenu.env_of(:v1)), fn _, c ->
        Context.extend(c, @nat_type)
      end)

    type_value = Eval.eval(p.type, Context.env(ctx))

    got =
      case Kernel.check(ctx, p.term, type_value) do
        :ok -> :accept
        {:error, _} -> :reject
      end

    if got == expected do
      :ok
    else
      {:violation, {:check_mode_disagreement, %{payload: p, expected: expected, got: got}}}
    end
  end
end
