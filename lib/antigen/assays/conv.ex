defmodule Antigen.Assays.Conv do
  @moduledoc """
  `conv/decision` — the known-label oracle for definitional equality. Builds a
  context of `ctx` fresh neutral variables and asks `Cure.Core.Conv.conv?/5`
  (sig = nil: no δ, opaque globals) to decide the pair; the verdict must match the
  correct-by-construction `expect`. A disagreement is a conversion-soundness
  infection (two definitionally-distinct terms judged equal, or vice versa).
  """
  alias Antigen.Challenge
  alias Cure.Core.Conv

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :conv_pair, payload: %{t1: t1, t2: t2, ctx: n, expect: expect}}) do
    env = for i <- 0..(n - 1)//1, do: {:vneutral, {:nvar, i}}

    # 4-arg form (sig defaults to nil): no δ, opaque globals — the same decision,
    # and it exercises conv?/4's default-injecting head.
    if Conv.conv?(t1, t2, env, n) == expect do
      :ok
    else
      {:violation, {:conv_disagreement, %{t1: t1, t2: t2, expected: expect}}}
    end
  end
end
