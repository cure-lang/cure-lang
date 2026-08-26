defmodule Cure.Elab.TypeConv do
  @moduledoc """
  Definitional convertibility of two Core type terms, phrased for the
  elaborator's overload machinery.

  This is a thin wrapper over `Cure.Core.Conv.conv?/5`: it evaluates both terms
  in a neutral value environment at binder depth 0 and asks the kernel whether
  they are definitionally equal, unfolding certified globals through the
  supplied elaborator `%Cure.Core.Env{}` (passed as the kernel `sig`).

  Depth 0 is adequate for the overload use sites, which compare first-order,
  closed parameter types (data types, `Int`, …). It never rewrites Core terms
  or invents identity; it only asks the trusted conversion checker a question.
  """

  alias Cure.Core.{Conv, Context, Env}

  @doc """
  Are `t1` and `t2` definitionally equal as Core type terms under `env`?

  `env` is the elaborator environment; its certified definitions are used for
  delta-unfolding during conversion.
  """
  @spec convertible?(Env.t(), term(), term()) :: boolean()
  def convertible?(%Env{} = env, t1, t2) do
    Conv.conv?(t1, t2, Context.neutral_env(0), 0, env)
  end
end
