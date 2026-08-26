defmodule Cure.Core.DefTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Inductive, Env, Kernel, Context}

  @dec {:data, :Dec, [], []}
  @dcoupled {:ctor, :Dcoupled, []}
  @causal {:ctor, :Causal, []}
  @dec_motive {:lam, Cure.Core.Grade.unrestricted(), @dec, @dec}

  defp base do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Dec, [], [], 0), [
      Inductive.ctor(:Dcoupled, [], []),
      Inductive.ctor(:Causal, [], [])
    ])
  end

  # and : Dec -> Dec -> Dec ; and(Causal, Causal) = Causal, else Dcoupled.
  defp and_type, do: {:pi, Cure.Core.Grade.unrestricted(), @dec, {:pi, Cure.Core.Grade.unrestricted(), @dec, @dec}}

  defp and_body do
    inner =
      {:case, {:var, 0}, @dec_motive, [{:Dcoupled, 0, @dcoupled}, {:Causal, 0, @causal}]}

    {:lam, Cure.Core.Grade.unrestricted(), @dec,
     {:lam, Cure.Core.Grade.unrestricted(), @dec,
      {:case, {:var, 1}, @dec_motive, [{:Dcoupled, 0, @dcoupled}, {:Causal, 0, inner}]}}}
  end

  test "checks and registers a well-typed global definition" do
    env = Env.add_def(base(), :and, and_type(), and_body())
    assert :ok == Kernel.check_def(env, :and)
    assert {:ok, {:vpi, _g, {:vdata, :Dec, []}, _cod}} = Kernel.infer(Context.empty(env), {:global, :and})
  end

  test "negative: a body whose type differs from the declared type" do
    # body : Dec -> Type1, but declared Dec -> Dec
    env =
      Env.add_def(
        base(),
        :bad,
        {:pi, Cure.Core.Grade.unrestricted(), @dec, @dec},
        {:lam, Cure.Core.Grade.unrestricted(), @dec, {:type, 0}}
      )

    assert {:error, {:conversion_failure, _, _}} = Kernel.check_def(env, :bad)
  end

  test "negative: a reference to an unregistered global" do
    assert {:error, {:unknown_global, :missing, details}} =
             Kernel.infer(Context.empty(base()), {:global, :missing})

    assert details.core_term == {:global, :missing}
    assert details.context_size == 0
  end

  test "check_def retains Core context for an unknown definition" do
    assert {:error, {:unknown_global, :missing, details}} = Kernel.check_def(base(), :missing)
    assert details.core_term == {:global, :missing}
    assert is_nil(details.context_size)
  end
end
