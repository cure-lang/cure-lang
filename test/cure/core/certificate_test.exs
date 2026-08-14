defmodule Cure.Core.CertificateTest do
  use ExUnit.Case, async: false
  alias Cure.Core.{Certificate, Conv, Env, Inductive, Kernel}
  alias Cure.Elab.TotalityClosure

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

  defp and_type, do: {:pi, Cure.Core.Grade.unrestricted(), @dec, {:pi, Cure.Core.Grade.unrestricted(), @dec, @dec}}

  defp and_body do
    inner = {:case, {:var, 0}, @dec_motive, [{:Dcoupled, 0, @dcoupled}, {:Causal, 0, @causal}]}

    {:lam, Cure.Core.Grade.unrestricted(), @dec,
     {:lam, Cure.Core.Grade.unrestricted(), @dec,
      {:case, {:var, 1}, @dec_motive, [{:Dcoupled, 0, @dcoupled}, {:Causal, 0, inner}]}}}
  end

  defp and_app(a, b), do: {:app, {:app, {:global, :and}, a}, b}

  defp certify(env, name) do
    certified = TotalityClosure.certify_available(env, name)
    if Env.total?(certified, name), do: {:ok, certified}, else: {:error, :not_total}
  end

  test "a structurally-total global certifies and then delta-reduces in conversion" do
    env = Env.add_def(base(), :and, and_type(), and_body())
    assert :ok == Kernel.check_def(env, :and)
    assert {:ok, env2} = certify(env, :and)

    # Before certification: and(Causal,Causal) is stuck (no δ).
    refute Conv.conv?(and_app(@causal, @causal), @causal, [], 0, env)

    # After: δ unfolds the certified def — and(Causal,Causal) ≡ Causal.
    assert Conv.conv?(and_app(@causal, @causal), @causal, [], 0, env2)
    assert Conv.conv?(and_app(@causal, @dcoupled), @dcoupled, [], 0, env2)
    refute Conv.conv?(and_app(@causal, @dcoupled), @causal, [], 0, env2)
  end

  test "a non-terminating global is rejected and stays opaque to δ" do
    env = Env.add_def(base(), :loop, @dec, {:global, :loop})
    assert {:error, :not_total} = certify(env, :loop)
    refute Conv.conv?({:global, :loop}, @causal, [], 0, env)
  end

  test "replacing a definition invalidates its prior totality certificate" do
    env = Env.add_def(base(), :stable, @dec, @causal)
    assert {:ok, certified} = certify(env, :stable)
    assert Env.certified?(certified, :stable)
    :ok = Cure.Pipeline.Events.subscribe(:kernel, :totality_metric)

    replaced = Env.add_def(certified, :stable, @dec, {:global, :stable})

    assert_receive {Cure.Pipeline.Events, :kernel, :totality_metric,
                    %{
                      operation: :component_certificate_invalidation,
                      reason: :definition_changed,
                      definition: :stable,
                      invalidated_components: 1
                    }, _metadata}

    refute Env.certified?(replaced, :stable)
    assert {:error, :not_total} = certify(replaced, :stable)
  end

  test "a mutually-recursive cycle f→g→f is NOT certified (mutual recursion is soundly rejected)" do
    ty = {:pi, Cure.Core.Grade.unrestricted(), @dec, @dec}
    bf = {:lam, Cure.Core.Grade.unrestricted(), @dec, {:app, {:global, :g}, {:var, 0}}}
    bg = {:lam, Cure.Core.Grade.unrestricted(), @dec, {:app, {:global, :f}, {:var, 0}}}
    env = base() |> Env.add_def(:f, ty, bf) |> Env.add_def(:g, ty, bg)

    assert {:error, :not_total} = certify(env, :f)
    assert {:error, :not_total} = certify(env, :g)
    # ...and neither δ-unfolds in conversion (stays opaque).
    refute Conv.conv?({:app, {:global, :f}, @causal}, @causal, [], 0, env)
  end

  test "a def that calls an unrelated (non-cyclic) global is still certified" do
    # `use_id = λx. id x` where `id = λx. x`: id does not call back, so use_id is
    # not in a cycle and must remain certifiable (guards against over-rejection).
    ty = {:pi, Cure.Core.Grade.unrestricted(), @dec, @dec}
    id_body = {:lam, Cure.Core.Grade.unrestricted(), @dec, {:var, 0}}
    use_body = {:lam, Cure.Core.Grade.unrestricted(), @dec, {:app, {:global, :id}, {:var, 0}}}
    env = base() |> Env.add_def(:id, ty, id_body) |> Env.add_def(:use_id, ty, use_body)

    assert {:ok, _} = certify(env, :use_id)
  end

  test "certificate validation records a canonical direct-call summary keyed by the checked body" do
    ty = {:pi, Cure.Core.Grade.unrestricted(), @dec, @dec}
    id_body = {:lam, Cure.Core.Grade.unrestricted(), @dec, {:var, 0}}
    use_body = {:lam, Cure.Core.Grade.unrestricted(), @dec, {:app, {:global, :id}, {:var, 0}}}

    env =
      base()
      |> Env.with_owner("Summary")
      |> Env.add_def(:id, ty, id_body)
      |> Env.add_def(:use_id, ty, use_body)

    assert {:ok, checked} = certify(env, :use_id)

    assert %{caller: :"Summary#use_id", body_hash: body_hash, summary_hash: summary_hash, calls: [call]} =
             Env.direct_call_summary(checked, :use_id)

    assert is_binary(body_hash) and byte_size(body_hash) == 32
    assert is_binary(summary_hash) and byte_size(summary_hash) == 32
    assert call.callee == :"Summary#id"
    assert Cure.Core.SizeChange.to_dense(call.matrix) == [[:equal]]
  end

  test "duplicate semantic calls retain distinct stable Core provenance" do
    ty = {:pi, Cure.Core.Grade.unrestricted(), @dec, @dec}
    id_body = {:lam, Cure.Core.Grade.unrestricted(), @dec, {:var, 0}}

    body =
      {:lam, Cure.Core.Grade.unrestricted(), @dec,
       {:ctor, :Pair, [{:app, {:global, :id}, {:var, 0}}, {:app, {:global, :id}, {:var, 0}}]}}

    env =
      base()
      |> Env.with_owner("Summary")
      |> Env.add_def(:id, ty, id_body)
      |> Env.add_def(:twice, ty, body)

    summary = Certificate.direct_summary(:twice, body, env)
    assert [left, right] = summary.calls
    assert left.callee == right.callee
    assert left.matrix == right.matrix
    refute left.id == right.id
    refute left.provenance.core_path == right.provenance.core_path

    assert summary == Certificate.direct_summary(:twice, body, env)
  end

  test "an applied dependent case preserves the proof parameter as a branch alias" do
    chain = {:data, :Chain, [], []}

    env =
      base()
      |> Inductive.declare(Inductive.family(:Chain, [], [], 0), [
        Inductive.ctor(:Stop, [], []),
        Inductive.ctor(:Step, [prior: chain], [])
      ])

    chain_motive = {:lam, Cure.Core.Grade.unrestricted(), chain, chain}

    recurse_on_prior =
      {:case, {:var, 0}, chain_motive,
       [
         {:Stop, 0, {:ctor, :Stop, []}},
         {:Step, 1, {:app, {:global, :consume}, {:var, 0}}}
       ]}

    # Dependent elimination lowers to a case returning a function, immediately
    # applied to the transported proof. The branch lambda's binder is therefore
    # definitionally the original `proof` parameter.
    applied_dependent_case =
      {:app,
       {:case, @causal, {:lam, Cure.Core.Grade.unrestricted(), @dec, {:pi, Cure.Core.Grade.zero(), chain, chain}},
        [{:Causal, 0, {:lam, Cure.Core.Grade.zero(), chain, recurse_on_prior}}]}, {:var, 0}}

    body = {:lam, Cure.Core.Grade.zero(), chain, applied_dependent_case}
    type = {:pi, Cure.Core.Grade.zero(), chain, chain}
    env = Env.add_def(env, :consume, type, body)

    assert [%{callee: :consume, matrix: matrix}] = Certificate.direct_summary(:consume, body, env).calls
    assert Cure.Core.SizeChange.to_dense(matrix) == [[:smaller]]

    recurse_on_original =
      {:case, {:var, 0}, chain_motive,
       [
         {:Stop, 0, {:ctor, :Stop, []}},
         # prior = 0, branch alias = 1, original caller parameter = 2
         {:Step, 1, {:app, {:global, :consume_control}, {:var, 2}}}
       ]}

    control_case =
      {:app,
       {:case, @causal, {:lam, Cure.Core.Grade.unrestricted(), @dec, {:pi, Cure.Core.Grade.zero(), chain, chain}},
        [{:Causal, 0, {:lam, Cure.Core.Grade.zero(), chain, recurse_on_original}}]}, {:var, 0}}

    control_body = {:lam, Cure.Core.Grade.zero(), chain, control_case}
    env = Env.add_def(env, :consume_control, type, control_body)

    assert [%{callee: :consume_control, matrix: control_matrix}] =
             Certificate.direct_summary(:consume_control, control_body, env).calls

    assert Cure.Core.SizeChange.to_dense(control_matrix) == [[:equal]]
  end

  test "replacing a definition invalidates its cached direct-call summary" do
    env = Env.add_def(base(), :stable, @dec, @causal)
    assert {:ok, checked} = certify(env, :stable)
    assert Env.direct_call_summary(checked, :stable)

    replaced = Env.add_def(checked, :stable, @dec, {:global, :stable})
    assert is_nil(Env.direct_call_summary(replaced, :stable))
  end

  test "an unchanged checked body is summarized once across repeated preparation" do
    env = Env.add_def(base(), :stable, @dec, @causal)
    :ok = Cure.Pipeline.Events.subscribe(:kernel, :totality_metric)

    assert {:ok, prepared} = Kernel.prepare_direct_call_summaries(env, [:stable])

    assert_receive {Cure.Pipeline.Events, :kernel, :totality_metric,
                    %{operation: :direct_summary, definition: :stable, cache: :miss}, _metadata}

    assert {:ok, _again} = Kernel.prepare_direct_call_summaries(prepared, [:stable])

    assert_receive {Cure.Pipeline.Events, :kernel, :totality_metric,
                    %{operation: :direct_summary, definition: :stable, cache: :hit}, _metadata}
  end

  test "a pending forward declaration preserves a sealed definition certificate" do
    env = Env.add_def(base(), :stable, @dec, @causal)
    assert {:ok, checked} = certify(env, :stable)
    summary = Env.direct_call_summary(checked, :stable)

    skeleton = Env.add_def(checked, :stable, @dec, {:hole, "__pending__"})

    assert Env.total?(skeleton, :stable)
    assert Env.direct_call_summary(skeleton, :stable) == summary
  end
end
