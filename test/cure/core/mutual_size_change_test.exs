defmodule Cure.Core.MutualSizeChangeTest do
  @moduledoc """
  Cross-function / mutual size-change termination (#13) in the TCB certificate
  (trusted direct-call summaries plus externally proposed closure evidence).

  Generalises the #14 single-function size-change from self-calls to calls to any
  global in the mutual group (the SCC of globals mutually reachable with `name`).
  A well-founded mutual pair whose shared argument decreases through the cycle now
  certifies total (the composed `f→…→f` change matrix has a `:smaller` diagonal);
  a divergent cycle with no descent is rejected by the size-change criterion
  itself (its idempotent `f→f` endo-edge has no `:smaller` diagonal), NOT by a
  blanket short-circuit.

  Nat = Z | S(Nat). After one leading lambda, param 0 is de Bruijn `var 0`; a
  `{:case, scrut, motive, branches}` S-branch binds the predecessor at index 0.
  Shapes mirror the banked Antigen totality generators (even/odd, permuted pair,
  one-leg, three-cycle) and the #14 Ackermann body.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive, Kernel}
  alias Cure.Elab.TotalityGraph
  alias Cure.Elab.TotalityClosure

  @nat {:data, :Nat, [], []}
  @nat_motive {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}

  defp z, do: {:ctor, :Z, []}
  defp s(t), do: {:ctor, :S, [t]}
  defp v(i), do: {:var, i}
  defp call1(name, a), do: {:app, {:global, name}, a}
  defp call2(name, a, b), do: {:app, {:app, {:global, name}, a}, b}

  # {:case scrut motive [{:S,1,s_body},{:Z,0,z_body}]}
  defp ncase(scrut, s_body, z_body),
    do: {:case, scrut, @nat_motive, [{:S, 1, s_body}, {:Z, 0, z_body}]}

  defp base_env do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Nat, [], [], 0), [
      Inductive.ctor(:Z, [], []),
      Inductive.ctor(:S, [{:n, @nat}], [])
    ])
  end

  defp with_defs(defs) do
    Enum.reduce(defs, base_env(), fn {name, body}, env ->
      Env.add_def(env, name, nat_arrow(body), body)
    end)
  end

  # A permissive type (unused by the structural certifier, which reads only bodies
  # + the call graph); arity is read from leading lambdas.
  defp nat_arrow(_body), do: {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}

  defp terminating?(env, name), do: Cure.Test.TotalityCertificateHelper.provably_total?(env, name)

  # -- Bodies -----------------------------------------------------------------

  # even n = case n {Z -> Z; S y -> odd y};  odd n = case n {Z -> S Z; S y -> even y}
  defp even_body, do: {:lam, Cure.Core.Grade.unrestricted(), @nat, ncase(v(0), call1(:odd, v(0)), z())}
  defp odd_body, do: {:lam, Cure.Core.Grade.unrestricted(), @nat, ncase(v(0), call1(:even, v(0)), s(z()))}

  # ping/pong: structurally-descending mutual pair (Z -> Z on both legs).
  defp ping_body, do: {:lam, Cure.Core.Grade.unrestricted(), @nat, ncase(v(0), call1(:pong, v(0)), z())}
  defp pong_body, do: {:lam, Cure.Core.Grade.unrestricted(), @nat, ncase(v(0), call1(:ping, v(0)), z())}

  # diverging f→g→f with no descent: f n = g n; g n = f n.
  defp dv_f_body, do: {:lam, Cure.Core.Grade.unrestricted(), @nat, call1(:g, v(0))}
  defp dv_g_body, do: {:lam, Cure.Core.Grade.unrestricted(), @nat, call1(:f, v(0))}

  # one-leg: f n = case n {Z -> Z; S y -> g y};  g n = f (S n).  Composed cycle
  # f (S m) → g m → f (S m) is non-decreasing → must be rejected.
  defp ol_f_body, do: {:lam, Cure.Core.Grade.unrestricted(), @nat, ncase(v(0), call1(:g, v(0)), z())}
  defp ol_g_body, do: {:lam, Cure.Core.Grade.unrestricted(), @nat, call1(:f, s(v(0)))}

  # three-cycle f→g→h→f, each passes its arg unchanged (:equal) → rejected.
  defp tc_f_body, do: {:lam, Cure.Core.Grade.unrestricted(), @nat, call1(:g, v(0))}
  defp tc_g_body, do: {:lam, Cure.Core.Grade.unrestricted(), @nat, call1(:h, v(0))}
  defp tc_h_body, do: {:lam, Cure.Core.Grade.unrestricted(), @nat, call1(:f, v(0))}

  # Permuted pair (descent visible only across the argument swap), 2-arg:
  #   f n m = case n {Z -> m; S y -> g n m};  g a b = f b a
  # (matches Antigen.Generators.Totality.wellfounded_permuted_pair/0).
  defp perm_f_body do
    {:lam, Cure.Core.Grade.unrestricted(), @nat,
     {:lam, Cure.Core.Grade.unrestricted(), @nat,
      {:case, v(1), @nat_motive, [{:Z, 0, v(0)}, {:S, 1, call2(:g, v(1), v(0))}]}}}
  end

  defp perm_g_body,
    do:
      {:lam, Cure.Core.Grade.unrestricted(), @nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, call2(:f, v(0), v(1))}}

  # Ackermann (single-function, lexicographic) — #14 no-regression control.
  defp ack_body do
    inner =
      ncase(
        v(1),
        call2(:ack, v(1), call2(:ack, s(v(1)), v(0))),
        call2(:ack, v(0), s(z()))
      )

    {:lam, Cure.Core.Grade.unrestricted(), @nat,
     {:lam, Cure.Core.Grade.unrestricted(), @nat, ncase(v(1), inner, s(v(0)))}}
  end

  # -- Positive: well-founded mutual groups must certify total ----------------

  test "even/odd mutual pair certifies total (shared arg decreases through the cycle)" do
    env = with_defs(even: even_body(), odd: odd_body())
    assert terminating?(env, :even)
    assert terminating?(env, :odd)
  end

  test "verified SCC validation certifies a mutual group once and invalidates it atomically" do
    env = with_defs(even: even_body(), odd: odd_body())
    assert {:ok, prepared} = Kernel.prepare_direct_call_summaries(env, [:even, :odd])
    partition = TotalityGraph.propose_partition(prepared, [:odd, :even])
    certificates = Cure.Elab.TotalityCertificate.propose_all(prepared, partition)

    assert {:ok, certified} =
             Kernel.validate_scc_certificates(
               prepared,
               partition,
               certificates,
               [:even, :odd]
             )

    assert Env.total?(certified, :even)
    assert Env.total?(certified, :odd)
    assert map_size(certified.totality_components) == 1
    assert certified.totality_component_of.even == certified.totality_component_of.odd

    replaced = Env.add_def(certified, :even, nat_arrow(even_body()), even_body())
    refute Env.total?(replaced, :even)
    refute Env.total?(replaced, :odd)
    assert replaced.totality_components == %{}
    assert replaced.totality_component_of == %{}
  end

  test "revalidating an unchanged SCC certificate performs no closure verification" do
    env = with_defs(even: even_body(), odd: odd_body())
    assert {:ok, prepared} = Kernel.prepare_direct_call_summaries(env, [:even, :odd])
    partition = TotalityGraph.propose_partition(prepared, [:even, :odd])
    certificates = Cure.Elab.TotalityCertificate.propose_all(prepared, partition)

    :ok = Cure.Pipeline.Events.subscribe(:kernel, :totality_metric)

    assert {:ok, certified} =
             Kernel.validate_scc_certificates(prepared, partition, certificates, [:even, :odd])

    assert_receive {Cure.Pipeline.Events, :kernel, :totality_metric,
                    %{operation: :closure_verification, result: :total}, _metadata}

    drain_totality_metrics()

    assert {:ok, unchanged} =
             Kernel.validate_scc_certificates(certified, partition, certificates, [:odd, :even])

    assert unchanged == certified

    assert_receive {Cure.Pipeline.Events, :kernel, :totality_metric, %{operation: :partition_verification, result: :ok},
                    _metadata}

    refute_receive {Cure.Pipeline.Events, :kernel, :totality_metric, %{operation: :closure_verification}, _metadata},
                   20
  end

  test "declaration fast path decides a complete dependency SCC once" do
    env = with_defs(even: even_body(), odd: odd_body())
    eager = TotalityClosure.certify_available(env, :even)
    assert Env.total?(eager, :even)
    assert Env.total?(eager, :odd)
    assert map_size(eager.totality_components) == 1
  end

  test "caller components depend on certified callees and invalidate through the reverse cone" do
    total_env =
      Env.empty()
      |> Env.add_def(:callee, @nat, z())
      |> Env.add_def(:caller, @nat, {:global, :callee})

    certified = TotalityClosure.certify_available(total_env, :caller)
    assert Env.total?(certified, :callee)
    assert Env.total?(certified, :caller)

    callee_digest = certified.totality_component_of.callee
    caller_digest = certified.totality_component_of.caller
    assert certified.totality_components[caller_digest].dependency_digests == [callee_digest]
    assert is_binary(certified.totality_components[caller_digest].certificate_digest)

    invalidated = Env.add_def(certified, :callee, @nat, z())
    refute Env.total?(invalidated, :callee)
    refute Env.total?(invalidated, :caller)
    assert invalidated.totality_components == %{}
    assert invalidated.totality_component_of == %{}
  end

  test "a caller is not certified when an ordinary callee component is partial" do
    env =
      Env.empty()
      |> Env.add_def(:callee, @nat, {:global, :callee})
      |> Env.add_def(:caller, @nat, {:global, :callee})
      |> TotalityClosure.certify_available(:caller)

    refute Env.total?(env, :callee)
    refute Env.total?(env, :caller)
  end

  test "ping/pong structural mutual pair certifies total" do
    env = with_defs(ping: ping_body(), pong: pong_body())
    assert terminating?(env, :ping)
    assert terminating?(env, :pong)
  end

  test "permuted pair (descent only across the swap) certifies total" do
    env = with_defs(f: perm_f_body(), g: perm_g_body())
    assert terminating?(env, :f)
    assert terminating?(env, :g)
  end

  # -- Negative: divergent cycles must be rejected by the criterion itself ------

  test "diverging f→g→f with no descent is rejected (idempotent endo, no :smaller diagonal)" do
    env = with_defs(f: dv_f_body(), g: dv_g_body())
    refute terminating?(env, :f)
    refute terminating?(env, :g)
  end

  test "one-leg pair (composed cycle non-decreasing) is rejected" do
    env = with_defs(f: ol_f_body(), g: ol_g_body())
    refute terminating?(env, :f)
    refute terminating?(env, :g)
  end

  test "three-cycle f→g→h→f with no descent is rejected" do
    env = with_defs(f: tc_f_body(), g: tc_g_body(), h: tc_h_body())
    refute terminating?(env, :f)
    refute terminating?(env, :g)
    refute terminating?(env, :h)
  end

  defp drain_totality_metrics do
    receive do
      {Cure.Pipeline.Events, :kernel, :totality_metric, _payload, _metadata} -> drain_totality_metrics()
    after
      0 -> :ok
    end
  end

  test "arity-0 CAF cycle f = g; g = f is rejected (empty endo-edge, no descent)" do
    # No parameters ⇒ 0×0 endo-edges. These are idempotent with no :smaller
    # diagonal, so the group must be rejected (the loop genuinely diverges). The
    # criterion must NOT treat an empty endo-edge as a benign non-loop.
    env =
      base_env()
      |> Env.add_def(:cf, @nat, {:global, :cg})
      |> Env.add_def(:cg, @nat, {:global, :cf})

    refute terminating?(env, :cf)
    refute terminating?(env, :cg)
  end

  # -- #14 no-regression: single-function group delegates unchanged -----------

  test "Ackermann (single-function lexicographic) still certifies total (no #14 regression)" do
    env =
      Env.add_def(
        base_env(),
        :ack,
        {:pi, Cure.Core.Grade.unrestricted(), @nat, {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}},
        ack_body()
      )

    assert terminating?(env, :ack)
  end

  test "a non-cyclic helper call does not pull the helper into the group" do
    # h calls plus (a plain subroutine that does NOT call back); h's own recursion
    # is structural. Group of h is {h} alone → #14 delegate certifies.
    plus =
      {:lam, Cure.Core.Grade.unrestricted(), @nat,
       {:lam, Cure.Core.Grade.unrestricted(), @nat, ncase(v(1), s(call2(:plus, v(0), v(1))), v(0))}}

    h =
      {:lam, Cure.Core.Grade.unrestricted(), @nat, ncase(v(0), call1(:h, v(0)), call2(:plus, z(), z()))}

    env =
      base_env()
      |> Env.add_def(
        :plus,
        {:pi, Cure.Core.Grade.unrestricted(), @nat, {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}},
        plus
      )
      |> Env.add_def(:h, {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}, h)

    assert terminating?(env, :h)
    assert terminating?(env, :plus)
  end
end
