defmodule Cure.Core.SccCertificateTamperTest do
  @moduledoc """
  §8.2 — the SCC verifier must not trust the proposer.

  docs/SOUNDNESS.md §8.2 records that the SCC closure in
  `Cure.Elab.TotalityGraph` is outside the TCB, and that "a bug there is
  invisible to the kernel". The design's answer is that the kernel does not
  trust the proposer: `Cure.Core.SCCCertificate.verify_partition/2`
  re-derives the edge set from the environment and checks the submitted
  partition against it.

  The existing tests (`totality_certificate_property_test.exs`) exercise the
  HONEST path — that a well-formed proposal is accepted. They do not test the
  direction that matters for soundness: that a LYING proposer is rejected.

  These tests forge partitions directly (bypassing `TotalityGraph`) and
  assert the verifier refuses each one. A mutual-recursion cycle `a -> b -> a`
  is the canonical non-terminating shape: if it can be split into two
  singleton components, each looks trivially terminating, so a verifier that
  accepted the split would certify a diverging program.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Certificate, Env, SCCCertificate}
  alias Cure.Elab.TotalityGraph

  @names [:a, :b]

  # a -> b -> a, a 2-cycle: one genuine SCC containing both names.
  defp cycle_env do
    @names
    |> Enum.with_index()
    |> Enum.reduce(Env.empty(), fn {name, index}, env ->
      callee = Enum.at(@names, rem(index + 1, length(@names)))
      Env.add_def(env, name, {:type, 0}, {:global, callee})
    end)
    |> then(fn env ->
      Enum.reduce(@names, env, fn name, acc ->
        %{body: body} = Env.get_def(acc, name)
        Env.put_direct_call_summary(acc, name, Certificate.direct_summary(name, body, acc))
      end)
    end)
  end

  # The honest proposal: one component holding both names.
  defp honest_partition do
    env = cycle_env()
    TotalityGraph.propose_partition(env, @names)
  end

  test "the honest proposal for a 2-cycle is accepted" do
    env = cycle_env()
    partition = honest_partition()

    assert {:ok, components} = SCCCertificate.verify_partition(env, partition)
    assert components == [Enum.sort(@names)]
  end

  # ---------------------------------------------------------------------
  # Forgery 1: SPLIT the cycle into two singleton components.
  #
  # This is the attack that matters. Two singletons have no self-loops and no
  # inter-component cycle is visible if the ranks are also forged, so a
  # verifier that trusted `component_of` would see two trivially terminating
  # definitions and certify a diverging program.
  # ---------------------------------------------------------------------
  test "a partition that SPLITS a real cycle is rejected" do
    env = cycle_env()
    partition = honest_partition()

    forged = %{
      partition
      | component_of: %{a: :a, b: :b},
        rank: %{a: 1, b: 0},
        components: %{
          a: %{members: [:a], root: :a, forward_tree: [], reverse_tree: []},
          b: %{members: [:b], root: :b, forward_tree: [], reverse_tree: []}
        }
    }

    # Rejected because the forged ranks leave the b -> a edge non-decreasing:
    # the verifier sees that the two singletons are still mutually reachable.
    assert {:error, {:totality_scc_invalid, %{reason: :rank_not_decreasing}}} =
             SCCCertificate.verify_partition(env, forged)
  end

  # ---------------------------------------------------------------------
  # Forgery 2: drop a definition from the universe, so its edge disappears.
  # ---------------------------------------------------------------------
  test "a partition that SHRINKS the universe is rejected" do
    env = cycle_env()
    partition = honest_partition()

    forged = %{partition | universe: [:a]}

    # The verifier re-derives the call set from the environment and reports the
    # omitted callee, rather than trusting the shrunken universe.
    assert {:error, {:totality_scc_incomplete, %{omitted: :b, verified_path: [:a, :b]}}} =
             SCCCertificate.verify_partition(env, forged)
  end

  # ---------------------------------------------------------------------
  # Forgery 3: submit a partition whose edges disagree with the environment.
  # The verifier re-derives edges from `Env.direct_call_summary`, so a
  # proposer cannot hide a call edge by omitting it.
  # ---------------------------------------------------------------------
  test "a partition that HIDES a call edge is rejected" do
    env = cycle_env()
    partition = honest_partition()

    forged = %{partition | edges: []}

    assert {:error, {:totality_scc_invalid, %{reason: :direct_edges_mismatch}}} =
             SCCCertificate.verify_partition(env, forged)
  end

  # ---------------------------------------------------------------------
  # Forgery 4: split the cycle and keep DISTINCT ranks.
  #
  # `verify_ranks` requires ranks to be a permutation of 0..n-1
  # (`rank_not_total` otherwise), so a forgery must keep them distinct. But a
  # 2-cycle needs BOTH a -> b and b -> a to be strictly rank-decreasing, which
  # no distinct pair of ranks can satisfy. So this forgery is rejected by
  # `rank_not_decreasing` whichever way the ranks are oriented — verified for
  # both `%{a: 0, b: 1}` and `%{a: 1, b: 0}`. That is the property that makes
  # SCC-splitting impossible: the rank check alone re-derives mutual
  # reachability from the edges.
  # ---------------------------------------------------------------------
  test "a SPLIT cycle with distinct ranks is rejected by the rank check" do
    env = cycle_env()
    partition = honest_partition()

    for rank <- [%{a: 0, b: 1}, %{a: 1, b: 0}] do
      forged = %{
        partition
        | component_of: %{a: :a, b: :b},
          rank: rank,
          components: %{
            a: %{members: [:a], root: :a, forward_tree: [], reverse_tree: []},
            b: %{members: [:b], root: :b, forward_tree: [], reverse_tree: []}
          }
      }

      assert {:error, {:totality_scc_invalid, %{reason: :rank_not_decreasing}}} =
               SCCCertificate.verify_partition(env, forged)
    end
  end

  # ---------------------------------------------------------------------
  # Forgery 5: claim a component spans members it cannot reach.
  # ---------------------------------------------------------------------
  test "a partition with a NON-SPANNING component tree is rejected" do
    env = cycle_env()
    partition = honest_partition()

    forged = put_in(partition, [:components, :a, :forward_tree], [])

    assert {:error, {:totality_scc_invalid, %{reason: :tree_edge_count}}} =
             SCCCertificate.verify_partition(env, forged)
  end
end
