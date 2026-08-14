defmodule Cure.Elab.TotalityGraphTest do
  use ExUnit.Case, async: true

  alias Cure.Core.{Certificate, Env, SCCCertificate}
  alias Cure.Elab.TotalityGraph

  defp env_with_graph do
    defs = %{
      a: {:global, :b},
      b: {:global, :a},
      c: {:global, :a},
      leaf: {:ctor, :Unit, []}
    }

    env =
      Enum.reduce(defs, Env.empty(), fn {name, body}, env ->
        Env.add_def(env, name, {:type, 0}, body)
      end)

    Enum.reduce(defs, env, fn {name, body}, env ->
      Env.put_direct_call_summary(env, name, Certificate.direct_summary(name, body, env))
    end)
  end

  test "proposes actual recursive SCCs rather than treating the scheduling region as mutual" do
    certificate = TotalityGraph.propose_partition(env_with_graph(), [:c, :b, :leaf, :a])

    assert Enum.map(certificate.components, fn {_id, c} -> c.members end) |> Enum.sort() ==
             [[:a, :b], [:c], [:leaf]]

    assert certificate.component_of.a == certificate.component_of.b
    refute certificate.component_of.c == certificate.component_of.a

    assert certificate.rank[certificate.component_of.c] >
             certificate.rank[certificate.component_of.a]
  end

  test "partition and witnesses are independent of declaration order" do
    env = env_with_graph()
    left = TotalityGraph.propose_partition(env, [:a, :b, :c, :leaf])
    right = TotalityGraph.propose_partition(env, [:leaf, :c, :b, :a])

    assert left == right
    assert left.components[left.component_of.a].forward_tree != []
    assert left.components[left.component_of.a].reverse_tree != []
  end

  test "the kernel-side checker verifies the proposed partition" do
    env = env_with_graph()
    certificate = TotalityGraph.propose_partition(env, [:a, :b, :c, :leaf])

    assert {:ok, components} = SCCCertificate.verify_partition(env, certificate)
    assert Enum.sort(components) == [[:a, :b], [:c], [:leaf]]
  end

  test "the checker rejects an omitted recursive member with a structured witness" do
    env = env_with_graph()
    certificate = TotalityGraph.propose_partition(env, [:a, :b, :c, :leaf])
    bad = %{certificate | universe: [:a, :c, :leaf]}

    assert {:error,
            {:totality_scc_incomplete,
             %{
               caller: :a,
               omitted: :b,
               proposed_component: [:a],
               verified_path: [:a, :b],
               direct_call_id: direct_call_id,
               summary_hash: summary_hash
             }}} =
             SCCCertificate.verify_partition(env, bad)

    assert is_binary(direct_call_id)
    assert is_binary(summary_hash)
  end

  test "stale summary diagnostics identify both bodies and the checker version" do
    env = env_with_graph()
    certificate = TotalityGraph.propose_partition(env, [:a, :b, :c, :leaf])
    old_body_hash = :crypto.hash(:sha256, "old body")
    bad = put_in(certificate.summary_body_hashes.a, old_body_hash)

    assert {:error,
            {:totality_summary_stale,
             %{
               definition: :a,
               old_body_hash: ^old_body_hash,
               new_body_hash: new_body_hash,
               checker_version: checker_version
             }}} = SCCCertificate.verify_partition(env, bad)

    assert is_binary(new_body_hash)
    assert is_integer(checker_version)
    assert checker_version > 0
  end

  test "the checker rejects a forged rank and a forged connectivity edge" do
    env = env_with_graph()
    certificate = TotalityGraph.propose_partition(env, [:a, :b, :c, :leaf])
    a_component = certificate.component_of.a
    c_component = certificate.component_of.c

    bad_rank =
      certificate
      |> put_in([:rank, a_component], certificate.rank[c_component])
      |> put_in([:rank, c_component], certificate.rank[a_component])

    assert {:error, {:totality_scc_invalid, %{reason: :rank_not_decreasing}}} =
             SCCCertificate.verify_partition(env, bad_rank)

    bad_tree = put_in(certificate.components[a_component].forward_tree, [:forged])

    assert {:error, {:totality_scc_invalid, %{reason: :unknown_tree_edge, edge: :forged}}} =
             SCCCertificate.verify_partition(env, bad_tree)

    bad_reverse_tree = put_in(certificate.components[a_component].reverse_tree, [:forged_reverse])

    assert {:error, {:totality_scc_invalid, %{reason: :unknown_tree_edge, edge: :forged_reverse}}} =
             SCCCertificate.verify_partition(env, bad_reverse_tree)
  end

  test "the checker rejects merging distinct one-way-connected SCCs" do
    env = env_with_graph()
    certificate = TotalityGraph.propose_partition(env, [:a, :b, :c, :leaf])
    a_component = certificate.component_of.a
    c_component = certificate.component_of.c
    c_to_a = Enum.find(certificate.edges, &(&1.source == :c and &1.target == :a))

    merged =
      certificate
      |> put_in([:component_of, :c], a_component)
      |> put_in([:components, a_component, :members], [:a, :b, :c])
      |> put_in(
        [:components, a_component, :reverse_tree],
        certificate.components[a_component].reverse_tree ++ [c_to_a.id]
      )
      |> update_in([:components], &Map.delete(&1, c_component))
      |> then(fn candidate ->
        ids = candidate.components |> Map.keys() |> Enum.sort()
        %{candidate | rank: ids |> Enum.with_index() |> Map.new()}
      end)

    assert {:error, {:totality_scc_invalid, %{reason: :tree_edge_count, component: ^a_component, direction: :forward}}} =
             SCCCertificate.verify_partition(env, merged)
  end

  test "the checker rejects an alias-shaped forged canonical universe key" do
    env = env_with_graph()
    certificate = TotalityGraph.propose_partition(env, [:a, :b, :c, :leaf])
    forged = %{certificate | universe: [:"Alias#a", :b, :c, :leaf]}

    assert {:error, {:totality_scc_invalid, %{reason: :unknown_definition, definition: :"Alias#a"}}} =
             SCCCertificate.verify_partition(env, forged)
  end

  test "an unresolved direct callee is not misreported as an omitted SCC member" do
    body = {:global, :missing}

    env =
      Env.empty()
      |> Env.add_def(:caller, {:type, 0}, body)
      |> then(&Env.put_direct_call_summary(&1, :caller, Certificate.direct_summary(:caller, body, &1)))

    certificate = TotalityGraph.propose_partition(env, [:caller])

    assert {:error,
            {:totality_unknown_callee,
             %{
               caller: :caller,
               callee: :missing,
               core_term: {:global, :missing},
               provenance: %{caller: :caller, core_path: 0}
             }}} = SCCCertificate.verify_partition(env, certificate)
  end

  test "malformed partition certificates are rejected without field-access exceptions" do
    env = env_with_graph()
    certificate = TotalityGraph.propose_partition(env, [:a, :b, :c, :leaf])

    assert {:error, {:totality_scc_invalid, %{reason: :malformed_certificate, missing: [:components]}}} =
             SCCCertificate.verify_partition(env, Map.delete(certificate, :components))

    component = certificate.component_of.a
    malformed_component = update_in(certificate.components[component], &Map.delete(&1, :root))

    assert {:error, {:totality_scc_invalid, %{reason: :malformed_component, component: ^component, missing: [:root]}}} =
             SCCCertificate.verify_partition(env, malformed_component)
  end
end
