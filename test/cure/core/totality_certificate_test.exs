defmodule Cure.Core.TotalityCertificateTest do
  use ExUnit.Case, async: true

  alias Cure.Core.{Env, TotalityCertificate}
  alias Cure.Elab.TotalityCertificate, as: Candidate

  defp summary(caller, calls) do
    core = %{
      version: 1,
      caller: caller,
      body_hash: :crypto.hash(:sha256, Atom.to_string(caller)),
      caller_arity: 1,
      calls:
        Enum.map(calls, fn {callee, matrix} ->
          %{
            id: :crypto.hash(:sha256, :erlang.term_to_binary({caller, callee, matrix})),
            callee: callee,
            callee_arity: 1,
            matrix: matrix,
            provenance: %{caller: caller}
          }
        end)
    }

    Map.put(core, :summary_hash, :crypto.hash(:sha256, :erlang.term_to_binary(core, [:deterministic])))
  end

  defp env_with_cycle(relation) do
    env =
      Env.empty()
      |> Env.add_def(:f, {:type, 0}, {:global, :g})
      |> Env.add_def(:g, {:type, 0}, {:global, :f})

    env
    |> Env.put_direct_call_summary(:f, summary(:f, [{:g, [[relation]]}]))
    |> Env.put_direct_call_summary(:g, summary(:g, [{:f, [[:equal]]}]))
  end

  test "an externally completed decreasing cycle has a kernel-checkable derivation" do
    env = env_with_cycle(:smaller)
    candidate = Candidate.propose(env, [:g, :f])

    assert {:ok, :total} = TotalityCertificate.verify(env, [:f, :g], candidate)
    assert Enum.any?(candidate.edges, fn {_id, edge} -> match?({:compose, _, _}, edge.derivation) end)
  end

  test "an exact non-decreasing cycle is verified and rejected as non-total" do
    env = env_with_cycle(:equal)
    candidate = Candidate.propose(env, [:f, :g])

    assert {:ok, {:not_total, %{source: source, target: source, matrix: matrix}}} =
             TotalityCertificate.verify(env, [:f, :g], candidate)

    assert Cure.Core.SizeChange.to_dense(matrix) == [[:equal]]
  end

  test "omitting a composed edge fails saturation instead of hiding a bad loop" do
    env = env_with_cycle(:equal)
    candidate = Candidate.propose(env, [:f, :g])

    {id, _edge} = Enum.find(candidate.edges, fn {_id, edge} -> edge.source == :f and edge.target == :f end)
    forged = %{candidate | edges: Map.delete(candidate.edges, id)}

    assert {:error, {:totality_derivation_invalid, %{reason: :closure_not_saturated, source: :f, target: :f}}} =
             TotalityCertificate.verify(env, [:f, :g], forged)
  end

  test "stale body and summary identities are rejected before proof replay" do
    env = env_with_cycle(:smaller)
    candidate = Candidate.propose(env, [:f, :g])

    stale_body = put_in(candidate.member_body_hashes.f, :crypto.hash(:sha256, "stale body"))

    assert {:error, {:totality_derivation_invalid, %{reason: :body_hash_mismatch, definition: :f}}} =
             TotalityCertificate.verify(env, [:f, :g], stale_body)

    stale_summary = put_in(candidate.direct_summary_hashes.g, :crypto.hash(:sha256, "stale summary"))

    assert {:error, {:totality_derivation_invalid, %{reason: :summary_hash_mismatch, definition: :g}}} =
             TotalityCertificate.verify(env, [:f, :g], stale_summary)
  end

  test "invalid and cyclic composition derivations are rejected explicitly" do
    env = env_with_cycle(:smaller)
    candidate = Candidate.propose(env, [:f, :g])
    {id, edge} = Enum.find(candidate.edges, fn {_id, edge} -> match?({:compose, _, _}, edge.derivation) end)
    {:compose, left, right} = edge.derivation

    invalid = put_in(candidate.edges[id].derivation, {:compose, right, left})

    assert {:error, {:totality_derivation_invalid, %{reason: reason, edge: ^id}}} =
             TotalityCertificate.verify(env, [:f, :g], invalid)

    assert reason in [:composition_mismatch, :incompatible_composition]

    cyclic = put_in(candidate.edges[id].derivation, {:compose, id, id})

    assert {:error, {:totality_derivation_invalid, %{reason: :cyclic_derivation, edge: ^id}}} =
             TotalityCertificate.verify(env, [:f, :g], cyclic)
  end

  test "every trusted direct edge must have a submitted Base derivation" do
    env = env_with_cycle(:smaller)
    candidate = Candidate.propose(env, [:f, :g])

    {base_id, _edge} =
      Enum.find(candidate.edges, fn {_id, edge} -> match?({:base, _}, edge.derivation) end)

    forged = %{candidate | edges: Map.delete(candidate.edges, base_id)}

    assert {:error, {:totality_derivation_invalid, %{reason: :missing_base_derivation, edge: ^base_id}}} =
             TotalityCertificate.verify(env, [:f, :g], forged)
  end
end
