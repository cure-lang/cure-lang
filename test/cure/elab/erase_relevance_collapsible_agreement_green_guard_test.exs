defmodule Cure.Elab.EraseRelevanceCollapsibleAgreementGreenGuardTest do
  @moduledoc """
  GREEN_GUARD for FINDING B (erasure-unify cluster): `Cure.Elab.Erase`'s private
  `collapsible_ctor?/3` (lib/cure/elab/erase.ex:190) and
  `Cure.Elab.Relevance`'s private `collapsible_case?/2` (lib/cure/elab/relevance.ex:738)
  are byte-identical judgments ("a case's single branch names its family's ONLY
  constructor, and every one of that constructor's fields is `:erased`")
  maintained as two separate copies. They agree TODAY — there is no live
  behavioral defect to red — but nothing stops them drifting apart on a future
  edit to just one copy.

  This pins the agreement through BOTH modules' PUBLIC entry points
  (`Erase.erase/2` and `Relevance.check/4`), over a table with one collapsible
  family (single ctor, all-erased fields) and one non-collapsible family
  (multiple ctors), by exploiting an OBSERVABLE side effect of each judgment:

    * `Erase.erase/2` on a single-branch `:case` COLLAPSES to the branch body
      (dropping the `:case` node entirely) iff `collapsible_ctor?` is true.
    * `Relevance.check/4` EXEMPTS the scrutinee from the relevance walk iff
      `collapsible_case?` is true — so a case whose scrutinee is an in-scope
      `:erased` parameter is accepted (`:ok`) iff collapsible, and rejected
      (`{:error, {:erased_used_relevantly, …}}`) iff not.

  Passes now (both judgments agree on both families); would go RED the moment
  either private copy's condition drifts from the other's, since the two
  independent observations below would then disagree with each other for the
  same family.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Env, Inductive}
  alias Cure.Elab.{Erase, Relevance}

  @dummy {:data, :Dummy, [], []}
  @motive {:lam, :unrestricted, @dummy, @dummy}

  # Collapsible: `Proof`'s sole constructor `MkProof` has ONE field, erased.
  defp proof_env do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Proof, [], [], 0), [
      Inductive.ctor(:MkProof, [w: @dummy], [], [:erased])
    ])
  end

  # NOT collapsible: `Bool2` has TWO constructors (even though the branch under
  # test only names one of them).
  defp bool2_env do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Bool2, [], [], 0), [
      Inductive.ctor(:T2, [], []),
      Inductive.ctor(:F2, [], [])
    ])
  end

  # Indexed singleton: the family has two constructors globally, but a checked
  # case at `IndexedProof(LeftIndex)` can retain only `LeftProof`.  Coverage has
  # already proved that branch exhaustive before either pass sees Core.  Since
  # its only field is erased, the case is computationally irrelevant just like
  # the globally-single-constructor `Proof` case above.
  defp indexed_proof_env do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Index, [], [], 0), [
      Inductive.ctor(:LeftIndex, [], []),
      Inductive.ctor(:RightIndex, [], [])
    ])
    |> Inductive.declare(Inductive.family(:IndexedProof, [], [index: {:data, :Index, [], []}], 0), [
      Inductive.ctor(:LeftProof, [], [{:ctor, :LeftIndex, []}]),
      Inductive.ctor(:RightProof, [], [{:ctor, :RightIndex, []}])
    ])
  end

  # A single-branch case scrutinising the sole in-scope `:erased` parameter
  # (`{:var, 0}`), whose branch body ignores every field it binds.
  defp erased_scrutinee_case(cname, arity),
    do: {:case, {:var, 0}, @motive, [{cname, arity, {:global, :done}}]}

  defp erased_via_erase?(env, cname, arity) do
    case Erase.erase(env, erased_scrutinee_case(cname, arity)) do
      {:case, _, _, _} -> false
      _collapsed_to_branch_body -> true
    end
  end

  defp exempted_via_relevance?(env, cname, arity) do
    case Relevance.check(env, :f, [:erased], erased_scrutinee_case(cname, arity)) do
      :ok -> true
      {:error, {:erased_used_relevantly, _}} -> false
    end
  end

  test "Erase and Relevance agree: a proof-like single-erased-field ctor collapses AND is exempt" do
    env = proof_env()
    assert erased_via_erase?(env, :MkProof, 1) == true
    assert exempted_via_relevance?(env, :MkProof, 1) == true
  end

  test "Erase and Relevance agree: a multi-constructor family neither collapses nor is exempt" do
    env = bool2_env()
    assert erased_via_erase?(env, :T2, 0) == false
    assert exempted_via_relevance?(env, :T2, 0) == false
  end

  test "an index-forced singleton case with erased fields collapses even in a multi-constructor family" do
    env = indexed_proof_env()

    assert erased_via_erase?(env, :LeftProof, 0)
    assert exempted_via_relevance?(env, :LeftProof, 0)
  end

  test "kernel-certified empty elimination neither retains nor scrutinises its erased proof" do
    term = {:case, {:var, 0}, @motive, []}

    assert Erase.erase(Env.empty(), term) == {:ctor, :cure_erased, []}
    assert Relevance.check(Env.empty(), :absurd, [:erased], term) == :ok
  end

  test "an impossible proof branch does not make an otherwise forced proof case runtime-relevant" do
    env = indexed_proof_env()

    term =
      {:case, {:var, 0}, @motive,
       [
         {:LeftProof, 0, {:global, :done}},
         {:RightProof, 0, {:case, {:global, :impossible_witness}, @motive, []}}
       ]}

    assert Erase.erase(env, term) == {:global, :done}
    assert Relevance.check(env, :forced, [:erased], term) == :ok
  end

  test "a convoy does not reapply runtime arguments after its case erases to unreachable" do
    env = indexed_proof_env()

    convoy =
      {:app,
       {:case, {:global, :proof}, @motive,
        [
          {:LeftProof, 0, {:lam, :erased, @dummy, {:case, {:global, :impossible_witness}, @motive, []}}}
        ]}, {:global, :runtime_argument}}

    assert Erase.erase(env, convoy) == {:ctor, :cure_erased, []}
  end

  test "the two judgments AGREE with each other across the whole family table" do
    table = [
      {proof_env(), :MkProof, 1},
      {bool2_env(), :T2, 0},
      {indexed_proof_env(), :LeftProof, 0}
    ]

    for {env, cname, arity} <- table do
      assert erased_via_erase?(env, cname, arity) == exempted_via_relevance?(env, cname, arity),
             "Erase.collapsible_ctor? and Relevance.collapsible_case? DISAGREED for #{cname}/#{arity}"
    end
  end
end
