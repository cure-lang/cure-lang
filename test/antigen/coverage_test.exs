defmodule Antigen.CoverageTest do
  use ExUnit.Case, async: true
  alias Antigen.{Challenge, Coverage}

  test "constructor set and depth bucket for a small term" do
    c = Challenge.stub({:app, {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}}, {:type, 0}})
    {ctors, bucket, _flags, label} = Coverage.key(c)
    assert :app in ctors and :lam in ctors and :type in ctors and :var in ctors
    assert bucket == :b0_2
    assert label == :none
  end

  test "app_present flag is set when an application occurs" do
    c = Challenge.stub({:app, {:var, 0}, {:var, 1}})
    {_ctors, _bucket, flags, _label} = Coverage.key(c)
    assert :app_present in flags
    refute :case_present in flags
  end

  test "depth bucket climbs into b3_5 for a deeper term" do
    deep = {:app, {:app, {:app, {:var, 0}, {:var, 0}}, {:var, 0}}, {:var, 0}}
    {_c, bucket, _f, _l} = Coverage.key(Challenge.stub(deep))
    assert bucket == :b3_5
  end

  test "key_string is stable and identical for equal keys" do
    c = Challenge.stub({:type, 0})
    assert Coverage.key_string(Coverage.key(c)) == Coverage.key_string(Coverage.key(c))
    assert is_binary(Coverage.key_string(Coverage.key(c)))
  end

  test "has_shadowing flag fires for a binder nested under another binder, not for a single binder" do
    single = {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}}
    {_c, _b, flags1, _l} = Coverage.key(Challenge.stub(single))
    refute :has_shadowing in flags1

    curried_pi =
      {:pi, Cure.Core.Grade.unrestricted(), {:type, 0}, {:pi, Cure.Core.Grade.unrestricted(), {:type, 0}, {:type, 0}}}

    {_c, _b, flags2, _l} = Coverage.key(Challenge.stub(curried_pi))
    assert :has_shadowing in flags2
  end

  test "terms_of returns every embedded term of an indexed_case challenge" do
    dec = {:data, :Dec, [], []}
    fam = Cure.Core.Inductive.family(:Box, [], [{:d, dec}], 0)
    ctors = [Cure.Core.Inductive.ctor(:mk, [{:x, dec}], [{:var, 0}])]

    body =
      {:case, {:ctor, :mk, [{:ctor, :Causal, []}]},
       {:lam, Cure.Core.Grade.unrestricted(), dec,
        {:lam, Cure.Core.Grade.unrestricted(), {:data, :Box, [], [{:var, 0}]}, dec}}, [{:mk, 1, {:var, 0}}]}

    c =
      Antigen.Challenge.new(
        kind: :indexed_case,
        assay: "indexed/case",
        label: :well_typed,
        payload: %{families: [{fam, ctors}], def_name: :probe, def_type: dec, def_body: body}
      )

    terms = Antigen.Coverage.terms_of(c)
    # family index type
    assert dec in terms
    # ctor result index
    assert {:var, 0} in terms
    # def body
    assert body in terms
  end

  test "terms_of extracts type, term and ctx for :mutant_term" do
    # "fst on a Nat" spelled inductively (D2): projection case over mk_pair.
    fault_term =
      {:case, {:ctor, :Z, []},
       {:lam, Cure.Core.Grade.unrestricted(),
        {:data, :Sigma,
         [{:data, :Nat, [], []}, {:lam, Cure.Core.Grade.unrestricted(), {:data, :Nat, [], []}, {:data, :Nat, [], []}}],
         []}, {:data, :Nat, [], []}}, [{:mk_pair, 2, {:var, 1}}]}

    c =
      Antigen.Challenge.new(
        kind: :mutant_term,
        assay: "mutation/rejection",
        label: :ill_typed,
        payload: %{
          sig: :v1,
          ctx: [{:data, :Nat, [], []}],
          type: {:data, :Nat, [], []},
          term: fault_term,
          fault: %{kind: :proj_non_pair, witness: :head, expected_head: :Sigma, injected_head: :Nat, scope: nil}
        }
      )

    ts = Antigen.Coverage.terms_of(c)
    assert fault_term in ts
    assert {:data, :Nat, [], []} in ts
  end

  defp tt(term),
    do:
      Challenge.new(
        kind: :typed_term,
        assay: "term/infer_check",
        label: :well_typed,
        payload: %{sig: :v1, ctx: [], type: {:data, :Nat, [], []}, term: term}
      )

  test "coverage key distinguishes terms that collide under the coarse key" do
    # `Coverage.constructors/1` folds `tag(node) = elem(node, 0)` over EVERY subterm,
    # so `ctors` is the set of former-tags present, not literal data-ctor names. Two
    # terms built from the SAME former-tag set (only :app/:global/:var), differing
    # only in :app *count*, collide today (same ctors, same :b0_2 bucket, same
    # {:app_present} flags, same label) but differ after the former-histogram enrichment.
    # one :app
    a = tt({:app, {:global, :plus}, {:var, 0}})
    # two :app
    b = tt({:app, {:app, {:global, :plus}, {:var, 0}}, {:var, 0}})
    refute Coverage.key(a) == Coverage.key(b)
    assert Coverage.key_string(Coverage.key(b)) =~ "former_app_nm"
  end

  test "enriched key still plateaus (bounded distinct keys over many terms)" do
    terms =
      for d <- 0..40 do
        Enum.reduce(0..rem(d, 6), {:ctor, :Z, []}, fn _, acc -> {:ctor, :S, [acc]} end)
      end

    keys = terms |> Enum.map(&Coverage.key(tt(&1))) |> Enum.uniq()
    assert length(keys) <= 12, "key space must saturate, got #{length(keys)}"
  end
end
