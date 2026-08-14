defmodule Antigen.Generators.SelfTest do
  @moduledoc """
  The generators ARE the oracle (spec §5, §12), so their label-correctness is
  validated here against the real kernel over a fixed known-good/known-bad set —
  including the confirmed mutual cycle Antigen must flag. If a check fails, the
  *generator* is wrong, not this test.
  """
  use ExUnit.Case, async: true

  alias Antigen.{Backend, Challenge}
  alias Antigen.Generators.{Totality, Positivity, Forcing}
  alias Cure.Core.{Env, Inductive, Eval, Term}

  # --- Totality: labels are correct by construction --------------------------

  test ":terminating def is genuinely accepted by the real certifier (completeness)" do
    c = Totality.structural_terminating()
    env = Totality.env_of(c)
    assert Enum.all?(c.payload.focus, &Cure.Elab.TotalityClosure.provably_total?(env, &1))
  end

  test ":diverging mutual pair is genuinely non-terminating by construction (mutual back-edges, no self-call)" do
    c = Totality.diverging_mutual_pair()
    env = Totality.env_of(c)
    bf = Env.get_def(env, :f).body
    bg = Env.get_def(env, :g).body
    # genuine mutual cycle: each references its sibling, neither references itself.
    # This label-by-construction check is the enduring proof the generator produces
    # real divergence, independent of the certifier's live behaviour (spec §2).
    assert mentions_global?(bf, :g) and not mentions_global?(bf, :f)
    assert mentions_global?(bg, :f) and not mentions_global?(bg, :g)
    # ...and (post-fix) the certifier now correctly REJECTS the mutual cycle.
    refute Cure.Elab.TotalityClosure.provably_total?(env, :f)
    refute Cure.Elab.TotalityClosure.provably_total?(env, :g)
  end

  # --- Positivity: labels agree with the real positivity checker -------------

  test ":positive family is accepted, :negative family is rejected" do
    pos = Positivity.positive_family()
    neg = Positivity.negative_family()
    assert :ok == positivity_verdict(pos)
    assert {:error, {:non_strictly_positive, _}} = positivity_verdict(neg)
  end

  # --- Forcing: distinct terms that genuinely force each global under plain eval

  test "forcing pair is structurally distinct and each term forces its global (non-δ eval)" do
    c = Forcing.forcing_pair()
    %{t: t, tprime: tp} = c.payload
    refute t == tp
    assert head_global(Eval.eval(t, [])) == :f
    assert head_global(Eval.eval(tp, [])) == :g
  end

  # --- Soundness meta-tests: every sampled challenge is well-formed -----------

  test "every sampled challenge from each generator is well-formed (env_of succeeds, terms are Terms)" do
    for gen <- [Totality.gen(), Positivity.gen(), Forcing.gen()] do
      Backend.StreamData.sample(Backend.StreamData.interp(gen), 20)
      |> Enum.each(&assert_well_formed/1)
    end
  end

  defp assert_well_formed(%Challenge{kind: :def_group} = c) do
    assert %Env{} = Totality.env_of(c)
    assert Enum.all?(c.payload.defs, fn d -> Term.term?(d.type) and Term.term?(d.body) end)
  end

  defp assert_well_formed(%Challenge{kind: :family} = c) do
    assert %Env{} = Positivity.env_of(c)
  end

  # Multi-family positivity shapes (through-constructor) ride the :indexed_case
  # record; Positivity.env_of declares every family in the payload.
  defp assert_well_formed(%Challenge{kind: :indexed_case, payload: %{families: fams}} = c) do
    assert %Env{} = Positivity.env_of(c)

    assert Enum.all?(fams, fn {_fam, ctors} ->
             Enum.all?(ctors, fn %{args: args} -> Enum.all?(args, fn {_n, ty} -> Term.term?(ty) end) end)
           end)
  end

  defp assert_well_formed(%Challenge{kind: :forcing_pair} = c) do
    assert %Env{} = Forcing.certified_env_of(c)
    assert Term.term?(c.payload.t) and Term.term?(c.payload.tprime)
  end

  # --- helpers ---------------------------------------------------------------

  defp positivity_verdict(c) do
    env = Positivity.env_of(c)
    Inductive.positive?(env, Inductive.get_family(env, c.payload.family.name))
  end

  defp mentions_global?({:global, n}, n), do: true
  defp mentions_global?(t, n) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&mentions_global?(&1, n))
  defp mentions_global?(l, n) when is_list(l), do: Enum.any?(l, &mentions_global?(&1, n))
  defp mentions_global?(_, _), do: false

  defp head_global({:vneutral, n}), do: head_global_n(n)
  defp head_global(_), do: nil
  defp head_global_n({:napp, n, _}), do: head_global_n(n)
  defp head_global_n({:nglobal, name}), do: name
  defp head_global_n(_), do: nil
end
