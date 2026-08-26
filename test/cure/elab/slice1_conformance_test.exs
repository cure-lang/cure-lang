defmodule Cure.Elab.Slice1ConformanceTest do
  @moduledoc """
  Conformance corpus (design spec §11, M11.1): the full Slice-1 program from a
  `.cure` fixture must elaborate + certify as a whole, and each §6 negative must
  be rejected. This is the falsifiable acceptance the whole initiative targets.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.Env
  alias Cure.Elab.{Erase, Program}

  @fixture Path.join([__DIR__, "..", "..", "fixtures", "slice1.cure"])

  test "the complete §6 program elaborates and certifies from the fixture" do
    source = File.read!(@fixture)
    assert {:ok, env} = Program.elaborate(source)

    for name <- [:andd, :compose, :run, :forget_dec, :recover, :sketch] do
      assert Env.get_def(env, name), "expected #{name} to be defined"
    end
  end

  test "the sketch function carries a hole that blocks codegen" do
    source = File.read!(@fixture)
    {:ok, env} = Program.elaborate(source)
    assert Erase.has_hole?(Env.get_def(env, :sketch).body)
    # compose, by contrast, is hole-free and may be emitted.
    refute Erase.has_hole?(Env.get_def(env, :compose).body)
  end

  # -- §6 negatives: each must be rejected --------------------------------------

  defp negative(replace, with_) do
    File.read!(@fixture) |> String.replace(replace, with_) |> Program.elaborate()
  end

  # The spec (§6/§11) requires each negative be rejected with the *right code*.
  defp code({:error, err}) do
    case Program.semantic_error(err) do
      tuple when is_tuple(tuple) -> elem(tuple, 0)
      other -> other
    end
  end

  test "negative #1: seq with disagreeing middle indices — index-unification error" do
    # give recover an ill-typed body that composes two SFs with mismatched middle
    result =
      negative(
        "fn recover({as: SVDesc}, {bs: SVDesc}, p: Sigma(x: Dec, SF(as, bs, x))) -> SF(as, bs, p.1) = p.2",
        "fn bad_mid({as: SVDesc}, {bs: SVDesc}, {cs: SVDesc}, l: SF(as, bs, Causal), r: SF(cs, bs, Causal)) -> SF(as, bs, Causal) = seq(l, r)"
      )

    assert code(result) == :index_mismatch
  end

  test "negative #2: declared return index contradicts and's computation — conversion error" do
    result =
      negative("-> SF(as, cs, andd(d1, d2)) = seq(l, r)", "-> SF(as, cs, Dcoupled) = seq(l, r)")

    assert code(result) == :conversion_failure
  end

  test "negative #3: a non-total function used in a type" do
    assert {:error, error} =
             negative("fn andd(x: Dec, y: Dec) -> Dec = x", "fn andd(x: Dec, y: Dec) -> Dec = andd(x, y)")

    assert {:totality_required, :"Main#andd"} = Program.semantic_error(error)
  end

  test "negative #4: a Sigma pair whose second component mismatches B[a/x] — Sigma type error" do
    result =
      negative("-> Sigma(x: Dec, SF(as, bs, x)) = %[d, sf]", "-> Sigma(x: Dec, SF(as, bs, x)) = %[Dcoupled, sf]")

    # Rejection preserved. The primitive-Σ-specific `:sigma_mismatch` diagnostic is
    # retired with the primitive (D2); the inductive `mk_pair` ctor check surfaces
    # the underlying, more precise reason — the SF middle-index contradiction.
    assert code(result) == :index_mismatch
  end

  test "negative #5: the program has an unfilled hole and is refused for codegen" do
    {:ok, env} = Program.elaborate(File.read!(@fixture))
    assert {:error, {:unfilled_hole, details}} = Program.check_codegen_ready(env)
    assert details.definition == :"Main#sketch"
    assert %Cure.Diagnostic.Span{} = details.span
  end
end
