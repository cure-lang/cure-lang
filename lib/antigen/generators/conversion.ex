defmodule Antigen.Generators.Conversion do
  @moduledoc """
  Conversion-at-depth carriers (spec B). The discriminating difference sits in a
  `Vec` index behind a `plus` redex, so the kernel must REDUCE to decide. Reject
  carriers (mismatched filler) → `:mutant_term`; accept carriers (matched filler) →
  `:typed_term`. Backend-free: built only via the `Antigen.Gen` DSL.
  """
  alias Antigen.Challenge
  alias Antigen.Gen

  @carriers [:conv_index, :conv_motive]
  def carriers, do: @carriers
  @max_depth 6
  def max_depth, do: @max_depth

  # menu term helpers (closed literals)
  defp z, do: {:ctor, :Z, []}
  defp s(n), do: {:ctor, :S, [n]}
  defp num(0), do: z()
  defp num(k) when k > 0, do: s(num(k - 1))
  defp vnil, do: {:ctor, :vnil, []}
  defp vec(i), do: {:data, :Vec, [], [i]}
  defp bd, do: {:data, :Bd, [], []}
  defp plus(a, b), do: {:app, {:app, {:global, :plus}, a}, b}

  # closed Vec (S^k Z)
  defp vec_of(0), do: vnil()
  defp vec_of(k) when k > 0, do: {:ctor, :vcons, [num(k - 1), z(), vec_of(k - 1)]}

  # carrier term with filler of S-depth `fd` at the hole
  def carrier_term(:conv_index, a, b, fd),
    do: {:ctor, :vcons, [plus(num(a), num(b)), z(), vec_of(fd)]}

  def carrier_term(:conv_motive, a, b, fd),
    do:
      {:case, {:ctor, :T, []}, {:lam, Cure.Core.Grade.unrestricted(), bd(), vec(plus(num(a), num(b)))},
       [{:T, 0, vec_of(fd)}, {:F, 0, vec_of(fd)}]}

  # accept: whole-term type when the filler matches
  def accept_type(:conv_index, d), do: vec(num(d + 1))
  def accept_type(:conv_motive, d), do: vec(num(d))

  # draw conv_depth uniformly FIRST, then split into a+b (spec §3)
  defp depth_split do
    Gen.bind(Gen.int(0, @max_depth), fn d ->
      Gen.bind(Gen.int(0, d), fn a -> Gen.return({d, a, d - a}) end)
    end)
  end

  defp carrier_gen, do: Gen.frequency(Enum.map(@carriers, fn c -> {1, Gen.return(c)} end))

  @doc """
  Coverage-manifest cells (`Antigen.CoverManifest`). The only deterministic branch
  the reject generator tags is the carrier KIND (`:conv_index` / `:conv_motive`);
  the conv depth/split is randomised and carries no enumerable shape-class. One cell
  per carrier under the reject assay.
  """
  @spec cover_cells() :: [{String.t(), atom()}]
  def cover_cells do
    for c <- @carriers, do: {"mutation/rejection", c}
  end

  @doc """
  Sampleable generator that guarantees every declared carrier cell by binding over
  the fixed `@carriers` set. Used by the coverage-manifest gate.
  """
  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.bind(Gen.member_of(@carriers), fn carrier -> reject_for(carrier) end)
  end

  # Carriers are closed, binder-free terms (spec §4) — no env/context is needed
  # to construct them; the assays independently rebuild their own env from the
  # payload's `sig: :v1` field when they run.
  @spec conv_reject() :: Gen.t()
  def conv_reject do
    Gen.bind(carrier_gen(), fn carrier -> reject_for(carrier) end)
  end

  # Build a reject carrier for a fixed carrier kind (filler one deeper ⇒ mismatch).
  defp reject_for(carrier) do
    Gen.bind(depth_split(), fn {d, a, b} ->
      term = carrier_term(carrier, a, b, d + 1)

      fault = %{
        kind: carrier,
        witness: :conv,
        expected_index: d,
        actual_index: d + 1,
        reduction: :required,
        depth: d,
        carrier: carrier
      }

      Gen.return(
        Challenge.new(
          kind: :mutant_term,
          assay: "mutation/rejection",
          label: :ill_typed,
          payload: %{sig: :v1, ctx: [], type: vec(num(d)), term: term, fault: fault},
          cover_tag: carrier
        )
      )
    end)
  end

  # Accept dual: filler matches the reduced index, so the carrier is well-typed —
  # but ONLY after the kernel reduces the `plus` redex (typed-term corpus).
  @spec conv_accept(String.t()) :: Gen.t()
  def conv_accept(assay) do
    Gen.bind(carrier_gen(), fn carrier ->
      Gen.bind(depth_split(), fn {d, a, b} ->
        # filler matches reduced index ⇒ accept
        term = carrier_term(carrier, a, b, d)

        Gen.return(
          Challenge.new(
            kind: :typed_term,
            assay: assay,
            label: :well_typed,
            payload: %{sig: :v1, ctx: [], type: accept_type(carrier, d), term: term}
          )
        )
      end)
    end)
  end
end
