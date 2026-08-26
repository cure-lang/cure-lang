defmodule Antigen.PortabilityGuardTest do
  @moduledoc """
  Bank-time portability guard. A challenge that reconstructs an atom absent from
  `Challenge.__known_atoms__/0` must be REJECTED — loudly — at banking time, never
  silently written to a store that then crashes the replay gate on a fresh VM.

  This is the general defense behind the `:many` fix. The poison atom is interned
  in the *generating* VM (the generator built a term literally carrying it), so a
  naive encode→decode roundtrip in that VM would pass. The guard therefore checks
  whitelist MEMBERSHIP (`__known_atoms__`), not mere interning — exactly what a
  fresh replay VM enforces.
  """
  use ExUnit.Case, async: false
  import ExUnit.CaptureIO
  alias Antigen.{Challenge, Corpus, Gen, Runner}
  alias Cure.Core.Inductive

  @tmp "tmp/antigen_portability_guard_test"

  setup do
    File.rm_rf!(@tmp)
    File.mkdir_p!(@tmp)
    on_exit(fn -> File.rm_rf!(@tmp) end)
    :ok
  end

  # A family challenge whose *only* non-portable atom is the ctor-field quantity:
  # every other name (:P/:pc/:x/:a) is whitelisted, and the quantity is minted here
  # (so it is interned in THIS VM) but never added to `@known_atoms` — precisely the
  # `:many` shape that slipped past banking and crashed the replay gate.
  defp unportable_challenge do
    bogus = String.to_atom("antigen_unportable_probe_qty")
    fam = Inductive.family(:P, [{:a, {:type, 0}}], [], 0)
    ct = Inductive.ctor(:pc, [{:x, {:type, 0}}], [], [bogus], [])

    Challenge.new(
      kind: :family,
      assay: "universes",
      label: :well_typed,
      payload: %{family: fam, ctors: [ct]},
      seed: 1,
      note: "portability probe"
    )
  end

  describe "Challenge.known_atom!/1" do
    test "returns the interned atom for a whitelisted name" do
      assert Challenge.known_atom!("many") == :many
      assert Challenge.known_atom!("P") == :P
    end

    test "raises UnknownAtomError naming a non-whitelisted string" do
      e =
        assert_raise Challenge.UnknownAtomError, fn ->
          Challenge.known_atom!("antigen_definitely_not_whitelisted_zzz")
        end

      assert e.name == "antigen_definitely_not_whitelisted_zzz"
    end
  end

  test "decode_record surfaces an UnknownAtomError for a non-portable record" do
    line = Corpus.encode_record(unportable_challenge())
    assert {:error, %Challenge.UnknownAtomError{}} = Corpus.decode_record(line)
  end

  test "Corpus.append rejects a non-portable challenge and writes nothing" do
    c = unportable_challenge()
    path = Path.join(@tmp, "seeds.sexp")

    assert {:rejected, %Challenge.UnknownAtomError{}} =
             Corpus.append(path, c, Corpus.dedup_key(c, :seed))

    assert Corpus.record_lines(path) == []
  end

  test "mix antigen banking loudly reports a non-portable challenge and banks none" do
    c = unportable_challenge()
    path = Path.join(@tmp, "seeds.sexp")

    {r, err} =
      with_io(:stderr, fn ->
        Runner.generate(gen: Gen.return(c), count: 3, seeds_path: path, seed: 1)
      end)

    assert r.seeds_banked == 0
    assert r.rejected >= 1
    assert err =~ "INVALID BUILD ARTIFACT [E100]"
    assert err =~ "non-portable"
    assert err =~ "antigen_unportable_probe_qty"
    assert err =~ "__known_atoms__"
    refute err =~ "!!! ANTIGEN"
    assert Corpus.record_lines(path) == []
  end
end
