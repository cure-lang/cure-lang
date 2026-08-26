defmodule Antigen.Generators.SeedPoolTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.SeedPool
  alias Antigen.{Challenge, Corpus}
  alias Cure.Core.Term

  @tmp "tmp/seedpool_test"
  setup do
    File.rm_rf!(@tmp)
    File.mkdir_p!(@tmp)
    on_exit(fn -> File.rm_rf!(@tmp) end)
    :ok
  end

  defp bank(path, c), do: Corpus.append(path, c, Corpus.dedup_key(c, :antibody))

  test "pool indexes only closed typed_term seeds, keyed by recorded type" do
    path = Path.join(@tmp, "seeds.sexp")
    nat = {:data, :Nat, [], []}

    bank(
      path,
      Challenge.new(
        kind: :typed_term,
        assay: "term/infer_check",
        label: :well_typed,
        payload: %{sig: :v1, ctx: [], type: nat, term: {:ctor, :S, [{:ctor, :Z, []}]}}
      )
    )

    # a mutant with a nominal type MUST NOT enter the pool
    # (term: "fst on a Nat" spelled inductively — D2 projection case over mk_pair)
    bank(
      path,
      Challenge.new(
        kind: :mutant_term,
        assay: "mutation/rejection",
        label: :ill_typed,
        payload: %{
          sig: :v1,
          ctx: [],
          type: nat,
          term:
            {:case, {:ctor, :Z, []},
             {:lam, Cure.Core.Grade.unrestricted(),
              {:data, :Sigma, [nat, {:lam, Cure.Core.Grade.unrestricted(), nat, nat}], []}, nat},
             [{:mk_pair, 2, {:var, 1}}]},
          fault: %{kind: :proj_non_pair}
        }
      )
    )

    pool = SeedPool.load(path)
    assert [{:ctor, :S, [{:ctor, :Z, []}]}] = Map.get(pool, nat)
    # `Antigen.Gen` has no `defstruct` — it is a plain tagged-tuple type, so the
    # generator SeedPool returns is a tuple, not a `%Antigen.Gen{}` struct.
    assert is_tuple(SeedPool.pool_gen(pool, nat))
    assert SeedPool.pool_gen(pool, {:data, :Vec, [], [{:ctor, :Z, []}]}) == :none
    assert Enum.all?(Map.get(pool, nat), &Term.term?/1)
  end

  test "absent file yields an empty pool and :none for every goal" do
    pool = SeedPool.load(Path.join(@tmp, "missing.sexp"))
    assert pool == %{}
    assert SeedPool.pool_gen(pool, {:data, :Nat, [], []}) == :none
  end

  test "an open typed_term (empty ctx, free de-Bruijn var) is excluded from the pool" do
    # `ctx: []` alone is not sufficient — a term can carry a free de-Bruijn index
    # despite an empty context; a spliced free variable would be unbound at any use
    # site, so closedness must be checked on the term itself.
    path = Path.join(@tmp, "seeds_open.sexp")
    nat = {:data, :Nat, [], []}

    bank(
      path,
      Challenge.new(
        kind: :typed_term,
        assay: "term/infer_check",
        label: :well_typed,
        payload: %{sig: :v1, ctx: [], type: nat, term: {:var, 0}}
      )
    )

    pool = SeedPool.load(path)
    assert pool == %{}
  end
end
