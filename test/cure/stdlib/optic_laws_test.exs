defmodule Cure.Stdlib.OpticLawsTest do
  @moduledoc """
  The optic laws, executed against the SHIPPING `lib/std/optic.cure`. These are
  the algebraic contract every well-behaved optic must satisfy; pinning them at
  runtime means a regression in the cross-module lowering or the eliminators
  surfaces as a violated law, not just a type error.

  - Lens (get-put / put-get / put-put): a lens is a well-behaved projection.
  - Affine (set-preview / preview-set / set-set / miss-is-no-op): a case optic
    focuses zero-or-one, and `set` is a no-op exactly when the focus is absent.
  - Traversal (identity / composition of `over`): `over` with `id` changes
    nothing, and `over(g)` after `over(f)` equals `over(g ∘ f)`.

  The laws are checked over a deterministic sample table (the codebase favours
  concrete run-tests over generative property tests — StreamData here is an
  Antigen-internal dependency, not an ExUnit style). Implicits erase, so the
  runtime arities are `lens/2`, `view/2`, `set/3`, `over/3`, `preview/2`,
  `lens_to_trav/1`, `affine_to_trav/1`. Option lowers OTP-lowercase
  (`{:some, v}` / `:none`); `Dynamic` constructors stay PascalCase (`{:Int, n}`).
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.{Program, Emit}

  setup_all do
    osrc = File.read!("lib/std/optic.cure")
    {:ok, otokens} = Lexer.tokenize(osrc, emit_events: false)
    {:ok, oast} = Parser.parse(otokens, emit_events: false)
    {:ok, oenv} = Program.elaborate(osrc)
    oorigins = Program.import_origins(oast)

    ofns =
      Program.reachable_def_names(oenv, [
        :lens,
        :view,
        :set,
        :over,
        :preview,
        :dyn_int,
        :lens_to_trav,
        :affine_to_trav
      ])

    {:ok, m} =
      Emit.compile_and_load(oenv, module: :"Cure.Test.OpticLaws", functions: ofns, origins: oorigins)

    dsrc = File.read!("lib/std/dynamic.cure")
    {:ok, denv} = Program.elaborate(dsrc)
    dfns = Program.reachable_def_names(denv, [:of_int, :of_str])
    {:ok, d} = Emit.compile_and_load(denv, module: :"Cure.Test.OpticLawsDyn", functions: dfns)

    # `fst` / `snd` lenses over an Int 2-tuple, built exactly as a caller would.
    fst = apply(m, :lens, [fn {a, _b} -> a end, fn n -> fn {_a, b} -> {n, b} end end])
    snd = apply(m, :lens, [fn {_a, b} -> b end, fn n -> fn {a, _b} -> {a, n} end end])

    {:ok, m: m, d: d, fst: fst, snd: snd}
  end

  # Sample structures and focus values the laws are quantified over.
  @tuples [{0, 0}, {1, 2}, {7, 3}, {-4, 9}]
  @ints [0, 1, 5, -2, 42]

  describe "lens laws" do
    test "get-put: viewing a freshly-set focus returns exactly what was set", %{m: m, fst: fst, snd: snd} do
      for l <- [fst, snd], s <- @tuples, v <- @ints do
        assert apply(m, :view, [l, apply(m, :set, [l, v, s])]) == v
      end
    end

    test "put-get: setting the focus back to what it already is changes nothing", %{m: m, fst: fst, snd: snd} do
      for l <- [fst, snd], s <- @tuples do
        assert apply(m, :set, [l, apply(m, :view, [l, s]), s]) == s
      end
    end

    test "put-put: the last set wins", %{m: m, fst: fst, snd: snd} do
      for l <- [fst, snd], s <- @tuples, v1 <- @ints, v2 <- @ints do
        assert apply(m, :set, [l, v2, apply(m, :set, [l, v1, s])]) == apply(m, :set, [l, v2, s])
      end
    end
  end

  describe "affine laws (dyn_int over Dynamic)" do
    setup %{m: _m, d: d} do
      hit = fn n -> apply(d, :of_int, [n]) end
      miss = apply(d, :of_str, [~c"nope"])
      {:ok, hit: hit, miss: miss}
    end

    test "set-preview: previewing a set focus yields Some(the set value) when the focus is present",
         %{m: m, hit: hit} do
      di = apply(m, :dyn_int, [])

      for n <- @ints, v <- @ints do
        assert apply(m, :preview, [di, apply(m, :set, [di, v, hit.(n)])]) == {:some, v}
      end
    end

    test "preview-set: setting a present focus to its current value is a no-op", %{m: m, hit: hit} do
      di = apply(m, :dyn_int, [])

      for n <- @ints do
        s = hit.(n)
        {:some, cur} = apply(m, :preview, [di, s])
        assert apply(m, :set, [di, cur, s]) == s
      end
    end

    test "set-set: the last set wins on a present focus", %{m: m, hit: hit} do
      di = apply(m, :dyn_int, [])

      for n <- @ints, v1 <- @ints, v2 <- @ints do
        s = hit.(n)
        assert apply(m, :set, [di, v2, apply(m, :set, [di, v1, s])]) == apply(m, :set, [di, v2, s])
      end
    end

    test "miss is a no-op: set/over on an absent focus leaves the structure untouched", %{m: m, miss: miss} do
      di = apply(m, :dyn_int, [])
      assert apply(m, :preview, [di, miss]) == :none

      for v <- @ints do
        assert apply(m, :set, [di, v, miss]) == miss
      end

      assert apply(m, :over, [di, fn n -> n + 1 end, miss]) == miss
    end
  end

  describe "traversal laws (via widened lens / affine)" do
    test "identity: over(id) changes nothing", %{m: m, d: d, fst: fst} do
      lens_trav = apply(m, :lens_to_trav, [fst])
      di_trav = apply(m, :affine_to_trav, [apply(m, :dyn_int, [])])
      id = fn x -> x end

      for s <- @tuples do
        assert apply(m, :over, [lens_trav, id, s]) == s
      end

      for n <- @ints do
        s = apply(d, :of_int, [n])
        assert apply(m, :over, [di_trav, id, s]) == s
      end
    end

    test "composition: over(g) after over(f) equals over(g ∘ f)", %{m: m, d: d, fst: fst} do
      lens_trav = apply(m, :lens_to_trav, [fst])
      di_trav = apply(m, :affine_to_trav, [apply(m, :dyn_int, [])])
      f = fn n -> n + 1 end
      g = fn n -> n * 3 end
      gf = fn n -> g.(f.(n)) end

      for s <- @tuples do
        assert apply(m, :over, [lens_trav, g, apply(m, :over, [lens_trav, f, s])]) ==
                 apply(m, :over, [lens_trav, gf, s])
      end

      for n <- @ints do
        s = apply(d, :of_int, [n])

        assert apply(m, :over, [di_trav, g, apply(m, :over, [di_trav, f, s])]) ==
                 apply(m, :over, [di_trav, gf, s])
      end
    end
  end
end
