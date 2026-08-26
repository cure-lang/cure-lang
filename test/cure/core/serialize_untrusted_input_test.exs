defmodule Cure.Core.SerializeUntrustedInputTest do
  @moduledoc """
  `Serialize.decode/1` is the entry point commitment C2 exists for: `docs/KERNEL.md` and this
  module's own moduledoc both describe it as the door an *independent, untrusted* checker feeds
  bytes into — "a kernel written in another language can parse this format, rebuild the Core
  term, and re-run check/infer on it". `Antigen.Generators.DecodeProbe` states the contract:
  decode "must be TOTAL ... malformed input returns `{:error, _}` and never crashes or loops".

  It did not hold. The existing fuzz corpus only exercised *parse*-level malforms — unbalanced
  parens, unknown heads, non-atom heads — and never a syntactically-valid s-expression whose
  **shape** violates a `Term.term?/1` invariant. `build_node` read every numeric field as a
  plain integer:

    * `(type -1)` rebuilt `{:type, -1}`, which `Kernel.infer/2` then typed as sound —
      `Universe.succ(-1)`'s guard `level + 1 <= ceiling` is satisfied by any negative level, so
      `Type(-1) : Type(0)` passed the trusted kernel with no error anywhere on the path.
    * `(var -1)` rebuilt `{:var, -1}`, and `Context.lookup/2` resolved it through `Enum.at/2`,
      which counts from the END for a negative index — type confusion against a binding the
      term does not name. (Both ends of that are now closed; see `hole_and_debruijn_test.exs`.)
    * `(nat -5)` / `(bounded -5)` rebuilt compact literals of an inherently non-negative tower.
      `Kernel.infer/2`'s clauses for both are guarded `n >= 0` with no fallback, so these
      crashed with `FunctionClauseError` rather than erroring.
    * `(branch Z -3 …)` rebuilt a branch binding a negative number of constructor fields.

  Separately, `build/1` had bare-leaf pass-through clauses (`{:int, n} -> {:ok, n}` and friends).
  They existed so `build_node`'s literal handlers could match a raw token — but `build_all/1`
  and `binary/3` recurse through the same `build/1` for every CHILD position, positions that
  must hold a full `(tag …)` term. `enc/1` never emits a bare token there, so the path was
  reachable only from adversarial input, and it produced a raw Elixir scalar sitting where a
  subterm belongs. The clauses are gone; `build_node` matches its tokens directly.

  Rather than bolt a guard onto each `build_node` clause, `decode/1` now checks the finished
  term against `Term.term?/1` — one linear pass that cannot drift from the grammar it validates.

  ## Round-trip fidelity for names

  `sym/1` emitted an atom's name as an unescaped bareword. Elixir atoms are arbitrary byte
  sequences, so `:"has space"` encoded to something the tokenizer read back as several tokens:
  `decode(encode(t)) != {:ok, t}` for a value `enc/1` happily produces. Names that are not
  barewords are now quoted, and symbol positions accept a quoted string. Two adjacent defects
  fell out: `str/1` escaped `"` but not `\\`, so a name ending in a backslash produced an
  unterminated string; and the tokenizer reassembled accumulated BYTES with `to_string/1`,
  which reads a list of integers as codepoints and re-encoded every byte of a multi-byte
  character separately.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Env, Inductive, Kernel, Serialize, Term}

  describe "decode rejects a bare token where a full term belongs" do
    test "in constructor-argument position" do
      assert {:error, _} = Serialize.decode("(ctor Z 5)")
    end

    test "in application-function position" do
      assert {:error, _} = Serialize.decode("(app foo (int 5))")
    end

    test "at the top level" do
      assert {:error, _} = Serialize.decode("5")
      assert {:error, _} = Serialize.decode("foo")
      assert {:error, _} = Serialize.decode(~S("hi"))
    end
  end

  describe "decode rejects shapes Term.term?/1 rejects" do
    test "a universe level outside 0..Universe.ceiling()" do
      assert {:error, _} = Serialize.decode("(type 999)")
      assert {:error, _} = Serialize.decode("(type -1)")
    end

    test "a negative de Bruijn index" do
      assert {:error, _} = Serialize.decode("(var -1)")
    end

    test "negative compact nat / bounded literals" do
      assert {:error, _} = Serialize.decode("(nat -5)")
      assert {:error, _} = Serialize.decode("(bounded -5)")
    end

    test "a negative case-branch arity" do
      assert {:error, _} = Serialize.decode("(case (var 0) (type 0) (branch Z -3 (var 0)))")
    end

    test "the rejection names the ill-formed term rather than crashing" do
      assert {:error, {:ill_formed_term, {:var, -1}}} = Serialize.decode("(var -1)")
    end

    test "the well-formed neighbours of each rejected shape still decode" do
      # Guard against a validator that simply rejects everything.
      assert {:ok, {:type, 0}} = Serialize.decode("(type 0)")
      assert {:ok, {:var, 0}} = Serialize.decode("(var 0)")
      assert {:ok, {:nat_lit, 0}} = Serialize.decode("(nat 0)")
      assert {:ok, {:bounded_lit, 0}} = Serialize.decode("(bounded 0)")
      assert {:ok, {:int_lit, -5}} = Serialize.decode("(int -5)")
    end
  end

  describe "round-trip fidelity for names encode/1 can produce" do
    test "a symbol containing whitespace" do
      term = {:global, String.to_atom("has space")}
      assert {:ok, ^term} = Serialize.decode(Serialize.encode(term))
    end

    test "a symbol containing parens and a quote" do
      term = {:global, String.to_atom(~S{f(x)"y})}
      assert {:ok, ^term} = Serialize.decode(Serialize.encode(term))
    end

    test "a symbol that would otherwise tokenize as a number" do
      term = {:ctor, String.to_atom("5"), []}
      assert {:ok, ^term} = Serialize.decode(Serialize.encode(term))
    end

    test "a symbol ending in a backslash" do
      term = {:global, String.to_atom("back\\")}
      assert {:ok, ^term} = Serialize.decode(Serialize.encode(term))
    end

    test "a non-ASCII symbol survives byte-exact" do
      term = {:global, String.to_atom("café")}
      assert {:ok, ^term} = Serialize.decode(Serialize.encode(term))
    end

    test "a hole label containing a backslash and a quote" do
      term = {:hole, ~S{a\b"c}}
      assert {:ok, ^term} = Serialize.decode(Serialize.encode(term))
    end

    test "ordinary barewords are still emitted unquoted" do
      assert Serialize.encode({:global, :int_add}) == "(global int_add)"
    end

    test "a decoded term is always a Core term" do
      assert {:ok, t} = Serialize.decode("(app (app (global int_add) (int 3)) (int 5))")
      assert Term.term?(t)
    end
  end

  describe "the :conversion_failure diagnostic preserves an indexed family's params/indices split" do
    # `Quote.reify/3`'s `sig` argument exists so a `{:vdata, …}` value's family-declared
    # params/indices split survives read-back. `check_via_infer/3` built its diagnostic with the
    # 2-arity form, defaulting `sig` to nil — the exact case a sig-less reify is documented to
    # get wrong: the index merges into the flat `params` slot with `indices => []`. `Conv`
    # compares the flat form and does not care, but the diagnostic exists to be legible to a
    # human and rebuildable by an independent checker, and both need the real split. The
    # correct pattern was already one call away in `check_case/…`, which threads
    # `Context.signature(ctx)` through; the `ctx` carrying that signature was in scope here too.
    test "an indexed family reports one param and one index, not two flattened params" do
      env =
        Env.empty()
        |> Inductive.declare(
          Inductive.family(:Dec, [], [], 0),
          [Inductive.ctor(:Dcoupled, [], []), Inductive.ctor(:Causal, [], [])]
        )
        |> Inductive.declare(
          Inductive.family(:P, [{:a, {:type, 0}}], [{:n, {:data, :Dec, [], []}}], 1),
          [Inductive.ctor(:wrap, [{:p, {:var, 0}}], [{:ctor, :Causal, []}], [:unrestricted], [{:var, 1}])]
        )

      dec_val = {:vdata, :Dec, []}

      # `{:var, 0}` is neither a `:ctor` nor a `:bounded_lit` node, so `check/3` falls through
      # to the generic `check_via_infer/3` fallback — the call site under test.
      ctx = Context.extend(Context.empty(env), {:vdata, :P, [dec_val, {:vctor, :Causal, []}]})
      expected = {:vdata, :P, [dec_val, {:vctor, :Dcoupled, []}]}

      assert {:error, {:conversion_failure, inferred, expected_term}} =
               Kernel.check(ctx, {:var, 0}, expected)

      assert {:data, :P, [{:data, :Dec, [], []}], [{:ctor, :Causal, []}]} == inferred
      assert {:data, :P, [{:data, :Dec, [], []}], [{:ctor, :Dcoupled, []}]} == expected_term
    end
  end
end
