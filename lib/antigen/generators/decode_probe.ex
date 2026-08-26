defmodule Antigen.Generators.DecodeProbe do
  @moduledoc """
  Known-label generator for the `serialize/decode` robustness vertical
  (`Antigen.Assays.Serialization`, `:decode_probe` clause): raw S-expression
  strings fed straight to `Cure.Core.Serialize.decode/1`, which must be TOTAL —
  a well-formed term decodes to `{:ok, _}`; malformed input returns `{:error, _}`
  and never crashes or loops.

  This reaches `Serialize`'s decode EDGE/ERROR paths that the term-roundtrip
  vertical cannot: the leaf `build_node` clauses, the string tokenizer
  (`take_string` + `tokenize`'s `?"` clause), the `parse` / `build` error branches
  (`:unexpected_eof` / `:unexpected_rparen` / `:unterminated_list` / `:malformed`),
  and the `:ill_formed_term` gate that rejects a syntactically-valid s-expression
  whose *shape* violates a `Cure.Core.Term.term?/1` invariant. The challenge carries
  a raw string (no Core term), so `Coverage.terms_of/1` returns `[]` and the runner's
  well-formedness gate keeps it.
  """
  alias Antigen.{Gen, Challenge}

  @doc """
  Coverage-manifest cells (`Antigen.CoverManifest`): the two decode outcomes the
  probe asserts — a well-formed leaf/string that must decode `{:ok, _}` and a
  malformed input that must return `{:error, _}` (never crash/loop).
  """
  @spec cover_cells() :: [{String.t(), atom()}]
  def cover_cells do
    for cell <- [:valid_sexp, :invalid_sexp], do: {"serialize/decode", cell}
  end

  # Decode to {:ok, _}: every leaf node, wrapped as `enc/1` always emits it. Quoted strings
  # (with an escaped quote and an escaped backslash) reach `take_string`'s escape clauses; the
  # structured leaves `hole`/`absurd` are tuple terms, so the assay re-encodes them and reaches
  # `enc`'s hole/absurd clauses that the well_formed? gate keeps out of the roundtrip gen.
  @valid [
    "(int 5)",
    "(int -3)",
    "(int 0)",
    "(float 1.5)",
    "(float -2.0)",
    "(type 0)",
    "(var 0)",
    "(nat 0)",
    "(bounded 0)",
    "(global foo)",
    "(global Nat)",
    "(int-type)",
    "(hole \"h\")",
    "(hole \"a\\\"b\")",
    "(hole \"a\\\\b\")",
    "(absurd)"
  ]

  # Decode to {:error, _}: unbalanced / non-atom-headed / truncated S-expressions, trailing
  # tokens, an unterminated string, an unknown node head, and case/ctor bodies whose sub-terms
  # fail to build (build_all / build_branches error paths).
  #
  # Then the shape violations: a bare token standing where a full term belongs (`enc` never
  # emits one), and every literal whose sign `Term.term?/1` constrains but `build_node` reads
  # as a plain integer — a universe level outside `0..Universe.ceiling()`, a negative de Bruijn
  # index, a negative compact `nat`/`bounded` literal, a negative case-branch arity. Each of
  # these once rebuilt a term the kernel's own grammar rejects.
  @invalid [
    "",
    ")",
    "(",
    "(foo",
    "(5 6)",
    "(int",
    "( )",
    "((",
    "))",
    "5 6",
    "\"abc",
    "(zzz)",
    "(ctor Foo (zzz))",
    "(case (var 0) (var 0) foo)",
    "(case (var 0) (var 0) (branch Z 0 (zzz)))",
    "5",
    "foo",
    "\"hi\"",
    "(ctor Z 5)",
    "(app foo (int 5))",
    "(type -1)",
    "(type 999)",
    "(var -1)",
    "(nat -5)",
    "(bounded -5)",
    "(case (var 0) (type 0) (branch Z -3 (var 0)))"
  ]

  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.frequency([
      {2, probe(@valid, :valid_sexp)},
      {3, probe(@invalid, :invalid_sexp)}
    ])
  end

  defp probe(pool, label) do
    Gen.bind(Gen.member_of(pool), fn s ->
      Gen.return(
        Challenge.new(
          kind: :decode_probe,
          assay: "serialize/decode",
          label: label,
          cover_tag: label,
          payload: %{input: s},
          note: "decode probe (#{label})"
        )
      )
    end)
  end
end
