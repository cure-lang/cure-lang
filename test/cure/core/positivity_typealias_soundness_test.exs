defmodule Cure.Core.PositivityTypealiasSoundnessTest do
  @moduledoc """
  Regression: strict positivity must δ-unfold `{:global, name}` type synonyms
  before scanning a constructor field for occurrences of the family.

  `Inductive.positive?/2`'s walker `occurs?` used to enumerate a FIXED set of
  term shapes and fall to `defp occurs?(_fname, _term), do: false` for anything
  else — including `{:global, name}`. Since `strictly_positive?` reads `false` as
  "safe to admit", `typealias Neg = Bad -> Int` smuggled a negative occurrence
  straight past the check: `MkBad : Neg -> Bad` was accepted, the literal spelling
  `MkBad : (Bad -> Int) -> Bad` rejected. That is the `MkBad : (Bad -> Nat) -> Bad`
  paradox constructor KERNEL.md's "Strict positivity" section calls out — "out
  comes a well-typed infinite loop with no recursion written anywhere ... it
  'proves' False".

  Agda (`Positivity.hs`), Lean 4 (the `inductive` elaborator) and Idris 2
  (`Positivity.idr`) all run the positivity walk over the alias-EXPANDED type,
  precisely to close this path.

  The walker is now fail-CLOSED: its catch-all descends into any unrecognized
  tuple/list instead of answering "does not occur". Do not reintroduce a
  `_ -> false` catch-all here.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Env, Inductive}

  @bad {:data, :Bad, [], []}

  defp base do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Empty, [], [], 0), [])
  end

  # I1: strict positivity does not δ-unfold a `{:global, name}` reference
  # (a `typealias`/global type synonym) when scanning a constructor field
  # type for occurrences of the family being defined.
  #
  # `Inductive.positive?/2` delegates to the private `occurs?/2` walker
  # (inductive.ex, the `occurs?` clauses just above the bottom catch-all).
  # `occurs?/2` enumerates a FIXED set of term shapes — `:data` (both the
  # self-family and other-family arms), `:pi`, `:lam`, `:app`, `:ctor`,
  # `:case` — and for anything else (including `{:global, name}`) falls to
  #     defp occurs?(_fname, _term), do: false
  # `strictly_positive?/4`'s own bottom catch-all then reads that `false`
  # as "safe":
  #     defp strictly_positive?(_env, fname, other, _seen), do: not occurs?(fname, other)
  #
  # A `typealias Neg = Bad -> Int` compiles to a `def` entry in `Env.defs`
  # (`Cure.Elab.Declarations.resolve_index_name/2` — any bare identifier
  # that is not a family/ctor/primitive resolves to `{:global, atom}`, and
  # this same `idx_to_core` path is what builds a constructor's ARGUMENT
  # telescope, e.g. declarations.ex:730/860). So a constructor field written
  # as the bare alias name `Neg` is recorded in `Inductive.ctor.args` as the
  # UNEXPANDED term `{:global, :Neg}` — never substituted with the alias's
  # body before `Inductive.positive?` runs (kernel.ex:279 confirms aliases
  # reach the kernel as bare global neutrals, not pre-expanded literals).
  #
  # The result: `mk : Neg -> Bad` (i.e. `mk : (Bad -> Int) -> Bad` behind one
  # level of typealias indirection) is accepted as strictly positive, even
  # though the literal, unaliased spelling `mk : (Bad -> Int) -> Bad` is
  # correctly rejected by the very next test in this file's sibling
  # `positivity_test.exs` ("a constructor with the family in a negative
  # position is rejected"). This is the exact `MkBad : (Bad -> Nat) -> Bad`
  # paradox pattern the kernel's own doc (KERNEL.md "Strict positivity")
  # calls out — "a `Bad` built out of a function that consumes `Bad`s ...
  # out comes a well-typed infinite loop with no recursion written anywhere
  # ... it 'proves' False" — merely hidden behind a type synonym.
  #
  # Agda, Lean 4, and Idris 2 all normalize/unfold type synonyms (Agda's
  # `Positivity.hs` works over the elaborated, alias-expanded type; Lean's
  # `inductive` elaborator and Idris's `Positivity.idr` likewise see through
  # `abbrev`/`%hide`-free type aliases) before running the positivity walk,
  # precisely so this smuggling path is closed. Cure's own KERNEL.md /
  # inductive.ex module doc promises the same nested rule ("mirrors Agda's
  # Positivity.hs / Idris's Positivity.idr ... so smuggling a negative
  # occurrence through an intermediate wrapper datatype is also rejected")
  # but the promise only covers OTHER INDUCTIVE FAMILIES (the `:data`-other
  # clause), not bare global/typealias references.
  test "I1: a negative occurrence hidden behind an unexpanded typealias (`{:global, name}`) field must be rejected, not silently accepted" do
    env =
      base()
      |> Env.add_def(:Neg, {:type, 0}, {:pi, Cure.Core.Grade.unrestricted(), @bad, {:int_type}})
      |> Inductive.declare(Inductive.family(:Bad, [], [], 0), [
        Inductive.ctor(:mk, [{:f, {:global, :Neg}}], [])
      ])
      # Control, declared alongside :Bad in the SAME env: the identical
      # negative occurrence, spelled out literally instead of through the
      # alias, IS correctly rejected today (mirrors
      # positivity_test.exs "a constructor with the family in a negative
      # position is rejected"). The field must mention :BadLiteral ITSELF —
      # positivity of a family is about occurrences of THAT family, so
      # spelling the domain as `@bad` here would make the control vacuous
      # (:BadLiteral never occurs in it) and `:ok` would be the CORRECT answer.
      |> Inductive.declare(Inductive.family(:BadLiteral, [], [], 0), [
        Inductive.ctor(
          :mk_literal,
          [{:f, {:pi, Cure.Core.Grade.unrestricted(), {:data, :BadLiteral, [], []}, {:int_type}}}],
          []
        )
      ])

    assert {:error, {:non_strictly_positive, :mk_literal}} ==
             Inductive.positive?(env, Inductive.get_family(env, :BadLiteral))

    # The aliased spelling of the SAME type must be rejected identically —
    # positivity is a property of the (fully-expanded) type, not of its surface
    # spelling. Before the fix `positive?` returned `:ok` for `:Bad`, because
    # `occurs?({:global, :Neg})` silently answered "does not occur".
    assert {:error, {:non_strictly_positive, :mk}} ==
             Inductive.positive?(env, Inductive.get_family(env, :Bad))
  end

  # I2: the same missing `{:global, name}` case also breaks the arrow-DOMAIN
  # scan specifically (`occurs_deep?/4`), independent of I1's catch-all path.
  #
  # `strictly_positive?(env, fname, {:pi, Cure.Core.Grade.unrestricted(), dom, cod}, seen)` guards the domain
  # via `occurs_deep?(env, fname, dom, seen)`, whose own definition is
  # `occurs?(fname, ty) or Enum.any?(data_heads(ty), ...)`. Both halves miss
  # a `{:global, name}` domain:
  #   * `occurs?/2` has no `:global` clause (same gap as I1).
  #   * `data_heads/1` (via `gather_data_heads/2`) also never resolves a
  #     `{:global, name}` to the family it aliases — `gather_data_heads`
  #     only special-cases `{:data, n, ps, is}` and otherwise walks the raw
  #     tuple/list structure, so `{:global, :NegDom}` yields the atom
  #     `:NegDom`, not a `:data` head worth exploring.
  #
  # So a field type `NegDom -> Int` (a Π whose DOMAIN is the alias) where
  # `typealias NegDom = Bad` is a direct negative occurrence of `Bad`
  # wrapped in exactly one indirection — the domain, after δ, IS `Bad`
  # itself — yet `occurs_deep?` reports "does not occur in the domain" and
  # the Π is admitted as strictly positive. This exercises a different
  # function (`occurs_deep?`, reached only from the `:pi` clause) than I1
  # (which exercises the bottom catch-all reached from a field whose whole
  # type, not just an arrow domain, is an alias), so a fix to one code path
  # does not necessarily fix the other unless the shared root cause
  # (`occurs?/2`'s incomplete term-shape enumeration) is what gets fixed.
  test "I2: a negative occurrence hidden behind a typealias used as an arrow DOMAIN must be rejected" do
    env =
      base()
      |> Env.add_def(:NegDom, {:type, 0}, @bad)
      |> Inductive.declare(Inductive.family(:Bad, [], [], 0), [
        Inductive.ctor(:mk, [{:f, {:pi, Cure.Core.Grade.unrestricted(), {:global, :NegDom}, {:int_type}}}], [])
      ])

    assert {:error, {:non_strictly_positive, :mk}} ==
             Inductive.positive?(env, Inductive.get_family(env, :Bad))
  end

  test "an unrelated recursive global does not invent an occurrence of the family under review" do
    env =
      base()
      |> Env.add_def(:Loop, {:type, 0}, {:global, :Loop})
      |> Inductive.declare(Inductive.family(:Fresh, [], [], 0), [
        Inductive.ctor(:mk_fresh, [{:field, {:global, :Loop}}], [])
      ])

    assert :ok == Inductive.positive?(env, Inductive.get_family(env, :Fresh))
  end
end
