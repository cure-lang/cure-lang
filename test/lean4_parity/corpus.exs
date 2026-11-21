defmodule Cure.Lean4Parity.Corpus do
  @moduledoc """
  The Lean-4-parity corpus: the recorded baseline for
  `docs/PATH_TO_LEAN4_PLAN.md`.

  Every case here pins CURRENT behaviour. Read the `:expect` field as "what
  Cure does today", never as "what Cure should do". A `:reject` pin with a
  `:reason` naming a reach gap is a *measured* gap, and the plan's phases
  exist to flip those pins — one reviewed diff at a time.

  ## These pins are verified, not assumed

  Every `:accept` pin below was compiled through
  `Cure.Compiler.compile_and_load/2` before being recorded, and every `:reject`
  pin was observed to fail. Several of the first draft's pins were WRONG and
  were corrected against the tree:

    * `g4-bare-simplify-user-lemma` was pinned `:reject` on the belief that a
      bare `simplify` ignores user lemmas. It does NOT: `ProofGoal` applies the
      global `@lemma` set (`simplify_lemma_set/2`). The pin is now `:accept`.
    * `g9-universe-polymorphic-binder` was pinned `:reject` on the belief that
      `{l: UniverseLevel}` was unavailable. It parses and elaborates. The pin
      is now `:accept`, and the remaining G9 gap is narrower than claimed.
    * `g1-hole-is-checkable` was pinned `:accept`. A hole type-checks but is
      refused at CODEGEN (`unfilled_hole`), and this corpus compiles, so it is
      `:reject` — matching `docs/PROOFS.md` §3.7 ("only `cure compile` reports
      E014").

  Grouped by the gap register in `docs/LEAN4_PARITY_STATUS.md` §3.

  Gaps G6, G7, G8 and G11 are proof-side or runtime-side obligations with no
  Cure-source witness, so they have no entries here. They are tracked in
  `docs/LEAN4_PARITY_STATUS.md` instead. That absence is deliberate, and
  `test/lean4_parity_test.exs` asserts it.
  """

  alias Cure.Lean4Parity.Case

  import Case, only: [parity_case: 1]

  @doc """
  All parity cases, in gap order.
  """
  @spec all() :: [Case.t()]
  def all do
    g3() ++ g4() ++ g5() ++ g9() ++ g1() ++ g2() ++ g10()
  end

  @doc """
  Cases for one gap.
  """
  @spec for_gap(atom()) :: [Case.t()]
  def for_gap(gap), do: Enum.filter(all(), &(&1.gap == gap))

  @doc """
  Cases for one Lean-parity axis (`:l1` … `:l7`).
  """
  @spec for_axis(atom()) :: [Case.t()]
  def for_axis(axis), do: Enum.filter(all(), &(&1.axis == axis))

  # ---------------------------------------------------------------------------
  # G3 — delta-reach / definitional equality (axis L2)
  #
  # The sharpest day-to-day difference from Lean. Cure gates delta-unfolding
  # behind a totality certificate (docs/SOUNDNESS.md §3.2) and `simplify`
  # deliberately refuses to unfold recursive definitions (docs/PROOFS.md §3.4).
  # Both are SOUND; the cost is reach. These pins measure that cost.
  # ---------------------------------------------------------------------------

  defp g3 do
    [
      parity_case(
        id: "g3-reflexive-nonrecursive",
        gap: :g3,
        axis: :l2,
        title: "reflexive closes a goal whose endpoints are definitionally equal",
        expect: :accept,
        module: "Cure.Parity.G3ReflexiveNonrecursive",
        source: """
        mod Parity.G3ReflexiveNonrecursive
          use Std.Equivalent

          fn same(x: Int) -> Equivalent(Int, x, x) = reflexive(x)
        end
        """
      ),
      parity_case(
        id: "g3-reflexive-recursive-unfolding",
        gap: :g3,
        axis: :l2,
        title: "reflexive does NOT close a goal needing a recursive definition unfolded",
        expect: :reject,
        reason:
          "delta-unfolding is gated behind a totality certificate, and `reflexive` " <>
            "closes only definitionally-equal endpoints; `plus(n, Z())` does not " <>
            "reduce to `n` without induction. This is the Lean `rfl` reflex that " <>
            "fails here -- a reach gap, not a soundness gap.",
        source: """
        mod Parity.G3ReflexiveRecursiveUnfolding
          use Std.Equivalent

          type Nat = Z | S(Nat)

          fn plus(a: Nat, b: Nat) -> Nat = match a
            Z() -> b
            S(k) -> S(plus(k, b))

          fn wrong(n: Nat) -> Equivalent(Nat, plus(n, Z()), n) = reflexive(n)
        end
        """
      ),
      parity_case(
        id: "g3-induction-closes-recursive",
        gap: :g3,
        axis: :l2,
        title: "the same goal IS closable with explicit induction + simplify using [ih]",
        expect: :accept,
        module: "Cure.Parity.G3InductionClosesRecursive",
        source: """
        mod Parity.G3InductionClosesRecursive
          use Std.Equivalent

          type Nat = Z | S(Nat)

          fn plus(a: Nat, b: Nat) -> Nat = match a
            Z() -> b
            S(k) -> S(plus(k, b))

          fn plus_zero_right(n: Nat) -> Equivalent(Nat, plus(n, Z()), n) = induction n
            case Z => reflexive(Z())
            case S(k, ih) => proof chain
              plus(S(k), Z()) == S(k)
              because
                simplify using [ih]
        end
        """
      )
    ]
  end

  # ---------------------------------------------------------------------------
  # G4 — `@[simp]`-style lemma sets (axis L3/L6)
  #
  # CORRECTED: a bare `simplify` DOES consult the global `@lemma` set via
  # `ProofGoal.simplify_lemma_set/2`. What is missing is the `@[simp]`
  # ATTRIBUTE (explicit opt-in, priority ordering) and `simp?` diagnostics.
  # ---------------------------------------------------------------------------

  defp g4 do
    [
      parity_case(
        id: "g4-bare-simplify-reflexive",
        gap: :g4,
        axis: :l3,
        title: "bare simplify closes a goal needing only reflexivity",
        expect: :accept,
        module: "Cure.Parity.G4BareSimplifyReflexive",
        source: """
        mod Parity.G4BareSimplifyReflexive
          use Std.Equivalent

          fn applied(x: Int) -> Equivalent(Int, x, x) = proof chain
            x == x
            because
              simplify
        end
        """
      ),
      parity_case(
        id: "g4-bare-simplify-uses-lemma-set",
        gap: :g4,
        axis: :l3,
        title: "bare simplify DOES use the global @lemma set (no explicit rule list)",
        expect: :accept,
        module: "Cure.Parity.G4BareSimplifyUsesLemmaSet",
        source: """
        mod Parity.G4BareSimplifyUsesLemmaSet
          use Std.Equivalent

          type Nat = Z | S(Nat)

          fn plus(a: Nat, b: Nat) -> Nat = match a
            Z() -> b
            S(k) -> S(plus(k, b))

          @lemma
          fn plus_z(n: Nat) -> Equivalent(Nat, plus(Z(), n), n) = reflexive(n)

          fn uses_it(n: Nat) -> Equivalent(Nat, plus(Z(), n), n) = proof chain
            plus(Z(), n) == n
            because
              simplify
        end
        """
      )
    ]
  end

  # ---------------------------------------------------------------------------
  # G5 — automation exposed as tactics (axis L6)
  #
  # The libraries exist. What is missing is a tactic-level entry point. These
  # pins record that the LIBRARY works while the TACTIC does not, and that
  # `decide_is_true`'s dependent return type is itself a reach gap.
  # ---------------------------------------------------------------------------

  defp g5 do
    [
      parity_case(
        id: "g5-confirmed-evidence",
        gap: :g5,
        axis: :l6,
        title: "Std.Proof.IntMath evidence constructor inhabits IsTrue(True())",
        expect: :accept,
        module: "Cure.Parity.G5ConfirmedEvidence",
        source: """
        mod Parity.G5ConfirmedEvidence
          use Std.Proof.IntMath

          fn confirmed() -> IsTrue(True()) = Confirmed()
        end
        """
      ),
      parity_case(
        id: "g5-decide-dependent-return",
        gap: :g5,
        axis: :l6,
        title: "decide_is_true's dependent return type is a reach gap",
        expect: :reject,
        reason:
          "`decide_is_true(claim) -> Decision(IsTrue(claim))` has a return type " <>
            "depending on the argument; elaborating it at a concrete claim is a " <>
            "reach gap, so the decision procedure cannot yet be used as a tactic. " <>
            "The evidence constructor alone (see g5-confirmed-evidence) works.",
        source: """
        mod Parity.G5DecideDependentReturn
          use Std.Proof.IntMath

          fn decided() -> Decision(IsTrue(True())) = decide_is_true(True())
        end
        """
      )
    ]
  end

  # ---------------------------------------------------------------------------
  # G9 — universe polymorphism (axis L1)
  #
  # CORRECTED: `{l: UniverseLevel}` parses and elaborates. The remaining G9 gap
  # is the kernel's canonical level algebra (U1-U3), not the surface binder.
  # ---------------------------------------------------------------------------

  defp g9 do
    [
      parity_case(
        id: "g9-fixed-universe-type",
        gap: :g9,
        axis: :l1,
        title: "Type is usable at level zero (the current fixed ceiling's base)",
        expect: :accept,
        module: "Cure.Parity.G9FixedUniverseType",
        source: """
        mod Parity.G9FixedUniverseType
          fn identity({a: Type}, x: a) -> a = x
        end
        """
      ),
      parity_case(
        id: "g9-universe-level-binder",
        gap: :g9,
        axis: :l1,
        title: "an explicit UniverseLevel binder is accepted at the surface",
        expect: :accept,
        module: "Cure.Parity.G9UniverseLevelBinder",
        source: """
        mod Parity.G9UniverseLevelBinder
          fn identity({l: UniverseLevel}, {a: Type}, x: a) -> a = x
        end
        """
      )
    ]
  end

  # ---------------------------------------------------------------------------
  # G1 — goal-state introspection (axis L3)
  #
  # CORRECTED: a hole type-checks but is refused at CODEGEN. This corpus
  # compiles, so the pin is `:reject` -- matching docs/PROOFS.md §3.7.
  # ---------------------------------------------------------------------------

  defp g1 do
    [
      parity_case(
        id: "g1-hole-blocks-codegen",
        gap: :g1,
        axis: :l3,
        title: "a typed hole typechecks but blocks codegen (E014)",
        expect: :reject,
        reason:
          "`cure check` accepts a hole and reports its goal via `:hole_goal`; only " <>
            "compilation refuses it (`unfilled_hole`, E014). This corpus compiles, " <>
            "so the pin is :reject. What G1 still lacks is a per-step remaining-goal " <>
            "list inside a `because` block.",
        source: """
        mod Parity.G1HoleBlocksCodegen
          use Std.Equivalent

          fn later(x: Int) -> Equivalent(Int, x, x) = ?goal
        end
        """
      ),
      parity_case(
        id: "g1-open-because-block",
        gap: :g1,
        axis: :l3,
        title: "an open because block fails with E110 and does NOT list the open goal",
        expect: :reject,
        reason:
          "a justification block ending open raises PROOF JUSTIFICATION IS UNFINISHED " <>
            "[E110]; there is no per-step remaining-goal list. Phase 1 adds it.",
        source: """
        mod Parity.G1OpenBecauseBlock
          use Std.Equivalent

          type Nat = Z | S(Nat)

          fn plus(a: Nat, b: Nat) -> Nat = match a
            Z() -> b
            S(k) -> S(plus(k, b))

          fn wrong(n: Nat) -> Equivalent(Nat, plus(Z(), n), n) = proof chain
            plus(Z(), n) == n
            because
              rewrite using reflexive(plus(Z(), n))
        end
        """
      )
    ]
  end

  # ---------------------------------------------------------------------------
  # G2 — user-extensible tactics (axis L3/L4)
  #
  # `macro` is a real Lean.Elab analogue (`syntax ... computed by`), but its
  # member table has no `tactic` rule kind, so a library cannot define a proof
  # command.
  # ---------------------------------------------------------------------------

  defp g2 do
    [
      parity_case(
        id: "g2-syntax-macro-works",
        gap: :g2,
        axis: :l4,
        title: "a `syntax ... becomes` macro rule expands at a use site",
        expect: :accept,
        module: "Cure.Parity.G2SyntaxMacroWorks",
        source: """
        mod Parity.G2SyntaxMacroWorks
          macro Twice
            syntax twice <n: Code> becomes n + n
              example twice 21 expands 21 + 21

          fn start() -> Int = twice 21
        end
        """
      ),
      parity_case(
        id: "g2-tactic-rule-kind",
        gap: :g2,
        axis: :l4,
        title: "a `tactic` macro rule kind is NOT available (Phase 3 adds it)",
        expect: :reject,
        reason:
          "the macro container's member table (docs/MACROS.md §2) has no `tactic` " <>
            "entry, so a library cannot define a proof command. Phase 3 adds the " <>
            "rule kind, expanding to Cure.Elab.Tactic combinators (never Core terms).",
        source: """
        mod Parity.G2TacticRuleKind
          macro MyTactics
            tactic my_close becomes simplify

          fn start() -> Int = 1
        end
        """
      )
    ]
  end

  # ---------------------------------------------------------------------------
  # G10 — simp-set debugging (axis L3)
  # ---------------------------------------------------------------------------

  defp g10 do
    [
      parity_case(
        id: "g10-simplify-using-explicit-rules",
        gap: :g10,
        axis: :l3,
        title: "simplify using [rules] closes a goal with an explicit rule list",
        expect: :accept,
        module: "Cure.Parity.G10SimplifyUsingExplicitRules",
        source: """
        mod Parity.G10SimplifyUsingExplicitRules
          use Std.Equivalent

          type Nat = Z | S(Nat)

          fn plus(a: Nat, b: Nat) -> Nat = match a
            Z() -> b
            S(k) -> S(plus(k, b))

          fn plus_zero_right(n: Nat) -> Equivalent(Nat, plus(n, Z()), n) = induction n
            case Z => reflexive(Z())
            case S(k, ih) => proof chain
              plus(S(k), Z()) == S(k)
              because
                simplify using [ih]
        end
        """
      )
    ]
  end
end
