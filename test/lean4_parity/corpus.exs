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
    * `g9-universe-level-binder` was then pinned `:accept` on the belief that
      "parses and elaborates" meant real level polymorphism. It does NOT: the
      parser records no universe kind, so `UniverseLevel`/`TypeN`/`TypeLimit`
      are ordinary type variables and a definition written at `Type37` is
      checked at `Type0`. The pin is `:reject` again — this time recording the
      defect rather than a missing feature. See
      `docs/LEAN4_PHASE5_U0_INVENTORY.md` §1.1.
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
    g3() ++
      g4() ++ g5() ++ g9() ++ g1() ++ g2() ++ g10() ++ phase_one_two() ++ phase_four()
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
        title: "right identity at a neutral argument requires induction, not unfolding",
        expect: :reject,
        reason:
          "`plus(n, Z())` cannot reduce with neutral n. This is a deliberate " <>
            "definitional-equality boundary shared with Lean, not a delta-reach gap.",
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
            "remaining library-call reach limitation for this particular reflector. " <>
            "Other Decision(P) procedures are usable through `by decide using`.",
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
  # CORRECTED TWICE. The first draft claimed `{l: UniverseLevel}` was
  # unavailable; it parses. The second draft then pinned it `:accept` on the
  # grounds that it "parses and elaborates" — that was WRONG in the other
  # direction. Measured against the tree (`docs/LEAN4_PHASE5_U0_INVENTORY.md`):
  # `parse_type_arrow_dispatch/2`'s simple-type arm routes every name through
  # `type_variable/1`, which records no universe kind. So `UniverseLevel`,
  # `Type37`, `TypeLimit` and `Type(0)` are all ORDINARY TYPE VARIABLES, and a
  # definition written at `Type37` is really checked at `Type0`.
  #
  # These pins now record that defect. They are `:reject` because the correct
  # behaviour is rejection (or real level polymorphism), not because the syntax
  # is unsupported. Flipping them to `:accept` is the U4 gate.
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
        title: "a UniverseLevel binder is misread as an ordinary type variable and ACCEPTED",
        expect: :accept,
        module: "Cure.Parity.G9UniverseLevelBinder",
        source: """
        mod Parity.G9UniverseLevelBinder
          fn identity({l: UniverseLevel}, {a: Type}, x: a) -> a = x
        end
        """
      ),
      parity_case(
        id: "g9-typen-misread-as-level-zero",
        gap: :g9,
        axis: :l1,
        title: "Type37 is an ordinary type variable, so an annotation at Type37 mismatches Type0",
        expect: :reject,
        reason:
          "MEASURED: `Type37` parses as a bare `{:variable, …, \"Type37\"}` with no level " <>
            "kind, so it elaborates to the unresolved global `{:global, :Type37}`. A definition " <>
            "written at `Type37` therefore does not inhabit `Type37` at all — the kernel reports " <>
            "`{:conversion_failure, {:type, 0}, {:global, :Type37}}`. The rejection is a " <>
            "CONSEQUENCE OF THE DEFECT, not the correct diagnosis: correct behaviour is that " <>
            "`Type37` is a real sort, so `Int : Type0` does NOT inhabit it and the definition " <>
            "is rejected for a level reason. Flipping this to :accept requires U4 to make " <>
            "`TypeN` a real sort. See docs/LEAN4_PHASE5_U0_INVENTORY.md §1.1.",
        source: """
        mod Parity.G9TypenMisread
          fn identity({a: Type37}, x: a) -> a = x
          fn use_it(n: Int) -> Int = identity(n)
        end
        """
      ),
      parity_case(
        id: "g9-typelimit-misread-as-variable",
        gap: :g9,
        axis: :l1,
        title: "TypeLimit is an ordinary type variable and ACCEPTED; no TypeLimit sort exists",
        expect: :accept,
        module: "Cure.Parity.G9TypeLimitMisread",
        source: """
        mod Parity.G9TypeLimitMisread
          fn identity({a: TypeLimit}, x: a) -> a = x
        end
        """
      ),
      parity_case(
        id: "g9-type-application-misread",
        gap: :g9,
        axis: :l1,
        title: "Type(0) in a binder position is an ordinary application and ACCEPTED",
        expect: :accept,
        module: "Cure.Parity.G9TypeApplicationMisread",
        source: """
        mod Parity.G9TypeApplicationMisread
          fn identity({a: Type(0)}, x: a) -> a = x
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
            "so the pin is :reject. This safety boundary is not a missing goal API.",
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
        title: "an open because block still fails with E110 (the diagnostic now names the goal)",
        expect: :reject,
        reason:
          "a justification block ending open raises PROOF JUSTIFICATION IS UNFINISHED " <>
            "[E110]. Goal inspection does not admit unfinished proofs.",
        source: """
        mod Parity.G1OpenBecauseBlock
          use Std.Equivalent

          type Nat = Z | S(Nat)

          fn plus(a: Nat, b: Nat) -> Nat = match a
            Z() -> b
            S(k) -> S(plus(k, b))

          fn wrong(n: Nat, m: Nat, equality: Equivalent(Nat, n, m)) -> Equivalent(Nat, n, m) = proof chain
            n == m
            because
              rewrite using equality
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
        title: "a `tactic` macro rule kind defines a new proof command (Phase 3)",
        expect: :accept,
        module: "Cure.Parity.G2TacticRuleKind",
        source: """
        mod Parity.G2TacticRuleKind
          macro Tactics
            tactic close becomes simplify

          fn id(n: Int) -> Int = n

          fn theorem(x: Int) -> Equivalent(Int, id(x), x) = proof chain
            id(x) == x
            because close
        end
        """
      ),
      parity_case(
        id: "g2-tactic-rule-refuses-false-goal",
        gap: :g2,
        axis: :l4,
        title: "a library tactic cannot close a false equality",
        expect: :reject,
        reason: "Template expansion must produce evidence checked at the original goal; 0 is not 1.",
        source: """
        mod Parity.G2TacticRuleFalseGoal
          macro Tactics
            tactic close becomes simplify
          fn wrong() -> Equivalent(Int, 0, 1) = proof chain
            0 == 1
            because close
        end
        """
      ),
      parity_case(
        id: "g2-tactic-rule-rejects-core-term",
        gap: :g2,
        axis: :l4,
        title: "a `tactic` rule expanding to a proof TERM (not a command) is rejected",
        expect: :reject,
        reason:
          "A tactic may only produce goals and apply existing steps. The expansion " <>
            "is checked against the closed tactic vocabulary, so a bare proof term " <>
            "is refused where the rule is written (E092) rather than bypassing the " <>
            "goal API. This is a deliberate safety boundary, not a reach gap.",
        source: """
        mod Parity.G2TacticRuleRejectsCoreTerm
          macro Tactics
            tactic cheat <x: Code> becomes reflexive(x)

          fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
            x == x
            because cheat x
        end
        """
      )
    ]
  end

  # ---------------------------------------------------------------------------
  # G10 — simp-set debugging (axis L3)
  # ---------------------------------------------------------------------------

  defp phase_one_two do
    [
      phase_case("CertifiedSimplify", :g3, :l2, """
      type Nat = Z | S(Nat)
      fn plus(left: Nat, right: Nat) -> Nat = match left
        Z() -> right
        S(previous) -> S(plus(previous, right))
      fn checked(n: Nat) -> Equivalent(Nat, plus(Z(), plus(Z(), n)), n) = proof chain
        plus(Z(), plus(Z(), n)) == n
        because simplify
      """),
      phase_case("QuantifiedSimp", :g4, :l3, """
      type Nat = Z | S(Nat)
      fn plus(left: Nat, right: Nat) -> Nat = match left
        Z() -> right
        S(previous) -> S(plus(previous, right))
      @simp
      fn plus_zero(n: Nat) -> Equivalent(Nat, plus(n, Z()), n) = induction n
        case Z => reflexive(Z())
        case S(previous, ih) => rewrite ih in reflexive(S(previous))
      fn checked(n: Nat) -> Equivalent(Nat, plus(plus(n, Z()), Z()), n) = proof chain
        plus(plus(n, Z()), Z()) == n
        because simplify
      """),
      phase_case(
        "LoopingSimp",
        :g4,
        :l3,
        """
        @simp
        fn loop(x: Int) -> Equivalent(Int, x, x) = reflexive(x)
        """,
        "Explicit simp rules must strictly decrease under substitution."
      ),
      phase_case("RewriteAll", :g2, :l3, """
      type Pair = Pair(Int, Int)
      fn checked(x: Int, y: Int, h: Equivalent(Int, x, y)) -> Equivalent(Pair, Pair(x, x), Pair(y, y)) = proof chain
        Pair(x, x) == Pair(y, y)
        because
          rewrite using h all
          simplify
      """),
      phase_case("Search", :g5, :l6, """
      use Std.Proof.Math
      fn checked(n: Nat, h: IsPositive(n)) -> IsPositive(n) = by search
      """),
      phase_case("Positivity", :g5, :l6, """
      use Std.Proof.Math
      fn checked(n: Nat, m: Nat, h: IsPositive(n)) -> IsPositive(plus(n, m)) = by positivity
      """),
      phase_case(
        "NotPositive",
        :g5,
        :l6,
        """
        use Std.Proof.Math
        fn wrong() -> IsPositive(Z()) = by positivity
        """,
        "Zero is not positive; automation must fail closed."
      ),
      phase_case("Decide", :g5, :l6, """
      use Std.Decision
      fn checked() -> Equivalent(Bool, True(), True()) = by decide
      """),
      phase_case(
        "DecisionNo",
        :g5,
        :l6,
        """
        use Std.Decision
        fn wrong() -> Equivalent(Bool, True(), False()) = by decide
        """,
        "No is disproof, not evidence of the requested proposition."
      )
    ]
  end

  defp phase_case(name, gap, axis, body, reason \\ nil) do
    parity_case(
      id: "#{gap}-phase12-#{Macro.underscore(name)}",
      gap: gap,
      axis: axis,
      title: "Phase 1/2 gate: #{name}",
      expect: if(reason, do: :reject, else: :accept),
      reason: reason,
      module: if(reason, do: nil, else: "Cure.Parity.#{name}"),
      source: "mod Parity.#{name}\n  " <> String.replace(String.trim(body), "\n", "\n  ") <> "\nend\n"
    )
  end

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

  # ---------------------------------------------------------------------------
  # Phase 4 — C1.2, C6, C7 (axis L3/L4)
  #
  # These pins are the review of the Phase 4 reach change. Each `:accept` was
  # observed to compile through the real pipeline before being recorded, and
  # each `:reject` was observed to fail. A `:reject` pin here is a deliberate
  # safety boundary, not an unfinished feature, unless its reason says so.
  # ---------------------------------------------------------------------------

  defp phase_four do
    [
      parity_case(
        id: "g2-computed-tactic-inspects-goal",
        gap: :g2,
        axis: :l4,
        title: "a library tactic inspects the goal through a computed expander (C1.2)",
        expect: :accept,
        module: "Cure.Parity.G2ComputedTacticInspectsGoal",
        source: """
        mod Parity.G2ComputedTacticInspectsGoal
          use Std.Tactic
          use Std.Equivalent
          use Std.Syntax
          use Std.Bool

          type Nat = Z | S(Nat)

          fn identity(value: Nat) -> Nat = value

          macro Tactics
            tactic close computed by close_goal

          fn close_goal(g: Goal) -> MacroResult = match is_equality(g)
            True() -> expand(Std.Tactic.simplify(g))
            False() -> reject_goal("only equalities")

          fn theorem(value: Nat) -> Equivalent(Nat, identity(value), value) = proof chain
            identity(value) == value
            because close
        end
        """
      ),
      parity_case(
        id: "g2-computed-tactic-refuses-false-goal",
        gap: :g2,
        axis: :l4,
        title: "a goal-inspecting tactic cannot close a false equality",
        expect: :reject,
        reason:
          "The expander returns requests, not evidence. `simplify` at the false goal " <>
            "fails, so the tactic fails. This is the C1.2 firewall: a computed tactic " <>
            "has exactly the power of the commands it names.",
        source: """
        mod Parity.G2ComputedTacticFalseGoal
          use Std.Tactic
          use Std.Equivalent
          use Std.Syntax
          use Std.Bool

          type Nat = Z | S(Nat)

          macro Tactics
            tactic close computed by close_goal

          fn close_goal(g: Goal) -> MacroResult = match is_equality(g)
            True() -> expand(Std.Tactic.simplify(g))
            False() -> reject_goal("only equalities")

          fn wrong() -> Equivalent(Nat, Z(), S(Z())) = proof chain
            Z() == S(Z())
            because close
        end
        """
      ),
      parity_case(
        id: "g2-computed-tactic-closed-vocabulary",
        gap: :g2,
        axis: :l4,
        title: "a computed tactic naming an unknown operation is refused",
        expect: :reject,
        reason:
          "`Tactic.Computed` validates every returned operation against a fixed " <>
            "table. An unknown name is a diagnostic, never a silent no-op, so the " <>
            "expander cannot invent a proof step.",
        source: """
        mod Parity.G2ComputedTacticClosedVocabulary
          use Std.Tactic
          use Std.Equivalent
          use Std.Syntax

          type Nat = Z | S(Nat)

          macro Tactics
            tactic cheat computed by cheat_goal

          fn cheat_goal(g: Goal) -> MacroResult =
            expand(operation(:prove_everything, g, []))

          fn wrong(value: Nat) -> Equivalent(Nat, value, value) = proof chain
            value == value
            because cheat
        end
        """
      ),
      parity_case(
        id: "g2-backward-apply-closes",
        gap: :g2,
        axis: :l3,
        title: "fully supplied `apply` preserves its checked closing behavior",
        expect: :accept,
        module: "Cure.Parity.G2BackwardApplyCloses",
        source: """
        mod Parity.G2BackwardApplyCloses
          use Std.Equivalent

          type Nat = Z | S(Nat)

          fn identity(value: Nat) -> Nat = value

          fn theorem(value: Nat) -> Equivalent(Nat, identity(value), value) = proof chain
            identity(value) == value
            because
              apply reflexive(identity(value))
        end
        """
      ),
      parity_case(
        id: "g2-backward-apply-mismatch",
        gap: :g2,
        axis: :l3,
        title: "closing `apply` that does not fit reports the residual goal",
        expect: :reject,
        reason:
          "`apply` elaborates the proof and checks it against the goal's expected " <>
            "type. A proof whose conclusion does not unify is E110 with the residual " <>
            "goal surfaced, never a silent success.",
        source: """
        mod Parity.G2BackwardApplyMismatch
          use Std.Equivalent

          type Nat = Z | S(Nat)

          fn wrong(value: Nat) -> Equivalent(Nat, S(value), value) = proof chain
            S(value) == value
            because
              apply reflexive(value)
        end
        """
      ),
      parity_case(
        id: "g2-backward-apply-premise-still-open",
        gap: :g2,
        axis: :l3,
        title: "backward apply generates a premise and reconstructs its checked parent",
        expect: :accept,
        module: "Cure.Parity.G2BackwardApplyPremise",
        source: """
        mod Parity.G2BackwardApplyPremise
          use Std.Equivalent
          fn need(x: Int, h: Equivalent(Int, x, x)) -> Equivalent(Int, x, x) = h
          fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
            x == x
            because
              apply need(x)
              reflexive(x)
        end
        """
      ),
      parity_case(
        id: "g2-backward-apply-unsolved-premise",
        gap: :g2,
        axis: :l3,
        title: "an unsolved application premise is not a closed proof",
        expect: :reject,
        reason: "Application creates a checked obligation, not invented evidence. An unfinished premise refuses E110.",
        source: """
        mod Parity.G2BackwardApplyUnsolved
          use Std.Equivalent
          fn need(x: Int, h: Equivalent(Int, x, x)) -> Equivalent(Int, x, x) = h
          fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
            x == x
            because apply need(x)
        end
        """
      ),
      parity_case(
        id: "g2-backward-apply-ordered-premises",
        gap: :g2,
        axis: :l3,
        title: "source commands close independent application premises in order",
        expect: :accept,
        module: "Cure.Parity.G2ApplyOrdered",
        source: """
        mod Parity.G2ApplyOrdered
          use Std.Equivalent
          fn theorem(
            x: Int, y: Int, z: Int,
            consume: (Equivalent(Int, x, y), Equivalent(Int, y, z)) -> Equivalent(Int, x, z),
            left: Equivalent(Int, x, y), right: Equivalent(Int, y, z)
          ) -> Equivalent(Int, x, z) = proof chain
            x == z
            because
              apply consume
              exact left
              exact right
        end
        """
      ),
      parity_case(
        id: "g2-backward-apply-dependent-witness",
        gap: :g2,
        axis: :l3,
        title: "an application premise is instantiated from its earlier explicit witness",
        expect: :accept,
        module: "Cure.Parity.G2ApplyDependent",
        source: """
        mod Parity.G2ApplyDependent
          use Std.Equivalent
          use Std.Nat
          fn need(x: Int, witness: Nat, evidence: Equivalent(Nat, witness, Z())) -> Equivalent(Int, x, x) =
            reflexive(x)
          fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
            x == x
            because
              apply need(x)
              exact Z()
              exact reflexive(Z())
        end
        """
      ),
      parity_case(
        id: "g2-induction-template-executes",
        gap: :g2,
        axis: :l4,
        title: "a genuine induction template uses a checked recursive hypothesis",
        expect: :accept,
        module: "Cure.Parity.G2InductionTemplate",
        source: """
        mod Parity.G2InductionTemplate
          use Std.Equivalent
          type Nat = Z | S(Nat)
          fn plus(left: Nat, right: Nat) -> Nat = match left
            Z() -> right
            S(k) -> S(plus(k, right))
          macro Tactics
            tactic induct <value: Code> becomes induction value
              case Z => simplify
              case S(previous, ih) => simplify using [ih]
          fn theorem(n: Nat) -> Equivalent(Nat, plus(n, Z()), n) = proof chain
            plus(n, Z()) == n
            because induct n
        end
        """
      ),
      parity_case(
        id: "g2-divergent-proof-evidence-refused",
        gap: :g2,
        axis: :l3,
        title: "uncertified divergence cannot discharge a false equality",
        expect: :reject,
        reason:
          "Completed proof-command declarations require ordinary kernel-backed totality certification; typing a self-call is not logical evidence.",
        source: """
        mod Parity.G2DivergentProof
          use Std.Equivalent
          use Std.Nat
          fn loop() -> Equivalent(Nat, Z(), S(Z())) = loop()
          fn theorem() -> Equivalent(Nat, Z(), S(Z())) = proof chain
            Z() == S(Z())
            because exact loop()
        end
        """
      ),
      parity_case(
        id: "g5-assumption-closes",
        gap: :g5,
        axis: :l6,
        title: "`by assumption` closes a goal that is a local hypothesis",
        expect: :accept,
        module: "Cure.Parity.G5AssumptionCloses",
        source: """
        mod Parity.G5AssumptionCloses
          use Std.Proof.Math

          fn theorem(value: Nat, h: IsPositive(value)) -> IsPositive(value) = by assumption
        end
        """
      ),
      parity_case(
        id: "g5-assumption-refuses",
        gap: :g5,
        axis: :l6,
        title: "`by assumption` refuses a goal that is not a local hypothesis",
        expect: :reject,
        reason:
          "`assumption` consults local hypotheses only -- no lemmas, no projections. " <>
            "A goal that is not one of them fails closed.",
        source: """
        mod Parity.G5AssumptionRefuses
          use Std.Proof.Math

          fn theorem(value: Nat) -> IsPositive(S(value)) = by assumption
        end
        """
      ),
      parity_case(
        id: "g5-assumption-value-type-refused",
        gap: :g5,
        axis: :l6,
        title: "`by assumption` does not inhabit a proof-relevant value type from a local",
        expect: :reject,
        reason:
          "`Nat` is proof-RELEVANT: a local `n: Nat` is a value, not a proof. " <>
            "`assumption` gates on `proposition?/3`, so it never silently chooses " <>
            "an inhabitant the author did not write.",
        source: """
        mod Parity.G5AssumptionValueType
          fn identity(n: Nat) -> Nat = by assumption
        end
        """
      ),
      parity_case(
        id: "g5-omega-linear",
        gap: :g5,
        axis: :l6,
        title: "`by omega` discharges a linear integer goal with a checked proof object",
        expect: :accept,
        module: "Cure.Parity.G5OmegaLinear",
        source: """
        mod Parity.G5OmegaLinear
          use Std.Proof.LinearArithmetic
          use Std.Proof.IntOrder

          fn theorem(a: Int, b: Int, c: Int, ab: IsLessThanOrEqual(a, b), bc: IsLessThanOrEqual(b, c)) -> IsLessThanOrEqual(a, c) =
            by omega
        end
        """
      ),
      parity_case(
        id: "g5-omega-outside-fragment",
        gap: :g5,
        axis: :l6,
        title: "`by omega` refuses a goal outside the linear fragment",
        expect: :reject,
        reason:
          "Natural-number sign goals are outside the stated integer-order reconstruction fragment. " <>
            "Neither a host witness nor a Boolean candidate verdict can substitute for checked goal evidence.",
        source: """
        mod Parity.G5OmegaOutsideFragment
          use Std.Proof.LinearArithmetic
          use Std.Proof.Math

          fn theorem(a: Nat, b: Nat) -> IsPositive(plus(a, b)) = by omega
        end
        """
      ),
      parity_case(
        id: "g5-omega-refuses-false-order",
        gap: :g5,
        axis: :l6,
        title: "omega refuses a false canonical integer-order goal",
        expect: :reject,
        reason: "Candidate validation and original-goal evidence checks cannot prove one is at most zero.",
        source: """
        mod Parity.G5OmegaFalseOrder
          use Std.Proof.LinearArithmetic
          use Std.Proof.IntOrder
          fn wrong() -> IsLessThanOrEqual(int_one(), int_zero()) = by omega
        end
        """
      ),
      parity_case(
        id: "g5-omega-strict-reconstruction-open",
        gap: :g5,
        axis: :l6,
        title: "a valid strict candidate without checked reconstruction is refused",
        expect: :reject,
        reason:
          "Zero is below one, but the current checked reconstruction subset handles only non-strict order. Full reflection remains open.",
        source: """
        mod Parity.G5OmegaStrictOpen
          use Std.Proof.LinearArithmetic
          use Std.Proof.IntOrder
          fn theorem() -> IsLessThan(int_zero(), int_one()) = by omega
        end
        """
      ),
      parity_case(
        id: "g10-simp-trace-closes",
        gap: :g10,
        axis: :l3,
        title: "`simp?` closes the same goal as `simplify` and reports the fired lemmas",
        expect: :accept,
        module: "Cure.Parity.G10SimpTraceCloses",
        source: """
        mod Parity.G10SimpTraceCloses
          use Std.Equivalent

          type Nat = Z | S(Nat)

          fn plus(left: Nat, right: Nat) -> Nat = match left
            Z() -> right
            S(previous) -> S(plus(previous, right))

          @simp
          fn plus_zero(value: Nat) -> Equivalent(Nat, plus(value, Z()), value) = induction value
            case Z => reflexive(Z())
            case S(previous, ih) => rewrite ih in reflexive(S(previous))

          fn reduced(value: Nat) -> Equivalent(Nat, plus(plus(value, Z()), Z()), value) = proof chain
            plus(plus(value, Z()), Z()) == value
            because simp?
        end
        """
      )
    ]
  end
end
