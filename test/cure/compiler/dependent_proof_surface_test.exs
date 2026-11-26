defmodule Cure.Compiler.DependentProofSurfaceTest do
  use ExUnit.Case, async: false

  test "surface Equivalent and reflexive elaborate through the dependent compiler" do
    src = """
    mod ProofReflOnly
      type Nat = Z | S(Nat)
      fn zero_refl() -> Equivalent(Nat, Z, Z) = reflexive(Z)
    end
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert mod == :"Cure.ProofReflOnly"
    # `reflexive` is now a genuine inductive constructor with an ERASED witness, so
    # it lowers to the canonical nullary ctor tag `:reflexive` (retiring the
    # faking-era `:cure_refl` sentinel — spec 2026-07-04-identity-type-as-inductive).
    assert apply(mod, :zero_refl, []) == :reflexive
  end

  test "surface rewrite proves plus right identity for Nat" do
    src = """
    mod ProofPlusZero
      type Nat = Z | S(Nat)
      fn plus(m: Nat, n: Nat) -> Nat = match m
        Z() -> n
        S(k) -> S(plus(k, n))
      fn plus_zero_right(n: Nat) -> Equivalent(Nat, plus(n, Z), n) = match n
        Z() -> reflexive(Z)
        S(k) -> rewrite plus_zero_right(k) in reflexive(S(k))
    end
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert mod == :"Cure.ProofPlusZero"
    # Both branches reduce to the erased inductive `reflexive` ctor tag (see above).
    assert apply(mod, :plus_zero_right, [:Z]) == :reflexive
    assert apply(mod, :plus_zero_right, [{:S, :Z}]) == :reflexive
  end

  test "reflexive is rejected when equality endpoints are not definitionally equal" do
    src = """
    mod ProofBadRefl
      type Nat = Z | S(Nat)
      fn bad() -> Equivalent(Nat, Z, S(Z)) = reflexive(Z)
    end
    """

    # `reflexive(Z)` proves `Equivalent(Nat, Z, Z)`, which the kernel's
    # conversion check refuses to unify with the declared goal
    # `Equivalent(Nat, Z, S(Z))`. The sole (dependent) pipeline surfaces that as
    # a `conversion_failure` rather than the classic `dependent_type_error`.
    assert {:error, error} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert {:codegen_error, {:conversion_failure, _lhs, _rhs}} = Cure.Elab.Program.semantic_error(error)
  end

  test "rewrite … in parses with `in` on the next line (multi-line chain)" do
    # A `rewrite … in …` chain may place `in` at the start of the next line at the
    # same indentation. `rewrite` always requires `in`, so the parser skips the
    # intervening newline to find it (regression: previously `:expected :in got :newline`).
    src = """
    mod ProofRewriteMultiline
      type Nat = Z | S(Nat)
      fn plus(m: Nat, n: Nat) -> Nat = match m
        Z() -> n
        S(k) -> S(plus(k, n))
      fn plus_zero_right(n: Nat) -> Equivalent(Nat, plus(n, Z), n) = match n
        Z() -> reflexive(Z)
        S(k) ->
          rewrite plus_zero_right(k)
          in reflexive(S(k))
    end
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert apply(mod, :plus_zero_right, [{:S, {:S, :Z}}]) == :reflexive
  end

  test "rewrite … in parses (and proves) with the BODY on the next line" do
    # Symmetric to the previous test: the body after `in` may start on the next line. The parser
    # must skip the newline AFTER `in` before reading the body (regression: `:unexpected_token :newline`).
    src = """
    mod ProofRewriteBodyMultiline
      type Nat = Z | S(Nat)
      fn plus(m: Nat, n: Nat) -> Nat = match m
        Z() -> n
        S(k) -> S(plus(k, n))
      fn plus_zero_right(n: Nat) -> Equivalent(Nat, plus(n, Z), n) = match n
        Z() -> reflexive(Z)
        S(k) ->
          rewrite plus_zero_right(k) in
          reflexive(S(k))
    end
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert apply(mod, :plus_zero_right, [{:S, {:S, :Z}}]) == :reflexive
  end

  test "a multi-line rewrite CHAIN parses (body of each `in` on the next line)" do
    # A `rewrite … in / rewrite … in / body` chain spanning several lines must parse — each `in`
    # skips the following newline before the next form. Parse-level check (the grammar is what is
    # under test; the proof's soundness is covered by the oracle probe `mailbox_exhaustive`).
    src = """
    mod ProofRewriteChain
      use Std.Equivalent
      type Nat = Z | S(Nat)
      fn plus(m: Nat, n: Nat) -> Nat = match m
        Z() -> n
        S(k) -> S(plus(k, n))
      fn chain(n: Nat, e: Equivalent(Nat, plus(n, Z), n)) -> Equivalent(Nat, plus(n, Z), n) =
        rewrite e in
        rewrite e in
        reflexive(n)
    end
    """

    assert {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
    assert {:ok, _ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)
  end

  # `exact` and `apply` are CONTEXTUAL proof commands: they claim their keyword
  # only when a proof expression actually follows. Two following tokens mean the
  # word is a NAME, not the command, and both were regressions when the commands
  # were introduced -- each broke a real stdlib module.

  test "`exact` as a bound match variable does not claim the proof keyword" do
    # `IsSingleCharacter(_, _, exact) -> match exact` binds `exact` and then
    # matches on it. Claiming `exact` as a proof command consumed the `->` as
    # the start of a proof expression and derailed the arm, breaking
    # `lib/std_deps/regex/regex_language.cure` with E094
    # `closing_delimiter_has_no_opener`.
    src = """
    mod ProofExactAsVariable
      use Std.Equivalent

      type SingleCharacter = MkSingleCharacter(Nat)

      fn unwrap(value: SingleCharacter) -> Nat = match value
        MkSingleCharacter(exact) -> match exact
          reflexive() -> Z()
    end
    """

    assert {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
    assert {:ok, _ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)
  end

  test "`exact` as a proof name before legacy-rewrite `in` does not claim the keyword" do
    # `rewrite exact in body` uses `exact` as the PROOF NAME and `in` as the
    # separator. Claiming `exact` swallowed `in` as its argument and left the
    # rewrite without a separator, breaking
    # `lib/std_deps/regex/regex_proof.cure` with E094 `rewrite_in_missing`.
    src = """
    mod ProofExactBeforeIn
      use Std.Equivalent
      type Nat = Z | S(Nat)
      fn plus(m: Nat, n: Nat) -> Nat = match m
        Z() -> n
        S(k) -> S(plus(k, n))
      fn id_rewrite(n: Nat, exact: Equivalent(Nat, plus(n, Z), n)) -> Equivalent(Nat, plus(n, Z), n) =
        rewrite exact in reflexive(n)
    end
    """

    assert {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
    assert {:ok, _ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)
  end

  test "`exact` with a real proof expression still claims the proof keyword" do
    # The contextual guard must not disable the command itself.
    src = """
    mod ProofExactCommand
      use Std.Equivalent
      type Nat = Z | S(Nat)
      fn plus(m: Nat, n: Nat) -> Nat = match m
        Z() -> n
        S(k) -> S(plus(k, n))
      fn plus_zero_right(n: Nat) -> Equivalent(Nat, plus(n, Z), n) = induction n
        case Z => exact reflexive(Z())
        case S(k, ih) => proof chain
          plus(S(k), Z()) == S(k)
          because
            simplify using [ih]
    end
    """

    assert {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
    assert {:ok, _ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)
  end

  # -- `apply` is BOTH a proof command and a public stdlib function -----------
  #
  # `lib/std/core.cure:68` defines `fn apply(f, x)`. No lookahead can separate
  # `apply(f, x)` from `apply some_proof`, so the parser carries an explicit
  # `proof_context` flag that is true only inside a `because` block. These tests
  # pin both directions.

  test "`apply` outside a justification block is the ordinary stdlib function" do
    src = """
    mod ProofApplyAsFunction
      use Std.Core

      fn twice(f: Int -> Int, x: Int) -> Int = apply(f, apply(f, x))
    end
    """

    assert {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
    assert {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)

    # It must parse as a CALL, never as a `proof_application` command.
    refute contains_tag?(ast, :proof_application),
           "`apply(f, x)` outside a proof block must not become a proof command"
  end

  test "`apply` inside a justification block is the proof command" do
    src = """
    mod ProofApplyAsCommand
      use Std.Equivalent
      type Nat = Z | S(Nat)
      fn plus(m: Nat, n: Nat) -> Nat = match m
        Z() -> n
        S(k) -> S(plus(k, n))
      fn plus_zero_right(n: Nat) -> Equivalent(Nat, plus(n, Z), n) = induction n
        case Z => reflexive(Z())
        case S(k, ih) => proof chain
          plus(S(k), Z()) == S(k)
          because
            apply ih
    end
    """

    assert {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
    assert {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)

    assert contains_tag?(ast, :proof_application),
           "`apply ih` inside a `because` block must become a proof command"
  end

  # -- A `tactic` macro rule's keyword is contextual, exactly like `apply` ----
  #
  # Phase 3 adds a `tactic` member to the macro container. Its keyword names a
  # proof command ONLY in command position; everywhere else it is an ordinary
  # identifier. Pin both directions, because the failure mode here (a soft
  # keyword claiming a position in which the word is a name) is the same one
  # that broke two stdlib modules when `apply`/`exact` were introduced.

  test "a tactic keyword outside a proof block is an ordinary identifier" do
    src = """
    mod TacticKeywordAsFunction
      macro Tactics
        tactic close becomes simplify

      fn close(x: Int) -> Int = x
      fn use_it(x: Int) -> Int = close(x)
    end
    """

    assert {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
    assert {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)

    refute contains_tag?(ast, :tactic_script),
           "`close(x)` outside a proof block must not become a tactic use"
  end

  test "a tactic keyword inside a justification block is a tactic use" do
    src = """
    mod TacticKeywordAsCommand
      macro Tactics
        tactic close becomes simplify

      fn id(n: Int) -> Int = n

      fn theorem(x: Int) -> Equivalent(Int, id(x), x) = proof chain
        id(x) == x
        because close
    end
    """

    assert {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
    assert {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)

    assert contains_tag?(ast, :tactic_script),
           "`close` inside a `because` block must become a tactic use"
  end

  # Walk the MetaAST 3-tuple tree looking for a node tag.
  defp contains_tag?({tag, _meta, _children}, tag), do: true

  defp contains_tag?({_tag, _meta, children}, tag) when is_list(children),
    do: Enum.any?(children, &contains_tag?(&1, tag))

  defp contains_tag?({_tag, _meta, _leaf}, _wanted), do: false

  defp contains_tag?(list, tag) when is_list(list),
    do: Enum.any?(list, &contains_tag?(&1, tag))

  defp contains_tag?(_other, _wanted), do: false
end
