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
end
