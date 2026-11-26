defmodule Cure.Elab.TacticMacroTest do
  @moduledoc """
  Phase 3 of `docs/PATH_TO_LEAN4_PLAN.md`: `tactic` macro rules (gap G2 / C1,
  part 2).

  The gate is that a **test library — not the stdlib** — defines a tactic macro
  and closes a real goal, with two negative controls:

    * a tactic whose expansion is a raw Core node is rejected;
    * an unexplained `fail` point is `E092`.

  Every acceptance assertion also re-checks the resulting definition through the
  kernel, so no test here can pass on an elaborator bug alone. The tactic adds
  no Core constructors and no kernel rules: it is a NAME for a composition of
  commands that already existed.
  """

  use ExUnit.Case, async: false

  alias Cure.Core.{Env, Kernel}
  alias Cure.Elab.Program

  defp elaborate!(source) do
    assert {:ok, env} = Program.elaborate(source)
    env
  end

  defp assert_certified!(env, name) do
    assert Env.certified?(env, name), "expected #{name} to be totality-certified"
    assert :ok = Kernel.check_def(env, Env.resolve_key(env, env.defs, name))
  end

  defp assert_rejected!(source, predicate) do
    assert {:error, reason} = Program.elaborate(source)
    assert predicate.(reason), "unexpected rejection shape: #{inspect(reason, limit: 12)}"
  end

  # ── The gate: a library tactic closes a real goal ────────────────────────

  describe "a library-defined tactic closes a goal" do
    test "a nullary tactic aliasing `simplify` closes a definitional goal" do
      env =
        elaborate!("""
        mod TacticLibrary
          macro Tactics
            tactic close becomes simplify

          fn id(n: Int) -> Int = n

          fn theorem(x: Int) -> Equivalent(Int, id(x), x) =
            proof chain
              id(x) == x
              because close
        end
        """)

      assert_certified!(env, :theorem)
    end

    test "a tactic with a hole forwards its argument to the command" do
      env =
        elaborate!("""
        mod TacticWithHole
          macro Tactics
            tactic finish <evidence: Code> becomes exact evidence

          fn refl_nat(x: Nat) -> Equivalent(Nat, x, x) = reflexive(x)

          fn theorem(x: Nat) -> Equivalent(Nat, x, x) =
            proof chain
              x == x
              because finish refl_nat(x)
        end
        """)

      assert_certified!(env, :theorem)
    end

    test "a tactic body may be a SEQUENCE of commands" do
      env =
        elaborate!("""
        mod TacticSequence
          macro Tactics
            tactic rewrite_then_close <evidence: Code> becomes
              rewrite using evidence all
              simplify

          type Pair = Pair(Int, Int)

          fn theorem(x: Int, y: Int, h: Equivalent(Int, x, y)) -> Equivalent(Pair, Pair(x, x), Pair(y, y)) =
            proof chain
              Pair(x, x) == Pair(y, y)
              because rewrite_then_close h
        end
        """)

      assert_certified!(env, :theorem)
    end

    test "a tactic composes a solver command" do
      env =
        elaborate!("""
        mod TacticSolver
          macro Tactics
            tactic settle becomes by decide

          use Std.Decision

          fn theorem() -> Equivalent(Bool, True(), True()) =
            proof chain
              True() == True()
              because settle
        end
        """)

      assert_certified!(env, :theorem)
    end

    test "a tactic works in an induction case body" do
      env =
        elaborate!("""
        mod TacticInInduction
          macro Tactics
            tactic close becomes simplify
            tactic close_using <e: Code> becomes simplify using [e]

          type Nat = Z | S(Nat)

          fn plus(a: Nat, b: Nat) -> Nat = match a
            Z() -> b
            S(k) -> S(plus(k, b))

          fn plus_zero_right(n: Nat) -> Equivalent(Nat, plus(n, Z()), n) = induction n
            case Z => reflexive(Z())
            case S(k, ih) => proof chain
              plus(S(k), Z()) == S(k)
              because
                close_using ih
        end
        """)

      assert_certified!(env, :plus_zero_right)
    end
  end

  # ── Negative control 1: a Core node is rejected ──────────────────────────

  describe "a tactic may not emit Core terms" do
    test "a tactic expanding to a bare expression is rejected" do
      # `reflexive(x)` is a proof TERM, not a command. A tactic that hands the
      # kernel a term directly would bypass the goal API, so the rule is refused
      # where it is written.
      assert_rejected!(
        """
        mod TacticEmitsTerm
          macro Tactics
            tactic cheat <x: Code> becomes reflexive(x)

          fn theorem(x: Int) -> Equivalent(Int, x, x) =
            proof chain
              x == x
              because cheat x
        end
        """,
        &match?({:source_context, {:invalid_tactic_expansion, "cheat", :not_a_step}, _}, &1)
      )
    end

    test "a tactic expanding to a lambda is rejected" do
      assert_rejected!(
        """
        mod TacticEmitsLambda
          macro Tactics
            tactic sneaky becomes fn(x) -> x

          fn theorem(x: Int) -> Equivalent(Int, x, x) =
            proof chain
              x == x
              because sneaky
        end
        """,
        &match?({:source_context, {:invalid_tactic_expansion, "sneaky", _}, _}, &1)
      )
    end

    test "a tactic expanding to a match is rejected" do
      assert_rejected!(
        """
        mod TacticEmitsMatch
          macro Tactics
            tactic branchy <x: Code> becomes match x
              _ -> x

          fn theorem(x: Int) -> Equivalent(Int, x, x) =
            proof chain
              x == x
              because branchy x
        end
        """,
        &match?({:source_context, {:invalid_tactic_expansion, "branchy", _}, _}, &1)
      )
    end

    test "a plain let is not admitted as a tactic command" do
      assert_rejected!(
        """
        mod TacticEmpty
          macro Tactics
            tactic nothing becomes
              let unused = 1

          fn theorem(x: Int) -> Equivalent(Int, x, x) =
            proof chain
              x == x
              because nothing
        end
        """,
        &match?({:source_context, {:invalid_tactic_expansion, "nothing", _}, _}, &1)
      )
    end
  end

  # ── Negative control 2: `explain` / `fail` obligations still apply ───────

  describe "tactic rules carry the self-proving obligations" do
    test "a tactic rule with an `explain` block must be pinned by an example" do
      assert_rejected!(
        """
        mod TacticUnpinned
          macro Tactics
            tactic close becomes simplify
            explain
              keyword "close" => "write `close` to finish with simplify"

          fn theorem(x: Int) -> Equivalent(Int, x, x) =
            proof chain
              x == x
              because close
        end
        """,
        &match?({:source_context, {:rule_unpinned, ["close"]}, _}, &1)
      )
    end

    test "an `explain` block that omits the tactic keyword is incomplete" do
      assert_rejected!(
        """
        mod TacticUnexplained
          macro Tactics
            tactic close becomes simplify
              example close expands simplify
            explain
              Code => "a proof"

          fn theorem(x: Int) -> Equivalent(Int, x, x) =
            proof chain
              x == x
              because close
        end
        """,
        &match?({:source_context, {:missing_diagnosis, [{:keyword, "close"}]}, _}, &1)
      )
    end

    test "a fully explained and pinned tactic rule is accepted" do
      env =
        elaborate!("""
        mod TacticExplained
          macro Tactics
            tactic close becomes simplify
              example close expands simplify
            explain
              keyword "close" => "write `close` to finish with simplify"

          fn id(n: Int) -> Int = n

          fn theorem(x: Int) -> Equivalent(Int, id(x), x) =
            proof chain
              id(x) == x
              because close
        end
        """)

      assert_certified!(env, :theorem)
    end
  end

  # ── Contextual vocabulary: the keyword is a NAME outside command position ──

  describe "a tactic keyword stays an ordinary identifier outside a proof" do
    test "a function may be named like the tactic" do
      # This is the regression class the Phase 0 findings recorded: a soft
      # keyword that claimed a position in which the word was a NAME broke a
      # real stdlib module. A library is free to name a function `close`.
      env =
        elaborate!("""
        mod TacticKeywordIsAName
          macro Tactics
            tactic close becomes simplify

          fn close(x: Int) -> Int = x

          fn use_it(x: Int) -> Int = close(x)
        end
        """)

      assert_certified!(env, :use_it)
    end
  end

  # ── A tactic that does not close the goal is reported, not accepted ──────

  describe "the refusal is a real diagnostic, not a crash" do
    test "a Core-term tactic renders as E092 with the rule blamed" do
      source = """
      mod TacticDiagnostic
        macro Tactics
          tactic cheat <x: Code> becomes reflexive(x)

        fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
          x == x
          because cheat x
      end
      """

      assert {:error, error} = Cure.Elab.Program.elaborate(source, file: "tactic_diag.cure")

      {diagnostic, registry} =
        Cure.Compiler.Errors.to_diagnostic(error, "tactic_diag.cure", source)

      assert diagnostic.code == "E092"
      assert diagnostic.title =~ "Tactic expansion"

      rendered = Cure.Diagnostic.Renderer.plain(diagnostic, registry, width: 80)
      assert rendered =~ "cheat"
      assert rendered =~ "E092"
    end
  end

  describe "a tactic that leaves the goal open" do
    test "reports the residual goal as an unfinished justification" do
      assert_rejected!(
        """
        mod TacticDoesNotClose
          macro Tactics
            tactic stuck <evidence: Code> becomes rewrite using evidence

          type Nat = Z | S(Nat)

          fn theorem(x: Nat, y: Nat, h: Equivalent(Nat, x, y)) -> Equivalent(Nat, x, y) =
            proof chain
              x == y
              because stuck h
        end
        """,
        &match?({:source_context, {:proof_chain_mismatch, %{kind: :unfinished_justification}}, _}, &1)
      )
    end
  end
end
