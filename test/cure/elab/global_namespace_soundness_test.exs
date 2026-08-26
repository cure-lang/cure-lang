defmodule Cure.Elab.GlobalNamespaceSoundnessTest do
  @moduledoc """
  Global / constructor / family name-collision behaviour, and the recorded decision
  about it (see memory `global-def-collision-gap`, audit K12 slice-4).

  Two distinct cases, deliberately treated differently:

  1. **Same-name globals WITHIN A MODULE overwrite (soundness) — REJECTED.** Two
     function definitions in one module sharing a name would silently overwrite one
     another in `env.defs`. `check_no_duplicate_defs` (program.ex) rejects this with
     `{:duplicate_definition, name}` — a landed soundness fix this session. (Two
     SIBLING modules sharing a name is legitimate namespacing and is accepted — see
     `Cure.Elab.CrossModuleNamesTest`.)

  2. **A function COEXISTING with a constructor / type of the same name — ACCEPTED,
     and DECLINED as a tightening (analysis discipline, faithfulness-without-
     soundness).** Constructors (`env.ctors`) and functions (`env.defs`) live in
     separate tables, so there is no overwrite; the fn simply shadows the ctor in
     expression position (Idris/Agda unify the value namespace and would reject the
     clash — a PARITY difference, not a soundness hole). The kernel remains sound
     against it: whatever the E-layer resolves the name to, the trusted Core
     re-checks the result, so a mis-resolution can only produce a *rejected* type
     mismatch, never an accepted ill-typed program. The discriminating test below is
     the recorded proof. A rejection rule here is entangled with the design-gated
     K12 qualified-`Sym` work and the LOCKED type-shadowing Approach B, and is
     flagged for operator design sign-off — so it is NOT landed unilaterally.
  """
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Errors, Lexer, Parser}
  alias Cure.Elab.Program

  defp check(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)

    case Program.check_ast(ast) do
      {:error, error} -> {:error, Program.semantic_error(error)}
      result -> result
    end
  end

  test "same-named globals within one module are rejected (no silent overwrite)" do
    src =
      "mod A\n  fn foo(x: Int) -> Int = x\n  fn foo(y: Int) -> Int = y\nend\n"

    assert {:error, {:overlapping_overload, %{name: :foo, arity: 1}}} = check(src)
  end

  test "a fn/ctor name collision within one module is rejected outright" do
    # `C` is both a constructor (: Foo) and a fn (() -> Int). Cure has no type-directed
    # constructor disambiguation, so whichever side `Resolution` favours, the other is
    # silently unreachable by name — a silent overwrite, not a choice. Reject it.
    #
    # This used to assert `{:conversion_failure, _, _}` on `wants(C())`, which passed for
    # the wrong reason: `type Foo = C` was mis-elaborated as an ALIAS to a nonexistent
    # family `C`, so `C` only ever named the function and the kernel caught Int-vs-Foo at
    # the call. Once `type Foo = C` correctly declares the constructor, `wants(C())`
    # resolves to it and is perfectly well-typed — nothing ill-typed was ever smuggled,
    # and nothing forced the collision to surface.
    src =
      "mod X\n  type Foo = C\n  fn C() -> Int = 3\n  fn wants(x: Foo) -> Int = 0\n  fn test() -> Int = wants(C())\nend\n"

    assert {:error, {:constructor_function_collision, :C}} = check(src)
  end

  # ---------------------------------------------------------------------------
  # Cross-module global-def collisions (design 2026-07-08).
  #
  # The gap this describe pins: `use A` + `use B` where both export a plain
  # global `helper/1` silently overwrites in `env.defs` (last-merge-wins). The
  # fixture points the dependent elaborator's ONLY import path
  # (`import_source_path/1`, which resolves "Std.<Name>" -> "<source_dir>/<name>.cure")
  # at a tmp source root. Canonical module discovery keeps the real stdlib as its
  # sole provider and adds only the two fixture modules from this root.
  # ---------------------------------------------------------------------------
  describe "cross-module global def collisions (design 2026-07-08)" do
    setup do
      tmp = Path.join(System.tmp_dir!(), "cure_global_coll_test_#{System.unique_integer([:positive])}")
      File.mkdir_p!(tmp)

      # `import_source_path/1` lowercases the module tail: Std.CollA -> colla.cure.
      # `dmeet` is a SECOND colliding name (also in collb.cure), a total, structural
      # (certifiable) function on `Dec`. The certificate-survival test below reaches
      # it QUALIFIED from the importing module's own GADT index, where a conversion
      # must δ-reduce it.
      File.write!(Path.join(tmp, "colla.cure"), """
      mod Std.CollA
        fn helper(x: Nat) -> Nat = Z()
        fn lonely_helper(x: Nat) -> Nat = Z()
        type Dec = DDec | DCau
        fn dmeet(a: Dec, b: Dec) -> Dec = match a
          DDec() -> match b
            DDec() -> DDec()
            DCau() -> DCau()
          DCau() -> DCau()
      end
      """)

      File.write!(Path.join(tmp, "collb.cure"), """
      mod Std.CollB
        fn helper(x: Nat) -> Nat = S(Z())
        fn dmeet(a: Nat, b: Nat) -> Nat = a
      end
      """)

      previous = Process.get(:cure_source_roots)
      Process.put(:cure_source_roots, [tmp])

      on_exit(fn ->
        if previous,
          do: Process.put(:cure_source_roots, previous),
          else: Process.delete(:cure_source_roots)

        File.rm_rf!(tmp)
      end)

      :ok
    end

    # In-memory importing modules (ordinary `check/1` sources — only the two
    # fixture files above live on disk). Each `helper` body is an OBSERVABLY
    # DISTINCT ctor shape (Z / S(Z) / S(S(Z))) so a wrong-but-well-typed
    # resolution is distinguishable from the right one.
    defp fixture_bare_call do
      "mod P\n  use Std.CollA\n  use Std.CollB\n  fn f() -> Nat = helper(Z())\nend\n"
    end

    defp fixture_bare_value do
      "mod P\n  use Std.CollA\n  use Std.CollB\n" <>
        "  fn ap(g: (Nat) -> Nat, x: Nat) -> Nat = g(x)\n" <>
        "  fn f() -> Nat = ap(helper, Z())\nend\n"
    end

    defp fixture_qualified_both do
      "mod P\n  use Std.CollA\n  use Std.CollB\n" <>
        "  fn fa() -> Nat = Std.CollA.helper(Z())\n" <>
        "  fn fb() -> Nat = Std.CollB.helper(Z())\nend\n"
    end

    defp fixture_local_shadow do
      "mod P\n  use Std.CollA\n  use Std.CollB\n" <>
        "  fn helper(x: Nat) -> Nat = S(S(Z()))\n" <>
        "  fn f() -> Nat = helper(Z())\nend\n"
    end

    defp fixture_no_collision do
      "mod P\n  use Std.CollA\n  fn f() -> Nat = lonely_helper(Z())\nend\n"
    end

    # `hsq(x, y) : H(dm(DDec, DDec))` must convert to `H(DDec)` for `hnd`. `dm` is a
    # local total wrapper whose body calls the colliding `dmeet` by its QUALIFIED name
    # `Std.CollA.dmeet` (bare `dmeet` is ambiguous — CollA + CollB — so qualified is the
    # only way to reach it). The conversion `dm(DDec, DDec) ≡ DDec` succeeds only if δ
    # can unfold through `dm` into the re-keyed `Std.CollA#dmeet` — i.e. that colliding
    # def is still certified total under its qualified key.
    defp fixture_certificate_survives do
      "mod P\n  use Std.CollA\n  use Std.CollB\n" <>
        "  fn dm(a: Dec, b: Dec) -> Dec = Std.CollA.dmeet(a, b)\n" <>
        "  type H indices (d: Dec)\n" <>
        "    hmk : H(DDec)\n" <>
        "    hsq : H(d1) -> H(d2) -> H(dm(d1, d2))\n" <>
        "    hnd : H(DDec) -> H(DCau)\n" <>
        "  fn f(x: H(DDec), y: H(DDec)) -> H(DCau) = hnd(hsq(x, y))\nend\n"
    end

    test "bare call of a doubly-imported name is an ambiguity error, not last-merge-wins" do
      # TODAY: silently binds the last-merged helper -> {:ok, _}
      # AFTER: an APPLIED bare call gathers both providers as an overload set and
      # prunes by argument type. Both `helper(x: Nat)` type-match the `Nat`
      # argument, so neither wins: {:ambiguous_overload, :helper, owners} with both
      # modules listed. (The un-applied VALUE reference below has no arguments to
      # prune, so it stays the pre-resolution {:ambiguous_name}.)
      assert {:error, {:ambiguous_overload, :helper, owners}} = check(fixture_bare_call())
      assert Enum.sort(owners) == ["Std.CollA", "Std.CollB"]
    end

    test "bare VALUE reference (higher-order arg) raises the same ambiguity error" do
      assert {:error, {:ambiguous_name, :helper, _}} = check(fixture_bare_value())
    end

    test "qualified calls reach their own module's body despite the collision" do
      # A wrong resolution (both qualified calls silently landing on the same
      # slice) is well-typed too, so inspect WHICH body each qualified key
      # resolved to, not just overall success.
      {:ok, env} = check(fixture_qualified_both())
      assert match?({:lam, _g, _, {:ctor, :"Std.Nat#Z", []}}, env.defs[:"Std.CollA#helper"].body)

      assert match?(
               {:lam, _g, _, {:ctor, :"Std.Nat#S", [{:ctor, :"Std.Nat#Z", []}]}},
               env.defs[:"Std.CollB#helper"].body
             )
    end

    test "local def shadows the imports; qualified still reaches them" do
      # Local helper(x) = S(S(Z())) -- a THIRD shape, so a bare call resolving to
      # the local body (correct) is distinguishable from either import's body.
      {:ok, env} = check(fixture_local_shadow())

      assert match?(
               {:lam, _g, _, {:ctor, :"Std.Nat#S", [{:ctor, :"Std.Nat#S", [{:ctor, :"Std.Nat#Z", []}]}]}},
               env.defs[:"P#helper"].body
             )

      assert match?({:lam, _g, _, {:ctor, :"Std.Nat#Z", []}}, env.defs[:"Std.CollA#helper"].body)

      assert match?(
               {:lam, _g, _, {:ctor, :"Std.Nat#S", [{:ctor, :"Std.Nat#Z", []}]}},
               env.defs[:"Std.CollB#helper"].body
             )
    end

    test "non-colliding imported defs retain their canonical owner identity" do
      {:ok, env} = check(fixture_no_collision())
      assert Map.has_key?(env.defs, :"Std.CollA#lonely_helper")

      refute Map.has_key?(env.defs, :lonely_helper)
    end

    test "a certified-total colliding def stays δ-reducible under its re-keyed qualified name" do
      # `dmeet` is certified total in CollA (type-level via G's index) and collides
      # with CollB's `dmeet`, so it is re-keyed to `Std.CollA#dmeet`. The importing
      # module's `need(seqg(x, y))` type-checks ONLY if that certificate survives the
      # re-key (δ must reduce `dmeet(DDec, DDec)` to `DDec`). Regression cover for
      # Task 2's `rekey_certified`: reverting the `certified:` field in
      # `rekey_module_env` makes this fail with a conversion error (verified).
      assert {:ok, _env} = check(fixture_certificate_survives())
    end

    test "E089 formatter names the code, both modules, and the qualified-form hint" do
      msg = Errors.format_error({:ambiguous_name, :helper, ["Std.CollA", "Std.CollB"]}, "x.cure")
      assert msg =~ "E089"
      assert msg =~ "Std.CollA"
      assert msg =~ "Std.CollB"
      assert msg =~ "Std.CollA.helper"
    end
  end
end
