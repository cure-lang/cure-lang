defmodule Cure.Elab.TypeShadowingTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.Program

  defp elaborate(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    Program.check_ast(ast)
  end

  test "R1a: explicit `use Std.Nat` + local `Nat = Zero|Suc` — local ctors cover the match" do
    src = """
    mod ExplicitShadow
      use Std.Nat
      type Nat = Zero | Suc(Nat)
      fn add(a: Nat, b: Nat) -> Nat = match a
        Zero() -> b
        Suc(m) -> Suc(add(m, b))
    end
    """

    assert {:ok, _env} = elaborate(src)
  end

  test "R1 full: local `Nat = Z|S` fully shadows same-named imported ctors" do
    src = """
    mod FullShadow
      use Std.Nat
      type Nat = Z | S(Nat)
      fn two() -> Nat = S(S(Z()))
      fn pred(n: Nat) -> Nat = match n
        Z() -> Z()
        S(m) -> m
    end
    """

    assert {:ok, _env} = elaborate(src)
  end

  # R2 local half — the `imported_one`/`Std.Nat`-return half is restored in Task 8
  # (it needs qualified type-slot resolution).
  test "R2 (local half): local Zero/Suc still elaborate under `use Std.Nat`" do
    src = """
    mod PartialShadow
      use Std.Nat
      type Nat = Zero | Suc(Nat)
      fn local_one() -> Nat = Suc(Zero())
    end
    """

    assert {:ok, _env} = elaborate(src)
  end

  test "R1 via transitive import: local `Nat` collides with a family reached only through `use Std.Vector` (no explicit `use Std.Nat`)" do
    src = """
    mod TransitiveShadow
      use Std.Vector
      type Nat = Zero | Suc(Nat)
      fn two() -> Nat = Suc(Suc(Zero()))
      fn pred(n: Nat) -> Nat = match n
        Zero() -> Zero()
        Suc(m) -> m
    end
    """

    assert {:ok, _env} = elaborate(src)
  end

  # Task 7 (value + pattern positions), isolated from the qualified TYPE slot
  # (Task 8): no local shadow, so `Nat`/`Std.Nat.Z`/`Std.Nat.S` resolve to the
  # imported family, exercising `elaborate_named_call` (expr) and `partition_arms`
  # (pattern) qualified-ctor resolution via bare-fallback. Full R3 (with `Std.Nat`
  # type slots + a local shadow) is added in Task 8.
  test "R3 (isolated): qualified ctor resolves in expression and pattern position" do
    src = """
    mod IsolatedEscape
      use Std.Nat
      fn two() -> Nat = Std.Nat.S(Std.Nat.Z())
      fn is_zero(n: Nat) -> Nat = match n
        Std.Nat.Z() -> Std.Nat.Z()
        Std.Nat.S(k) -> Std.Nat.S(Std.Nat.Z())
    end
    """

    assert {:ok, _env} = elaborate(src)
  end

  test "R2 full: unshadowed imported ctors Z/S resolve bare via uniform shadowed resolution" do
    src = """
    mod PartialShadowFull
      use Std.Nat
      type Nat = Zero | Suc(Nat)
      fn imported_one() -> Std.Nat = S(Z())
      fn local_one() -> Nat = Suc(Zero())
    end
    """

    assert {:ok, _env} = elaborate(src)
  end

  test "R2 pattern: bare Z/S patterns on an imported Std.Nat scrutinee under a local Nat shadow" do
    src = """
    mod BarePatternImported
      use Std.Nat
      type Nat = Zero | Suc(Nat)
      fn is_zero(n: Std.Nat) -> Nat = match n
        Z() -> Zero()
        S(k) -> Suc(Zero())
    end
    """

    assert {:ok, _env} = elaborate(src)
  end

  test "R3: shadowed ctor reachable qualified in expression and pattern position" do
    src = """
    mod EscapeHatch
      use Std.Nat
      type Nat = Zero | Suc(Nat)
      fn imported_two() -> Std.Nat = Std.Nat.S(Std.Nat.Z())
      fn is_zero(n: Std.Nat) -> Nat = match n
        Std.Nat.Z() -> Zero()
        Std.Nat.S(k) -> Suc(Zero())
    end
    """

    assert {:ok, _env} = elaborate(src)
  end

  test "R5: using a shadowed bare ctor on the local family yields a targeted :shadowed_ctor error" do
    src = """
    mod WrongCtor
      use Std.Nat
      type Nat = Zero | Suc(Nat)
      fn bad(n: Nat) -> Nat = match n
        Z() -> Zero()
        S(m) -> Suc(m)
    end
    """

    assert {:error, {:source_context, {:shadowed_ctor, info}, _} = reason} = elaborate(src)
    assert info[:ctor] == :Z
    assert info[:shadowed_module] == "Std.Nat"
    assert info[:hint] == "Std.Nat.Z"
    assert info[:local_family] == :"WrongCtor#Nat"

    # The reason must reach the author as a diagnostic. It had no registered
    # conversion at all, so every module that tripped R5 got an
    # `UnhandledError` crash out of the adapter instead of the message above.
    {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(reason, "wrong_ctor.cure", src)
    rendered = Cure.Diagnostic.Renderer.plain(diagnostic, registry, width: 80)

    assert rendered =~ "`Z` IS SHADOWED BY THIS MODULE'S OWN `NAT` [E091]"
    assert rendered =~ "`Z` is a constructor of `Std.Nat`'s `Nat`, but this module declares its own"
    assert rendered =~ "The local `Nat` provides `Zero`, `Suc`."
    assert rendered =~ "Write `Std.Nat.Z` to name `Std.Nat`'s constructor explicitly"
    assert rendered =~ "Or match a constructor of the local `Nat`: `Zero`, `Suc`"
  end

  # `:shadowed_ctor` says something specific: the local module declared a type
  # whose name shadows the imported one, so the imported family's constructors
  # can no longer be reached by their bare spelling — write `Std.Nat.Z` instead.
  # The classifier asked a much weaker question: does this bare ctor resolve
  # through an import rather than locally? That is true of EVERY imported
  # constructor, so an ordinary wrong-family pattern was reported as shadowing
  # and hinted at a qualified spelling that does not type-check either.
  #
  # The concrete case that surfaced it: `match input` on a `String` with a cons
  # pattern. `String` is a nominal record now, not a `List(Char)` alias, so
  # `Cons` is simply foreign to it — nothing about `List` is shadowed, and
  # "write `Std.List.Cons`" is not the fix.
  test "an imported ctor from an unshadowed family is foreign, not shadowed" do
    src = """
    mod ForeignNotShadowed
      fn classify(input: String) -> Int = match input
        ['x' | _] -> 1
        _ -> 2
    end
    """

    assert {:error, {:source_context, {:foreign_ctor, ctor}, context}} = elaborate(src)
    assert ctor == :"Std.List#Cons"
    assert context.expected_family == :"Std.String#String"
    assert context.actual_family == :"Std.List#List"
  end

  describe "a local `typealias` shadows a same-named type reached from another module" do
    # "Unqualified precedence: local wins" is the whole rule, and it has to hold for
    # every kind of type declaration — a `typealias` is a declaration of the name
    # just as `type` is. It did not hold here, because `resolve_index_name/2` orders
    # its lookup by TABLE (primitive → family → def → ctor) with no notion of who
    # owns what, while `Env.resolve_key/3` will reach through a cross-module alias
    # index to answer for a bare name. So an *imported* family named `Char` was
    # found at the family step and returned before the def step could ever see the
    # module's own `typealias Char`. Table order is for disambiguating within one
    # scope; deciding between scopes is a separate question, and answering it with
    # table order hands imports precedence over the local declaration.
    #
    # `Char` is the name that exposed it: `@prelude @builtin(:char) opaque type Char`
    # is ambient in every module, so any module aliasing that spelling silently got
    # `Std.Char#Char` in its annotations instead of its own type.

    test "the annotation uses the local alias, not the ambient type of the same name" do
      src = """
      mod AliasShadow
        typealias Char = Int
        fn a() -> Char = 97
      end
      """

      assert {:ok, env} = elaborate(src)

      # `Int`, so an integer literal is an `int_lit`. Had the annotation resolved to
      # the ambient `Std.Char#Char`, `97` would go through that type's
      # `ExpressibleByNaturalLiteral` implementation instead.
      assert Cure.Core.Env.get_def(env, :a).body == {:int_lit, 97}
    end

    test "the alias's own right-hand side governs the literal protocol" do
      src = """
      mod AliasShadowBounded
        use Std.Bounded
        typealias Char = Bounded(1114112)
        fn a() -> Char = 97
      end
      """

      assert {:ok, env} = elaborate(src)
      assert Cure.Core.Env.get_def(env, :a).body == {:bounded_lit, 97}
    end

    test "the alias's own right-hand side governs the bound check too" do
      # Not just which protocol, but which *type* — the local bound rejects, and the
      # error names the local bound rather than the ambient type's.
      src = """
      mod AliasShadowRange
        use Std.Bounded
        typealias Char = Bounded(10)
        fn a() -> Char = 500
      end
      """

      assert {:error, {:source_context, {:bounded_lit_out_of_range, 500, 10}, _}} = elaborate(src)
    end

    test "with no local declaration the ambient type still wins the bare name" do
      # The control: shadowing must be triggered by the local declaration, not by
      # the spelling. Nothing here declares `Char`, so `Char` is `Std.Char#Char`.
      #
      # The discriminating observable is the annotation's resolved TYPE, not an
      # error. `Char` is `@builtin(:char)` and the kernel's compact-literal rule is
      # its introduction form, so `97` is a perfectly good `Char` — as it is a
      # perfectly good `Bounded(1114112)`. Both elaborate to `{:bounded_lit, 97}`;
      # what tells the two apart is which type the definition ended up at.
      src = """
      mod NoAliasShadow
        fn a() -> Char = 97
      end
      """

      assert {:ok, env} = elaborate(src)
      definition = Cure.Core.Env.get_def(env, :a)

      assert definition.body == {:bounded_lit, 97}
      assert definition.type == {:data, :"Std.Char#Char", [], []}
    end
  end

  test "R4: `Std.Nat` in a type slot resolves to the imported type (module==typename collapse)" do
    src = """
    mod Collapse
      use Std.Nat
      type Nat = Zero | Suc(Nat)
      fn imported_zero() -> Std.Nat = Std.Nat.Z()
    end
    """

    assert {:ok, _env} = elaborate(src)
  end

  describe "a constructor name collides in its OWN namespace, independent of its family" do
    # The collision-detection pipeline used to scan exactly two namespaces: family/type names
    # (`owned_family_names/1`) and top-level def names (`owned_def_names/1`). A constructor was
    # only ever re-keyed as a SIDE EFFECT of its owning family colliding — `rekey_module_env`
    # derived its owned-ctor set from the owned FAMILY names.
    #
    # So a local constructor whose bare name matches an imported constructor of a DIFFERENT,
    # non-colliding family was never seen as a collision at all. `Std.Result` was never re-keyed,
    # and the plain `Map.put` in `Inductive.declare/3` destroyed its `Ok` — with no diagnostic
    # AND no qualified escape hatch, since `resolve_qualified/3` reads the re-keyed env. That
    # breaks this module's own promise of "keeping the imported family reachable via a qualified
    # escape hatch". Constructor ownership is now scanned as its own namespace.
    @src """
    mod CtorNameCollision
      use Std.Result
      type Res = Ok(Int) | Nope
      fn mk() -> Res = Ok(5)
    end
    """

    test "the losing import stays reachable at its qualified key" do
      assert {:ok, env} = elaborate(@src)

      assert {:ok, :"Std.Result#Ok"} =
               Cure.Elab.Resolution.resolve_qualified(env, "Std.Result.Ok", :value)

      assert env.ctor_to_family[:"Std.Result#Ok"] == :"Std.Result#Result"
    end

    test "the local declaration wins the bare key" do
      assert {:ok, env} = elaborate(@src)

      assert env.ctor_to_family[:"CtorNameCollision#Ok"] == :"CtorNameCollision#Res"

      assert Cure.Core.Env.get_def(env, :mk).body ==
               {:ctor, :"CtorNameCollision#Ok", [int_lit: 5]}
    end

    test "a non-colliding constructor of the same import keeps its bare key" do
      # `Result` is `Ok(t) | Error(e)`; only `Ok` collides. `Error` must not be dragged along —
      # "a constructor keeps its bare key unless its own name is in shadowed_ctor_names".
      assert {:ok, env} = elaborate(@src)

      assert env.ctor_to_family[:"Std.Result#Error"] == :"Std.Result#Result"
      assert env.families[:"Std.Result#Result"].name == :"Std.Result#Result"
    end
  end
end
