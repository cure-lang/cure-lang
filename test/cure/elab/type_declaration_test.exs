defmodule Cure.Elab.TypeDeclarationTest do
  @moduledoc """
  Regressions around what a type declaration actually declares.

  `type X = Y` with a single bare right-hand side is ambiguous, and the parser cannot
  resolve it — it tags the RHS `variant: true` and defers:

      type MyNat = Nat        # an ALIAS: `Nat` names a type in scope
      type Unit  = MkUnit     # a one-constructor ENUM: `MkUnit` names no type

  Both used to take the alias branch, which installed `Unit := {:data, :MkUnit, [], []}`
  with a hardcoded kind of `{:type, 0}` and never checked it — so a one-constructor enum
  silently became an alias to a family that does not exist. Nothing checked because the
  only kernel call on a typealias was `maybe_certify/2`, whose whole job is to SWALLOW
  errors: for a function body a failure there means "does not certify as total, stop
  δ-unfolding", never "ill-typed" (the body's `Kernel.check/3` already ran). A typealias
  had no prior check, so a genuine kind error was discarded like a benign non-termination
  verdict.

  Three consequences, all fixed:

    * `typealias Bad = Z` (aliasing a Nat CONSTRUCTOR) reported `{:ok, _}`. Idris
      (`Bad : Type; Bad = Z`) and Lean (`def Bad : Type := Z`) reject it.
    * an `interface` declares its dictionary as a record family of the same name, but
      `:interface` was missing from the per-module duplicate-type scan, so a sibling
      `type Equatable = ...` silently overwrote it.
    * a plain zero-type-param enum was built by a duplicate constructor pipeline that
      reimplemented a strict subset of `idx_to_core/5` and rejected arrow types outright,
      so `type Callback = Wrap((Int) -> Int)` failed while the identical `rec Callback`
      and `type Callback(a) = ...` succeeded. That pipeline is deleted.
  """
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.{Emit, Program}

  @nat "  type Nat = Z | S(Nat)\n"

  describe "typealias" do
    test "an alias to a type is accepted" do
      assert {:ok, _} = Program.elaborate("mod M\n" <> @nat <> "  typealias Good = Nat\nend\n")
    end

    test "an alias to a constructor is rejected — a constructor is not a type" do
      source = "mod M\n" <> @nat <> "  typealias Bad = Z\nend\n"
      assert {:error, {:typealias_not_a_type, %{name: :Bad}} = error} = Program.elaborate(source)

      {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(error, "bad_alias.cure", source)

      assert Renderer.plain(diagnostic, registry, width: 80) ==
               String.trim_trailing("""
               -- `BAD` ALIASES A VALUE, NOT A TYPE [E093] --------------------- bad_alias.cure

               The right side of a `typealias` must itself be a type, but this expression is a
               value whose type is `Nat`. Type aliases give another name to a type; they cannot
               name one particular value.

               at bad_alias.cure:3:19
               3 |   typealias Bad = Z
                 |             ---   ^ this declaration promises a type alias; this is a value of type `Nat`

               Hint: If `Bad` should alias the value's type, write `typealias Bad = Nat`
               """)

      lsp = Renderer.lsp(diagnostic, registry)

      assert lsp["range"] == %{
               "start" => %{"line" => 2, "character" => 18},
               "end" => %{"line" => 2, "character" => 19}
             }

      assert [related] = lsp["relatedInformation"]

      assert related["location"]["range"] == %{
               "start" => %{"line" => 2, "character" => 12},
               "end" => %{"line" => 2, "character" => 15}
             }

      assert lsp["data"]["payload"] == %{
               "actual_surface" => "Nat",
               "kind" => "typealias_not_a_type",
               "name" => "Bad",
               "rhs_shape" => "variable"
             }

      assert {:ok, _environment} =
               source
               |> String.replace("typealias Bad = Z", "typealias Bad = Nat")
               |> Program.elaborate(file: "fixed_alias.cure")
    end
  end

  describe "type X = Y" do
    test "resolves to an ALIAS when Y names a type in scope" do
      src =
        "mod M\n" <>
          @nat <> "  type MyNat = Nat\n  fn f(n: MyNat) -> MyNat = S(n)\nend\n"

      assert {:ok, _} = Program.elaborate(src)
    end

    test "resolves to a one-constructor ENUM when Y names no type" do
      src = "mod M\n  type Unit = MkUnit\n  fn u() -> Unit = MkUnit()\nend\n"

      assert {:ok, env} = Program.elaborate(src)
      assert {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Test.UnitEnum", functions: [:u])
      assert apply(mod, :u, []) == :MkUnit
    end

    test "a one-constructor enum whose constructor already exists is a duplicate" do
      assert {:error, {:duplicate_constructor, %{name: :Z, spans: [first, second]}}} =
               Program.elaborate("mod M\n" <> @nat <> "  type Bad = Z\nend\n")

      assert first.start_line == 2
      assert second.start_line == 3
    end
  end

  describe "name collisions within a module" do
    test "an interface's dictionary record collides with a sibling type declaration" do
      src = """
      mod X
        interface Equatable(a)
          fn eq(x: a, y: a) -> Bool
        type Equatable = Foo | Bar
      end
      """

      assert {:error, {:duplicate_type, %{name: :Equatable, spans: [first, second]}}} =
               Program.elaborate(src)

      assert first.start_line == 2
      assert second.start_line == 4
    end
  end

  describe "constructor field types" do
    test "a plain enum constructor accepts a function-typed field, like a record" do
      src = "mod M\n  type Callback = Wrap((Int) -> Int)\nend\n"

      assert {:ok, _} = Program.elaborate(src)
    end

    test "a negative occurrence in a function-typed field is still rejected by positivity" do
      # Admitting arrow fields must not admit the Curry paradox. `MkBad : (Bad -> Nat) -> Bad`
      # puts `Bad` to the left of an arrow in its own constructor.
      src = "mod M\n" <> @nat <> "  type Bad = MkBad((Bad) -> Nat)\nend\n"

      assert {:error, error} = Program.elaborate(src, file: "positivity.cure")
      assert {:non_strictly_positive, :"M#MkBad"} = Program.semantic_error(error)

      {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(error, "positivity.cure", src)

      assert Renderer.plain(diagnostic, registry, width: 80) ==
               String.trim_trailing("""
               -- RECURSIVE TYPE APPEARS IN A FUNCTION INPUT [E103] ----------- positivity.cure

               `Bad` appears in a function input stored by `MkBad`. A recursive type may appear
               in a stored function's result, but not in one of its inputs.

               at positivity.cure:3:21
               3 |   type Bad = MkBad((Bad) -> Nat)
                 |              -----  ^^^ this constructor stores the unsafe function type; recursive `Bad` is consumed here

               Hint: Move `Bad` to the function result, or make the input non-recursive
               """)

      lsp = Renderer.lsp(diagnostic, registry)

      assert lsp["range"] == %{
               "start" => %{"line" => 2, "character" => 20},
               "end" => %{"line" => 2, "character" => 23}
             }

      assert [related] = lsp["relatedInformation"]
      assert related["message"] == "this constructor stores the unsafe function type"

      assert related["location"]["range"] == %{
               "start" => %{"line" => 2, "character" => 13},
               "end" => %{"line" => 2, "character" => 18}
             }
    end

    test "an alias-expanded negative occurrence keeps honest constructor-level blame" do
      src = "mod M\n  typealias Neg(a) = (a) -> Int\n  type Bad = MkBad(Neg(Bad))\nend\n"

      assert {:error, error} = Program.elaborate(src, file: "alias_positivity.cure")
      assert {:non_strictly_positive, :"M#MkBad"} = Program.semantic_error(error)

      {diagnostic, registry} =
        Cure.Compiler.Errors.to_diagnostic(error, "alias_positivity.cure", src)

      assert Renderer.plain(diagnostic, registry, width: 80) ==
               String.trim_trailing("""
               -- NON-STRICTLY-POSITIVE TYPE [E103] --------------------- alias_positivity.cure

               The recursive occurrence in `MkBad` cannot be proven strictly positive, so this
               type cannot be accepted by the normalising kernel.

               at alias_positivity.cure:3:14
               3 |   type Bad = MkBad(Neg(Bad))
                 |              ^^^^^ this constructor is not strictly positive

               Hint: Move recursive types out of function-input and other negative positions in this constructor
               """)

      assert diagnostic.secondary == []

      assert Renderer.lsp(diagnostic, registry)["range"] == %{
               "start" => %{"line" => 2, "character" => 13},
               "end" => %{"line" => 2, "character" => 18}
             }
    end
  end
end
