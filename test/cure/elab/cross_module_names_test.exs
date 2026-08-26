defmodule Cure.Elab.CrossModuleNamesTest do
  @moduledoc """
  A module is a namespace: each `mod` compiles to its own BEAM module (`Cure.A`, `Cure.B`), so
  two modules sharing a function / type / constructor name is legitimate — the stdlib has `map`
  in six modules. Those collisions are resolved by the E-layer resolution/rekey machinery
  (`Resolution.rekey_module_env`, LOCKED type-shadowing Approach B), not by rejection.

  That rekey machinery runs on IMPORTED module slices. It does not run on two sibling `mod`
  blocks in one compilation unit, and that distinction is load-bearing. `declarations/1`
  flattens every sibling of one AST into a single list before `elaborate_declarations/3` runs,
  so siblings share one flat `env.defs` / `env.families` / `env.ctor_to_family`, each a plain
  `Map.put`. This file used to assert `{:ok, _}` for exactly that case without ever inspecting
  which declaration survived. It did not survive:

    * `mod A fn foo = 1 end  mod B fn foo = 2 end` kept only B's body. A's own callers would
      δ-unfold B's `foo`.
    * `mod A type Foo = MkA end  mod B type Foo = MkB end` left `MkA` registered as a
      constructor whose `ctor_to_family` entry names a family whose constructor set holds only
      `MkB` — the incoherent state `check_no_duplicate_ctors` rejects within one module.

  So sibling collisions are now rejected. Rekeying them instead would mean elaborating each
  sibling into its own slice, which would break the bare cross-sibling references flat
  elaboration makes work today (see the last test). The within-module duplicate checks stay
  scoped per module: a repeat inside one module remains its own, distinct error.
  """
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.Program

  defp check(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)
    Program.check_ast(ast)
  end

  describe "modules in separate files may share names (the rekey path)" do
    test "two imported stdlib modules both declaring `map` coexist" do
      # Std.Result and Std.Vector each declare their own `map`. The import rekey path keeps
      # both; this is the guarantee the sibling check below must not disturb.
      src = "mod Client\n  use Std.Result\n  use Std.Vector\n  fn f() -> Int = 1\nend\n"
      assert {:ok, _} = check(src)
    end

    test "overlapping published dependency closures merge without re-entering cyclic source loading" do
      # Both interfaces carry dependencies from the legal Prelude SCC.  Once a
      # canonical stdlib generation exists, importing them together must merge
      # that checked interface graph directly; rebuilding source skeletons for
      # the already-published cycle used to leave a bare `Result` Core key.
      src = "mod Client\n  use Std.Otp\n  use Std.ExitReason\n  fn value() -> Int = 1\nend\n"

      assert {:ok, _} = check(src)
    end
  end

  describe "sibling modules in ONE compilation unit may not share a name" do
    test "a shared function name is rejected, naming both owners" do
      src = "mod A\n  fn foo(x: Int) -> Int = x\nend\nmod B\n  fn foo(x: Int) -> Int = 99\nend\n"

      assert {:error, {:sibling_module_collision, %{name: :foo, owners: [:A, :B], spans: [first, second]}} = error} =
               check(src)

      assert {first.start_line, first.start_column, first.end_column} == {2, 6, 9}
      assert {second.start_line, second.start_column, second.end_column} == {5, 6, 9}

      assert Program.semantic_result({:error, error}) ==
               {:error, {:sibling_module_collision, :foo, [:A, :B]}}
    end

    test "a shared type name is rejected" do
      src = "mod A\n  type Foo = MkA\nend\nmod B\n  type Foo = MkB\nend\n"
      assert {:error, {:sibling_module_collision, %{name: :Foo, owners: [:A, :B], spans: [first, second]}}} = check(src)

      assert {first.start_line, first.start_column} == {2, 8}
      assert {second.start_line, second.start_column} == {5, 8}
    end

    test "a shared constructor name is rejected even across different families" do
      src = "mod A\n  type Foo = C\nend\nmod B\n  type Bar = C\nend\n"
      assert {:error, {:sibling_module_collision, %{name: :C, owners: [:A, :B], spans: [first, second]}}} = check(src)

      assert {first.start_line, first.start_column} == {2, 14}
      assert {second.start_line, second.start_column} == {5, 14}
    end

    test "a function in one sibling colliding with a constructor in another is rejected" do
      # `fn` names and constructor names share one bare-atom namespace, exactly as
      # `check_no_fn_ctor_collision` establishes within a single module.
      src = "mod A\n  fn C(x: Int) -> Int = x\nend\nmod B\n  type Bar = C\nend\n"
      assert {:error, {:sibling_module_collision, %{name: :C, owners: [:A, :B], spans: [first, second]}}} = check(src)

      assert {first.start_line, first.start_column} == {2, 6}
      assert {second.start_line, second.start_column} == {5, 14}
    end

    test "siblings with disjoint names are fine, and may still call each other by bare name" do
      src = "mod A\n  fn bar() -> Int = 7\nend\nmod B\n  fn baz() -> Int = bar()\nend\n"
      assert {:ok, env} = check(src)
      assert env.defs[:"A#bar"]
    end
  end

  describe "a duplicate within one module keeps its own error" do
    test "function" do
      src = "mod A\n  fn foo(x: Int) -> Int = x\n  fn foo(y: Int) -> Int = y\nend\n"
      assert {:error, {:overlapping_overload, %{name: :foo, arity: 1}}} = check(src)
    end

    test "constructor across two types" do
      src = "mod A\n  type Foo = C | D\n  type Bar = C | E\nend\n"
      assert {:error, {:duplicate_constructor, %{name: :C, spans: [first, second]}}} = check(src)
      assert first.start_line == 2
      assert second.start_line == 3
    end
  end

  # E3: a stdlib module whose name is a compound CamelCase word lives in a snake_cased file
  # (`Std.Proof.BooleanReflection` -> `proof_boolean_reflection.cure`). The module->file mapping used to
  # only downcase (`otp_inferencelaws`), so `use` of any multi-word module resolved NONE of its
  # functions (`:unknown_global`). This is independent of whether the function carries implicits.
  describe "multi-word stdlib module names resolve on use (E3)" do
    test "an explicit-arg function from Std.Proof.BooleanReflection resolves" do
      src =
        "mod X\n  use Std.Bool\n  use Std.Proof.IntMath\n  use Std.Proof.BooleanReflection\n" <>
          "  fn t() -> IsTrue(True()) = left_operand_is_true_from_true_conjunction(True(), True(), Confirmed())\nend\n"

      assert {:ok, _} = check(src)
    end

    test "an implicit-carrying function from Std.Proof.BooleanReflection resolves" do
      src =
        "mod X\n  use Std.Bool\n  use Std.Proof.IntMath\n  use Std.Proof.BooleanReflection\n" <>
          "  fn t() -> IsTrue(`and`(True(), True())) = conjunction_is_true_when_both_operands_are(Confirmed(), Confirmed())\nend\n"

      assert {:ok, _} = check(src)
    end
  end
end
