defmodule Cure.Elab.SubstGradeLaunderingTest do
  @moduledoc """
  A graded `let` inside a MATCHED ARM must keep its grade.

  `Relevance` is the only thing in the codebase that ever reads a `let`'s grade — the kernel
  binds it to `_g` and ignores it (`kernel.ex:126`, `:349`), and `Erase` rewrites it to ω
  (`erase.ex:48`). So the grade in the term IS the obligation; there is no signature to
  re-derive it from, unlike a `:pi`/`:lam` grade, which `Kernel.infer` re-derives from the
  registered declaration and therefore cannot be corrupted by the elaborator.

  `wrap_join` shifts every branch body of a join-eligible `case` — an ordinary match with a
  default arm and ≥2 uncovered constructors (`elaborator.ex:4619`):

      {c, arity, body} -> {c, arity, Subst.shift(body, 1, arity)}

  and `Subst.shift`'s `:let` clause used to reconstruct the node with
  `Grade.unrestricted()` hardcoded, discarding the binder's real grade. So a graded `let`
  written inside a matched arm reached `Relevance` as ω, where `admits?(:unrestricted, _)` is
  true for every usage count — and the obligation silently vanished. An `:erased` proof could
  be used at runtime; a `:linear` value could be dropped or duplicated.

  The un-join red team already found this failure mode from the other side and fixed it by
  branching on `Grade.restricted?(g)` (`relevance.ex:260`). That guard is sound. It was being
  handed a term whose grade had already been laundered before it ran.

  The last two tests are the control: the SAME programs with every constructor written out
  (no default arm ⇒ no join ⇒ no shift) were always rejected correctly. That contrast is what
  pins the defect on the shift rather than on the grade machinery.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  # Six constructors, so a `_` arm leaves ≥2 uncovered and `join_point?` fires.
  @enum "  type C = A | B | D | E | G | H\n"

  defp elab(body), do: Program.semantic_result(Program.elaborate("mod SGL\n" <> @enum <> body <> "end\n"))

  describe "a join-eligible case (default arm) — the branch bodies go through Subst.shift" do
    test "an erased let-binding used at runtime in a matched arm is REJECTED" do
      # The soundness case. `p` is erased, so `Erase` will drop it — returning it means
      # referencing a value that does not exist at runtime.
      assert {:error, {:erased_used_relevantly, %{site: :returned}}} =
               elab("""
                 fn f(x: C) -> Int =
                   match x
                     A() ->
                       let @erased p = 1
                       p
                     _ -> 0
               """)
    end

    test "a linear let-binding dropped in a matched arm is REJECTED" do
      assert {:error, {:usage_violation, %{declared: :linear}}} =
               elab("""
                 fn f(x: C) -> Int =
                   match x
                     A() ->
                       let @linear v = 1
                       0
                     _ -> 0
               """)
    end

    test "a linear let-binding used exactly once in a matched arm is accepted" do
      # The obligation must be ENFORCED, not merely reintroduced as a blanket rejection.
      assert {:ok, _} =
               elab("""
                 fn sink(@linear x : Int) -> Int = x
                 fn f(x: C) -> Int =
                   match x
                     A() ->
                       let @linear v = 1
                       sink(v)
                     _ -> 0
               """)
    end
  end

  describe "control — the same arms with no default (no join, no shift) always worked" do
    test "an erased let-binding used at runtime is REJECTED" do
      assert {:error, {:erased_used_relevantly, %{site: :returned}}} =
               elab("""
                 type Two = T | F
                 fn g(x: Two) -> Int =
                   match x
                     T() ->
                       let @erased p = 1
                       p
                     F() -> 0
               """)
    end

    test "a linear let-binding dropped is REJECTED" do
      assert {:error, {:usage_violation, %{declared: :linear}}} =
               elab("""
                 type Two = T | F
                 fn g(x: Two) -> Int =
                   match x
                     T() ->
                       let @linear v = 1
                       0
                     F() -> 0
               """)
    end
  end
end
