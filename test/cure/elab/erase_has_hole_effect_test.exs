defmodule Cure.Elab.EraseHasHoleEffectTest do
  @moduledoc """
  `Erase.has_hole?/1` must see holes inside the Effect formers.

  It enumerated `:lam`, `:let`, `:pi`, `:app`, `:ctor`, `:data` and `:case` and then fell to
  `def has_hole?(_term), do: false` — so a hole sitting inside an `{:effect_pure, …}` or
  `{:effect_bind, …}` was reported as "no hole here".

  This is NOT the codegen firewall, and today it is not reachable from the surface either.
  `Program.check_codegen_ready/1` routes through `Validator`, which descends everywhere, so an
  unfilled hole still cannot reach the backend (that is exactly why the validator was
  introduced — see the comment at `program.ex:1009` about "gaps" in this hand-rolled walker).
  And the surface only admits a hole as an entire function body: `emit(?rest)` and a `?rest`
  tail inside an effectful body are both rejected as `:unsupported_expression`, so no source
  program can currently put a hole underneath an effect node.

  The predicate must still be total, because two things read it that do not go through the
  surface at all:

    * `Antigen.Assays.Erasure` SYNTHESISES Core terms directly, and its metamorphic property
      is `has_hole?(t) == false and has_hole?(erase(t)) == true → :hole_introduced`. A
      predicate that under-reports holes silently weakens the very assay meant to police hole
      introduction — it cannot detect a hole the walker refuses to look at.
    * `Antigen.Assays.Elab` skips definitions whose body has a hole.

  So these are unit contract tests, not a surface regression. They pin the walker's totality
  where the walker's consumers actually live. If hole-in-expression-position ever lands, the
  `Program.hole_goals/1` diagnostic inherits the repair for free.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Erase
  alias Cure.Core.Grade

  describe "has_hole? descends into effect nodes" do
    test "a hole inside effect_pure is found" do
      assert Erase.has_hole?({:effect_pure, {:hole, "x"}})
    end

    test "a hole in either side of effect_bind is found" do
      k = {:lam, Grade.unrestricted(), {:int_type}, {:int_lit, 1}}
      assert Erase.has_hole?({:effect_bind, {:hole, "e"}, k})

      assert Erase.has_hole?(
               {:effect_bind, {:effect_pure, {:int_lit, 1}}, {:lam, Grade.unrestricted(), {:int_type}, {:hole, "k"}}}
             )
    end

    test "a hole inside effect_type is found" do
      assert Erase.has_hole?({:effect_type, {:hole, "t"}})
    end

    test "an effectful term with no hole is still hole-free" do
      # The predicate must be REPAIRED, not made vacuously true.
      refute Erase.has_hole?(
               {:effect_bind, {:effect_pure, {:int_lit, 1}}, {:lam, Grade.unrestricted(), {:int_type}, {:var, 0}}}
             )
    end
  end
end
