defmodule Cure.Elab.UsageCheckTest do
  @moduledoc """
  Slice 4b: the **usage check** — `Relevance` counts occurrences and holds each
  binder to its declared grade.

  Idris runs two independent mechanisms in `Core/LinearCheck.idr`, and Cure needs
  both:

    * `rigSafe` (`:166-170`), at a `Local` occurrence — a *position/preorder*
      check. This is what Cure already had, specialised to `{0, ω}`: an `:erased`
      binder may not appear in a relevant position. Its errors keep the
      `{:erased_used_relevantly, …}` shape and are asserted unchanged below.
    * `checkUsageOK` (`:274-276`), at a `Bind` — a *counting* check:
      `when (isLinear r && used /= 1) (throw …)`. This is what 4b adds, and where
      affinity enters, because `:affine` admits both `0` and `1`.

  Usage is carried as a **grade** (`:erased` = 0 uses, `:linear` = 1,
  `:unrestricted` = many), composed with `Grade.add/2` in sequence and scaled with
  `Grade.mul/2` on entering a subterm. The rule is then `Grade.leq(used, declared)`
  — subusaging — which is exhaustively equivalent to `Grade.admits?(declared, n)`
  over the carrier (`grade_test.exs` pins that).

  Two consequences worth stating, because both are easy to get wrong:

    * **Branches combine by agreement, not summation.** A `case` yields a *set* of
      possible usages, one per branch, and every member must satisfy `leq`. A
      `:linear` binder used in one branch and dropped in another is rejected; an
      `:affine` one is accepted. Idris's `combineUsage` throws on any `Use0`/`Use1`
      mismatch regardless of grade — correct for Idris, which has no affine, and
      wrong for Cure.
    * **Closure capture falls out of `mul/2`, not a special case.** A λ is a value
      that may be entered any number of times, so its body's usage of *outer*
      binders is scaled by `ω`. A linear binder captured by a returned closure is
      therefore used `ω` times, and rejected. Idris gets this via `eraseLinear env`
      when checking a `Lam` in a `top` context (`:233-237`).
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Env, Inductive}
  alias Cure.Elab.{Erase, Relevance}

  @nat {:data, :Nat, [], []}
  @motive {:lam, :unrestricted, @nat, @nat}

  defp nat_env do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Nat, [], [], 0), [
      Inductive.ctor(:Z, [], []),
      Inductive.ctor(:S, [n: @nat], [])
    ])
  end

  # A one-field box whose field carries `grade`.
  defp box_env(grade) do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Box, [], [], 0), [
      Inductive.ctor(:mk, [v: @nat], [], [grade])
    ])
  end

  # `let _ = <x> in <x>` — the shortest term that uses parameter `x` TWICE.
  # Sequential composition, so the two usages are summed: `1 + 1 = ω`.
  defp uses_twice, do: {:let, :unrestricted, @nat, {:var, 0}, {:var, 1}}

  defp check(env \\ Env.empty(), quantities, body),
    do: Relevance.check(env, :f, quantities, body)

  describe "linear binders must be used exactly once" do
    test "a linear parameter used exactly once is accepted" do
      assert :ok = check([:linear], {:var, 0})
    end

    test "a linear parameter used twice is rejected" do
      assert {:error, {:usage_violation, %{binder: 0, declared: :linear, used: :unrestricted}}} =
               check([:linear], uses_twice())
    end

    test "a linear parameter used zero times is rejected" do
      assert {:error, {:usage_violation, %{binder: 0, declared: :linear, used: :erased}}} =
               check([:linear], {:int_lit, 7})
    end
  end

  describe "affine binders may be dropped, but not duplicated" do
    test "an affine parameter used zero times is ACCEPTED" do
      assert :ok = check([:affine], {:int_lit, 7})
    end

    test "an affine parameter used once is accepted" do
      assert :ok = check([:affine], {:var, 0})
    end

    test "an affine parameter used twice is rejected" do
      assert {:error, {:usage_violation, %{binder: 0, declared: :affine, used: :unrestricted}}} =
               check([:affine], uses_twice())
    end
  end

  describe "unrestricted binders impose no obligation" do
    test "zero, one, and two uses are all accepted" do
      assert :ok = check([:unrestricted], {:int_lit, 7})
      assert :ok = check([:unrestricted], {:var, 0})
      assert :ok = check([:unrestricted], uses_twice())
    end
  end

  describe "inner binders carry their own grade" do
    test "a linear lambda binder used twice is rejected" do
      # `fn(x) -> fn(1 y) -> let _ = y in y`
      body = {:lam, :linear, @nat, uses_twice()}

      assert {:error, {:usage_violation, %{declared: :linear, used: :unrestricted}}} =
               check([:unrestricted], body)
    end

    test "a linear lambda binder used once is accepted" do
      assert :ok = check([:unrestricted], {:lam, :linear, @nat, {:var, 0}})
    end

    test "an unused linear let binder is rejected" do
      assert {:error, {:usage_violation, %{declared: :linear, used: :erased}}} =
               check([], {:let, :linear, @nat, {:int_lit, 1}, {:int_lit, 2}})
    end

    test "a linear let binder used once is accepted" do
      assert :ok = check([], {:let, :linear, @nat, {:int_lit, 1}, {:var, 0}})
    end
  end

  describe "closure capture (the mul/2 hazard)" do
    test "a linear parameter captured by a returned closure is rejected" do
      # `fn(1 x) -> fn(_) -> x` — the closure may be entered any number of times,
      # so `x`'s single syntactic occurrence is `ω` uses. This must fall out of
      # `Grade.mul(:unrestricted, …)`, not a bespoke closure rule.
      body = {:lam, :unrestricted, @nat, {:var, 1}}

      assert {:error, {:usage_violation, %{binder: 0, declared: :linear, used: :unrestricted}}} =
               check([:linear], body)
    end

    test "an affine parameter captured by a returned closure is also rejected" do
      body = {:lam, :unrestricted, @nat, {:var, 1}}
      assert {:error, {:usage_violation, %{declared: :affine}}} = check([:affine], body)
    end
  end

  describe "case branches combine by agreement, not summation" do
    # `x` is used in the Z branch and dropped in the S branch.
    defp lopsided_case do
      {:case, {:var, 0}, @motive, [{:Z, 0, {:var, 1}}, {:S, 1, {:int_lit, 0}}]}
    end

    test "a linear binder used in one branch and dropped in another is rejected" do
      assert {:error, {:usage_violation, %{binder: 0, declared: :linear, used: :erased}}} =
               check(nat_env(), [:linear, :unrestricted], lopsided_case())
    end

    test "an affine binder used in one branch and dropped in another is ACCEPTED" do
      assert :ok = check(nat_env(), [:affine, :unrestricted], lopsided_case())
    end

    test "a linear binder used once in EVERY branch is accepted" do
      body = {:case, {:var, 0}, @motive, [{:Z, 0, {:var, 1}}, {:S, 1, {:var, 2}}]}
      assert :ok = check(nat_env(), [:linear, :unrestricted], body)
    end

    test "usages are not SUMMED across branches — once per branch is once" do
      # If the two branches were summed this would be `1 + 1 = ω` and rejected.
      body = {:case, {:var, 0}, @motive, [{:Z, 0, {:var, 1}}, {:S, 1, {:var, 2}}]}
      assert :ok = check(nat_env(), [:linear, :unrestricted], body)
    end
  end

  describe "the erased position check is unchanged (Idris rigSafe)" do
    test "an erased parameter returned as the value is still rejected" do
      assert {:error, {:erased_used_relevantly, %{binder: 0, site: :returned}}} =
               check([:erased], {:var, 0})
    end

    test "an erased parameter in an ERASED argument position is still exempt" do
      assert :ok = check(box_env(:erased), [:erased], {:ctor, :mk, [{:var, 0}]})
    end

    test "an erased branch field does not shadow a binder inside an outer convoy argument" do
      # `(case box of mk(_) -> fn(x) -> x) (fn(y) -> y)`. The constructor field
      # occupies an erased branch-local level, while the argument lambda is
      # authored in the outer frame. Reusing the branch erasure set while walking
      # the argument aliases those unrelated levels and falsely rejects `y`.
      identity = {:lam, :unrestricted, @nat, {:var, 0}}

      convoy =
        {:app, {:case, {:var, 0}, @motive, [{:mk, 1, {:lam, :unrestricted, @nat, {:var, 0}}}]}, identity}

      assert :ok = check(box_env(:erased), [:unrestricted], convoy)
    end

    test "an unused convoy binder does not make its erased administrative argument relevant" do
      convoy =
        {:app, {:case, {:global, :box}, @motive, [{:mk, 1, {:lam, :erased, @nat, {:int_lit, 0}}}]}, {:var, 0}}

      assert :ok = check(box_env(:unrestricted), [:erased], convoy)

      assert {:case, {:global, :box}, _motive, [{:mk, 1, {:int_lit, 0}}]} =
               Erase.erase(box_env(:unrestricted), convoy)
    end

    test "an erased convoy function placeholder absorbs its administrative application" do
      term = {:app, {:ctor, :cure_erased, []}, {:global, :proof_argument}}

      assert Erase.erase(Env.empty(), term) == {:ctor, :cure_erased, []}
    end
  end

  describe "argument positions are gated by present?/1, not by == :unrestricted" do
    # Slice 4a renamed `:present` to `:unrestricted` across the tree. In `Erase`
    # and `Emit` the predicate was corrected to `Grade.present?/1`; in `Relevance`
    # the rename left `q == :unrestricted`, which EXEMPTS `:linear` and `:affine`
    # argument positions from the walk entirely. Dormant until 4b made those
    # grades reachable. This is the dual of the bug `quantity_grade_test` pins for
    # `Erase`.
    test "an erased parameter passed in a LINEAR argument position is rejected" do
      assert {:error, {:erased_used_relevantly, %{binder: 0, site: :present_arg}}} =
               check(box_env(:linear), [:erased], {:ctor, :mk, [{:var, 0}]})
    end

    test "an erased parameter passed in an AFFINE argument position is rejected" do
      assert {:error, {:erased_used_relevantly, %{binder: 0, site: :present_arg}}} =
               check(box_env(:affine), [:erased], {:ctor, :mk, [{:var, 0}]})
    end
  end

  describe "type positions are erased positions" do
    test "a linear parameter occurring only in a Pi domain counts as zero uses" do
      # `:pi` is exempt from the walk, so the occurrence contributes nothing and
      # the linear obligation is unmet.
      assert {:error, {:usage_violation, %{declared: :linear, used: :erased}}} =
               check([:linear], {:pi, :unrestricted, {:var, 0}, @nat})
    end
  end
end
