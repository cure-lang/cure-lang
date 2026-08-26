defmodule Cure.Elab.JoinUnjoinDifferentialTest do
  @moduledoc """
  Differential oracle for the join-point un-join in the usage checker (review F11,
  the linearity-checker rewrite).

  The join point (slice 4c) shares a `match` catch-all body under a `{:lam, ω, …}`.
  The usage checker (`Relevance`) now UN-JOINS that idiom: instead of ω-scaling the
  shared continuation's captures, it counts them ONCE and combines them as one
  alternative into the branch agreement — matching how Idris usage-checks each case
  alternative independently (`LinearCheck.idr` `getArgUsage`: `traverse getPUsage
  pats; combine us`).

  The un-join is sound ONLY if it produces exactly the verdict the un-joined
  PER-BRANCH form produces. That per-branch form is what the elaborator emits when
  the join is disabled. So this test is a differential oracle: for each graded
  program, the accept/reject verdict with the join ON (un-join) must be IDENTICAL to
  the verdict with the join OFF (per-branch). The `:qtt_join_disabled` process flag
  is the test hook that forces the per-branch form.

  A divergence here means the un-join is UNSOUND (accepts what per-branch rejects) or
  incomplete (rejects what per-branch accepts) — either way a real bug. This battery
  is the primary evidence the rewrite is correct.
  """
  use ExUnit.Case, async: false

  alias Cure.Elab.Program

  @enum "type C = A | B | D | E | G | H\n"
  @prelude "  fn sink(@linear x : Int) -> Int = x\n" <>
             "  fn asink(@affine x : Int) -> Int = x\n" <>
             "  fn use2(a: Int, b: Int) -> Int = a\n" <>
             "  fn add(a: Int, b: Int) -> Int = a\n"

  defp verdict(src) do
    case Program.elaborate(src) do
      {:ok, _} -> :accept
      {:error, _} -> :reject
    end
  end

  # Per-branch (join OFF) vs un-join (join ON) verdicts for the same program.
  defp both(src) do
    Process.put(:qtt_join_disabled, true)
    per_branch = verdict(src)
    Process.delete(:qtt_join_disabled)
    un_join = verdict(src)
    {per_branch, un_join}
  end

  # Every program in the battery: `{label, source, expected_verdict}`. The oracle
  # asserts per-branch == un-join == expected for each.
  @battery [
    {"linear once per branch",
     "  fn f(x: C) -> Int =\n    let @linear v = 1\n    match x\n      A() -> sink(v)\n      _ -> sink(v)\n", :accept},
    {"linear twice in catch-all",
     "  fn f(x: C) -> Int =\n    let @linear v = 1\n    match x\n      A() -> use2(v, v)\n      _ -> use2(v, v)\n",
     :reject},
    {"linear used in matched arm AND catch-all (alt not seq)",
     "  fn f(x: C) -> Int =\n    let @linear v = 1\n    match x\n      A() -> sink(v)\n      B() -> sink(v)\n      _ -> sink(v)\n",
     :accept},
    {"linear in only some branches",
     "  fn f(x: C) -> Int =\n    let @linear v = 1\n    match x\n      A() -> 0\n      _ -> sink(v)\n", :reject},
    {"affine dropped on a branch",
     "  fn f(x: C) -> Int =\n    let @affine v = 1\n    match x\n      A() -> 0\n      _ -> asink(v)\n", :accept},
    {"affine twice",
     "  fn f(x: C) -> Int =\n    let @affine v = 1\n    match x\n      A() -> use2(v, v)\n      _ -> use2(v, v)\n",
     :reject},
    {"linear used once, only in the catch-all, all-catch-all (single arm)",
     "  fn f(x: C) -> Int =\n    let @linear v = 1\n    match x\n      _ -> sink(v)\n", :accept},
    {
      "two linear vars combined via an ω function → ω-scaled → reject (correct QTT)",
      # `add`'s params are ω, so passing `sink(v)`/`sink(w)` scales v,w by ω
      # (`mul(ω, linear) = ω`, Idris `checkRig = rigf |*| rig`). Rejected — and the
      # un-join must agree with per-branch, which is the point.
      "  fn f(x: C) -> Int =\n    let @linear v = 1\n    let @linear w = 2\n    match x\n      A() -> add(sink(v), sink(w))\n      _ -> add(sink(v), sink(w))\n",
      :reject
    },
    {"two linear vars, one dropped in catch-all",
     "  fn f(x: C) -> Int =\n    let @linear v = 1\n    let @linear w = 2\n    match x\n      A() -> add(sink(v), sink(w))\n      _ -> sink(v)\n",
     :reject},
    {"linear used in catch-all body's own nested match",
     "  fn f(x: C, y: C) -> Int =\n    let @linear v = 1\n    match x\n      A() -> sink(v)\n      _ -> match y\n        A() -> sink(v)\n        _ -> sink(v)\n",
     :accept},
    {"linear captured, catch-all uses it twice via nested match sequence",
     "  fn f(x: C, y: C) -> Int =\n    let @linear v = 1\n    match x\n      A() -> sink(v)\n      _ -> add(sink(v), sink(v))\n",
     :reject},
    {"unrestricted var through catch-all (no obligation)",
     "  fn f(x: C, n: Int) -> Int =\n    match x\n      A() -> use2(n, n)\n      _ -> use2(n, n)\n", :accept},
    {"named catch-all: v via ω `add` → ω-scaled → reject (correct); un-join must agree",
     "  fn rank(y: C) -> Int =\n    match y\n      A() -> 1\n      B() -> 2\n      D() -> 3\n      E() -> 4\n      G() -> 5\n      H() -> 6\n  fn f(x: C) -> Int =\n    let @linear v = 1\n    match x\n      A() -> sink(v)\n      z -> add(rank(z), sink(v))\n",
     :reject}
  ]

  for {label, body, expected} <- @battery do
    @body body
    @expected expected
    test "un-join ≡ per-branch: #{label}" do
      src = "mod JUD\n  #{@enum}#{@prelude}#{@body}end\n"
      {per_branch, un_join} = both(src)

      assert per_branch == @expected,
             "per-branch (oracle) verdict #{per_branch} != expected #{@expected} — the test's own expectation is wrong"

      assert un_join == per_branch,
             "UN-JOIN DIVERGED from per-branch: un_join=#{un_join}, per_branch=#{per_branch}. " <>
               "The un-join is #{if un_join == :accept, do: "UNSOUND (accepts what per-branch rejects)", else: "incomplete (rejects what per-branch accepts)"}."
    end
  end

  # The @battery uses only NULLARY constructors, so the `arity > 0` machinery
  # (`drop_levels`, `Subst.shift(scrut, 1 + arity, 0)`) is never exercised there.
  # These use field constructors, whose defaulted branches bind `arity` pattern
  # variables under the join, stressing exactly that arithmetic (red-team Finding 2).
  @arity_battery [
    {"1-field constructor swept into the catch-all",
     "mod JA\n  type C = A | B(Int) | D | E | G(Int) | H\n" <>
       "  fn sink(@linear x : Int) -> Int = x\n" <>
       "  fn f(x: C) -> Int =\n    let @linear v = 1\n    match x\n      A() -> sink(v)\n      _ -> sink(v)\nend\n",
     :accept},
    {"matched arm binds a field, catch-all captures linear v",
     "mod JA\n  type C = A(Int) | B | D | E | G | H\n" <>
       "  fn sink(@linear x : Int) -> Int = x\n" <>
       "  fn f(x: C) -> Int =\n    let @linear v = 1\n    match x\n      A(n) -> sink(v)\n      _ -> sink(v)\nend\n",
     :accept},
    {"2-field constructor in the catch-all (drop_levels range > 1)",
     "mod JA\n  type C = A | B(Int, Int) | D | E | G | H\n" <>
       "  fn sink(@linear x : Int) -> Int = x\n" <>
       "  fn f(x: C) -> Int =\n    let @linear v = 1\n    match x\n      A() -> sink(v)\n      _ -> sink(v)\nend\n",
     :accept},
    {"linear v used twice under a field-constructor catch-all → reject",
     "mod JA\n  type C = A | B(Int) | D | E | G | H\n" <>
       "  fn sink(@linear x : Int) -> Int = x\n  fn use2(a: Int, b: Int) -> Int = a\n" <>
       "  fn f(x: C) -> Int =\n    let @linear v = 1\n    match x\n      A() -> use2(v, v)\n      _ -> use2(v, v)\nend\n",
     :reject}
  ]

  for {label, src, expected} <- @arity_battery do
    @arity_src src
    @arity_expected expected
    test "un-join ≡ per-branch (arity>0): #{label}" do
      {per_branch, un_join} = both(@arity_src)

      assert per_branch == @arity_expected,
             "per-branch (oracle) verdict #{per_branch} != expected #{@arity_expected}"

      assert un_join == per_branch,
             "UN-JOIN DIVERGED (arity>0): un_join=#{un_join}, per_branch=#{per_branch}"
    end
  end
end
