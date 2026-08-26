# Axiom-Free Refinement Reflection Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Let open `IsTrue(bool-comparison)` refinement obligations draw on the inductive `Std.Proof.Math` lemma library via a constructive, zero-trust reflection bridge, plus an axiom-free refined→base coercion — no solver, no new axioms, no kernel change.

**Architecture:** Three stdlib layers (a boolean-connective algebra over `IsTrue`; a `Nat` reflection bridge tying boolean comparisons to `IsPositive`/`IsLessThan`/`IsLessThanOrEqual`; a free `Nat → Int` projection), consumed by the *existing* `Cure.Elab.ProofSearch` (new lemmas are `@lemma`-tagged; conjunction elimination is one new candidate source mirroring `projection_candidates/3`), plus one elaborator coercion that inserts `sigma_first` when a refinement value flows into its base type.

**Tech Stack:** Cure (`.cure` stdlib in `lib/std/`), Elixir elaborator (`lib/cure/elab/*`), ExUnit (`test/cure/**`), differential oracle (`mix cure.oracle refine` + Idris2), Antigen.

## Global Constraints

- **Worktree:** `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/axiom-free-refinement-reflection`; branch `autopilot/axiom-free-refinement-reflection`. Run every command from there.
- **Zero new trust:** NO edit to `lib/cure/core/*` (K/TCB). No new `@extern`, `@axiom`, `believe_me`, or `postulate`. If any task seems to require a kernel change, STOP and report — it is a scope violation (certificate checking is in flight).
- **Only the dependent pipeline:** work lives in `lib/cure/elab/*` + `lib/std/*.cure`. IGNORE `lib/cure/compiler/*` and `lib/cure/types/*` — same-named functions there are decoys.
- **`priv/std` is GENERATED:** author only in `lib/std/`. After ANY `lib/std/*.cure` change, re-stage before running elaborate-based tests: `mix cure.bundle_stdlib` (stages `lib/std/*.cure` → `priv/std/`). New `lib/std/*.cure` files are auto-discovered by glob — no manifest edit.
- **Descriptive naming:** spell names out in full (`IsLessThan` not `LT`, `predecessor` not `n`, `Decision` not `Dec`). This is a hard requirement of this feature.
- **Ghost-writer commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, NO `Co-Authored-By`, no Claude signature.
- **Explicit-pathspec staging only:** `git add -- <path>` / `git commit -- <path>`. NEVER `git add -A`/`git add .`.
- **One build at a time:** never run two `mix` suites concurrently. Prefer scoped `mix test <file>`; the full suite runs once, alone, at the final gate.
- **Tests immutable once green;** behavioral, not implementation-coupled.
- **Test harness:** `Cure.Elab.Program.elaborate(source_string)` returns `{:ok, env}` or `{:error, reason}`. `env.defs` holds elaborated Core terms. A surviving proof hole is a `{:hole, id}` neutral node inside a def's term (see the `has_hole?/1` helper pattern in `test/cure/elab/proof_hole_resolution_test.exs`); a hole blocks codegen. Mirror existing `test/cure/stdlib/proof_math_test.exs` / `proof_int_math_test.exs` / `refine_test.exs` for module-elaboration assertions.
- **Oracle cluster:** `refine` (dir `test/oracle/refine/`). `.idr` files carry `%default total` and no `module` line. One shared name-keyed `verdicts.json` per directory. Regenerate with `mix cure.oracle refine` (needs `idris2` at `~/Develop/Idris2/build/exec/idris2`); replay with `mix test test/oracle_replay_test.exs`.

---

### Task 1: Layer 1 — `Std.Proof.BooleanReflection` connective algebra

**Files:**
- Create: `lib/std/proof_boolean_reflection.cure`
- Test: `test/cure/stdlib/proof_boolean_reflection_test.exs`

**Interfaces:**
- Consumes: `Std.Bool` (`Bool`/`True`/`False`/`` `and` ``/`` `or` ``/`` `not` ``), `Std.Decision` (`Empty`), `Std.Proof.IntMath` (`IsTrue`/`Confirmed`).
- Produces (module `Std.Proof.BooleanReflection`):
  - `left_operand_is_true_from_true_conjunction({left: Bool}, {right: Bool}, conjunction_is_true: IsTrue(`and`(left, right))) -> IsTrue(left)`
  - `right_operand_is_true_from_true_conjunction(...) -> IsTrue(right)`
  - `@lemma conjunction_is_true_when_both_operands_are({left}, {right}, left_is_true: IsTrue(left), right_is_true: IsTrue(right)) -> IsTrue(`and`(left, right))`
  - `@lemma disjunction_is_true_from_left_operand({left}, {right}, left_is_true: IsTrue(left)) -> IsTrue(`or`(left, right))`
  - `@lemma disjunction_is_true_from_right_operand({left}, {right}, right_is_true: IsTrue(right)) -> IsTrue(`or`(left, right))`
  - `true_negation_contradicts_truth({claim: Bool}, negation_is_true: IsTrue(`not`(claim)), claim_is_true: IsTrue(claim)) -> Empty`

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/stdlib/proof_boolean_reflection_test.exs
defmodule Cure.Stdlib.ProofBooleanReflectionTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  @moduletag :stdlib

  # A client module that USES each connective lemma, so the whole file only
  # elaborates if every signature and proof term kernel-checks.
  @client """
  mod BooleanReflectionClient
    use Std.Bool
    use Std.Decision
    use Std.Proof.IntMath
    use Std.Proof.BooleanReflection

    fn split_left(both: IsTrue(`and`(True(), True()))) -> IsTrue(True()) =
      left_operand_is_true_from_true_conjunction(both)

    fn split_right(both: IsTrue(`and`(True(), True()))) -> IsTrue(True()) =
      right_operand_is_true_from_true_conjunction(both)

    fn combine(l: IsTrue(True()), r: IsTrue(True())) -> IsTrue(`and`(True(), True())) =
      conjunction_is_true_when_both_operands_are(l, r)

    fn from_left(l: IsTrue(True())) -> IsTrue(`or`(True(), False())) =
      disjunction_is_true_from_left_operand(l)

    fn from_right(r: IsTrue(True())) -> IsTrue(`or`(False(), True())) =
      disjunction_is_true_from_right_operand(r)

    fn contradiction(neg: IsTrue(`not`(True())), pos: IsTrue(True())) -> Empty =
      true_negation_contradicts_truth(neg, pos)
  end
  """

  test "the boolean-connective algebra elaborates and every lemma kernel-checks" do
    assert {:ok, _env} = Program.elaborate(@client)
  end
end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/cure/stdlib/proof_boolean_reflection_test.exs`
Expected: FAIL — module `Std.Proof.BooleanReflection` does not resolve (unknown module / unbound names).

- [ ] **Step 3: Write the module**

```
# lib/std/proof_boolean_reflection.cure
@group(:core)
mod Std.Proof.BooleanReflection
  ## Boolean-connective algebra over `IsTrue` (constructive, zero trust).
  ##
  ## `IsTrue` reflects `Bool`, and `Std.Bool`'s connectives reduce definitionally
  ## (`and`(True(), b) ≡ b), so these lemmas are proved by matching the reducing
  ## operand. They never inspect what a comparison *means* — they serve `Int` and
  ## `Nat` obligations alike. Uninhabited arms are discharged by an empty match on
  ## the evidence, exactly like `Std.Proof.IntMath.true_is_not_false`.

  use Std.Bool
  use Std.Decision
  use Std.Proof.IntMath

  ## Split a true conjunction into its left operand's truth.
  fn left_operand_is_true_from_true_conjunction(
    {left: Bool},
    {right: Bool},
    conjunction_is_true: IsTrue(`and`(left, right))
  ) -> IsTrue(left) = match left
    True()  -> Confirmed()
    False() -> match conjunction_is_true

  ## Split a true conjunction into its right operand's truth.
  fn right_operand_is_true_from_true_conjunction(
    {left: Bool},
    {right: Bool},
    conjunction_is_true: IsTrue(`and`(left, right))
  ) -> IsTrue(right) = match left
    True()  -> conjunction_is_true
    False() -> match conjunction_is_true

  ## Combine two truths into the truth of their conjunction.
  @lemma
  fn conjunction_is_true_when_both_operands_are(
    {left: Bool},
    {right: Bool},
    left_is_true: IsTrue(left),
    right_is_true: IsTrue(right)
  ) -> IsTrue(`and`(left, right)) = match left
    True()  -> right_is_true
    False() -> match left_is_true

  ## Either operand's truth suffices for a disjunction.
  @lemma
  fn disjunction_is_true_from_left_operand(
    {left: Bool}, {right: Bool}, left_is_true: IsTrue(left)
  ) -> IsTrue(`or`(left, right)) = match left
    True()  -> Confirmed()
    False() -> match left_is_true

  @lemma
  fn disjunction_is_true_from_right_operand(
    {left: Bool}, {right: Bool}, right_is_true: IsTrue(right)
  ) -> IsTrue(`or`(left, right)) = match left
    True()  -> Confirmed()
    False() -> right_is_true

  ## A claim and its negation cannot both hold.
  fn true_negation_contradicts_truth(
    {claim: Bool},
    negation_is_true: IsTrue(`not`(claim)),
    claim_is_true: IsTrue(claim)
  ) -> Empty = match claim
    True()  -> match negation_is_true
    False() -> match claim_is_true
end
```

Note on the `match left` in `left_operand_is_true_from_true_conjunction`: `left` is an erased implicit but is in scope as a term; matching it refines `` `and`(left, right) `` in the evidence type (`` `and`(True(), right) ≡ right``, `` `and`(False(), right) ≡ False()``). If the elaborator rejects matching on an erased implicit here, promote `left`/`right` to explicit `left: Bool, right: Bool` (the automation in Task 6 is unaffected — telescope slots are solved by conclusion-unification regardless of implicit/explicit). Prefer implicit; fall back to explicit only if the match is rejected.

- [ ] **Step 4: Re-stage the stdlib, then run the test to verify it passes**

Run: `mix cure.bundle_stdlib && mix test test/cure/stdlib/proof_boolean_reflection_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add -- lib/std/proof_boolean_reflection.cure test/cure/stdlib/proof_boolean_reflection_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(std): boolean-connective algebra over IsTrue" -- lib/std/proof_boolean_reflection.cure test/cure/stdlib/proof_boolean_reflection_test.exs
```

---

### Task 2: Layer 2a — Bool-valued natural-number comparisons in `Std.Proof.Math`

**Files:**
- Modify: `lib/std/proof_math.cure` (add imports + three functions; append before `end`)
- Test: `test/cure/stdlib/proof_math_test.exs` (add cases; do not alter existing ones)

**Interfaces:**
- Consumes: `Std.Bool` (`Bool`/`True`/`False`), `Std.Nat` (`Nat`/`Z`/`S`).
- Produces (in `Std.Proof.Math`):
  - `natural_is_less_than_or_equal(left: Nat, right: Nat) -> Bool`
  - `natural_is_less_than(left: Nat, right: Nat) -> Bool` ( `= natural_is_less_than_or_equal(S(left), right)` )
  - `natural_is_positive(value: Nat) -> Bool`

- [ ] **Step 1: Write the failing test** (append to `test/cure/stdlib/proof_math_test.exs`)

```elixir
  test "boolean-valued Nat comparisons reduce correctly" do
    src = """
    mod NatComparisonClient
      use Std.Bool
      use Std.Nat
      use Std.Proof.Math

      # Each equality holds only if the comparison reduces as intended.
      fn lte_true() -> IsTrue(natural_is_less_than_or_equal(S(Z()), S(S(Z())))) = Confirmed()
      fn lt_true() -> IsTrue(natural_is_less_than(S(Z()), S(S(Z())))) = Confirmed()
      fn positive_true() -> IsTrue(natural_is_positive(S(Z()))) = Confirmed()
    end
    """
    # Confirmed() only type-checks if each comparison reduces to True().
    assert {:ok, _env} = Cure.Elab.Program.elaborate(add_is_true_import(src))
  end
```

Use whatever import the file already uses for `IsTrue`/`Confirmed` (`use Std.Proof.IntMath`); if the test module needs it, add `use Std.Proof.IntMath` to the `src` module header directly rather than a helper. (Inline the import in `src`; the `add_is_true_import` reference above is illustrative — write `use Std.Proof.IntMath` into the module.)

- [ ] **Step 2: Run to verify it fails**

Run: `mix test test/cure/stdlib/proof_math_test.exs`
Expected: FAIL — `natural_is_less_than_or_equal` unbound.

- [ ] **Step 3: Implement** — add to the top of `lib/std/proof_math.cure` imports:

```
  use Std.Bool
  use Std.Proof.IntMath
```

and append these three functions before the final `end`:

```
  ## Boolean-valued "less than or equal", structural on both operands.
  fn natural_is_less_than_or_equal(left: Nat, right: Nat) -> Bool = match left
    Z() -> True()
    S(left_predecessor) -> match right
      Z() -> False()
      S(right_predecessor) -> natural_is_less_than_or_equal(left_predecessor, right_predecessor)

  ## Boolean-valued strict "less than".
  fn natural_is_less_than(left: Nat, right: Nat) -> Bool =
    natural_is_less_than_or_equal(S(left), right)

  ## Boolean-valued positivity.
  fn natural_is_positive(value: Nat) -> Bool = match value
    Z() -> False()
    S(predecessor) -> True()
```

- [ ] **Step 4: Re-stage + run to verify it passes**

Run: `mix cure.bundle_stdlib && mix test test/cure/stdlib/proof_math_test.exs`
Expected: PASS (new + existing cases).

- [ ] **Step 5: Commit**

```bash
git add -- lib/std/proof_math.cure test/cure/stdlib/proof_math_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(std): boolean-valued Nat comparisons" -- lib/std/proof_math.cure test/cure/stdlib/proof_math_test.exs
```

---

### Task 3: Layer 2b — Nat reflection lemmas (both directions)

**Files:**
- Modify: `lib/std/proof_math.cure` (append reflection lemmas before `end`)
- Test: `test/cure/stdlib/proof_math_test.exs` (add cases)

**Interfaces:**
- Consumes: Task 2's comparisons; the existing `IsPositive`/`IsLessThan`/`IsLessThanOrEqual` families and their constructors; `IsTrue`/`Confirmed`.
- Produces (in `Std.Proof.Math`), each pair a reflection direction. Tag ONLY the `…_holds_when_boolean_comparison_is_true` (forward) direction `@lemma`; leave the reverse untagged:
  - `@lemma less_than_or_equal_holds_when_boolean_comparison_is_true(left: Nat, right: Nat, evidence: IsTrue(natural_is_less_than_or_equal(left, right))) -> IsLessThanOrEqual(left, right)`
  - `boolean_comparison_is_true_when_less_than_or_equal_holds({left: Nat}, {right: Nat}, proof: IsLessThanOrEqual(left, right)) -> IsTrue(natural_is_less_than_or_equal(left, right))`
  - `@lemma less_than_holds_when_boolean_comparison_is_true(left: Nat, right: Nat, evidence: IsTrue(natural_is_less_than(left, right))) -> IsLessThan(left, right)`
  - `boolean_comparison_is_true_when_less_than_holds({left: Nat}, {right: Nat}, proof: IsLessThan(left, right)) -> IsTrue(natural_is_less_than(left, right))`
  - `@lemma positive_holds_when_boolean_comparison_is_true(value: Nat, evidence: IsTrue(natural_is_positive(value))) -> IsPositive(value)`
  - `boolean_comparison_is_true_when_positive_holds({value: Nat}, proof: IsPositive(value)) -> IsTrue(natural_is_positive(value))`

- [ ] **Step 1: Write the failing test** (append to `proof_math_test.exs`)

```elixir
  test "Nat reflection lemmas round-trip between boolean and inductive forms" do
    src = """
    mod NatReflectionClient
      use Std.Bool
      use Std.Nat
      use Std.Proof.IntMath
      use Std.Proof.Math

      # 1 < 2 obtained through the boolean surface, then reflected back.
      fn lt_from_bool() -> IsLessThan(S(Z()), S(S(Z()))) =
        less_than_holds_when_boolean_comparison_is_true(S(Z()), S(S(Z())), Confirmed())

      fn bool_from_lt(proof: IsLessThan(S(Z()), S(S(Z())))) ->
          IsTrue(natural_is_less_than(S(Z()), S(S(Z())))) =
        boolean_comparison_is_true_when_less_than_holds(proof)

      fn positive_from_bool() -> IsPositive(S(Z())) =
        positive_holds_when_boolean_comparison_is_true(S(Z()), Confirmed())
    end
    """
    assert {:ok, _env} = Cure.Elab.Program.elaborate(src)
  end
```

- [ ] **Step 2: Run to verify it fails**

Run: `mix test test/cure/stdlib/proof_math_test.exs`
Expected: FAIL — reflection lemmas unbound.

- [ ] **Step 3: Implement** — append before the final `end` of `lib/std/proof_math.cure`:

```
  ## Reflection: the boolean comparison being true carries the same information as
  ## the inductive relation. Proved by induction, mirroring the boolean function's
  ## own match structure; uninhabited arms discharge by empty match on `evidence`.
  @lemma
  fn less_than_or_equal_holds_when_boolean_comparison_is_true(
    left: Nat, right: Nat,
    evidence: IsTrue(natural_is_less_than_or_equal(left, right))
  ) -> IsLessThanOrEqual(left, right) = match left
    Z() -> ZeroIsLessThanOrEqual()
    S(left_predecessor) -> match right
      Z() -> match evidence
      S(right_predecessor) -> SuccessorsAreLessThanOrEqual(
        less_than_or_equal_holds_when_boolean_comparison_is_true(left_predecessor, right_predecessor, evidence))

  fn boolean_comparison_is_true_when_less_than_or_equal_holds(
    {left: Nat}, {right: Nat},
    proof: IsLessThanOrEqual(left, right)
  ) -> IsTrue(natural_is_less_than_or_equal(left, right)) = match proof
    ZeroIsLessThanOrEqual() -> Confirmed()
    SuccessorsAreLessThanOrEqual(inner) ->
      boolean_comparison_is_true_when_less_than_or_equal_holds(inner)

  @lemma
  fn less_than_holds_when_boolean_comparison_is_true(
    left: Nat, right: Nat,
    evidence: IsTrue(natural_is_less_than(left, right))
  ) -> IsLessThan(left, right) = match right
    Z() -> match evidence
    S(right_predecessor) -> match left
      Z() -> ZeroIsLessThanSuccessor()
      S(left_predecessor) -> SuccessorsAreLessThan(
        less_than_holds_when_boolean_comparison_is_true(left_predecessor, right_predecessor, evidence))

  fn boolean_comparison_is_true_when_less_than_holds(
    {left: Nat}, {right: Nat},
    proof: IsLessThan(left, right)
  ) -> IsTrue(natural_is_less_than(left, right)) = match proof
    ZeroIsLessThanSuccessor() -> Confirmed()
    SuccessorsAreLessThan(inner) ->
      boolean_comparison_is_true_when_less_than_holds(inner)

  @lemma
  fn positive_holds_when_boolean_comparison_is_true(
    value: Nat,
    evidence: IsTrue(natural_is_positive(value))
  ) -> IsPositive(value) = match value
    Z() -> match evidence
    S(predecessor) -> PositiveSuccessor()

  fn boolean_comparison_is_true_when_positive_holds(
    {value: Nat},
    proof: IsPositive(value)
  ) -> IsTrue(natural_is_positive(value)) = match proof
    PositiveSuccessor() -> Confirmed()
```

If the elaborator rejects `match evidence` in an arm where it cannot see the index reduces to `False()` (i.e. it does not refine `evidence`'s type on the `right`/`value` split), route through the existing ex-falso helper instead: `true_is_not_false(evidence)` gives `Empty`, then empty-match it — but first confirm reduction is the issue by dumping the normal form. Do NOT introduce a kernel change to force the reduction (hard-stop).

- [ ] **Step 4: Re-stage + run to verify it passes**

Run: `mix cure.bundle_stdlib && mix test test/cure/stdlib/proof_math_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add -- lib/std/proof_math.cure test/cure/stdlib/proof_math_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(std): Nat reflection lemmas bridging boolean and inductive comparison" -- lib/std/proof_math.cure test/cure/stdlib/proof_math_test.exs
```

---

### Task 4: `Std.Nat.to_integer` — the free Nat → Int projection

**Files:**
- Modify: `lib/std/nat.cure` (append before final line)
- Test: `test/cure/stdlib/nat_to_integer_test.exs` (create)

**Interfaces:**
- Produces: `to_integer(value: Nat) -> Int` — structural fold, total, non-`@extern`.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/stdlib/nat_to_integer_test.exs
defmodule Cure.Stdlib.NatToIntegerTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program
  @moduletag :stdlib

  test "to_integer is a total structural fold, not an FFI boundary" do
    src = """
    mod ToIntegerClient
      use Std.Nat
      fn three() -> Int = to_integer(S(S(S(Z()))))
    end
    """
    assert {:ok, env} = Program.elaborate(src)
    # Guard: to_integer must have a real body (structural), not an @extern stub.
    to_int = Enum.find(Map.values(env.defs), fn d ->
      is_map(d) and Map.get(d, :name) |> to_string() |> String.ends_with?("to_integer")
    end)
    assert to_int != nil
    assert Map.get(to_int, :body) not in [nil, :extern]
  end
end
```

If `env.defs` shape or the extern marker differs, adapt the guard after inspecting one existing structural def vs. the `of_int` extern def in `env.defs` — the behavioral intent is: `to_integer` has a Core body, `of_int` does not. Keep the elaboration assertion regardless.

- [ ] **Step 2: Run to verify it fails**

Run: `mix test test/cure/stdlib/nat_to_integer_test.exs`
Expected: FAIL — `to_integer` unbound.

- [ ] **Step 3: Implement** — append to `lib/std/nat.cure`:

```
  ## Project a natural number to a machine integer (structural, total; the
  ## constructive inverse of the trusted `of_int` clamp — this direction needs no
  ## assertion because `Nat` is well-founded).
  fn to_integer(value: Nat) -> Int = match value
    Z() -> 0
    S(predecessor) -> to_integer(predecessor) + 1
```

- [ ] **Step 4: Re-stage + run to verify it passes**

Run: `mix cure.bundle_stdlib && mix test test/cure/stdlib/nat_to_integer_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add -- lib/std/nat.cure test/cure/stdlib/nat_to_integer_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(std): total Nat to Int projection" -- lib/std/nat.cure test/cure/stdlib/nat_to_integer_test.exs
```

---

### Task 5: Elaborator — refinement→base projection coercion (item c)

**Files:**
- Modify: `lib/cure/elab/elaborator.ex` (the `:no` branch of `elaborate_expr_checked_fallback/5`, around line 1998–2005; build the projection directly from Core terms — do NOT reuse `sigma_projection/5` at line ~1201, which expects surface AST, not an already-elaborated term)
- Test: `test/cure/elab/refinement_base_projection_test.exs` (create)

**Interfaces:**
- Behavior: when checking `expr` against a base type `T`, and `expr` infers to a Sigma refinement `Sigma(T, λx. φ)` whose first component's type is convertible to `T`, insert the kernel builtin first projection (`sigma_first`) so the refined value is usable directly as its base type.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/elab/refinement_base_projection_test.exs
defmodule Cure.Elab.RefinementBaseProjectionTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  # A positive natural (a Sigma refinement) used where a base Nat is expected.
  @client """
  mod RefinementBaseClient
    use Std.Nat
    use Std.Proof.Math
    use Std.Refine

    fn underlying(p: PositiveNatural) -> Nat = p
  end
  """

  test "a refined value is usable directly where its base type is expected" do
    assert {:ok, _env} = Program.elaborate(@client)
  end

  @mismatch """
  mod RefinementBaseMismatch
    use Std.Nat
    use Std.Bool
    use Std.Refine
    use Std.Proof.Math

    fn wrong(p: PositiveNatural) -> Bool = p
  end
  """

  test "the coercion does not paper over a genuine type mismatch" do
    assert {:error, _} = Program.elaborate(@mismatch)
  end
end
```

The test asserts a `PositiveNatural` fed to a `Bool`-returning function still fails.

- [ ] **Step 2: Run to verify it fails**

Run: `mix test test/cure/elab/refinement_base_projection_test.exs`
Expected: `underlying` FAILs today with a `:conversion_failure` (Sigma vs. base `Nat`); the mismatch test passes already.

- [ ] **Step 3: Implement** — in `elaborate_expr_checked_fallback/5`, in the `:no` branch, after inferring `{:ok, term, type}` and before/around the `maybe_inject_union` + `Kernel.check`, add a refined→base coercion attempt. Add a private helper and call it:

```elixir
        :no ->
          with {:ok, term, type} <- elaborate_expr_typed(expr, names, ctx, env) do
            term = maybe_inject_union(term, type, expected_core, ctx, env)
            term = maybe_coerce_refined_to_base(term, type, expected_core, ctx, env)

            with :ok <- Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
              {:ok, term}
            end
          end
```

**IMPORTANT — do not call `sigma_projection/5` here.** `term`/`type` at this point are already-ELABORATED: `term` is a Core term and `type` is the semantic Value `elaborate_expr_typed/4` returned (the same pair `maybe_inject_union/5` just consumed above via `Quote.reify(type, ...)`  — read its body around line 2098 for the precedent). `sigma_projection/5`'s own doc comment (elaborator.ex:1196-1200) is explicit that its `inner` parameter must be **surface AST**, which it re-elaborates itself via `elaborate_implicit_global_app` → `elaborate_expr_typed`; handing it an already-built Core term feeds a Core tuple where a parser-AST node is expected. Instead, build the projection application directly from the Core pieces you already have — exactly how `proof_search.ex`'s `sigma_second_of/5` (line ~175) builds `refinement_proof`'s application from `sigma_params/3`'s already-pinned `a_value`/`predicate_value`, via `Quote.reify` + a `build_app` fold:

```elixir
  # If `term`'s inferred `type` WHNFs to the Sigma refinement family and the
  # expected base type is convertible to the Sigma's first-component type, coerce
  # by inserting the first projection (`sigma_first`, or `Std.Refine.refined_value`
  # when that idiomatic accessor is in scope) — the reverse of the base->refined
  # injection. This is the ONLY new behavior; if the shapes don't match, return
  # `term` unchanged so ordinary checking (and its error) stands.
  #
  # `type` is a semantic VALUE here (not a Core term — see the call site), so it
  # is inspected with `Normalise.whnf_value/2` (mirror `sigma_params/3` in
  # proof_search.ex), never `Kernel.normalize/2` (which expects a Core term and
  # matches `:data`, not `:vdata`).
  defp maybe_coerce_refined_to_base(term, type, expected_core, ctx, env) do
    sigma_fam = Inductive.builtin(env, :sigma)
    depth = Context.length(ctx)
    sig = Context.signature(ctx)

    with false <- is_nil(sigma_fam),
         {:vdata, ^sigma_fam, [dom_value, predicate_value]} <- Normalise.whnf_value(type, sig),
         # Do not coerce when the expected type is itself that Sigma (no coercion
         # needed) — only when expected is the base component type.
         false <- sigma_typed?(expected_core, sigma_fam, ctx),
         dom_term <- Quote.reify(dom_value, depth, sig),
         true <- convertible?(dom_term, expected_core, ctx, env) do
      predicate_term = Quote.reify(predicate_value, depth, sig)
      build_app({:global, first_projection_head(env)}, [dom_term, predicate_term, term])
    else
      _ -> term
    end
  end

  # The global to head the first projection with: `Std.Refine.refined_value` when
  # the refinement API is in scope (the idiomatic accessor a human writes,
  # mirroring `refinement_proof`), else the kernel builtin `sigma_first`. Mirror
  # `second_projection_head/1` in `proof_search.ex` EXACTLY: nil-check via
  # `Env.get_def` FIRST. `Env.resolve_key/3` itself never returns `nil` — its
  # `@spec` is `:: atom()`; an unresolved name falls back to the bare input atom
  # unchanged, so calling `resolve_key` before confirming the def exists would
  # silently hand back a nonexistent global instead of the intended fallback.
  defp first_projection_head(env) do
    case Env.get_def(env, "refined_value") do
      nil -> :sigma_first
      _def -> Env.resolve_key(env, env.defs, "refined_value")
    end
  end

  # Same one-line fold `proof_search.ex` uses (line ~303) to assemble a curried
  # application from a head and an argument list.
  defp build_app(head, args), do: Enum.reduce(args, head, fn a, f -> {:app, f, a} end)
```

Implement the remaining small predicate next to the helper:
- `sigma_typed?(expected_core, sigma_fam, ctx)` — `expected_core` really is a Core term here (it is the function's own `expected_core` parameter, never assigned from `elaborate_expr_typed`), so `Kernel.normalize/2` is the right tool: `match? {:data, ^sigma_fam, _, []}, Kernel.normalize(ctx, expected_core)`.
- `convertible?(a_term, b_term, ctx, env)` — both arguments here are Core terms (`dom_term` was just reified; `expected_core` always was one) — call the existing kernel conversion (`Cure.Core.Conv.conv?/5` as used in `proof_search.ex:317`, which "takes Core terms and evaluates them itself, so pass the terms directly, not pre-evaled" per that file's own comment) or the elaborator's existing conversion entry point if one already wraps it — grep `elaborator.ex` for how it already compares two Core types and reuse that; do NOT hand-roll normalization.

`Context`, `Env`, `Normalise`, `Quote`, `Inductive`, `Kernel` are all already aliased at the top of `elaborator.ex` (line 16) — use the short forms shown above, not fully-qualified names.

- [ ] **Step 4: Run to verify it passes**

Run: `mix test test/cure/elab/refinement_base_projection_test.exs`
Expected: PASS (both tests).

- [ ] **Step 5: Guard against regressions in existing refinement tests**

Run: `mix test test/cure/elab/refinement_autodischarge_test.exs test/cure/elab/refinement_sugar_test.exs test/cure/stdlib/refine_test.exs`
Expected: PASS (the new coercion must not perturb base→refined discharge).

- [ ] **Step 6: Commit**

```bash
git add -- lib/cure/elab/elaborator.ex test/cure/elab/refinement_base_projection_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): coerce refinement value to its base type via sigma_first" -- lib/cure/elab/elaborator.ex test/cure/elab/refinement_base_projection_test.exs
```

---

### Task 6: ProofSearch — conjunction-elimination candidate source + reflection auto-discharge

**Files:**
- Modify: `lib/cure/elab/proof_search.ex` (add `conjunction_candidates/3`, wire into the `candidates` list in `resolve/4` at line ~51–54)
- Test: `test/cure/elab/conjunction_saturation_test.exs` (create); `test/cure/elab/nat_reflection_discharge_test.exs` (create)

**Interfaces:**
- Behavior A (reflection, no code change — verification only): an open proof hole with goal `IsLessThan(a, b)` and a local hypothesis `IsTrue(natural_is_less_than(a, b))` discharges via the `@lemma`-tagged `less_than_holds_when_boolean_comparison_is_true` through the existing `lemma_candidates` path.
- Behavior B (new): a proof hole with goal `IsTrue(left)` and a local hypothesis of type `IsTrue(`and`(left, right))` discharges by applying `left_operand_is_true_from_true_conjunction` (and symmetrically `right`), a new candidate source mirroring `projection_candidates/3`.

- [ ] **Step 1: Write the failing tests**

```elixir
# test/cure/elab/nat_reflection_discharge_test.exs
defmodule Cure.Elab.NatReflectionDischargeTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  defp has_hole?({:hole, _}), do: true
  defp has_hole?(t) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&has_hole?/1)
  defp has_hole?(l) when is_list(l), do: Enum.any?(l, &has_hole?/1)
  defp has_hole?(m) when is_map(m), do: m |> Map.values() |> Enum.any?(&has_hole?/1)
  defp has_hole?(_), do: false

  @src """
  mod NatReflectionDischarge
    use Std.Nat
    use Std.Proof.IntMath
    use Std.Proof.Math

    fn derive({a: Nat}, {b: Nat}, e: IsTrue(natural_is_less_than(a, b))) -> IsLessThan(a, b) = ?
  end
  """

  test "an IsLessThan goal is auto-discharged from an IsTrue(<) hypothesis via the tagged reflection lemma" do
    assert {:ok, env} = Program.elaborate(@src)
    derive = Enum.find(Map.values(env.defs), fn d ->
      is_map(d) and to_string(Map.get(d, :name)) |> String.ends_with?("derive")
    end)
    refute has_hole?(derive.body), "reflection lemma should have filled the hole"
  end
end
```

```elixir
# test/cure/elab/conjunction_saturation_test.exs
defmodule Cure.Elab.ConjunctionSaturationTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  defp has_hole?({:hole, _}), do: true
  defp has_hole?(t) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&has_hole?/1)
  defp has_hole?(l) when is_list(l), do: Enum.any?(l, &has_hole?/1)
  defp has_hole?(m) when is_map(m), do: m |> Map.values() |> Enum.any?(&has_hole?/1)
  defp has_hole?(_), do: false

  @src """
  mod ConjunctionSaturation
    use Std.Bool
    use Std.Proof.IntMath
    use Std.Proof.BooleanReflection

    fn pick_left({p: Bool}, {q: Bool}, both: IsTrue(`and`(p, q))) -> IsTrue(p) = ?
  end
  """

  test "an IsTrue(left) goal is discharged from an IsTrue(and(left,right)) hypothesis" do
    assert {:ok, env} = Program.elaborate(@src)
    f = Enum.find(Map.values(env.defs), fn d ->
      is_map(d) and to_string(Map.get(d, :name)) |> String.ends_with?("pick_left")
    end)
    refute has_hole?(f.body), "conjunction elimination should have filled the hole"
  end
end
```

- [ ] **Step 2: Run to verify they fail**

Run: `mix cure.bundle_stdlib && mix test test/cure/elab/nat_reflection_discharge_test.exs test/cure/elab/conjunction_saturation_test.exs`
Expected: `nat_reflection_discharge` — **may already pass** (the tagged lemma from Task 3 is enough; if so, keep it as a regression test and note it passed without new code). `conjunction_saturation` — FAILS (hole survives; no candidate source applies the elimination lemmas).

If `nat_reflection_discharge` fails instead, diagnose whether the reflection lemma's explicit `left`/`right` args are being solved by conclusion-unification; that is the intended path (see `try_lemma`/`fill_args`). Do not add a bespoke solver — the tag + generic `lemma_candidates` must suffice.

- [ ] **Step 3: Implement `conjunction_candidates/3`** in `proof_search.ex`, and add it to the `candidates` list:

```elixir
      candidates =
        local_candidates(goal, ctx, env) ++
          projection_candidates(goal, ctx, env) ++
          conjunction_candidates(goal, ctx, env) ++
          lemma_ok
```

```elixir
  # Conjunction-elimination search: for every local binder whose type WHNFs to
  # `IsTrue(and(left, right))`, both operand-projection lemmas
  # (`left_operand_is_true_from_true_conjunction` / `right_...`) yield a proof of
  # `IsTrue(left)` / `IsTrue(right)` respectively. Each assembled application is
  # kernel-checked against the goal, so a non-matching operand simply drops out.
  # This is the "context saturation" of the design, realized as a candidate
  # source (no context mutation, no backtracking) — the exact shape of
  # `projection_candidates/3`.
  defp conjunction_candidates(goal, ctx, env) do
    goal_val = Eval.eval(goal, Context.env(ctx))
    len = Context.length(ctx)

    for k <- 0..(len - 1)//1, len > 0, {head_name, arg_terms} <- is_true_and_binder(Context.lookup(ctx, k), ctx, env) do
      # arg_terms are the reified [left, right] indices of the and(...) inside IsTrue.
      for {global, prov} <- [
            {and_left_projection_head(env), {:conj_left, k}},
            {and_right_projection_head(env), {:conj_right, k}}
          ],
          global != nil do
        term = build_app({:global, global}, arg_terms ++ [{:var, k}])

        case Kernel.check(ctx, term, goal_val) do
          :ok -> {term, prov}
          _ -> {nil, prov}
        end
      end
    end
    |> List.flatten()
    |> Enum.filter(fn {term, _} -> term != nil end)
  end
```

Implement the three small helpers:
- `is_true_and_binder(type, ctx, env)` — returns `[{:and, [left_term, right_term]}]` when `type` WHNFs to `{:vdata, IsTrue_fam, [claim_value]}` (a semantic Value — use `Normalise.whnf_value/2`, mirroring `sigma_params/3`, never `Kernel.normalize/2`) and `claim_value` itself WHNFs to the two-argument `and`-application spine; else `[]`. Resolve the `IsTrue` family and the `and` global via `Env.get_def`/`Inductive.builtin` the same way `second_projection_head/1` resolves `refinement_proof`.
- `and_left_projection_head(env)` / `and_right_projection_head(env)` — mirror `second_projection_head/1` (`proof_search.ex:185`) EXACTLY, do not call `Env.resolve_key` directly: `case Env.get_def(env, "left_operand_is_true_from_true_conjunction") do nil -> nil; _def -> Env.resolve_key(env, env.defs, "left_operand_is_true_from_true_conjunction") end` (and the `right_` variant). This nil-checks via `get_def` FIRST so the source stays inert unless `Std.Proof.BooleanReflection` is in scope. `Env.resolve_key/3` itself is spec'd `:: atom()` and never returns `nil` — called directly (without the `get_def` guard) on a name nothing defines, it falls back to returning the bare, unbound input atom, which is not the `nil` this candidate source's `global != nil` filter (Step 3) needs to drop an out-of-scope source.

The two elimination lemmas take `{left}`,`{right}` erased implicits then the evidence; supplying `arg_terms ++ [binder]` provides the reified implicits explicitly (as `sigma_second_of/5` does for `refinement_proof`). If passing erased implicits positionally is rejected, follow exactly how `sigma_second_of/5` reifies and applies `refinement_proof`'s implicits and copy that calling convention.

- [ ] **Step 4: Run to verify they pass**

Run: `mix test test/cure/elab/nat_reflection_discharge_test.exs test/cure/elab/conjunction_saturation_test.exs`
Expected: PASS.

- [ ] **Step 5: Guard the existing proof-search suite**

Run: `mix test test/cure/elab/proof_search_test.exs test/cure/elab/proof_hole_resolution_test.exs test/cure/elab/proof_search_registry_test.exs test/cure/elab/lemma_decorator_test.exs`
Expected: PASS (the new candidate source must not introduce ambiguity or regress existing resolution).

- [ ] **Step 6: Commit**

```bash
git add -- lib/cure/elab/proof_search.ex test/cure/elab/nat_reflection_discharge_test.exs test/cure/elab/conjunction_saturation_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): conjunction-elimination candidate source in proof search" -- lib/cure/elab/proof_search.ex test/cure/elab/nat_reflection_discharge_test.exs test/cure/elab/conjunction_saturation_test.exs
```

---

### Task 7: Differential-oracle probes (refine03/04/05)

**Files:**
- Create: `test/oracle/refine/refine03_boolean_and.cure` + `.idr`; `refine04_boolean_or.cure` + `.idr`; `refine05_nat_reflection.cure` + `.idr`
- Modify: `test/oracle/refine/verdicts.json` (add three name-keyed entries)

**Interfaces:**
- Each `.cure`/`.idr` pair expresses the SAME program (faithful transliteration). Relation `same`, both `accept`.

- [ ] **Step 1: Author the pairs**

`refine03_boolean_and.cure` — derive both operands of a true conjunction:
```
mod Refine03
  use Std.Bool
  use Std.Proof.IntMath
  use Std.Proof.BooleanReflection
  fn both(p: IsTrue(`and`(True(), True()))) -> IsTrue(True()) =
    left_operand_is_true_from_true_conjunction(p)
end
```
`refine03_boolean_and.idr` (no `module` line, `%default total` on its own line after the import — match `refine01_is_true.idr`'s exact layout) — the Idris `Data.So` analogue:
```
import Data.So

%default total

splitLeft : So (True && True) -> So True
splitLeft x = case soAnd x of (l, _) => l
```
Verified against the on-disk Idris base (`~/Develop/Idris2/libs/base/Data/So.idr`): the elimination function is `soAnd : {a : Bool} -> So (a && b) -> (So a, So b)` — it destructures a conjunction proof into a pair, which is the direction this probe needs. `andSo : (So a, So b) -> So (a && b)` is the opposite (introduction) direction — it takes a pair and produces the conjunction, so it cannot be applied to `x : So (True && True)` as in an earlier draft of this probe; use `soAnd`, not `andSo`.

`refine04_boolean_or.{cure,idr}` — disjunction introduction from the left operand (Cure `disjunction_is_true_from_left_operand`; Idris `orSo`/`Left`-injection analogue).

`refine05_nat_reflection.{cure,idr}` — `1 < 2` via the boolean surface reflected to the inductive relation (Cure `less_than_holds_when_boolean_comparison_is_true`; Idris `Data.Nat` `LT` from a decision / `Data.So` on `lt`).

- [ ] **Step 2: Run the oracle to generate verdicts**

Run: `mix cure.oracle refine`
Expected: writes `refine03/04/05` entries into `test/oracle/refine/verdicts.json`; each should be `{"cure":"accept","idris":"accept","relation":"same"}`.

- [ ] **Step 3: Triage** — if any entry diverges (`cure` ≠ `idris`), STOP and diagnose. A `cure:reject`/`idris:accept` means the Cure transliteration or a lemma is wrong (fix the `.cure`/lemma, not the verdict). A `cure:accept`/`idris:reject` is a soundness surprise — STOP and report. Never hand-edit a verdict.

- [ ] **Step 4: Replay to confirm frozen-green**

Run: `mix test test/oracle_replay_test.exs`
Expected: PASS (all `refine` entries, old and new, replay to their recorded verdicts).

- [ ] **Step 5: Commit**

```bash
git add -- test/oracle/refine/refine03_boolean_and.cure test/oracle/refine/refine03_boolean_and.idr test/oracle/refine/refine04_boolean_or.cure test/oracle/refine/refine04_boolean_or.idr test/oracle/refine/refine05_nat_reflection.cure test/oracle/refine/refine05_nat_reflection.idr test/oracle/refine/verdicts.json
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "test(oracle): boolean-connective and Nat-reflection differential probes" -- test/oracle/refine/refine03_boolean_and.cure test/oracle/refine/refine03_boolean_and.idr test/oracle/refine/refine04_boolean_or.cure test/oracle/refine/refine04_boolean_or.idr test/oracle/refine/refine05_nat_reflection.cure test/oracle/refine/refine05_nat_reflection.idr test/oracle/refine/verdicts.json
```

---

### Task 8: Layer 3 worked example + full gate

**Files:**
- Modify: `lib/std/refine.cure` (add a documented `decide_is_true`-at-boundary example, OR add it as a test-only fixture if it would widen the stdlib surface undesirably — prefer a test fixture to keep the stdlib lean)
- Test: `test/cure/stdlib/decide_at_boundary_test.exs` (create)

**Interfaces:**
- Behavior: a worked demonstration that an external `Int` is checked (not asserted) with `decide_is_true`, and the `Yes` branch carries kernel-valid `IsTrue(...)` evidence inward; both branches type-check.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/stdlib/decide_at_boundary_test.exs
defmodule Cure.Stdlib.DecideAtBoundaryTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program
  @moduletag :stdlib

  @src """
  mod DecideAtBoundary
    use Std.Bool
    use Std.Decision
    use Std.Proof.IntMath

    # An external Int is DECIDED, not asserted; the Yes branch carries evidence.
    fn classify(external_value: Int) -> Bool =
      match decide_is_true(external_value > 0)
        Yes(evidence) -> True()
        No(_) -> False()
  end
  """

  test "the decide-at-boundary pattern type-checks in both branches" do
    assert {:ok, _env} = Program.elaborate(@src)
  end
end
```

Verify the surface syntax for `>` in a `Bool` position and `Yes`/`No` matching against the existing int-refinement fixtures (`test/oracle/refine/refine01_is_true.cure` and the level-1/level-2 tests) and match their exact idiom; adjust `external_value > 0` to whatever comparison spelling those use.

- [ ] **Step 2: Run to verify it fails or passes**

Run: `mix cure.bundle_stdlib && mix test test/cure/stdlib/decide_at_boundary_test.exs`
Expected: PASS if the surface already supports it (Layer 3 is "guidance + example", needing no new machinery) — in which case this test is a codified regression example. If it FAILS on surface syntax only, fix the fixture syntax (not the compiler); if it fails for a deeper reason, STOP and report (Layer 3 is explicitly no-new-machinery).

- [ ] **Step 3: Commit the example**

```bash
git add -- test/cure/stdlib/decide_at_boundary_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "test(std): worked decide-at-boundary example (Layer 3)" -- test/cure/stdlib/decide_at_boundary_test.exs
```

- [ ] **Step 4: Full gate — run ONCE, alone**

Re-stage the stdlib, then run the full suite and Antigen and the oracle replay (serially, never concurrently):

Run: `mix cure.bundle_stdlib && mix test --include slow`
Expected: all green (existing + new).

Run: `mix antigen`
Expected: exit 0, healthy, survivors = 0.

Run: `mix test test/oracle_replay_test.exs`
Expected: PASS.

- [ ] **Step 5: Record the final counts**

Note the pass/skip count and Antigen cell count in the Stage 6 completion report. Do NOT commit anything if the gate is red — STOP and report which check failed with its output.

---

## Self-Review

**Spec coverage:**
- §4 Layer 1 connective algebra → Task 1. ✅
- §5 Layer 2 comparisons → Task 2; reflection lemmas → Task 3; `to_integer` → Task 4. ✅
- §5b Layer 3 decide-at-boundary → Task 8. ✅
- §5c automation (tagged lemmas + conjunction saturation) → Task 6. ✅
- §6 deferred axiom ledger → non-goal, no task (correctly out of scope). ✅
- §7 refinement→base coercion (item c) → Task 5. ✅
- §8 testing (unit + oracle + gate) → Tasks 1–8, oracle in Task 7, gate in Task 8. ✅
- §9 files → all created/modified files appear in a task. ✅
- §10 non-goals → honored (no kernel edit, no axioms, no solver — Task 6 is a candidate source, not a solver). ✅

**Placeholder scan:** proof terms are concrete (match structures given); the places with genuine discovery risk (matching an erased implicit; `match evidence` ex-falso reduction; `Conv.conv?/5`'s exact signature; Idris `So` API names) each carry an explicit fallback and a hard-stop guard rather than a bare "TBD". The refinement→base coercion (Task 5) and the `resolve_key`/`get_def` nil-contract (Task 6) are now given as concrete, verified code rather than left to on-the-fly discovery.

**Type consistency:** `natural_is_less_than`/`natural_is_less_than_or_equal`/`natural_is_positive` names are identical across Tasks 2, 3, 6, 7. The reflection-lemma names match between Task 3 (definition), Task 6 (automation), and Task 7 (oracle). `to_integer` consistent Tasks 4. New Elixir identifiers and where each is defined: `maybe_coerce_refined_to_base`, `first_projection_head`, `sigma_typed?`, `convertible?`, and a local `build_app` (Task 5, all in `elaborator.ex`); `conjunction_candidates`, `is_true_and_binder`, `and_left_projection_head`, `and_right_projection_head` (Task 6, in `proof_search.ex`, which already has its own `build_app/2` — no collision since the two modules are separate).

**Scope:** single plan, one subsystem (the reflection bridge + two elaborator touch-points). No decomposition needed.

## Notes for the executor

- The genuinely hard tasks are 3 (dependent proof terms) and 6 (candidate-source calling convention). Both are strict TDD: let the kernel/type-checker confirm each proof; iterate the body, never weaken a test.
- If ANY task appears to need a `lib/cure/core/*` edit, STOP — that is the zero-trust invariant and a hard-stop per the elaborator-hard-stop principle. The elaborator only ever *builds* Core terms that the kernel re-checks; there is always an untrusted-term route.
- Re-stage `priv/std` (`mix cure.bundle_stdlib`) after every `lib/std/*.cure` change before any elaborate-based test, or the test resolves the stale bundle.
