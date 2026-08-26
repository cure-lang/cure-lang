# Infer/Check Coherence (task #14) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** `infer(t) = {:ok, A}` implies `check(t, A) = :ok` for params-on-spine constructor applications — route the arity `check`'s fields-only strategy cannot measure to the existing infer+conv fallback — spec `docs/superpowers/specs/kernel/2026-07-09-infer-check-coherence-design.md` (hardened `5b7b46e`).

**Architecture:** One clause-body restructure in `lib/cure/core/kernel.ex` `check/3` (TCB, Lean-aligned: check = infer + def-eq; blanket-approved, FULL gate mandatory), with the generic fallback body extracted into a shared `check_via_infer/3`. Then Antigen widening (the round-trip assay already exists — widening the equality generator arms it) and a docs-only ledger filing of the sibling value-spelling-dichotomy finding.

**Tech Stack:** Elixir, `Cure.Core.Kernel`, ExUnit, Antigen.

## Global Constraints (every task implicitly includes these)

- Working dir: `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/kernel-parity-batch`, branch `autopilot/kernel-parity-batch`. Never the parent checkout.
- Two-pipeline steer: kernel = `lib/cure/core/*`, dependent elaborator = `lib/cure/elab/*`; `lib/cure/types/*`/`lib/cure/compiler/*` are decoys — ZERO diff there (and zero elaborator diff too: it already emits fields-only ctors, spec §6).
- **TCB scope:** kernel.ex changes = the ctor-check clause restructure + the `check_via_infer/3` extraction, NOTHING else under `lib/cure/core/`.
- Strict red-green; tests behavioral, immutable once green; spec §5 pins are immutable — fix the implementation, never the pin.
- ONE `mix` command at a time, ever. Full suites once, alone, in Task 4. NO `mix cure.oracle` (replay only; divergence = STOP).
- Ghost commits `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, NO trailers, explicit pathspec only. Commit per task.
- Record `git rev-parse HEAD` at Task 1 Step 0 as `<pre-14-commit>`.
- STOP-and-report: any spec §5 pin failing; any pre-existing test failing (except the known one-off Antigen-seed flake, re-run once alone); oracle replay divergence; any need to touch a kernel site beyond the two named; anything uninterpretable.

## File Structure

- `lib/cure/core/kernel.ex` — the restructure (Task 1).
- `test/cure/core/infer_check_coherence_test.exs` — NEW red-green driver (Task 1).
- `lib/antigen/generators/equality.ex`, `lib/antigen/generators/rewrite.ex` — widening + comment updates (Task 2).
- `test/antigen/spine_ctor_coherence_antibody_test.exs` — NEW deterministic antibody pin (Task 2; follows the `test/antigen/*_antibody_test.exs` naming convention shared by all six existing files there; name deliberately NOT `eq_inductive_antibody_test.exs`, which exists and is unrelated — spec §2 review note).
- Parity-ledger roadmap spec §2 + memory — sibling-finding filing (Task 3).

---

### Task 1: the kernel restructure, red-green

**Files:** Modify `lib/cure/core/kernel.ex` (ctor-check clause ~237-265; fallthrough clause ~267-278). Test: `test/cure/core/infer_check_coherence_test.exs` (NEW).

- [ ] **Step 0: Pre-flight (read-only).** `git rev-parse HEAD` → `<pre-14-commit>`. Re-read kernel.ex:227-280 and :480-495 (anchors verified 2026-07-09 post-D2; re-locate by the quoted code if shifted). Confirm `Builtins.seed/2` (env, exclude-set with default) gives a test env with `Equivalent` (the existing kernel tests' pattern — read `test/cure/core/k6_param_ctor_infer_test.exs` setup and reuse it VERBATIM: `Context.empty(Builtins.seed(Env.empty()))` — `Cure.Core.Env` (defined in `lib/cure/core/inductive.ex`) exposes `empty/0`, NOT `new/0`; `Env.new/0` is a different module, `Cure.Types.Env`, part of the decoy pipeline — do not confuse them).

- [ ] **Step 1: Write the failing tests.**

```elixir
defmodule Cure.Core.InferCheckCoherenceTest do
  @moduledoc """
  Task #14 (spec 2026-07-09-infer-check-coherence): check subsumes infer+conv
  on the params-on-spine ctor spelling — the shape whose arity the fields-only
  checking strategy cannot measure. Lean-aligned (check = infer + def-eq).
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Builtins, Context, Env, Kernel}

  # Reuse k6_param_ctor_infer_test.exs's env/ctx construction verbatim.
  defp ctx do
    env = Builtins.seed(Env.empty())
    Context.empty(env)
  end

  @spine_refl {:ctor, :reflexive, [{:int_type}, {:int_lit, 3}]}

  test "coherence: the spine reflexive checks against its own inferred type" do
    ctx = ctx()
    assert {:ok, inferred} = Kernel.infer(ctx, @spine_refl)
    assert :ok = Kernel.check(ctx, @spine_refl, inferred)
  end

  test "wrong-endpoint expected rejects with conversion_failure, not ctor_arity" do
    ctx = ctx()
    wrong = {:vdata, :Equivalent, [{:vint_type}, {:vint, 3}, {:vint, 4}]}
    assert {:error, {:conversion_failure, _, _}} = Kernel.check(ctx, @spine_refl, wrong)
  end

  test "genuinely malformed arity still rejects :ctor_arity" do
    ctx = ctx()
    bad = {:ctor, :reflexive, [{:int_type}, {:int_lit, 3}, {:int_lit, 3}]}
    {:ok, good_ty} = Kernel.infer(ctx, @spine_refl)
    assert {:error, :ctor_arity} = Kernel.check(ctx, bad, good_ty)
  end

  test "checking position inside inference: (λ p : Eq(Int,3,3). p)(spine_refl) infers" do
    ctx = ctx()
    eq_ty = {:data, :Equivalent, [{:int_type}], [{:int_lit, 3}, {:int_lit, 3}]}
    term = {:app, {:lam, eq_ty, {:var, 0}}, @spine_refl}
    assert {:ok, _} = Kernel.infer(ctx, term)
  end
end
```

(Value/term shapes cribbed from `k6_param_ctor_infer_test.exs` — adjust the exact `{:vdata,…}` combined-args spelling and env construction to that file's working forms; the ASSERTIONS are the immutable part. The `wrong` expected type may need to be built by evaluating a `{:data,…}` term instead of hand-writing the vdata — mirror how existing kernel tests build expected values.)

- [ ] **Step 2: Run to verify red.** `mix test test/cure/core/infer_check_coherence_test.exs` — tests 1, 2, 4 FAIL with `:ctor_arity` in the pipeline (test 1: check returns error; test 2: error is `:ctor_arity` not conversion_failure; test 4: infer of the app fails because the argument check hits `:ctor_arity`); test 3 PASSES (already `:ctor_arity`). Record all four.

- [ ] **Step 3: Restructure.** In kernel.ex's ctor-check clause, replace the `if Inductive.ctor_family(…) != family … else … end` body with an ordered `cond` (ORDER IS LOAD-BEARING — spec §1: for `pc == 0` the spine condition collapses to the fields-only predicate; fields-only MUST be tested first):

```elixir
      %{args: tele, result_indices: result_indices} = ctor_sig ->
        result_params = Map.get(ctor_sig, :result_params, [])

        cond do
          Inductive.ctor_family(sig, cname) != family ->
            {:error, {:foreign_ctor, cname}}

          # Fields-only spelling — the existing specialized path, byte-identical.
          # MUST be first: for a paramless family (pc == 0) the spine condition
          # below collapses to this same predicate (spec §1 "order is load-bearing").
          length(args) == length(tele) ->
            with {:ok, arg_env} <- check_ctor_app(ctx, params, args, tele) do
              actual_params = Enum.map(result_params, &Eval.eval(&1, arg_env))
              actual_indices = Enum.map(result_indices, &Eval.eval(&1, arg_env))
              actual = {:vdata, family, actual_params ++ actual_indices}

              if Conv.conv_values?(actual, expected, Context.length(ctx), sig) do
                :ok
              else
                {:error, {:conversion_failure, actual, expected}}
              end
            end

          # Params-on-spine spelling (K6/§E.1, the inference form): the fields-only
          # strategy cannot measure this arity. Coherence (spec 2026-07-09, Lean's
          # check = infer + def-eq): route to the generic fallback — infer re-checks
          # the spine params against the family telescope (the K6 arm), then the
          # result converts against `expected`. Accepts nothing that is not already
          # inferable-and-convertible.
          pc > 0 and length(args) == pc + length(tele) ->
            check_via_infer(ctx, {:ctor, cname, args}, expected)

          true ->
            {:error, :ctor_arity}
        end
```

And extract the fallthrough clause's body (behavior-neutral — same code, one indirection):

```elixir
  def check(ctx, term, expected), do: check_via_infer(ctx, term, expected)

  # The generic checking rule (moduledoc: "falling back to `infer` plus a
  # cumulative conversion test") — shared by the fallthrough clause and the
  # params-on-spine ctor branch above so the coherence logic exists exactly once.
  defp check_via_infer(ctx, term, expected) do
    with {:ok, inferred} <- infer(ctx, term) do
      if subtype?(inferred, expected, ctx) do
        :ok
      else
        # Conversion failure diagnostic (§10): report both normal forms so the
        # mismatch is legible (and serializable via C2 for independent checkers).
        depth = Context.length(ctx)
        {:error, {:conversion_failure, Quote.reify(inferred, depth), Quote.reify(expected, depth)}}
      end
    end
  end
```

(Note the `:ctor_arity` for wrong counts now comes from the clause's own `true ->` branch rather than `check_ctor_app`'s length guard — `check_ctor_app`'s guard stays untouched for its other callers.)

- [ ] **Step 4: Run to verify green.** `mix test test/cure/core/infer_check_coherence_test.exs` — 4/4. Then `mix test test/cure/core/` — ALL green, in particular the spec §5 pins: `k6_param_ctor_infer_test.exs` (spine infer accept; fields-only infer `:ctor_requires_checking_mode`), `param_index_split_test.exs` (fields-only check paths INCLUDING the value-form conversion_failure pin at :110-125), `equivalent_kernel_test.exs`, `eq_refl_retirement_test.exs`. Any pin failure = the restructure broke the fields-only path = fix the code.

- [ ] **Step 5: Commit.**

```bash
git add -- lib/cure/core/kernel.ex test/cure/core/infer_check_coherence_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "fix(kernel): check subsumes infer+conv on params-on-spine ctors (coherence, Lean-aligned)" \
  -- lib/cure/core/kernel.ex test/cure/core/infer_check_coherence_test.exs
```

---

### Task 2: Antigen widening + deterministic pin

**Files:** Modify `lib/antigen/generators/equality.ex`, `lib/antigen/generators/rewrite.ex`; Create `test/antigen/spine_ctor_coherence_antibody_test.exs` (naming: ALL six existing files under `test/antigen/*_antibody_test.exs` — `certify_hardening_`, `unify_indices_`, `size_change_`, `eq_inductive_`, `cycle_rule_`, `lazy_unfold_` — use the `_antibody_test.exs` suffix and an `Antigen.<Name>AntibodyTest` module; spec §2 itself names the example `spine_ctor_coherence_antibody_test.exs` for exactly this reason — match the convention, do not drop the suffix).

- [ ] **Step 1: Widen `equality.ex`.** Add to `eq_term/0`'s frequency list (~:57-64; iterate exact shapes against the existing `test/antigen/generators/equality_test.exs` property, which is immutable): (a) a top-level params-on-spine reflexive arm — challenge `{{:ctor, :reflexive, [ty, a]}, {:data, :Equivalent, [ty, a, a], []}, []}` using the generator's existing ty/a menu and the FLAT claimed-type spelling (the reify-flat note at ~:96-99 — copy its convention exactly); (b) a checking-position arm via the check-embedding idiom (`mutation.ex:141-148` precedent): `{:app, {:lam, <eq_ty_term>, {:var, 0}}, <spine_refl>}` claiming the same eq type. Reword the moduledoc policy lines (~:15-22): the coherent-fragment restriction is HISTORICAL as of this fix — spine reflexives now generate in both positions; keep the old text as a dated note. Update `rewrite.ex`'s comment (~:179): the spine form is now also checkable, not an inference-position-only artifact.
- [ ] **Step 2: Run the generator property + assays.** `mix test test/antigen/generators/equality_test.exs` — green (iterate arm shapes if the claimed type disagrees with infer; the test is the oracle). Then `mix test test/antigen/` — FULL suite green; the `term/infer_check` and `term/subject_reduction` assays now sample the widened space (this is spec §4 item 2's property-level antibody).
- [ ] **Step 3: The deterministic pin.** `test/antigen/spine_ctor_coherence_antibody_test.exs`:

```elixir
defmodule Antigen.SpineCtorCoherenceAntibodyTest do
  @moduledoc """
  Task #14 antibody: the exact historical counterexample (params-on-spine
  reflexive, K6 inference spelling) round-trips infer→check through the real
  kernel. Regression here = the check-mode ctor clause stopped delegating its
  unmeasurable arity to check_via_infer.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Builtins, Context, Env, Kernel}

  test "infer→check round-trip on the spine reflexive" do
    ctx = Context.empty(Builtins.seed(Env.empty()))
    t = {:ctor, :reflexive, [{:int_type}, {:int_lit, 3}]}
    assert {:ok, ty} = Kernel.infer(ctx, t)
    assert :ok = Kernel.check(ctx, t, ty)
  end
end
```

Run it scoped — green (pins Task 1's landed behavior; its red evidence is Task 1 Step 2).
- [ ] **Step 4: Commit.**

```bash
git add -- lib/antigen/generators/equality.ex lib/antigen/generators/rewrite.ex test/antigen/spine_ctor_coherence_antibody_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "test(antigen): widen equality generator past the coherent fragment + spine-ctor coherence pin" \
  -- lib/antigen/generators/equality.ex lib/antigen/generators/rewrite.ex test/antigen/spine_ctor_coherence_antibody_test.exs
```

---

### Task 3: file the sibling finding (docs-only)

**Files (in-repo, git-tracked):** the parity-ledger roadmap spec (locate `docs/superpowers/specs/*idris-parity-roadmap*.md` → `docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md`, §2) + the task-#14 spec already carries §3.
**Files (NOT in-repo, NOT git-tracked — do not pathspec these into any worktree commit):** a NEW memory-note file under the operator's Claude memory directory (`~/.claude/projects/-Users-ch-Develop-esp32-beam-cure-lang/memory/`) + its index entry in that directory's `MEMORY.md` (spec §4 item 6 requires "a parity-ledger row PLUS a memory note" — both, not either; completion is not claimed until both are checked off). That memory directory lives outside `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/kernel-parity-batch` entirely — it is not part of this git repo, so it is edited directly (no `git add`/commit for it, no pathspec, no ghost-authorship concern).

- [ ] **Step 1:** Add a ledger row/finding note to the roadmap spec: "value-level ctor-spelling dichotomy — spine vs fields-only vctors are NOT definitionally equal (conv.ex length-strict spine compare); case ι-reduction over a spine-form scrutinee mis-binds OPEN branch bodies (ambient de Bruijn refs shift by pc, eval.ex ι env); erase keeps spine params. Pre-existing, incidence raised by #14's coherence fix; resolution = canonical-spelling design fork (Lean params-always vs Agda fields-only) — OPERATOR decision, prose. Evidence anchors in spec 2026-07-09-infer-check-coherence §3." Also mark the #14 row done.
- [ ] **Step 2:** File a memory note OUTSIDE the repo, per the existing convention (one short topic file + one index line in `MEMORY.md`, mirroring e.g. `global-def-collision-gap.md`'s entry — also a "flagged for operator, not landed" finding): create a new file (e.g. `ctor-spelling-value-dichotomy.md`) in the memory directory above stating the finding, its evidence anchors (`eval.ex:38`, `eval.ex:56-62`; `conv.ex:88-89`, `conv.ex:183-186`; `erase.ex:20-36`), and that it is filed as an operator design fork (not fixed); add its one-line index entry to that directory's `MEMORY.md`. This step touches no file under the worktree and is not part of Step 3's commit.
- [ ] **Step 3:** Commit (worktree-scoped, in-repo files only): `docs(ledger): #14 done; file ctor-spelling dichotomy as operator design fork` — explicit pathspec is the roadmap-spec file alone.

---

### Task 4: full gate + verification

- [ ] **Step 1 (one at a time, alone):** 1. `mix test test/antigen/` — green (count re-derived: prior 498 + 1 pin file). 2. `mix test` — green, 0 failures; delta vs 3260 enumerated (+4 Task-1 tests, +1 Task-2 pin = ~3265). 3. `mix test test/oracle_replay_test.exs` — zero divergence.
- [ ] **Step 2:** From `<pre-14-commit>`: `git diff <pre-14-commit> HEAD -- lib/cure/core/` = ONLY the kernel.ex restructure + helper; `git diff --stat ... -- lib/cure/elab/ lib/cure/types/ lib/cure/compiler/` = empty; authors = ghost only.
- [ ] **Step 3:** No commit (Tasks 1-3 committed); report per the report-back spec.

## Self-review notes

- Spec §1 fix → Task 1 Step 3 (ordered cond, load-bearing order comment inline). §2 → Task 2 (both arms + comments + renamed pin file). §3/§7.6 → Task 3 Step 1 (ledger row). §4 item 6 (ledger + memory note, both required) → Task 3 Steps 1-2 (ledger row in-repo, memory note out-of-repo — the two live in different places and are handled by separate steps). §4 items 1-5 gate → Task 4 + Task 1 Step 4 pins. §5 pins → named in Task 1 Step 4. §6 non-goals — untouched.
- Latitude: test-value spellings in Task 1 Step 1 (crib from k6 test; assertions immutable), generator arm shapes in Task 2 Step 1 (iterate against immutable equality_test), gate recounts. All report-required.
