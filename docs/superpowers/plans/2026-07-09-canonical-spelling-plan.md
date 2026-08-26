# Canonical-Spelling Kernel Batch Implementation Plan (task #22)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax.

**Goal:** Canonicalize constructor values to fields-only (ledger #28) and make `Normalise` readback signature-aware (nf_ill_typed class), per the hardened spec `docs/superpowers/specs/language/2026-07-09-canonical-spelling-design.md` (commit 4d3b2b8) — the SPEC is authoritative; this plan sequences it into red-green tasks.

**Architecture:** Two kernel commits. **C-A** (Part A): ι-rule coercion (eval.ex + normalise.ex) + conversion mixed-spelling completeness (conv.ex) + the `ctor_spelling` antibody. **C-B** (Part B): signature-aware readback at all four `Normalise` reify sites + the `equality.ex`/`equality_test.exs` companion flip + the `nf_welltyped` antibody. Each change is red-first.

**Tech Stack:** Elixir, Cure kernel (`lib/cure/core/*`), Antigen.

## Global Constraints

- Working dir: `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/kernel-parity-batch` (branch `autopilot/kernel-parity-batch`). NEVER read/touch the parent checkout.
- Ghost commits (`--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no trailers), explicit pathspecs, ONE mix at a time, no `iex`.
- **Diff confined to** (spec §0): `lib/cure/core/{eval,normalise,conv}.ex`, `lib/antigen/generators/equality.ex`, new antibody files `test/antigen/ctor_spelling_antibody_test.exs` + `test/antigen/nf_welltyped_antibody_test.exs`, and `test/antigen/generators/equality_test.exs:20` (the ONLY existing-test edit, ledgered under spec §3.4). `lib/cure/elab/` EMPTY, `lib/cure/compiler/` EMPTY, `quote.ex` EMPTY (already sig-aware). Any other file needing a change = STOP.
- **TCB bar:** every kernel edit is red-green with an antibody; the four gate-1 antibodies (A4.i, A4.ii, B4.i, B4.iii) MUST be shown RED on baseline before their fix — a non-red antibody = STOP (spec §4), do not fake the red.
- Tests immutable except the single §3.4 flip. Oracle replay (65) must stay 65/65 — any flip = STOP.

---

### Task 0: Baseline

- [ ] **Step 0.1:** `mix test` ONCE. Record passed/failures/skipped as **B** (expected 3142/0/0 post-firewall — record actual). This is the reconciliation anchor.

---

### Task 1 (C-A): fields-only constructor values

**Files:** `lib/cure/core/eval.ex`, `lib/cure/core/normalise.ex`, `lib/cure/core/conv.ex`, `test/antigen/ctor_spelling_antibody_test.exs`.

**Interfaces:**
- `Cure.Core.Inductive.arg_telescope(sig, cname)` → field telescope (list) or nil; `F = length(arg_telescope(sig, cname))`.
- Branch tuples are `{cname, arity, body}` (verified eval.ex:58); `arity` == field count (kernel.ex:708 enforces at type-check time).

- [ ] **Step 1.1: Write the A4 antibody RED** — `test/antigen/ctor_spelling_antibody_test.exs`. Model on `test/antigen/eq_inductive_antibody_test.exs` (base_sig via `Program.elaborate("mod M\nend\n")`, `Eval`, `Kernel`, `Context`). Three tests:

```elixir
defmodule Antigen.CtorSpellingAntibodyTest do
  @moduledoc """
  TCB antibody — fields-only is the canonical constructor-value spelling
  (ledger #28). The K6 params-on-spine ctor TERM (inference-only) must not
  cause a de Bruijn misalignment if it reaches the ι-rule (A1), and Conv must
  equate the two spellings of one ctor value under a shared type (A2).
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Kernel, Context, Conv, Eval}
  alias Cure.Elab.Program

  defp base_sig do
    {:ok, sig} = Program.elaborate("mod M\nend\n")
    sig
  end

  @nat {:data, :Nat, [], []}
  defp z, do: {:ctor, :Z, []}

  # A1 — reflexive has ONE field (w); Equivalent has ONE param (a). The K6
  # params-on-spine term {:ctor, :reflexive, [ty, w]} infers OK and evals to a
  # 2-arg vctor. Under a case whose reflexive branch (arity 1) body references
  # the branch-EXTERNAL binder ({:var,1} past the single field binder), a
  # correct fields-only ι binds [w] and {:var,1} resolves to the outer env slot;
  # WITHOUT A1 the 2-arg spine binds [w, ty] and {:var,1} wrongly resolves to ty.
  test "A4.i: ι over a params-on-spine ctor term matches the fields-only result" do
    sig = base_sig()
    env = [{:vint, 42}]  # a distinct outer binder value in the eval env
    scrut = {:ctor, :reflexive, [@nat, z()]}         # K6 params-on-spine
    motive = {:lam, @nat, {:lam, @nat, {:lam, {:data, :Equivalent, [@nat], [{:var, 1}, {:var, 0}]}, @nat}}}
    body = {:var, 1}                                  # branch-external reference
    node = {:case, scrut, motive, [{:reflexive, 1, body}]}
    # Expected: the outer binder (42), NOT the coerced-away param (@nat value).
    assert Eval.eval(node, env) == {:vint, 42}
  end

  # A2 — Conv equates the fields-only and params-on-spine spellings of the SAME
  # reflexive value at a shared Equivalent type.
  test "A4.ii: Conv equates the two spellings of one ctor value" do
    sig = base_sig()
    fields_only = Eval.eval({:ctor, :reflexive, [z()]}, Context.env(Context.empty(sig)))
    spine = Eval.eval({:ctor, :reflexive, [@nat, z()]}, Context.env(Context.empty(sig)))
    assert Conv.conv_values?(fields_only, spine, 0, sig)
  end

  # A4.iii — the SAME de Bruijn-misalignment repro as A4.i, but entered via
  # `Normalise.nf` instead of a raw `Eval.eval` call. IMPORTANT (verified by
  # hand-trace, 2026-07-09 review): `Eval.eval({:case,...}, env)` resolves a
  # concrete (non-neutral) scrutinee's ι-reduction DIRECTLY inside `eval.ex`'s
  # own `:case` clause (eval.ex:55-61) — `Normalise.nf`'s `eval_in` calls
  # `Eval.eval` on the WHOLE node in one pass, so for a scrutinee that is a
  # closed ctor literal (as here), `Normalise.nf`'s OWN `:ncase` sites
  # (normalise.ex:235-246, :269-288) are NEVER reached — those only fire when
  # `Eval.eval` first leaves a genuinely NEUTRAL `{:vneutral,{:ncase,...}}`
  # (e.g. an unresolved global/free-var scrutinee), which requires machinery
  # (a certified global) disproportionate for this antibody. A4.iii therefore
  # does NOT independently exercise normalise.ex's two ι sites — it re-drives
  # the SAME eval.ex site as A4.i, through the `Normalise.nf` entry point, and
  # is only a meaningful (non-vacuous) regression check if its branch body
  # actually references the branch-external binder (a literal-only body like
  # `z()` is insensitive to the extra param and would be GREEN unconditionally,
  # before and after A1 — not a valid antibody). Coverage of normalise.ex's own
  # two `:ncase` sites is instead achieved STRUCTURALLY: Step 1.3 below MANDATES
  # that both sites call the exact SAME exported helper A1 introduces in
  # eval.ex, so a bug in the shared algorithm is caught by A4.i regardless of
  # which call site would eventually execute it (no untested duplicate).
  test "A4.iii: nf of the params-on-spine case, entered via Normalise.nf, agrees with fields-only" do
    sig = base_sig()
    # Context.extend/2 wants a VALUE, not a term — {:vdata, :Nat, []}, not @nat.
    ctx = Context.extend(Context.empty(sig), {:vdata, :Nat, []})  # one outer binder
    node = {:case, {:ctor, :reflexive, [@nat, z()]},
            {:lam, @nat, {:lam, @nat, {:lam, {:data, :Equivalent, [@nat], [{:var,1},{:var,0}]}, @nat}}},
            [{:reflexive, 1, {:var, 1}}]}
    # WITHOUT A1: the 2-arg spine binds [w, ty] ahead of the outer binder, so
    # {:var,1} wrongly resolves to `ty` (a Nat data value), not the outer var.
    # WITH A1: fields-only binds [w] only, so {:var,1} resolves to the outer
    # context variable, which reifies back to itself ({:var,0} at depth 1).
    assert Cure.Core.Normalise.nf(ctx, node) == {:var, 0}
  end
end
```

Run `mix test test/antigen/ctor_spelling_antibody_test.exs` — A4.i (the formal gate-1 antibody, Global Constraints) MUST be RED; if it is GREEN on baseline, STOP (the K6 hazard is unreachable as constructed — revisit the construction, do not proceed). A4.iii is NOT one of the four formal gate-1 antibodies, but — now that its construction is corrected to be non-vacuous — it exercises the identical eval.ex code path as A4.i through a second entry point (`Normalise.nf`) and should co-vary with it: expect it RED too. A4.iii green while A4.i is red would be a genuine anomaly (the two should agree by construction) — investigate before proceeding, though it does not by itself trigger the plan's formal STOP protocol. A4.ii may be red or green depending on whether the length-strict path rejects; if green, note it (it still guards A2's completeness).

- [ ] **Step 1.2: A1 — eval.ex ι-rule coercion.** At eval.ex:56-62 replace the `{:vctor, ...}` arm:

```elixir
      {:vctor, cname, args} ->
        {_cname, arity, body} = Enum.find(branches, fn {c, _ar, _b} -> c == cname end)
        fields = drop_leading_params(args, arity)
        eval(body, Enum.reverse(fields) ++ env)
```

Add a helper in eval.ex, exported `@doc false` (same pattern as `Eval.fold/2` — its own comment: "Public (`@doc false`) so `Cure.Core.Normalise`'s builtin-op compute hook folds through the SAME table" — reuse, don't duplicate):

```elixir
  # Fields-only canonicalization: a K6 params-on-spine ctor value carries its
  # family params ahead of its fields; the ι-rule binds ONLY the fields (the
  # branch's `arity`). length(args) == arity is the canonical zero-cost path.
  # Public (`@doc false`) so `Cure.Core.Normalise`'s two ι sites call the SAME
  # function (Step 1.3) — a single audited algorithm, not a duplicated twin.
  @doc false
  def drop_leading_params(args, arity) when length(args) > arity,
    do: Enum.drop(args, length(args) - arity)

  def drop_leading_params(args, _arity), do: args
```

- [ ] **Step 1.3: A1 — normalise.ex ι sites.** Apply the identical coercion at both ι sites (normalise.ex:235-246 `whnf` path and :269-288 `reduce_unfolded` path — locate by the `Eval.eval(body, Enum.reverse(cargs) ++ env)` shape and the `{c, ar, b}` branch destructure). **MANDATORY (not executor's choice):** both sites call `Eval.drop_leading_params(cargs, ar)` — the exact function Step 1.2 exports, not a local twin. This is load-bearing: A4.iii (below) re-enters this SAME code through `Normalise.nf`'s top-level `eval_in`, which resolves a concrete (non-neutral) scrutinee inside `eval.ex`'s own `:case` clause and never actually reaches normalise.ex:235-246/:269-288 for that construction (see A4.iii's comment) — so those two sites have NO dedicated red antibody of their own. Correctness there is guaranteed structurally (same function, audited once by A4.i/A4.iii) rather than behaviorally; a reviewer checking this step should only need to confirm the CALL (`Eval.drop_leading_params(cargs, ar)`, right variable for `ar`) at each site, not re-derive the algorithm.

- [ ] **Step 1.4: Run A4.i/A4.iii green.** `mix test test/antigen/ctor_spelling_antibody_test.exs` — A4.i and A4.iii now PASS. A4.ii may still be red (needs A2).

- [ ] **Step 1.5: A2 — conv.ex mixed-spelling completeness.** Two edits:

(a) Thread `sig` through the `same_*_no_delta?` family (conv.ex:152-180): widen `same_neutral_no_delta?/3`→`/4`, `same_value_no_delta?/3`→`/4`, `same_spine_no_delta?/3`→`/4`, adding a trailing `sig` to **every clause's head pattern** (not just the ones touched below — this includes the scalar clauses of `same_value_no_delta?`, e.g. `:vtype`/`:vint_type`/`:vint`/`:vfloat_type`/`:vfloat`/the catch-all `_a, _b`, which gain the extra arg but otherwise stay unchanged). Update every internal recursive call to pass `sig` through: the `:napp` clause at :155-156 (`same_neutral_no_delta?(f1,f2,depth,sig)` and `same_value_no_delta?(a1,a2,depth,sig)`), the `:vneutral` clause at :160-161 (`same_neutral_no_delta?(n1,n2,depth,sig)`), the `:vdata` clause at :169-170 (`same_spine_no_delta?(args1,args2,depth,sig)` — sig passed through UNCHANGED, no coercion — Part A is constructor VALUES only), and the `:vctor` clause at :172-173 (superseded by (b) below, which both widens it AND adds coercion). Update the sole external caller at conv.ex:60: `same_neutral_no_delta?(n1, n2, depth, sig)` (sig already in scope there). Elixir will refuse to compile a mismatched-arity call, so this is mechanically checkable — but a reviewer should confirm no clause was left at the OLD 3-arg head pattern (a stray old-arity clause silently becomes dead code, not a compile error, since Elixir dispatches by arity+guard).

(b) At the two vctor clauses — conv.ex:88-89 (`conv_struct?`) and conv.ex:172-173 (`same_value_no_delta?`) — coerce each spine to its last F elements before the spine walk, F from the signature (caller has the ctor name `n1`):

```elixir
  defp conv_struct?({:vctor, n1, vs1}, {:vctor, n2, vs2}, depth, sig),
    do: n1 == n2 and conv_spine?(coerce_fields(n1, vs1, sig), coerce_fields(n2, vs2, sig), depth, sig)
```
```elixir
  defp same_value_no_delta?({:vctor, n1, args1}, {:vctor, n2, args2}, depth, sig),
    do: n1 == n2 and same_spine_no_delta?(coerce_fields(n1, args1, sig), coerce_fields(n2, args2, sig), depth, sig)
```

with a shared private helper (do NOT touch `conv_spine?`/`same_spine_no_delta?` themselves, nor the `:vdata` clauses):

```elixir
  # Coerce a possibly-params-on-spine ctor value spine to fields-only (last F),
  # F = the ctor's field count. Nil sig or unknown ctor ⇒ unchanged (falls back
  # to today's length-strict compare — sound, at worst a false-reject).
  defp coerce_fields(_cname, vs, nil), do: vs

  defp coerce_fields(cname, vs, sig) do
    case Cure.Core.Inductive.arg_telescope(sig, cname) do
      tele when is_list(tele) and length(vs) > length(tele) ->
        Enum.drop(vs, length(vs) - length(tele))

      _ ->
        vs
    end
  end
```

Confirm `Cure.Core.Inductive` is aliased in conv.ex (it aliases `Normalise`, `Eval` — add `Inductive` to the alias or use the fully-qualified name as above).

- [ ] **Step 1.6: A4 green + scoped conv suite.** `mix test test/antigen/ctor_spelling_antibody_test.exs test/cure/core/conv_test.exs` — all green. A2 must ONLY add acceptances: if any previously-passing conv test now FAILS (an accept became a reject), STOP (spec §4).

- [ ] **Step 1.7: Scoped kernel + antigen.** `mix test test/cure/core/ test/antigen/` — green.

- [ ] **Step 1.7b: Full-suite standalone check (commit-boundary proof).** `mix test` ONCE, full suite. Part A must be a complete, independently-shippable commit — nothing outside `test/cure/core/`/`test/antigen/` depends on Part B's readback fix, so this MUST be green (0 failures) with Part B's changes not yet made. Record the count; it becomes the reconciliation anchor for Task 2 (baseline **B** from Step 0.1, plus the 3 new A4 antibodies, no deletions). If this is NOT green, STOP — Part A is not actually independent of Part B and the two-commit architecture (spec §0, this plan's own "Architecture" line) is unsound as scoped; do not commit C-A until resolved.

- [ ] **Step 1.8: Commit C-A** (ghost, explicit pathspecs): `feat(kernel): fields-only constructor values — ι-rule coercion + conversion completeness (ledger #28)`. Stage eval.ex, normalise.ex, conv.ex, ctor_spelling_antibody_test.exs.

---

### Task 2 (C-B): signature-aware nf readback

**Files:** `lib/cure/core/normalise.ex`, `lib/antigen/generators/equality.ex`, `test/antigen/generators/equality_test.exs` (line 20 only), `test/antigen/nf_welltyped_antibody_test.exs`.

- [ ] **Step 2.1: Write the B4 antibody RED** — `test/antigen/nf_welltyped_antibody_test.exs`:

```elixir
defmodule Antigen.NfWellTypedAntibodyTest do
  @moduledoc """
  TCB antibody — Normalise readback preserves well-typedness for indexed
  families. The signature-less reify collapses an indexed family's param/index
  split (Equivalent 1-param/2-index → {:data,:Equivalent,[ty,a,b],[]}), which
  fails re-inference :arg_arity. B1 makes all four Normalise reify sites
  signature-aware.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Kernel, Context, Normalise, Eval}
  alias Cure.Elab.Program

  defp base_sig do
    {:ok, sig} = Program.elaborate("mod M\nend\n")
    sig
  end

  @nat {:data, :Nat, [], []}
  defp z, do: {:ctor, :Z, []}

  # B4.i — nf of the FAMILY TYPE itself (not a proof of it). IMPORTANT (verified
  # by hand-trace, 2026-07-09 review — the originally-drafted construction used
  # a bare fields-only ctor term, `t = {:ctor, :reflexive, [z()]}`, as the thing
  # to `Kernel.infer`; that is REJECTED unconditionally by kernel.ex's ctor-arity
  # `cond` (`{:error, {:ctor_requires_checking_mode, :Equivalent}}`) whenever the
  # family has params (Equivalent has 1) and the ctor term is bare fields-only in
  # INFERENCE position — `{:ok, ty} = Kernel.infer(ctx, t)` crashes via MatchError
  # for that reason, BOTH before and after B1, since B1 never touches
  # `Kernel.infer`'s ctor dispatch. That construction can never go green and
  # proves nothing about the readback bug — replaced below). The flat-collapse
  # bug is specifically about reifying a `{:vdata,...}` VALUE (a family TYPE),
  # so the antibody must nf the TYPE term directly, then re-check the normal
  # form is still well-formed.
  test "B4.i: nf of an indexed-family TYPE term stays well-formed" do
    sig = base_sig()
    ctx = Context.empty(sig)
    ty_term = {:data, :Equivalent, [@nat], [z(), z()]}   # Equivalent(Nat, Z, Z) : Type
    assert {:ok, _sort} = Kernel.infer(ctx, ty_term)
    normal = Normalise.nf(ctx, ty_term)
    # Pre-B1: reify has no signature, so params++indices (1+2=3 combined values)
    # all land in `params`; re-inferring against Equivalent's 1-param telescope
    # is an arity mismatch — `check_spine` (kernel.ex:470-475) returns
    # `{:error, :arg_arity}`. Post-B1: reify recovers the 1-param/2-index split
    # and re-inference succeeds.
    assert match?({:ok, _}, Kernel.infer(ctx, normal))
  end

  # B4.ii — idempotence retained on the same TYPE shape (regression guard: must
  # not flip under B1's signature-aware reify — same construction as B4.i, since
  # only a `:vdata` value's readback is sensitive to the split at all).
  test "B4.ii: nf is idempotent on the indexed-family TYPE shape" do
    sig = base_sig()
    ctx = Context.empty(sig)
    ty_term = {:data, :Equivalent, [@nat], [z(), z()]}
    once = Normalise.nf(ctx, ty_term)
    assert Normalise.nf(ctx, once) == once
  end

  # B4.iii — the SAME TYPE shape nested under a binder exercises quote_nf
  # (:177), a different code path than nf's top-level reify (normalise.ex:142-154
  # `nf_struct`'s `:vlam` clause reifies the body via `quote_nf`, not directly).
  # As with B4.i, the body must be a TYPE-valued term (`Equivalent(Nat,x,x)`),
  # not a ctor/proof term — a fields-only `reflexive x` body hits the identical
  # `:ctor_requires_checking_mode` crash as the original B4.i draft (same root
  # cause, same fix).
  test "B4.iii: nf of a binder body containing an indexed-family TYPE re-checks" do
    sig = base_sig()
    ctx = Context.empty(sig)
    # λx:Nat. Equivalent(Nat, x, x) : Nat -> Type
    lam = {:lam, @nat, {:data, :Equivalent, [@nat], [{:var, 0}, {:var, 0}]}}
    {:ok, ty} = Kernel.infer(ctx, lam)
    normal = Normalise.nf(ctx, lam)
    assert Kernel.check(ctx, normal, ty) == :ok
  end
end
```

Run `mix test test/antigen/nf_welltyped_antibody_test.exs`. B4.i and B4.iii MUST be RED (`{:error, :arg_arity}` on re-check — see each test's comment for the traced call chain). If either is GREEN on baseline, STOP and report (the flat-readback hazard is not reproduced as constructed — refine the term, do not proceed). B4.ii may pass on baseline (idempotence already holds); it guards against B1 regressing it.

- [ ] **Step 2.2: B2 — consumer audit table.** Before editing normalise.ex, write the consumer-audit table into the execution report (the spec §2 B2 bullet pre-lists the sites — verify each still holds, don't rediscover): the four normalise sites (reconciled by B1); the `Eval.eval`-roundtrip-immune sites (kernel.ex:975, :987, :86, :296; elab/unify.ex:482 already 3-arg); the flat-by-design `unify_indices` at kernel.ex:831-835 (out of scope §5 — confirm nothing now feeds it split-shaped index terms it can't handle); the confirmed regression at equality_test.exs:20. If any site NOT in this list consumes nf/whnf/quote output as a `:data`-shaped term, STOP.

- [ ] **Step 2.3: B1 — the four reify sites.** In normalise.ex:
  - `:31` (`whnf`): `|> Quote.reify(Context.length(ctx), Context.signature(ctx))`
  - `:42` (`nf`): `|> Quote.reify(Context.length(ctx), Context.signature(ctx))`
  - `:48` (`quote`): `def quote(value, depth, sig \\ nil), do: Quote.reify(value, depth, sig)` (repurpose the discarded 3rd param; 2-arg callers still default flat)
  - `:177` (`quote_nf`): forward the in-scope `sig` into the trailing reify: `Quote.reify(depth, sig)`

- [ ] **Step 2.4: B4 green.** `mix test test/antigen/nf_welltyped_antibody_test.exs` — B4.i, B4.ii, B4.iii all PASS.

- [ ] **Step 2.5: B3 — equality generator + its test (the §3.4 flip).** **VERIFIED 2026-07-09 review: there are THREE flat `{:data, :Equivalent, [ty, a, a], []}` claimed-type literals in `equality.ex`, not two** (`grep -n Equivalent lib/antigen/generators/equality.ex`) — the spec (§2 item 3, §3.4) and this plan's earlier draft both cite only `:80-83` and `:130-133`, missing the THIRD at `checked_spine_refl_term` (~line 91-98, the flat literal at ~line 95: `eq_ty_flat = {:data, :Equivalent, [ty, a, a], []}`). `checked_spine_refl_term` IS sampled by `Equality.gen()`'s frequency list (`{2, checked_spine_refl_term()}`) and IS exercised by the SAME `equality_test.exs` assay that B1+B3 make signature-aware — leaving it flat means its samples flip from green to RED once B1 lands and `equality_test.exs:20` starts passing `Context.signature(cx)` for every generator's output alike (a real regression, not hypothetical: `Normalise.quote` would return split, `c.payload.type` would stay flat, syntactic `==` fails). Update **all three** sites — `spine_refl_term` (~line 83), `checked_spine_refl_term` (~line 95), and `checked_refl_transport_term` (~line 133) — from the flat `{:data, :Equivalent, [ty, a, a], []}` shape to the split `{:data, :Equivalent, [ty], [a, a]}` shape. In `test/antigen/generators/equality_test.exs:20`, add `Context.signature(cx)` as `Normalise.quote`'s 3rd arg. All land here together (B3 is unsound without the test companion — flat actual vs split claimed under syntactic `==`). Ledger the equality_test.exs:20 edit (file:line, old→new, "pinned flat readback indirectly via runtime Normalise.quote output; §3.4 flip class").

- [ ] **Step 2.6: Scoped green.** `mix test test/antigen/ test/cure/core/` — green (equality_test.exs:20 now consistent, the four other `Normalise.quote(...)==...` generator tests untouched and still flat-defaulted).

- [ ] **Step 2.7: Commit C-B** (ghost, explicit pathspecs): `fix(kernel): signature-aware Normalise readback — split indexed-family params/indices (nf_ill_typed)`. Stage normalise.ex, equality.ex, equality_test.exs, nf_welltyped_antibody_test.exs.

---

### Task 3: Gates + report

- [ ] **Step 3.1: Full suite ONCE.** `mix test` → 0 failures. Reconcile: **B** + 6 new antibody tests (A4.i/ii/iii + B4.i/ii/iii) = final passed (the §3.4 flip edits a test in place, no count change). State the number.
- [ ] **Step 3.2: Oracle replay.** Confirm 65/65 inside that run (readback change must not flip any elaboration verdict). Any flip = STOP.
- [ ] **Step 3.3: Diff-scope.** `git diff <B-commit-parent>..HEAD --stat` touches ONLY: eval.ex, normalise.ex, conv.ex, equality.ex, equality_test.exs, the two antibody files. `lib/cure/elab/` + `lib/cure/compiler/` + `quote.ex` EMPTY. Firewall test green.
- [ ] **Step 3.4: Report** — both commit hashes, baseline B → final arithmetic, the B2 consumer-audit table, the §3.4 flip-ledger line, red→green evidence for the four gate antibodies, oracle 65/65, diff-scope stat, and an honest deviation statement.
