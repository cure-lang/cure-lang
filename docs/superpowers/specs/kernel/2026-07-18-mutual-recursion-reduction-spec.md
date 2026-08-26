# Spec — δ-reduction of mutually-recursive functions (certify the whole SCC)

**Status:** ✅ LANDED (`a4f071fb`). Fix + red-green + soundness antibody in
`test/cure/core/mutual_recursion_reduction_test.exs`; full Antigen 569/0 (coverage
baseline re-recorded), full suite 4877/0. Payoff probe `otp_nary_choice` (`158b07be`)
`rel=same`. History below kept for the record.

**Original status:** diagnosed, root-caused, fix designed. Ready to hand off.
**Layer:** K (TCB — kernel certification decides δ-reducibility). HARD-STOP discipline applies:
red-green + Antigen antibody + full Antigen + full suite. The change aligns with Idris/Agda/Lean
(a mutual block certifies as a unit), so it is a legitimate, well-founded TCB change.

## 0. Symptom

Two mutually-recursive functions do not δ-reduce inside a *later* definition's type/conversion,
so proofs about them fail with `:conversion_failure`. Minimal repro (fails today):

```
mod CheckRed
  use Std.Equivalent
  type Tag = TA | TB
  type Local = LEnd | LSel(Branches) | LBra(Branches)
  type Branches = BNil | BCons(Tag, Local, Branches)
  fn dual(l: Local) -> Local = match l          -- declared FIRST
    LEnd()     -> LEnd()
    LSel(bs)   -> LBra(dual_branches(bs))
    LBra(bs)   -> LSel(dual_branches(bs))
  fn dual_branches(bs: Branches) -> Branches = match bs
    BNil()            -> BNil()
    BCons(t, l, rest) -> BCons(t, dual(l), dual_branches(rest))
  fn check_reduce() -> Equivalent(Local, dual(dual(LEnd())), LEnd()) = reflexive(LEnd())
end
```

`dual(dual(LEnd()))` stays a stuck neutral `napp(dual, napp(dual, <ctor LEnd>))` instead of reducing
to `LEnd`. **Swapping the declaration order** (declare `dual_branches` first, `dual` second) makes the
SAME `check_reduce` succeed — the tell that this is a certification-ordering bug, not a size-change or
reduction-capability bug.

This blocks the natural encoding of **n-ary session types** (a `Local` type and its list of
`Branches`, with mutually-recursive `dual`/`dual_branches`, `project`/`project_branches`, and their
mutually-inductive proofs), which is the current open frontier in the OTP-metatheory work.

## 1. What already works (do NOT rebuild)

- **Mutual-recursion totality is already implemented and correct.** `Certificate.terminating?/3`
  handles a genuine mutual SCC via cross-function size-change (`mutual_group/3` +
  `mutual_group_total?/4`, certificate.ex "Mutual recursion" §). Elaborating `dual` + `dual_branches`
  *alone* certifies **both** `true` (verified). The size-change criterion is not the problem.
- **δ-unfolding of certified globals works** (`Normalise.unfold_certified_head`, gated on
  `Env.certified?`). A certified mutual function reduces fine — verified by the declaration-order swap.
- **A whole-env re-certification sweep exists** (`TotalityClosure.certify_deferred/1`, called in
  `Program` merge/completion paths) and re-certifies deferred defs once every body is present.

## 2. Root cause (precise)

Certification is per-definition and certifies **only the submitted name**:

- `kernel.ex:validate_certificate/2` (≈ line 651):
  ```elixir
  if Certificate.terminating?(name, body, env),
    do: {:ok, Env.certify(env, name)},   # <-- certifies ONLY `name`
    else: {:error, :not_total}
  ```
- `Certificate.terminating?/3` **defers** (returns `false`) when any callee still has a
  `{:hole, "__pending__"}` body (`pending_callee?`) — correct, because the SCC is under-computed
  while a sibling's body is unelaborated.

Bodies are elaborated in declaration order; each triggers `maybe_certify` → `validate_certificate`.
For a mutual pair `A` (declared first), `B` (declared last):

1. **validate(A):** `B`'s body is still the pending placeholder ⇒ `pending_callee?` true ⇒ `terminating?`
   defers ⇒ **A uncertified.**
2. **validate(B):** `A`'s body is now real ⇒ `pending_callee?` false ⇒ `mutual_group_total?({A,B})`
   proves the whole SCC total ⇒ but `validate_certificate` certifies **only B.** **A stays uncertified.**
3. `A` is finally certified only by the end-of-module `certify_deferred` sweep — which runs *after*
   every body, hence after any dependent def (`check_reduce`, or a mutually-inductive proof) was
   already checked with `A` still opaque to δ.

So the first-declared member of every mutual group is un-δ-reducible for the entire remainder of the
module's body-checking. The swap works only because `check_reduce` happened to use `dual`, and in the
swapped file `dual` is the *last*-declared (hence self-certified) member.

## 3. The fix

**When a mutual-group check succeeds, certify every member of the SCC, not just the submitted name.**

At the point `terminating?` returns true for a genuine group, `pending_callee?` was false and
`mutual_group_total?` has proven **every** member of the SCC terminating together — the exact
Idris/Agda/Lean semantics of certifying a `mutual` block as a unit. Each member has already been
type-checked (`check_def` runs in its own `validate_certificate` before its `terminating?` deferral),
and each member's body is real (guaranteed by `pending_callee?` = false). So certifying all members is
sound and needs no additional check.

### Implementation sketch (`kernel.ex:validate_certificate/2`)

```elixir
_ ->
  with :ok <- check_def(env, name) do
    %{body: body} = Env.get_def(env, name)

    if Certificate.terminating?(name, body, env) do
      # Certify the whole proven-total SCC, not just `name`. For a singleton /
      # non-recursive def this is exactly {name} (behaviour unchanged); for a
      # mutual group it also certifies the siblings the declaration-order
      # deferral left uncertified.
      group = Certificate.total_group(name, body, env)   # MapSet incl. `name`
      {:ok, Enum.reduce(group, env, &Env.certify(&2, &1))}
    else
      {:error, :not_total}
    end
  end
```

`Certificate.total_group/3` is a thin public wrapper: return `mutual_group(name, body, env)` when
`terminating?` succeeded (it recomputes the same SCC `terminating_ready?` used). Keep it a **separate,
explicit** function rather than folding the member list out of `terminating?/3` so the existing
boolean contract of `terminating?/3` (called directly by `certify_hardening_test.exs` and
`TotalityClosure`) is untouched.

**Guardrails to preserve (do NOT regress):**

- Only certify members returned by `mutual_group` for a def whose `terminating?` was true this call.
  Never certify a member with a pending body (can't happen when `terminating?` is true — assert it or
  filter defensively with `pending_callee?`).
- Singleton groups must behave exactly as today (certify just `name`). Verify a non-recursive def and a
  single-function self-recursive def each still certify only themselves (no accidental over-certify).
- Do not weaken `pending_callee?` deferral. The fix changes *how many* names a **successful** group
  check certifies, never *whether* a group with an unelaborated member is certified.

### Scope / known limitation (state it honestly)

The fix certifies the group at the point **all** its bodies are present — i.e. at the last-declared
member's validation. A def interleaved *inside* an incomplete mutual group (declared between two of its
members) that needs an earlier member to δ-reduce still sees it opaque. That is unavoidable without
certifying before every body exists (which would be unsound), and it is not a real authoring pattern —
proofs come after the complete group. Document it; do not chase it.

## 4. Alternatives considered (and why not)

- **Eagerly run `certify_deferred` after each def.** Correct results, but O(defs²) re-certification and
  it still can't certify a group until its last body lands — same scope as the fix, more cost.
- **Two-phase: certify all groups before checking any body.** Impossible — `terminating?` needs the
  elaborated bodies, which only exist after body-checking.
- **Make δ-unfold ignore certification for mutual defs.** Unsound — δ would unfold non-total mutual
  functions and loop. Rejected outright.

## 5. Soundness argument (for the Antigen antibody + review)

Certifying a name makes it δ-reducible. Soundness requires every certified name be **total**
(terminating), else δ diverges / equates distinct normal forms.

- For every member `m` of the certified group, `mutual_group_total?(name, …, group, env)` established a
  size-change well-foundedness over the whole SCC — this is exactly the property `mutual_group_total?`
  already certifies for the single submitted name; the members share one proof. So each `m` is total.
- Each `m` was `check_def`-validated when its own body elaborated. So each `m` is well-typed with a
  closed body (the A5 closed-body guard in `Normalise` still applies at unfold time regardless).
- Therefore certifying all of `group` certifies only total, type-correct, closed-bodied functions —
  the same invariant `Env.certify` upholds today, just applied to the whole SCC at once.

The change **only ever certifies more members that were already proven total in the same call** — it
never lowers the bar for *whether* a group certifies. A conservative rejection stays a rejection.

## 6. Test plan (HARD-STOP checklist)

1. **Red test (new).** A `test/cure/core/` (or elab) test elaborating the §0 `CheckRed` module in
   BOTH declaration orders; assert `{:ok, _}` for both, and that `dual`/`dual_branches` are both
   `Env.certified?` immediately after the module elaborates (not only after a manual sweep). Confirm it
   is RED before the fix (first order fails today), GREEN after.
2. **Antigen antibody (soundness).** Add an assay proving the change does NOT certify a **non-total**
   mutual group: a divergent mutual pair (e.g. `f(x) = g(x)`, `g(x) = f(x)` with no decrease) must stay
   uncertified and must NOT δ-reduce (no loop / no false equation). This is the must-reject guardrail —
   the change must not make it certify. Also an assay that a certified mutual group's δ-reduction
   terminates (no non-termination introduced).
3. **Full Antigen suite** (`mix test test/antigen/…` per the metatheory engine) — exit 0.
4. **Full test suite** — one run, alone, at the gate.
5. **Oracle**: add an n-ary-choice probe (`otp_nary_choice.{cure,idr}`) exercising mutual
   `dual`/`dual_branches` + `dual_involution` (mutually-inductive proof), `rel=same`, replay green — the
   real-world payoff that this fix unblocks.

## 7. Definition of done

Both declaration orders of the mutual pair elaborate; `dual_involution` (mutually-inductive) checks;
the n-ary-choice oracle probe is `rel=same` and replay-green; full Antigen + full suite pass; the red
test and the two antibodies are committed. Ghost-author commits
(`--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, explicit pathspec, no co-sign).

## 8. Pointers (verify against source before trusting)

- `lib/cure/core/kernel.ex` — `validate_certificate/2` (the one-line-scope change site, ≈ 631–655).
- `lib/cure/core/certificate.ex` — `terminating?/3`, `terminating_ready?/3`, `mutual_group/3`,
  `mutual_group_total?/4`, `pending_callee?`. Add `total_group/3` here.
- `lib/cure/elab/declarations.ex` — `maybe_certify/2` (calls `validate_certificate`), the two-pass
  signature-then-body registration that creates the deferral.
- `lib/cure/elab/totality_closure.ex` — `certify_deferred/1` (the end-of-module sweep that currently
  masks the bug at module scope but is too late for in-module dependent defs).
- `lib/cure/core/normalise.ex` — `unfold_certified_head/3` (δ gated on `Env.certified?`; A5 closed-body
  and A6 freeze guards — unchanged by this fix).
