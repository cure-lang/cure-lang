# Core Walker Drift — Defect Audit

**Status:** AUDIT COMPLETE · **REMEDIATION COMPLETE** — see **§10**, which is the current
truth. §4 below is preserved as the audit's *pre-probe* record: two of its severities were
overturned by probing (§4.7 **up**, §4.4 **down**), and §10 says so. Where §4 and §10
disagree, §10 wins.
**Date:** 2026-07-15 (audit) · 2026-07-15 (remediation)
**Scope:** `lib/cure/elab/*` (E) and `lib/cure/core/*` (K). The non-dependent
`lib/cure/compiler/{codegen,pattern_compiler}.ex` and `lib/cure/types/*` are out of scope
and any finding located there is void.

**Provenance.** Eight parallel audit agents, one lens each; every candidate finding then
attacked by two independent skeptics instructed to refute it; then a synthesiser and a
completeness critic over the survivors. 40 agents, 15 candidates, 13 survived the skeptics.
Every defect recorded under §4 has additionally been **re-verified by hand against the
source** — the agents supplied leads, not facts.

**The adversarial pass earned its keep, and the proof is that it killed one of my own
findings.** The first draft of this document filed `has_meta?` as CRITICAL. Both skeptics
independently refuted it, and they were right (§9). It also *split* on the QTT-grade finding
— one skeptic refuted it, the synthesiser ranked it #1 CRITICAL. Both were correct about
different halves of the same function, and reconciling them (§4.2) produced the most serious
defect in this audit. **Read §9 before re-reporting anything.**

---

## 1. Thesis

This audit was commissioned after two latent elaborator defects shipped
(`12cb6163`, `a8b4e7e9`), on the suspicion that they were instances of a class rather
than accidents. They were.

**The class:** Cure's Core has 24 term formers. Ten of them are *compound* (they carry
subterms). Roughly 25 hand-written walkers traverse Core terms across E and K. Almost none
of them enumerate all ten. That would be merely untidy — except that most of these walkers,
on meeting a former they do not know, **return it unchanged and report success**. They treat
an unknown compound former as a **leaf**. They do not crash. They quietly do nothing, and
their caller cannot tell the difference between "walked it, nothing to do" and "never looked
inside."

This is not twelve independent mistakes. It is **one missing invariant, instantiated twelve
times**, and it is *generated* by the way the language grew: every former added to
`Core.Term` after a walker was written silently invalidates that walker, and nothing in the
build catches it. `:let` (the 7th former), the QTT grades on binders, and the `Effect` family
all landed recently. Every walker predating them is incomplete **by construction**.

The evidence that this is systemic rather than incidental is in the codebase's own comments.
At `lib/cure/elab/program.ex:831-834` someone hit this exact bug, fixed it, and left a note:

> The `:let` binder is the seventh Core former. Without this clause it fell through to the
> catch-all below, and every global referenced only inside a `let` vanished from
> `reachable_def_names/2` — co-emitting such a closure produced a module that called a
> function it never defined.

That is a precise diagnosis of the bug class. It was applied to **one former in one walker**,
and no sweep followed. The `Effect` family reintroduces the identical bug in the identical
function today (§4.6).

---

## 1b. Bottom line

Twenty-five Core walkers screened. Twelve fail open. **Two of those are live and critical,
four are live and minor, six are inert.** The thing that separates live from inert is *not*
fail-open-ness — it is whether the walker traverses **values** or only **types** (§3a), and,
for the headline defect, whether **anything downstream re-derives what the walker destroyed**
(§3c). Triage on those two axes before assigning any severity.

| # | defect | severity | live? |
|---|---|---|---|
| §4.2 | `Subst.shift` **launders the QTT grade off every `let`**, and `Relevance` is the *only* thing that ever enforces one → **an `:erased` proof can be used at runtime; a `:linear` value can be dropped or duplicated** | **CRITICAL — soundness** | ✅ live, chain hand-verified end to end |
| §4.0 | `Subst` skips `effect_pure`/`effect_bind` → erasure fails to strengthen outer vars → **wrong BEAM code, never re-checked** | **CRITICAL — miscompilation** | ✅ live, hand-verified |
| §4.4 | TCB: `subst_params` / `replace_branch_vars` fail open on `:let`/`Effect` | **HIGH** ¹ | ✅ live |
| §4.7 | `count_level` returns 0 for `Effect` → un-join gate **permits** an optimisation it must forbid | **MEDIUM** ² | ✅ live |
| §4.6 | `global_refs` misses `Effect` → `reachable_def_names/2` omits a real dependency | **LOW** ³ | ✅ live, tooling/tests only |
| §4.9 | dead retry on the dotted-qualified path | LOW | ✅ live, waste only |
| §4.5 | `mabs` skips `:let`/`Effect` | — | ⬜ inert (types only) |
| §4.8 | `has_hole?` skips `Effect` | — | ⬜ inert (no route for a hole into an effect body; and emit is separately protected — `check_codegen_ready` routes through `Validator`, which is fail-closed) |
| §9 | **`has_meta?`** · `Relevance.walk` on `Effect(T)` · `totality_closure` · `Validator` · the **`:pi`/`:lam` half of §4.2** | — | ❌ **refuted** |

¹ TCB, and the *direction* of failure is argued, not proven. Probe before believing either way.
² Unsound-accept is narrowed to the `:affine` grade specifically (`Grade.leq(:erased, :affine)` is
`true` by design); for `:linear` the outcome is a spurious rejection, which is safe.
³ Confirmed by the critic: the production `.cure`→BEAM path (`compiler.ex:411`) does **not** call
`reachable_def_names`; it emits every declared def. Nothing in `lib/` calls it. Test-harness only.

**The two CRITICALs are independent, both silent, and neither is the bug we shipped last week.**
One defeats the erasure/linearity discipline at the type level; the other emits wrong code. They
share a single root cause — `lib/cure/elab/subst.ex`, a 116-line file, is wrong in **two
unrelated ways at once**, and is the single highest-leverage file in the repo to fix.

---

## 2. The invariant that is missing

> **Every traversal of a Core term must be total over `Core.Term.t()`, and where it cannot
> be, its catch-all must fail CLOSED.**

The codebase already knows this. `lib/cure/elab/unify.ex:389-401` states it exactly, and is
the *only* walker that gets it right on purpose:

> This walker is FAIL-CLOSED: its catch-all answers `true` (escapes). […] Refusing to solve a
> metavariable is soundly incomplete; solving it out of scope is not.
>
> Note a generic structural tuple-walk would NOT be a correct catch-all here, the way it is
> for `Inductive.occurs?`: binder-introducing nodes must bump `local`, and walking a branch
> body without bumping it *under*-estimates the free index […] So every binder is enumerated
> explicitly, every leaf is enumerated explicitly, and anything unknown is assumed to escape.

The audit's job was to find every walker that does **neither** of the two safe things.

---

## 3. Taxonomy of catch-alls

The coverage matrix (§5) cannot by itself distinguish a bug from a correct omission. What
separates them is the **polarity of the catch-all**. Three classes:

### Class A — generic structural descent (SAFE, self-healing)
Catch-all is `when is_tuple(t) -> descend into every element`. A new former is handled
automatically the day it is added. Correct **iff** the operation does not need to track
binder depth (`Effect` nodes bind nothing, so they are safe under this catch-all).

- `core/validator.ex:163` `children`
- `core/term.ex:240` `has_free_var?`
- `elab/totality_closure.ex:105` `collect`
- `elab/elaborator.ex:2183` `abstract_term`, `:2212` `free_indices`, `:987` `occurs_below?`

**These are not defects.** In particular the nightmare hypothesis — *a recursive call hidden
inside an `Effect` node that `totality_closure` never sees, certifying a non-total function
as total* — **is refuted**: `collect/1` descends generically through any tuple, so it sees
into `effect_bind`. Recording this explicitly because it was the single highest-severity
thing the audit was looking for, and it is not there.

### Class B — fail-closed (SAFE, soundly incomplete)
Catch-all answers with the conservative verdict; an unknown former degrades to *rejection*,
never to silent acceptance.

- `elab/unify.ex:435` `escapes?` → `true` ("assume it escapes; refuse to solve")
- `core/meta_check.ex:63` `canonical_head?` → `false`
- `core/kernel.ex:1470` `rigid_index?` → `false`

**Not defects.** They may cost completeness on `let`/`Effect`-bearing terms; that is a
tolerable, and *loud*, failure mode.

### Class C — fail-open leaf assumption (THE DEFECT CLASS)
Catch-all returns the node **unchanged**, or a zero-value (`false` / `0` / `[]`), thereby
asserting "this former has no interesting content." For a compound former that assertion is
**false**, and the caller has no way to detect it.

Every finding in §4 is Class C.

---

## 3a. The discriminator: does this walker see TYPES, or VALUES?

**This is the most useful thing the audit produced, and it did not come from a finder — it
came from two skeptics refuting findings.** It cuts the twelve Class C walkers cleanly into
"inert" and "live", and it is the reason a raw fail-open count is a bad triage signal.

`:let`, `effect_pure`, and `effect_bind` **cannot appear in a type**. Two independent
choke-points enforce this, and the skeptics traced both exhaustively:

1. **Every declared type** funnels through exactly one grammar, `idx_to_core`
   (`declarations.ex:1658-1805`) — reached from all 9 type-elaboration entry points. Its
   clause list is closed (`:variable`, `:function_call`, `:sigma_type`, `:tuple_type`,
   `:pi_type`, `:attribute_access`, `:union_type`) with an explicit
   `{:error, {:unsupported_index_expr, other}}` catch-all. `let`/do-block surface syntax is
   **rejected outright**.
2. **Every inferred type** arrives via `Quote.reify` of a `Cure.Core.Value.t()`
   (`value.ex:56-74`), which has **no `:vlet` form at all** — `let` evaluates away by
   substitution during NbE, so there is nothing to reify back into a `{:let, …}`.

**Therefore:**

- A walker that only ever traverses **type-level** terms **cannot** meet these formers. Its
  fail-open gap is **inert today** — real hygiene debt, zero live blast radius. This covers
  `mabs` and everything else downstream of `Unify.unify`, whose 12 call sites in
  `elaborator.ex` were enumerated one by one and shown to unify **types only** (an argument's
  inferred type via `Quote.reify`, a codomain, a domain instantiation) — **never an argument's
  value.**
- A walker that traverses **value-level** terms — definition bodies, chosen arguments, branch
  bodies — **does** meet them, because that is exactly where `do`-blocks and `let`-chains live.
  Its fail-open gap is **live**.

Triage every walker by which side of that line it sits on **before** assigning severity. A
gap that cannot be reached is not a bug; saying otherwise is how an audit loses the reader's
trust. It is also the reason the `derive_actor` shadowing bug went unnoticed for so long: `let`
appears only in *values*, and the value-side walkers are the under-maintained ones.

---

## 3b. Severity is decided by position relative to the kernel check

The audit surfaced an ordering principle that was not obvious going in, and it governs every
severity below. **A fail-open walker's blast radius depends on whether anything re-checks its
output.**

- **Walkers that run *before* or *during* kernel checking** (`unify`, `has_meta?`, the
  kernel's own `subst_params`) produce a term that the kernel then judges. A corruption here
  is *usually* caught — as a conversion failure or a validator rejection. The damage is
  **completeness** (a good program mysteriously rejected) and the failure is at least *loud*.

- **Walkers that run *after* kernel checking — `Erase`, `emit` — have nothing downstream to
  catch them.** `emit.ex:354` feeds `Erase.erase/2`'s output straight into codegen. Erasure
  output is **never re-verified by the trusted kernel**. A de Bruijn index corrupted at this
  stage does not get rejected; it either crashes emit on an unbound index, or — worse —
  **silently resolves to the wrong bound variable and generates wrong code.**

`relevance.ex:4-7` states the invariant that governs this half of the pipeline:

> `Erase.erase` produces [a term that] never references a binding that no longer exists.

The top finding below is a direct violation of that stated invariant. **Post-kernel walkers
are where silent miscompilation lives, and they should be fixed first.**

---

## 3c. The second discriminator: is the destroyed information **re-derivable**?

§3a and §3b were enough to triage *structural* gaps (a former the walker never looked
inside). They are **not** enough for a *destructive* walker — one that looks at a node and
writes back something different. For those, the question is:

> **After this walker corrupts the field, does anything downstream reconstruct it from an
> independent source of truth?**

This is the axis that resolved the audit's one genuinely split verdict, and it is worth
stating plainly because the two skeptics who disagreed were **both right**.

`Cure.Elab.Subst` discards the QTT grade on **all three** binder formers — `:pi`, `:lam` and
`:let` — hardcoding `Grade.unrestricted()` in each. One skeptic refuted this as inert; the
synthesiser ranked it the #1 CRITICAL. The reconciliation:

- **For `:pi` and `:lam`, the grade is re-derivable, so the corruption is INERT.** The
  refutation is correct and its mechanism is exact: `Kernel.infer(ctx, {:app, f, a})`
  (`kernel.ex:155-166`) re-infers `f`'s type **from the registered declaration** via
  `Context.signature/1`, reached through the *trusted* `Core.Term.subst` — never through
  `Elab.Subst`. The grade compared at `kernel.ex:324-329` therefore comes from the real
  signature, not from any `Subst`-corrupted intermediate. The elaborator is untrusted by
  design, and here that design holds: a wrong grade on a Pi is caught, not believed.

- **For `:let`, the grade is re-derivable from NOTHING, so the corruption is CRITICAL.** A
  `let`'s grade is not in any signature. It exists **only in the term itself**. And the term
  is the one thing `Subst` just rewrote. Hand-verified:
  - `Kernel.infer(ctx, {:let, _g, …})` — `kernel.ex:126` — **binds the grade to `_g` and
    ignores it.**
  - `Kernel.check(ctx, {:let, _g, …}, exp)` — `kernel.ex:349` — **same.**
  - `Erase.erase({:let, _g, …})` — `erase.ex:48` — **discards it and rewrites to ω.**
  - `Relevance.walk({:let, g, …})` — `relevance.ex:260` — **the only reader in the codebase.**

  The kernel is deliberately quantity-blind (`declarations.ex:532`: *"E-layer; the kernel
  stays quantity-blind"*). That is a defensible design — **but it means the E-layer's single
  usage check is load-bearing for soundness, and it means an E-layer walker that overwrites
  a grade is not "untrusted scratch." It is the last word.**

**Generalised rule.** *A walker that only omits structure is bounded by §3a/§3b. A walker
that overwrites a field is only safe if some later, independent authority re-derives that
field. Find the re-deriver before you call it inert — and if the field's sole authority is
the term, there is no re-deriver.*

---

## 4. Confirmed defects

All hand-verified. Ordered by severity.

### 4.0 `Subst` skips `effect_pure`/`effect_bind` → **silent miscompilation** · **CRITICAL**
> **RESOLVED (§10).** Fixed in `lib/cure/elab/subst.ex`; `test/cure/elab/subst_effect_traversal_test.exs` (8) red→green.
`lib/cure/elab/subst.ex:75` and `:115`

*(This subsumes what was filed as §4.3 in the first draft; the adversarial pass established
reachability and it escalated past everything else.)*

`replace/4` and `shift/3` have an explicit clause for `{:effect_type, inner}` (`:64`, `:104`)
but **none for `{:effect_pure, t}` or `{:effect_bind, e, k}`**. Both fall to the catch-all
(`do: other`) and are returned **byte-identical, with zero recursion into their subterms**.

**What it silently does.** `instantiate/2` is documented to replace a telescope's binders and
*strengthen every free variable past the telescope*. Any `{:var, i}` nested inside an
`effect_pure`/`effect_bind` is neither substituted nor strengthened. When the surrounding
binders are peeled away, that variable is left **pointing at the wrong binder, or at one that
no longer exists.** No error is raised.

**Reachability — HAND-VERIFIED. Read this carefully, because one skeptic refuted a
*different* route to the same function and the distinction matters.**

*The refuted route (do not chase it):* a do-block becoming a **metavariable's solution**, later
corrupted by `force_d`'s `Subst.shift`. **Dead.** Per §3a, `Unify.unify`'s operands are
type-level terms exclusively — an argument's *value* is appended to `chosen` and never unified.
Effect values never reach `force_d`.

*The live route (this is the bug), verified by reading `erase.ex:146-154` directly:*

```elixir
def erase(env, {:case, s, m, [{cname, arity, body}] = branches}) do
  if collapsible_ctor?(env, cname, arity) do
    body
    |> Cure.Elab.Subst.instantiate(List.duplicate({:ctor, :cure_erased, []}, arity))
    |> then(&erase(env, &1))
```

`body` is a **branch body — a value-level term.** It can absolutely contain effect nodes; we
know this for certain because `erase/2`'s *own* clauses eight lines below explicitly handle
`{:effect_pure, _}` / `{:effect_bind, _, _}`, with a comment insisting they must never be
dropped.

**The corruption is in the *strengthening*, not the placeholder substitution.** This is the
part the finder got fuzzy and it is worth stating precisely. `instantiate/2` does two jobs:

1. replace `{:var, i}` for `i < arity` (the branch's erased pattern binders) with the
   placeholder — *harmless, those binders are surface-inaccessible*; and
2. **strengthen every outer reference**: `{:var, i}` for `i >= arity` becomes `{:var, i - arity}`,
   because collapsing the case **deletes those `arity` binders from the context.**

Job (2) is the one that matters, and it is precisely what gets skipped. An outer variable
sitting inside an `effect_bind`/`effect_pure` is returned **unchanged** by the catch-all, so it
still counts past `arity` binders **that no longer exist**. It does not dangle — it **silently
resolves to the wrong enclosing binder.**

**Consequences, in order:**

1. Erasure runs **strictly after** kernel typechecking and **its output is never re-verified**
   (§3b); `emit.ex:354` hands it straight to `peel_params`/`lower`.
2. So the wrong-variable reference is **never caught**. It emits wrong BEAM code, or crashes
   emit on an out-of-range index. There is no third outcome.
3. `relevance.ex:4-7` states the invariant this breaks in as many words: *"`Erase.erase`
   produces [a term that] never references a binding that no longer exists."*

**Trigger.** A collapsible family is single-constructor with all fields erased and `arity ≥ 1`
— the code's own comment names `Equivalent`'s `reflexive`, i.e. **the identity type**, and the
identity-type-as-inductive work is active. So: *an effect-returning function that pattern-matches
an equality proof and then references one of its own parameters inside a `do` block.*

```cure
fn f(x: Int, p: Equivalent(x, y)) -> Effect(Unit) =
  match p
    reflexive -> do
      print(x)      # <-- {:var, N} inside an effect_bind; never strengthened
      pure(unit)
```

That is not an exotic shape. It is dependent types plus BEAM effects — the two things the
language exists to combine.

**Why this is provably an oversight and not a design decision.** Three *other* walkers get
this right, including one in the TCB:

- the **kernel's own** `Term.shift`/`Term.subst` (`core/term.ex:204-206`, `:293-295`) — handle both;
- `declarations.ex:2007-2011` `beta_substitute` — handles both;
- `erase.ex:160-166` `erase/2` itself — handles both, with a comment that reads like a warning
  written by someone who had just been bitten: *"Effect nodes are NEVER dropped… Without these
  they hit the identity catch-all."*

The author of `erase/2` was alert to exactly this hazard — and the `Subst.instantiate` call
**eight lines above it, on the same body**, was not given the same treatment.

**Fix.** Two clauses per function. `effect_type`/`effect_pure` are congruence; `effect_bind`
recurses into both subterms **at the same depth** — the node itself binds nothing (the binder
lives in the `lam` it contains), exactly like `:app`.

---

### 4.2 `Subst.shift` launders the grade off a `let`, defeating the only check that reads it · **CRITICAL — soundness**
> **RESOLVED (§10).** Fixed in `lib/cure/elab/subst.ex`; `test/cure/elab/subst_grade_laundering_test.exs` (5) red→green.
`lib/cure/elab/subst.ex:93-95` (`shift`) and `:53-55` (`replace`)

**This is the most serious defect in the audit, it was ranked below three other findings in
the first draft, and the thing that surfaced it was §3c.** The whole chain below is
hand-verified against the source.

```elixir
def shift({:let, _g, t, v, b}, amount, cutoff),
  do: {:let, Cure.Core.Grade.unrestricted(), shift(t, ...), shift(v, ...), shift(b, ...)}
#            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ the binder's grade, overwritten
```

Every binder clause in `replace/4` and `shift/3` binds the incoming grade to `_g` and
hardcodes `Grade.unrestricted()`. Per §3c, on `:pi`/`:lam` this is inert — the kernel
re-derives those grades from the declaration. **On `:let` nothing re-derives anything.** The
grade lives only in the term, and `Subst` just overwrote it.

**The chain, link by link.**

1. **A user can write a graded `let`.** The parser accepts one (`parser.ex:2589-2619`) and
   attaches the grade to the binder — `let pf :erased = proof_of(x)`. Grades are
   `:erased | :linear | :affine | :unrestricted` (`grade.ex:60`). `elaborator.ex:5344`/`:5495`
   build `{:let, grade, …}` carrying the **real** grade.

2. **`wrap_join` shifts every branch body of a join-eligible `case`** (`elaborator.ex:4617-4620`):

   ```elixir
   {c, arity, body} -> {c, arity, Subst.shift(body, 1, arity)}
   ```

   "Join-eligible" is an *ordinary* match: a default arm, ≥2 uncovered constructors, no
   carried index, non-dependent motive (`join_point?`, `:4582`). So: **any graded `let`
   inside a matched arm of an ordinary `case` goes through `Subst.shift` — and comes out `ω`.**

3. **`Relevance` is the only thing in the codebase that ever reads a `let` grade** (§3c):
   `kernel.ex:126` and `:349` bind `_g` and ignore it; `erase.ex:48` rewrites it to ω.
   `relevance.ex:260` is the sole reader, and it runs on the **final assembled body**
   (`declarations.ex:536`, `Relevance.check(env, sig.name, quantities, body_term)`) —
   i.e. **strictly after** `wrap_join` has already laundered the term.

4. **With the grade now `ω`, the check disarms itself.** `Grade.restricted?(:unrestricted)`
   is `false`, and `admits?(:unrestricted, used)` is `true` for **every** usage count
   (`grade.ex:132`). So the binder carries no obligation: an `:erased` binder may be
   returned, scrutinised, or passed in a present position; a `:linear` binder may be dropped
   or used twice. **Undetected, with no diagnostic, in a program that compiles.**

**Why this is damning rather than merely bad.** Read `relevance.ex:260`'s own comment:

> A user-written `let g :linear = λ …` that happens to match the join shape has a restricted
> grade `g`, so it takes the generic path below, where `check_binder(st, depth, g, …)`
> enforces g's own obligation (**found by the un-join red-team: skipping it accepted a linear
> closure dropped in some branch**).

A red team **already found this failure mode**, and the fix they landed was to branch on
`Grade.restricted?(g)` — i.e. **to trust the grade in the term**. That fix is correct and it
is defeated upstream: by the time `Relevance` reads `g`, `Subst.shift` has set it to `ω`, so
`restricted?/1` answers `false` and the guard never fires. **The guard is sound; the term it
guards has been laundered before it arrives.**

This is the audit's thesis in its purest form. The bug is not that someone forgot a clause —
it is that a walker nobody thought of as authoritative (a de Bruijn renumberer!) is silently
the last writer of a field that a *soundness check* is the only reader of.

**Blast radius.** This is the discipline that makes erasure safe. `relevance.ex:4-7` says so:
the `{0,ω}` check exists because *erasure will drop the `:erased` slots, so reject any body
that uses one relevantly.* Defeat it and an erased proof term is dropped by `Erase` and then
referenced at runtime.

**Trigger (needs a red test — §7.1):** a graded `let` in a matched arm of an ordinary
`case` with a default arm and ≥2 uncovered constructors. Nothing exotic:

```cure
match c
  A(x) -> let pf :erased = proof_of(x)   # grade → ω on the way to Relevance
          use(pf)                        # relevant use of an erased binder: ACCEPTED
  _    -> fallback()
```

**Fix.** Thread `g`. Six clauses, one substitution each — `{:let, g, …}` instead of
`{:let, Grade.unrestricted(), …}`, exactly as the trusted `Core.Term.shift`/`subst`
(`term.ex:190-191`, `:277-278`) already do. This is E-layer, zero TCB. **Do not fix it
without the red test in hand first** — a fix this small must be *proven* to have closed
something.

*Note: `Erase.erase`'s identical grade-discard (`erase.ex:48`) is harmless — erasure runs
after the last grade reader, so the output grade is dead data. Leave it or thread it for
hygiene, but it is not part of this defect.*

---

### 4.1 `has_meta?` — **REFUTED.** See §9.

Filed as CRITICAL in the first draft. Both skeptics refuted it independently and they were
right; the reachability argument is recorded in §9 so it is not re-litigated. What survives
is tech debt, not a defect: the local `has_meta?` is structurally incomplete *and* a complete
`Unify.has_meta?/1` already exists and is used elsewhere in the same file. Swap the call, for
consistency and defence in depth — but do not report it as a bug found.

---

### 4.3 — *(promoted to §4.0 after adversarial verification established reachability)*

---

### 4.4 TCB · `subst_params` and `replace_branch_vars` fail open inside the kernel  · **HIGH** (severity pending probe)
> **DOWNGRADED — NOT FIXED (§10.2).** The probe this section demanded was run and it
> **exonerated the kernel**: both walkers are *fail-safe*, not fail-open-unsound. No red test
> exists, so under the TCB HARD-STOP rule `kernel.ex` was left untouched. **Do not "fix" this
> without first reading §10.2** — a naive repair changes kernel behaviour with no failing test
> to justify it.
`lib/cure/core/kernel.ex:1244` and `:1561`

```elixir
defp subst_params(other, _pmap, _depth), do: other          # :1244
defp replace_branch_vars(other, _subst), do: other          # :1561
```

Both are **in the trusted kernel**. Both enumerate `:pi :lam :app :data :ctor :case` and
**omit `:let` and the entire `Effect` family**, then fail open.

These two implement dependent pattern matching's index refinement: `replace_branch_vars`
applies the substitution derived from GADT index unification to a branch body
(`:1523`, `:1535`, `:1572`), and `subst_params` substitutes data-type parameters (`:1201`).

**What it silently does.** A branch body containing a `let` or an effect node has the
refinement substitution applied to *everything except* the interior of that node. The
interior keeps its pre-refinement variables. Because the branch binders still exist (arity is
unchanged), those variables still *resolve* — to the **un-refined** value. The kernel then
checks the body against a motive in which the index **has** been refined.

**Direction of failure — argued, not yet proven.** Refinement makes types *more* specific, so
skipping it should leave the body *more general* and cause a **conversion failure**
(completeness bug: a good program rejected, mysteriously). I can construct no case where
skipping a refinement makes an ill-typed program check. **But this is the TCB, and "I could
not construct one" is not a proof.** A discriminating probe is mandatory before this severity
is settled (§7.2). Under the standing rule, any TCB change here needs an Antigen antibody, the
full Antigen suite, and the full gate.

---

### 4.5 `mabs/5` — Miller-pattern abstraction skips `:let` and `Effect`  · **LATENT, not live**
> **REPAIRED (§10).** Clauses added in `lib/cure/elab/unify.ex`. Latent confirmed: no observable
> defect, so no test. Its catch-all was deliberately left **open** — see §10.3.
`lib/cure/elab/unify.ex:269` · catch-all `do: leaf`

The gap is real: `mabs` abstracts pattern variables out of a term when solving `?F(x̄) := t`,
and a `{:var, k}` inside a `:let` or effect node would be neither abstracted nor shifted,
producing a misnumbered solution.

**But it cannot be reached today, and the skeptic proved it via §3a**: all 12 `Unify.unify`
call sites unify **type-level terms only**, and `:let`/`effect_pure`/`effect_bind` are
structurally excluded from types (closed `idx_to_core` grammar; no `:vlet` in `Value.t()`).
Nothing can hand `mabs` one of these formers.

Worth fixing anyway — as **insurance**, not as a bug. The moment `idx_to_core` is extended to
accept `let`/do-block syntax at the type level (a plausible extension), this becomes live and
silent. The tell is that its sibling **twelve lines away**, `escapes?`, was *already patched to
fail closed against this exact hazard* (`unify.ex:385-401, :435`) and carries a comment
explaining why. Same file, same author, same week — one walker learned the lesson and the one
next to it did not. Flip `mabs`'s catch-all to fail closed and the asymmetry disappears.

---

### 4.6 `global_refs` — the `:let` reachability bug, reintroduced for `Effect`  · **LOW** (tooling only)
> **RESOLVED (§10).** Fixed in `lib/cure/elab/program.ex`; `test/cure/elab/reachability_effect_test.exs` (2) red→green.
`lib/cure/elab/program.ex:838` · catch-all `do: []`

**The most instructive finding in the audit, and — after the critic's reachability check —
one of the least dangerous.** Both facts matter.

The fix for its twin is **three lines above it** (quoted in §1). `global_refs` now handles
`:let`. It does **not** handle `effect_type` / `effect_pure` / `effect_bind`. A def whose
body sequences effects — `x <- helper(); pure(x)`, elaborating to
`{:effect_bind, {:app, {:global, :helper}, _}, {:lam, …}}` — reports **no global reference to
`helper`**, so `reachable_def_names/2` omits it.

**Downgraded from MEDIUM on a verified reachability finding.** The critic checked the actual
consumer, and I confirmed it: **nothing in `lib/` calls `reachable_def_names/2`.** The
production `.cure`→BEAM path (`compiler.ex:411`) emits every syntactically-declared def
regardless of reachability, so no compiled program can be affected. The function's only
consumers are **test/tooling harnesses** (`Emit.compile_and_load(env, functions:
Program.reachable_def_names(env, roots))`, e.g. `test/cure/elab/reachability_let_test.exs`).
There it reproduces the original failure mode exactly — silently omits a real dependency,
`UndefinedFunctionError` later — but it cannot ship wrong code to a user.

Keep it in §4 anyway, at LOW, because **it is the audit's clearest proof that the bug class
regenerates**: someone diagnosed this precisely, wrote the diagnosis down, fixed one former
in one walker, and did not sweep. The next former walked straight back into it.

---

### 4.7 `count_level` — the un-join safety gate is blind to `Effect`  · **MEDIUM**
> **UPGRADED to CONFIRMED SOUNDNESS HOLE, then RESOLVED (§10.1).** This section's own hedge —
> "the unsound-accept outcome exists but is narrower than implied" — was too generous to the
> code. A **working exploit** was built: an `:affine` parameter used **twice** and accepted.
> Fixed in `lib/cure/elab/relevance.ex`; `test/cure/elab/relevance_count_level_effect_test.exs`
> (3) red→green. This is the most serious defect the audit found, and it was ranked fifth.
*(Found by two independent lenses. Severity **settled at MEDIUM**, not the HIGH of the first
draft: the unsound-accept outcome exists but is narrower than "permits too much" implied.)*
`lib/cure/elab/relevance.ex:451` · catch-all `do: 0`

`count_level` answers "how many times does variable `t` occur here?" and `join_binder_safe?`
(`:414-430`) consumes it as a **safety gate**: a branch must be *provably free* of the join
binder before `walk_join_branches` may count that binder's captures **once, unscaled** instead
of ω-scaled.

**What it silently does.** For any `Effect`-wrapped subterm it returns **`0`** — "the variable
does not occur" — indistinguishable from genuine absence. And the trigger is *ordinary*, not
contrived: a sequential-effect branch (`B -> let r = some_effect(); cont(r)`) elaborates via
`effectful_let_bind` (`elaborator.ex:5510-5518`) to a body whose **top-level** former is
`{:effect_bind, …}`. `count_level` zeroes the entire branch out **without ever looking at
whether the join binder occurs in it.**

Its sibling `walk/4` **in the same file** (`:353-373`) was already patched for these three
formers, with a comment describing this exact class of bug (*"Without this clause … NO usage
inside it … was ever counted"*). `count_level`, a few dozen lines below, was not.

**Why MEDIUM and not HIGH — the polarity is grade-dependent.** For a `:linear` capture the
outcome is a **spurious rejection** (`Grade.leq(:erased, :linear)` is `false`) — annoying,
safe. The unsound direction requires `:affine` specifically: `Grade.leq(:erased, :affine)` is
`true` **by design** (`grade.ex:147`, the deliberate 0-or-1 subusaging exception), so a
genuinely double-used affine capture can pass a check whose whole job is to reject exactly
that. Real, but narrow.

**Fix:** give `count_level` the same three Effect clauses `walk/4` already has.

---

### 4.8 `has_hole?` — a hole inside an effect is invisible  · **LATENT, not live**
> **RESOLVED (§10).** Fixed in `lib/cure/elab/erase.ex`; `test/cure/elab/erase_has_hole_effect_test.exs` (4) red→green (unit-contract, not surface — see that file's moduledoc).
`lib/cure/elab/erase.ex:200` · catch-all `do: false`

Handles `:let` (swept) but not the `Effect` family, while its sibling `erase/2` immediately
above (`:160-166`) handles all three. So the walker **is** incomplete.

**But the bad state is unreachable today, and the skeptic proved it.** A surface hole cannot
currently get inside an effect node: `elaborate_declared_body` (`declarations.ex:600-606`)
tests `effect_goal?` **first** and routes effect-typed bodies to `elaborate_effect_branch`,
which — like `elaborate_expr_checked` and `elaborate_expr_typed` — has **no `{:hole, …}`
clause at all** and hard-errors instead. Such a definition therefore fails to elaborate and
never reaches `Env.defs`, so `hole_goals/1` can never be asked about it. The only Core hole
that lands in `Env.defs` is the bare top-level one, which `has_hole?`'s **first** clause
already handles.

Recorded as **latent hygiene**, not a live defect: it becomes a real bug the moment anyone
adds a route for holes inside effectful bodies — which is a plausible near-term change. Fix it
while fixing §4.0 (same file, same trio of clauses); do not claim it as a bug found.

*This is the audit working as intended. The lens found a genuine structural gap; the skeptic
established that nothing can currently drive it. Both facts are worth having, and conflating
them would have been the easy, wrong outcome.*

---

### 4.9 Dead retry on the dotted-qualified call path  · **LOW**
> **RESOLVED (§10).** Dead branch removed in `lib/cure/elab/elaborator.ex`. The *sibling* retry on the
> non-lambda path is **load-bearing** and was kept — see §10.3.
`lib/cure/elab/elaborator.ex:269-288`

A sibling of the dead retry deleted in `a8b4e7e9`, and the same shape: in
`elaborate_named_call/5`'s qualified-plain-global clause, when `args` contains a lambda,
`:272` calls `elaborate_implicit_app_bidirectional(env, resolved, args, names, ctx)`; on
`{:error, _}`, `:284` calls **the same function with the same five bindings** — both omitting
the optional 6th `expected`, which defaults to `nil` identically. Nothing is reassigned
between them, and the function is pure (fresh `MetaCtx.new/0`, no process state that could
flip an error to success). The retry is **guaranteed** to fail identically.

Wasted work only — the surfaced error is unchanged — but it re-runs Miller-pattern solving
over the whole argument list on every such failure.

**Fix:** drop the retry **in the lambda sub-branch only**. The non-lambda sub-branch's retry
is *legitimate* and must stay: it runs a genuinely different algorithm
(`map_present_args` + `elaborate_global_app` vs. `elaborate_implicit_app_bidirectional`).
Deleting both would be the easy wrong fix.

---

## 5. Coverage matrix

Mechanically derived: for each walker, which of the ten *compound* formers it explicitly
matches. `--` = falls to the catch-all. Read **only** with §3 in hand — a `--` in a Class A or
Class B walker is not a defect.

| walker | pi | lam | let | app | data | ctor | case | eff_type | eff_pure | eff_bind | class |
|---|---|---|---|---|---|---|---|---|---|---|---|
| `core/kernel.ex subst_params` | OK | OK | -- | OK | OK | OK | OK | -- | -- | -- | **C** |
| `core/kernel.ex replace_branch_vars` | OK | OK | -- | OK | OK | OK | OK | -- | -- | -- | **C** |
| `core/kernel.ex rigid_index?` | OK | -- | -- | -- | OK | OK | -- | -- | -- | -- | B |
| `core/meta_check.ex canonical_head?` | OK | OK | -- | -- | OK | OK | -- | OK | OK | OK | B |
| `core/term.ex has_free_var?` | OK | OK | OK | -- | -- | -- | OK | -- | -- | -- | A |
| `core/validator.ex children` | OK | OK | OK | OK | OK | OK | OK | -- | -- | -- | A |
| `core/printer.ex print` | OK | OK | OK | OK | OK | OK | OK | -- | -- | -- | C (cosmetic) |
| `elab/subst.ex replace` | OK | OK | OK | OK | OK | OK | OK | OK | -- | -- | **C** |
| `elab/subst.ex shift` | OK | OK | OK | OK | OK | OK | OK | OK | -- | -- | **C** |
| `elab/elaborator.ex has_meta?` | OK | OK | -- | OK | OK | OK | -- | -- | -- | -- | **C** |
| `elab/elaborator.ex generalize` | OK | OK | -- | OK | OK | OK | OK | -- | -- | -- | **C** |
| `elab/elaborator.ex replace_branch_vars` | OK | OK | -- | OK | OK | OK | OK | -- | -- | -- | **C** |
| `elab/elaborator.ex abstract_term` | OK | OK | -- | -- | -- | -- | OK | -- | -- | -- | A |
| `elab/elaborator.ex free_indices` | OK | OK | -- | -- | -- | -- | OK | -- | -- | -- | A |
| `elab/elaborator.ex occurs_below?` | OK | OK | -- | -- | -- | -- | OK | -- | -- | -- | A |
| `elab/unify.ex mabs` | OK | OK | -- | OK | OK | OK | OK | -- | -- | -- | **C** |
| `elab/unify.ex escapes?` | OK | OK | -- | OK | OK | OK | OK | -- | -- | -- | B |
| `elab/unify.ex do_unify_struct` | OK | OK | -- | OK | OK | OK | -- | OK | -- | -- | (see §7.4) |
| `elab/erase.ex has_hole?` | OK | OK | OK | OK | OK | OK | OK | -- | -- | -- | **C** |
| `elab/program.ex global_refs` | OK | OK | OK | OK | OK | OK | OK | -- | -- | -- | **C** |
| `elab/relevance.ex count_level` | OK | OK | OK | OK | OK | OK | OK | -- | -- | -- | **C** |
| `elab/resolution.ex rekey_term` | OK | OK | -- | OK | OK | OK | OK | -- | -- | -- | **C** (owned elsewhere) |
| `elab/totality_closure.ex collect` | OK | OK | -- | OK | OK | OK | OK | -- | -- | -- | A |

**Formers missing across the 25 walkers:** `effect_pure` **24**, `effect_bind` **24**,
`effect_type` **21**, `:let` **15**, `:app` 6, `:data` 5, `:ctor` 5, `:case` 4, `:lam` 1,
`:pi` 0.

The gradient is the audit's whole story: **the older the former, the better covered.** `:pi`
is universal; `:let` is missing from 60% of walkers; the `Effect` family from ~95%. Coverage
is a direct function of *how long the former has existed*, which is precisely what "drift"
means and precisely what a type system is supposed to prevent.

---

## 6. The systemic fix

Patching twelve walkers by hand fixes today's formers and guarantees this recurs at former 25.
The recurrence is the defect. Options, in ascending order of strength:

1. **Sweep + regression test.** Fix the twelve; add a test that enumerates
   `Core.Term.t()`'s formers and asserts each Class C walker handles every compound one.
   Cheap; catches the next former **only if someone remembers to extend the enumeration**.

2. **Make the catch-alls fail closed.** Convert Class C catch-alls to raise on an unrecognised
   compound former. The next former added breaks the build loudly at every site that must be
   updated. This is the `escapes?` doctrine applied uniformly, and it converts a silent
   wrongness class into a compile-time error class. **Recommended.**

3. **Derive the traversals.** A single generic fold over `Core.Term` (a `Traversable`/
   `children`+`rebuild` pair — `Validator.children/1` is already 80% of it), with walkers
   expressed as folds. Eliminates the class by construction. Bigger change; the depth-tracking
   walkers (§3's caveat: binder nodes must bump `depth`, so a naive tuple-fold is *wrong* for
   them) need the fold to carry binder arity per former — which is exactly the information
   `Core.Term` should be publishing anyway.

(2) and (3) compose: fail closed now, derive later.

**Note on TCB scope.** §4.4 is a kernel change and is gated accordingly. Everything else in
§4 is E-layer and carries no TCB risk. §4.2's grade threading is arguably *restoring* the TCB
contract the kernel already implements in `core/term.ex`, not changing it.

---

## 7. What to do next — probes, in order

The house rule is that *"I could not construct a counterexample"* is not a proof. Everything
below is a **probe**, not an argument.

**No fix should be attempted before its red test exists.** Both CRITICALs are one-line-per-clause
fixes in a 116-line file, which is exactly the situation in which a fix silently changes nothing
and everyone declares victory.

1. **§4.2 — the red test, first, before anything else.** A graded `let` in a matched arm of a
   join-eligible `case` that *relevantly uses an erased binder*. It should **compile today**
   (that is the bug) and be **rejected by `Relevance` after the fix**. This is the highest-value
   single action in this document: it is a soundness hole, the trigger is an ordinary surface
   shape, and the fix is six clauses.
2. **§4.0 — the second red test.** The `Equivalent`/`reflexive` + `do`-block shape should fail
   *today* at emit, with a wrong or unbound variable. Confirm the failure before fixing; keep
   it as the regression test.
3. **§4.4 direction — TCB.** Can skipping index refinement inside a `let`/effect in a branch
   body ever make an ill-typed program *check*, or only make a well-typed one fail? Settle by
   probe, not argument. Any fix needs an Antigen antibody + the full gate, per standing rule.
4. **`do_unify_struct`** fits none of the three classes — its fallthrough (`unify.ex:316`)
   attempts δ-conversion rather than returning a verdict. Given §3a it is probably inert, but
   it has not been read.
5. **The systemic fix (§6).** Do it *after* the two red tests are green, not instead of them.

### 7b. Antigen — the real indictment

**None of these were caught.** The shape-coverage manifest reports **318/318 cells**, and that
number is *true* and *useless here*: it measures **kernel** shapes, and every live defect in
this document is in an **E-layer walker** that no cell exercises. A coverage cell per
**(walker × former)** — mechanically enumerable from `Core.Term.t()` — would have caught all of
them on the day each former landed.

**The metric was green while the bug class was wide open.** That is the most important single
thing the audit found, and it is not a bug in any walker.

---

## 8. What this audit did NOT cover

*(From the completeness critic, kept because an audit that does not say where it did not look is
a marketing document. Nothing below is a finding — these are **un-searched areas**, ranked by how
much it would hurt to be wrong about them.)*

The 13 surviving findings cite **six files**. `lib/cure/elab` is 19 files / 17,222 lines;
`lib/cure/core` is 17 files / 6,325 lines. In `core/`, only `kernel.ex` was grazed — two lines.
Everything else has **zero findings anchored in it**, and mostly zero attention.

1. **`core/kernel.ex` (1,629 lines) — the TCB's own exhaustiveness was never the target.** Every
   finding here treats `kernel.ex` as the *ground truth* to diff E-layer walkers **against**;
   nobody asked whether its own matches over `Core.Term`/`Core.Value` are exhaustive. This is the
   worst possible place for a fail-open catch-all, because there is **no re-check downstream of
   the kernel**. And there is direct evidence the authors have been bitten here before:
   `check_coverage` (`:1042`) carries **two hand-added, explicitly-documented "coverage soundness
   hole" bridges** (`{:nat_lit,_}`↔`Z/S` at `:1281`; `{:bounded_lit,_}`↔`First/Next` at `:1298`).
   A third literal/constructor duality — or the next Core former — hitting `unify_one`'s generic
   rigid-head-clash fallback would be verdicted `:impossible` when it is actually reachable, and
   `check_coverage` would accept a `case` that omits a real constructor.
2. **`core/certificate.ex` (664) — `terminating?/3`, the structural-termination checker, is
   entirely unaudited.** `Kernel.validate_certificate/2` (`:630`) calls it to decide whether a def
   may be δ-certified. If *its* walker fails open on a call shape it doesn't recognise — say, a
   recursive call inside a `:let` or an `:effect_bind` continuation, **the exact two formers every
   finding in this document shows getting dropped** — it certifies a non-terminating function for
   type-level computation. That is non-normalising δ-reduction feeding the conversion checker.
   Note the contrast that makes this sharp: `totality_closure.ex` *was* checked and **is**
   hardened (fails closed, with a comment naming this bug class and citing
   `Certificate.walk_node/4` as an already-patched sibling). Its neighbour — the file
   `walk_node/4` actually lives in — was never opened.
3. **`core/conv.ex` (285) — definitional equality itself was never a target.** If `conv`'s
   dispatch over paired `Value` shapes treats an unrecognised pair as *convertible* rather than
   rejecting, that is the most direct unsoundness available. This is not hypothetical: it is
   **literally the mechanism of the `Effect(T)` motive bug already in the memory index**
   (`infer_type_value_sort` lacking a `{:veffect_type}` case) — the same shape of bug, one layer
   over.
4. **`elab/coherence.ex` (92) + `implementation.ex` (358)** — typeclass coherence / instance
   overlap. Named in the task brief; no lens ran. If the `(iface, head)` key computation under- or
   over-normalises through transparent synonyms, two conflicting anonymous instances register
   without error and dictionary resolution silently picks one.
5. **`elab/resolve.ex` (319) + the bulk of `resolution.ex` (508)** — import/qualified-name
   resolution. Only `rekey_term`'s catch-all was cited, and only as someone else's known bug.
   Memory already flags this area as fragile twice over. A qualified call resolving to the local
   shadowing def instead of the imported one is *wrong semantics, no crash*.
6. **`elab/macro_expand.ex` (263)** — zero coverage, and per the memory index this is the last
   open macro gap. Nightmare: hygienic renaming misses a binder shape a macro introduces, so a
   macro-injected variable silently captures a user variable. **Note for the macro branch: none
   of §4's defects are in macro code** (expansion is surface→surface at `program.ex:383` and
   never touches `Elab.Subst`), so it is not blocked by this audit — but macro-*generated*
   effectful code is exposed to §4.0 like any other code, and this file is the obvious place to
   point the next audit.
7. **`elab/union.ex` (658) + `guard_lint.ex` (249)** — anonymous-union coverage and pattern-guard
   exhaustiveness, both adjacent to coverage checking, no lens. Anonymous ADTs are recent.

### 8b. The one suspicious silence

Eight lenses were declared. **Seven produced findings. "Metavariable lifecycle (zonk/occurs/
scope)" produced none — and never appears as a lens tag at all.**

The critic checked the obvious targets rather than trusting the silence: `Unify.zonk/2`
(`:465`) is a generic tuple/list walk, `Inductive.occurs?/4` (`:696-721`) is a generic walk with
a fail-closed leaf default. Both look deliberately hardened, so the silence *may* be legitimate.

**But nothing demonstrates that lens ever ran against `solve/4`'s Miller-vs-first-order dispatch,
or against how a coherence/dictionary metavariable gets zonked before crossing into kernel-checked
code. And this cycle's headline bug — `bidir_app_slot`/`resolve_deferred_slots` — *was* a
metavariable-lifecycle defect.** A second instance of that exact shape is the single most
plausible thing still hiding, and no finding in this document rules it out.

---

## 9. Findings NOT confirmed (recorded so they are not re-litigated)

Kept deliberately, with the refuting argument, so nobody "rediscovers" them.

- **`has_meta?` letting an unsolved metavariable reach the kernel** (`elaborator.ex:7344-7350`)
  — filed **CRITICAL in the first draft of this document**, and **REFUTED** by both skeptics
  independently. I hand-checked their argument and they are right.

  The *textual* claim is entirely true: the local `has_meta?` handles 5 of 10 compound formers
  and falls to `_ -> false` for `:case`/`:let`/`effect_*`, while a structurally-complete
  `Unify.has_meta?/1` (`unify.ex:456`) exists **in the same file** and is used at five other
  call sites. What is false is the **trigger**. A `:case`/`:let` term can never reach an outer
  `has_meta?` gate while still carrying a live meta, because **every construction site
  kernel-checks itself before returning**: `elaborate_expr_typed({:pattern_match,…})` calls
  `Kernel.check(ctx, term, result_type_val)` at `:723-724` *inside the same clause*, before
  `{:ok, term, …}` is returned (verified directly); `elaborate_expr_checked({:pattern_match,…})`
  does the same at `:1518-1519`; `elaborate_expr_typed({:block,…})` at `:600-601`; and
  `declarations.ex:588-593` re-checks the whole assembled body regardless. `Kernel.infer` has no
  `{:meta,_}` clause and no catch-all, so a live meta nested in a branch **aborts there**. And a
  meta that is a *direct* element of `chosen` — which is what the deferred-slot machinery
  actually produces — is caught by `has_meta?`'s **first clause**, no recursion needed.

  Worst case is therefore a `FunctionClauseError` instead of a clean `:unsolved_metavariables`,
  in a scenario neither skeptic could show is reachable at all. **Not a soundness finding.**
  Residual action: swap the local `has_meta?` for `Unify.has_meta?` — defence in depth and one
  less misleading bespoke walker. **File it as tech debt, not as a bug.**

  *Why I got it wrong: I reasoned from the broken invariant ("this gate is incomplete, and the
  gate's job is soundness") and never asked whether anything else already enforced it. The
  elaborator's comments say the caller re-checks; I read that as an empty promise. It is not.*

- **`Subst` discarding the QTT grade on `:pi` and `:lam`** — **REFUTED as inert**, and this
  refutation is *correct and important*: it is what allowed §4.2 to be stated precisely instead
  of as a vague "grades get mangled." The kernel re-derives Pi/Lam grades from the registered
  declaration via `Context.signature/1` and the trusted `Core.Term.subst`, and compares at
  `kernel.ex:324-329` — never consulting `Elab.Subst`'s output. A wrong grade on a Pi is caught,
  not believed. The elaborator being untrusted is doing real work here.

  **This does NOT extend to `:let`** (§3c, §4.2): a let's grade is re-derivable from nothing,
  and the same refutation, applied there, is false. *Both skeptics who touched this were partly
  right; the file is wrong in one place and harmless in two others.*

- **`mabs/5` skipping `:let`/`Effect`** (`unify.ex:269`) — **REFUTED as unreachable**, twice, and
  re-verified by the synthesiser reading the source directly rather than re-asserting the prior
  verdict. Every `Unify.unify` operand is built either through `idx_to_core`'s closed grammar
  (`declarations.ex:1658-1805`, whose catch-all *rejects* anything outside its 7 forms, including
  let/do syntax) or via `Quote.reify` of a semantic `Value` (which has no `:vlet`). Neither can
  produce a `:let`/`effect_pure`/`effect_bind` in type position. Real code, structurally dead.
  See §4.5 — worth fixing as insurance, not reportable as a bug.

- **`totality_closure.collect` skipping recursive calls inside `Effect` nodes** — the audit's
  worst-case hypothesis (**a non-total function certified total**). **REFUTED**: `collect/1` is
  Class A (generic tuple descent, `:105`) and does see into effect nodes. This was the single
  highest-severity thing the audit went looking for, and it is not there.

- **`Validator.children/1` missing the effect formers** — **REFUTED**. `validator.ex:384-387`
  has explicit `eff_children` clauses for all three. The codegen release gate is sound; only
  the *diagnostic* `has_hole?` (§4.8) is blind, and that is unreachable anyway.

- **`Relevance.walk` treating `Effect(T)`'s payload as runtime-relevant** (`relevance.ex:373`)
  — reported as a completeness bug falsely rejecting erased type-level uses. **REFUTED on
  reachability, with a thorough trace**: `{:effect_type, _}` can never occur in a `body_term`
  that `Relevance.check` walks. The *only* site in the entire elaborator that recognises the
  surface name `Effect` is `idx_to_core` (`declarations.ex:1696`, `:1807-1821`), which is
  exclusively the **type/index-position** lowerer — never called from body/value elaboration.
  `Effect` is deliberately not registered as a family, global, or constructor, so `Effect(a)`
  in a body position fails name resolution outright. The one construct that *does* put
  `{:effect_type, …}` into a stored def body — `elaborate_typealias` — never calls
  `Relevance.check`. Dead code, not a live rejection.

- **`Erase.has_hole?` under-reporting holes** — **REFUTED as live**; retained as latent hygiene.
  See §4.8 for the reachability argument.

---

## 10. Resolution — what was actually done (2026-07-15)

Remediation followed the audit's own recommendation (§6 option 2): **fix the twelve, and make
the Class C catch-alls fail closed** so former #25 breaks the build instead of the semantics.
Strict red-green throughout — every fix that had an observable defect got a failing test first.

**Two verdicts in §4 were overturned by probing, in opposite directions.** That is the single
most important thing on this page:

| § | audit said | probe said | outcome |
|---|---|---|---|
| §4.2 | CRITICAL — soundness | confirmed | **FIXED** (`subst.ex`) · 5 tests |
| §4.0 | CRITICAL — miscompilation | confirmed | **FIXED** (`subst.ex`) · 8 tests |
| **§4.7** | **MEDIUM**, unsound-accept "narrower than implied" | **CONFIRMED SOUNDNESS HOLE — exploit built** | **FIXED** (`relevance.ex`) · 3 tests |
| **§4.4** | **HIGH**, TCB, "direction argued not proven" | **fail-SAFE, not fail-open-unsound** | **NOT FIXED — deliberately.** §10.2 |
| §4.6 | LOW (tooling) | confirmed | **FIXED** (`program.ex`) · 2 tests |
| §4.8 | LATENT | confirmed latent | **FIXED** (`erase.ex`) · 4 unit-contract tests |
| §4.9 | LOW (waste) | confirmed, *and* half-refuted | **FIXED** (`elaborator.ex`) · §10.3 |
| §4.5 | LATENT | confirmed latent | **REPAIRED** (`unify.ex`), no test · §10.3 |

Files changed: `lib/cure/elab/{subst,relevance,program,erase,unify,elaborator}.ex`. **The TCB
(`lib/cure/core/*`) was not touched.** Gate: **4122/4123**, `136 immune responses (expected)`,
Antigen shape-coverage `318/318`. The single failure is a pre-existing stale Antigen coverage
baseline (`Cure.Core.Eval` floor 89 vs 91, `Cure.Core.Normalise` 103 vs 104) in modules this
work never edited; it was already red at HEAD and was deliberately **not** re-recorded here,
because doing so inside this commit would launder whoever actually added those clauses.

The coverage matrix in §5 is the **pre-fix** snapshot. It has not been re-derived; read it as
the diagnosis, not the current state.

### 10.1 §4.7 is the real finding, and the audit under-ranked it

The audit ranked `count_level` **fifth**, MEDIUM, and softened its own claim to "the
unsound-accept outcome exists but is narrower than implied." That was too kind to the code. The
exploit is short and it is not contrived:

```cure
mod CA
  @extern(:erlang, :display, 1)
  fn lsink(v :linear Int) -> Effect(Int)
  type Two = T | F
  fn f(x: Two, n :affine Int) -> Effect(Int) =
    let k : (Int) -> Effect(Int) = fn(y) -> lsink(n)
    match x
      T() ->
        let a = k(0)
        k(0)              # n is consumed TWICE on this path
      F() -> k(0)
```

`n` is declared `:affine` — **at most one** use. On the `T` path it is used twice. Before the
fix this **elaborated clean**. `count_level` met the branch bodies, whose top-level former is
`{:effect_bind, …}` (that is just what `let r = <effect>; …` elaborates to), returned **`0`
— "the join binder does not occur here"** — and `join_binder_safe?` therefore authorised the
un-join, which counts `k`'s captures **once, unscaled** instead of ω-scaled. Two uses were
counted as zero. After the fix it is
`{:error, {:usage_violation, %{declared: :affine, kind: :param}}}`.

Three properties of this finding are worth keeping:

- **It is `:affine`, not `:linear`.** The walker under-counts *to zero*, and zero **satisfies**
  affine (≤1) while **violating** linear (=1) — so at `:linear` the same bug produces a
  spurious *rejection*, which is safe and therefore invisible. The audit's footnote ² guessed
  this correctly; the exploit confirms it. Anyone hunting this class must probe at `:affine`.
- **The pure twin is the control.** The identical program with `Int` in place of `Effect(Int)`
  was *always* rejected. That isolates the cause to `count_level`'s missing `Effect` clauses and
  nothing else.
- **A one-shot control must stay ACCEPTED.** The third test pins a program the un-join is
  genuinely entitled to optimise. Without it, "disable the un-join" would pass as a fix. The
  optimisation was **repaired**, not disabled.

### 10.2 §4.4 (TCB) — probed, exonerated, NOT changed

The audit demanded a probe before settling this severity. The probe was run and it went the
other way: `subst_params` is **fail-safe**.

`unify_one` has no `effect_type` clause *either*, so two `Effect(…)` indices share a head key,
never produce a rigid clash, and fall through to `:undecided` — and `reduce_index_pairs`
**drops** `:undecided` pairs (documented sound, `kernel.ex:1246`). The case-checker skips a
branch body only on `:impossible`. Net effect: the ill-typed branch is still **rejected** and
the well-typed one still **accepted**. What is lost is index *refinement* — a completeness cost,
not a soundness one. For `replace_branch_vars` no divergence could be constructed at all: the
plain-`t` control fails **identically** to the `Effect(t)` case.

So there is **no red test**, and under the standing TCB HARD-STOP rule a kernel edit without a
failing test is not licensed. `kernel.ex` was left byte-for-byte unchanged. The two walkers are
still *incomplete*, and a future former may well not enjoy the `:undecided` escape hatch that
saves this one — but the fix belongs in a reviewed TCB run with an Antigen antibody, not
smuggled into an E-layer sweep. **Its catch-alls were likewise left open on purpose:** making
the kernel fail closed is itself a kernel behaviour change.

### 10.3 Two places where "fix everything uniformly" would have been wrong

The sweep was deliberately **not** applied mechanically, and twice the mechanical answer was the
wrong one:

- **`unify.ex mabs` (§4.5) keeps its OPEN catch-all.** Clauses for `:let` and the `Effect`
  family were added, but the leaf catch-all was left permissive. `mabs` sits on the unifier's
  hot path and there is no evidence about the full shape domain that reaches it; a fail-closed
  raise there converts an unknown-but-currently-harmless shape into a hard crash on a path the
  audit never characterised. Fail closed where the domain is known; do not fail closed to look
  consistent.

- **The §4.9 retry is only half dead.** The *lambda* sub-branch called
  `elaborate_implicit_app_bidirectional/5` and then, on failure, called it **again, identically**
  — genuinely dead, and removed. The *non-lambda* sub-branch's retry is **load-bearing** and was
  kept: its first attempt runs a **different algorithm** (`elaborate_global_app`), so the retry
  is a real fallback, not a repeat. Deleting both — the obvious reading of "remove the dead
  retry" — would have been a regression.

### 10.4 The fail-closed doctrine paid for itself during the fix

Converting the Class C catch-alls to raise immediately surfaced **two body shapes that reach
these walkers and appear nowhere in `Core.Term.t()`** — neither of which the audit knew about,
and both of which the old catch-alls had been silently swallowing:

- **`{:extern, {mod, fun, arity}}`** — the `Env` body marker for an `@extern` declaration. Not a
  Core former at all, but `global_refs/1` and `has_hole?/1` fold over *every def body*, so they
  meet it.
- **`nil`** — the body of a signature-only declaration.

Both are now **explicit clauses** (`:extern` in the leaf guards; `nil` in its own clause,
deliberately *not* folded into the leaf guard, so that an unknown **former** still raises). The
doctrine caught, on its first day, exactly the class of thing it exists to catch. Note the
implication for §5: the coverage matrix enumerates the ten compound formers, but the real domain
of a body-walker is **wider than `Core.Term.t()`**. Any future generic fold (§6 option 3) must
account for that.

### 10.5 Still open

- **§6 option 3 (derive the traversals).** Not done. Fail-closed is a tripwire, not a cure: it
  guarantees former #25 *breaks the build*, it does not guarantee anyone writes the right clause.
- **The kernel's two walkers (§10.2)** remain incomplete-but-safe. Reach-pin, not a repair.
- **The stale Antigen coverage baseline** (`Cure.Core.Eval`, `Cure.Core.Normalise`) predates this
  work and is still red. It belongs to whoever added those clauses.
