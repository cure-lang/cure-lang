# QTT Graded Binders — Implementation Plan

**STATUS: COMPLETE & CLOSED (2026-07-11).** All eight slices landed and gated on
`core-let-binder`: 1 `4050c81` · 2+3 · 4a `330dca6` · 4b `a5306ed` · 4c `87dcaeb`
· 5a `f5bc929` · 5b `4ab3450` · 6 `4624909`, plus the Conv λ-grade TCB fix
`fc97ed7` that an extended Antigen antibody surfaced.

The adversarial multi-agent review has since **converged** — three red-team rounds
over the whole stack, no accepts-unsound hole surviving. It drove the F11 join-point
over-rejection to a real fix: the usage checker now **un-joins** the slice-4c join
idiom (counts the shared continuation's captures once, Idris-per-branch) — landed
`a844b53`, with four soundness fixes the red-team caught (`e2ec55b`, `4e1f59a`) and a
final hardening making the un-join lean on structure not coincidence (`937ede3`:
`join_view` requires the continuation λ's grade unrestricted). The review cron was
then cancelled and `autopilot/kernel-parity-batch` merged in (`33c41b9`), which
adopts Dialyzer as a gate; a latent dead `{:vstring_type}` classify clause it
surfaced was removed as an integration fix.

Post-merge gate (the current numbers; supersedes the pre-merge 3902/65/44):
**4025 tests / 0 failed**, Antigen **322/322 cells + 0 infections** (200-run
campaign), oracle replay **69/69**, `mix dialyzer` **green**, stdlib **48/48**.

Deferred, non-blocking, and OUT OF THIS PLAN (each needs its own spec if pursued):
(i) **surface grades on λ-expressions and constructor fields** — representable in
Core today, just unspellable; this is E/P-layer (parser + elaborator), NOT K-layer,
and landing it re-arms the `937ede3` landmine (the un-join's soundness currently
holds because `elaborate_lambda` hardcodes ω), so it must be co-designed with a
graded-λ usage rule. (ii) **`quantities` as a pure projection of the Pi** — the
slice-6 assertion already makes the two a verified mirror, so this is churn with no
behavioural change, not a soundness need.

**Branch:** `core-let-binder`
**Goal:** full Quantitative Type Theory (Atkey) with `{0, 1, affine, ω}` grades on
Core binders, so linear *and* affine types land on one mechanism.
**Authority:** Idris (`~/Develop/Idris2`), which abstracts its quantity behind
`Algebra.Semiring` + `Algebra.Preorder` and instantiates `ZeroOneOmega`. Cure
instantiates a four-element carrier. Pre-approved under the standing
TCB-alignment directive (`tcb-change-blanket-approval`).

---

## Settled decisions — do not relitigate

1. **Grade is the FIRST field.** `{:pi, g, dom, cod}`, `{:lam, g, dom, body}`,
   `{:let, g, ty, val, body}`. This is not a fresh choice: `validator.ex:125,128`
   already reserves exactly these shapes ("the future graded 4-tuple forms are
   matched so the walker survives the later grade reshape").

2. **ONE canonical spelling.** Never leave a 3-tuple and a 4-tuple form of the
   same binder coexisting. Two spellings of one binder diverge *below* the typing
   judgement — the recorded `ctor-spelling value dichotomy` bug class.

3. **Grades are opaque.** Nothing outside `Cure.Core.Grade` pattern-matches a
   grade. Go through `add/2`, `mul/2`, `admits?/2`, `leq/2`, `erased?/1`,
   `present?/1`, `restricted?/1`. This is what keeps the carrier extensible.

4. **`Conv` MUST compare grades.** Idris `Core/Normalise/Convert.idr:328`:
   `if sameBinders bx by && multiplicity bx == multiplicity by`. So
   `(1 x : A) -> B` is a *different type* from `(x : A) -> B`. Comparison is by
   **equality**, never by the preorder — `leq/2` belongs to the usage check, not
   to conversion.

5. **The usage check stays OUT of the kernel.** Idris keeps `LinearCheck.idr`
   outside `Core.Normalise`. Cure keeps it in the E layer (`relevance.ex`
   generalised). The kernel *carries and compares* grades; it does not *count*
   uses.

6. **`:let` gets a grade too**, uniformly with `:pi`/`:lam` (Idris `Binder.idr`
   grades `Lam`, `Pi`, `Let`, `PVar`, `PLet`). This retires the deliberate
   omission made when `:let` landed (`a84c454`).

7. **Default grade is `:unrestricted`.** Every existing 3-tuple site migrates to
   `:unrestricted`, which is behaviour-preserving.

8. **`:lam` IS graded, even though it doubles the migration.** Considered and
   REJECTED: grading only the types (`:pi`, `:vpi`, `:let`) and leaving `:lam` a
   3-tuple. That is 380 sites instead of 1029, and it looks sound at slice 2 —
   `Conv` only ever compares *types*, a λ's grade is redundant with its Π's, and
   `Kernel.infer` on a λ could default to `ω` (the elaborator can never infer a
   bare lambda anyway, so λs always arrive in checking mode).

   It breaks at **slice 4**, which is how a soundness hole ships. `relevance.ex`
   learns a binder's quantity from the **def's parameter vector**, so it only
   knows *top-level* params. An **inner** λ binding a linear variable —
   `fn(1 c: Chan) -> Effect(Unit)`, exactly a `spawn` body — would be invisible to
   the usage check, and its linear binder silently unchecked. Idris stores the
   multiplicity on `Lam` for precisely this: `LinearCheck.lcheck` reads
   `multiplicity b` off the binder (`Core/LinearCheck.idr`, `lcheckBinder`).

   Site split, measured post-merge: `:pi` 315, `:vpi` 18, `:let` 47 (= 380);
   `:lam` 634, `:vlam` 15 (= 649). Total 1029.

---

## Blast radius (measured 2026-07-10)

Re-measured after merging `feature/idris-parity` (2026-07-10, tree at 3795 tests
green):

| area | binder sites | nature |
|---|---|---|
| `lib/cure/core/` | 76 | **TCB. Reviewed diff.** |
| `lib/cure/elab/` | 92 | mechanical |
| `lib/antigen/` | 339 | mechanical (generators construct binder literals) |
| `test/` | 435 | mechanical |
| `types/`, `compiler/`, `mix/` | 13 | classic pathway; check whether it even sees Core binders |

**Hazard:** Elixir will not error on a stale 3-tuple `{:pi, a, b}` — it falls
through to a catch-all and behaves silently wrong. The nets are `Term.term?/1`
(reject 3-tuples once migrated), the `Validator`, and the 3694-test suite. Do not
rely on the compiler.

---

## Slices

Each slice is independently gated and independently committable. Never commit a
half-migrated tree.

- [x] **1. `Cure.Core.Grade`** — the semiring. `4050c81`.
      Laws checked exhaustively over the finite carrier (all 64 triples):
      additive commutative monoid, multiplicative monoid, `0` annihilates, both
      distributive laws, preorder reflexive/transitive with `ω` as top.
      Pinned asymmetries: `erased ⊀ linear` (a linear value must be used);
      `affine ⊀ linear` (an affine value may be dropped).

- [x] **2 + 3. Binder reshape + full migration (TCB).** LANDED.
      All Core binders are graded 4-/5-tuples; `Conv` compares grades by
      **equality**; `Kernel.check` rejects a λ whose grade differs from its Π's;
      `validator.ex`'s `grade_on_binders` rule flipped `:off` → `:reject`.
      1195 grades inserted across 150 files; 125 match sites converted.
      Antibody `kernel/grade_conv` (7 cells), mutation-validated both ways.

      **What the mechanical pass could NOT see, and what caught it:**
      * `wrap_binders(:pi, …)` / `wrap(:pi, …)` (elab) and
        `Generators.Serialization.binary(tag, …)` build the binder tuple from a
        **tag**. No textual pass sees those. `Term.term?/1` rejecting 3-tuples
        caught the first two at runtime; a generator round-trip test the third.
      * **`normalise.ex` was missed entirely.** `nf_struct({:vpi, dom, cl})` kept
        matching the ungraded shape, fell through a catch-all, and δ-normalisation
        silently stopped happening under a binder. Exactly one test caught it
        (`NfStuckCaseDeltaTest`). This is the fallthrough hazard, in the TCB.
        **Sweep every file in `lib/cure/core/` after any taxonomy change; do not
        trust a list of files you believe you edited.**
      * The blanket pass **corrupted tests that deliberately construct stale
        shapes** (`validator_test`, `grade_binder_test`). Those now build them with
        `:erlang.list_to_tuple/1` so no mechanical pass can "fix" them.

      **`lib/cure/types/` IS OFF-LIMITS.** It has its OWN, unrelated
      `{:pi, [{name, type, mode}], ret_ast}` — the *classic* pipeline's Pi, with
      `mode :: :explicit | :implicit | :erased`. The mechanical pass injected a
      Core grade into it, including into an `@type` spec. It compiled. Reverted.
      Two different `:pi` namespaces exist; only Core's is graded.

      **Metastatic is not a constraint.** Its MetaAST is `{type, keyword_meta,
      children}` and governs the *surface* AST (`Cure.Compiler.Parser`). Cure never
      calls Metastatic (`grep -rn "Metastatic\." lib/` → nothing). Core was never
      3-arity-uniform anyway: `{:var, k}` is 2-arity, `{:data, …}` and `{:case, …}`
      are 4-arity, `{:absurd}` is 1-arity.

      **Corpora needed migrating, idempotently.** `key=` (base64 s-expr) and
      `pieces=` (plaintext) in `corpus.sexp`/`seeds.sexp`/`coverage.sexp` plus
      `test/fixtures/core_conformance.txt` hold serialized binders. Scaffolds hold
      none (verified). `mix test` **banks seeds into the committed corpora**, so a
      run under the graded kernel leaves already-graded records behind and a blind
      regex double-inserts. The migration checks for an existing grade first, and
      asserts idempotence on re-application.

      *Gate:* 3813 passed / 0 failed. Antigen 314/314 cells, 400-run campaign → 0
      infections. Oracle replay 65/65. `mix dialyzer` passes.

- [x] **4a. Quantities are grades.** LANDED. Def/ctor `quantities` were the ad-hoc
      `:erased | :present` pair; `:present` (the ω one) is now `:unrestricted`, and
      `Inductive.quantity/0` IS `Grade.t/0`. 123 atoms renamed across 29 files.

      **The dangerous half was `Erase`.** It keeps an argument iff a runtime value
      exists for it, and asked `q == :present`. A blind rename turns that into
      `q == :unrestricted`, which **silently drops every `:linear` and `:affine`
      argument** from the emitted term. The predicate is `Grade.present?/1`
      (anything but `0`). Same trap in `Emit` (which params get real BEAM variable
      names vs `_e` placeholders) and three `Enum.count(.., & &1 == :present)`
      sites in the elaborator. Guarded by `test/cure/elab/quantity_grade_test.exs`,
      mutation-validated: the equality predicate fails 3 of 7.

      **Corpora again.** `:present` lives in `scaffold=` as a **binary string**
      leaf (35 records) and in `key=` as base64 text (369 records) — never in
      `pieces=`. The key rewrite MUST use a strict boundary regex: flags named
      `case_present` / `app_present` exist and a naive word swap corrupts them
      (271 preserved in `seeds.sexp`).

      *Gate:* 3820 passed / 0 failed. Antigen 314/314 cells, 300-run campaign → 0
      infections. Oracle replay 65/65. `mix dialyzer` passes.

- [x] **4b. Usage check (E layer).** LANDED. `relevance.ex` now runs the **two
      mechanisms Idris runs**, which the old plan text conflated into one:

      1. **Position check** — Idris `rigSafe` (`LinearCheck.idr:166-170`), at a
         `Local` occurrence. This is what Cure already had: an `:erased` binder may
         not appear in a relevant position. Kept, unchanged, errors and all.
      2. **Usage check** — Idris `checkUsageOK` (`:274-276`), at a `Bind`:
         `when (isLinear r && used /= 1) (throw …)`. Generalised over the carrier;
         this is where affinity enters.

      **Usage is carried as a grade**, not a count (`:erased` = 0 uses, `:linear` =
      1, `:unrestricted` = many), so composition IS the semiring: `add/2` in
      sequence, `mul/2` on entering a subterm. The rule is then `Grade.leq(used,
      declared)` — subusaging — which is *exhaustively equivalent* to
      `Grade.admits?(declared, n)` over all 16 pairs (pinned in `grade_test.exs`).
      This is what let the whole pass keep grades **opaque**: `relevance.ex`
      pattern-matches no grade.

      **The closure hazard falls out of `mul/2`, as predicted.** A λ's body scales
      its usage of *outer* binders by `ω`, because a closure may be entered any
      number of times. `fn(1 x) -> fn(_) -> x` is rejected with `used: ω`. Idris
      does the same via `eraseLinear env` (`:233-237`). Mutation-validated: delete
      the scale, exactly the two closure tests fail.

      **Branches combine by AGREEMENT, not summation.** A `case` yields a *set* of
      usages per binder, one per branch; every member must satisfy `leq`. A
      `:linear` binder used in one branch and dropped in another is rejected; an
      `:affine` one is accepted. Idris's `combineUsage` (`:528-540`) throws on any
      `Use0`/`Use1` mismatch **regardless of grade** — right for Idris, which has
      no affine, wrong here. Mutation-validated: sum the branches instead of
      collecting them and exactly the three agreement tests fail.

      **A latent slice-4a bug was found and fixed here.** 4a's rename turned
      `q == :present` into `q == :unrestricted` at the two argument-position gates
      in `relevance.ex` — the *precise* predicate 4a's own notes say silently drops
      `:linear` and `:affine`, corrected in `Erase` and `Emit` but missed here. It
      was dormant only because no restricted grade was reachable; **4b is what made
      it reachable.** Now `Grade.present?/1`. Mutation-validated: restore the
      equality and exactly the two new gate tests fail. *The lesson generalises:
      after a taxonomy rename, grep for the OLD predicate's shape, not the old
      atom.*

      *Division of labour:* counting runs for `:linear`/`:affine`. `:erased` stays
      with the position check, which reports the *site* and carries the
      collapsible-family exemption. `:unrestricted` imposes no obligation — so
      **every existing program is unaffected**, which is why the suite moved only
      by the 24 new tests.

      *Known conservatism (not a bug, recorded):* the ω-scale applies to every λ,
      including the one-shot λs the elaborator itself emits (join points,
      `bind_once_guard`). A linear variable used inside such a λ will be counted
      `ω`. Idris is conservative in the same place. Revisit only if slice 5's
      surface syntax makes it bite.

      *Gate:* 3852 passed / 0 failed. Antigen 314/314 cells, 300-run campaign → 0
      infections. Oracle replay 65/65. `mix dialyzer` passes.

- [x] **4c. Join points (E layer).** *(landed `87dcaeb`)* Bind a catch-all body **once** instead of
      re-elaborating it per uncovered constructor. Encoding uses only existing
      Core formers: wrap the `:case` in the `:let` binder slice 1 added, binding
      `j = {:lam, ω, S, e}` at type `{:pi, ω, S, R}` — literally the motive λ with
      `:lam` rewritten to `:pi` — and emit `{:app, j, scrut}` in each defaulted
      branch. The λ supplies the laziness a bare `:let` would destroy: the
      catch-all must not run when a real arm matches.
      *Scope:* only when the motive is **non-dependent** (its body has no free
      `{:var, 0}`) and **≥2** constructors are uncovered. A dependent motive would
      need the branch's reconstructed `C(args…)` — including its erased telescope
      args — rather than `scrut`, so it keeps today's expansion; one uncovered
      constructor makes a closure a pessimization.
      *Red tests to write first:* a 6-constructor type with one arm covered
      elaborates the catch-all body **once**, not 5×; two nested catch-alls give
      1 copy, not 25 (sharing composes — nesting adds a binding rather than
      multiplying copies); a named catch-all `x -> g(x)` still sees the scrutinee's
      value; each constructor still normalizes to the same result it does today
      (semantics preserved); one uncovered constructor emits **no** join point; a
      dependent-motive match is unchanged and still typechecks.
      *Not a blocker for 4b* — see "Known prerequisite" above.

- [x] **5a. Surface syntax — parameters.** LANDED. The grade **replaces the binder's
      colon** and sits at the binding site; absent means `ω`, so no existing source
      changes (stdlib: 44 passed, 0 failed).

      ```
      fn run({ n : Nat},  c : Chan(Cmd),  h : Handle, budget: Int) -> Unit
      ```

      **The numeral spelling this plan originally specified is impossible, measured.**
      `fn f(x: 1) -> Int` already parses, with `1` as a literal type, so `:1` collides
      with real syntax; `?` is already the **hole** token, so `1?` would overload
      Cure's hole taxonomy; and Idris has **no affine grade**, so "Idris parity" only
      ever justified `0`/`1` — the two that collide. `:erased`/`:linear`/`:affine`
      already lex as single `atom` tokens, are unambiguous after a binder name, and —
      being atoms, not keywords — steal no identifiers.

      **The grade decorates the ARROW, not the name and not the type.** Core spells it
      `{:pi, g, dom, cod}`; `Conv` compares `g` while `dom` is an ordinary type. So
      `linear c` (decorates the name) and `c: linear T` (would make `linear T` a type
      Cure has no former for) are both wrong. ` c : T` decorates the binding.
      `:unrestricted` is deliberately **not** a spelling — `ω` is written by omission,
      so each grade has exactly one surface form.

      *Also fixed:* `check_extern_arity/2` counted `q == :unrestricted` as "present" —
      slice 4a's rename trap for the third time, after `Erase`/`Emit` (4a) and
      `Relevance` (4b). An `@extern` on a def with a `:linear` parameter was rejected
      as an arity mismatch. Now `Grade.present?/1`.

      Four mutations validated, each failing exactly its own tests: admit
      `:unrestricted` as a spelling → the one-spelling test; make a graded binder's
      type optional → the type-required test; ignore `meta[:grade]` in the telescope →
      **4** tests (the compiles-and-lies guard); restore `== :unrestricted` in
      `check_extern_arity` → the extern test.

      *Gate:* 3872 passed / 0 failed. Antigen 314/314 cells, 300-run campaign → 0
      infections. Oracle replay 65/65. `mix dialyzer` passes. stdlib 44/44.

- [x] **5b. Surface syntax — `let`.** LANDED. `let  c = e` when `e` infers;
      `let  c : T = e` when it does not.

      Idris's `letBinder` is `multiplicity >> pat >> option (":" type) >> "=" >> val`
      (`Idris/Parser.idr:821-824`), so the type stays **optional even when graded** —
      the grade and the type are orthogonal, and `let_inferred/8` synthesises the type.

      **The one place a graded `let` must be ascribed, and its mechanical cause.** When
      the rhs has no inferable type (a bare lambda, an `if`, a `pickup`),
      `let_inferred/8` abandons the `:let` node and **surface-substitutes** the rhs into
      its single use site. On that path no `:let` node exists, so there is nowhere to
      record the grade and it would be silently dropped — the program would compile,
      pass, and lie about its linearity. So: a graded `let` MUST produce a real `:let`
      node; if the rhs infers that is automatic, otherwise
      `{:graded_let_needs_annotation, name, meta}`. Never substitute and discard.

      Graded destructuring (`let [h | _t] :linear = xs`) is a **parse error**: a
      destructuring `let` lowers to a `case`, whose binders take their grades from the
      constructor's field quantities, so there is no single Core binder to carry it.

      **A hole this slice opened, and closed.** Making `:erased` spellable on a `let`
      exposed the fact that `Relevance`'s POSITION check tracked only erased
      *parameters* and erased constructor *fields* — never `:let`/`:lam` binders. And
      `check_binder/5` defers `:erased` to that position check. So `:erased` was the one
      grade **no** mechanism policed on those binders: `let c :erased = e` and then
      returning `c` was accepted. `Emit` binds every `:let` unconditionally, so the
      value does exist at runtime — the lie was in the annotation, not in erasure. Fixed
      by `track_erased/3`: an erased `:let`/`:lam` binder joins the tracked set, exactly
      as an erased constructor field already does.

      Five mutations validated, each failing exactly its own claims: hardcode `ω` in
      `bind_once_let/10` → **7** tests (the compiles-and-lies guard); drop the
      graded-let substitution guard → the not-silently-substituted test; drop the
      graded-destructuring guard → its test; make the type non-optional after a grade →
      12 tests; drop `track_erased/3` → the 3 erased-binder tests.

      *Gate:* 3896 passed / 0 failed. Antigen 314/314 cells, 300-run campaign → 0
      infections. Oracle replay 65/65. `mix dialyzer` passes. stdlib 44/44.

- [x] **6. The Pi is the single source of truth (E layer, structural).** LANDED.
      The stored Pi and λ now carry the real per-parameter grade, and the two agree
      across `demote_unused_dicts/3`.

      **What was wrong, measured.** For `fn ignore({a}, x) -> a where Eqs(a)`, the def
      stored `quantities: [:erased, :unrestricted, :erased]` (implicit erased, dict
      demoted) while BOTH binders were all-`ω`. The parallel store was the truth; the
      binders lied. The `ctor-spelling value dichotomy` class, one level up.

      **Idris settles it** — the quantity lives on the Pi (`lcheck` App reads `rigf`
      off the callee's type, `LinearCheck.idr:283`) and `eraseArgs` is a derived
      projection (`findErasedFrom`, `TTImp/Elab/Utils.idr:39-49`); nothing lowers a
      quantity after the type is fixed.

      **The fix, three parts.** (i) `wrap_binders/4` threads the quantity vector onto
      each binder. (ii) `sig.pi` is built at signature time from the ORIGINAL
      quantities (honest for pre-registration and recursion); the final stored Pi is
      **rebuilt from the DEMOTED vector** so it agrees with the λ — otherwise the Pi
      (dict `ω`) and λ (dict `:erased`) disagree, which the graded `Conv` forbids.
      (iii) the assertion that would have caught the whole class: `Kernel.check` the
      final λ against the final Π before `Env.add_def`. Mutation-validated — rebuild
      the Pi from the ORIGINAL vector instead of the demoted one and the assertion
      fires with exactly `{:grade_mismatch, %{pi: :unrestricted, lam: :erased}}`.

      The extern path is coherent by construction (Pi from `sig.quantities`, no body to
      demote). A graded function's TYPE now advertises its grade, so `Conv`
      distinguishes `( c : T) -> R` from `(c: T) -> R` and linearity survives
      passing `f` itself as a value.

      *Deferred, deliberately:* making `quantities` a *pure projection* of the Pi (a
      representation refactor touching every `.quantities` reader). The assertion
      already makes the two stores a **verified mirror** — they cannot diverge at any
      def boundary without `Kernel.check` firing — so removing the field is churn with
      no behavioural change, not a soundness need.

      *Gate:* 3902 passed / 0 failed. Antigen 322/322 cells, 300-run campaign → 0
      infections. Oracle replay 65/65. `mix dialyzer` passes. stdlib 44/44.
---

## Known prerequisite, already met

`let` no longer duplicates or discards its rhs (`9e7eeb2`): surface substitution
runs only at exactly one use, and `let x : T = e` binds a check-only rhs once.
Without that, a linear handle could be cloned *below* the usage check — the
elaborator would manufacture the aliasing the type system forbids. Slice 4 may
therefore proceed with no substitution-path escape clause.

The remaining sibling defect is the **join-point residual**. An earlier draft of
this plan described it as "`elaborate_match` copies a continuation into every
branch" and concluded that **slice 4 must either fix join points or reject linear
values in a duplicated continuation**. Both halves of that sentence were wrong.
The corrected, measured account:

**Where the duplication actually is.** Core `:case` has no default branch, so a
surface catch-all (`_ -> e` / `x -> e`) is expanded into one Core branch per
*uncovered constructor*, and `elaborate_default_branch/10` surface-substitutes
the catch-all's variable and **re-elaborates `e` from scratch each time**. Guards
are not the cause: `guard_chain/7` is already linear (its fall-through `ff` is
elaborated once), and `split_first_tuple_column/2` refuses to duplicate a row
(it bails to `:not_applicable` unless the first-column heads are distinct).
`fold_ctor_guard_groups/2` splices the closer per guarded group, but that is
subsumed by the catch-all expansion.

Measured on `elaborate/1`, counting occurrences of the catch-all body's callee in
the elaborated Core:

| shape | copies |
|---|---|
| 3-constructor type, 1 arm covered | 2 |
| 6-constructor type, 1 arm covered | 5 |
| two *nested* catch-alls, 6-constructor type | **25** |

So *k* nested catch-alls over an *n*-constructor type yield **(n−1)^k** copies —
exponential term growth, paid in flash on an ESP32.

**It is not a soundness problem.** Idris combines branch usages by *agreement*,
not summation (`LinearCheck.idr:528-540`, `combineUsage`): a `Use0`/`Use1`
mismatch across branches is an error, and `UseAny` wins over anything. Every copy
the expansion makes lands in a **disjoint constructor branch**, never
sequentially within one branch, so a linear variable in the copied body is still
counted **once**. Duplication cannot inflate `1` to `ω`. Slice 4b is therefore
safe with or without join points, and needs no escape clause.

Cure's `combine` must nevertheless be **grade-aware**, where Idris's is not.
Idris throws on a `Use0`/`Use1` mismatch regardless of the binder's grade because
Idris has no affine quantity. For Cure, a `:affine` binder used in one branch and
dropped in another is **legal** — affine may be dropped. The rule is
`Grade.admits?(declared, uses_in_branch)` checked **per branch**, not on a summed
count.

Join points are therefore a **term-size fix, not a soundness fix** — tracked
below as slice 4c on the operator's direction.

---

## Discipline (from `cure-porting`)

- Red-green: a named failing test before every fix. **A test that passes with and
  without the change is vacuous** — delete it and drop the claim. (This already
  bit us once: the `Certificate` "blind spot" tests were vacuous and the claimed
  soundness hole did not exist.)
- TCB changes: red→green, new Antigen antibody **mutation-validated** (break it,
  prove it fires, restore), full Antigen campaign, full `mix test`.
- Ghost commits, explicit pathspec staging. Revert `test/antigen/seeds.sexp`
  noise before committing — `mix antigen` banks seeds into a committed corpus,
  including from runs where the kernel was deliberately broken.
- One `mix` at a time.
- `Antigen.Runner.@group_table` is indexed by generator POSITION. **Append** new
  generators; a mid-list insert silently renumbers the rest and adaptive
  reweighting bumps the wrong ones.
