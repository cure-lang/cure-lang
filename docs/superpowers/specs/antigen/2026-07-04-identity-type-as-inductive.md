# Retire the primitive identity type: `Eq`/`refl`/`rewrite` become an inductive + sugar

**Status:** design (pre-plan). TCB-central. Author-driven from the standing
"align with the real languages" directive + operator steer ("these builtins were
added when we were faking dependent types; they need to get rewritten").

## Problem

Cure's propositional equality is faked at the kernel level. Three bespoke Core
term forms encode it as primitives:

- **Type former** `{:eq, ty, a, b}` — the type `a = b : ty`.
- **Constructor** `{:refl, a}` — the proof `refl a : a = a` (value form `{:veq, ...}`).
- **Eliminator** `{:rewrite, proof, motive, body}` — transport.

These are threaded through ~33 sites in seven `lib/cure/core/*` files
(`term.ex`, `kernel.ex`, `eval.ex`, `quote.ex`, `certificate.ex`, `serialize.ex`,
`inductive.ex`) and eight `lib/cure/elab/*` files. Surface `Eq(ty,a,b)`
elaborates to `{:eq}` (`declarations.ex:813`); surface `refl(x)` to `{:refl}`
(`elaborator.ex:254` infer / `:736` check); `rewrite … in …` to `{:rewrite}` via
`rewrite_plan/6` (`elaborator.ex:1000‑1123`).

The observable symptom (oracle cluster `refl`, authored 2026‑07‑04): `refl`‑matching
does not work. `sym`/`trans`/`cong` written the canonical way — `sym Refl = Refl`
— are `cure=reject / idris=accept` (`rf03`/`rf04`/`rf05`), because `{:refl}` is a
kernel primitive, not a constructor the pattern matcher recognises. The *only*
eliminator Cure exposes is `rewrite`, the derived one. This inverts how every
real system is built.

## How the real systems treat the identity type (verified against vendored source)

None of them has a kernel‑primitive equality term. In all of them equality is an
**ordinary inductive** whose constructor `refl`/`Refl` is directly matchable, and
`rewrite`/`rw` is **sugar/tactic layered on top**:

- **Agda** — `_≡_` is `data … where refl : x ≡ x`. Matching `refl` is ordinary
  dependent pattern matching → drives the LHS index unifier
  (`Rules/LHS/Unify.hs`, the file we ported the Cycle rule from). The `rewrite`
  **keyword desugars to a `with`‑abstraction that matches the proof against
  `refl`**. `{-# BUILTIN EQUALITY #-}` only names which inductive the sugar uses.
- **Lean 4** — `inductive Eq {α} (a : α) : α → Prop`; the eliminator `Eq.rec`
  (J) is auto‑generated like any recursor. `rw`/`simp` are tactics emitting
  `Eq.rec`/`Eq.mpr`. Kernel special‑casing is only two *optional* accelerations
  (`inductive.cpp`, `type_checker.cpp`): **K‑like reduction** (`m_K_target`,
  single‑ctor/no‑field ⇒ recursor reduces on a stuck major premise ⇒ K/UIP) and
  **Prop proof‑irrelevance** (`is_def_eq_proof_irrel`).
- **Idris 2** — `Equal`/`Refl` is a builtin `data` looked up by name
  (`ProcessDef.idr:522,578`); `IRewrite` (`WithClause.idr`) elaborates through it,
  tied to `with`‑clause desugaring.

**Unanimous verdict:** equality is a *derived* inductive; matching its constructor
drives the standard unifier (Agda/Idris) or recursor (Lean/Coq); `rewrite` is
sugar. Cure's primitives are exactly backwards.

## Design decisions (locked)

1. **`Eq` becomes a genuine homogeneous inductive family**, seeded into every
   `env0` exactly as `Bool`/`Nat` already are (`core/builtins.ex`
   `family` + `ctor` + `register_builtin` + schema):

   ```
   Eq  : (a : Type) -> a -> a -> Type        # 1 parameter, 2 indices
   refl : {w : a} -> Eq(a, w, w)             # single constructor
   ```

   Homogeneous (single carrier `a`) matches Agda/Lean/Coq *and* Cure's current
   single‑`ty` shape. **Rejected:** Idris's heterogeneous `a -> b -> Type` — more
   surface, no benefit for Cure. The constructor shape mirrors exactly the
   user‑level `type MyEq(a) indices (x,y)  mrefl : MyEq(a,w,w)` that **already
   works today** (`dotpat/dp01` `congS`, accept/accept) — proving the target
   machinery is sound and present.

2. **`refl`‑matching is ordinary dependent pattern matching.** No new eliminator:
   matching `p : Eq(a,x,y)` against `refl` goes through the existing
   `elaborate_match` → kernel `:case` → index unifier (now Cycle‑rule‑hardened).
   This yields `sym`/`trans`/`cong`/absurd‑discharge uniformly, for free.

3. **`rewrite` is demoted from primitive to surface sugar.** The `rewrite … in …`
   keyword stays (all three real systems keep the ergonomic construct); it
   elaborates to a **single‑branch dependent `match` on the proof against `refl`**
   carrying the motive `rewrite_plan/6` already computes — i.e. Agda's
   `rewrite p ⟿ with p | refl`. The kernel `{:rewrite}` node is **retired**.
   `rewrite_plan/6`'s motive/occurrence‑abstraction logic is *reused verbatim*;
   only its output node changes (`{:rewrite}` → `{:case}`).

4. **Eliminator = pattern‑matching, not a generated recursor.** Cure has no
   auto‑recursor generation but *does* lower dependent matching to kernel `:case`.
   Use that (Agda/Idris path). **Rejected:** synthesising an `Eq.rec` (Lean/Coq) —
   large new TCB surface for no gain, since `:case` already does the job.

5. **K / UIP is adopted; `--without-K` is rejected.** This is the one place the
   real systems disagree (Lean/Idris/Coq take K; Agda defaults to without‑K for
   HoTT compatibility). Cure targets practical verified systems programming on
   AtomVM with no univalence/cubical/HIT roadmap, so without‑K would only add
   proof‑obligation friction for compatibility Cure will never use — the
   "aligning buys nothing" case. Cure's existing **deletion rule** (Antigen
   vertical, ledger #23) is already K‑flavoured; K is the status‑quo‑preserving
   choice. We do **not** add Lean's Prop‑proof‑irrelevance or K‑like‑reduction
   accelerations in this change (Cure has no Prop universe); `Eq` is a
   `Type`‑valued family like `MyEq`, and definitional behaviour is whatever
   ordinary `:case` on a single‑ctor family already gives.

## Non‑goals

- No Prop universe, no proof irrelevance, no K‑like stuck‑premise reduction
  (those are Lean accelerations, out of scope).
- No heterogeneous equality, no cubical/observational equality.
- No change to `rewrite`'s *surface syntax* or its motive‑inference behaviour
  (row 7 parity — `rw01`‑`rw09`, `frp08` — must stay green).
- No auto‑generated recursors for other inductives.

## Implementation findings (2026‑07‑04, discovered during execution)

Three facts surfaced once seeding began; they revise the phasing below.

1. **Phases A and B are coupled — the `Eq` type former and `rewrite` must move
   together.** The kernel `{:rewrite}` node types its proof with `ensure_eq`,
   which demands a `{:veq}` *value* (`kernel.ex:118`). The instant surface `Eq`
   elaborates to `{:data, :Eq, …}`, every `rewrite p in …` proof is a data value
   `ensure_eq` rejects. So retargeting the `Eq` *type former* (Phase A) forces
   `rewrite`→`:case` (Phase B) in the **same** coordinated change. The spec's
   original "Gate A leaves the rewrite cluster on the primitive `{:rewrite}`" is
   not achievable; A and B merge into one kernel step (primitives kept as dead
   code until C).

2. **`refl`'s witness is erased, mirroring `mrefl` exactly; the surface keeps the
   explicit `refl(x)` construction.** ~20 green, immutable probes
   (`rewrite/*`, `frp/*`, `match/mt02,mt03`, `refl/rf01,rf02`) *construct*
   `refl(x)` with an explicit witness but *pattern‑match* `refl()` nullary. So
   the ctor is `refl : {w:a} → Eq(a,w,w)` with `w` **erased** (quantity 0) — a
   byte‑for‑byte mirror of `mrefl`, which makes the nullary `refl()` pattern and
   its index refinement work for free (identical to `dp01`). The surface
   construction special‑case (`elaborator.ex:254/736`) is retained but now builds
   the inductive ctor `{:ctor, :refl, [x]}` (witness supplied explicitly, erased
   at runtime) instead of the primitive `{:refl, x}`.

3. **Stdlib fakery to retire (operator‑requested 2026‑07‑04).** `Std.Equal`
   (`lib/std/equal.cure`) defines `refl/sym/trans/cong` that all return the atom
   `:cure_refl` with an `Atom` return type — faking‑era placeholder tokens, not
   proofs. `Std.Proof` (`lib/std/proof.cure`) declares law‑shaped stubs
   (`plus_zero`, `zero_plus`, `plus_comm : Eq(Int,a,a)`, `append_nil`, `map_id`)
   that all return `:cure_refl`. With genuine inductive `Eq`/`refl`, these become
   real proofs where structurally provable (reflexivity‑at‑reducing‑type like
   `rf01`; `sym`/`trans`/`cong` like `rf03`‑`rf05`) and are removed where they
   were unsound stubs (a `plus_comm` over the non‑inductive `Int` erasure target
   cannot be proven by induction — retire rather than fake). Mirror any change in
   `priv/std/` copies. This is a new phase **B′** (stdlib), gated after the
   kernel retarget lands and before/with Phase C.

## Approach — phased, TCB‑gated (mirrors the Bool retirement #39‑43/#74)

### Phase A — additive: seed inductive `Eq`, route surface onto it (TCB)
- `core/builtins.ex`: add `eq_family`/`eq_ctors` (param `a:Type`, indices `x,y:a`,
  ctor `refl` with implicit `w` and result indices `(w,w)`), a `:eq` schema entry,
  and `maybe_seed(:eq, …)` in `seed/2` (respecting the local‑declaration exclude
  rule). Mirror the `MyEq` lowering for the constructor's index telescope.
- `declarations.ex:813`: `Eq(ty,a,b)` → `{:data, :Eq, [ty], [a, b]}` instead of
  `{:eq, ty, a, b}`.
- `elaborator.ex:254,736`: `refl(x)` → an application of constructor `refl`
  (`{:ctor, :refl, …}` via the normal ctor path) instead of `{:refl, x}`.
- **Red first:** oracle `refl/rf03,rf04,rf05` (reject→accept) and a kernel test
  that `match p { refl() -> … }` typechecks and refines indices. Keep `{:eq}`/
  `{:refl}` kernel clauses *in place* this phase (dead‑but‑present) so nothing
  else breaks yet.
- **Gate A:** full suite green; `rf01`/`rf02` unchanged; row‑7 rewrite cluster
  unchanged (still on the primitive `{:rewrite}` at this phase).

### Phase B — rewrite as sugar; retire `{:rewrite}` (TCB)
- `rewrite_plan/6`: emit a single‑branch `:case` on the proof (motive reused)
  instead of `{:rewrite, …}`.
- Remove `{:rewrite}` from `term.ex`, `eval.ex`, `kernel.ex` (infer :116),
  `quote.ex`, `certificate.ex`, `serialize.ex`, and the elab helper clauses
  (`kernel.ex:1013`, `subst.ex`, `erase.ex`, `relevance.ex`, `resolution.ex`,
  `unify.ex`).
- **Red first:** oracle `rewrite/rw01…rw09` + `frp08` must remain accept/reject
  exactly as before (behavioural pin — the desugaring is observationally
  identical). A kernel test that a retired‑node term no longer round‑trips.
- **Gate B:** full suite; row‑7 cluster byte‑for‑byte verdicts preserved.

### Phase C — retire `{:eq}`/`{:refl}`/`{:veq}` primitives (TCB, subtractive)
- Remove the type former `{:eq}` (kernel :100, :670 type‑formation), constructor
  `{:refl}` (kernel :109 infer, :264 check), value `{:veq}` (eval/quote), and all
  `replace_branch_vars`/`subst`/`shift`/`erase`/`has_hole?` clauses for them.
  After Phases A/B every surface path builds the inductive, so these are dead.
- **Gate C (full TCB gate):** new Antigen antibody — *Eq‑as‑inductive soundness*:
  (i) `refl`‑matching discharges/refines exactly as the index unifier dictates and
  equates **no** distinct normal forms (the change must not collapse defeq);
  (ii) termination unaffected; (iii) the retired nodes are truly unreachable. Then
  full Antigen, full suite, oracle replay, and the `refl` + `rewrite` + `cycle`
  clusters all green. Adversarial‑verify the antibody.

## Verification

- **Oracle (differential):** `refl/rf03,rf04,rf05` reject→accept; `rf01`/`rf02`
  unchanged; **no regression** in `rewrite/*`, `frp/*`, `cycle/*`, `dotpat/*`,
  `withmulti/*`. Replay green before each commit.
- **Kernel unit tests:** `Eq` type‑formation via the family path; `refl` ctor
  typing; `match refl` index refinement; rewrite‑desugars‑to‑case equivalence.
- **Antigen:** the new Eq‑inductive antibody + the full suite (≥450) green.
- **Full suite:** 2996+/0, run once, alone, at each gate.

## Risks

- **Defeq drift (soundness).** The primitive `{:rewrite}` and inductive `:case`
  transport must be observationally identical. Mitigation: Phase‑B behavioural pin
  on the entire row‑7 cluster + the Gate‑C antibody's "equates no distinct normal
  forms" obligation. This is the load‑bearing check.
- **Constructor index telescope for `refl`.** Getting the `refl : Eq(a,w,w)`
  implicit‑`w`/result‑index shape wrong yields a family that either won't match or
  over‑unifies. Mitigation: mirror the *already‑green* `MyEq`/`mrefl` lowering
  byte‑for‑byte; `dp01` is the reference.
- **Erasure/codegen.** `erase.ex` maps `{:refl}`→`{:ctor,:cure_refl,[]}` and
  `{:eq}`→`{:ctor,:cure_eq,[]}` today (equality is runtime‑irrelevant). The
  inductive `Eq`/`refl` must erase to the same runtime‑nothing. Mitigation: keep
  the erasure target identical; add an erase clause for the `:refl` ctor.
- **Scope.** ~33 kernel sites. Mitigation: the three‑phase additive→subtractive
  order keeps the suite green throughout; no phase both adds and removes a form.

## Open question for the operator — RESOLVED

Decision 5 (adopt K, reject `--without-K`) is the only genuinely
soundness‑flavoured fork. Recorded here with justification; flagged for explicit
sign‑off before Phase C, since it is the one choice a future HoTT‑direction could
regret. Everything else follows from "align with the real systems + reuse Cure's
existing inductive machinery."

**Operator sign‑off obtained 2026‑07‑04: "Yes, with K/UIP."** After reviewing
the with/without‑K contrast (distinct‑endpoint `sym`/`trans`/`cong` identical
either way; only reflexive‑endpoint matches like `kAxiom`/`uip` differ — accepted
under K, requiring an explicit `J`‑motive detour without it), the operator
adopted K/UIP. Phase C is unblocked. This is consistent with the already‑K
behaviour of user‑level inductives (`MyEq`/`mrefl`, `dp01`) and Cure's existing
deletion rule (ledger #23); seeding builtin `Eq` extends, not introduces, the
K stance.

## Current state — REVISED 2026‑07‑08 (evening): the K6 gate is STALE; Phase B/C authorized and re‑scoped

Operator approval obtained 2026‑07‑08: *"I approve the identity-type kernel
surgery rewrite."* A fresh evidence probe (kernel-parity-batch branch) then
found the section below OUTDATED in its central claim. Revised ground truth:

1. **The K6‑blocks‑refl‑inference concern is DODGED AND LANDED.** The kernel
   now infers a **params‑on‑spine saturated ctor** (commit `b355753` — K6
   task 1 — `kernel.ex:200‑216`: when `length(args) == param_count +
   field_count`, it re‑checks `params ++ fields` against the concatenated
   telescopes and NbE‑derives the result indices — no metavariables, no grade
   tracking, a small strictly‑sound kernel addition, NOT the deferred K6 grade
   machinery). Commit `f3b0e73` — K6 task 2 — is the elaborator‑side consumer:
   it retargets `bridge_step` to build its inference‑position proof through
   this new capability instead of the primitive `{:refl}`.
   `mk_refl_infer(ty,x) = {:ctor, :reflexive, [ty, x]}` (`elaborator.ex:1051`)
   is inferable: probe evidence
   `infer {:ctor,:reflexive,[Nat,Z]} => {:ok, {:vdata,:Equivalent,[Nat,Z,Z]}}`
   (bare form still correctly rejects with `:ctor_requires_checking_mode`,
   which is a KERNEL atom — `kernel.ex:222` — not an elaborator one as the
   stale section below claimed). `bridge_step` already uses the inductive
   spine form; additionally it is currently DORMANT in the whole corpus
   (normalizer improvements route rw07 through the `contains_a` syntactic
   path — traced with `CURE_REWRITE_LOG=1`, no test reaches `bridge_step`).
2. **Primitive `{:eq}`/`{:refl}` have NO producers left.** All surface paths
   build `{:data, :Equivalent, …}` / `{:ctor, :reflexive, …}`; the remaining
   `{:eq,}`/`{:refl,}` matches in `lib/cure/elab/*` are structural traversal
   clauses only. `no_eq_node` is `:warn` in the default validator config and
   `:reject` in `release_config` (`validator.ex:45,81`).
3. **The REAL remaining blocker for Phase B is the computed‑endpoints
   desugaring problem, not refl inference.** The first Phase‑B attempt
   (`d44edb8`, `rw_case_build`) was REVERTED in `c635e8c` with the diagnosis:
   shifting an already‑elaborated body +1 into the refl branch type‑checks
   only for VARIABLE endpoints (where `unify_indices` substitutes the branch
   witness); for COMPUTED endpoints it drifts verdicts (empirically:
   `frp01_par_assoc` accept→reject). **The correct Phase B re‑elaborates the
   body INSIDE the refl branch** — routing through `elaborate_match`'s branch
   machinery, whose `build_motive` sentinels handle computed indices — rather
   than shifting a pre‑built body. That revert message is the roadmap.

**Re‑scoped remaining work (this batch, operator‑approved):**

- **Phase B (the surgery's heart):** `rewrite p in body` → single‑branch
  inductive `:case` via in‑branch re‑elaboration (route through
  `elaborate_match`/`build_motive`), replacing every `{:rewrite, …}` producer —
  **seven** literal‑construction sites, not six (the previous count missed the
  `bridge_step` outer wrap): `elaborator.ex:1083` (`rewrite_plan`'s
  `contains_a`/symmetry branch), `:1095` (`contains_b` branch), `:1162`
  (`bridge_step`'s inner bridge proof), `:1166` (`bridge_step`'s outer wrap —
  previously omitted), `:1195` (`symmetry_proof`), `:1856`
  (`elaborate_with_eq_branch`'s sibling transport), and `:3421`
  (`elaborate_carried_eq_branch`'s sibling transport). Behavioural pin:
  oracle `rewrite/rw01‑rw09`, `refl/rf01‑rf05`, and the **frp cluster with
  computed endpoints (`frp01_par_assoc` is the sentinel that killed the naive
  attempt)** must keep byte‑identical verdicts. Because two of the seven
  producer sites (`:1856`, `:3421`) are the `with`‑clause sibling‑transport
  machinery, not the `rewrite` keyword, the pin must also cover `with/*`
  (`wi05_sibling_refine` exercises exactly this transport) and `withmulti/*` —
  a regression there would be invisible to the `rewrite`/`refl`/`frp`
  clusters alone.
- **Phase C (subtractive):** with producers gone, strip the dead
  `{:rewrite}`/`{:eq}`/`{:refl}`/`{:veq}` clauses across
  `term.ex`/`eval.ex`/`kernel.ex`/`quote.ex`/`certificate.ex`/`serialize.ex`
  and elab traversal helpers; flip `no_rewrite_node` (and default
  `no_eq_node`) to `:reject`. Full TCB gate: the existing
  `test/antigen/eq_inductive_antibody_test.exs` extended per Gate C
  (equates‑no‑distinct‑normal‑forms obligation), full Antigen, full suite,
  oracle replay.
- **Phase B′ (stdlib fakery retirement) — ALREADY LANDED, not remaining
  work.** Finding 3 above is stale: `48c68ab` (2026‑07‑04, before this batch)
  rewrote `Std.Equal`/`Std.Proof`'s `:cure_refl` stubs into genuine inductive
  proofs — `sym`/`trans`/`cong` now match `reflexive` for real (no runtime
  token), and `Std.Proof` proves `plus_zero_right`/`plus_succ_right`/
  `plus_comm` by induction on `Nat`, closing with `reflexive`/`rewrite`;
  `plus_comm`'s old non‑inductive‑`Int` stub and the unprovable
  `append_nil`/`map_id` stubs were dropped rather than faked. `ae02ba5` and
  `b199a2a` (2026‑07‑08, earlier the same day — already on this branch, just
  before this doc revision) renamed the module to
  `Std.Equivalent`/`reflexive`. Both `lib/std/` and `priv/std/` carry the
  current versions (`equivalent.cure`, `proof.cure`) — verified in this
  review to contain no `:cure_refl` occurrences outside a doc‑comment
  contrasting the old behaviour. Residual fakery (`:cure_refl`) survives only
  in `examples/proof_laws.cure` and `vicure/test_syntax.cure`, which are demo/
  fixture files outside finding 3's stated scope (`lib/std/equal.cure`,
  `lib/std/proof.cure`) — not a Phase B′ blocker, and out of scope for this
  batch unless the operator wants them swept too.

The section below is retained verbatim as the historical record of the
(now‑stale) 2026‑07‑08 morning assessment.

## HISTORICAL (superseded): Current state & the K6 coupling that blocks Phase B/C (2026‑07‑08)

**Phase A is LANDED and green.** Surface `Eq(ty,a,b)` elaborates to
`{:data, :Eq, [ty], [a,b]}` (`declarations.ex:813`), `refl(x)` to
`{:ctor, :refl, [x]}` (`elaborator.ex:254,747`), the inductive `Eq` family is
seeded (`builtins.ex:110‑115`), and the kernel bridges both representations via
`ensure_eq`/`eq_parts` (accept `{:veq}` *and* `{:vdata,:Eq}`). The **observable
symptom is fixed**: `refl/rf03,rf04,rf05` (`sym`/`trans`/`cong`) are now
`cure=accept / idris=accept / same`, `rf01`/`rf02` unchanged. This is the
soundness‑relevant part — refl is now a matchable constructor driving the
index unifier.

**Phase B/C (retire primitive `{:eq}`/`{:refl}`/`{:veq}`/`{:rewrite}`) is
DEFERRED — it is faithfulness, not soundness, AND it is blocked by K6.**

1. *Not a soundness fix.* The kernel types the `{:rewrite}` transport correctly
   (`kernel.ex:116`: `proof:Eq(ty,a,b)`, motive `λx.M[x]`, checks `body:M[a]`,
   yields `M[b]`) — it is a sound internal transport mechanism, bridged to the
   inductive representation. Retiring it in favour of a single‑branch `:case`
   (Agda's `rewrite p ⟿ with p | refl`) is *faithfulness* (matching how the real
   systems layer transport), buying no soundness. The `:case` translation is
   constructible in principle — case‑motive `λ x y p. expected[b:=y]` over the two
   `Eq` indices + scrutinee (`apply_motive(motive, indices ++ [scrut])`), refl
   branch refines `a≡b` — but see (2).

2. *Blocked by K6.* `bridge_step` (the rw07 reducible‑inner‑occurrence path,
   green) constructs `bridge_proof = {:rewrite, {:refl, s_nf}, const_motive,
   mk_refl(s_nf)}` (`elaborator.ex:1127`) using the **primitive** `{:refl}` in
   *proof (inference) position* — precisely because "a bare inductive refl ctor
   has no inference rule (`:ctor_requires_checking_mode`)" (its own comment,
   :1119‑1122). That is the **K6 param‑constructor‑inference limitation**, whose
   fix (params riding the ctor spine at grade 0) is grade‑coupled and deferred.
   Until K6 lands, the inductive `refl` cannot be inferred in proof position, so
   `{:rewrite}`/`{:refl}` cannot be fully retired. A *partial* migration (main
   `rewrite_plan` paths → `:case`, bridge left on the primitive) buys no soundness,
   cannot reach Phase C, and leaves TWO transport mechanisms — a net complexity
   increase. Declined per the analysis discipline.

**Conclusion:** the Eq cluster's soundness‑relevant content (Phase A) is done;
the primitive retirement (Phase B/C, `no_eq_node` clause) is a faithfulness
migration **gated on K6** (hence on the grade machinery). It joins K6/K12‑Sym/K7
as the deferred grade+representation modernization — surfaced to the operator as
the campaign‑state finding. `no_eq_node` stays `:off`.

## Phase-B encoding amendment (2026-07-08, post-B1 empirical STOP)

The "re-elaborate the body inside the refl branch" prescription (from
`c635e8c`'s diagnosis) is UNIMPLEMENTABLE for propositional rewrites, proven
empirically during B1: `Equivalent`'s single ctor binds both index positions
to one witness, so `build_motive` abstracts BOTH endpoints and the refl-branch
goal demands `a ≡ b` definitionally in-branch — false precisely when a rewrite
is needed (`plus_zero_right`: goal became `Equivalent(Nat, S(plus(n,Z)), S(n))`,
a conversion failure; the endpoint is stuck-computed, so the index equation
degrades to `:undecided` and no substitution occurs).

**Adopted encoding — the standard J/subst transport** (canonical in
Agda/Lean, where `subst`/`Eq.mpr` derive exactly this way from J):

```
transport = {:case, proof, λ(x y p). (motive@x) -> (motive@y), [reflexive(w) -> λh. h]}
result    = {:app, transport, body}     # body elaborated OUTSIDE at motive@A, unchanged
```

Verdict-preserving by construction (the body is still checked at the identical
`body_expected = motive@A`; only the eliminator node changes), no de Bruijn
body-shift, dodges the indexed-motive reify gap (motive result only ever
`Eval.apply`-ed). This is a faithful instantiation of locked Decision 3
("single-branch dependent match on the proof carrying the motive
`rewrite_plan` computes") — the branch body is the identity, and the motive is
the arrow form. All seven producer sites reduce to one identity-transport
helper.
