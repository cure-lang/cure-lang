# Kernel Specs — Condensed Master (2026-07-21)

**Scope.** This document condenses all 26 design specs in
`docs/superpowers/specs/kernel/` into one master reference covering the Cure
dependent kernel: the Final Core grammar and cleanup campaign, the
builtin-inductive foundation and primitive retirements (Bool/Nat/Sigma/Eq/prim
ops/Int), dependent-case index unification, WHNF-before-unification, size-change
and mutual-recursion termination certification, the refinement arc (SMT removal
→ decidable-boolean reflection → proof search → verified LIA reflection →
first-class holes), the trust-ledger axiom-closure enforcement, the core-walker
drift audit, the open elaborator-gap ledger, and the long-range evidential
systems architecture doctrine. It preserves locked decisions, invariants,
TCB-boundary statements, and status markers with full fidelity; it replaces
reading the individual specs, which remain untouched as historical record.

Layers: **K** = trusted kernel (`lib/cure/core/*`, the TCB), **E** =
untrusted elaborator (`lib/cure/elab/*`; kernel re-checks its output), **P**
= parser, **C** = codegen/erase/emit (untrusted, post-kernel), **A** =
Antigen. Non-negotiable steer: dependent machinery lives in
`lib/cure/elab/*` + `lib/cure/core/*`; `lib/cure/compiler/*` and
`lib/cure/types/*` are non-dependent decoys. **Elaborator hard-stop
principle:** before accepting any TCB change for a conversion/elaboration
failure, prove NO untrusted term works; TCB changes are pre-approved only
iff aligned with Idris, Agda, or Lean (Idris alone suffices), and always run
the full gate.

---

## 1. Cleanup campaign strategy & Final Core grammar

### 1.1 Strategy (approved, 7 locked decisions — dependent-kernel-cleanup-strategy)

1. Antigen safety net = known-label self-checks; sole legacy coupling is
   the normalizer/differential assay (K10).
2. Only the compiler gate is meaningful for the campaign.
3. **One uniformly strict kernel** — unsound machinery DELETED, not
   mode-gated. `Any` killed as universal subtype / implicit fallback;
   survives only as an explicit opaque dynamic type eliminable solely by a
   checked coercion at a declared FFI boundary.
4. Wave 0 = the entire Final-Core grammar up front; validator clauses
   hard-enable per wave (`:off` → `:warn` → `:reject` ratchet).
5. Final Core is **Idris/Agda-shaped, NOT Lean-shaped**: QTT
   multiplicities; predicative cumulative universes; irrelevance via
   quantity 0; no impredicative Prop. QTT→Lean projection is
   forgetful/mechanical; the reverse undecidable.
6. lean4lean is kept as a **second checking backend** via forgetful
   projection: it witnesses the dependent skeleton ONLY, never the
   quantitative layer (the kernel's sole permanent responsibility); pure
   yes/no gate.
7. Lean-compiler C-extraction = possible future host/native target,
   distinct from ESP32 (embedded stays BEAM/AtomVM); deferred.

### 1.2 Final Core grammar (final-core-grammar; Wave-0 deliverable)

17 nodes kept/reshaped; 5 deleted (`:eq`, `:refl`, `:rewrite`, `:prim`,
`:absurd`); `:hole` excluded from certified Core (see §6.6); no new nodes.
(`:let` later added as the 7th compound former by the core-let work; grades
ride binders.)

- **Grades (§B):** `%Cure.Core.Grade{usage, security}` on pi/lam/sigma binders.
  Usage semiring `{0, ≤1, 1, ω}` behind a module interface; only `{0, ω}`
  enforced initially. Security = opt-in module-declared IFC join-semilattice,
  default `{Public}`, contagious, with explicit audited `declassify`.
- **Universes (K7):** level-expressions (lzero/lsucc/lmax/lvar), predicative +
  cumulative, NO imax/Prop; `@ceiling 2` removed.
- **Names (K12):** qualified `Sym` identifiers; kill `String.to_atom`.
- **Elimination (§E):** sole eliminator = motive-carrying
  `{:case, scrut, motive, branches}`. Recursion is definitional (no `fix`),
  gated by the size-change certificate; Lean recursors exist only as a
  ModuleEncoder lowering.
- **Constructors (K6):** flat ctor spine; params ride the spine at grade 0; the
  signature is the sole authority on the param/field split.
- **Per-branch index refinement (K5):** a kernel typing rule (see §3).
- **Equality (K1):** inductive `Eq : (A: Type ℓ) → A → A → Type ℓ` with `refl`;
  `rewrite` is case-sugar; **K/UIP adopted** (deliberately forecloses
  cubical/HoTT).
- **Primitives (K2):** prims become delta-reducible globals (§2.4); the delta
  table is a named TCB member. Two soundness rules: partial ops never reduce
  when undefined (div/mod by literal zero stays neutral); integer semantics
  model AtomVM/BEAM promote-not-wrap bignums; floats leave NaN/div-by-zero
  non-reducing.
- **Absurdity (K4):** `absurd` deleted; an empty `:case` is accepted when every
  ctor is absent or index-impossible.
- **Serialization (§K, C2):** total and reversible, updated in lockstep.

**Validator status (2026-07-08, §J):** `no_eq_node` :reject LANDED (K1a);
`no_hole` :reject LANDED (K3, Option B — reject at release/emit boundary,
:warn at dev time so `?name` holes typecheck); `no_absurd_node` :reject
LANDED (kernel infer keeps a defensive clause — load-bearing for totality);
`no_rewrite_node` :warn — **Phase B DECLINED with proof**: a sound
`{:rewrite}` node is kept as an accepted representation divergence (two
empirical retirement attempts drifted parity); `no_prim_node` :reject
LANDED; `ctor_signature` partial (grade remainder rides the grade wave);
`case_coverage`/`usage_relevance` kernel-enforced; `grade_on_binders`,
`qualified_syms`, `level_expr`, `no_legacy_reducer` :off (design-gated).
**§J.1 terminal state:** Core is clean to Idris-2 parity minus linear types
ON SOUNDNESS; a declaration-hygiene sweep closed 8 silent-overwrite holes;
six soundness axes probed sound.

---

## 2. Builtin-inductive foundation & primitive retirements

### 2.1 Registry (builtin-inductive-foundation — approved; both phases landed)

Prelude declares `@builtin(:bool) type Bool = False | True` and
`@builtin(:nat) type Nat = Z | S(Nat)`. The schema is validated at seed time on
shape AND constructor names (name check is load-bearing: literal wiring and
erasure atoms key on `False`/`True`; arity-only validation would let
`Coin = Heads | Tails` miscompile). Lookup via `builtin(sig, :key)` on
`Cure.Core.Env`. **Single-registration invariant:** `@builtin` honored only in
prelude sources AND the registry rejects rebinding. Matching is nominal, not
structural. Builtin decls compile first in the `:core` group.

- **Phase 1 (K, gated):** `bool_elim` retired across 9 modules; `{:prim}`
  comparisons return builtin Bool; `Eval.fold/2` HARDCODES `:True`/`:False`
  (no sig threading through Eval; drift guarded by an assertion test);
  `if`/guards retarget to `:case`; erasure emits lowercase booleans.
- **Phase 2 (untrusted C):** Nat→Int erasure (§2.2). The schema table is
  K-owned, seeded in Phase 1.

### 2.2 Nat→Int erasure (nat-int-erasure — Phase 2, untrusted C; landed)

Four lowering rules for the `Inductive.builtin(env, :nat)` family only
(nominal rule — local-Nat fixtures must NOT flip): `Z` → `0`; `S(e)` →
`e + 1`; case → `0 -> a; N when N > 0 -> K = N - 1, b`; first-class `S`/`Z`
→ increment closure / `0` (needed an E-layer eta-expansion fix). The
generics gap is resolved by **parametricity, no monomorphisation** (an
unspecialized body cannot ctor-match a type-param-typed scrutinee; STOP if
any path lets it). Representation-agreement assay `elab/nat_rep`: oracle =
`Normalise.nf(..., delta: :certified, mode: :nf)` (NOT bare `Eval.eval`) vs
the BEAM result.

### 2.3 Sigma retirement (sigma-retirement — Sigma D2, task #13; landed)

Primitive `{:sigma}/{:pair}/{:fst}/{:snd}` + `vsigma/vpair/nfst/nsnd` (~115
sites, 13 core files) retired in favor of the canonical stdlib inductive
`@builtin(:sigma) type Sigma(a: Type, b: (a) -> Type)` with `mk_pair`,
`first`/`second` by match (Agda/Lean/Idris keep Σ in the library, not the
kernel). Locked: level-0 universe haircut (same as Eq); the D1 napp sort clause
SURVIVES (sorts dependent-projection motives); consumption via registry lookup,
not hardcoded atoms (Eq's hardcoded `:Equivalent` is a known wart). **BEAM ABI
preserved exactly** — bare 2-tuples via emit builtin hooks, projections inline
`element/2`. Programmatic seed + stdlib decl with a byte-equal drift pin.
Ordering defends the gate: producers re-pointed before the kernel strip,
`no_sigma_node` :warn between, :reject at end. `core_bridge.ex` was ruled a
Core-grammar consumer — the single authorized carve-out under
`lib/cure/types/`. Corpus was PURGED, not transformed.

### 2.4 Prim ops → delta-reducible globals (prim-delta-globals — K2, task #15; landed)

Re-opened on the parity criterion (Lean `reduce_nat`, Idris builtin-op
records). Locked decisions: (1) builtin-op def-kind is **registry-keyed** —
consumers resolve through the def record, never bare atoms (a user def named
`int_add` must never be delta-folded); (2) compute hook in
`unfold_certified_head` checked BEFORE the certified-body path (ordering
load-bearing: a nil body + `Term.closed?` nil-vacuous quirk would crash
`Eval.eval(nil, [])`); fires only when all spine args whnf to literals via
shared `Eval.fold`; div/rem-by-zero stays neutral; (3) monomorphic per-type
ops (int_*/float_*), type-directed via `primitive_scrut_kind`; (4)
types-carve-out: `core_bridge.ex` retargeted both directions (from_core
needs spine-recognition clauses BEFORE the generic app clause); `reduce.ex`
→ `Normalise.whnf_value`; (5) emit: registry-keyed saturated inline, eta
fun-wrapper when unsaturated; (6) GuardLint recognizes op spines via the
registry; (7) three-phase ratchet — coexist → flip producers → strip (no
phase leaves validator/kernel/emit disagreeing); (8) open prim indices →
generic neutral-spine congruence.

**Amendment A1:** op set = 25 — added polymorphic
`struct_eq`/`struct_ne : Pi(a: Type). a -> a -> Bool` as a transitional
representation of structural runtime equality (NOT a new equational theory):
folds only int/float literal pairs, neutral on ADTs, always uninterpreted by
GuardLint; a future Equatable retargets one site.

### 2.5 infer/check coherence (infer-check-coherence — task #14, K; landed)

Fixed `infer(t)=A ⇏ check(t,A)`: check's ctor clause hard-failed
`:ctor_arity` on the params-on-spine spelling infer accepts. Fix: ordered
branch — fields-only path first, byte-identical (order load-bearing: `pc == 0`
collapses both predicates); `pc + length(tele)` args → shared
`check_via_infer/3` (infer + `subtype?`); anything else → `:ctor_arity`.
Lean-aligned (check = infer + def-eq). The sibling value-level ctor-spelling
dichotomy (Eval/Conv/ι/Erase treating spine vs fields-only differently) was
filed separately and later resolved fields-only (`7b7f071`).

### 2.6 Inductive Int (inductive-int — design approved 2026-07-18)

Replaces primitive `Int` (`{:int_type}`, no constructors, hence no induction or
`match` — root cause of the whole refinement-workaround family) with an
inductive that still compiles to a native BEAM integer, mirroring `Nat`'s
in-tree machinery; Lean's `Int` (`ofNat | negSucc`) is the shape authority.

- **Representation (locked):**
  `@builtin(:int) type Int = FromNat(Nat) | NegativeSuccessor(Nat)` —
  canonical (zero only `FromNat(Z())`), decidable structural equality.
  Rocq-style binary `Z0|Zpos|Zneg` REJECTED (needs a `Positive` type; the
  proof presentation doesn't need speed — the runtime stays native).
- **Native-parity mechanism:** `{:int_lit, n}` is the compact canonical form
  (like `{:nat_lit}`); an audited single-step `reduce_int` fold (analog of
  `Eval.nat_to_ctor/nat_to_ctor_if`) wired into the four ι-sites: `Eval`'s
  `:case`, `Normalise`'s two ncase arms, and — soundness-critical —
  `conv.ex` literal-vs-ctor conversion. Eliminator on `{:int_lit, n}`:
  `n ≥ 0` → `FromNat` binding `{:nat_lit, n}`; `n < 0` →
  `NegativeSuccessor` binding `{:nat_lit, -n-1}`. Existing int_* ops stay as
  the audited computational rule. Codegen needs a **new name-keyed**
  `int_ctor?` lowering for open ctor applications (both ctors 1-ary; arity
  dispatch cannot disambiguate): `FromNat(n)` → `lower(n)`;
  `NegativeSuccessor(n)` → `-(lower(n)+1)`.
- **Representation question:** approach (i) chosen — move `Int` out of
  `seed_primitives` into a genuine `seed_builtin(:int, ...)` family and
  repoint every `{:int_type}`/`{:int_lit}` special-case (~11 core/elab
  files); fallback (ii) facade (`{:int_type}` defeq to the family) only if
  the blast radius proves unmanageable, recorded not silent.
- **TCB:** the `reduce_int` fold is the ONE trusted addition (Lean-aligned →
  blanket approval). **Sound only because BEAM integers are
  arbitrary-precision** — on a fixed-width target the correspondence would
  be UNSOUND (load-bearing caveat for the module doc). Anything needing a
  kernel rule beyond the fold: hard-stop.
- **Back-compat hard gate:** entire existing suite byte-identically green;
  any non-provably-equivalent regression is a Halt condition. Phase 1 =
  substrate + induction smoke-test; Phase 2 = ordered-ring lemma kit (order
  family, monotonicity, transitivity, sign lemmas, `0 ≤ -1` contradiction
  extractor), each Idris-mirrored `rel=same`. `IsTrue` and the `of_int`
  clamp behavior are untouched (two stale "Int is primitive" doc comments
  get refreshed).

---

## 3. Dependent case & index unification (case-index-unification — approved; landed)

Replaces `branch_index_subst/4` with a bidirectional first-order unifier
`unify_indices(ctx, result_indices, scrut_indices, arity) ::
{:solved, subst} | :trivial | :impossible` for dependent-`case` branch
refinement (closes the GADT incompleteness; e.g. `wrap : Ix Causal` forces
`n := Causal`). Rules:

- A bare ctor-telescope var on the result side always binds to the scrutinee
  side. **Load-bearing:** Cure declares indexed types with an EMPTY param
  telescope, so uniform params show up as var-vs-var; the reverse orientation
  corrupts shared params (an earlier draft mandating reverse orientation was
  WRONG).
- `:data` heads compared on the flattened spine; rigid head clash →
  `:impossible` (branch discharged, body unchecked; coverage unchanged).
- Undecidable pairs → no binding, fall through to conversion (**monotonic
  degradation** — never a new rejection class).
- Same-key rebinding must Conv-check (clash → `:impossible`, never a silent
  clobber).

De Bruijn: single space = ctx_branch numbering; ctor args at `0..arity-1`
unshifted; outer-var keys reified at outer depth then `Term.shift(arity, 0)`.
Invariants: refinement soundness; impossible-only-on-definite-clash;
occurs-check; monotonic degradation; merge consistency.

---

## 4. Unification & WHNF

**Supersession:** `2026-07-03-postponed-constraints-design.md` is SUPERSEDED
by whnf-unification — the reachable gap was missing WHNF before unification,
not lack of postponement (which flipped no reachable verdict); kept for
history, do not implement.

**whnf-unification (landed; roadmap row #11, E-layer only):** insert whnf
between `force_d` and structural dispatch in `Cure.Elab.Unify.do_unify`; if
reduced, recurse (Lean's loop). Meta-aware whnf trick: zonk → substitute
unsolved `{:meta, id}` with reserved opaque globals `:"$meta$<id>"` (no
signature entry → neutral, blocks as scrutinee) → reduce via `Eval.eval/2` +
`Normalise.whnf_value(..., delta: :certified, stuck_cases: :preserve)` +
`Quote.reify` with a hand-built neutral-var env → reverse-map placeholders.
Fuel exhaustion → fall back un-reduced (strictly additive). Fixes
`plus(Z,?m) =? S(Z)`; genuinely-stuck `plus(?m,Z)` still rejects
(correctly). All three reference languages reduce both sides before
comparing.

---

## 5. Termination certification

### 5.1 Size-change (size-change-termination — K/certificate.ex; landed)

Port of Idris `SizeChange.idr`, scoped to single-function self-recursion.
`SizeChange = Smaller | Equal | Unknown` semiring (multiply: Unknown absorbs,
Smaller∘Equal = Smaller; add: keep strongest). One change matrix per
self-call; transitive closure; total iff EVERY idempotent matrix has a Smaller
diagonal entry. **Reconstruct-equal rule** (Ackermann shape): a call-arg
syntactically identical to the ctor form the param matched is `Equal` — NEVER
`Smaller` from reconstruction. Mutual recursion conservatively rejected at
this layer (see §5.2). Pre-approved under the Idris-alignment blanket;
assurance, not reach.

### 5.2 Mutual-recursion SCC certification (mutual-recursion-reduction — ✅ LANDED `a4f071fb`)

**Bug:** certification was per-definition and certified only the submitted
name. For a mutual pair A (declared first), B (last): validate(A) defers
(B's body still pending → `pending_callee?`); validate(B) proves the whole
SCC total via `mutual_group_total?` but certifies ONLY B; A stays
uncertified (un-δ-reducible) until the too-late end-of-module
`certify_deferred` sweep — proofs about the first-declared member failed
`:conversion_failure`, and swapping declaration order "fixed" it.

**Fix (K, hard-stop discipline; Idris/Agda/Lean certify a `mutual` block as
a unit):** when the group check succeeds, certify every member of the SCC —
`Certificate.total_group/3` (thin wrapper over `mutual_group`) +
`Env.certify` each member in `validate_certificate/2`. Guardrails: never
certify a member with a pending body; singleton groups behave exactly as
before; `pending_callee?` deferral untouched — the fix changes how many
names a SUCCESSFUL check certifies, never whether a group certifies.
Soundness: every member shares one size-change proof and was
`check_def`-validated; only already-proven-total members get certified.
Known limitation (documented, not chased): a def interleaved inside an
incomplete mutual group still sees earlier members opaque. Antibody: a
divergent mutual pair stays uncertified. Payoff: n-ary session types
(`dual`/`dual_branches`, `dual_involution`); oracle `otp_nary_choice`
rel=same. Related (still valid): a plain forward reference defers
certification to the end-of-module sweep — workaround is define-before-use
ordering.

### 5.3 Known checker gap (K-bug 2, OPEN — elaborator-gaps-verified-status)

`certificate.ex` (`walk_node` `{:lam,...}`, `arg_relation/2`) rejects
guarded-lambda recursion: a self-call under an unapplied lambda
(`Bind(e, fn(y) -> bind(g(y), f))`) yields `:unknown` → never certifies →
Conv never δ-unfolds `bind` → every `bind(...)` in type/index position stuck.
Idris2 accepts under `%default total`. Fix is HARD-STOP TCB-approved: recognize
deferred self-calls under an unapplied lambda as not owing the decrease at
that point (mirror Idris). Antibody = must-certify pin. Completeness bug, not
soundness.

---

## 6. The refinement arc: SMT removal → reflection → proof search → LIA → holes

### 6.1 Refinement removal (refinement-removal — task #19; landed)

Operator order: remove refinement types ENTIRELY; return only if SMTCoq-style
proof reconstruction is ever ported (stretch, deliberately NOT queued).
Classic-pipeline-only; zero core/elab changes by construction. Deleted: parser
refinement grammar (`{x: T | p}` became a plain parse error), SMT
solver/translator/parser, five classic refinement modules, `Std.Refine`, docs
claims, Antigen smt surface. Kept: GuardLint + z3 `Cure.SMT.Process` (untrusted
lint), kernel `refine_branch` (Class-C, different concept). Locked context:
**Z3 stays out of the TCB permanently** (smt-trust-boundary decision).
*Partially superseded:* the 07-18 int-refinement prelude (§6.2) reintroduced
the `{x: T | φ}` surface over IsTrue — proof-backed, still no solver.

### 6.2 Int refinement prelude (int-refinement-prelude — LANDED, branch `implicit-goal-solving`; later merged `cf3591a5`)

Closes the Int gap of the restored proof-backed refinement surface via
**decidable-boolean reflection (route B, chosen over a Nat-bridge)** — the
idiom all three reference languages use for primitive integers (Idris
`So`/`Oh`, Agda `T`, Lean `Decidable`). Sound because a closed comparison
folds to the inductive `True()` ctor value, so `IsTrue(5 > 0)` normalizes to
`IsTrue(True())`, inhabited by `Confirmed()` **by pure computation** — no
solver, no postulate, no kernel change (K untouched; a needed change =
hard-stop). "No E change expected" framing retired — three approved
untrusted changes: **P** comparison operators parse inside a
type-application argument (`6ea68573`); **E1** `idx_to_core` lowers
comparison/connective indices to the Int-builtin Core spine; **E2** the
refinement sugar. Surface: `Std.Proof.IntMath` with
`type IsTrue indices (claim: Bool)`, `Confirmed : IsTrue(True())`,
`decide_is_true` (Decision with evidence); descriptive names per the
standing directive. Sugar (operator-approved "Both"):

- **Level 1 — auto-wrap:** in `{x: T | φ}`, a `Bool`-typed clause becomes
  `IsTrue(φ)`; a `Type`-typed clause passes through; neither → rejected.
- **Level 2 — auto-discharge:** a value whose obligation reduces
  (whnf+delta) to `IsTrue(True())` gets `Confirmed()` filled automatically;
  `IsTrue(False())` → rejected; stuck/open → the elaborator does NOT invent
  a proof (explicit evidence or `refine(value, proof)`, the open-term path).

**Honest scope boundary (unchanged from SMT):** closed/binder-carried
obligations discharge now; abstract quantified Int arithmetic is not
constructively provable without induction and defers to the verified
decision procedure (§6.5) — parity, not regression (deleted SMT couldn't
soundly discharge it either). Acceptance: `dependent_types.cure` re-refined,
un-skipped, `main() == 6`. Scoped out with reasons: `moneta.cure` `scale`
(no refinement→base projection coercion — later designed in §6.4 item (c) —
and the build has `check_types: false`); a nested-stdlib out-of-tree
resolution gap; named predicates (`-> Type = IsTrue(n > 0)` bodies hit
comparison-in-term-position `unsupported_expression`).

### 6.3 Auto-lemma proof search (auto-lemma-proof-search — approved; MERGED `cf3591a5`)

E-only; soundness-neutral by construction (kernel re-checks every found
term — exactly Idris/Agda/Lean). Trigger: a `?` hole in argument position —
a new `{:hole, meta, _}` clause on `elaborate_expr_checked`; success → found
Core term; `:none` → graceful `{:hole, name}` (participates in
`hole_goals`/`check_codegen_ready`), NOT a hard error. Architecture:
`Cure.Elab.ProofSearch.resolve(goal_type, local_context, env) ::
{:ok, core_term} | :none`; the ordered solver list is a staging seam.

- **Solver 1 — tagged-lemma resolver:** `@lemma` registry indexed by
  conclusion head; head lookup → unify candidate conclusion vs goal
  (instantiates implicits) → explicit hypotheses become recursive
  sub-goals → assemble application. Local-context path includes single-level
  refinement/Sigma second-projection candidates. Ambiguity discipline =
  **Agda's** (collect all, unique-or-defer; ≥2 distinct candidates → hard
  ambiguity error naming competitors), deliberately NOT Idris's
  order-sensitive first-wins. Backtracking with state save/restore; depth
  bound + "trying"-stack cycle check (cycle → `:none`, never crash). Found
  proofs not erased by default (explicit params default ω).
- **v2 (SHIPPED) — `solver_positivity`:** Lean-`positivity`-style
  syntax-directed decision procedure for the arithmetic-sign fragment;
  `run_solvers` returns the first non-`:none` verdict (a genuine ambiguity
  error surfaces immediately, never masked by fallback). Untagged stdlib
  sign lemmas reached via virtual lemma entries fed to the SAME `try_lemma/5`
  path; syntax-directed because both plus-lemmas conclude
  `IsPositive(plus(a,b))` — tagging both would raise a FALSE ambiguity;
  `multiply` deliberately excluded (owned by solver_lemma via its tag).
  Verification lives at the codegen gate, not the differential oracle (an
  unfilled hole still elaborates `{:ok, env}`).

### 6.4 Axiom-free refinement reflection (axiom-free-refinement-reflection — design; landed UNMERGED `0d1e2f17`+`3213fe2a`)

Stdlib + E; NO kernel change (doubly load-bearing while certificate checking
is being built — zero new trust: no axioms/postulates/@extern/believe_me;
perceived kernel need = hard-stop). Goal: open `IsTrue(boolean comparison)`
obligations reach the inductive `Std.Proof.Math` families. Key insight: stop
treating primitive `Int` as the refined-quantity carrier — represent refined
non-negative quantities as `Nat`/`Bounded` where induction exists; project
to machine `Int` only at the boundary. Naming is a first-class requirement
(fully spelled-out lemma and binder names). Layers: (1)
`Std.Proof.BooleanReflection` — connective algebra over IsTrue (conjunction
split/intro, disjunction injections, negation contradiction), proved by
matching on the reducing operand (`and(True(), r) ≡ r`); (2) Nat reflection
bridge — structural boolean comparisons + both-direction reflection lemmas
(agda-stdlib `<ᵇ⇒<` transliterations) plus free structural
`to_integer(value: Nat) -> Int` (constructive inverse of the trusted
`of_int` clamp; total, no assertion); (3) runtime decision at genuine
external boundaries via `decide_is_true` (checked branch; asserts nothing).
Automation: NO new solver — intro/reflection lemmas carry `@lemma`;
conjunction ELIMINATION = a small terminating context-saturation pass in
ProofSearch (each hypothesis `IsTrue(and(l,r))` contributes both halves
before search). **Honest deferred ledger:** static proof about abstract
primitive-Int arithmetic requires trusted `Int ↔ Nat`
homomorphism-on-the-non-negative-cone axioms, each a named ledger entry WITH
its non-negativity guard (load-bearing: `of_int(2 + (-1)) = 1` but
`plus(of_int 2, of_int(-1)) = 2`); property-testable though unprovable;
designed and ledgered, NOT built. **Item (c):** refinement→base projection
coercion — checking a `Sigma(refined_value: T, predicate)` term against
expected `T` inserts kernel builtin `sigma_first` (NOT
`Std.Refine.refined_value` — import-independent); pure E; unblocks the
moneta blocker.

### 6.5 Verified LIA reflection (verified-lia-reflection — approved design, branch `smt-solver`; rebased 2026-07-20 onto inductive Int)

Closes the open-linear-integer-arithmetic breadth gap the sound way named in
the locked smt-trust-boundary decision: **a verified LIA decision procedure
via computational reflection — no solver in the TCB** (SMTCoq/Rocq-Micromega
architecture specialized to LIA and the target `IsTrue(<Bool comparison>)`).
**2026-07-20 authoritative amendment:** `Std.Int.Int = FromNat |
NegativeSuccessor` + `Std.Proof.IntOrder` are the sole integer substrate — do
NOT create the formerly-planned parallel `Std.Integer.Zed` family; scalar
order monotonicity alone is not enough to justify Farkas combination (the
algebra/vector-semantics/shape/Boolean-inversion layers §3.5–3.9 are
required).
**2026-07-22 execution plan:**
`2026-07-22-certificate-generator-integration-design.md` records the exact
remaining checker proof, canonical producer boundary, elaborator integration,
strict external protocol, diagnostics, IDE work, phases, and definition of
done. It is authoritative for implementation details beyond this summary.
**2026-07-22 OTP-first amendment:** the first vertical slice is B3 semantic
inclusion for commutative-regex mailbox patterns, not generic QF-LIA. Patterns
normalize to finite unions of linear sets over Parikh vectors; an untrusted
producer supplies affine component embeddings, checked by ordinary Cure code
and bridged back to `Otp.Meta.MailboxPattern.Accepts`. The locked positive probe
is `PStar(PTimes(TA,TA)) <= PStar(TA)` and the reversed negative control has
Parikh counterexample `[1,0,0]`. This slice lands end to end before the general
Farkas and cut/split pipeline. Full mailbox inclusion may require semilinear
covering or quantified Presburger elimination; the affine-embedding checker
returns honest `Unknown` outside its sufficient fragment.

- **Seam (E, additive):** obligation the syntactic paths can't close →
  registered `(recognizer, producer, checker)` entry → untrusted producer
  emits `Prf certificate | Model | Unknown` → elaborator builds
  `check_lia(hyps, goal, cert)` → **kernel discharges by COMPUTING it to
  `True()`** (existing whnf/δ; no new kernel rule — hard-stop if one seems
  needed). One registry entry today (LIA); Alethe native-proof replay is a
  future registration.
- **Checker (Cure metatheory, `Std.Proof.LinearArithmetic`):** `LinearAtom`
  (coeff vector, constant, relation LessEqual/Less/Equal; `≥`/`>`
  normal-formed by negation), `FarkasWitness = List Nat` of length
  `|hyps| + 1` (dense positional), `Valuation`, `evalAtom`, `AllHold`.
  `check_lia` is total/structural: negate goal, form `Σ wᵢ·atomᵢ`, check
  manifest contradiction (`0 ≤ -1`/`0 < 0`). The proof object is
  `ValidFarkasCertificate` (checked shape/combination/zero-coefficient/
  negative-bound evidence); `check_lia` is its Boolean projection with a
  proven inversion bridge. `check_lia_sound : ... ->
  IsTrue(evalAtom(goal, env))` proven in Cure, Idris-mirrored — trust rests
  on the existing kernel checking it; TCB does not grow.
- **General-LIA scope & honesty (after the OTP slice):** goals restricted to
  `LessEqual`/`Less` (negating `Equal` is a disjunction no single Farkas
  combination certifies; `Equal`
  hypotheses fine). Farkas core is sound for ℤ, complete over ℚ; ℤ-only
  instances (`2n = 1`) need cutting planes (additive follow-on; producer
  reports `Unknown` meanwhile). Silent truncation of malformed certificates
  is inadmissible — explicit shape evidence.
- **Producer (P2, untrusted Elixir):** deterministic Fourier–Motzkin/simplex
  (fixed variable order/pivot rule/iteration bound — replay determinism).
  External solvers (Z3/cvc5/veriT) are a documented drop-in
  coefficient-finder, native proof discarded. Phasing P1 checker+soundness →
  P2 producer (property-test agreement) → P3 seam. Probes: positive
  certificate, forged-witness antibody, shape antibodies, `2n = 1` boundary;
  probes immutable once fixed.

### 6.6 First-class holes (first-class-holes — design approved, branch `implicit-goal-solving`; K+E hard-stop; TCB-size commitment explicitly relaxed for user-friendliness — "we're doing C")

Slice 1: a `?` hole becomes a first-class stuck NEUTRAL `{:nhole, id}`
surviving elaboration and normalization (foundation for
Agda/Idris/Hazel-style typed-hole interaction), removing a crash
(`Eval.eval` had no `{:hole,_}` clause → `FunctionClauseError` on
argument-position holes; an undischarged proof-search obligation must
degrade to a live hole). K changes additive only: `eval.ex` hole →
`{:vneutral, {:nhole, id}}`; `conv.ex` two identity clauses (`a == b`;
catch-alls already reject hole-vs-other); `quote.ex` reify back;
`normalise.ex`, `kernel.ex` (check accepts a hole at any goal; infer stays
`:hole_in_inference_position`), `term.ex` (inert leaf, id stable) unchanged.
**Soundness pivot — unique deterministic hole ids:** previously all holes
lowered to `{:hole, ""}`; as neutrals, same-id holes are definitionally
equal, so `refl : ?a = ?b` then filling 0/1 would "prove" 0 = 1 — UNSOUND.
Scheme: unnamed `?` → `"<module>.<def>:<line>:<col>"`; named `?foo` →
`"<module>.<def>#foo"` (repeated `?foo` in one def = deliberately the SAME
hole, Idris named-hole model); deterministic/positional (NO gensym) so
Antigen and the oracle replay identically. Each hole = its own fresh axiom
of its checked type, convertible only to itself. **Codegen stays blocked:**
validator `no_hole: :reject` (K3) unchanged — "type-checks ≠ ships"; the
`{:hole, "__pending__"}` sentinel is collision-free by construction. E
wiring: resolver `:none` → surviving `{:hole, id}`; ambiguity errors still
surface. Antibodies: distinct holes not convertible; hole vs non-hole not
convertible; same-id reflexivity; stuck-not-crashing. Slices 2 (hole
registry/goal reporting) and 3 (refine/case-split/auto actions) are
follow-on specs.

---

## 7. Trust ledger — axiom-closure enforcement (trust-ledger-ph2-enforcement — DESIGN APPROVED `f362196f`)

Turns the reporting tool `cure audit trust` (Ph0/Ph1 merged `7b82c9f`) into
executable policy; first slice of doctrine Gate 10; TCB-additive, zero
kernel risk. The auditor (`lib/cure/audit/`) is untrusted and reads the
elaborated `Cure.Core.Env` — the only vantage seeing every axiom after macro
re-elaboration. `Ledger.reachable/2` + `collect/3` compute the transitive
axiom closure of `@extern` Axioms `{mfa, type, via, bucket}`; `Refs` is a
fail-closed Core-term walk; holes/absurd collected; `not_proven_total` =
completeness note; `unresolved` = defect class; determinism load-bearing.
CLI philosophy (locked): "Never wired into `cure build`: a compiler that
refuses to build over an audit trains people to hate the audit" —
enforcement is opt-in.

Ph2 adds: (1) per-def closure `--def <name>` (unknown def = error); (2) axiom
allowlist `priv/audit/allowlist` keyed `{mfa, type}`, with a deterministic
`--emit-allowlist` bootstrap generator (a human commits it — never an
auto-approver) — a machine-checked ratchet replacing manual diff; (3)
profiles: `dev` (report, exit 0) / `release` (exit 1 on hole, unresolved,
unaudited, or non-allowlisted axiom). `release` deliberately does NOT fail on:
absurd (kernel-checked impossibility), `not_proven_total` (general recursion
is legal in the computation stratum), builtins, opaque types, allowlisted
axioms. Deferred: per-module gating (~40% of stdlib UNAUDITED blocks a
program-wide release), evidence-class taxonomy (Ph3), content-addressed
manifests (Ph3). No kernel/TCB changes — a need means stop and re-scope.

---

## 8. Core-walker drift audit (core-walker-drift-audit — AUDIT + REMEDIATION COMPLETE; §10 of the spec is current truth over §4)

**Missing invariant (now instituted):** *every traversal of a Core term must
be total over `Core.Term.t()`, and where it cannot be, its catch-all must
fail CLOSED* (`unify.ex escapes?` is the exemplar). ~25 hand-written walkers
across E and K mostly treated unknown compound formers as leaves and
reported success — one missing invariant instantiated 12×, generated by
language growth (`:let`, QTT grades, Effect family). Taxonomy: **Class A**
generic structural descent (safe iff no binder-depth tracking); **Class B**
fail-closed (safe, soundly incomplete); **Class C** fail-open leaf
assumption (the defect class). Discriminators: (a)
`:let`/`effect_pure`/`effect_bind` CANNOT appear in types, so type-only
walkers are inert; (b) post-kernel walkers (Erase, emit) are never
re-verified — silent miscompilation lives there; (c) destructive walkers are
safe only if the field is re-derivable — Pi/Lam grades re-derive from the
signature, but the `:let` grade lives ONLY in the term (the kernel is
deliberately quantity-blind; the E-layer usage check is load-bearing for
soundness).

**Fixed (all with red→green tests):**
- **§4.2 CRITICAL:** `Subst.shift`/`replace` hardcoded
  `Grade.unrestricted()` on `:let`, laundering grades before `Relevance`
  (sole reader) → erased proofs usable at runtime / linear binders
  droppable. Fix: thread `g`.
- **§4.0 CRITICAL:** `Subst` skipped `effect_pure`/`effect_bind`;
  `instantiate/2`'s outer-var strengthening skipped inside effect nodes
  during collapsible-ctor erasure → silently resolved to the wrong binder,
  wrong BEAM code, never re-checked. Fix in subst.ex (effect_bind recurses
  at same depth — binds nothing).
- **§4.7 CONFIRMED SOUNDNESS HOLE → FIXED:** `count_level` returned 0 for
  Effect-wrapped subterms, so `join_binder_safe?` authorized an un-join;
  working exploit — an `:affine` param consumed twice on one path was
  ACCEPTED. Fixed in relevance.ex; the one-shot control stays accepted
  (optimization repaired, not disabled).
- **§4.6 LOW** `global_refs` missed Effect (tooling-only); **§4.8** latent
  erase.ex fixed; **§4.9** dead lambda sub-branch retry removed (non-lambda
  retry is LOAD-BEARING, kept).

**Deliberately NOT changed:** §4.4 kernel
`subst_params`/`replace_branch_vars` fail open on :let/Effect — the probe
EXONERATED the kernel as fail-SAFE (`unify_one` lacks an effect_type clause
too → `:undecided` → dropped → completeness cost only); no red test → under
the TCB hard-stop rule `kernel.ex` left byte-identical (reach-pinned). §4.5
`mabs` clauses added but catch-all left OPEN (hot path, uncharacterised
domain — "do not fail closed to look consistent").

**Refuted findings (do not re-report):** `has_meta?`; Pi/Lam grade discard
(kernel re-derives and compares); `mabs` reachability;
`totality_closure.collect` (Class A, sees into effect_bind);
`Validator.children` (has eff_children clauses — codegen release gate
sound); `Relevance.walk` on Effect(T) (unreachable in bodies).

**Residual:** fail-closed conversion surfaced two non-Term body shapes old
catch-alls swallowed — `{:extern, {m,f,a}}` and `nil` (now explicit; the
body-walker domain is wider than `Core.Term.t()`). Open: derive the
traversals (fail-closed is a tripwire, not a cure); kernel walkers
incomplete-but-safe (reach-pinned); a stale Antigen coverage baseline.
Antigen indictment: 318/318 kernel shape cells were green while the E-layer
walker class was wide open — proposal: a coverage cell per
(walker × former). Un-searched areas flagged: kernel.ex's own exhaustiveness
(`check_coverage`'s two literal/ctor duality bridges — a third duality would
be mis-verdicted `:impossible`), certificate/conv dispatch, coherence,
resolve, macro_expand, union/guard_lint; the metavariable-lifecycle lens
produced no findings and never appears as a tag — suspicious silence.

---

## 9. Elaborator gaps — open ledger (open-elaborator-gaps-handoff + elaborator-gaps-verified-status)

**Framing:** every gap is a completeness/ergonomics REACH gap, never
soundness — Cure sometimes rejects a well-typed term Idris accepts; the kernel
re-check is the safety net. Unifying theme: E1/E2/E6/E8 are ONE family —
**index existentials + sibling/context refinement**; Idris avoids it by
solving each clause as one simultaneous unification problem with one threaded
metacontext. Verified status (branch `elaborator-gaps`, six independent agents
+ Idris differential), reconciled with later landings:

- **E1 + E1-sub** ✅ CLOSED by `specialize_branch_context_subst` (rewrites
  BOTH `ctx.types` and `ctx.env` by the branch-unify subst — sibling
  refinement reaches the coverage checker AND written body terms); locked by
  oracles `e1sib`/`e1sub` + antibody (batch `1e7e25f5`).
- **E2-residual** ✅ LANDED `47b0cacc`: relevant implicit ctor-index binders
  via plicity/quantity DECOUPLING (per-slot `plicities`; kernel never reads
  them → out of TCB). The `{:erased_used_relevantly}` erasure gate itself is
  SOUND.
- **E6-residual** ✅ LANDED `105b43ea`: shared-metacontext problem closed via
  component-wise `unify_data_components` + deferred-eq fixpoint. ⚠️ VARIANT
  A (concrete goal → `:ctor_arity`, declarations.ex split bug) reach-pinned
  OPEN. The floating-OUTPUT-index variant is NOT a gap — Idris rejects it
  too; reformulate (index family gets only its INPUT indices) — authoring
  guidance, not a bug.
- **E8** ✅ LANDED `3d9f6b1a`: `invertible_index?` narrowed to HEAD-only — a
  ctor-headed index carrying a computed subterm inverts by ordinary
  structural unification; only non-ctor heads keep the
  `elaborate_carried_eq_branch` detour. Workaround removed from
  `otp_mailbox_pattern.cure`.
- **E9** OPEN, premise FALSIFIED: Idris rejects the repro too (clause split,
  `case`, real `with...proof p`) — NOT a reach gap; closing it means
  inventing auto-synthesis of an `Equivalent` hypothesis on stuck index
  pairs, beyond Idris parity. The index-generalization technique (carry
  `q : idx = concrete` as an explicit argument) stays the sanctioned route.
- **E10** OPEN (K+E, hard-stop, do last): higher-order function argument not
  reduced in a dependent index position (lambda in an `Equivalent` index
  crashes normalization; named/partial applications don't reduce in
  conversion). Workaround: first-order monoid formulation
  (`Otp.Meta.EffAlgebra`). **E10a** ✅ LANDED (P+E): `fn(y) -> ...` in
  type/index position no longer mis-parses as an arrow type.
- **E11** ✅ crash fixed + **E11-Stage-2** ✅ LANDED: index-position
  type-directed overloads via public `Elaborator.elaborate_overloaded_app/7`;
  ambiguity fails closed.
- **E12** OPEN (E-only): `rewrite`'s occurrence-finder is δ-blind —
  `abstract_term` walks the goal without unfolding defined functions →
  `:rewrite_no_match` for an LHS exposed only after δ+ι; kernel conversion
  DOES see through. Fix = WHNF/δ-reduce on miss (matches Idris). Distinct
  from E8 (present-but-unrefined vs absent-until-unfolded — do not
  conflate). Workaround: case scrutinees concretely.
- **E13** OPEN (E-only): a reflexive/diagonal GADT ctor (`SubRefl :
  Sub(l, l)`) unifies `a = b` only one-directionally; later refinement of
  one side doesn't mirror → `:unsolved_metavariables`. Fix: two-way link +
  re-solve. Workaround: explicit shared continuation (`7d0ccad1`).
- **K-bug 1** OPEN (K, hard-stop TCB-approved): order-dependent constructor
  injectivity in `unify_one/4`/`bind_index/4` — var-first fails where
  ground-first accepts; missing symmetric clause. Antibody =
  symmetric-decidability pin. Completeness, not soundness; does NOT unblock
  E9. **K-bug 2** OPEN — see §5.3.
- **K-bug 3** MISDIAGNOSED — NOT a Cure gap: Idris also rejects the n-ary
  branch-merge group (`idris2 --check` exits 0 even on totality errors — the
  "Idris accepts" evidence was bogus); Cure is correctly conservative and
  aligned. REAL finding (LANDED): the oracle's `idris_verdict` was
  totality-blind; `oracle.ex` now rejects on `is not total|is not
  covering|not strictly positive` (for a proof oracle, totality IS
  soundness). Zero shipped verdicts flipped; older-cluster regeneration is a
  hygiene follow-up.

Discipline per gap: red-green oracle-anchored (paired `.cure`/`.idr`,
`rel=same`); a negative antibody per fix; hard-stop for K; done = the
workaround is removed from at least one real module which still replays
`rel=same`.

---

## 10. Resolved limitation: typealias forward reference (typealias-forward-reference-limitation — RESOLVED 2026-07-17)

Forward-referencing an explicit `typealias` now works: a header pre-pass
registers a body-less alias def (erased type-param telescope, conservative
universe); the main pass installs checked bodies; a dependency-ordered
completion pass re-elaborates for exact universes; a kernel-driven
certification sweep makes chains available to conversion before bodies
check. `typealias` nodes carry a parser marker (disambiguating from
single-ctor `type X = Y`); alias cycles rejected before certification.
Lift-module was never affected (`LiftModule.inherit_scope/2` prepends
enclosing-unit declarations with shadow-drop).

---

## 11. Evidential systems architecture (cure-evidential-systems-architecture — doctrine, 2026-07-13)

The 4637-line north-star doctrine for future architecture (explicitly NOT a
claim about the current implementation; supersedes prior architecture docs).
Governing principle: *"Cure must be more suspicious of its own proof
infrastructure than it is of user programs."* Binding commitments:

- **Executive shape:** small intensional quantitative dependent value
  kernel; separate dependent computation core (CBPV) with explicit effects,
  continuation multiplicity, destruction, cancellation, runners;
  identity-only implicit subsumption; explicit
  adapters/validation/approximation; opaque modules; stratified contract
  theories; domain calculi; relationally specified compiler stages; a
  claim-and-evidence graph; deployment profiles (development through
  security.hardened). **Evidence classes (9, NEVER implicitly
  convertible):** Proof, CheckedCertificate, Assumption, Observation,
  Measurement, MonitorKnowledge, StatisticalEvidence, TestEvidence,
  TrustedClaim. Solver results are Proven/Disproven/Unknown(reason); no
  timeout or budget exhaustion is ever interpreted as acceptance.
- **Core constitution:** the kernel MUST NOT contain Flow/actor scheduling,
  SMT, model checking, FFI, codegen, migration, or optimization. ValueType
  vs ComputationType strata; effectful computations MUST NOT execute during
  conversion; Partial never reduces in conversion. Predicative universes,
  explicit levels, no Type:Type; no general equality reflection; no
  universal proof irrelevance (quantity-0 marking);
  funext/quotients/univalence only as explicit axioms in the axiom closure.
  Proof irrelevance alone MUST NOT imply erasability. Only regular strictly
  positive inductive families initially; dependent pattern matching
  elaborates to checked eliminators/decision trees with a coverage
  certificate — the kernel MUST NOT trust surface coverage; absurd branches
  carry emptiness evidence. Holes explicit; no hidden sorry in certified
  artifacts. Unfolding opaque across module boundaries by default;
  transparency in semantic hashes. ReferenceChecker + ProductionChecker.
- **Conversions:** five relations (RuntimeIdentityInclusion,
  ProofForgettingRefinement, Adapter, Approximation, DynamicValidation);
  only the first two implicit, and only if representation-identical with no
  code/allocation/failure/effect/loss. Int is NOT a subtype of Float.
  Coercion graph acyclic, deterministic, link-time validated. Coherence: one
  canonical instance per protocol/type head; resolution never depends on
  import/filesystem/hash/timing order; the kernel checks the elaborated
  call, never reruns instance search.
- **Computation/actors/Flow (selected):** continuation quantities
  (NeverResume…Many), handlers default one-shot; destruction taxonomy
  Linear/AffineForgettable/AffineDestructible/Unrestricted; cancellation is
  an effectful protocol transition. Flow: two primary semantics (stream +
  transition) with required equivalence; guarded feedback (delay or
  constructive-causality proof); only Universal/SchedulerBounded queue
  bounds suffice for static embedded allocation. Mailbox formalism MUST
  model actual BEAM semantics (arrival order, selective scan, retained
  unmatched messages, timeouts, starvation); a Cure-to-CoreErlang proof MUST
  NOT imply ERTS is verified. UnknownCommitStatus MUST NOT auto-retry
  non-idempotent effects. Monitors compute knowledge, not infinite-trace
  proof; safety shields MUST own the actuator capability. Noninterference
  names secrets/observer/attacker; declassification is a governed effect,
  not a cast; attestation yields scoped revocable authority, never Bool.
- **Cure Low / embedded:** a small imperative systems calculus (NOT
  unrestricted dependent C) with explicit memory classes (prefer weakest);
  interrupts need whole-call-graph closure; static Flow fuses (never one
  process per node); memory/stack/timing certificates with NO implicit
  promotion; AtomVM MUST NOT inherit BEAM/ERTS certificates by analogy; FFI
  evidence levels reject Unchecked in high-assurance profiles.
- **Evidence infrastructure:** canonical binary checked core (text is not
  the authoritative identity); standalone `cure-check artifact.cureproof`
  (no plugins/network, deterministic, resource-limited); certificate
  producers untrusted, checkers recompute; many trusted checkers ≠ small
  TCB; axiom-closure exposure + allowlist (implemented as §7); no hidden
  admission; cache hit ≠ evidence; replayable from scratch.
- **Red-team & gates:** metatheory interaction matrix; ~23 Antigen attack
  classes; differential semantics across ~10 evaluators; proof mutation
  (every meaningful mutation rejected). Implementation Gates 0–20.
  Prohibitions §161–177 (selected): no Type:Type, no general equality
  reflection, no effectful conversion, no hidden approximation, no unchecked
  pattern coverage, no silent holes, no monitor-as-proof, no hard-realtime
  claim without a deployment model, no session-type marketing without BEAM
  semantics, no exactly-once without commit detectability, no security
  property without attacker+observer, no "small TCB" claim ignoring
  checkers, no compatibility claim without an observer, no
  paper-name-driven assurance.

---

## Source specs

- `2026-07-01-case-index-unification-design.md` — bidirectional first-order index unifier for dependent-case branch refinement (§3).
- `2026-07-03-builtin-inductive-foundation-design.md` — `@builtin` registry, Bool/Nat schemas, bool_elim retirement (§2.1).
- `2026-07-03-postponed-constraints-design.md` — SUPERSEDED by whnf-unification; kept for history (§4).
- `2026-07-03-whnf-unification-design.md` — WHNF before structural unification with meta-placeholder trick (§4).
- `2026-07-04-size-change-termination-design.md` — Idris-ported size-change termination semiring (§5.1).
- `2026-07-07-dependent-kernel-cleanup-strategy-design.md` — the 7 locked campaign decisions incl. Idris-shaped Core and lean4lean second checker (§1.1).
- `2026-07-07-final-core-grammar-design.md` — Final Core node set, grades, universes, Eq-as-inductive, validator ratchet status (§1.2).
- `2026-07-08-nat-int-erasure-design.md` — Nat→Int erasure rules, parametricity resolution, nat_rep assay (§2.2).
- `2026-07-09-infer-check-coherence-design.md` — check accepts every spelling infer accepts (§2.5).
- `2026-07-09-prim-delta-globals-design.md` — prim ops as registry-keyed delta-reducible globals; struct_eq amendment (§2.4).
- `2026-07-09-refinement-removal-design.md` — full SMT-refinement removal; GuardLint retained (§6.1).
- `2026-07-09-sigma-retirement-design.md` — primitive Σ retired to `@builtin(:sigma)` stdlib inductive; BEAM ABI preserved (§2.3).
- `2026-07-13-cure-evidential-systems-architecture.md` — the long-range evidential-systems doctrine, gates, and prohibitions (§11).
- `2026-07-14-trust-ledger-ph2-enforcement-design.md` — per-def axiom closure, allowlist, dev/release profiles (§7).
- `2026-07-14-typealias-forward-reference-limitation.md` — forward-referenced typealiases; resolved via header pre-pass (§10).
- `2026-07-15-core-walker-drift-audit.md` — fail-closed walker invariant, taxonomy, three critical fixes, refuted findings (§8).
- `2026-07-18-auto-lemma-proof-search-design.md` — `@lemma` proof search + positivity solver; Agda ambiguity discipline (§6.3).
- `2026-07-18-axiom-free-refinement-reflection-design.md` — boolean-reflection/Nat-bridge library, context saturation, deferred Int↔Nat axiom ledger (§6.4).
- `2026-07-18-elaborator-gaps-verified-status.md` — six-agent verification of gap statuses; K-bugs 1–2; E9 premise falsified (§9).
- `2026-07-18-first-class-holes-design.md` — holes as stuck neutrals with deterministic unique ids (§6.6).
- `2026-07-18-inductive-int-design.md` — inductive Int (FromNat/NegativeSuccessor) with audited reduce_int fold (§2.6).
- `2026-07-18-int-refinement-prelude-design.md` — IsTrue/Confirmed prelude + level-1/2 refinement sugar (§6.2).
- `2026-07-18-mutual-recursion-reduction-spec.md` — certify the whole SCC on mutual-group success (§5.2).
- `2026-07-18-open-elaborator-gaps-handoff.md` — scoped work list, unifying theme, priority order, discipline for open gaps (§9).
- `2026-07-18-verified-lia-reflection-design.md` — verified Farkas/LIA checker via computational reflection; solver stays untrusted (§6.5).
- `2026-07-22-certificate-generator-integration-design.md` — OTP-first
  semilinear-inclusion slice followed by the general verified checker,
  producer-neutral boundary, elaborator seam, strict external protocol,
  diagnostics, and IDE support (§6.5).
