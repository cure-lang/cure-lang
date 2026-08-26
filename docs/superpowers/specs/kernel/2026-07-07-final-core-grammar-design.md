# Final-Core Grammar (Wave 0)

**Date:** 2026-07-07
**Branch:** `feature/idris-parity`
**Status:** design — the Wave-0 deliverable. Specifies the *entire* end-state
Core term language up front (strategy decision 4). The kernel will not *produce*
all of this until the later waves land; the validator (§J) is written against the
whole grammar and flips each clause to hard-reject as its wave completes.

## Purpose

This is the target `Cure.Core.Term` taxonomy after the dependent-kernel cleanup —
the shape every wave converges on. It fills in the field reservations decided in
the grammar brainstorm and resolves the three open grammar forks (eliminator
form, primitives, equality). It supersedes the *shape* documented in
`lib/cure/core/term.ex`'s moduledoc; that moduledoc's claim that Core "carries no
implicits, holes, or erasure annotations … fully explicit and fully relevant" is
**revised** — Core stays hole/implicit-free, but it *does* carry a per-binder
**grade** (erasure + the reserved resource axes). Relevance becomes a *checked
property under the grade*, not a blanket invariant.

Companion documents (do not duplicate; this defers to them):
- Wave ordering and per-K scope: [`audit_categorised.md`](../audit_categorised.md).
- Cross-cutting execution frame: [`2026-07-07-dependent-kernel-cleanup-strategy-design.md`](2026-07-07-dependent-kernel-cleanup-strategy-design.md).
- Effects (deliberately **out** of Core): [`2026-07-07-sound-effect-discipline-design.md`](2026-07-07-sound-effect-discipline-design.md).

## Design principles (recap, load-bearing here)

1. **Idris/Agda-shaped, not Lean-shaped** (strategy decision 5): QTT-style
   multiplicities on binders; predicative cumulative universes;
   irrelevance-via-quantity-0. Lean is a *forgetful projection* target, never the
   native shape.
2. **Uniformly strict** (decision 3): one kernel, no permissive mode. No holes,
   no universal-subtype `Any`, no unproven obligations inside the TCB.
3. **Reserve the invasive fields now, keep everything else additive** (grammar
   triage): the only Wave-0 field reshapes are the grade record on binders,
   level-expressions + level-params, and qualified symbol ids. Every deferred
   language feature is either a new additive type-former, a conversion-algorithm
   upgrade, an elaborator/surface construct, or a new axis on the (extensible)
   grade record — none of which touches an existing node's arity a second time.

## §A. The final node taxonomy

Legend for **Change**: **keep** = unchanged; **reshape** = same role, new fields
(invasive — reserved in Wave 0); **delete** = removed, role re-expressed via
another node; **new** = added node.

| Final node | Current form | Change | K / wave |
|---|---|---|---|
| `{:type, level}` — `level` is a **level-expression** | `{:type, level}` (int, 0..2) | reshape | K7 |
| `{:var, k}` | same | keep | — |
| `{:pi, grade, dom, cod}` | `{:pi, dom, cod}` | reshape (+grade) | grade |
| `{:lam, grade, dom, body}` | `{:lam, dom, body}` | reshape (+grade) | grade |
| `{:app, f, a}` | same | keep | — |
| `{:sigma, grade, a, b}` | `{:sigma, a, b}` | reshape (+grade) | grade |
| `{:pair, a, b}` | same | keep | — |
| `{:fst, p}` / `{:snd, p}` | same | keep | — |
| `{:data, sym, params, indices}` — `sym` is a **qualified id** | `{:data, name, params, indices}` (atom) | reshape (id) | K12 |
| `{:ctor, sym, args}` — qualified id; params erased (§E) | `{:ctor, name, args}` (atom, flat) | reshape (id) | K6, K12 |
| `{:case, scrut, motive, branches}` — sole eliminator; sound index-refinement + coverage rule | same shape; branch ctor names become qualified ids | reshape (id) + checker rule | K5, K12 |
| `{:global, sym, levels}` — qualified id + level args | `{:global, name}` (atom) | reshape (id, levels) | K7, K12 |
| `{:int_type}` / `{:int_lit, n}` | same | keep | — |
| `{:float_type}` / `{:float_lit, f}` | same | keep | — |
| `{:eq, ty, a, b}` | present | **delete** → inductive `Eq` (§F) | K1 |
| `{:refl, a}` | present | **delete** → ctor `refl` (§F) | K1 |
| `{:rewrite, proof, motive, body}` | present | **delete** → `case`-sugar (§F) | K1 |
| `{:prim, op, args}` | present | **delete** → delta-reducible globals (§G) | K2 |
| `{:hole, _}` | leaks in | **excluded** — never in Core (§I) | K3 |
| `{:absurd}` | present as a Core node | **delete** → empty-`case` (§H) | K4 |

Net: **17 kept/reshaped nodes, 5 deleted nodes (`:eq`, `:refl`, `:rewrite`,
`:prim`, `:absurd`), 1 excluded (`:hole`).** No new node is added — every "new"
capability rides a reshaped field or an existing node. The taxonomy *shrinks*.

## §B. Grades — the reserved binder field

Every binding site (`:pi`, `:lam`, `:sigma`) carries one `Cure.Core.Grade`. This
is the single invasive reservation that unlocks erasure now (enforced), carries
linearity/affinity and security as already-present fields whose *enforcement*
lands in later waves (§B.2, §B.3), and leaves room for cost/uniqueness/graded
effects as future additive axes (§B.1) — all without a second re-thread of an
existing node's arity.

### B.1 The grade record (extensible)

```
%Cure.Core.Grade{
  usage:    Usage.t(),      # {0, ≤1, 1, ω}  — QTT multiplicity
  security: Security.t()    # element of a module-declared IFC lattice; default ⊥ (Public)
}
```

It is a **struct, not a tuple**: adding a future axis (uniqueness, cost/WCET, a
graded-effect axis) is a defaulted field addition — additive, no node-arity
change. This is the hedge that keeps four **Bucket-B features** (this document's
label for deferred features that ride an additive grammar change rather than a
node-arity reshape: linearity/affinity, uniqueness, cost/WCET, graded effects)
additive. A missing axis defaults to its most-permissive element (`usage: ω`,
`security: ⊥`), so un-annotated surface code elaborates to the unrestricted
grade and behaves as today.

### B.2 Usage — ordered semiring behind a module boundary

`Cure.Core.Usage` exposes the interface the kernel programs against, never the
raw carrier:

```
zero()            # 0     — erased / type-only
one()             # 1     — linear (reserved)
omega()           # ω     — unrestricted
add(a, b)         # contraction: two uses in different branches/positions
mul(a, b)         # composition: use under a binder of grade a
leq(a, b)         # sub-usage order for checking a value of grade a where b is required
relevant?(a)      # a ≠ 0  — participates at runtime
```

Carrier `{0, ≤1, 1, ω}` is fixed in the type but **only `{0, ω}` is enforced in
Wave 0** (the existing erasure relevance-check: a grade-0 binder must not appear
in a computationally-relevant position — return value, scrutinee, applied
function, present argument — per the erasure-relevance-check decision). `≤1`
(affine) and `1` (linear) are *accepted and carried* but their at-most/exactly
once checks are **stubs that pass** until the linear-types wave; the interface is
what makes turning them on additive. Semiring laws (`0·a = 0`, `1·a = a`,
distributivity) are the checked contract on any carrier the module ever grows to.

### B.3 Security — opt-in module-level IFC

`Cure.Core.Security` is a **bounded join-semilattice**, declarable per module,
defaulting to the trivial one-point lattice `{Public}` (`⊥ = Public`). Semantics
match the grammar decision:

- **Default off:** with the trivial lattice every grade's `security = ⊥`, all
  flow checks are vacuous no-ops, zero overhead.
- **Opt-in is contagious/sticky:** a module that declares a non-trivial lattice
  and labels a definition forces consumers to participate — the label rides the
  definition's type through the env, so a downstream module cannot silently
  discard it (it was "deemed important at definition time").
- **Enforcement:** the kernel rejects a flow that would move a value to a strictly
  *lower* security level (non-interference: no `High → Low`). The join tracks the
  least upper bound through elimination.
- **Declassification is explicit and audited:** the only downward move is a
  surface `declassify` form that elaborates to a marked, logged coercion; it is
  the one sanctioned hole in non-interference and is visible in the term.

Like usage, security enforcement is **carried in Wave 0, enforced when the IFC
wave lands**; the trivial default means shipping it early costs nothing.

### B.4 Kernel obligations for grades

- Well-formedness: the grade on every binder is a valid `Grade` (each axis a
  valid element of its algebra).
- Usage: on checking `{:lam, g, A, b}` against `{:pi, g', A, B}`, require
  `Usage.leq(g.usage, g'.usage)` and check the body's variable usage against `g`.
- Grade-0 relevance: the existing erasure check, generalized to read the binder's
  `usage` instead of a separate `{0,ω}` side-table.
- Security flow: LUB tracking + no-downward-flow, active only under a non-trivial
  lattice.

## §C. Universes (K7)

`{:type, level}` where `level` is a **level-expression**, not a bounded int:

```
level ::= lzero
        | lsucc level
        | lmax level level          # predicative max — NOT Lean's imax
        | lvar α                    # a bound universe parameter
```

- **Predicative & cumulative:** `Type ℓ : Type (lsucc ℓ)`; `lmax` for the
  universe of a `:pi`/`:sigma` (`Type (lmax ℓ₁ ℓ₂)`). **No `imax`, no
  impredicative `Prop`** (decision 5; a **Bucket-C** decline — this document's
  label for a feature considered and deliberately declined rather than
  deferred). Irrelevance is grade-0, not a `Prop` sort.
- **Level polymorphism:** globals and data families may bind universe
  parameters. `{:global, sym, levels}` carries the list of level-expression
  **arguments** instantiating those parameters at the use site; the binding
  parameters live in the global's stored signature.
- **Remove the `@ceiling 2` cap** — the hierarchy is unbounded. `term?/1`'s
  `level <= @ceiling` check is replaced by well-formedness of the level-expression
  (all `lvar`s in scope).

## §D. Symbols & identity (K12)

`:global`, `:data`, `:ctor`, and `:case` branch heads reference a **qualified
symbol id**, not a bare atom:

```
Cure.Core.Sym  ≈  %{module: [atom], name: atom}   # or an interned integer id + table
```

- **Kill `String.to_atom/1`** in `from_external/1` (unbounded atom interning =
  table-exhaustion + collision risk). Decode into `Sym` values, interned through a
  bounded symbol table.
- Identity is structural on `Sym`, so two distinct modules' `foo` never collide,
  and constructor/data resolution is unambiguous — a property signature-driven
  constructor checking in §E depends on for soundness in the final grammar.
  (`audit_categorised.md`'s Wave-2 list happens to order K6 before K12; whether
  that intra-wave ordering needs to flip, or K6 can land first with the interim
  atom-collision risk accepted, is for the sequencing plan to resolve, not this
  document.)
- Serialization (§K) encodes `Sym` explicitly (module path + name), keeping the
  C2 external form total and collision-free.

## §E. Eliminator & recursion — the eliminator-form fork resolved

**Decision: the sole native eliminator is the motive-carrying dependent
`{:case, scrut, motive, branches}` (a single split, non-recursive). Recursion is
definitional — a global whose body references itself (or a mutual group),
gated by the existing size-change termination certificate. Lean-style recursors
are the *encoder's* lowering target, never a native Core node.**

Rationale:

- **Consistency with decision 5.** Case-tree + a separate termination checker is
  the Agda/Idris shape; recursors-with-no-termination-checker is the Lean shape.
  We committed to the former.
- **Reuse of landed infrastructure.** The size-change termination certificate
  (`certificate.ex`, the #13/#14 work) already validates definitional recursion.
  A recursor-based core would *discard* that and re-encode every recursion as a
  recursor application — strictly more work for a poorer fit with erasure/usage.
- **Grades live naturally on `case` + definitional recursion.** Threading
  multiplicities through motive-carrying case branches is direct; through
  generated recursors it is indirect.

There is **no `fix` term node** — recursion is not a term former but a property
of the global environment (self/mutual reference), exactly as today. `:case` is
the only elimination node; `:fst`/`:snd` remain the sigma projections.

**Reframing the recent Lean-recursor commits** (`Add Lean-style {mutual,indexed}
recursor shape`, `Align recursor eliminator levels with Lean`, `Route dependent
checking through Lean backend`): that recursor-generation logic is repositioned
as **`Cure.Lean.ModuleEncoder` lowering** — Lean's core *requires* recursors, so
synthesizing them belongs in the translator (outside the TCB, decision 6), fed by
the native `case` + definitional recursion. The work is not discarded; it moves
to the correct side of the fork.

### E.1 Constructor values (K6)

**Decision: flat spine `{:ctor, sym, args}`, split by the signature — Lean's
kernel representation.** `sym` (§D) gives the constructor **family identity** and
resolves to its stored signature (a graded telescope naming which leading
arguments are the data **parameters** and which are the **fields**; the family's
**indices** are *not* stored — they are computed from the field values via the
constructor's return type). The kernel splits `args` using that signature. The
data **parameters ride the spine at grade 0** — present so a constructor is
checkable in inference position and re-checkable by the independent verifier (§K),
erased at runtime (zero footprint). This is exactly how Lean's kernel stores
constructor applications (params in the spine, `nparams`/`nfields` in the
environment); Agda goes further and drops params from the value entirely — we keep
Lean's form because it keeps synthesis signature-local and makes the Lean
projection (§L) an identity on this node.

Why flat over a structural `{:ctor, sym, params, fields}`: the signature is
already the sole authority on per-argument grades and on the param/field boundary,
and must be consulted to type the constructor at all. Storing the split *again* in
the value would duplicate derivable data — a consistency invariant the validator
would then have to police — and would re-tuple the node the moment a new argument
category appears. A flat spine keeps the de Bruijn operations one-liners, keeps
the trusted term minimal, and makes any future argument category a *signature*
change rather than a *grammar* change (the reserve-fields-keep-the-rest-additive
discipline). The one cost — iota-reduction consulting the signature to drop the
params — is the cost Lean and Agda both accept, and the environment is always in
hand during reduction. K6's "flat args / lost constructor identity" is resolved by
the `sym` identity plus signature-driven checking, not by re-structuring the
value.

### E.2 Index refinement & coverage (K5) — the soundness-critical eliminator rule

`:case` stays structurally `{ctor, arity, body}` (**no new payload field**); the
*checking rule* is strengthened to the sound dependent-match discipline. For each
branch: instantiate the motive at the constructor's index expressions, **unify**
those against the scrutinee's actual indices, and check the body under the
resulting refinement (solved equations substituted into context and goal).
Constructors whose indices fail to unify are **impossible** and rejected/omitted;
every possible constructor must be **covered**. This closes the "branch-skipping
index unifier" divergence — today's eliminator skips the refinement, which is
unsound (it accepts branches under an unrefined context).

K5 is a **kernel typing rule**, not a structural-shape clause, so it is enforced
by the case-checker rather than the grammar validator (§J). It reuses the landed
index-unification machinery (`unify_indices`, the Agda Cycle rule, size-change).
The audit splits it K5a (acute unifier-soundness fixes) / K5b (canonical
`Eq.rec`/transport, joined with K1b); this grammar treats both as the one sound
`:case` rule.

## §F. Equality — inductive `Eq`, transport-as-sugar (K1)

Delete `{:eq}`, `{:refl}`, `{:rewrite}`. Equality becomes an ordinary inductive
family in the global environment — **the inductive `Eq`/`refl` already exist in
`builtins.ex`**, so K1 re-points to them rather than creating them (the
identity-type-as-inductive thread, task #90):

```
Eq   : (A : Type ℓ) → A → A → Type ℓ
refl : (A : Type ℓ) (a : A) → Eq A a a
```

- `{:eq, T, a, b}` ⤳ `{:data, Eq-sym, [T], [a, b]}`.
- `{:refl, a}` ⤳ `{:ctor, refl-sym, [a]}` (with `A` erased per §E).
- `{:rewrite, …}` / surface `transport` / `subst` / `J` ⤳ **elaborator sugar**
  producing a `{:case}` on the equality proof with the appropriate motive. No
  transport node survives in Core.
- **K/UIP is adopted** (decision 5, task #90): case on `refl` may collapse the
  index — this is what forecloses cubical/HoTT (Bucket-C) and is the deliberate
  trade for a simpler conversion. The `K`/`J` eliminators are the two
  derived-in-surface forms; both bottom out in `:case`.

## §G. Primitives — delta-reducible globals, native int/float (K2)

Delete `{:prim, op, args}`. Two categories replace it:

1. **Primitive types & literals stay native:** `{:int_type}`, `{:int_lit, n}`,
   `{:float_type}`, `{:float_lit, f}` remain first-class term nodes. These are the
   machine-int/float builtins the ESP32 story depends on (the builtin-inductive /
   native-int foundation; `Nat` erases to native `Int`). They are **not**
   inductives.
2. **Primitive operations become typed global constants** with a trusted
   **delta-rule** reducer: e.g. `Int.add : Int → Int → Int` is a `{:global, …}`
   whose reduction fires — inside the kernel's normalizer — only on
   fully-applied literal arguments, computing the result. Applied via ordinary
   `{:app}`; no bespoke node. The delta table is a small, fixed, audited part of
   the reducer's TCB.

`Bool` and all other datatypes are real inductive families (already true) — the
primitive surface is exactly {int/float types + literals + the fixed delta-op
globals}.

### G.1 The delta table is a named TCB member — two rules keep it sound

The delta table is trusted because the **conversion checker computes with it**: to
see `Vec A (2 + 3) ≡ Vec A 5` the normalizer must actually evaluate `2 + 3`. A
wrong result there is a soundness hole. This is the standard, universally-accepted
cost of native numbers (Coq `Int63`/`PrimFloat`, Agda built-in `Nat` via GMP,
Lean `Nat`/`Int` literals all do exactly this). It is contained by keeping the
table small, fixed, and **enumerated as an explicit TCB member under K11** (the
trusted-boundary catalog) rather than an implicit one. Two rules:

1. **Totality — partial ops must not reduce when undefined.** A delta rule may
   never get stuck mid-normalization or raise. `Int.div`/`Int.mod` applied to a
   **zero** divisor literal simply **do not fire** — the application stays a
   neutral term and conversion compares it syntactically. Normalization stays
   total, and the kernel never invents a value for `x / 0`. (Making `div` take a
   `NonZero` proof is a *stdlib* choice layered on top; the table only needs the
   non-reducing fallback for soundness.)

2. **Model AtomVM's integer semantics — which are BEAM-faithful, so this is
   easy.** AtomVM integers are tagged word-immediates (28-bit on the 32-bit ESP32,
   60-bit on 64-bit hosts) that **promote on overflow, never wrap**: immediate →
   boxed `int64` → multi-precision `IntN` (sign-magnitude, ≤256-bit), confirmed in
   `term.h`/`intn.h`/`bif.c`. Therefore the table may compute with **Elixir's
   native arbitrary-precision integers** and agree with the device exactly for
   every value ≤ 2²⁵⁶ — i.e. every integer a type could realistically hold (vector
   lengths, `Fin` bounds, dimensions never approach even 2⁶⁰). The sole divergence
   is above AtomVM's `IntN` ceiling, where the device errors on overflow while the
   kernel's Elixir ints continue; this is unreachable for type-level values and is
   documented as such, not designed around. (Version footnote: the 256-bit `IntN`
   is a ~0.7 feature; a 0.6.x device caps lower but is still promote-not-wrap —
   same unreachable-ceiling footnote.) Floats follow the analogous rule: model
   AtomVM/IEEE-754 double semantics, and leave `NaN`/division-by-zero non-reducing
   rather than producing a value.

The precise op set, their signatures, and the per-op reducers are pinned down in
the K2 wave spec; this section fixes only the two soundness rules and the TCB
registration.

## §H. Empty & absurd (K4)

`{:absurd}` is a current Core node (K4). Delete it. Ex-falso is instead the
elimination of a **provably-uninhabited scrutinee** via
`{:case, scrut, motive, []}` — a `case` with an empty branch list. Per §E.2's
coverage rule, the kernel accepts an empty branch list whenever every
constructor of the scrutinee's family is either absent (a literally-empty family
like `Empty`) **or** ruled impossible by index-unification failure at the
scrutinee's actual indices — the standard Agda/Idris index-contradiction
discipline (e.g. a proof of `Eq Bool true false`: `Eq` has one constructor,
`refl`, but `refl`'s index requirement `x = y` can never unify with `true`/
`false`, so the one constructor is impossible and the empty case is accepted
even though the family is not literally empty). Otherwise an empty branch list
is a coverage error (§E.2). This removes the node and makes "impossible" a
derived, checked fact rather than a trusted marker. (The audit's K4 also allows
an *elaborator-only* marker; we take the stricter line — absurd never appears in
checked Core, only empty-`case` does.)

## §I. Explicitly excluded from Core (with where they live instead)

- **Holes** `{:hole, _}` (K3) — never in a checked Core term. They exist only in
  the elaborator's open-term representation; the validator hard-rejects any
  residual hole. `closed?/1`'s hole mention is dropped.
- **Implicits** — resolved by the elaborator before Core; Core is fully explicit
  (unchanged invariant).
- **Effects** — a *surface* discipline erased before Core (the effect spec); Core
  never sees an effect. No arrow-effect slot (Fork closed: "no").
- **`Any` as a universal subtype / implicit fallback** (K14) — banned (decision
  3). `Any` survives only as an explicit opaque dynamic type with a single
  checked-cast elimination at a declared FFI boundary; that is a normal global
  type, not a conversion hole.
- **Deleted term nodes** `{:eq}` `{:refl}` `{:rewrite}` `{:prim}` `{:absurd}` —
  re-expressed per §F/§G/§H.

## §J. The Wave-0 validator — the executable checklist

`Cure.Core.Validator` checks a term against the **full final grammar** above.
Each grammar commitment is a named clause with a mode:

- `:off` — not yet checked (legacy form still produced upstream).
- `:warn` — legacy form detected; logged, not rejected.
- `:reject` — hard error; the clause is enforced.

A clause is authored at `:warn` in Wave 0 — or `:off` where its target shape does
not yet exist in the grammar, so its predicate would otherwise fire on every
current node — and **flipped to `:reject` as its wave lands** (decision 4). "Wave N
done" ≡ its clauses are `:reject` and the kernel still produces terms that pass
them, with Antigen green + fixtures updated. No clause is `:reject` in Wave 0
itself: K11a builds the scaffold and runs it as pure instrumentation (warn/off);
the reject *mechanism* is exercised by config-override, not by enabling any clause.

| Validator clause | Enforces | Flips at |
|---|---|---|
| `grade_on_binders` | every `:pi`/`:lam`/`:sigma` carries a well-formed `Grade` | grade wave — when the binder grade field lands (`:off` in Wave 0: current binders carry no grade, so the predicate would fire on every node) |
| `usage_relevance` | grade-0 binders absent from relevant positions; `{0,ω}` only | grade wave (affine/linear stay `:off`) |
| `no_eq_node` | no `{:eq}`/`{:refl}`; `Eq` is `:data`/`:ctor` | **K1a — LANDED**: `:reject` in `release_config` (0e75a13). Both are dead-producers (inductive Eq via `mk_eq`; inductive refl via surface refl + `symmetry_proof` + `bridge_step` f3b0e73, unblocked by K6 param-in-spine b355753). Enforced on every program's final Core (`program.ex:272`) ⇒ green suite proves absence. Kernel/serialize keep *defensive* handling (Phase C) |
| `no_rewrite_node` | no `{:rewrite}`; transport is single-branch `:case` | **Phase B DECLINED (2026-07-08)**: stays `:warn` as an accepted Core-representation divergence. Surface rewrite is already Idris-faithful via `rewrite_plan`; retiring the sound `{:rewrite}` node buys no soundness and two empirical attempts drifted parity (`frp01` computed endpoints; `rw03` no-occurrence more-permissive; bridge-case regression `std/proof.cure`). Per design-fork-prose-preference (just semantics ⇒ lower-risk option). See audit K1 for the full proof |
| `no_prim_node` | no `{:prim}`; primitive ops are delta-globals | K2 wave |
| `no_hole` | no `{:hole, _}` anywhere | **K3 — LANDED**: `:reject` in `release_config/0` (release/emit boundary); dev-time `check_def` stays `:warn` so deferred `?name` bodies still typecheck (Option B). Enforced at both release exits (`Emit.reject_holes`, `Program.check_codegen_ready`) on the *pre-erase* term |
| `qualified_syms` | `:global`/`:data`/`:ctor`/branch heads use `Sym`, not atoms | K12 wave |
| `ctor_signature` | `:ctor` args check against resolved signature; params at grade 0 | K6 wave |
| `case_coverage` | branch ctor set exactly covers the family; arities match signature | K5 wave (structural part) |
| `level_expr` | `{:type, ℓ}` is a well-formed level-expression; globals carry level args; no ceiling | K7 wave |
| `no_absurd_node` | no `{:absurd}`; ex-falso only via empty-`case` (structural absence of branches — coverage per §E.2/§H decides when that's valid) | **K4 — LANDED**: `:reject` in `release_config` (16718f6). Kernel `check_coverage` accepts provably-`:impossible` omissions (35da361); elaborator omits impossible branches instead of `{:absurd}` bodies (34aecae). Node gone from grammar (`Term.term?`), producers, and final Core; kernel-infer/serialize keep *defensive* handling (infer has no catch-all ⇒ its clause is load-bearing for totality) |
| `no_legacy_reducer` | normal forms produced by the clean reducer only | K10 wave |

The validator checks **structural shape**, not typing. The soundness-critical
part of K5 — sound index unification and refinement per branch (§E.2) — is a
*typing* rule enforced by the kernel's case-checker, not a validator clause;
`case_coverage` above only checks the structural coverage/arity shape. Building
this validator scaffold is itself the audit's **K11a** step (Final-Core grammar +
validator), the first item in the tackle order.

The validator is thus the single source of truth for "how far the cleanup has
progressed": at any commit it names precisely which constructs remain in legacy
form.

### §J.1 Terminal state — Core cleanup complete (2026-07-08)

All **soundness-bearing** validator clauses are `:reject`; every clause still at
`:warn`/`:off` is so for a recorded, principled reason (out-of-scope, declined-with-
proof, kernel-enforced, or a design-gated feature) — none is an open soundness hole.

| Clause | State | Why not `:reject` |
|---|---|---|
| `no_eq_node` | **`:reject`** | landed (K1a, 0e75a13) |
| `no_hole` | **`:reject`** | landed (K3) |
| `no_absurd_node` | **`:reject`** | landed (K4, 16718f6) |
| `no_rewrite_node` | `:warn` | Phase B declined-with-proof — the sound `{:rewrite}` transport is a deliberate representation choice (K1) |
| `no_prim_node` | **`:reject`** | landed (K2, 2026-07-09 prim-delta-globals): `{:prim}`/`{:nprim}` stripped; arithmetic is registry-keyed builtin-op GLOBALS with certified-δ literal acceleration. (Historical note: this row previously read `:off` while validator.ex had `:warn` — a recorded doc/code drift, now moot. The earlier decline-with-proof was re-opened on the parity criterion — see `audit_categorised.md` §K2 pointer and spec `2026-07-09-prim-delta-globals-design.md` §0.) |
| `ctor_signature` | partial | K6 soundness (params-in-spine, 545/599, b355753) landed; the grade-coupled remainder rides the out-of-scope grade wave |
| `case_coverage` | kernel | structural coverage + the soundness-critical per-branch index unification are enforced by the kernel case-checker (K5a landed), not this structural clause |
| `usage_relevance` | kernel | the `{0,ω}` erasure-relevance check is enforced by the kernel (returned / scrutinised / applied erased binder rejected), not structurally |
| `grade_on_binders`, affine/linear `usage_relevance` | `:off` | **out of scope** — QTT multiplicity-1/linear machinery |
| `qualified_syms` | `:off` | K12 qualified-`Sym` — a large representation FEATURE, design-gated (slices 1–2 decode-hardening landed) |
| `level_expr` | `:off` | K7 universe-level *polymorphism* — a large parity FEATURE (universe SOUNDNESS is already met: the kernel is predicatively stratified, `Type₀ : Type₁`, no `Type:Type`) |
| `no_legacy_reducer` | `:off` | K10 legacy-system deletion — cleanup, not soundness (the clean reducer is already the sole normal-form producer) |

Beyond the validator clauses, the E-layer received a **declaration-hygiene sweep**
closing eight silent-overwrite / shadowing holes the grammar validator does not
cover: duplicate top-level def / type / constructor (per module — cross-module
sharing is legitimate namespacing, resolved by the rekey layer), duplicate function
param / record field / family index / GADT-ctor named domain, and non-linear
constructor patterns. All six dependent-soundness axes were then independently
probed and confirmed sound: telescope linearity, strict positivity, match coverage,
termination (partial-by-default like Idris, but δ never unfolds a non-terminating
global), erasure relevance, and universe consistency.

**Net:** the Core is clean to Idris-2 parity minus linear types **on the soundness
dimension**. What remains are faithfulness-only representation choices (declined with
recorded proof) and large parity *features* (canonical `Eq` transport, universe-level
polymorphism, qualified `Sym`) that each need their own design — the deferred "gaps".

## §K. Serialization / C2 impact

`to_external/1` + `from_external/1` (the JSON-able C2 encoding for an independent
re-checker) grow in lockstep with §A:

- Binders emit their `Grade` (both axes, with defaults elided as permissive).
- `:type` emits a level-expression tree; globals emit level args.
- `:global`/`:data`/`:ctor` emit `Sym` (module path + name), **replacing
  `String.to_atom`** with symbol-table interning on decode.
- Deleted nodes lose their encodings; `Eq`/`refl`/absurd round-trip through the
  `:data`/`:ctor`/`:case` encodings, and former `:prim` operations round-trip
  through the ordinary `:global` encoding (§G) — no new encoding case needed for
  any of the four (`:rewrite` never reaches Core, so it needs none).

The encoding stays total and reversible (no PIDs/refs/closures in Core), so the
independent-checker contract holds across the reshape.

## §L. Lean projection (forgetful) — consistency note

`ModuleEncoder` lowers Final Core → Lean Core as a **forgetful map** (decision 6):
erase grades (drop usage + security), lower `:case` + definitional recursion to
Lean **recursors** (§E), map the inductive `Eq` to Lean's `Eq`, map delta-globals
to Lean primitives or `@[extern]` shims, and map the predicative universe
hierarchy into Lean's (richer) one. lean4lean then witnesses the **dependent
skeleton only** — never the quantitative layer, which is the Elixir kernel's sole
permanent responsibility. Each wave that deletes a divergence is a node the
encoder no longer has to special-case; the two forks converge as a side effect.

## Non-goals (this document)

- Not the implementation plan — that is the next artifact (writing-plans), which
  sequences the validator clause flips against the audit's wave order.
- Not a re-specification of per-wave scope — that stays in `audit_categorised.md`.
- No Bucket-B feature is designed here; §B.1's extensible record and §C's open
  level-expression are the only forward-compatibility hooks, and both are
  zero-cost today.
