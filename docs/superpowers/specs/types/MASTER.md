# Cure Type-System Specifications — Master Condensation

**Date:** 2026-07-21

**Scope.** This document condenses every specification in
`docs/superpowers/specs/types/` into one theme-organized reference intended to
replace reading the individual files: the dependent-types foundation, the
Agda-style universe-polymorphism replacement for the fixed ceiling, QTT
grades, indexed families and dependent pattern matching, the consolidated
algebraic-data-type model (with anonymous unions, primitive declarations,
constructor qualification, length-indexed binaries), typeclass/dictionary/
coherence machinery and its type-directed search engine, the staged
overloading–labels–operators–fixity family, and record field-lens deriving.
Locked decisions, invariants, status markers, and supersessions are preserved;
already-executed implementation plans are dropped. Where documents disagree,
the newest approved document governs (per the folder README).

---

## 1. Dependent-types foundation

*Source: 2026-06-30-cure-dependent-types-frp-design.md (foundational; its
fixed-universe sections 3/4.3 are SUPERSEDED by §2 below).*

Motivation: replace Cure's previously faked dependent types with a real
checked core; north-star validation target is a port of Sculthorpe & Nilsson's
Safe Functional Reactive Programming (ICFP'09) with `SF`-style indexed signal
functions.

**Locked decisions:**

- **Theory:** a bounded, Agda-subset intensional MLTT. Indexed inductive
  families with computed indices; dependent Π with implicit erased arguments;
  Σ; dependent pattern matching; typed holes.
- **Equality:** definitional equality first, plus a minimal sound
  propositional `Eq`/`refl`/`rewrite` (`refl` accepted only when both sides
  reduce equal). (A later initiative retires primitive Eq for an inductive
  identity type; that lives outside this folder.)
- **Evaluator:** a real NbE (normalization-by-evaluation) evaluator drives
  conversion (β/ι/δ-certified-only/η).
- **Universes:** `Type : Type` REJECTED — Girard-paradox inconsistency plus a
  non-normalizing theory makes checking undecidable. Original design fixed
  Type₀ : Type₁ : Type₂ with cumulativity and inferred levels; superseded by
  the universe-polymorphism spec (§2).
- **Erasure:** checked `{0, ω}` quantities (later extended to full QTT, §3).
  Linearity deliberately omitted at first: BEAM blunts its payoff (immutable
  data, per-process GC, message copying); `fsm`/`actor` approximates sessions.
  Erasure criterion: a 0-graded binder may never be returned, passed in a
  present position, scrutinised, or applied.
- **Totality:** targeted, not global. Type-level and `@total` functions must
  certify termination (hard error otherwise); totality certificates gate
  δ-unfolding so conversion always terminates. The kernel re-runs the totality
  decision procedure itself — the elaborator only contributes the closure walk.
- **Architecture:** trusted small kernel (`lib/cure/core/**`, the TCB) +
  untrusted elaborator (de Bruijn criterion / LCF discipline). Everything the
  elaborator produces is re-checked by the kernel.
- **Refinements/Z3:** orthogonal; later removed from the trust story entirely
  (Z3 out of TCB; refinement types removed).
- **Kernel-trust roadmap:** Elixir bootstrap (spec + serializable Core +
  conformance corpus) → Cure self-hosted checker differentially tested against
  the Elixir oracle → verified metatheory.
- **Reference languages:** Idris2 for architecture/totality/patterns/holes;
  Lean4 for kernel discipline and universes (not Idris's permissive
  universes); Agda for LHS unification/coverage (not Idris's QTT multiplicity
  surface wholesale).

## 2. Universes — Agda-style predicative universe polymorphism

*Source: 2026-07-20-agda-style-universe-polymorphism-design.md (authoritative;
SUPERSEDES the fixed ceiling in the FRP design §§3/4.3, the Sigma-retirement
level-0 haircut, `Type2`-is-max tests/comments, and Antigen's
`:family_ceiling`/`:universe_ceiling` obligations).*

**Decision:** replace `Type0 : Type1 : Type2` (ceiling 2) with an infinite,
predicative, universe-polymorphic hierarchy `Type(l) : Type(universe_succ(l))`.
Levels are compile-time values of primitive `UniverseLevel` with
`universe_zero` / `universe_succ` / `universe_max`. Cumulativity is retained
and mandatory (Agda makes it optional). No `Type : Type`; no ceiling;
level-rigid quantification is classified by a `TypeLimit(n)` (Setω-style)
hierarchy. This is a kernel change: checked Core contains explicit canonical
levels, no level metavariables, no unverified universe claims.

**Basis:** derived from the local Agda checkout (`7273757e5e`), not a surface
summary. Adopted: canonical maximum-plus normal form
`max(c, a₁+k₁, …, aₙ+kₙ)` (Agda's `Level'`/`levelMax`), which decides the
level laws (commutativity/idempotence/associativity,
succ-distributes-over-max, `max(a, succ(a)) = succ(a)`, zero neutrality)
directly; univSort/funSort/piSort separation; least-upper-bound solving for
underconstrained metas; complete erasure of levels. NOT adopted: `Prop`,
`SSet`, cubical/size/lock universes, `--type-in-type`, `--omega-in-omega`,
polymorphic limit levels, level rewrite rules, runtime reflection, pattern
matching/recursion on `UniverseLevel`, auto-generalization of undeclared
identifiers.

**Surface:** `Type` still means level zero (existing `{a: Type}` code is NOT
silently reinterpreted as polymorphic — API stability); `Type(l)` takes a
`UniverseLevel` term; closed spellings `TypeN` store a constant (never N
successor nodes); `TypeLimitN`. Polymorphism is explicit at declaration sites
(`{l: UniverseLevel}`); use-site levels are inferred like other erased
implicits.

**Core:** `sort_index ::= {:finite, level_nf} | {:omega, n}`; new terms
`{:level_type}`, `{:level_value, nf}`, `{:type, sort_index}`. Level atoms are
quoted neutral Core terms; EVERY generic Core walker (shift/subst, scope,
occurs, relevance, totality closure, serialization/hashing, printing,
validator, macro walkers, Antigen) must descend into level atoms — treating a
level as an inert leaf is a soundness bug (scope escape). The kernel rejects
any Core containing a meta marker.

**Sorting:** `Type(u) : Type(universe_succ(u))`; `TypeLimit(n) :
TypeLimit(n+1)`; non-dependent Π sorts at the join; a Π whose codomain sort
rigidly mentions the binder's level sorts at `Limit(0)` (classifies
`(l: UniverseLevel) -> Type(l) : TypeLimit`; not general impredicativity).
Cumulativity is identity-only subsumption (`U(a) <= U(b)` iff `a <= b`;
`U(_) <= Limit(n)` always; `Limit(_) <= U(_)` never), decided by the kernel,
never asserted by the elaborator; definitional `vtype` equality uses
sort-index equality, NOT cumulativity. Ordering `a <= b` :=
`universe_max(a,b) == b`, complete for the maximum-plus language.

**Elaborator:** dedicated `%LevelMeta{}` (never unified with term metas);
constraint worklist; least-solution assignment from accumulated lower bounds;
unconstrained use-site metas default to `universe_zero`; defaulting only at
declaration/application boundaries, never in the kernel; the old
retry-levels-0..2 loop is deleted. Family result sort = constructor-field
least upper bound; field rule: `A : sA` admissible iff `sA <= U(d)` (a stored
`T : Type(l)` field needs `succ(l) <= d`).

**Erasure:** every `UniverseLevel` binder forced to grade 0 (marking one
present rejected); relevance checker rejects runtime level use; after erasure
no level values/operations survive and specialization at different levels is
byte-equivalent. Closed levels are arbitrary-precision (avoids Agda's
historical Int overflow).

**Stdlib and migration:** `List`/`Option`/`Sigma`/`Equivalent` (and audited
others) become universe-polymorphic; FFI-bound/runtime-limited APIs stay
explicitly small — never generalize an API merely to make a test pass.
Serialization version bumps; every cache/hash containing Core (artifacts,
certificates, interfaces, incremental hashes, Antigen corpus) must include the
universe representation version. Phased plan U0–U7 with per-phase gates;
completion requires `Type : Type` and `TypeLimit : TypeLimit` unrepresentable,
single polymorphic definitions working at arbitrary levels, and Antigen
sensitivity to weakened level equality/ordering/scope/limit rules.

## 3. QTT grades

*Source: 2026-07-10-qtt-grades-plan.md — **STATUS: COMPLETE & CLOSED
2026-07-11** (kept for its settled decisions; do not relitigate).*

Full quantitative type theory grades `{0, 1, affine, ω}` on Core binders
(Idris ZeroOneOmega as authority). Settled decisions:

1. Grade is the FIRST field of graded formers (`{:pi, g, dom, cod}` etc.).
2. ONE canonical spelling per node — graded/ungraded tuples never coexist.
3. Grades are opaque behind `Cure.Core.Grade`
   (add/mul/admits?/leq/erased?/present?/restricted?).
4. Conv compares grades by EQUALITY, never by preorder — `leq` belongs to the
   usage check only.
5. The usage check stays OUT of the kernel (E-layer `relevance.ex`): position
   check (erased binder used relevantly) + semiring usage check
   (`Grade.leq(used, declared)`).
6. `:let` is graded.
7. Default grade `:unrestricted` (ω), written by omission only.
8. `:lam` IS graded — inner-λ linear binders would otherwise be invisible to
   the usage check (soundness, not convenience).

Semantics: closures scale outer usage by ω; match branches combine by
per-branch agreement, grade-aware (an affine binder may be dropped in one
branch and used in another — deliberately more permissive than Idris). Surface:
grades are decorators before the complete binder (`@linear c : Chan(Cmd)`); numeral spellings impossible
(collide with literal types/holes); a graded `let` must produce a real `:let`
Core node or error `{:graded_let_needs_annotation}`; graded destructuring is a
parse error. Stored Π types are rebuilt from the demoted quantity vector and a
`Kernel.check` λ-vs-Π assertion makes ctor quantities a verified mirror.

Recorded trap: after the `:present` → `:unrestricted` rename, `q == :present`-
shaped equality predicates silently dropped `:linear`/`:affine` in Erase, Emit,
Relevance, and extern-arity checks — always route through `Grade.present?/1`
and grep for the OLD predicate's shape after taxonomy renames.

Deferred to future specs: surface grades on λ and constructor fields (re-arms
a known un-join soundness landmine — `elaborate_lambda` currently hardcodes ω);
quantities-as-pure-projection refactor.

## 4. Indexed families and dependent pattern matching

### 4.1 Parameter/index split (approved)

*Source: 2026-07-02-param-index-split-design.md.*

Fixes the design error of conflating parameters with indices. Surface:
`type Vector(a: Type) indices (n: Nat)` + indented constructor block; the
`indices` clause discriminates from `=` (ordinary ADT); parameter-free indexed
form `type Length indices (n: Nat)` allowed. Invariants: parameters are
uniform across constructors and NEVER refined/unified (non-uniform restatement
rejected as `non_uniform_parameter`, matching Agda); `{:vdata}` carries
`params ++ indices` split by `param_count`; motive and branch unifier range
over indices only; motive arity = index_arity + 1; `param_count == 0` is
behaviorally identical to the old form (backward compatible). Future/out of
scope: parameter inference when omitted; GADT syntax for param-only ADTs.

### 4.2 Dependent-match surface: impossible branches (approved)

*Source: 2026-07-02-dependent-match-surface-design.md.*

Surfaces kernel index unification. Exactly one TCB wrapper —
`branch_unify(ctx, dname, cname, scrut_indices) :: {:solved, subst} | :trivial
| :impossible` — plus one always-fails kernel clause: `infer(_ctx, {:absurd})
-> {:error, :absurd_in_reachable_position}`. `{:absurd}` chosen over reusing
`{:hole,_}` for defense-in-depth: the kernel can never accept it, so a buggy
elaborator marking a reachable branch impossible still fails closed. Surface:
omit provably-impossible branches, or write `pattern -> impossible`
(soft-keyword recognition). Elaborator partitions branches into
matched / explicitly-impossible / omitted; errors `:missing_branch`,
`:reachable_impossible`, `{:duplicate_branch, cname}`, plus foreign/unknown
constructor validation. Branch de Bruijn frame is `ctor-args ++ outer` (no
params segment). Refinement completeness is scoped to verbatim reuse of the
scrutinee's compound index term in the result type; the bare-inner-variable
case (result `Vec a m` from scrutinee `Vec a (S m)`) is an explicit NON-goal
(constructor inversion is partial; needs with-abstraction, later subsumed by
§4.3). Kernel coverage checking is unchanged — the elaborator always emits the
full constructor set.

### 4.3 Lean-shape general dependent matching (approved)

*Source: 2026-07-02-lean-shape-matching-design.md.*

One unification-driven generalizing match subsuming value-abstraction `with`,
eq-transport with-proof, and index-inversion rematch. FRP crux: matching
`SF (as ++ bs)`-style stuck-application indices requires CARRIED `Eq`
equations discharged by associativity/identity rewrites — a Cure-specific
automation of Lean's opt-in `match h : e with` idiom, NOT inherited Lean
behavior (Lean's discriminant refinement handles only `x=t`/`t=x`/ctor=ctor
and deliberately refuses stuck applications; reviewer directive: re-check
actual Lean source at every review pass). Motive generalization composes
dependency-based context reversion with syntactic occurrence-abstraction. The
five-rule first-order index unifier is already landed (solution both
directions, injectivity, conflict ⇒ `:impossible`, occurs-check ⇒
`:undecided` — NEVER `:impossible`: "uncertainty is never impossible",
deletion). Phase 5 (signature-aware `Quote.reify`, TCB, reach-pinned
`reify_split_gap`) may be pulled forward if earlier phases hit its wall.
Gaps: the kernel has only homogeneous Eq — eq-transport on indexed
scrutinees needs HEq (its own HARD-STOP gate) or stays scoped to non-indexed;
the rw07 bridge-lemma technique is proven only for a single reducible inner
occurrence — multi-occurrence discharge is unproven reach gating the final
phase.

### 4.4 Relevant implicit constructor indices (LANDED `47b0cacc`)

*Source: 2026-07-18-relevant-implicit-ctor-index-design.md.*

Idris's fourth quadrant `{k : Nat}` — implicit AND relevant (ω) — was
unspellable because Cure welded plicity to quantity (inferred index ⇒
implicit+erased; explicit domain ⇒ explicit+ω). Design: DECOUPLE.
`Inductive.ctor` gains `plicities :: [:implicit | :explicit]` parallel to
`quantities`; the kernel type-checker does NOT read plicities (elaboration
concern — out of the TCB despite living on the core record). Surface
`{name : Type}` constructor domain → `{:implicit_dom, name, inner}`
(disambiguated from refinements by `{ ident :` lookahead); default quantity ω.
Application arity and meta-insertion key off plicity, not quantity;
`branch_scope` binds named implicits (`{k = kk}`) at the slot's actual
quantity. The erased `{0 k}` surface is intentionally NOT added — it already
exists as the inferred index variable, and the `{:erased_used_relevantly}`
gate stays sound. Removed the `otp_conversation.cure` explicit-carry
workaround.

## 5. Algebraic data types

### 5.1 Consolidated ADT model (design specification)

*Source: 2026-07-20-algebraic-data-types-design.md — the stable language-level
reference over the existing inductive kernel, not a new kernel feature.*

- **Ordinary ADTs:** nominal families, one constructor per alternative;
  constructors are functions returning the family; same-shape declarations are
  distinct types; an empty declaration (`type Never =`) is an empty type,
  eliminated only via the kernel-checked empty/absurd path.
- **Parameters vs indices:** parameters uniform, indices per-constructor
  (see §4.1). Indices are arbitrary well-typed terms and are part of family
  identity, not runtime proofs.
- **GADTs:** constructor result indices refine the branch context via the
  dependent case motive — never a cast or mutable type-variable assignment.
  Invalid branch bodies are rejected even when unreachable; vacuous branches
  discharge only through kernel-checked obligations.
- **Records:** nominal single-constructor ADTs with named fields; literals
  lower to the positional constructor in declaration order; missing/extra/
  duplicate fields are errors; projection resolves against the declaration,
  not the runtime tuple; update reconstructs the constructor.
- **Aliases vs opaque:** `typealias` introduces no family (unfolds
  definitionally); `opaque type` is a nominal boundary — hidden constructors
  unmatchable outside the defining module; aliases must not bypass opacity or
  create structural equivalence.
- **Constructor applications:** inferred parameters inserted only at declared
  implicit positions, solved from explicit args/expected types/index
  constraints; unresolved metas rejected at definition boundaries; annotations
  guide elaboration but never introduce casts.
- **Pattern matching:** the eliminator; checks constructor validity/family
  identity, arity/field types, per-branch index refinement, exhaustiveness,
  provable redundancy, branch result compatibility. Scrutinees must be values
  (effects belong to branch bodies or the computation judgment). Coverage is
  static — never replaced by a runtime catch-all fabricating a result.
- **Positivity/recursion:** strict positivity; negative occurrences rejected;
  mutual families checked as a group over the resolved declaration graph.
- **Runtime representation:** constructor-directed erasure — nullary
  constructors → atoms; present-field constructors → tagged tuples; erased
  parameters/proofs absent; builtin families (Bool/Nat/List) may opt into
  native representations via trusted schema-validated bindings only
  (structural similarity does not confer one); Unix BEAM and AtomVM must agree
  on observable shape.
- **Effects:** ADT values are pure values; computations use `-> T ! Effect`
  (result type is `T`, not `Effect(T)`).
- **Equality/proofs:** constructor equality is nominal; coinciding erased BEAM
  terms never make distinct constructors equal; effectful operations and FFI
  cannot fabricate proof-relevant constructors without an audited evidence
  contract.
- **Non-goals:** structural subtyping, untagged unions, unchecked
  casts/believe_me, row-polymorphic variants, representation equality between
  families, effectful type-level computation, general recursion in the kernel.
- **Boundaries:** surface/resolution/canonicalization/diagnostics =
  parser/elaborator; family formation, positivity, constructor typing, case
  checking, certificates, serialization validation = trusted core (full TCB +
  Antigen gates on change); representation selection = erasure/codegen with
  cross-target tests.

### 5.2 Anonymous ADTs / union types (Approved; BUILT + GREEN, zero TCB)

*Source: 2026-07-11-anonymous-adts-design.md.*

`A | B` in type-expression position (lowest precedence, below `->`) elaborates
to a compiler-generated discriminated inductive family keyed by its sorted
member list — a real tagged sum; "nothing about it is TypeScript except the
syntax". REJECTED: untagged unions (impossible — `String = List(Char)` and
`List(Int)` erase identically; identity coercion needs subtyping or
believe_me, both deliberately absent); row polymorphism; transparent
all-literal erasure in v1 (the correct condition — pairwise-distinct erased
terms — is subtle; may return opt-in). Canonicalization: flatten → normalize
each member to FULL normal form (`nf/3`, not whnf — `Bounded(1+1)` and
`Bounded(2)` must key identically) → key by resolved post-rekeying
`Mod#Name` identity, numerals as (type, value) → dedupe → sort → collapse
singletons. The sorted key names the family, so two modules writing
`Int | String` get the same definitionally-equal family, emitted once into a
synthetic module; members must be ground and closed. REVISED (`583fafe`):
literal-alongside-its-own-type ADMITTED (`Int | 3` sentinel patterns) as a
genuine disjoint sum with most-specific-wins precedence. Introduction is
check-mode-only injection (bare `42` never infers a union; un-annotated
heterogeneous lists error — accepted cost of zero TCB); widening is a real
generated remap function. Elimination: typed patterns (`n: Int => …`),
admissible anywhere patterns are; sub-union narrowing; coverage via existing
machinery. Erasure: uniform tagged rule — literal member → bare quoted atom
(`:'3'`), type member → `{:'Int', v}`. REVISED (`06be19e`): `@extern` CAN
return a union — the compiler generates a discriminating wrapper (ordered
most-specific-first BEAM class guards, NO catch-all: out-of-contract values
raise an honest CaseClauseError); runtime-indistinguishable pairs
(`Int | Nat`) rejected at declaration; nested unions in extern returns still
rejected.

### 5.3 Primitive type declarations (Approved)

*Source: 2026-07-10-primitive-type-declarations-design.md.*

New `primitive` keyword with `@builtin(:tag)`: `@builtin(:int) primitive Int`
in `Std.Int` (likewise Float → `{:float_type}`, Binary → `{:binary_type}`);
exactly three legal tags. Rejected alternatives: `opaque` (would create a
postulate family severed from the primitive-keyed literal/op machinery) and
`@extern` (functions only). `Cure.Core.Builtins.seed` registers the bindings
in every initial env (replacing the deleted hardcoded `primitive_type/1`); the
declaration marker must agree with the seed (consistency contract). The
declaring modules join the auto-prelude; `Std.Binary` is preluded wholesale.

### 5.4 Constructor qualification & `exposing` imports (PARKED)

*Source: 2026-07-19-constructor-qualification-design.md — approved direction,
deliberately not scheduled; recorded so it isn't re-derived.*

A defining module (or single type) opts its data constructors into
qualified-by-default (`Dynamic.Atom(x)`), and importers opt back into bare
scope with `use M exposing(*)` / `exposing(Type.*)` / `exposing(A, B)`.
Settled: opt-in at the defining module, NOT a global default (a global flip
would break every stdlib ADT); type-qualified, not module-qualified
(`Dynamic.Atom`, composing with existing qualified-type resolution); governs
data constructors only (module functions import unqualified as today).
Qualified and bare spellings are the same constructor — identical runtime tag;
zero TCB. Until built, `Std.Dynamic`'s constructors stay bare (positional
resolution keeps the stdlib compiling). Out of scope: qualified
function/value references; module-qualified constructor syntax; any global
default flip.

### 5.5 Length-indexed Binary (DEFERRED — build only when a consumer appears)

*Source: 2026-07-10-length-indexed-binary-design.md.*

`Binary(n)` — byte-count-indexed (not bits) view over the `{:binary_type}`
primitive; dependent bit-syntax (`<<len: 8, payload: len/binary>>` giving
`payload : Binary(len)`) rides existing dependent-match machinery; the index
is erased. Open decision deferred with it: refinement-carrying primitive vs an
indexed `{:binary_type, n_core}` node. Triggers that would justify building:
(A, primary) a typed protocol/session library with length invariants; (B)
totalizing destructure (needs the removed Nat-bound facility); (C) zero-copy
length-tracked views. Explicitly NOT a trigger: the I2C/UART driver layer;
fixed-literal field sizes are already covered by the primitive, and
runtime-length frames alone are enforced by BEAM match at runtime. Non-goals:
bit-level indexing, reintroducing general refinements, changing the primitive.

## 6. Typeclasses and instance machinery

### 6.1 Why an elaborator feature (design)

*Source: 2026-07-09-typeclasses-elaborator-feature-design.md.*

`proto`/`impl` (surface: `interface`/`implementation`) is the one construct
that is neither a macro (macros are type-blind → could only do runtime
dispatch) nor kernel (no dependent language puts instance resolution in its
kernel). Three layers: dictionaries = ordinary Core records (zero kernel
delta); resolution = E-layer instance search (§6.3); elaboration lowers
resolved methods to direct calls — avoiding runtime dictionary lookup on ESP32.
Buys: constraints usable inside dependent types, zero
device cost, coherence plus statable laws. Its open ledger (superclasses,
deriving, overlap/orphans, defaults, MPTC/associated types deferred) is
resolved by the later approved specs below.

### 6.2 Typeclasses core design (approved)

*Source: 2026-07-10-typeclasses-design.md.*

Locked surface: `interface` / `implementation` keywords (Idris2 lineage),
indentation blocks; coherence = global uniqueness + named implementations;
deriving approved (declaration-attached `deriving Equatable` and standalone
`derive X for T`). Interfaces elaborate to dependent record types; head kind
is INFERRED from method signatures — `Functor` is true HKT `f : Type → Type`
in v1; inconsistent head use = `{:inconsistent_head_kind}`. Implementations
are dictionary values in a coherence table keyed
`(interface_id, head_type_id)`; duplicates `{:overlapping_instance}`; orphans
`{:orphan_instance}` with a builtin/moduleless-head exemption so primitives
register cleanly. Resolution: concrete key → project and inline statically (no
runtime dictionary); abstract head under a constraint → project from an
implicit dict parameter; HKT heads extracted by Miller pattern-fragment
unification; failure → `{:no_instance, iface, T}`. Named instances are used
only via explicit projection, never picked automatically. Constraints ride the
existing post-return-type `where` clause. Dict quantity: elaborate as present,
occurs-check demote to erased if unused (one-way demotion only — respects the
locked no-auto-promotion rule). Migration scope: Equatable, Ord, Show,
Functor, Access; `Equivalent` (propositional identity GADT) and JSON (ADT +
FFI) are explicitly OUT. Known hazards recorded: `==` on `Any` operands is a
documented blocker with no resolution rule; String/Atom equality had no
dedicated builtin (decision needed before migration — resolved downstream by
the sole-route work, §7.3); deriving over mutual recursion needs two-pass or
explicit scope cut; any TCB change would be a HARD-STOP.

### 6.3 Type-directed search engine (design; instance profile BUILT)

*Source: 2026-07-09-type-directed-search-design.md.*

One reusable E-layer goal-directed search over hint databases; entirely
untrusted, every result kernel-checked (LCF: untrusted-AND-checked — the
opposite corner from the retired Z3, which was trusted-unchecked).
`solve(goal, db, fuel)` = backward chaining with backtracking. Two profiles of
the same engine: **instance resolution** (class-headed goals, NO backtracking
— coherence guarantees ≤1 match; shallow fuel; decreasing instance heads give
fuel-independent termination) and **hint/lemma search** (arith/user databases,
full backtracking, deep fuel). Fuel is mandatory; unification restricted to
the Miller pattern fragment; NO solver/SMT ever. Surface `by search` tries
computation first (whnf/refl — e.g. `So(5>0)` → `So(True)` → `Oh()`), search
only if needed. Reserved-but-unbuilt clients: refinement `So` discharge,
verified linear-arithmetic decision procedure, general `auto`.

## 7. Overloading, argument labels, operators, fixity

*The folder README fixes these as ONE staged feature family (typeclasses-design
→ elaborator-feature → overloading-and-labels → type-directed resolution →
precedence-groups), refining rather than competing; the newest approved
document and its named implementation gate govern disagreements.*

### 7.1 Overloading and argument labels — parent spec (approved)

*Source: 2026-07-10-overloading-and-argument-labels-design.md.*

Overloads keyed by `(name, arity, argument types, labels)`; Idris2-style
elaborate-and-prune; Swift-style labels with one deliberate divergence —
labels are optional by default and mandatory only when declared load-bearing.
Three parameter forms: `fn f(x: T)` (label usable, optional);
`fn f(to dest: T)` (label mandatory; internal name private to the body);
`fn f(_ x: T)` (label forbidden — Phase 3, deferred). Arguments stay in
declaration order (labels are annotations, not reordering — Swift, not OCaml).
Call-site algorithm: gather → label filter → type filter → decide
(one / `{:no_matching_overload}` / `{:ambiguous_overload}`). `f(x: 1)`
already parses as the record field-pair form; the elaborator routes on the
head. Pinned: zero TCB (labels erase); qualified `Mod.f` is the escape hatch.
Phases: 1 type-directed resolution, 2 labels, 3 suppression.

### 7.2 Type-directed overload resolution — first slice (approved 2026-07-18; BUILT + GREEN)

*Source: 2026-07-18-type-directed-overload-resolution-design.md.*

Buildable Phase-1 slice: same-module and `use`-imported overload sets resolved
by argument type. Zero TCB; no Antigen antibody needed. OUT of scope here:
labels, the `+`/operator ergonomic (deferred to §7.3 — do NOT add operator
desugaring in this slice), `_`-suppression, return-type-directed resolution,
sibling-module sets. Mechanism: the duplicate-definition gate becomes an
overload-set builder; canonical keys extend `Mod#name` with arity +
declaration-order ordinal (`Mod#plus/2#0`); a size-one set stays byte-identical
to today (inertness constraint — no golden-test movement). Same-arity mutually
unifiable telescopes remain rejected: `{:overlapping_overload, name, arity}`
(preserving the old safety). Resolution: gather (with a prefer-direct rule),
infer each argument ONCE, prune by first-order unification, decide → member
key / `{:no_matching_overload}` / `{:ambiguous_overload}` (diagnostics name the
qualified escape hatch). Members emit under distinct mangled BEAM names.
Bare unapplied references are NOT extended (actionable diagnostics, never a
silent `:unknown_global`); the key-format ripple through helpers that match
the `#name` suffix textually is the top named risk.

### 7.3 Precedence groups and operator overloading (Step 2 / sole-route LANDED `93ed411d`; Step 3 ahead)

*Source: 2026-07-18-precedence-groups-and-operator-overloading-design.md.*

Declaration-driven operator system, Swift shape; end state: the compiler owns
NO fixed operator list and the static `Precedence.ex` table is gone. Enabling
property: Cure has no juxtaposition application, so an identifier in operator
position is unambiguous — word operators (`a and b`) parse cleanly. Non-goals:
no new coherence policy; no reducibility knob; no numeric priorities in
surface; builtin syntactic operators (`.`, `|>`, `<-|`, `=`/`+=`, `..`) stay
syntactic and non-overloadable; TCB untouched.

- **Step 1 (kernel-routed instances):** coherence key = `Normalise.whnf` head
  symbol (single-atom key suffices under global uniqueness — deliberately NOT
  Lean's discrimination trees); signature conformance decided by kernel
  conversion (the `alpha_equal?` family deleted); sited
  `{:method_signature_mismatch, iface, method}` diagnostic.
- **Step 2 (sole route):** backtick-escaped identifiers (`` fn `+`(a,b) ``)
  enable operator-named functions. Superinterfaces:
  `interface Comparable(t) requires Equatable(t)`
  (`{:missing_superinterface,…}`; superinterface dictionary in default-body
  scope — load-bearing for derived `compare`). Minimal basis: `==` (Equatable)
  and `<` (Comparable), everything else derived (Swift basis; `NaN == NaN`
  correctly false; `compare` an overridable derived default). Arithmetic split
  Additive(`+`,`-`,`negate`) / Multiplicative(`*`) / Divisible(`/`), motivated
  by Std.Units; `%` deliberately NOT in Divisible (Integral-style home; Float
  never implements a broken modulo). Bool connectives are ordinary monomorphic
  backtick functions in Std.Bool — no interface. **Sole-route invariant:** the
  typeclass method is the ONLY route to `==`/`!=`/`<`/… — build_binop
  hardcoding removed; primitive comparisons live only inside leaf instance
  bodies; static instance selection preserves emitted-code parity. Universal structural
  `==` becomes an auto-derived per-type Equatable instance (overridable for
  user types, primitives locked by coherence; NOT a blanket instance);
  `Comparable` is NOT auto-derived. Equatable/Comparable are ambient via
  `@prelude`; a stdlib-DAG bootstrap audit guarantees no `==` below
  Std.Equatable.
- **Step 3 (fixity):** `precedencegroup Name` with
  `associativity: left|right|none`, `higher_than:` / `lower_than:` — a partial
  order compiled to topological binding powers; incomparable adjacent groups ⇒
  `{:ambiguous_precedence, g1, g2}` (stricter than numeric levels; Swift
  behavior). Declarations: `` infix `<?>` : Additive ``, `infix and : …`,
  `prefix not`, `postfix`. A fixity with no function ⇒
  `{:no_operator_meaning}` at use. Builtins are declared in a preloaded
  `Std.Operators` seeded from the old table; the lexer emits generic
  operator-lexeme tokens; the session fixity table must be O(1) (heed the
  parser-quadratic-lookup finding). Prefix `-` → `negate` recommended.

### 7.4 `use`-propagated fixity (design)

*Source: 2026-07-19-use-propagated-fixity-design.md.*

Makes fixity propagate through `use`, uniformly for user modules and stdlib,
with `@prelude` making core operators ambient. Zero TCB; fixity is a syntactic
property resolved at parse time, never dependent on elaboration.

**Model:** `fixity(M) = own(M) ∪ ⋃ own(X) for X ∈ use_reach(M) ∪ ⋃ own(X) for
X ∈ use_reach(P) ∪ {P} over all @prelude providers P` — a prelude provider is
treated exactly as an implicit transitive `use`, including the provider's own
`use`-closure (flattening only `own(P)` would under-propagate once a provider
itself `use`s an operator-declaring module). Precedence groups travel as
ordinary AST nodes with the operators that reference them.

**Key enabler:** fixity extraction is table-independent — declarations parse
without consulting the fixity table, so `own(X)` reuses the existing
macro-harvest pass (full parse seeded with `BuiltinFixity.table()` — never an
empty table except the one-time `operators.cure` bootstrap — with
per-statement `synchronize_to_statement` recovery). `use_reach(M)` is an
on-demand name-based BFS via existing path resolution, NOT the precomputed
`DepGraph` (which only computes compile order). Caching must be
provenance-scoped (unconditional only for shipped stdlib paths;
per-generation for user modules — the `cached_module_interface` rule); this
applies to `own/1`, `fixity(M)`, and the reimplemented
`BuiltinFixity.table/0` once user `@prelude` modules exist. In-scope
precondition: `DepGraph.scan_file` currently drops a whole file (with its
`use` edges and `@prelude` flag) on ANY parse error — exactly wrong for a
module using a not-yet-propagated operator; it must gain the same
statement-level recovery, and the CLI/`Cure.Project` driver must thread the
discovered `prelude_provider?` set into each `Parser.parse` call, or user
`@prelude` modules never reach sibling files.

**Conflict rule (replaces the privileged builtin list):** within one module's
assembled table, each operator lexeme has at most one fixity per slot
(infix/prefix/postfix are independent — `-` may be both prefix and infix).
Different-group redeclaration = hard whole-module parse error
`:conflicting_operator_fixity {lexeme, group_a, group_b}`, raised during table
assembly (unlike body-parse failures, it cannot be recovered around); an
identical redeclaration is a silent no-op; function overloads never conflict
(fixity attaches to the symbol — Haskell/Swift semantics). Same-name
`precedencegroup` with a different body = `:conflicting_precedence_group`
(separate tag; different payload shape). `check_no_builtin_rebind` is deleted
(its three test call sites move to the new tag); `check_no_precedence_cycle`
is repointed at `fixity(M)` (cycles degrade gracefully via `incomparable?`, so
it stays an elaboration-time pass). Locked decisions: full transitive closure
(over-approximation is safe — unimported operators still fail at elaboration
with `no_operator_meaning`); cycles merged by union; conflicts detected over
the full transitive union, not just direct `use`s. Edge cases: single-file
parses bind only the compiler-bundled prelude; an operator whose group is
unreached degrades to `incomparable?`; the bootstrap re-entrancy guard
generalizes from the single `operators.cure` case to the whole prelude
closure. Printer callers must thread `fixity(M)` or reprinted operators
degrade to unknown precedence.

### 7.5 General and literal-aware conversion

*Source: 2026-07-22-type-directed-literal-interfaces-design.md (locked).*

Ordinary `From(target,source)` and `TryFrom(target,source,error)` interfaces
cover total and fallible runtime conversion. Authored literal syntax first
searches the ordinary `FromLiteral`/`TryFromLiteral` tier; only when that tier
has no applicable candidate does it materialize its normal value and fall back
to `From`/`TryFrom`. Ambiguity, rejection, stuck evaluation, or kernel failure
in a selected literal tier never falls through. There is no new declaration
syntax and no order-based tie-break.

Literal syntax has no canonical default target. Without an expected type it
creates a deferred monomorphic constraint shared by every use; annotation or
use fixes one type and the literal is elaborated once. Direct literal use and a
single-use unannotated `let` are equivalent. Conflicting uses are an error, not
per-use reinterpretation. Unused or underconstrained bindings require deletion
or annotation, and unresolved inference never crosses a public separately
compiled interface.

Exact descriptors preserve decimal spelling and structural evidence:
`ListLiteral(a,n)` derives Vector length from syntax even when its elements are
runtime values; statically sized binary descriptors similarly support fixed
byte/bit targets. Decimal selects exact String and never round-trips through
Float; interpolated strings, variables, and dynamic binaries use the general
tier. Runtime Nat-to-Bounded is fallible, while refined proof-carrying input is
total; literals can discharge the check early. `Char = Bounded(1114112)` exactly
matches Erlang `char()` including zero and surrogate integers. Produced terms
are independently kernel-checked and conversion machinery erases. Rich
diagnostics plus completion, hover, navigation, reflection, TCB, totality,
erasure, and Antigen gates are mandatory.

## 8. Records and optics

*Source: 2026-07-19-record-field-lens-deriving-design.md (approved;
Sub-project 1 of the optic-path programme).*

Derive a law-checked `Lens` for every field of every record with no record
tag and no bespoke compiler machinery: field `f` of record `R` is exactly
`lens(fn(r) -> r.f, fn(v) -> fn(r) -> R{r | f: v})` — both halves are
existing surface syntax, so derivation is purely syntactic decl-position
Tier-3 macro codegen (the landed message-code-derivation model, before
`LiftModule.collect`), type-checked afterward by the normal kernel; zero TCB.
Names: `R_f` per field, collision-free by construction; an existing user
binding of that name errors `{:field_lens_name_clash, R, f}` — never silently
overwritten. Derivation is eager for every `rec`; unused lenses tree-shake at
emit. Companions: `ix(i)` list-index optic — deliberately an AFFINE, not a
lens (bare lists carry no length; miss-is-a-no-op law; totality is obtained
by choosing `Vector(a,n)` + `Bounded(n)` — the container is the totality
declaration); new total `Std.List.at/3` and `set_at/4`; `each()` list
traversal via count-indexed `TravRep` is the highest-risk piece, scheduled
last and severable. Deferred to later specs (do NOT build here): operator
sugar (`<~`, compose — gated on the operator/overload branches);
projection/bracket sugar (`u.scores[0] <~ v` — requires a future type-aware
macro tier, a Lean-MetaM analogue, still outside the TCB); grade-decorator
refactor (`@linear cap: T`); Vector index lens and `_Some` prism. Terminology
guard: optic `AffineKind` (focus may be absent) and the QTT `:affine` grade
(binder used at most once) are unrelated — same name by historical accident.

---

## Source specs

- `README.md` — declares the five overload documents one staged family; newest approved document governs disagreements.
- `2026-06-30-cure-dependent-types-frp-design.md` — foundational MLTT-subset charter: kernel/elaborator split, NbE, totality-gated δ, erasure, Safe-FRP target; fixed-universe sections superseded.
- `2026-07-02-dependent-match-surface-design.md` — impossible-branch surface over one TCB `branch_unify` wrapper and the always-fails `{:absurd}` leaf.
- `2026-07-02-lean-shape-matching-design.md` — unification-driven generalizing match with carried stuck-index equations; five-rule unifier; HEq gap.
- `2026-07-02-param-index-split-design.md` — `indices (…)` surface and the params-never-refined invariant through `{:vdata}`/motive/unifier.
- `2026-07-09-type-directed-search-design.md` — one untrusted-AND-checked backward-chaining search engine; instance vs hint/lemma profiles; `by search`.
- `2026-07-09-typeclasses-elaborator-feature-design.md` — why proto/impl is an elaborator feature: Core-record dictionaries, E-layer search, and compile-time resolution.
- `2026-07-10-length-indexed-binary-design.md` — deferred `Binary(n)` design with explicit build triggers and non-triggers.
- `2026-07-10-overloading-and-argument-labels-design.md` — parent overload spec: identity key, Swift labels with optional-by-default divergence, phases.
- `2026-07-10-primitive-type-declarations-design.md` — `@builtin(:tag) primitive` declarations replacing hardcoded primitive seeding.
- `2026-07-10-qtt-grades-plan.md` — completed QTT `{0,1,affine,ω}` program; eight settled grade decisions and the predicate-shape rename trap.
- `2026-07-10-typeclasses-design.md` — approved dictionaries/coherence design: HKT heads, orphan/overlap rules, dict-quantity demotion, migration scope.
- `2026-07-11-anonymous-adts-design.md` — `A | B` as content-addressed generated tagged families; post-landing revisions for literal members and extern wrappers.
- `2026-07-18-precedence-groups-and-operator-overloading-design.md` — declaration-driven operators: kernel-routed instances, sole-route `==`/`<` basis, precedence groups as a partial order.
- `2026-07-18-relevant-implicit-ctor-index-design.md` — plicity/quantity decoupling giving relevant implicit `{k : T}` constructor indices.
- `2026-07-18-type-directed-overload-resolution-design.md` — first resolution slice: ordinal-keyed overload sets, infer-once prune, inertness constraint.
- `2026-07-19-constructor-qualification-design.md` — parked qualified-by-default constructors with `exposing(…)` import filters.
- `2026-07-19-record-field-lens-deriving-design.md` — eager syntactic per-field lens deriving plus `ix` affine and list traversal.
- `2026-07-19-use-propagated-fixity-design.md` — transitive `use`-closure fixity tables, prelude providers, conflict detection replacing the builtin rebind list.
- `2026-07-20-agda-style-universe-polymorphism-design.md` — authoritative replacement of the universe ceiling: canonical level algebra, sort indices, `TypeLimit`, phased migration.
- `2026-07-20-algebraic-data-types-design.md` — consolidated language-level ADT reference: nominal families, GADT refinement, records, opacity, representation, trust boundaries.
- `2026-07-22-type-directed-literal-interfaces-design.md` — `From`/`TryFrom` plus literal-aware `FromLiteral`/`TryFromLiteral`; strict tier fallback, exact descriptors, Vector length derivation, and `Bounded`/`Char`/`Decimal` laws.
