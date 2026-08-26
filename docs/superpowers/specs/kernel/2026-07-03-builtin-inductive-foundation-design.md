# Builtin-Inductive Foundation — Design

**Status.** Approved design (2026-07-03). Branch `autopilot/lean-shape-matching`.
**Layer.** Per the repo's canonical K/E/P/A/C layer map (`cure-porting` skill):
**K** (kernel/TCB, `lib/cure/core/*` — the `Env`/`Inductive` registry extension,
schema validation, `infer_prim`, `bool_elim` retirement across
`term`/`value`/`eval`/`quote`/`conv`/`normalise`/`kernel`/`certificate`/
`serialize`). `lib/cure/core/eval.ex`'s `fold/2` (the plumbing decision in §2)
sits at a genuine overlap in the map's own definitions — its directory rule
("K = `lib/cure/core/*`") and its keyword rule ("C = eval/codegen/erase") both
apply to the same file. What actually matters for this design, independent of
which letter wins: `fold/2` runs *inside* kernel conversion-checking (whnf
during `conv.ex`/`normalise.ex`'s definitional-equality judgment), so it is
trusted-path code regardless of taxonomy — that's the substantive reason §2
treats threading `sig` through it as a TCB-wide change to weigh carefully, not
a label dispute. **E** (elaborator, `lib/cure/elab/*` — literal
`true`/`false` → `True`/`False` wiring and `if`/guard/literal-pattern
retargeting to `:case`); **P** (parser, `lib/cure/compiler/*` — new
`@builtin`-on-`type` decorator support, per §1's surface-syntax note); **C**
(eval/codegen/erase, per the map's own definition — includes
`Cure.Elab.Erase`'s Bool/Nat representation selection despite living under the
`elab/` directory, and the BEAM lowering of the chosen representation). Note
this doc's earlier drafts used "P" for "prelude," which
collides with the layer map's actual P (parser) — the prelude *source*
(`lib/std/*.cure`) is where `Bool`/`Nat` are declared, but it is a source
location, not one of the five layers above. TCB-touching (K) — gated per the
HARD-STOP discipline.

## Goal

Introduce a **builtin-inductive registry** so the kernel and erasure can know a
*canonical* inductive by key, then use it to (1) make **`Bool` a real inductive**
— retiring the bespoke `bool_elim` primitive into the general `:case`/recursor —
and (2) give **`Nat` an efficient native runtime representation** (`Nat → Int`),
replacing today's fatal unary encoding.

## Why (motivation)

- **Lean/Agda-class minimal TCB.** `bool_elim` is a hand-written primitive
  eliminator spread across ~8 core modules (term/value/eval/quote/conv/normalise/
  kernel/certificate) — and already sprang one conversion soundness hole. Folding
  `Bool` into the general `:case` the kernel already has removes a whole
  primitive and a class of future soundness risk. One eliminator scheme, not two.
- **Device-viable runtime representations.** Today `Nat = Z | S(Nat)` erases to
  unary nested tuples (`{:S, {:S, :Z}}`) — O(n) space. On ESP32/AtomVM a `Nat`
  loop counter or list length would exhaust RAM. The Idris "Nat hack"
  (`%builtin Natural Nat`, GMP at runtime) is the fix: erase `Nat` to a machine
  integer. This is directly load-bearing for the repo's whole reason to exist.
- **One mechanism, double duty.** The same registry lets the kernel *construct*
  canonical `Bool` (so `{:prim}` comparisons yield it) **and** lets erasure pick
  the native representation (`Bool → atom`, `Nat → int`). Building it once buys
  both the type-level and the runtime-level payoff.

## Background — current state (verified)

- The dependent kernel (`lib/cure/core`) has **no** notion of a canonical/builtin
  inductive; every inductive lives in the signature, user-declared. (`grep` for
  builtin/preloaded/canonical inductive in `lib/cure/core` finds nothing.)
- `Bool` is a **primitive**: `{:bool_type}`, `{:bool_lit}`, and the `{:bool_elim}`
  eliminator, plus `{:prim, op, args}` ops whose results are `{:vbool, _}` typed
  at `{:vbool_type}` (`kernel.ex` `infer_prim`, `eval.ex` fold).
- `Nat` is an ordinary user inductive; it erases via the generic constructor
  lowering to nested tuples/atoms (confirmed: demo output `{:S, {:S, :Z}}`).
- `{:absurd}` is rejected by the kernel in a reachable position; branches are
  discharged as vacuous only via the kernel's own index unification.

## Architecture

### 1. The builtin-inductive registry (the mechanism)

- The prelude declares the builtin types as **ordinary Cure inductives**, each
  carrying a binding to a canonical key:
  ```cure
  @builtin(:bool)
  type Bool = False | True

  @builtin(:nat)
  type Nat = Z | S(Nat)
  ```
- `@builtin(:key)` registers `key → family-id` in the signature. Registration is
  **schema-validated at seed time** against a fixed expected shape per key —
  **arity and constructor name, not arity alone**: `:bool` ⇒ exactly two nullary
  constructors named `False` and `True` (either declaration order); `:nat` ⇒ a
  nullary constructor named `Z` and a unary constructor named `S` whose one field
  is the family itself. Name-checking is load-bearing, not cosmetic: the
  `true`/`false` → `True`/`False` literal wiring (§2) and the erasure atom
  mapping `False`/`True` → `false`/`true` (§2) both key off these exact names. An
  arity-only schema would let a binding like `type Coin = Heads | Tails` register
  under `@builtin(:bool)` — passing shape-validation while the name-based
  erasure/literal wiring silently produces nothing sensible (`heads`/`tails`
  atoms that don't match what `{:prim}` comparisons independently return as
  `true`/`false`). That is a real miscompile risk from an honest naming mistake,
  not just an adversarial one, so the schema must check names, not just shape,
  for the trust chain below to hold. A binding that fails its full schema (shape
  + names) is a hard error — the kernel relies only on a *validated* binding,
  never on arbitrary signature data.
- `builtin(sig, :key)` resolves the family — a new function on the kernel's
  actual signature struct, `Cure.Core.Env` (`lib/cure/core/inductive.ex`,
  commonly aliased `Inductive`, threaded through the kernel as `sig`; there is no
  separate `Signature` module). Today's struct (`families`, `ctors`,
  `ctor_to_family`, `defs`, `certified`) has no slot for builtin bindings, so this
  adds one (e.g. a `builtins: %{}` field) — a small, explicit `Env` extension,
  called out here so it isn't discovered mid-implementation. Used by the kernel
  (`infer_prim` returns `builtin(sig, :bool)`) and by erasure (representation
  choice) — see the eval-time caveat in §2 for why the *erasure/evaluation* side
  of that consumption needs its own plumbing note, not just the type-checking
  side.
- **Trust chain / why signature-seeded is sound:** the prelude inductive is
  kernel-checked like any declaration (`check_family`), *and* the `@builtin`
  binding is schema-checked (shape + names, per above), so `infer_prim`'s
  assumption "the thing I return has two nullary constructors named `False` and
  `True`" is doubly guaranteed. Net TCB change: **remove** `bool_elim` (large)
  and **add** the registry lookup + schema validation (small) → a net reduction.
- **Single-registration invariant.** Schema validation alone doesn't prevent a
  *second*, independently schema-conformant `@builtin(:bool)` declaration
  elsewhere — e.g. ordinary application code that happens to declare `type
  MyBool = False | True` and tags it `@builtin(:bool)` too. Without an explicit
  rule, whichever declaration is processed last would silently rebind (or
  error inconsistently on) a key `infer_prim` already resolved against earlier
  in the same compilation — a real hijack path that doesn't require a malformed
  schema at all, only a second well-formed one. The design requires: (1)
  `@builtin` is only *honored* when compiling designated prelude sources (the
  compiler must know which files those are — the same privileged-mode
  distinction other prelude-only mechanisms already need), and (2) independent
  of (1), the registry itself rejects a second registration for an
  already-bound key as a hard error rather than overwriting it. Both are
  required: (1) keeps ordinary user code from registering at all; (2) keeps a
  second prelude module (accidental duplicate, or a future prelude change) from
  silently rebinding a key already resolved elsewhere in the same run.
- **Surface syntax note:** `@builtin(:key)` attached directly before a `type`
  declaration (as shown above) is new parser surface — today's decorator
  attachment (`lib/cure/compiler/parser.ex`, `parse_at`/`attach_decorator`) only
  recognizes a following `fn`/`local` or `rec` construct; there is no case for a
  following `type` declaration, so as written the annotation would currently
  parse as a disconnected standalone decorator node. Phase 1's task list (below)
  must include extending decorator attachment to `type` declarations — this is
  not free surface syntax the mechanism can assume already works.
- **Nominal, not structural.** The registry binds one specific family — the
  prelude's own `Std.Nat`/`Bool` declaration, identified by family-id — not
  "any inductive shaped like `Z | S(Nat)`." This matters in practice: the
  codebase's own tests already show Cure programs declaring a **local**,
  self-contained `type Nat = Z | S(Nat)` inline in their own module rather than
  importing `Std.Nat` (e.g. `test/cure/compiler/dependent_vec_codegen_test.exs`'s
  `@src` fixture). That local family is structurally identical but is a
  *different* family from the prelude's, carries no `@builtin(:nat)` tag, and
  so gets none of Phase 2's native-Int representation — it keeps the O(n) unary
  encoding. Given the motivation section's own justification is exactly this
  shape ("a `Nat` loop counter... would exhaust RAM" on ESP32/AtomVM demo
  programs, which are typically small, self-contained `.cure` files rather than
  stdlib consumers — see `phase35/`), this is a real scope caveat, not a
  hypothetical one: the design must state plainly that the optimization applies
  only to code that imports the canonical `Std.Nat`/`Bool`, and that a
  locally-redeclared lookalike is a silent no-op (same accept/accept behavior,
  no size win) — worth a compiler note/lint recommending `use Std.Nat` even
  though it's out of scope to implement in this design.

### 2. Bool as an inductive (Phase 1, TCB)

- `Bool` becomes the prelude inductive above; `True`/`False` are its constructors.
- `{:prim}` ops (`:eq`,`:ne`,`:lt`,`:le`,`:gt`,`:ge`,`:and`,`:or`,`:not`) return
  `builtin(sig, :bool)` instead of `{:vbool_type}`, and their evaluation produces
  the corresponding constructor value instead of `{:vbool, _}`.
  **Plumbing decision:** the type-level half of this is straightforward —
  `kernel.ex`'s `infer`/`check` already thread `ctx → sig` (`Context.signature/1`)
  everywhere `infer_prim` runs. The value-level half is not symmetric today:
  `eval.ex`'s reduction path (`Eval.eval/2` → `prim/2` → `fold/2`, which is what
  actually computes `{:vbool, a < b}` etc. today) carries only the local
  variable-value environment, never `sig`. **Decision: `fold/2` hardcodes the
  atoms `:True`/`:False`** rather than threading `sig` through `Eval.eval` and
  every call site that reaches it (whnf during conversion-checking runs deep
  inside `kernel.ex`/`conv.ex`/`normalise.ex`, so plumbing `sig` there is an
  invasive, TCB-wide change for no added safety). This is still sound, not a
  compromise: the registry's job is a *one-time* validated contract at seed
  time — once schema validation has pinned `:bool`'s constructors to
  `False`/`True` for the whole program, every consumer relies on that same
  fixed contract, whether it re-derives it dynamically (`infer_prim`, which
  already has `sig` for free) or bakes it in as a literal (`fold/2`, which
  doesn't). "Registry-driven" describes how the *binding* is established and
  validated once, not that every downstream read must re-query it. Net effect:
  `fold/2`'s hardcoded `:True`/`:False` and the schema's validated names must
  never drift apart — call this out as a single-source-of-truth comment at both
  sites so a future rename of the schema's expected names doesn't silently
  desync from `fold/2`.
- Surface `true`/`false` literals elaborate to the `True`/`False` constructors.
- `if` / `when` guards / literal-pattern desugarings **retarget** from
  `{:bool_elim, …}` to `{:case, …}` on `Bool` (a 2-constructor family the kernel
  already covers — coverage, motive, and branch conversion all handled).
- **Retire** `{:bool_type}`/`{:bool_lit}`/`{:bool_elim}` and their clauses across
  `term`/`value`/`eval`/`quote`/`conv`/`normalise`/`kernel`/`certificate` (the
  eight modules `bool_elim` itself spans) **plus a ninth: `serialize.ex`**, whose
  S-expression grammar independently encodes/decodes `(bool-type)` and
  `(bool <atom>)` nodes for the C2 independent-re-validation commitment
  (`serialize.ex`'s own moduledoc: "design spec §9, commitment C2" — a
  cross-reference into the separate core design spec, not a section of this
  document).
  That grammar change also invalidates specific lines of the checked-in
  conformance fixture `test/fixtures/core_conformance.txt` — e.g. `accept | (bool
  true) | (bool-type)` and `accept | (prim lt (int 3) (int 5)) | (bool-type)` —
  which must be rewritten to the new `Bool`-as-inductive grammar (constructor
  S-expressions, and `(prim lt …)` typing to the builtin family, not
  `(bool-type)`) as part of Phase 1, not discovered later when an independent
  reimplementation stops matching. Keep `{:prim}` (the ops themselves stay — only
  their result *type* and *value* become the inductive Bool).
- **Erasure:** `False`/`True` lower to the native lowercase atoms `false`/`true`
  (one registry rule — Cure constructors are capitalized but BEAM booleans are
  lowercase). A `:case` on `Bool` lowers to a BEAM `case` on those atoms — which
  is exactly what `{:prim}` comparisons already return, so construct/match/prim
  are self-consistent at runtime with essentially no special erasure work.

### 3. Nat → Int runtime erasure (Phase 2, untrusted C-layer)

- Kernel is **unchanged** — it keeps checking and reducing `Nat` as the inductive
  (type-level Nats are small; no GMP kernel acceleration in v1). This is purely an
  erasure/codegen representation choice, *below* the kernel.
- Registry-driven representation selection in erasure/emit for the `:nat` builtin:
  - `Z()` ⇒ `0`; `S(n)` ⇒ `n + 1`.
  - `match n | Z() -> a | S(m) -> b` ⇒ `case n of 0 -> a; _ -> (m = n - 1; b)`.
  - `Nat`-typed `{:prim}`/arithmetic ⇒ the machine integer op.
  - `S`/`Z` used as first-class values ⇒ the increment / zero closures.
- **Soundness placement:** untrusted. The kernel already accepted the term against
  inductive `Nat`; erasure only chooses a representation. A bug here yields a wrong
  *runtime value*, never an unsound acceptance. Verified by BEAM execution + the
  differential oracle + a **representation-agreement property**: erased-Nat
  evaluation must agree with inductive-Nat evaluation on a generated corpus.
- Index-only `Nat` (e.g. `Vector(a, n)`) is erased entirely, so runtime `Nat`
  values arise only where `Nat` is computationally-relevant data — the rep applies
  cleanly there.
- **Generics gap (open question, not yet resolved by this design):** the
  dependent-kernel path already supports functions generic over a type
  parameter (e.g. `Vector`'s `append({a: Type}, …)` in
  `test/cure/compiler/dependent_vec_codegen_test.exs`). If such a parameter is
  instantiated at `Nat` in one call and at a different (differently-represented)
  inductive in another, a single unspecialized generic body cannot use both the
  native-Int representation and a generic tuple representation for the same
  erased code. The four rules above don't say whether Nat's native-Int
  representation is contingent on monomorphisation running first (each
  instantiation gets its own specialized, uniformly-represented copy) or how an
  unspecialized fallback body would reconcile the two representations.
  Phase 2 must state which, before implementation — this is a real missing case,
  not a hypothetical one, given the existing test coverage of generic dependent
  functions.

## Data flow

Compile-time: kernel checks terms against the *inductive* `Bool`/`Nat`. →
Erasure: registry picks the *native* representation (`Bool → atom`, `Nat → int`).
→ Runtime: BEAM atoms/integers. The inductive is a checking-time fiction; the
machine value is native.

## Phasing (sequential; each phase separately gated + verified)

Phase 2 depends on Phase 1 (it consumes the registry and the `:nat` schema case
Phase 1 seeds — see the ownership clarification below). "Each phase separately
gated + verified" means each has its own complete merge/verification gate and
neither phase's changes need to bundle into one merge with the other's — it
does **not** mean the phases can land in either order or in isolation from
each other; Phase 1 must land first.

- **Phase 1 — registry + Bool-as-inductive (TCB, GATED).** Build the registry +
  schema validation for **both** `:bool` and `:nat` (shape + constructor names,
  §1); extend decorator attachment to `type` declarations so `@builtin(:key)`
  actually attaches (§1); extend `Cure.Core.Env` with the builtin-bindings field
  (§1); move `Bool` to the prelude; rewire `{:prim}` results, resolving the
  eval-time plumbing choice from §2; retarget `if`/guard/literal desugarings to
  `:case`; delete `bool_elim` across all nine affected modules including
  `serialize.ex`, and update `test/fixtures/core_conformance.txt` to match (§2).
  Gate: red-green + a new Antigen antibody (binding-validation rejects a
  malformed `Bool`; `:case`-on-`Bool` equates no distinct normal forms the old
  `bool_elim` did/didn't) + full Antigen + full suite + independent adversarial
  review.
- **Phase 2 — Nat → Int erasure (untrusted).** Registry-driven rep selection in
  erase/emit; representation-agreement property; BEAM + oracle verification. No
  kernel change, so no TCB gate — but still red-green + full suite.
  **Ownership clarification (required for Phase 2 to stay genuinely
  ungated, per the sequencing above):** Phase 1 must land the `:nat` schema case and the
  `@builtin(:nat)` binding on `lib/std/nat.cure`'s existing `type Nat = Z |
  S(Nat)` together with `:bool`'s — the registry's schema table is
  kernel/TCB-owned code, so *adding a new key's schema* is itself a K-layer
  (gated) change regardless of which phase's erasure work consumes it. If the
  `:nat` schema case were instead added during Phase 2, Phase 2 would silently
  reacquire a TCB-gated change under its "no kernel change, no gate" framing.
  With schema-seeding for both keys done in Phase 1, Phase 2 is purely
  erase/emit consumption of an already-validated binding, which is what makes
  it legitimately ungated.

## Testing

- **Oracle:** existing `cond`/`guard`/`match` clusters must stay accept/accept
  after the Bool migration (behavior-preserving); a new probe exercises efficient
  `Nat` arithmetic and confirms the integer representation on the BEAM.
- **Antigen:** antibody for binding-schema validation — covering both a
  shape-malformed `Bool` (wrong arity) and a shape-conformant but
  name-mismatched binding (e.g. `Coin = Heads | Tails` tagged `@builtin(:bool)`)
  — both rejected; antibody that a second, already-bound-key registration
  (§1's single-registration invariant) is a hard error, not a silent rebind;
  antibody that the `bool_elim → :case` migration preserves normal forms and
  termination certification; a regression test asserting `fold/2`'s hardcoded
  `:True`/`:False` atoms equal the schema-validated `:bool` constructor names
  (§2's plumbing decision) — a code comment alone doesn't stop the two from
  silently drifting apart if the schema is ever touched, so this needs an
  actual assertion, not just documentation.
- **Property:** Nat representation-agreement (erased vs inductive evaluation).
- **Full suite** once, alone, at each phase gate; **adversarial review** for
  Phase 1 (kernel-touching).

## Deferred / committed next

- **Match-embedded `when` (general)** — constructor-pattern guards woven into the
  pattern matrix + fall-through, plus Z3 as an **untrusted** coverage lint
  (trichotomy drops the catch-all; non-exhaustive errors; shadowed warns). The
  variable-pattern subset already landed (`92d11d5`). This is the immediate
  follow-on once the foundation lands, and it must be built on inductive-`Bool`
  `:case`, not `bool_elim`. (Roadmap §4.2.)

## Out of scope

- `Int`/`Float`/`String` as inductives — irreducibly primitive BEAM machine types.
  `Int` stays a **distinct** type from `Nat` (`0 : Int` vs `Z() : Nat`); integer
  literals remain `Int`.
- GMP/native kernel acceleration of `Nat` reduction — v1 reduces `Nat`
  inductively; only the *runtime* representation changes.
- A user-facing `@builtin` pragma as a general language feature — the mechanism is
  internal (prelude-only) for now.
- Trusting Z3 in the dependent kernel — locked out (see the SMT trust-boundary
  decision); unrelated to this work but restated so scope is total.

## Risks + mitigations

- **Bootstrapping.** `{:prim}`/erasure need the canonical `Bool`/`Nat` seeded.
  Mitigation: the prelude always seeds them; a `{:prim}` reached without the
  binding is an explicit early compiler error, never a silent miscompile. This
  requires an explicit **load-order** guarantee, not just "the prelude does it
  eventually": prelude modules are compiled in `__group__`-ordered batches
  (`lib/cure/stdlib/preload.ex`, `lib/cure/elab/program.ex`), and multiple
  existing `:core`-group modules (`Std.Eq`, `Std.Core`) already use comparison
  `{:prim}` ops that would need `builtin(sig, :bool)` resolved. The design must
  pin `Bool`'s (and `Nat`'s) `@builtin` declarations to compile strictly before
  any other prelude module that uses `{:prim}` comparisons or `Nat` arithmetic —
  e.g. as the first member of the `:core` group — rather than leaving "seeded
  eventually" to implicit file ordering.
- **Migration churn.** Retiring `bool_elim` touches code committed earlier this
  run (`if`/guards/literals). Mitigation: the retarget is mechanical
  (`{:bool_elim,…}` → `{:case,…}`), covered by the existing green tests, gated by
  the full suite.
- **Literal ↔ constructor wiring / capitalization.** `true`/`false` literals must
  resolve to `True`/`False` constructors and erase to lowercase atoms; covered by
  the registry rule and an explicit test.
