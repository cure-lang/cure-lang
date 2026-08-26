# `Effect` — an Inert Opaque Type Former for Core

**Date:** 2026-07-09
**Status:** historical decision record — superseded for new architecture by
the 2026-07-21 computation/effect-row specifications. The alternative
("Agda-purist" effects-as-data) is specified separately in
[`2026-07-09-effects-as-data-design.md`](2026-07-09-effects-as-data-design.md)
so its rejection is conscious and its staging insights stay available.

**Historical decision:**
[`2026-07-07-sound-effect-discipline-design.md`](2026-07-07-sound-effect-discipline-design.md)'s
stance that effects are surface-only and erased before elaboration. Operator
decision 2026-07-09 made effects Core-representable through an inert former.
The later 2026-07-21 design separates value and computation typing, adds
effect rows and latent effects, and is now authoritative for new work.

**Companion to:**
[`macros/2026-07-08-macro-facility-design.md`](macros/2026-07-08-macro-facility-design.md)
§14 — the BEAM/OTP callback ADTs defined there get effect-typed handler
fields (§7 below), which is what lets user-level macros reimplement
`fsm`/`actor`/`sup`/`app` soundly.

---

## 1. Purpose and locked decisions

Cure's dependent pathway needs a sound way to type effectful computation —
message send, process spawn, timers, effectful FFI — so that macro-defined
constructs (fsm, actor, and everything after them) elaborate through Core
instead of through bespoke compilers. The operator locked the following:

1. **The type former is named `Effect`.** `Effect(T)` is the type of a
   computation that may perform effects and produce a `T`.
2. **Effects are inert in the kernel.** No reduction rules, not even monad
   laws. Conversion treats every effect node as an uninterpreted congruence.
3. **Sound from day one — no retrofit.** The normalizer, the elaborator's
   substitution machinery, erasure, and emission are all closed against
   duplicating, inlining, discarding, or reordering effects *in this design*,
   not in a later hardening pass.

This is the Lean/Idris shape: Lean's `IO` is a set of opaque constants the
kernel never reduces; Idris's `PrimIO`/`%World` likewise. Per the standing
rule that kernel changes are pre-approved iff they align Cure with Agda or
Lean, this qualifies as the Lean-aligned move.

## 2. Design at a glance

```
surface        let x = send(pid, msg)   ──elaborates──►  {:effect_bind, op, λx. rest}
               rest ...

Core           Effect(T) type former; pure / bind / op nodes — all INERT
kernel         typing rules + structural congruence ONLY; zero equations

emit           bind-chains lower to straight-line Erlang statements;
               ops lower to direct BEAM calls  ⇒  zero runtime overhead

runtime        a handler body compiles to the same code the bespoke
               fsm/actor compilers emit today
```

The kernel learns to *type* effects, never to *run* or *rewrite* them. The
trusted runtime (emitted BEAM code + OTP) is the only interpreter.

## 3. Core grammar delta

Four new term nodes (extending the taxonomy in `core/term.ex`):

```
{:effect_type, t}            Effect(T)          — the type former
{:effect_pure, a}            pure(a)            — trivial computation
{:effect_bind, e, k}         bind(e, k)         — sequencing; k binds NOTHING
                                                  itself (it is an ordinary
                                                  Core function term, usually
                                                  a {:lam, ...})
{:effect_op, name, args}     a primitive effect — name drawn from the trusted
                                                  effect-signature table (§3.3)
```

Matching value forms (`{:veffect_type, _}`, `{:veffect_pure, _}`,
`{:veffect_bind, _, _}`, `{:veffect_op, _, _}`) in `core/value.ex`, plus the
structural clauses in `term?/1`, `subst/3`, `Eval.eval/2`, `Conv`,
`Normalise.nf_struct`, `Quote`, `Serialize`, and `Validator`.

**Why dedicated nodes rather than reusing `{:prim, op, args}`-stuck or
`{:global, name}`:** the stuck-prim pattern (`eval.ex:100-105`) already
*behaves* inertly, but reusing it would make effect ops indistinguishable
from merely-unfolded arithmetic to every downstream pass. Dedicated nodes
make the relevance rule (§5.3), the validator backstops (§8), and the emit
special-casing greppable and enforceable by shape, which is what
"sound from day one" requires.

### 3.1 Typing rules (kernel)

```
Γ ⊢ T : Type ℓ
──────────────────────────           Effect : Type ℓ → Type ℓ
Γ ⊢ Effect(T) : Type ℓ

Γ ⊢ a : T
──────────────────────────
Γ ⊢ pure(a) : Effect(T)

Γ ⊢ e : Effect(A)    Γ ⊢ k : A → Effect(B)
────────────────────────────────────────────
Γ ⊢ bind(e, k) : Effect(B)

sig(op) = (T₁, …, Tₙ) → Effect(R)    Γ ⊢ aᵢ : Tᵢ
────────────────────────────────────────────────
Γ ⊢ op(a₁, …, aₙ) : Effect(R)
```

`bind` is **non-dependent** in v1 (`B` may not mention the bound result) —
matching Lean's `Bind.bind`. Dependent bind is ledgered (§10).

### 3.2 Inertness — the definitional-equality contract

**Zero new equations.** Specifically and deliberately:

- **No monad laws.** `bind(pure(a), k) ≢ k(a)` definitionally. If the laws
  were definitional, conversion could rewrite effect structure during type
  checking — the exact door we are closing. (Lean likewise does not reduce
  `IO.bind` in the kernel.)
- **No η, no commuting conversions**, no floating ops in or out of `bind`.
- `Eval.eval` maps each node to its value form, evaluating *subterms* (an
  op's arguments are ordinary values and evaluate normally — `send(pid,
  1 + 2)` evaluates the `1 + 2`) but never the effect structure itself.
- `Conv` compares effect values by congruence: same node, same op name,
  pointwise-convertible children. Nothing else.
- `Normalise.nf` reads effect values back structurally (new `nf_struct`
  clauses), preserving shape exactly. The nf-idempotence Antigen suite gains
  effect-node seeds (§9).

Consequence for the metatheory: the extension is *conservative* in the
standard sense — `Effect`/`pure`/`bind`/ops form an uninterpreted signature,
so no existing conversion judgement changes and normalization/termination of
the existing fragment is untouched.

### 3.3 The effect-signature table (TCB)

A small trusted table (sibling of `core/builtins.ex`) declaring each op's
name, Core signature, and BEAM lowering. Its role, sharpened by the
provenance rule (below), is narrow: **BIFs we implement natively**, plus the
generic FFI bridge. Stock Erlang/OTP BIFs do **not** belong here — they are
raw externs wrapped by the typed process algebra (see
[`2026-07-09-typed-beam-process-algebra-design.md`](2026-07-09-typed-beam-process-algebra-design.md)).
v1 inventory:

| op            | Core signature                          | BEAM lowering                          |
|---------------|------------------------------------------|----------------------------------------|
| `extern_call` | per-declaration (see below)               | direct remote call                     |

The named-op table is therefore **empty of process/messaging ops** — `send`,
`self`, `sleep`, `print`, timers, and the whole OTP surface resolve to stock
BIFs, so they live in the sealed raw base `Std.Otp.Raw` and are wrapped by the
typed algebra `Std.Otp`, not enshrined here. The table gains an entry only when
Cure implements an actual custom effectful primitive (a native NIF with no
honest stock MFA); the process algebra needs none.

`extern_call` is the FFI bridge: `@extern` gains an effect-typed form whose
declared return is `Effect(T)`; it lowers to the same direct remote call as
today. This *closes the existing FFI purity lie for new code* — today every
`@extern` wears a pure type regardless of behaviour. Migration of existing
externs is ledgered (§10). Raw `receive`/`spawn` remain rejected (E043); the
mailbox is owned by the OTP behaviour a container lowers onto (`gen_server`/
`gen_statem`), so callback bodies never `receive`. Process-lifecycle ops
(`spawn_link`, `monitor`, `exit`, …) are raw-base externs reachable only via
the typed algebra / macro output, never the surface.

## 4. Kernel delta summary (TCB)

- `Effect` formation/introduction/`bind` typing rules in `Kernel.check`/`infer`.
- Structural congruence clauses in `Conv`.
- Value forms + structural eval clauses in `Eval` (no reductions).
- Readback clauses in `Normalise`/`Quote`.
- Op signatures resolved from the trusted table.

Nothing else. No changes to Pi/Sigma/case/Eq machinery. The δ-gate at
`eval.ex:53` gains one rule: **an effect-typed global is categorically never
δ-unfolded**, independent of totality certification (§5.4).

## 5. Elaborator delta — closing the duplication/discard/reorder doors

This is where "sound from day one" is actually enforced. Each known hazard
site, and its closure:

### 5.1 Surface `let` substitution (the documented duplicator)

`elaborate_let_block` (elaborator.ex:879-890) eliminates `let x = e` by
substituting `e` at every use — its own comment says: *"this INLINES `e` at
each use (it does not bind-once)."* An effectful rhs routed through it would
duplicate the effect once per use and vanish at zero uses.

**Closure:** effectful `let` never reaches surface substitution. In a block,
when the rhs elaborates to type `Effect(T)`:

```
let x = e          ⇒   {:effect_bind, ⟦e⟧, {:lam, T, ⟦rest⟧}}   -- x : T, a REAL binder
rest
```

`x` binds the *result* (a `T`, not the `Effect(T)`), via a genuine Core
lambda — bound exactly once by construction. A bare effectful statement
(non-`let`) elaborates to `bind(e, λ_. rest)` with an unused binder — the
effect is explicitly sequenced, never dropped. The block's final expression
must itself be `Effect(R)` when any statement was effectful (no silent
escape from the effect type).

**Defense in depth:** `subst_surface_var` and `elaborate_let_block` assert
the rhs type is not `Effect(_)` before substituting; violation is an
internal error, not a miscompile. (Same pattern for any future surface
construct that substitutes: the guard lives at the substitution entry
points, not per-construct.)

### 5.2 NbE β-reduction

`Eval.apply` (eval.ex:85) β-reduces eagerly. Two cases:

- *Effect value passed to a pure function that uses it twice*: the value is
  shared in the environment during evaluation, but readback (`nf`) prints it
  twice — the normal *form* textually duplicates the effect term. This is
  harmless **because nothing consumes normal forms as code**: emit lowers
  the stored elaborated body (`Emit.def_body/2`), never a normal form, and
  kernel normalization is used only for typing judgements. And no
  definitional equation exists that could equate a two-occurrence normal
  form with anything that performs the effect a different number of times —
  inertness (§3.2) makes textual duplication semantically inert too.
- *Effect op in a type/index position*: stays a neutral-like inert value;
  conversion is congruent. (Also restricted — see §5.5.)

### 5.3 Relevance and erasure

`Relevance` (the {0,ω} check) gains: a binder of type `Effect(T)` — or whose
type's head is `Effect` — may **not** be declared `:erased`, and effect
nodes count as relevant occurrences everywhere. `Erase.erase` therefore
never encounters an effect node in a droppable position; a `Validator`
release clause (`no_effect_in_erased_position`, §8) is the trusted backstop,
in the same style as the existing hole-in-erased-position check (#102).

### 5.4 δ-unfolding

Globals unfold in conversion only when certified total (`eval.ex:53-54`'s
M7 gate). Extension: a def whose type mentions `Effect` is **never**
δ-unfoldable, even if certified. Types should rarely depend on effectful
calls at all, but the rule makes "conversion cannot look inside an effectful
definition" unconditional rather than incidental.

### 5.5 Effects in types

v1 restriction: `Effect(T)` may appear anywhere a type may, but an
`{:effect_op, …}`/`{:effect_bind, …}` term may not appear **inside a type or
index expression** (validator clause). An fsm indexed by an effect
computation has no sensible meaning under inertness; forbidding it early
avoids a class of stuck-index puzzles. Relaxation is ledgered.

### 5.6 Totality

Effectful defs still pass the size-change termination check. Handlers are
per-message and total; the forever-loop lives in the trusted OTP runtime
(`gen_server`'s own structure — the callback is total, the loop is the
framework's). An escape hatch for deliberately partial effectful functions
(`unsafe`?) is ledgered with the holes/unsafe taxonomy work.

## 6. Emission — the zero-overhead argument

Erasure leaves effect nodes intact (§5.3); `Emit` lowers them:

- **A def body of type `Effect(T)` lowers direct-style**: the bind-chain
  spine becomes a sequence of Erlang expressions —
  `bind(op₁, λx. bind(op₂, λy. pure(f(x,y))))` →
  `X = <op₁>, Y = <op₂>, f(X, Y)`. Each `{:effect_op, name, args}` becomes
  the direct BEAM call from the signature table. This is byte-for-byte the
  shape the bespoke fsm/actor compilers emit today.
- **First-class effect values** (an `Effect(T)` passed as an argument,
  stored in a structure, or returned un-run) lower as **thunks**: a nullary
  fun capturing the computation; `bind` on a dynamic effect value is
  "call the thunk, continue." Direct-style is the optimization of the
  dominant case (effect consumed where produced, i.e. every handler body);
  thunking is the uniform fallback that keeps first-class effects correct.
  One closure allocation per first-class effect value — and only there.
- `{:effect_pure, a}` in direct position → just `a`; as a first-class value
  → `fun() -> A end`.

Downstream safety: `erlc` cannot assume purity of remote calls, so it never
duplicates or eliminates the emitted `erlang:send/2` etc. There is no Core-
or emit-level DCE pass, and this spec forbids adding one that touches
effect nodes without extending the validator contract.

### Performance estimate

| scenario | vs. today's bespoke compilers |
|---|---|
| handler bodies / `start`-style effectful defs (direct-style) | **0%** — same direct calls, same shapes |
| first-class `Effect` values | one fun alloc + one call per value (rare; today's code cannot express this at all) |
| compile time | +small: four node kinds threaded through ~9 modules; no new search or solving |

There is no interpreter anywhere in this design, hence no interpretive
overhead to recover. AtomVM/ESP32 footprint is unchanged: what ships is
direct BEAM calls.

## 7. Macro-facility integration

The §14 callback ADTs
([macro facility design](macros/2026-07-08-macro-facility-design.md)) get
effect-typed handler fields:

```cure
# before (purity lie):            # after:
handle : State -> Msg -> Reply(State)
handle : State -> Msg -> Effect(Reply(State))
```

Two orthogonal axes now compose on the same field:

- **Discipline indices** (the FRP-index-algebra generalization): *which*
  handler is legal in *which* state — GADT indices, checked by ordinary
  conversion, erased at runtime.
- **Effect typing** (this spec): *what a handler may do* — `Effect` in the
  codomain, lowered to direct calls.

`lift module` receives Core values whose handler fields are effect-typed
lambdas; it emits them direct-style (§6) into the behaviour callbacks. The
fsm/actor reimplementation-via-macros work builds on exactly this pair.

## 8. Validator / release-config additions (trusted backstops)

New `Validator` release clauses, enforced at the single trusted emission
gate (`Emit.reject_holes`-style, emit.ex:93-112):

1. `no_effect_in_erased_position` — no effect node reachable under an
   erased ctor argument or erased binder.
2. `no_effect_in_type_position` — no effect *term* node inside a type/index
   or inside `rewrite` proof/motive or `refl`/`eq` argument positions
   (compile-time-only subterms must be effect-free).
3. `effect_ops_known` — every `{:effect_op, name, _}` names a table entry
   with matching arity.

## 9. Verification gate

- **Antigen seeds** for all four node kinds: σ-law/substitution cross-checks,
  nf-idempotence (the Pi oscillation precedent says: seed these on day one),
  conversion congruence, and a dedicated family asserting *inertness
  invariance* — for random well-typed effectful terms, `nf(t)` preserves the
  multiset and order of `{:effect_op, …}` occurrences along every spine.
- **Count-preservation differential test**: elaborate surface programs with
  N textual effect calls (including via `let`, blocks, duplicated-use
  patterns that route near `subst_surface_var`); assert the elaborated Core
  and the emitted Erlang forms contain exactly N op sites in source order.
- **Idris/Lean oracle pairs** (differential harness, `test/oracle/`): pure
  `IO`-shaped programs accepted/rejected identically; `bind(pure(a),k) ≠ k(a)`
  *definitionally* on both sides (conversion-failure parity).
- Full existing gate (kernel suite, frp cluster, oracle ledger) stays green.

## 10. Ledger (open decisions)

1. **Op inventory growth** — which fsm/actor runtime shims become ops vs.
   stay behind `extern_call`; criteria for admission to the trusted table.
2. **Existing `@extern` migration** — today's externs all claim purity.
   Sweep policy (warn? per-module opt-in? epoch flag) for re-typing the
   effectful ones as `-> Effect(T)`.
3. **Dependent `bind`** — needed only if a later result type must mention an
   earlier effect *result*; Lean lives without it in `IO`.
4. **Partial effectful functions** — escape hatch design; belongs with the
   holes/`unsafe` taxonomy wave.
5. **Effects in indices** (§5.5 relaxation) — revisit only with a concrete
   consumer.
6. **Selective reflection into data** — the effects-as-data spec's
   provability payoff (theorems like "sends exactly once") can be recovered
   *on top of* this design later by reflecting a fragment of the op algebra
   into an inductive for proof purposes. Deliberately out of v1.

## 11. Non-goals

- No algebraic effect handlers, no user-defined ops, no effect polymorphism
  rows (`Effect` is one monolithic effect in v1 — the BEAM's own "can do
  anything a process can" granularity).
- No kernel-side evaluation of effects under any flag, ever.
- No linearity interaction (grade-wave concern; `Effect` is ω like
  everything else in the {0,ω} slice).
