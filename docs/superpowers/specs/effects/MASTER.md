# Effects — Master Specification

**Date:** 2026-07-21

**Scope.** This condenses the entire `specs/effects/` family: the current
normative computation/effect-row typing model, the dependent-effects and
stackless-Flow architecture (with BEAM Core-Erlang backend policy and the
Flow IR), and the historical records it supersedes — the surface `!`
discipline, the landed inert `Effect(T)` former, the rejected effects-as-data
alternative, and the old deferred-items ledger. It replaces reading the
individual specs; originals remain for archaeology.

## 1. Architecture and supersession chain

Three stages; only the last is authoritative for new work:

1. **Surface `!` discipline** (2026-07-07) — surface-only, erased before
   Core. Superseded; its soundness fixes remain migration guidance.
2. **Inert `Effect(T)` Core former** (2026-07-09) — landed end-to-end (a real
   effectful program runs on generic-unix AtomVM); superseded as the
   *semantic model*, remains implementation history.
3. **Computation/effect-row model + stackless Flow** (2026-07-21) — **current
   normative architecture**, split across two complementary canonical specs:
   the computation-typing spec owns typing rules, the dependent-effects/Flow
   spec owns language/runtime architecture; update together when a decision
   crosses both. A fourth path — effects-as-data (free monad + trusted
   interpreter) — was consciously evaluated and **rejected** (§8).

**The three layers (locked):**

1. **Values** (`Γ ⊢v v : A`) — the trusted dependent theory: types, indices,
   proofs, refinements, definitional equality. Runtime effects cannot enter
   this layer by being wrapped in a constructor.
2. **Computations** (`Γ ⊢c c : A ! ρ [ι]`) — produce values, carry effect
   info; never normalized as values by the kernel. Source keeps direct-style
   sequencing; `Effect(A)`/`Computation(A,ρ)` are not ordinary values.
3. **Flow frames** — explicit, defunctionalized, one-shot continuation state
   when a computation suspends across the ESP32 outer loop. A
   runtime/compiler artifact — never a proof term, index, or normalization
   object.

**Executive decision:** direct-style algebraic effects and explicit
monadic/flow composition are **two interfaces to one computation IR**. An
async boundary needs a continuation representation, not a native stack
unwind; on ESP32 that is a defunctionalized one-shot flow frame. Multi-shot
resumptions and dynamic handler capture deferred. No keyword spelling frozen.

## 2. Computation and effect typing (normative)

### 2.1 Judgments, value types, computation types

`A` is a value type, `ρ` a qualitative effect row, `ι` optional
indexed/refinement info; `Comp(A, ρ, ι)` is the computation type. Row and
index are separate: a label says *what op may occur*; an index describes
cost, protocol state, ownership, temporal facts, or a refinement summary —
only `(A, ρ)` are required initially. Types may depend only on a restricted
**IndexTerm** language of total, effect-free, ground values (variables,
literals, ctors, projections, certified pure primitives); a type may not
contain an unevaluated computation, a lambda/recursive closure, an effect
invocation, or a runtime Flow frame.

### 2.2 Effect rows

`ρ ::= {ℓ1, ..., ℓn | α}` with normalization, inclusion, union, and checked
subtraction. Each label has an `EffectDecl`:
`category : primitive | abstract | higher-order | suspend | concurrency |
foreign`, `handling : open | sealed`, `control : ordinary | suspending`.
Labels are nominal; primitive and abstract labels share one namespace so
effect closure computes uniformly. Category, sealing, and suspension are
independent properties. **A sealed primitive or sealed suspension cannot be
removed by an ordinary user handler.**

### 2.3 Selected typing rules

```text
Γ ⊢v v : A  ⟹  Γ ⊢c return v : A ! ∅ [1]
Γ ⊢c c₁ : A ! ρ₁ [ι₁]   Γ, x:A ⊢c c₂ : B ! ρ₂ [ι₂]
  ⟹  Γ ⊢c let x = c₁ in c₂ : B ! (ρ₁ ∪ ρ₂) [ι₁ ⋄ ι₂]
```

Applying `f : (A → Comp(B, ρ, ι))` to value `v` yields `B ! ρ[v/x] [ι[v/x]]`
(ordinary dependent substitution on values).

**Dependent sequencing restriction (locked, from Kura et al.):** initially
the continuation's row/index may not depend directly on the runtime result of
`c₁`; refinement substitution removes the dependency when a checked value
relation proves the required equality/predicate. Permitted early: indices on
values already in context; result refinements rewriting/bounding an index;
pure computations safe for ordinary dependent substitution. Deferred:
runtime-result-dependent rows; executing a suspended computation to discover
a type; effectful terms in refinement predicates; dependent equality needing
handler execution. A soundness boundary, not a permanent rejection.

### 2.4 Handlers

A handler has handled labels `H`, return clause, operation clauses, mode, and
continuation-ownership policy:
`handle c with h : B ! ((ρ \ H) ∪ ρ')` given `c : A ! ρ`, `h` handles
`H ⊆ ρ` and returns `B ! ρ'`. Admissible only if every handled op has a
compatible clause, the return path is typed, and **sealed effects are not
removed**. Deep-vs-shallow is a semantic field, not an optimization choice.
User handlers interpret **abstract** effects only; **sealed runtime effects**
(suspension, foreign calls, selected OTP/device primitives) are lowered only
by the compiler/runtime. Handling must not erase the fact that the handler
itself suspends, allocates, or performs another sealed effect.

### 2.5 Higher-order / latent effects

An op receiving or storing a computation records its **latent** computation
type separately from the caller's immediate effects, e.g.
`runLater : Deferred(Comp(A, ρ, ι)) → Comp(B, {runLater}, ι')` — `ρ` is not
performed at scheduling time, and the op is not first-order merely because
the computation is a closure. Callbacks, process children, supervisor bodies,
resource brackets, and deferred device work retain latent rows for deployment
closure checking; a child process's effects are not charged to the spawner,
but its computation type retains them for deployment/supervision.

### 2.6 Suspension

`Suspend` is a **sealed, suspending** effect (name provisional, surface
spelling deliberately deferred): execution may return to the outer
scheduler/event loop before producing the result. It propagates through calls
and latent higher-order types — a caller of
`read_sensor : Unit -> Sample ! {Device.Sensor, Suspend}` is suspending even
unannotated. User code cannot forge a scheduler continuation or remove
`Suspend` with an ordinary handler; the scheduler/runtime owns the boundary.

### 2.7 Foreign operations

Every foreign op declares name, argument/result types, effect row,
capability, failure behavior, ownership/resource behavior. **An FFI call
without a declaration is rejected.** Deployment closure checks all reachable
foreign capabilities.

### 2.8 Lean requirements and initial restrictions

The Lean middle-end provides checked row union/inclusion/subtraction,
effect-category validation, dependent substitution over values, computation
typing, handler effect accounting, latent-effect propagation, and deployment
effect closure — via explicit derivations or intrinsically typed IR values
after JSON validation; **raw decoded syntax must not be accepted by lowering
functions.** First theorem-bearing scope: first-order effects, one-shot
continuations, sealed primitives, conservative dependent sequencing.
Deferred: multi-shot handlers, arbitrary answer-type modification, effectful
dependent indices, full higher-order handler composition.

### 2.9 Consolidated decisions carried forward

Surface `!` may remain as syntax/diagnostics, but computation typing + rows
are authoritative. Inert `Effect(T)` is implementation history;
effects-as-data is not required. Computation values, latent effects,
handlers, and suspension are distinct concepts — never collapsed into one
opaque runtime wrapper. Deferred work lives in the Lean middle-end / multi-IR
implementation ledgers, not a competing `Effect(T)` spec.

## 3. Kernel and normalization boundary (non-negotiable)

Forbidden: effectful computations in dependent indices or proof bodies;
foreign execution during normalization; handler execution during conversion;
treating `Effect(A)` as an escape hatch into the value universe; using
qualitative rows as proofs of exact operation counts; using an indexed grade
as evidence without a checked refinement/certificate; placing dependent
grades directly into the qualitative runtime row namespace (indexed grades
are a separate, value-checked layer).

## 4. Stackless Flow and the Flow IR

Stackless is not free: a resuming handler still preserves the continuation,
captured locals, handler state/nesting, success/failure/timeout/cancel paths,
and resource ownership across suspension — hence an explicit defunctionalized
state machine on ESP32. **Initial ESP32 policy (locked):** one-shot
resumptions only; linear/affine treatment where ownership requires; no
multi-shot continuation duplication; no handler capture that can't live in a
flow frame; explicit bounds/diagnostics for frame size and suspension depth
where enforceable. Non-suspending ops lower as direct calls; handlers that
never cross a suspension boundary compile locally without a persistent frame.

**Flow IR** — properly a *typed defunctionalized computation/flow IR*: the
standard CPS-conversion → defunctionalization → abstract-machine pipeline,
made typed with effects, kernel boundaries, and one-shot guarantees.
Entities: `FlowProgram` (entry state, state defs, effect transitions,
terminal return/failure), `FlowState` (id, captured fields, current step,
handler fields, transitions), `FlowFrame` (continuation state id, captured
values, expected result type, remaining effect obligations, one-shot
ownership status). **Fixed invariants:** (1) every suspended continuation has
an explicit frame or statically known state transition; (2) frame fields are
typed independently of the value kernel — effectful computations never enter
definitional equality or proof normalization; (3) each resumption consumed at
most once, multi-shot cloning rejected until duplication/ownership/
answer-state changes have a formal account; (4) one Computation IR lowers to
direct BEAM calls, Core Erlang flow dispatch, or a C/ESP32 scheduler loop;
(5) Flow IR appears only where a computation can suspend, cross a
handler/process boundary, or need a restricted-runtime scheduler — pure
straight-line code is never framed.

**Implementation order:** value/computation split + rows → Computation IR +
typing → CPS + defunctionalization into Flow IR → verify a pure/effectful
pair and a suspension/resumption pair → actor/process/mailbox transitions
preserving latent effects → lower to Core Erlang (BEAM) and scheduler loop
(C/ESP32) → abstract handlers with one-shot resumptions last. Every step runs
the full kernel/Antigen/compiler/BEAM/AtomVM gates; ESP32 flow additionally
requires a real device-observed suspension/resumption test.

## 5. BEAM backend policy

**Lower to Core Erlang** — not Erlang abstract forms, not BEAM bytecode:
`Cure AST → value/computation IR → Flow IR (where required) → Core Erlang →
OTP compiler → BEAM`. Core Erlang is the better semantic boundary and has a
machine-checked concurrent formalisation (Rocq 9.1, frame-stack semantics;
clone at `algebraic-effects/core-erlang-formalization/`, commit `4a59339c…`)
as a future verified-translation target. It does **not** replace the
Computation/Flow IRs — those carry Cure's proofs, rows, latent effects, and
one-shot guarantees, discharged before the boundary. Target a **versioned
Core Erlang subset/encoder**, not the unstable internal OTP `cerl` API
(adapter isolated behind a backend module, output tested through the
installed OTP compiler); unsupported OTP features **fail closed** — no opaque
escape nodes. Direct bytecode emission is rejected as a first backend
(premature coupling to a versioned object format/loader contract). Proof
boundary: first prove `Cure computation/Flow IR semantics ≈ Core Erlang
semantics of the generated program`; this proves neither the OTP compiler nor
AtomVM correct. For C/ESP32 the same IR lowers directly to C state machines +
scheduler calls; Core Erlang is the BEAM target, not a universal IR.

## 6. Historical: surface `!` discipline (2026-07-07, superseded)

Smallest honest fix for the advertised surface effect system; effects erased
before Core. Four defects: violations only emitted diagnostics; unannotated
functions never checked; name-table inference; higher-order application
laundered callback effects to pure. Existing subeffecting sound and preserved
(`{:effun,e1} <: {:effun,e2}` iff `e1⊆e2`; pure usable where effectful
expected). Design, still valid as migration guidance: effects form a
join-semilattice over `:io/:state/:exception/:spawn/:extern` (⊥ = ∅, join =
union, order = subset). **Default-pure, mandatory** — no `!` means declared
`∅`, still checked; undeclared effect use = hard error **E091**;
over-annotation = warning (sound upper bound); an extern's explicit `!` must
equal its classification. Type-driven inference: effects originate only at
`@extern` (module-classification tables = trusted FFI ground truth) and
intrinsics (`send`/`receive` → `:state`, `throw` → `:exception`, `spawn` →
`:spawn`); all else propagates via signatures in the env; name tables
removed. Higher-order: read the callback's type; a statically unknown effect
set contributes conservative ⊤.

## 7. Historical: inert `Effect(T)` (2026-07-09/11 — landed, superseded as model)

Locked decisions at the time: former named `Effect`; **inert in the kernel**
(zero equations — no monad laws, no η, no commuting conversions;
`bind(pure(a),k) ≢ k(a)` definitionally; conversion = congruence only — the
Lean `IO` shape); **sound from day one** — every duplication/discard/reorder
door closed in the design. Landed end-to-end: kernel former → surface type →
`let`→`bind`+`pure` → erasure rule → validator → direct-style emit. Key
mechanisms: four dedicated Core nodes
`{:effect_type|effect_pure|effect_bind|effect_op}` (not stuck-prims — passes
enforce by shape), `bind` non-dependent in v1. **Hazard closures:** effectful
`let` never reaches surface substitution — it elaborates to a real
`{:effect_bind, e, {:lam, T, rest}}` binder (bound exactly once); bare
effectful statements become `bind(e, λ_. rest)`; substitution entry points
assert rhs is not `Effect(_)`; `Effect`-typed binders never `:erased`; effect
nodes always relevant; effect-typed globals never δ-unfolded even if
certified total; effect *terms* forbidden inside types/indices.
**Emission:** bind-chains lower direct-style to straight-line Erlang —
byte-identical to the bespoke fsm/actor compilers, **0% overhead**, no
interpreter; validator clauses `no_effect_in_erased_position`,
`no_effect_in_type_position`, `effect_ops_known`. The op table stayed
**empty of process/messaging ops**: `send`/`self`/OTP are stock BIFs reached
as effect-typed `@extern` postulated globals via sealed `Std.Otp.Raw` + typed
algebra `Std.Otp`; raw `receive`/`spawn` remain rejected (E043). Handlers are
per-message and total; the forever-loop lives in the trusted OTP framework.

**Deferred-items ledger (2026-07-11, historical; new deferrals → Lean/IR
ledgers).** Principle: build only when a real consumer forces it; none block
`Std.Otp`. (1) First-class Effect-value **thunks** — only literal-λ
continuations emit, a non-λ bind fails loudly; trigger: an `Effect`-typed
argument position (`raw_spawn`-style) in the final `Std.Otp` API. (2)
`effect_op` + trusted signature table — YAGNI, the process algebra needs zero
native BIFs; trigger: a native primitive with no honest stock MFA. (3)
`@extern` migration off the purity lie — module-by-module; sweep policy open
(warn / opt-in / epoch flag). (4) Dependent `bind` — OTP doesn't need it
(`ReplyOf(req)` is Pi-dependence on the argument, not the effect result). (5)
CLI → dependent emit — belongs to classic-pipeline deletion (#18). Also
deferred: surface grades on λ-literals/ctor fields; effects in indices;
reflecting the op algebra into an inductive for proofs.

## 8. Rejected: effects-as-data (free monad, 2026-07-09)

`EffectM(A)` as an ordinary inductive (CPS ctors) interpreted by a ~50-line
trusted runtime. Pros: zero kernel lines; effects provable as data; mock-free
testing; duplication hazards vanish. Costs: CPS/DSL ergonomics; ~3–10× naive
overhead on effect-dense handlers (unacceptable on AtomVM/ESP32); NbE staging
(first Futamura projection — `nf` specializes handler trees to direct code,
δ-certification as throttle) recovers 0% overhead **but relocates and grows
the TCB** into a tree-walking staged emitter. **Why it lost:** ergonomics
(operator priority); post-staging trust accounting inverts its headline
advantage; provability recoverable later by reflecting an op fragment into an
inductive on top; performance only ties after building the staging pass.
**Revisit if:** kernel-inertness proves structurally buggy; proof-carrying
effect protocols become a headline feature; a verified-compilation push wants
staged-emit-from-normal-forms.

## 9. Research conclusions (condensed review log, 2026-07-21)

- **Kura et al. (dependent effect systems):** source of the value/computation
  split, value-dependent grades, no-effectful-execution-during-conversion,
  and the conservative `let` rule (§2.3).
- **Kura (categorical semantics of handlers):** monadic API, direct
  semantics, and CPS/defunctionalized lowering can all model **one** typed
  calculus; lowerings must preserve handler equations.
- **Kawamata et al. (ARM):** supports sealed runtime effects + explicit frame
  storage; CPS translation is an internal cross-check only.
- **van den Berg & Schrijvers:** scoped/parallel/latent/bracketing effects
  need latent computation types, not a flat row; on ESP32 lower to explicit
  frame fields, never an interpreted tree.
- **van der Rest et al.:** affine (≤1) continuation use preserves handler
  separation — independent support for one-shot; intentional handler
  interaction must be encoded in types (future separation-law test).
- **Frank:** closest source-language precedent (value/computation split,
  ambient effect polymorphism, small core) — but its value-like suspended
  computations must **not** enter Cure's trusted value universe; also: no
  continuation allocation for once-invoked handlers, linear continuation
  typing, session-indexed interfaces.

## 10. Terminology

**Value / computation / flow frame** — the three layers (§1).
**Effect row (ρ)** — qualitative nominal label set + row variable.
**Index (ι)** — quantitative/refinement info, value-checked, separate from ρ.
**Latent effects** — a stored/deferred computation's row, carried by its
type, not charged at scheduling. **Sealed vs abstract** — sealed removable
only by compiler/runtime; abstract handleable by users. **Suspend** — sealed
suspending marker, provisional name. **Flow IR** — typed defunctionalized
computation/flow IR. **IndexTerm** — the restricted value language types may
depend on. **Purity lie** — legacy `@extern`s declaring pure types regardless
of behavior. **Inertness** — zero definitional equations for effect nodes
(historical `Effect(T)` contract).

## Source specs

- `README.md` — family index; declares the two 2026-07-21 docs canonical.
- `2026-07-21-cure-computation-effect-typing.md` — normative typing spec:
  judgments, IndexTerm, rows/EffectDecl, typing + handler rules, latent
  effects, suspension, FFI, Lean requirements (§2–3 here).
- `2026-07-21-dependent-effects-and-stackless-flow-design.md` — companion
  rationale: three layers, sequencing restriction, handler/kernel boundaries,
  ESP32 one-shot policy, Flow IR + invariants, Core Erlang backend policy,
  paper review log (§1, §3–5, §9).
- `2026-07-09-effect-type-former-design.md` — historical: the landed inert
  `Effect(T)` former — nodes, inertness contract, hazard closures,
  direct-style emit, validator backstops (§7).
- `2026-07-11-effect-deferred-items.md` — historical `Effect(T)` deferral
  ledger with build-on-consumer triggers (§7).
- `2026-07-07-sound-effect-discipline-design.md` — historical surface
  `!`-soundness repair: default-pure, E091, type-driven inference (§6).
- `2026-07-09-effects-as-data-design.md` — rejected free-monad alternative
  with the NbE-staging (Futamura) insight and revisit conditions (§8).
