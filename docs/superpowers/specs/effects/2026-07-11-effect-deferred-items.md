# Effect(T) — Deferred Items Ledger

**Date:** 2026-07-11
**Status:** historical ledger — the deferred items for the earlier inert
`Effect(T)` implementation. New deferrals belong in the implementation ledgers
of the 2026-07-21 computation, IR, and Lean specifications.
**Context:** the inert `Effect` former and its full pipeline landed end-to-end
(kernel former → surface type → `let`→`bind`+`pure` → erasure rule → validator →
direct-style emit; a real effectful program runs on generic-unix AtomVM). See
`2026-07-09-effect-type-former-design.md` and memory `effect-former-slice1-landed`.
Graded effect binders are being built separately (the linear-channel enabler); this
ledger covers everything else.

The governing principle throughout: **build a mechanism only when a real consumer
forces it.** Each item below has been checked against the checked-BEAM-concurrency /
`Std.Otp` design (`2026-07-10-checked-beam-concurrency-design.md`) and confirmed NOT
to block it (except where noted).

---

## 1. First-class Effect-value thunks (§6 completion)

**What.** Today an effectful def lowers DIRECT-STYLE: `bind(e, λx. body)` becomes a
`begin X = <e>, <body> end` block and runs when the function is called. That is
correct for the dominant case (effect consumed where produced) but only handles a
**literal-λ continuation**. An `Effect` value that is passed as an argument, stored
in a field, or returned un-run has no representation — a non-λ `{:effect_bind, e, k}`
currently hits the emit `raise`, and an `Effect` value in a non-tail position runs at
the wrong time (at construction, not when forced).

**The shape when built.** Per §6: a first-class `Effect` value lowers as a **thunk** —
a nullary fun capturing the computation (`{:effect_pure, a}` → `fun() -> A end`;
an effectful expression → `fun() -> <expr> end`); `bind(e, k)` on a dynamic (non-λ)
`k` is "run `e`, apply `k` to the result, force the resulting thunk"
(`begin X = <e>, (<k>(X))() end`). One closure allocation per first-class value, only
there; the direct-style path stays 0-overhead.

**Why deferred.** The behaviour-based OTP path does not need it: `gen_server`/
`gen_statem` callbacks *return* `Effect(...)` in tail position (run direct-style when
the framework calls them), and `start_link(Module, Arg)` takes an atom + data, not an
`Effect`.

**Trigger.** Any `Std.Otp` op — or user program — that passes an `Effect` as an
**argument**: a raw `spawn(body : Effect(Unit))`, a supervisor child-spec storing an
effectful start-fun, or any stored/deferred action. **Resolve first:** audit the final
`Std.Otp` API for an `Effect`-typed argument position. If none, this stays deferred; if
`raw_spawn`-style exists, build it before that op ships. Until then, a non-λ bind fails
LOUDLY at emit (a `raise`), never silently.

---

## 2. `effect_op` + the trusted signature table

**What.** A dedicated Core node `{:effect_op, name, args}` plus a small trusted table
(sibling of `core/builtins.ex`) mapping each op name → fixed Core signature + BEAM
lowering, for **native custom BIFs we implement** (a NIF with no honest stock MFA).
Kernel typing rule already specified (`2026-07-09` §3.1): `sig(op) = (T₁..Tₙ) →
Effect(R)`, arg-checked, result `Effect(R)`. Validator clause `effect_ops_known`
already registered (vacuous — no such node exists).

**Why deferred / YAGNI.** The typed process algebra needs **zero** native BIFs — the
spec is explicit that `send`/`self`/`sleep`/timers/`gen_server:*` are all stock
Erlang/OTP, reached as **postulated globals** (`@extern` with an `Effect(T)` return),
not ops. Externs are NOT ops (that resolution is why the whole `extern_call`
"per-declaration signature" problem dissolved). So the op family has no consumer.

**Trigger.** Cure implements an actual native effectful primitive with no honest stock
MFA. Build the node + table then (it is a closed, fixed-signature mechanism with no
per-declaration difficulty — that difficulty was unique to externs, which are globals).

---

## 3. `@extern` migration to `Effect(T)`

**What.** Existing stdlib `@extern`s all declare **pure** return types regardless of
behaviour (the "purity lie"). New effect-typed externs already work (surface `Effect(T)`
landed in slice b); this item is retrofitting the *effectful existing ones*
(`Std.Io`, timers, process ops as they get typed) to declare `-> Effect(T)`.

**Why deferred.** `Std.Otp.Raw` writes **new** effect-typed externs from scratch, so the
OTP library does not need any migration. Pure programs are unaffected by the lie. The
migration only matters where an existing effectful extern is called in an effect
context and its purity would let it be duplicated/reordered.

**Trigger + policy question.** A sweep policy is the open decision (`2026-07-09` §10.2):
warn, per-module opt-in, or an epoch flag. Do it when converting a stdlib module
(e.g. `Std.Io`) to the effect discipline, module-by-module, not as a big-bang.

---

## 4. Dependent `bind`

**What.** `bind : Effect(A) → ((a:A) → Effect(B(a))) → Effect(B(a))` where the
continuation's result type depends on the **runtime result** of the first effect. Today
`bind` is non-dependent (`B` may not mention the bound value), matching Lean's
`Bind.bind`.

**Why deferred.** The OTP floor does not need it. `call : GenServer(c,_,_) → (req:c) →
Effect(ReplyOf(req))` has a reply type that depends on the *argument* `req` — an ordinary
dependent **function** result (a Pi); `ReplyOf(req)` is a fixed type once `req` is in
scope, so binding the reply is non-dependent bind over a computed payload type. True
dependent bind was only needed for the rung-3 session ceiling `Effect(pre,post,T)`
indexed bind, which the checked-concurrency spec **overturned**. Lean lives without it in
`IO`.

**Trigger.** A program where a later *type* must mention an earlier effect's runtime
*result value*. Kernel change (the bind typing rule generalizes the codomain to a
dependent function; read `B` by instantiating the continuation's codomain at the bound
var instead of a fresh neutral).

---

## 5. CLI → dependent emit (the #18 classic rip-out)

**What.** The `cure` CLI `compile` command still routes through the **classic**
pipeline (`compiler/`, `types/checker`), which is effect-blind — so `cure-avm run` on an
effectful program fails in the classic type checker. Effectful programs run today only
via the **dependent** emit path (`Emit.module_forms` + `BeamWriter.compile_forms`/
`write_beam`, in-process or driven manually into packbeam + AtomVM).

**Why deferred / not-our-job.** Switching the CLI to the dependent emitter is the
**classic-pipeline deletion (#18)** initiative — auto-approved, gated on stdlib-green
(see memory `classic-pipeline-deletion` / `post-parity-teardown-batch`). It is not
Effect-specific; the dependent emit path used for effects is already correct and proven.

**Trigger.** The #18 rip-out. After it, `cure-avm run` compiles effectful programs
directly.

---

## Also-deferred (adjacent, not on any current critical path)

- **Surface grades on λ-*literals*** (`fn(x :linear) -> …` on an anonymous lambda). The
  graded *effect* binder gets its grade from the surface `let c :linear = …`, not from a
  lambda literal, so it does not need this. Grades on lambda-literal params remain
  unspellable at the surface until a consumer appears.
- **Graded constructor fields.** Representable in Core, unspellable at the surface; the
  other half of the QTT "surface grades on λ / ctor fields" deferral. No current consumer.
- **Effects in indices** (`2026-07-09` §5.5 relaxation) — an `{:effect_bind}`/`{:effect_op}`
  inside a type/index is forbidden (validator §8). Revisit only with a concrete consumer;
  under inertness an effect computation in an index has no sensible meaning.
- **Selective reflection of the op algebra into an inductive** for proof payoff (theorems
  like "sends exactly once") — `2026-07-09` §10.6. Deliberately out of scope; recoverable
  on top of the inert design later.
