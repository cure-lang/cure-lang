# Typed BEAM Process Algebra — Correct-by-Typing OTP Access

**Date:** 2026-07-09
**Status:** design (operator-directed). Consumes the `Effect` inert type former
([`2026-07-09-effect-type-former-design.md`](2026-07-09-effect-type-former-design.md));
supplies the typed surface the macro facility's fsm/actor/sup/app reimplementations
([`macros/2026-07-08-macro-facility-design.md`](macros/2026-07-08-macro-facility-design.md)
§14) emit against.

**Decision (operator, 2026-07-09):** the BEAM process/OTP model is exposed to
Cure programs as a **typed algebra** — precise, dependent, indexed operation
signatures that make *incorrect use of the BEAM ops a compile error* — rather
than as a thin layer of `@extern` declarations with asserted signatures. The
typed algebra is the **only sanctioned surface**; the raw foreign base it is
built over is sealed (`unsafe`, internal). A process's accepted-message set is
modelled as a **code** (data describing the message set, §4), which is the
BEAM-native representation and the one that lets subsumption and reply-lookup
*compute*.

---

## 1. Purpose and locked decisions

Concurrency is where dependent types pay off most: the dominant real bug classes
on BEAM are *sending a process a message it does not handle*, *sending the right
tag with a wrong-typed payload*, and *using a reply at the wrong type* — all
invisible on the dynamically-typed substrate. Cure can turn them into type
errors. The operator locked:

1. **Type the whole process/OTP surface as an algebra**, not a set of loosely
   typed externs. Misuse is caught by the kernel checking the algebra, not by
   trusting a table.
2. **Rich types, inert values.** This composes with — does not fight — the inert
   `Effect` former: `send` still *computes* nothing at type-check time; only its
   *type* becomes precise. Inertness (Effect spec §3.2) is untouched.
3. **Minimal trust, maximal checking.** The algebra is ordinary kernel-checked
   Cure over a tiny raw base typed at honest BEAM signatures. The TCB does **not**
   grow; it shrinks relative to "one asserted extern per operation."
4. **The typed algebra is the only sanctioned surface.** The raw base is
   `unsafe` and internal to `Std.Otp`; deliberate raw access means the user
   writes their own `@extern`.
5. **A message type is a code, with payload shapes.** A pid is indexed by a
   *code* — data describing the set of tagged messages it accepts, each
   constructor carrying its payload field types — **derived** from the message
   ADTs / handler clauses, never hand-written, and **erased** at runtime (§4).
   This is the BEAM-native model (a mailbox *is* a set of tags-with-data) and the
   one under which `subset`/`union`/reply-lookup are ordinary computations.
6. **No subtyping.** Cure is conversion-based (Agda/Lean/Idris-aligned); it gains
   no `<:` judgment. "Use a wider pid where a narrower is wanted" is an explicit,
   runtime-identity coercion whose obligation `subset(narrow, wide)` is
   discharged **by computation**, not a subtyping rule (§5.5).
7. **Floor now, ceiling deferred.** The typed+codes floor (typed pids, dependent
   call/reply, behaviour conformance, computed subsumption) ships first; session
   /state discipline (indexed effects) is designed-in and landed later (§8, §10).

## 2. Architecture — layers over `Effect`

```
  user / macro-emitted code
        │  programs only against …
        ▼
  ┌─────────────────────────────────────────────┐
  │  Typed process algebra   (Std.Otp)           │  ← ordinary CHECKED Cure
  │  Pid(m), GenServer(c,k,i), send, call, …      │    m = a message-type CODE
  │  message-type codes + El + subset/union       │    (kernel verifies it)
  └─────────────────────────────────────────────┘
        │  narrows / is defined in terms of …
        ▼
  ┌─────────────────────────────────────────────┐
  │  Raw foreign base  (Std.Otp.Raw, unsafe)     │  ← the ONLY trust boundary
  │  raw_send : RawPid -> Any -> Effect(Unit) …  │    (honest permissive types)
  └─────────────────────────────────────────────┘
        │  lowers to …
        ▼
  stock erlang:/gen_server:/gen_statem: BIFs  +  the inert Effect former
```

The kernel checks that (a) the algebra is internally consistent and (b) user
code uses it correctly. The *only* asserted-not-proven facts are the raw base's
base signatures — irreducible, because you cannot prove properties of a foreign
runtime, only state its interface honestly.

## 3. The trust boundary

### 3.1 Raw base — sealed, `unsafe`, honest

A private module `Std.Otp.Raw`, every function an effect-typed `@extern` at its
**most permissive honest** BEAM type. It is the sole consumer of the
process/OTP BIFs and the sole thing tagged `unsafe` in this design.

| raw op | honest type | BEAM |
|---|---|---|
| `raw_send` | `RawPid -> Any -> Effect(Unit)` | `erlang:send/2` |
| `raw_self` | `Effect(RawPid)` | `erlang:self/0` |
| `raw_call` | `RawPid -> Any -> Effect(Any)` | `gen_server:call/2` / `gen_statem:call/2` |
| `raw_cast` | `RawPid -> Any -> Effect(Unit)` | `gen_server:cast/2` / `gen_statem:cast/2` |
| `raw_start` | `Module -> Any -> Effect(RawPid)` | `gen_server:start_link` / `gen_statem:start_link` |
| `raw_stop` | `RawPid -> Effect(Unit)` | `gen_server:stop` / `gen_statem:stop` |
| `raw_send_after` | `Int -> RawPid -> Any -> Effect(TRef)` | `erlang:send_after/3` |
| `raw_cancel_timer` | `TRef -> Effect(Unit)` | `erlang:cancel_timer/1` |
| `raw_spawn` / `raw_spawn_link` | `(Effect(Unit)) -> Effect(RawPid)` | `erlang:spawn` / `spawn_link` |
| `raw_exit` | `RawPid -> Any -> Effect(Unit)` | `erlang:exit/2` |
| `raw_link` / `raw_unlink` | `RawPid -> Effect(Unit)` | `erlang:link/1` / `unlink/1` |
| `raw_monitor` / `raw_demonitor` | `RawPid -> Effect(MRef)` / `MRef -> Effect(Unit)` | `erlang:monitor/2` / `demonitor/1` |
| `raw_process_flag` | `Atom -> Any -> Effect(Any)` | `erlang:process_flag/2` |
| `raw_is_alive` | `RawPid -> Effect(Bool)` | `erlang:is_process_alive/1` |
| `raw_register` / `raw_unregister` / `raw_whereis` | `Atom -> RawPid -> Effect(Unit)` / `Atom -> Effect(Unit)` / `Atom -> Effect(RawPid)` | `erlang:register/2` / `unregister/1` / `whereis/1` (raw registry, **not** Elixir `Registry`) |

`RawPid`, `TRef`, `MRef`, `Module` are opaque foreign-handle types declared
here. `Any` is the **foreign-boundary type**: every Cure value is representable
as an Erlang term, so the typed layer only ever *injects into* `Any` (a total,
information-losing embed), never projects out of it without a check. This is the
untyped FFI edge — **not** a top type in a subtyping lattice (there is no
subtyping, §6). Device/user FFI (`gpio`, `uart`, …) is *not* part of this base —
it stays ordinary user `@extern`, unrelated to the process algebra.

### 3.2 Sealing mechanism

`Std.Otp.Raw` is not re-exported by `Std.Otp`. Its `@extern`s carry the
`unsafe` tag (holes/`unsafe` taxonomy). The only module that imports it is
`Std.Otp` itself, whose typed wrappers (§5) inject/narrow the honest permissive
types to the precise ones. Consequences:

- User and macro-emitted code cannot reach `raw_*` — the typed algebra is the
  path of least (and only casual) resistance.
- A genuine raw need is met by the user's **own** `@extern`: explicit in their
  source, their asserted signature, greppable, deliberate — strictly better
  than a shared casual bypass. This directly answers the classic-ripout's
  "wayward agent wires to the unsound path because it exists" concern: there is
  no ambient untyped `send` to grab.

## 4. Message types as codes

The index `m` in `Pid(m)` is a **code**: an ordinary data value describing the
set of tagged messages a process accepts. This is the model, chosen over
"`m` is a type," because on the BEAM a mailbox *is* a set of tagged terms — the
tags a `gen_server`'s `handle_*` clauses match — so representing it as data is
both native and computable.

### 4.1 What a code is

A code is a set of message constructors, each a tag plus its payload field
shapes:

```
# conceptual shape of the code datatype (first-order universe)
MsgShape  = { tag: Atom, fields: List(TypeCode) }     # one constructor
MsgType   = Set(MsgShape)                              # an accepted-message set
```

`TypeCode` is a code for **first-order** Cure types (atoms, ints, floats,
strings, binaries, tuples, lists, user ADTs). The restriction to first-order is
not a compromise: BEAM messages are copied across process boundaries and must be
plain serialisable terms, so the message universe is *exactly* the first-order
fragment reality already imposes.

A decoder `El : MsgType -> Type` turns a code back into the sum type of legal
terms, so a value `msg : El(m)` is a real BEAM term of an accepted shape. **The
code is primary; `El(m)` is the definition of the message type the user sees** —
they cannot drift.

### 4.2 Codes are derived, not written

The user never writes a `MsgType`. It is projected, at compile time, from the
message ADTs and the handler clauses — the *same* source the macro compiles into
`handle_*`:

```cure
type AccountMsg = Balance | Deposit(Int) | Transfer(AccountId, Int)
# derived code:  { :balance/0, :deposit/1(Int), :transfer/2(AccountId, Int) }
```

Each constructor's declared field types *are* the payload shapes — so modelling
the data costs nothing beyond reading the ADT the program already declares. The
message-type code and the `gen_server` dispatch clauses are the same information
in two forms, produced together (§7).

### 4.3 Computable operations

Because a code is data, the operations subsumption and dispatch need are
ordinary total functions, discharged by computation:

```
handles : MsgType -> Atom -> Bool          # is this tag accepted?
subset  : MsgType -> MsgType -> Bool       # is a ⊆ b ?  (every shape of a is in b)
union   : MsgType -> MsgType -> MsgType     # combine two accepted sets
```

This is the inverse of a subtyping *judgment*: there is no `<:` rule in the
kernel; inclusion is a `Bool`-valued computation whose truth is checked by
normalisation (§5.5).

### 4.4 Erasure — zero device cost

The code index on `Pid`/`GenServer` is a **`0`-quantity (erased) argument**
(Cure's {0,ω} relevance). At runtime a pid is a bare `RawPid`; the code exists
only during checking. What ships to the ESP32 is `erlang:send(Pid, {:deposit,
100})` — no manifest, no schema, nothing. This is a hard requirement, enforced
by the erasure/relevance check and the release validator (§12).

## 5. The typed floor

Built entirely as checked Cure in `Std.Otp` over §3.1 and §4. Uses `Effect(T)`
exactly as the Effect spec locks it — **no new monad structure**.

### 5.1 Typed pids

```cure
type Pid(m)          # opaque; wraps a RawPid, indexed (erased) by a message-type code m

fn send(p: Pid(m), msg: El(m)) -> Effect(Unit) =
  raw_send(unwrap(p), inject(msg))     # inject : El(m) -> Any, total foreign embed
```

`send` accepts only a value the code `m` describes. `send(p, Deposit("100"))`
fails to check twice over: wrong-tag *and* wrong-payload are both caught, because
the code carries shapes.

### 5.2 `self` — typed by the ambient message type

`self` yields a pid at *this* process's own message-type code, known only inside
a behaviour that declares it (§7):

- Inside a behaviour whose code is `m`, `self : Effect(Pid(m))`.
- Outside any behaviour context, `self` has no typed code; a bare handle uses
  `self_raw : Effect(Pid(empty))` (the empty accepted-set — passable, not
  sendable-to). Whether `Pid(empty)` is the right encoding or bare `self` should
  simply be a type error outside a declared context is ledgered (§13.2).

The ambient code is threaded by `lift module`'s behaviour elaboration (§7).

### 5.3 Dependent call / reply

A call-code carries each request's reply type; `reply_of` looks it up — a pure
function on the code, **not** a type family or GADT:

```
reply_of : CallCode -> Atom -> TypeCode        # request tag → reply type (a lookup)

fn call(s: GenServer(calls, casts, infos), req: El(calls))
     -> Effect(El(reply_of(calls, tag_of(req)))) =
  narrow(raw_call(unwrap(s), inject(req)))

fn cast(s: GenServer(calls, casts, infos), msg: El(casts)) -> Effect(Unit) =
  raw_cast(unwrap(s), inject(msg))
```

`call(acct, Balance) : Effect(Int)`, `call(acct, Deposit(100)) : Effect(Ok)` —
the reply type is read out of the code. This closes the `gen_server:call`-returns-
`Any` hole and needs no type-level machinery beyond a lookup.

### 5.4 Behaviour conformance

`start_link` yields a handle whose channels are the behaviour's declared codes,
so handle and callbacks provably agree:

```cure
fn start_link(spec: ServerSpec(calls, casts, infos), arg: a)
     -> Effect(GenServer(calls, casts, infos)) =
  narrow(raw_start(module_of(spec), inject(arg)))
```

The §14.3 callback ADTs supply `(calls, casts, infos)`: `handle_call` handles
`calls` and produces `reply_of`, `handle_cast` handles `casts`, `handle_info`
handles `infos`. A callback whose handled shapes disagree with its channel code
fails checking — conformance is structural, not convention.

### 5.5 Subsumption by computation (no subtyping)

To use a `Pid(wide)` where a `Pid(narrow)` is wanted — safe exactly when
`subset(narrow, wide)` — the user applies a coercion, **not** a subtyping step:

```
fn narrow_pid(p: Pid(wide)) -> { subset(narrow, wide) } -> Pid(narrow)   # runtime-identity
```

The obligation `subset(narrow, wide) = true` discharges **by computation** for
concrete codes (the common case: no proof written, no search run) and by
`by search` for abstract ones. The coercion is runtime-identity — the raw pid is
unchanged, the code is erased — so it costs nothing at runtime. This keeps the
kernel conversion-based and decidable; there is no `<:` judgment anywhere.

> Subsumption is an **ergonomic enhancement, not a soundness requirement**: the
> floor's guarantee (send only what is handled) holds with invariant `Pid(m)`
> and no coercions at all. `narrow_pid` matters only when a pid crosses into
> code expecting a different code — real but secondary, and buildable last
> within the floor.

## 6. What lives where

- **Kernel / `Effect` former:** the four structural nodes + `extern_call`
  (Effect spec §3). No process ops, no stock BIFs.
- **`Std.Otp.Raw` (sealed, `unsafe`):** the raw base (§3.1) — the one trust
  boundary.
- **`Std.Otp` (checked, sanctioned):** the message-type codes, `El`,
  `subset`/`union`/`handles`, and the typed algebra (§4–§5) — what everything
  else programs against.

The provenance rule holds and is sharp: a stock BIF is *never* a kernel/vocab
entry — it is a raw-base extern, wrapped by the typed algebra. The effect
table's named-op vocabulary is reserved for BIFs *we* implement natively, of
which the process algebra needs **none**.

## 7. Macro-facility integration

fsm/actor/sup/app macros emit against the typed algebra, never the raw base:

- Callback bodies (`on_message`, `on_transition`, …) are checked Cure using
  `send`/`call`/`cast` at typed channels — misuse in a handler is a compile
  error like any other.
- Convenience-export wrappers (`start_link`, `send_event`, `get_state`) — today
  templated `GenServer.call`/`cast` bodies — become thin typed-algebra calls
  with `Effect(...)` returns, generated by the macro.
- `lift module`'s `behaviour` declaration establishes the ambient message-type
  code and the channel codes `(calls, casts, infos)`, **derived from the same
  handler clause list** the macro compiles into `handle_*` (§4.2), and threads
  them to the callbacks and to `self`.

Macro output is re-elaborated like hand-written code (facility §9), so it is held
to the same discipline — a macro cannot emit an untyped send any more than a user
can.

## 8. Staging — the vertical rollout

Three substantive rungs over the preconditions, each independently shippable;
stop at any rung and the language is coherent.

**Rung 0 — preconditions.** The classic rip-out merges; the macro facility +
`lift module` + §14 callback ADTs land; the inert `Effect` former lands. Nothing
below starts until these exist.

**Rung 1 — Externs. *Feature restored.*** Macros rebuild `actor`/`fsm`
(`sup`/`app` too) as `lift module` behaviours whose callback bodies and
convenience exports call effect-typed externs into `gen_server`/`gen_statem` (or
a rebuilt thin Cure runtime — the lowering-target fork, §13.1, is decided here).
Effects typed only as `Effect(T)`; pids raw; no message checking. *Done when* the
phase35/examples actor-fsm programs compile and run on generic-unix (and the
phase3 turnstile fsm on hardware), matching the old bespoke behaviour.

**Rung 2 — Sealed typed + codes floor. *Correct and BEAM-native.*** Introduces
`Std.Otp` over the now-`unsafe`-sealed `Std.Otp.Raw`; message-type codes derived
from the ADTs/clauses (§4); `Pid(m)`, `send`, dependent `call`/reply,
behaviour conformance, and computed subsumption (§5). Macros switch to emitting
against `Std.Otp`; the seal validator (§12) turns on. The floor ships **with**
codes — no intermediate plain-type index is built only to be replaced. *Done
when* wrong-tag and wrong-payload sends are compile errors, `call` returns the
looked-up reply type, "wider pid where narrower wanted" typechecks by
computation with no hand-written proof, the seal holds, existing programs still
compile (surface unchanged) but now type-checked, and the ESP32 build shows no
runtime footprint from the codes.

**Rung 3 — Session ceiling. *Enforces protocols over time.*** Indexed effect
`Effect(pre, post, T)`; session-state codes (allowed message set per state +
transitions — a richer code of which the floor's flat set is the one-state
degenerate case); operations carry pre/post; no-send-after-stop becomes a type
error; pids-in-messages (typed delegation). *Done when* "deposit only while Open;
Close → Closed where nothing sends" is compile-time enforced. (§10.)

**The property that makes this a good stack: the kernel is touched only at the
ends.** Rung 0 adds the inert `Effect` former; rung 3 adds indexed bind.
**Rungs 1–2 are pure elaborator + stdlib work — no TCB change.** So the whole
correctness floor *and* the BEAM-native computing codes land with zero further
kernel risk; the one research-grade, kernel-touching piece (the parameterised
monad) sits at the very top, where it can wait.

## 9. Honest limits (state up front; do not over-promise)

1. **The mailbox is dynamically typed.** A BEAM process can receive *anything*,
   and the runtime injects `{'EXIT', …}`, monitor `DOWN`, and system messages the
   code does not describe. The algebra governs **what you send through typed
   channels**, not the raw mailbox — the opt-in boundary Akka Typed draws.
   `handle_info`'s `infos` code is therefore a best-effort declared subset, not a
   totality claim over the mailbox.
2. **Foreign-boundary trust is irreducible.** That `erlang:send` truly delivers
   an `El(m)`-shaped term, that `gen_server:call` truly returns the looked-up
   reply, is asserted by the raw base's honest signatures — provable only about
   Cure code, never about the VM.
3. **The inject/narrow wrappers are the audited seam.** Each typed op embeds via
   `inject : El(m) -> Any` (total) and, for results, narrows a permissive raw
   type to the precise one. Injection is always safe; the result-narrows are the
   spot the release validator checks (§12) so a wrapper cannot widen the wrong
   way.

## 10. The ceiling — session / state discipline (rung 3, designed-in)

Encode message ordering and lifecycle — "no `send` after `stop`", per-state legal
operations, request/response session shape. This is the FRP index-algebra
generalization ([`frp`](2026-07-04-identity-type-as-inductive.md) lineage)
applied to concurrency, and it needs an **indexed effect**:

```
Effect(pre, post, T)          # legal from session-state `pre`, leaving `post`, producing T
```

- Session-state codes generalise §4's flat `MsgType`: a message set *per state*
  plus transitions. The floor's code is the single-state case, so the ceiling is
  an **enrichment of the same universe**, not a rewrite.
- Operations gain pre/post indices: `stop` moves to a `Stopped` state whose
  message set is empty → post-stop send is a type error.
- The discipline rides on **indices** (like FRP's `Dec`/`Init`) — **not** linear
  types (out per the post-parity teardown). No linearity machinery.
- It is a parameterised monad, strictly more than the inert non-dependent
  `Effect(T)`: real elaborator + kernel surface (indexed bind), research-grade
  (session types on BEAM: Links, Idris `ST`, typed protocols). Its own spec,
  landed once the floor is proven (§13.5).

## 11. Relationship to the `Effect` spec

This spec **consumes** `Effect`; it does not extend the former. One edit lands on
the Effect spec as a consequence (§3.3 there):

- The stock BIFs once listed in the trusted signature table (`send`, `self_pid`,
  `sleep`, `print`) move **out** into `Std.Otp.Raw` (raw externs) and `Std.Otp`
  (typed wrappers). The table's residual role is "BIFs we implement natively" +
  the generic `extern_call`.
- `TRef`/`MRef` are declared in `Std.Otp.Raw`, not fixed by the table.

## 12. Validator / release backstops (trusted)

At the single emission gate (Effect spec §8 style):

1. `otp_raw_sealed` — no module other than `Std.Otp` references `Std.Otp.Raw`
   (the seal is enforced, not merely conventional).
2. `no_widening_narrow` — a typed wrapper's result narrow must land at a type the
   raw op's result can inhabit; a wrapper that widens the *result* is rejected.
3. `unsafe_confined` — every `unsafe` process extern is inside `Std.Otp.Raw`.
4. `codes_erased` — no message-type code survives into emitted code; a `Pid`
   index reaching the backend un-erased is a release error (the zero-device-cost
   guarantee, §4.4).

## 13. Ledger (open decisions)

1. **Lowering target (Rung 1)** — externs into stock `gen_server`/`gen_statem`
   vs. a rebuilt thin Cure runtime. AtomVM reality (the manual-start
   `Cure.FSM.Runtime`) leans toward a runtime; decided when Rung 1 is built.
   Does **not** affect the codes or the floor's types, only the extern targets.
2. **`self` outside a behaviour** — `Pid(empty)` vs. `self` being a type error
   outside a declared context (§5.2). Ergonomics call.
3. **Codes: bespoke vs. reuse `schema`** — the message-type universe could be its
   own small first-order code type, or reuse the `schema` macro facility (a
   general data-description mechanism). Lean: bespoke for the floor, watch for a
   later merge into `schema`, to avoid a dependency on an unbuilt facility.
4. **Payload universe scope** — v1 first-order codes cover scalars, user ADTs,
   tuples, lists. Deep maps/records and **pids-in-messages** (typed delegation —
   a message code referencing another pid code, recursively) are deferred; the
   latter is ceiling-flavoured (§10).
5. **Ceiling scheduling** (§10) — the indexed-effect monad is its own spec; queue
   after the floor ships and the fsm/actor macros are proven against it.
6. **`handle_info` / system messages** — how much of `{'EXIT',…}`/`DOWN` to
   surface in the `infos` code vs. leave as an acknowledged untyped remainder.
7. **Registry typing** — `whereis` returns a `RawPid`; recovering a typed
   `Pid(m)` from a name needs a name→code association (a typed registry facade)
   or an explicit user-asserted cast. Design when named-process use returns.
8. **`unsafe` tag surface** — reuse the holes/`unsafe` taxonomy's keyword
   verbatim for the raw base, or a dedicated `@extern(..., unsafe: true)` form.

## 14. Non-goals

- **Not** the indexed-effect ceiling (§10) — designed-in, deferred to Rung 3.
- **Not** typing the raw mailbox or system messages beyond the declared codes
  (§9.1).
- **Not** subtyping — subsumption is computed over codes, not a `<:` judgment
  (§5.5).
- **Not** linear/affine resource tracking for timer/monitor refs — indices, not
  linearity.
- **Not** touching the inert-`Effect` kernel contract — rich types, inert values.
- **Not** device/user FFI — `gpio`/`uart`/etc. stay ordinary typed `@extern`,
  outside this algebra.
