# `workflow` & `bot` — Reducers at Business Timescale and Against Humans

**Date:** 2026-07-08
**Status:** design (operator-requested). Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
(§7.3); sibling of
[`2026-07-08-protocol-macro-design.md`](2026-07-08-protocol-macro-design.md)
(a bot conversation is morally a session — §7 below). Both surfaces are built
as `macro`s (parent §5) and both are **specializations of `reducer`**
(parent §5.5) — host-side, full BEAM, no MCU constraints.

---

## 1. Purpose

`reducer` gave Cure a state machine whose payload *type* depends on its state,
with typed emissions and a `Signal.scan` lowering. That design was built for a
door motor — but nothing in it says "milliseconds." This spec points the same
machine at two domains where the step interval is minutes to months and the
peer is a database or a human:

- **`workflow`** — event-sourced business processes (Order → Paid → Shipped).
  A reducer whose model persists, whose emission log *is* the audit trail,
  and whose clock ticks in days.
- **`bot`** — conversational agents (Telegram/Discord/Slack/MQTT). A reducer
  per user, one BEAM actor per conversation, where the transition graph makes
  nonsensical dialogue *inexpressible*.

The pitch for both is the same inversion: the industry builds workflow engines
and bot frameworks as *runtime* systems that discover invalid transitions in
production. Here the transition discipline is the type system, so an invalid
business step or an out-of-order conversation turn is a **compile error in
business vocabulary** (parent §3 principle 2, §4).

## 2. `workflow` — the surface

A `workflow` is a `reducer` plus exactly three things: persistence, wall-clock
timers, and human decision points. Everything else — per-state payload schemas,
typed emits/rejects, guard-refinement flow, the mandatory catch-all — is
inherited verbatim from parent §5.5.

```cure
type OrderEmit =
  InvoiceIssued(ref: InvoiceRef)
  | PaymentCaptured(ref: PaymentRef)
  | Dispatched(tracking: TrackingId)
  | Refunded(ref: PaymentRef, amount: Money)
  | Expired

type OrderReject =
  InvalidTransition(source: Order.State, msg: Order.Msg)

workflow Order
  store: Std.Store          # schema-backed persistence (capability, like clock)
  clock: Std.Clock
  emits: OrderEmit
  rejects: OrderReject

  Draft           --Submit-->        AwaitingPayment
  AwaitingPayment --PaymentReceived--> Paid
  AwaitingPayment --Expire-->        Cancelled
  Paid            --Ship-->          Shipped
  Paid            --RefundRequested--> Cancelled

  Draft over {
    customer: CustomerId
    items: List(LineItem)
  }

  AwaitingPayment over {
    customer: CustomerId
    items: NonEmpty(LineItem)
    total: Money
    invoice_ref: InvoiceRef
  }

  Paid over {
    customer: CustomerId
    items: NonEmpty(LineItem)
    payment_ref: PaymentRef
    paid_at: Instant
  }

  Shipped over {
    payment_ref: PaymentRef
    tracking: TrackingId
  }

  Cancelled over {
    reason: CancelReason
  }

  init: Draft { customer: ..., items: [] }

  fn body =
    on Submit from Draft with (payload, _)
      when payload.items != [] ->
        let inv = invoice(payload.items)
        emit <| AwaitingPayment {
          customer: payload.customer,
          items: as_nonempty(payload.items),
          total: inv.total,
          invoice_ref: inv.ref
        } <| InvoiceIssued(ref: inv.ref)

    on PaymentReceived from AwaitingPayment with (payload, clock) ->
      emit <| Paid {
        customer: payload.customer,
        items: payload.items,
        payment_ref: msg.ref,
        paid_at: clock.now
      } <| PaymentCaptured(ref: msg.ref)

    after 3d in AwaitingPayment ->
      emit <| Cancelled { reason: PaymentTimeout } <| Expired

    await approval from :finance in Paid on RefundRequested with (payload, _) ->
      emit <| Cancelled { reason: Refunded }
           <| Refunded(ref: payload.payment_ref, amount: msg.amount)

    on Ship from Paid with (payload, _) ->
      emit <| Shipped {
        payment_ref: payload.payment_ref,
        tracking: dispatch(payload.items)
      } <| Dispatched(tracking: msg.tracking)

    on _ with (model, msg) ->
      reject InvalidTransition(model.state, msg)
```

The typestate payoff, concretely: the refund clause reads
`payload.payment_ref` — a field that **only exists in `Paid`'s schema**. Move
that clause to `from AwaitingPayment` and it does not typecheck; there is no
payment reference to refund because no payment happened. "You cannot refund an
unpaid order" is not a code review comment or a runtime guard — it is the
`{:no_field, ...}` explainer (§5). The business rule is structural.

### 2.1 Event sourcing by construction — the centerpiece

This is not a feature added to `reducer`; it **falls out of the §5.5 design**
and this macro's job is mostly to say so and persist it:

- The reducer's `Step` already separates `model` from `emission`. The
  emissions are exactly what an event-sourcing system calls the event log —
  typed, per-instance, ordered.
- The current state is, by the lowering's own definition, `Signal.scan` over
  the message history — **state = fold of events**, the event-sourcing
  equation, already literal in the generated code.
- Replay is therefore not a subsystem: rerun the same `scan` over the stored
  history and you must reach the same model. Audit, debugging ("what did this
  order look like last Tuesday"), and read-model rebuilds are all the same
  one-line fold.

`workflow` adds the persistence: each instance's message history + emission
log lives in a `schema`-backed store (the `store` capability above; schemas,
columns-as-refinements, and the storage backends are the `schema` macro's
business — [`2026-07-08-schema-macro-design.md`](2026-07-08-schema-macro-design.md)).
Because emissions are typed against `OrderEmit`, the audit log is not strings
in a table — it is a schema the `view`/`api` macros can render directly.

### 2.2 Wall-clock time — durable timers

`after 3d in AwaitingPayment -> …` declares a timeout transition. Unlike
`reducer`'s `Signal` clock (sampled or merged per parent §9.9), a workflow
timer must **survive restarts and deploys** — a 3-day timer that dies with the
process is a bug generator. Design:

- Entering a state with an `after` clause writes a **due-time row**
  (`instance_id`, `state`, `due_at`) to the store, in the same transaction as
  the step's persistence. Leaving the state deletes it.
- A single per-node timer sweep scans due rows and injects the timeout as an
  ordinary internal message into the instance's actor — so in the reducer
  lowering it is just another merged message, exactly the Debounce
  `InternalTick` pattern from parent §5.5. No new reducer semantics.
- On node restart, the sweep resumes from the store; pending timers are data,
  not process state. Recovery is a query, not a special case.
- Firing is transactional with the step: a timeout that fires but whose step
  fails to persist re-fires (at-least-once, idempotent by construction since
  `after 3d in AwaitingPayment` is a no-op unless the instance is still in
  `AwaitingPayment`).

Granularity is coarse (seconds, not milliseconds) — stated in the docs;
workflows are not `flow`.

### 2.3 Human-in-the-loop

`await approval from :finance in Paid on RefundRequested -> …` is sugar, not
machinery: it lowers to (a) an emission recording that a decision was
requested (who, what, when — into the same event log), and (b) a declared
message (`ApprovalGranted` / `ApprovalDenied`-shaped) that delivers the
decision and is only receivable in that state. Approvals are just messages;
the reducer already knows how to wait.

The dividend: a `view`/`api` admin surface renders **pending approvals for
free** — they are exactly the requested-decision emissions not yet followed by
a delivering message, a fold over the log the macro ships as a template
query. Nobody builds an inbox table; the event log *is* the inbox.

### 2.4 In-flight migration

Deploys happen mid-process; an order three weeks into `AwaitingPayment` must
survive a schema change to `AwaitingPayment over {…}`. This is the `schema`
spec's problem, deliberately not duplicated here: workflow models are
schema-backed, so the **totality-checked migration chain**
(`2026-07-08-schema-macro-design.md`) applies to them like any other stored
record — every historical shape has a checked, total path to the current one.
What this spec adds is the *semantics* question (migrate in place vs. drain
old-version instances on their old definition), which is a genuine fork —
ledgered (§8.3).

## 3. `bot` — the surface

A `bot` is a reducer whose peer is a human and whose sessions are actors. The
parent's §7.3 Support sketch, expanded:

```cure
bot Support
  clock: Std.Clock
  emits: SupportEvent           # analytics stream — same emission machinery

  Idle     --Start-->     Menu
  Menu     --BrowseItem--> Ordering
  Ordering --AddItem-->   Ordering
  Ordering --Pay-->       Done
  Ordering --Cancel-->    Menu

  Idle     over { user: UserId }
  Menu     over { user: UserId }
  Ordering over { user: UserId, cart: NonEmpty(LineItem) }
  Done     over { user: UserId, receipt: Receipt }

  init: Idle { user: session.user }

  fn body =
    on Start from Idle ->
      say("Hi! What do you need?") then Menu { user: payload.user }

    on BrowseItem from Menu with (payload, _) ->
      ask("Which item?") expecting Sku
        then Ordering { user: payload.user, cart: cart_with(msg.sku) }

    on AddItem from Ordering with (payload, _) ->
      say("Added.") then Ordering { user: payload.user,
                                    cart: payload.cart.push(msg.item) }

    on Pay from Ordering with (payload, _) ->
      let receipt = checkout(payload.cart)
      say("Paid — receipt " <> show(receipt.id))
        then Done { user: payload.user, receipt: receipt }

    after 10m in Ordering ->
      say("Still there? Your cart is waiting.") then Ordering { ..payload }

    on _ with (model, msg) ->
      say(explain_unavailable(model.state, msg))   # re-prompt, never crash
```

Conversation typestate is the same structural argument as §2's refund: the
`Pay` clause requires `from Ordering`, and only `Ordering` has a `cart` —
"ask for payment before a cart exists" is inexpressible, not rejected. The
graph *is* the dialogue design.

### 3.1 Sessions = actors

One user's conversation = one actor holding one reducer instance. This is
BEAM's exact sweet spot: 10k concurrent conversations is an unremarkable
Tuesday, isolation is per-process (one user's crash re-prompts one user), and
idle sessions hibernate. Session lifecycle (spawn on first message, timeout to
termination after declared inactivity) is the macro's generated supervisor —
users never write it. Long-lived session persistence rides the same store
machinery as `workflow` (a bot session that must survive restarts is just a
small workflow).

### 3.2 Routing and platform adapters

A **platform adapter** normalizes each platform's webhook/socket traffic
(Telegram, Discord, Slack, or MQTT for device-facing bots) into the bot's
typed `Msg` values and routes by platform user id to the session actor.
Adapters are **packages, not compiler work** — the macro defines the
adapter-facing interface (deliver typed `Msg` in, receive `say`/`ask` render
calls out; interface details ledgered §8.5) and ships a reference adapter.
Parsing free-text into a typed `Msg` is the adapter's problem, by whatever
means it likes (§9).

### 3.3 `say` / `ask expecting` — and the explainer payoff

- `say(text)` renders a message to the user via the adapter.
- `ask(text) expecting T` sends a prompt and types the *reply*: the adapter's
  raw string is run through `T`'s parser/refinement (`Sku`, `{n: Int | n > 0}`,
  a `parse` grammar — the same machinery everywhere else). On success the
  clause receives a `T`; on failure the session **stays in its state and
  re-prompts** — and the re-prompt text is the refinement's **explainer**
  rendered for the end user.

That last point is worth savoring: the error-explainer architecture (parent
§4) was built to talk to Cure programmers; here it talks to the bot's *end
users*. "Quantity must be between 1 and 20 — you sent 0" is the same
refinement, explained once, serving both audiences. A `parse`/refinement
failure is never a crash and never a silent drop — it is dialogue.

- `after 10m -> …` timeouts (nudges, cart-abandonment reminders, session
  expiry) use §2.2's durable-timer machinery unchanged.

## 4. Invisible machinery (both surfaces)

- Per-state payloads = the state-indexed GADT model from parent §5.5;
  clause-scoped field access is index refinement. Zero new type-system work.
- Event log typing = the reducer's `Option(emits)` stream, given a schema.
- `after` = merged internal messages (the Debounce pattern) + a store-backed
  due-time sweep. `await approval` = one emission + one message. `ask
  expecting` = a parser at the adapter boundary + a self-loop on failure.
- Totality: size-change gives "a step provably terminates" — for `workflow`
  that is "the engine cannot wedge an instance"; for `bot`, "no user input
  can hang a session."

## 5. Explainers

Following the parent §4 template (what you wrote → why forbidden → what
instead), registered by this macro:

```
error[E175]: an order in AwaitingPayment has no payment to refund
  --> order.cure:71
  This clause reads payload.payment_ref, but that field only exists once
  the order is Paid (payment_ref appears in `Paid over {…}`, order.cure:34).
  Handle RefundRequested `from Paid`, or add a cancellation path for
  unpaid orders instead.

error[E176]: Support cannot receive Pay in state Menu
  --> support.cure:48
  The graph has no edge Menu --Pay--> …. A user in Menu has no cart yet.
  Route them through BrowseItem first, or add the edge if paying from the
  menu is intended.

error[E177]: workflow Order must end with a catch-all
  (inherited from reducer: `on _ with (model, msg) -> …` — for a bot this
  is also your "I didn't understand that" reply, so you want it anyway.)
```

## 6. `check` integration

Shipped templates (parent §7.5 macro-template mechanism), atop `reducer`'s
inherited graph-conformance and init-validity templates:

- **Replay determinism** (`workflow`): generate a message sequence, run it,
  persist, then fold the stored event history — the fold must reach the same
  model. This tests the persistence glue; the fold-equation itself is the
  lowering's definition.
- **Timeout reachability** (`workflow`): every `after`-bearing state is
  reachable from `init`, and generated runs that park in one actually fire it
  under the simulated clock.
- **Terminal liveness** (`workflow`): every state has a path in the declared
  graph to a terminal state (no outgoing edges) — a **static** graph check,
  0 runs, reported as *proved by construction*. An order that can never
  finish is caught before the first instance exists.
- **Conversation fuzzing** (`bot`): generated user inputs — including garbage
  strings at `ask expecting` prompts — never crash a session; garbage always
  yields a re-prompt in the same state.
- **Typestate conformance** (`bot`): random valid traces only ever traverse
  declared edges; everything else lands in the catch-all.

## 7. Relations

- **`reducer`** (parent §5.5) — the base; this spec adds no reducer
  semantics, only capabilities (`store`), merged timer messages, and sugar.
- **`schema`** — persistence + the totality-checked migration chain (§2.4).
- **`protocol`** — a bot conversation is morally a session against a human;
  `serve` is a cousin container. Whether `bot` lowers onto `protocol`
  internally is already ledgered there (protocol spec §10.7) — not re-decided
  here.
- **`view` / `api`** — admin surfaces over the event log: pending approvals
  (§2.3), instance timelines, and the bot's live-session dashboard are folds
  over emissions.
- **`job`** — scheduled nudges and batch sweeps share the durable-timer
  substrate; a `job` that pokes workflows is just a message sender.
- **`fleet`** — device-triggered workflows: a fleet telemetry edge injecting
  `Msg`s into workflow instances is the MCU↔business bridge (a sensor fault
  opens a repair `workflow`).

## 8. Open decisions (ledger)

1. **Durable-timer implementation** — one per-node sweep over due-time rows
   (recommended: restart recovery is a query, scales with due timers not
   instances) vs. per-instance BEAM timers with a rehydration pass; sweep
   resolution and at-least-once redelivery bounds.
2. **Emission-log compaction / snapshots** — replay from genesis is O(events);
   decide snapshot cadence (every N events vs. on state change), and whether
   snapshots are derived-only (always re-foldable) — recommended, keeps the
   log the single source of truth.
3. **Workflow versioning for in-flight instances** — migrate models through
   the schema chain (one live definition) vs. drain-old-version (instances
   finish on the definition that started them; new instances get the new
   one). Migration is cleaner but demands the graph change be
   migration-expressible; draining needs multi-version dispatch. Likely
   per-deploy choice, surfaced in the deploy tool.
4. **Saga / compensation surface** — explicit compensating transitions
   (**recommended**: a compensation is just more edges + emissions, visible
   in the graph and the audit log) vs. an automatic reverse-log mechanism
   (rejected tentatively: hides business decisions the graph should state).
   Decide whether a `compensates` annotation adds checked pairing.
5. **Bot platform adapter interface** — the exact typed boundary (Msg
   decode, say/ask render hooks, rich-media capabilities per platform,
   delivery acks), and which reference adapters ship.
6. **Multi-bot / multi-workflow composition** — a workflow spawning child
   workflows (order → per-item fulfillment), a bot handing a session to
   another bot; likely just messages + emitted references, but the sugar and
   the supervision shape need deciding.
7. **Rate limiting** — per-session and per-platform outbound limits
   (platforms ban chatty bots); adapter-level concern vs. a declared
   `rate` capability the macro checks statically where literal.

## 9. Non-goals

- **No BPMN import/export.** The graph notation is the process language;
  round-tripping someone else's notation is a tooling project, not a macro.
- **No NLP / LLM intent parsing in the macro.** An adapter may plug one in
  (free text → typed `Msg` is exactly the adapter's job); the macro sees
  typed messages and stays testable and total.
- **No distributed workflow instances.** One instance = one actor = one node
  at a time; that is the consistency model. Fleets of instances are just many
  actors — BEAM already does that; nothing to design.
