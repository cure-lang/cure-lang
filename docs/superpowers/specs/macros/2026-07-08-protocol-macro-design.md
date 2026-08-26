# `protocol` — Session-Typed Conversations, One Declaration, Every Endpoint

**Date:** 2026-07-08
**Status:** design (operator-requested). Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
(§7.4); sibling and substrate of
[`2026-07-08-fleet-macro-design.md`](2026-07-08-fleet-macro-design.md)
(fleet's generated channels are `protocol` sessions). Built as a `macro`
(§5) — zero compiler special-casing.

---

## 1. Purpose & positioning

A `protocol` declares a **conversation** — who says what, in what order, with
what choices — once. From that single declaration Cure generates **every
endpoint**: the ESP32 side, the host side, or both halves of an in-process
actor conversation. Sending the wrong message at the wrong step is a compile
error *at whichever end tries it*, phrased in conversation vocabulary.

Three consumers, one mechanism:

1. **Directly by users** — device↔phone provisioning, device↔host links over
   UART/BLE/WiFi, service↔service on the BEAM.
2. **As `fleet`'s substrate** — every cross-node flow edge fleet projects
   becomes a generated protocol session (fleet spec §3).
3. **In-process** — a session between two `actor`s on one node gives the
   Melquiades send (`<-|`) a *conversation-level* typing discipline, upgrading
   today's per-message inbox checks (E045/E046) to whole-dialogue checking.
   Same declaration, transport = BEAM messages.

The theory underneath is **(multiparty) session types** (Honda/Yoshida) with
endpoint projection — the per-conversation twin of fleet's choreography. Per
hiding principle 2, the surface is restricted so that **ill-projectable
protocols are inexpressible** (§3): users never see a projectability error,
because the grammar can't utter the problem.

## 2. Surface — declaring a conversation

Flagship example (hobbyist-real: WiFi provisioning of a device from a phone):

```cure
protocol Provisioning
  roles phone, device
  timeout 10s                       # per-step default; overridable per step

  phone  -> device: Hello(name: String)
  device -> phone:  DeviceInfo(model: String, fw: Version)

  loop setup
    choose phone
      | Join(ssid: String, pass: secret String) ->
          choose device
            | Accepted(ip: IpAddr)        -> end
            | Rejected(reason: JoinError) -> continue setup
      | Scan ->
          device -> phone: Networks(found: List(Ssid))
          continue setup
      | Cancel -> end
```

Grammar rules (each one is a projectability theorem in disguise):

- **`roles`** — v1 is **two-party**; the multiparty grammar is accepted but
  gated (§10.1).
- **Steps** are `sender -> receiver: Msg(fields…)` — fields are ordinary
  (refinable, `secret`-able) types; the wire format is delegated to
  `packet`/`codec`.
- **`choose role`** — every choice names its decider, and every branch begins
  with a message **from** that decider (or terminates). This is the classic
  well-formedness condition that makes "knowledge of choice" hold *by
  construction* — the branch's first message is itself the notification. No
  merge/projectability checker needed; the grammar cannot express the broken
  case.
- **`loop name` / `continue name` / `end`** — recursion as labeled loops;
  `end` closes the session. Tail-position `continue` only (checked), which
  keeps sessions finite-state and the generated handles simple.

## 3. Generated endpoints — two APIs per role

### 3.1 Typestate handles (the precise API)

Each role gets a state-indexed handle; every operation consumes the handle
and returns the next state's handle. Wrong-step usage is a type error:

```cure
fn provision(t: Transport) -> Result(IpAddr, ProvisionError) =
  let s0 = Provisioning.phone.connect(t)
  let s1 = s0.hello(name: "kitchen-display")?
  let %[info, s2] = s1.recv_device_info()?
  let s3 = s2.join(ssid: cfg.ssid, pass: cfg.pass)?
  match s3.recv()?
    Accepted(ip, s_end) -> { s_end.close(); Ok(ip) }
    Rejected(_r, s_loop) -> ...      # handle is back at `setup` — retry or cancel
```

- The handle's state is a **GADT index** (the landed machinery) — calling
  `.join(..)` on an `s1` handle is a compile error: *"at this step, phone can
  only send Hello"*.
- Handles are **affine** (usage `≤1` on the reserved grade axis): each may be
  used at most once, so a *stale* handle cannot be replayed — but the error
  path may simply drop it (that's why affine, not linear; see §5). Until the
  grade wave enforces `≤1`, the state index alone already catches wrong-step
  reuse; silent *duplication* is the only gap, closed when grades land.

### 3.2 `serve` — the handler container (the beginner API)

Most users never touch handles. `serve` is the `reducer`-flavored surface:
one clause per receivable message, and **which `reply` is legal is
constrained by the protocol state**:

```cure
serve Provisioning.device over uart0
  on Hello(name) ->
    reply DeviceInfo(model: "cure-c3", fw: v(1, 2, 0))
  on Join(ssid, pass) ->
    pickup
      wifi.join(ssid, pass) -> reply Accepted(ip: wifi.ip())
      else                  -> reply Rejected(reason: BadCredentials)
  on Scan   -> reply Networks(found: wifi.scan())
  on Cancel -> done
```

`serve` compiles onto the `fsm` container (the protocol's local type *is* a
finite state machine — §2's tail-`continue` rule guarantees it), supervised,
one session per peer. Coverage checking applies: an unhandled receivable
message is a compile error listing the protocol step it arises from.

Representative explainer:

```
error[E14x]: device cannot reply Networks here
  --> provision.cure:9
  After Join, the protocol says device answers Accepted or Rejected
  (Provisioning, line 12). Networks is only a reply to Scan.
```

## 4. Wire compilation

- Each message compiles to a `packet` frame; transports: `uart`, `espnow`,
  `udp`, `mqtt`, `beam` (in-process). Same declaration everywhere; only
  `connect`/`serve … over <transport>` names the medium.
- **Tag elision** — the session-type dividend: at a *deterministic* step both
  ends already know exactly which message must come next, so the wire carries
  **no discriminator at all**; only `choose` points carry a branch tag sized
  by `Bounded(number_of_branches)`. Session typing literally saves airtime —
  worth a docs callout, since it converts "types" into a number an embedded
  person respects (bytes).
- Handshake: session open carries the protocol's **declaration hash** (and a
  version, §10.5); mismatched peers fail at connect with both hashes named,
  never mid-conversation.

## 5. Failure, timeouts, affinity

Links drop mid-conversation; the design makes that ordinary, not exceptional:

- Every blocking operation returns `Result(next_state, SessionError)` —
  `Timeout(step)`, `Disconnected`, `PeerVersionMismatch`. The `?` operator
  keeps the happy path linear-reading (§3.1). In `serve`, session death
  invokes the container's supervised restart (a fresh session), and an
  optional `on_disconnect` clause states cleanup.
- `timeout` is declared in the protocol (default per-protocol, overridable
  per step) — so *both* endpoints agree on patience by construction, and a
  timeout is a protocol-level fact, not a per-call magic number.
- **Affine, not linear**: an error path drops the dead handle without
  ceremony (`≤1`, matching practical session systems), while `close` exists
  for the deliberate early exit *where the protocol allows `end`*.

## 6. What the dependent types do invisibly

- Step discipline = GADT state index on handles; conversation coverage =
  the existing exhaustiveness machinery pointed at local session types.
- Affinity = the reserved `≤1` usage grade (first real consumer of the
  affine rung; sessions are the canonical motivating example to ship with
  the grade wave).
- **IFC × transport** (novel check, shared with fleet §11.8): a `secret`
  field (`pass` above) **refuses to project onto an unencrypted transport**
  — `serve Provisioning.device over udp(:lan)` without a keyed layer is a
  compile error naming the field and the step. The security lattice meets
  the wire exactly here.
- Refinements on fields generate validation at *both* ends from one source;
  `check` templates (§7) exercise them.
- Erasure: state indices, role types, and session brands cost zero bytes;
  the wire cost is §4's elided-tag minimum.

## 7. `check` integration

Shipped property templates (surfaces spec §7.5):

- **Conformance**: generated random *valid* traces drive both endpoints
  in-process; each side must accept every message the other legally sends.
  (Fidelity per step is static; the template exercises the generated
  codec/transport glue, which is code, not types.)
- **Fault injection**: in `cure run --sim`, drop/duplicate/delay/corrupt
  frames; properties assert every run ends in a defined `SessionError` or a
  completed session — never a hang (timeouts are declared, so "never a hang"
  is actually testable) and never an out-of-protocol state.
- Round-trip of every message payload comes free from the `packet` template.

## 8. Relation to siblings

- **`fleet`** consumes protocol as its channel compiler; fleet's
  latest-value signal edges use a degenerate one-step protocol (no session
  state), its acked command edges use a two-step `Cmd`/`Ack` session with
  the retry policy in the protocol's timeout terms.
- **`driver`** init blocks (surfaces §6.2) are morally single-role protocols
  against silicon; no unification attempted (the datasheet side can't run
  our endpoint), but explainer vocabulary is shared ("at this step…").
- **`bot`** conversations and **`api`** request/response are session
  specializations (an `api` route is a two-step protocol); those macros
  may lower onto protocol internally — ledgered (§10.7).

## 9. Non-Cure peers

A phone app or browser isn't Cure. The declaration exports:

- a **JSON schema + state chart** of the protocol (documentation artifact,
  rendered by `cure protocol report` — the fleet-report philosophy: the
  conversation is inspectable);
- generated **TypeScript / Swift client stubs** implementing the same local
  type discipline (typestate via phantom types where the host language
  allows). Scope and languages ledgered (§10.6) — but this is the "one
  declaration, both ends" pitch escaping the Cure boundary, and it matters
  for exactly the provisioning-app use case in §2.

## 10. Open decisions (ledger)

1. **Multiparty scope** — v1 two-party; true MPST (3+ roles, one session)
   deferred until a probe needs it (fleet does *not* — its multi-node
   coordination lives at the flow layer).
2. **Delegation** (sending a session endpoint *over* a session) — classic,
   powerful, deferred; interacts with linearity and transports that can't
   carry handles (everything except `beam`).
3. **Linearity timing** — affine enforcement arrives with the grade wave;
   decide interim story (state-index-only, documented duplication gap) vs.
   an elaborator-side affine lint shipped early.
4. **Timeout semantics under `beam` transport** — in-process sessions may
   want no timeouts by default; per-transport defaults?
5. **Version compatibility** — declaration-hash equality (strict) vs. a
   declared compatibility window (adds `deprecated` steps); shared problem
   with fleet mixed-version rollout (fleet §11.5) — resolve once, here.
6. **Foreign stub generation** (§9) — which languages first; whether stubs
   are part of the macro or a separate tool.
7. **Lowering `api`/`bot` onto protocol** (§8) — unify now or after all
   three exist.
8. **Encrypted transport story** for the IFC check (§6) — what counts as
   "keyed" per transport (ESP-NOW LMK, TLS for mqtt, noise-style layer for
   udp/uart?).

## 11. Non-goals

- No full MPST generality in v1 (§10.1) and no delegation in v1 (§10.2).
- No dynamic protocol negotiation (capabilities exchange beyond the version
  handshake) — declare a bigger protocol instead.
- No attempt to session-type *existing* raw `<-|` code — the discipline is
  opt-in by writing a protocol; bare typed sends stay as they are (E045/
  E046).
- Not a crypto library — §10.8 picks existing transport security; the
  macro only *checks* that secrets meet a keyed edge.
