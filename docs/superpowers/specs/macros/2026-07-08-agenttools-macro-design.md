# `agenttools` — Tool-Using Agent Loops Where the Type System Is the Sandbox

**Date:** 2026-07-08
**Status:** design. Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
(idea backlog #49, promoted); sibling of
[`2026-07-08-workflow-bot-macro-design.md`](2026-07-08-workflow-bot-macro-design.md)
(`bot` = conversations with humans; `agenttools` = loops with models). Built
as a `macro` (parent §5), a specialization of `reducer` (parent §5.5),
consuming the effect discipline
([`../effects/2026-07-07-sound-effect-discipline-design.md`](../effects/2026-07-07-sound-effect-discipline-design.md))
and [`2026-07-08-config-secret-macro-design.md`](2026-07-08-config-secret-macro-design.md)'s
`secret` semantics. Host-side, full BEAM. Zero TCB delta.

---

## 1. Purpose

The effect system was designed as a hardware capability manifest — `fn poll()
! Gpio, Wifi` (parent §6.10). Pointed at AI agents it becomes the thing the
agent-safety ecosystem fakes with regexes and prayer: **an agent physically
cannot call outside its declared tool manifest, because the call does not
type-check.** The sandbox is the type system, not a wrapper that hopes.

Every agent framework ships a loop, tool schemas, a stringly-typed
dispatcher, and runtime guards hoping to keep the model inside the list.
Here the manifest is an effect row, the dispatcher a checked total function,
the audit log the reducer's emission stream — structural, not aspirational.

## 2. Surface

Two declarations: `tool` and `agent`. A `tool` is **one declaration, two
artifacts** — the schema sent to the model (name, doc string, typed params)
and the checked implementation binding — which cannot drift, being one text.

```cure
tool read_climate
  ## Current temperature and humidity for a room.
  params  room: Room
  returns { temp: Celsius, humidity: Pct }
  ! Http(:get, "climate.home.local")
  fn run(p) = climate.sample(p.room)

tool set_thermostat
  ## Set a room's target temperature. Accepts 15–28 °C only.
  params  room: Room, target: {c: Float | c >= 15.0 and c <= 28.0}
  returns Ack
  ! Mqtt(:publish, "home/thermostat/#")
  fn run(p) = thermostat.set(p.room, p.target)

tool unlock_door
  ## Unlock an exterior door. A resident must approve each use.
  params  door: ExteriorDoor
  returns Ack
  ! Gpio(pin.lock_relay), Await(:resident)
  fn run(p) = await approval from :resident then lock.open(p.door)
```

- The `##` doc string **is** the model-facing tool description — the docs
  the model reads are the docs that stay current.
- `params` are ordinary typed, refinement-carrying parameters. Refinements
  are serialized into the schema sent to the model *and* checked at the
  boundary — the model is told the rule and cannot break it either way.
- `returns` is a result schema; results re-enter the context as typed values.
- The `!` row is the tool's **capability effect**, the same discipline as
  every Cure function. `unlock_door`'s `Await(:resident)` is `workflow`'s
  human-approval gate (§9) — the loop parks until a human decides.

An `agent` is the loop container:

```cure
agent HomeButler
  model:  Std.Agent.Adapter          # capability, like clock/store (§10.1)
  clock:  Std.Clock
  store:  Std.Store                  # persisted transcript + audit log
  tools   [read_climate, set_thermostat, unlock_door]
  policy
    max_turns:  12
    max_tokens: 50_000
    retries:    2                    # malformed-output retry budget (§5)
  state ButlerState reducer          # loop state is a reducer model (§6)
```

`tools` is the **manifest** — a subset of the tools in scope. The agent's
derived entry point inherits the union of the manifest's effect rows —
`HomeButler.run ! Model, Http(:get, "climate.home.local"), Mqtt(:publish,
"home/thermostat/#"), Gpio(pin.lock_relay), Await(:resident)` — so LSP hover
on the agent reads out its complete blast radius.

## 3. The manifest — effects as the sandbox

There are **two layers**, and they catch different things — say which is
which, always:

1. **Static — agent code.** Every tool call the *agent's own code* makes
   (`run` bodies, reducer clauses, prompt assembly) is checked against the
   effect discipline like any Cure code: a tool outside the manifest has no
   callable binding in scope; an effect outside the derived row is `E091`.
   No code path in a compiled agent reaches an unmanifested capability —
   nothing at runtime can widen this, because the call's code does not exist.
2. **Runtime — model requests.** The model is not Cure code; its output is
   data at a boundary. Each requested tool call is parsed against the
   declared schemas and checked for manifest membership. A model requesting
   an unmanifested or unknown tool, or arguments failing a refinement, is a
   **rejected event in the loop** — recorded, surfaced to the model as a
   typed refusal, never executed. Rejection is a normal reducer transition.

Composite guarantee: layer 1 proves the *loop* cannot exceed the manifest;
layer 2 ensures the *model* cannot either, every attempt an auditable event.
The schemas sent and the validator judging replies are generated from the
same `tool` declarations — no third artifact to drift.

**Prompt-injection honesty.** The manifest bounds what injection can *do*:
injected text cannot widen capabilities — widening is a compile-time concept
and the compiler is not in the loop. But injection can still *misuse
manifested tools within their refinements*: a hijacked HomeButler can set
the thermostat to 28 °C; not to 60 °C, not on a non-home topic, not via a
tool it wasn't given. Refinements (`amount: {n: Int | n <= 100}`) are the
per-tool blast-radius limiter; `Await(:resident)` gates the irreversible.
This macro reduces injection to **declared blast radius**; it does not
eliminate it. Write that sentence in the docs verbatim.

## 4. The IFC payoff

The config/secret spec (§3) defined the rule; here is its sharpest consumer:
**the compiler proves your API key can't leak into the context window.**

- Prompt text and tool arguments bound for the model are `Public` sinks
  (config-secret §3.5: sinks declare their clearance). A `secret` value
  cannot flow into a prompt, system message, or model-bound tool result
  without an explicit, audited `declassify(v, reason: "...")` (config-secret
  §3.3). Interpolation is a flow (config-secret §5.4): the sneaky
  `"context: #{cfg.token}"` is caught at the interpolation site.
- Tool **results** can be labeled: a tool whose `returns` carries `secret`
  fields yields data the agent's *code* may use (store, compare, pass to an
  elevated sink) but cannot echo back to the model. A credentials-fetching
  tool is safe to manifest — its output is structurally barred from the
  next prompt.
- The adapter's own credential (`api_key: secret String` in `config`) never
  appears in agent-authored text either; it flows only into the adapter's
  elevated transport.

No wrapper framework can state this: the leak paths are type-level flows —
enumerated, closed, with `cure audit` listing every sanctioned exception.

## 5. Structured outputs

Model responses are data at a boundary, so they get the boundary treatment —
the `parse`/`codec` machinery (parent §7.2):

- Every response parses against declared shapes: a tool-call request into
  `%[tool, typed_args]` against the manifest's schemas; a final answer
  against the agent's declared result type. **No stringly-typed tool
  arguments exist anywhere** — agent code only ever sees refined, typed
  values.
- Malformed output (unparseable JSON, unknown fields, refinement failure) is
  a typed parse error fed into the **bounded retry policy** (`retries`): the
  explainer is rendered back to the model as a correction prompt — `bot`'s
  `ask expecting` re-prompt move (workflow-bot §3.3), the audience now a
  model. Retry exhaustion is a **typed failure** (`MalformedOutput` in the
  reject stream), a normal terminal transition — never a crash, never a
  silent drop.

## 6. Audit by construction

The loop is a reducer, so the audit log is not a feature — it falls out,
the same argument as workflow-bot §2.1:

- Every prompt sent, response received, tool call validated or rejected,
  tool result, approval request, and policy decision is an **emission** in
  the reducer's typed event stream, persisted via `store` (the `schema`
  macro's business).
- State = fold of events; **replay is deterministic given the recorded model
  responses** — the model is the only nondeterminism in the loop, and it is
  recorded. "What did the agent see before it did that" is a fold, not
  forensics; a recorded incident replays exactly on a laptop.
- Budgets (`max_turns`, `max_tokens`) are policy transitions in the same
  machine: exhaustion is a typed terminal event, not a killed process.
  Size-change totality: no tool call or reducer step can hang the loop.

## 7. Explainers

Registered per parent §4 (*what you wrote → why forbidden → what instead*);
runtime rejections reuse the same text as the model-facing correction
prompt (§5).

```
error[E225]: agent HomeButler calls tool `send_email`, not in its manifest
  --> butler.cure:44
  HomeButler declares tools [read_climate, set_thermostat, unlock_door]
  (butler.cure:20). Add send_email to the manifest — widening the agent's
  capability row (Http(:post, "smtp.home.local") joins it) — or remove
  the call.

error[E226]: `cfg.api_key` is secret and cannot appear in prompt text
  --> butler.cure:31
  Prompts are sent to the model provider; api_key was declared secret in
  config (butler.cure:8). If you really mean it:
  declassify(cfg.api_key, reason: "...").
```

## 8. `check`

Shipped templates (parent §7.5), adversarial by design:

- **Fuzzed model outputs never crash the loop** — garbage, truncated JSON,
  wrong-schema replies, hostile tool-call requests all land in retry/reject
  transitions; the session survives. `bot`'s conversation fuzzing, pointed
  at a model-shaped peer.
- **Manifest widening is impossible — a static report.** No dynamic test
  exists to run, so the template reports on the proved-by-construction rung
  (`✓ no_unmanifested_call — proved by construction; 0 runs`) alongside the
  derived effect row and the declassify inventory.
- **Refinement fuzzing on tool params** — generated in-refinement arguments
  always execute; out-of-refinement arguments are always rejected at the
  boundary (generator-is-the-oracle, both directions).
- **Replay determinism** — run against a scripted fake adapter, persist,
  re-fold the recorded events: same terminal state, same emissions.

## 9. Relations

- **`prompt`** (backlog sibling) — typed prompt templating; consumed for
  prompt assembly, nothing added to it.
- **`reducer` / `workflow` / `bot`** — the base and the siblings. The
  human-approval gate (`Await(...)`, `unlock_door`) is `workflow`'s `await
  approval` machinery unchanged (workflow-bot §2.3); a bot and an agent
  differ only in which peer is typed and which is validated.
- **Effects spec** — the manifest is the `!` discipline; parameterized
  capability instances (`Http(:get, host)`) are this macro's demand on
  the effect-kind taxonomy (§10.7).
- **`config`/`secret`** — §4 consumes sink clearance and `declassify`
  wholesale, adding only the model-bound sink classifications.
- **`schema`** — audit-log persistence and transcript storage (§6).
- **MCP interop** — the ecosystem's tool protocol (scope ledgered, §10.3).
  *Importing* an MCP server's tools yields **unrefined** tools (params typed
  from the MCP schema, conservative effect row) that still get full manifest
  treatment — bounded even though the author never heard of Cure; refinements
  are added by wrapping. *Exporting* Cure tools as an MCP server is codegen
  over the same declarations — doc string, schema, refinements travel out
  as JSON-schema constraints.

## 10. Open decisions (ledger)

1. **Model adapter interface** — the typed boundary to Anthropic/OpenAI/
   local backends (adapters are packages, like `bot` platform adapters):
   request/response shapes, per-provider tool-schema serialization,
   recorded-response replay format, fake adapter for `check`.
2. **Streaming** — token streaming into the loop (partial-output reducer
   events?) vs. turn-granular v1 (recommended: streaming is UX, turns are
   semantics).
3. **MCP import/export scope** — schema translation fidelity, the
   conservative effect row for imported tools (`⊤`? declared-per-import?),
   export completeness.
4. **Human-in-the-loop approval surface** — per-call (`Await(:role)` as
   designed) vs. per-session pre-authorization vs. budget-scoped ("approve
   up to 3 unlocks"); rendering in `view`/`api` (the workflow inbox fold).
5. **Token/cost budgets** — declared in `policy`, enforced at runtime (token
   counts are runtime data); per-agent vs. per-session vs. hierarchical;
   whether currency cost joins tokens as a budget axis.
6. **Multi-agent composition** — an agent as another agent's tool. The rule
   that must hold: the child's effect row joins the parent's, so a parent
   cannot launder capabilities through a child — **capability intersection
   at the boundary, union in the report**. Surface and supervision shape
   need design.
7. **Filesystem/network capability granularity** — host allowlists
   (`Http(:get, host)`), path-prefix filesystem capabilities (`Fs(:read,
   "/data/**")`) as refinements on the effect instance; how far the
   parameterized-effect taxonomy stretches before it needs the graded axis.

## 11. Non-goals

- **No model training or fine-tuning.** The macro consumes models only.
- **No eval framework.** Scoring agent quality over task suites is `evals`
  (backlog #50); `check` tests the *loop's* invariants, not the model's
  judgment.
- **No autonomous self-modification — a designed impossibility, not a
  policy.** An agent cannot edit its own manifest: the manifest is a
  compile-time declaration, the compiler is not a manifested capability, no
  runtime value can reach the effect row. The loop that rewrites its own
  permissions is not discouraged; it is unrepresentable.
