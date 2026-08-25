# `config` & `secret` — Validated Deployment Config and One-Word IFC

**Date:** 2026-07-08
**Status:** design. Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
(§6.7 `config`, §6.8 `secret`); the `secret` semantics defined here are
consumed by
[`2026-07-08-protocol-macro-design.md`](2026-07-08-protocol-macro-design.md)
(§6, IFC × transport) and the fleet spec (§11.8). Built as a `macro` (§5):
`config` is Tier-1 declarative data, `secret` is Tier-2 sugar over the
Final-Core Security grade axis
([`2026-07-07-final-core-grammar-design.md`](../kernel/2026-07-07-final-core-grammar-design.md)
§B.3). Zero compiler special-casing; zero TCB delta.

---

## 1. Purpose & positioning

Two features, one spec, because they meet in the same block: the values a
program is *deployed with* (SSIDs, broker hosts, topics, credentials) are
exactly the values most often wrong at 11pm on the workbench — and most
catastrophic to leak. `config` makes the first failure class a **build error
in deployment vocabulary**; `secret` makes the second **inexpressible without
a marked, audited escape**. Pitch sentences, per the parent's marketing rule:
*"your firmware cannot boot with a malformed topic"*; *"the compiler proves
your WiFi password can't leak over serial."* Pure refinements plus the
already-designed security lattice — boring machinery, high-value surface.

## 2. `config` — the surface

A module-level block; fields are `name: Type = default`:

```cure
mod Greenhouse
  board :esp32c3

  config
    ssid:   String        = env("WIFI_SSID")
    pass:   secret String = env("WIFI_PASS")
    broker: Host          = "mqtt.local"
    topic:  Topic         = "home/greenhouse/temp"
    led:    Pin           = pin.gpio4
```

- **`env("WIFI_SSID")` reads at BUILD time.** The value is resolved when
  `cure build`/`cure flash` runs on the host and baked into the image as a
  constant (v1; runtime provisioning is §3.4).
- **Every field is refinement-validated at build**, against the *resolved*
  value: SSIDs carry the 802.11 length limit (`{s: String | len(s) <= 32}`),
  `Topic`'s refinement is the MQTT topic grammar (no `#`/`+` in a publish
  topic, no empty levels), `Host` checks hostname/IP syntax, and a `Pin`
  field joins the board file's claim table — a config pin colliding with a
  board-default bus assignment is the same E118 the ownership check gives
  everywhere else.
- **A missing env var at build is a clear error naming the variable and
  where it's consumed** (§5.2) — never a runtime `nil` on the device.
- Access is `cfg.ssid` etc.; the block elaborates to a record of refined
  constants, so every downstream obligation discharges by literal
  computation (parent §1). No user sees a refinement unless it fails.

## 3. `secret` — the semantics

### 3.1 One word, one lattice point

`pass: secret String` is a `String` whose grade's `security` axis sits at a
high point of the module's security lattice. Per §B.3 the default lattice is
the trivial `{Public}`; writing `secret` anywhere in a module instantiates
the two-point lattice `Public ⊑ Secret` for it. **Default-off means zero
cost when unused**: a program with no `secret` pays nothing, checks nothing,
carries nothing.

### 3.2 No downward flow

The label is **sticky** (§B.3): it rides the type, joins upward through
every elimination (`"pw: #{cfg.pass}"` is Secret; a record with a secret
field is Secret at projection), and the checker rejects any flow to a
strictly lower sink. Serial output, MQTT publish, HTTP bodies, log calls are
all declared `Public` sinks, so a secret cannot reach them:

```
error[E120]: `cfg.pass` is secret and cannot be written to serial output
  --> main.cure:22
  pass was declared secret in config (main.cure:6).
  If you really mean it: puts(declassify(cfg.pass, reason: "debugging"))
```

### 3.3 The only door down: `declassify`

`declassify(value, reason: "...")` is the sole downward coercion: explicit
(a call the user writes), **marked in the term** (a tagged coercion node
visible in Core), and audited (§8.4 ledgers where the trail surfaces;
`cure audit` listing every declassify site with its reason string is the
working assumption). `reason:` is mandatory — declassification without a
stated reason is a parse error, not a style nit.

### 3.4 The label is on the TYPE, not on the provenance

This is what makes the feature coherent across the build/runtime split.
Build-time `env()` is v1's delivery mechanism, but the protocol spec's
Provisioning example delivers `ssid`/`pass` at **runtime** (`Join(ssid:
String, pass: secret String)` over a session). A runtime-provisioned secret —
received off the wire, read from NVS flash, typed into a provisioning app —
is still a `secret String`. Where the value *came from* is irrelevant; where
it may *go* is fixed by its type. A future NVS-backed field
(`= nvs("wifi_pass")`) changes only the initializer, not one line of the
checking story.

### 3.5 Sinks declare their clearance — the general rule

The E120 check is one instance of a rule this spec owns and siblings consume:
**a sink's security clearance comes from its declaration, and the checker
enforces no-downward-flow into it.** Serial, logs, and plain HTTP are
`Public`. An encrypted transport session (TLS-backed MQTT, a keyed ESP-NOW
link) is declared at an elevated level, so a secret may flow *into* it —
which is precisely the protocol spec's §6 check: `pass: secret String`
refuses to project onto an unkeyed `serve … over udp(:lan)`, and fleet §11.8
is the same rule pointed at generated channels. What counts as "keyed" per
transport is protocol §10.8's ledger item, not ours: we define the rule, they
classify the wires.

## 4. Invisible machinery

- `config` fields are refined constants; validation is ordinary refinement
  checking against literals — everything discharges by computation (hiding
  principle 3), and erasure makes the refinements cost zero bytes on device.
- `secret` elaborates to a grade annotation (`security: Secret`) on the
  binder. The kernel's §B.4 obligation (LUB tracking + no-downward-flow
  under a non-trivial lattice) does all enforcement; the macro contributes
  only surface and explainers. Until the IFC wave lands enforcement, the
  label is carried-not-checked (§B.3) and the macro ships an
  elaborator-side flow lint so the UX exists early — the same interim
  pattern as protocol affinity (protocol §10.3).
- **Crash-report/log redaction — the runtime half of the guarantee.** Static
  flow checking does not cover a VM crash dump: if a secret sits in a
  process's heap when the supervisor formats a crash report, the bytes are in
  the log. Direction: secret values are **boxed in a redacting wrapper at
  runtime** — a one-field struct whose formatter/inspect path prints
  `<<secret>>`, unwrapped only inside elevated sinks and `declassify`. One
  boxed cell per secret (acceptable: secrets are few and small); covers every
  formatting path that goes through inspection — but NOT a raw memory dump of
  the VM, and AtomVM's crash paths need an audit to confirm they format via
  that path. The hardest part of the feature; ledgered honestly (§8.1) rather
  than promised.

## 5. Explainers

Registered per parent §4; template *what you wrote → why forbidden → what
instead*.

1. **E120 secret-to-sink** — §3.2's exemplar; the variant for MQTT/HTTP names
   the transport and points at the keyed alternative when one is configured.
2. **Missing env var:**

   ```
   error[E121]: environment variable WIFI_SSID is not set
     --> greenhouse.cure:5
     config field `ssid` reads env("WIFI_SSID") at build time.
     Set it and rebuild:  WIFI_SSID=MyNetwork cure flash
   ```

3. **Refinement-failed config value** shows the expected grammar:

   ```
   error[E122]: "home/greenhouse/#" is not a valid publish topic
     --> greenhouse.cure:8
     `#` is an MQTT subscribe wildcard; publish topics are literal levels:
     letters, digits, -, _ separated by /.  Did you mean "home/greenhouse/temp"?
   ```

4. **Secret in string interpolation** — the sneaky flow: `"#{cfg.pass}"` IS
   a flow, and the string then hits a public sink. The explainer attributes
   the leak to the interpolation site, not the distant `puts`: *"this string
   contains cfg.pass (interpolated at line 14) and is secret; it cannot be
   logged."*

## 6. `check` integration

- **Config refinements are generators** (parent §7.5): a prop taking
  `t: Topic` generates *valid* topics; `packet`/`protocol`/`api` templates
  run user declarations against generated in-refinement configs — "works
  with my one config value" becomes "works with every legal one" for free.
- **Shipped template "no secret reaches a public sink"** is fully static —
  it *is* the flow check. Nothing remains dynamic, so the template is a
  **static report**: `cure test` prints it on the proved-by-construction rung
  (`✓ no_secret_to_public_sink — proved by construction; 0 runs`) together
  with the declassify inventory (count + sites) — the sanctioned holes belong
  next to the green check.
- The redaction wrapper (§4) gets a genuinely *dynamic* template: crash a
  supervised process holding a secret in `cure run --sim`, assert the
  formatted report contains `<<secret>>` and not the value — real testing,
  because it exercises runtime formatting code, not types.

## 7. Relations

- **protocol** (§6) and **fleet** (§11.8) consume §3.5's sink-clearance rule
  for transports and edges; they classify wires, we define flow.
- **board** — config `Pin` fields join the board claim table (§2).
- **Final-Core §B.3** — `secret` is the *only* v1 surface of the security
  axis; the kernel supports arbitrary bounded join-semilattices underneath
  (§8.5).
- **fleet OTA** — config schema identity across firmware versions is shared
  with fleet's channel versioning (§8.3, fleet §11.5); resolve once.

## 8. Open decisions (ledger)

1. **Crash-dump redaction mechanism** — §4's boxed redacting wrapper vs.
   erased-to-opaque rewriting in error formatting only; whether AtomVM's
   crash paths all route through the inspect path (needs an audit); what to
   promise about raw VM memory dumps (likely: nothing — document the
   boundary).
2. **Per-environment profiles** — dev/prod config overlays (`config for
   :dev` blocks? `--profile` mapping to env-var sets?); interacts with
   `cure run --sim` wanting fake credentials.
3. **Config schema versioning across OTA** — a fleet updating firmware whose
   config block changed shape; shared resolution with protocol §10.5 / fleet
   §11.5 version windows.
4. **Declassify audit trail** — compile-time listing via `cure audit`
   (working assumption) vs. additionally a runtime log line per declassify
   execution; if runtime, that line must itself not carry the value.
5. **Lattices beyond secret/public** — §B.3 supports full module-declared
   lattices (`Public ⊑ Telemetry ⊑ Secret`). Recommendation: **v1 exposes
   only the `secret` keyword**; the general surface waits for a real
   consumer. One word is a product; a lattice declaration is a seminar.
6. **`fleet` mixed-version config** — should the fleet report diff config
   schemas across versions live in a rollout, and is a secret field changing
   level across versions a hard error?

## 9. Non-goals

- No secrets-manager integrations (Vault, AWS SM, …) in v1 — `env()`
  composes with all of them at the CI boundary, which is where they live.
- No encryption at rest on device flash — IDF-level NVS encryption exists
  and applies; out of scope for the language.
- No runtime config UI — protocol provisioning sessions are the sanctioned
  runtime delivery path.
- No general lattice surface in v1 (§8.5).
