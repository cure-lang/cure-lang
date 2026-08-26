# Toolchain Ergonomics — The Fifteen-Minute Path

**Date:** 2026-07-08
**Status:** design. Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
(§2 — gating ergonomics), **priority #1** of the parent's §8: "invisible
dependent types are only a *product* if the fifteen-minute path exists."
This spec formalizes the toolchain that replaces the phase1/phase3 scripts.

---

## 1. Purpose — the fifteen-minute path

Today's first fifteen minutes: install Erlang, Elixir, rebar3, esptool,
ESP-IDF 5.4.1; clone and build AtomVM; restore four local patches; hold the
flash map (0x0 / 0x1d0000 / 0x250000) in your head while running a shell
script. That path selects for BEAM-toolchain veterans — the exact opposite of
the parent spec's audience.

The replacement path, end to end:

```
$ curl -fsSL https://cure-lang.org/install | sh      # or brew install cure
$ cure new blink --board esp32c3
$ cd blink && cure run                               # blinks in the terminal
$ cure flash --port auto && cure monitor             # blinks on the desk
```

Target: **under fifteen minutes from nothing to LED, on a machine with no
Erlang installed.** Every section below exists to make one of those four
lines true. The architecture is not speculative — every hard part (unix-AtomVM
fast loop, prebuilt VM images, patch set, flash composition) is *already
proven practice* in this repo's phase1/phase3 work; this spec productizes it.

## 2. The `cure` CLI

One distributable binary. Command surface (accumulated across the parent and
sibling specs — this is the canonical list):

| Command | Does |
|---|---|
| `cure new <name> --board <b>` | Template project: `cure.toml`, `src/main.cure`, `.gitignore`, a `check` block |
| `cure build` | `.cure → .beam → .avm`; stops at artifacts |
| `cure run` | Build + run on host simulation (generic-unix AtomVM) |
| `cure run --sim [--seed N] [--faults spec]` | Explicit sim variants: deterministic seed, fault injection (§4) |
| `cure flash [--port auto]` | Compose image + libs + app, flash; port autodetected by USB VID/PID |
| `cure monitor` | Serial console (replaces `serial_monitor.py`); auto-reconnect |
| `cure repl` | Host REPL; `:push` targets a device (§5) |
| `cure test` | The `check` macro runner (parent §7.5): static-discharge, then property runs |
| `cure fleet report` | Projected-system report (fleet spec §9) |
| `cure protocol report` | Session/endpoint report (protocol spec) |
| `cure driver report` | Rendered regmap doc (driver spec §8.7) |
| `cure jobs` | Job/schedule status (cli-job spec) |
| `cure doctor` | Prereq + environment diagnosis (§9 — recommended in) |

**Project manifest — `cure.toml`.** TOML, not another macro: the manifest
is read by tools before the compiler exists in the process, and TOML is the
ecosystem-neutral choice users already know from Cargo.

```toml
[project]
name = "blink"

[toolchain]
cure  = "0.9.2"          # toolchain version pin
image = "esp32c3-0.9.2"  # board image version pin (§3)

[deps]
driver-bme280 = "1.2"

[fleet]                   # fleet targets, when the fleet macro is used
sensor = { count = 3 }
```

**Board declaration: code is the source of truth.** The `board :esp32c3` line
in the module (parent §6.1) decides pins, capabilities, and flash map — it
must, because the *type system* consumes it. The manifest never repeats the
board; it pins **versions** (toolchain, image, deps) — the reproducibility
axis, which types don't see. Rule: anything the elaborator needs lives in
code; anything only the build needs lives in `cure.toml`. `cure flash` reads
the board from the compiled module and errors if a project has none.

**Packaging: burrito-style self-contained binary** — the Elixir escript plus
a bundled ERTS, wrapped into one native executable per platform
(macOS arm64/x64, Linux x64/arm64). This is the only option that makes "no
Erlang installed" true, and it is what makes OTP pinning (§3) enforceable
rather than documented. Brew/apt become thin distributors of the same
artifact. Alternatives ledgered (§9.1).

## 3. Board images & flashing

Formalizes phase1's prebuilt-`*.img` practice into a product artifact.

**A board image is:** the AtomVM VM build for that chip + core libs (`.avm`
boot partition) + **the local patch set baked in** — the process-dictionary
and Enum helpers in exavmlib, `ets:whereis/1`, the network-driver IDF guard,
and the enlarged Elixir boot partition (repo CLAUDE.md "AtomVM patches").
Baking the patches into the published image is precisely what makes this safe
to formalize: users can never be missing a patch, and `build-and-flash-c3.sh`'s
patch-verification step becomes obsolete by construction.

**Versioned, downloadable, checksummed.** Images are published per
board × Cure release (`esp32c3-0.9.2.img`), SHA-256 checksummed, fetched on
first `cure flash` for that board, and cached locally (`~/.cure/images/`).
The `[toolchain] image` pin in `cure.toml` makes builds reproducible. Hosting
channel and signing are ledgered (§9.2).

**Flash composition.** The board definition (`boarddef`, parent §6.1) carries
the flash map — VM image at `0x0`, core libs at `0x1d0000`, app `.avm` at
`0x250000`-class offsets (per board; phase3's enlarged-partition layout uses
`0x270000`). `cure flash` composes image + libs + app from that map and drives
esptool internally. **No user ever types a flash offset.** The map lives in
exactly one place, written by board authors, consumed by the tool.

**OTP pinning — invisible.** Cure beams must be compiled with OTP 26–28;
OTP-29 beams boot-loop on AtomVM 0.6.x (repo CLAUDE.md, learned the hard
way). Resolution: the packaged binary **carries its own known-good ERTS/OTP**
(§2 packaging), so the constraint is enforced by construction — users never
see it, never install Erlang, and cannot violate it. If a future distribution
channel uses a system OTP, the CLI verifies the version at startup and refuses
with a plain-language error; but the primary channel makes the check moot.

## 4. Host simulation architecture

**Foundation: generic-unix AtomVM.** Identical VM semantics to the device —
this repo's proven practice ("fast iteration is on generic-unix AtomVM first,
hardware second"; phase35 validated the feature surface this way). `cure run`
*is* that loop, productized. On top of it:

- **Sim registry.** A host-side process registry providing virtual
  GPIO/UART/I2C/SPI buses. The board's bus/pin handles resolve to virtual
  endpoints when running under sim — same `@extern` call surface, different
  backend, zero program changes.
- **Generated device mocks attach automatically.** Driver-macro
  declarations synthesize mock devices (driver spec §4); `cure run --sim`
  wires each mock onto the virtual bus its driver was declared over. Mock
  state is scriptable (`sim.bme280.set(celsius: 31.0)`) from the REPL and
  from `check` props.
- **Terminal rendering.** Pin and LED state render live in the terminal
  (a one-line-per-pin dashboard; blink actually blinks). UART virtual ports
  attach to the console or to pipes.
- **Sim transport for fleets.** All nodes of a `fleet` run as BEAM processes
  over a simulated transport supporting **loss, latency, and partition
  injection** (fleet spec §9) — `cure run --sim --faults 'partition(sensor.1)'`,
  and programmatically from `check` props (`sim(Greenhouse) |> partition(cut)`).
- **Deterministic seeded mode.** `--seed N` fixes the sim clock, mock
  dynamics, and fault schedule so `cure test` failures replay exactly.

**Fidelity boundary — stated honestly, in the docs and in the sim banner:**
the sim proves **logic, concurrency, and protocol behavior**. It does not
prove timing, electrical behavior, or RF. Hardware verification remains
observable-output-based (console output, LED/pin state — repo rule), and the
docs never claim "sim-green ⇒ hardware-green" beyond the pure + concurrency
layer.

## 5. REPL & hot code push

BEAM's birthright and the demo that ends arguments (parent §2.5) — scoped
honestly against AtomVM's limited code-loading support.

- **Host REPL: always, fully.** `cure repl` runs against the host sim;
  expressions elaborate through the full pipeline (types checked, macros
  active); module redefinition hot-swaps into the running sim. Pattern-macro
  live-coding (parent §7.6) depends **only on this host-side swap** — the
  easy path, deliberately.
- **Device push: whole-module swap where AtomVM supports loading.** From the
  REPL, `:push ModName` sends a recompiled module over serial or WiFi to a
  small on-device agent, which loads it where the AtomVM build supports
  runtime code loading. Granularity is the whole module, no state migration,
  no `code_change` — change the blink rate, push, watch it change.
- **Fallback: fast reflash.** Where loading is unsupported (or the change
  touches the boot module), `:push` transparently falls back to
  `cure flash` of just the app partition — still seconds, not a full-image
  reflash, because the VM image and libs partitions are untouched.
- The deep version — stateful upgrades, FSM state migration (parent §6.11),
  fleet-wide rollout — is ledgered (§9.3), not promised.

## 6. LSP, formatter, editor

- **LSP for free from the macro registry.** Because macro grammars are
  declarative data (parent §5.1), the LSP consumes the *same* macro
  registry as the compiler: per-macro syntax highlighting, completion, and
  diagnostics arrive with zero per-DSL work — a structural consequence of the
  design, and the reason the LSP is cheap enough to be priority-#1 adjacent.
- **Hover speaks domain vocabulary.** Hover is the error-explainer
  architecture's positive twin: hovering `pin.gpio4` says "output-capable
  GPIO on esp32c3 (also: input, adc)" — never `Pin(Esp32c3, 4)` with a
  refinement. The same explainer registrations that translate failures
  (parent §4) translate types; raw Pi types on hover are a defect by the same
  definition as raw kernel errors.
- **Formatter: indentation-canonical, macro-aware.** Cure's block structure
  is indentation; the formatter normalizes to the canonical form and formats
  macro-extended syntax via the grammar rules (a declarative grammar is a
  pretty-printer specification read backwards). No configuration knobs in v1.
- **Editor: VS Code extension** wrapping the LSP + a `cure monitor` terminal
  panel. Other editors get the LSP as-is.

## 7. The generated `start/0`

The zero-boilerplate rule (parent §2, end): a module with a `board`
declaration and task/fleet/flow containers **auto-generates `start/0`** —
including the runtime-boot calls (`Cure.FSM.Runtime.start_link`,
`Cure.Actor.Runtime.start_link`, sim-registry attach under `--sim`) that
today every driver program hand-writes and every newcomer forgets. Ordering:
runtime boot → module-level `let` hardware bindings (in declaration order) →
container starts under a generated supervisor.

**Coexistence rule (resolving parent §9 items 14–15 — carry this to the
ledger there):** a hand-written `start/0` in a module that also has
containers is a **compile error**, with the fix in the message: *"this module
generates start/0 from its board/task declarations — move your startup code
into `on_start`"*. An `on_start() -> Unit` hook runs after runtime boot and
hardware bindings, before containers start. We do not silently merge: a
half-generated, half-manual entry point is undebuggable, and the error costs
one edit. Modules with *no* containers keep hand-written `start/0` unchanged
(today's non-DSL programs still compile).

## 8. Migration from today's scripts

- `phase1/cure-avm` and `phase3/build-and-flash-c3.sh` become **thin wrappers**
  over `cure build`/`cure flash` for one release cycle (printing the
  equivalent `cure` command), then deprecate. `serial_monitor.py` is replaced
  by `cure monitor` outright.
- The phase directories **stay as test corpus**: phase35's feature-coverage
  programs become `cure run --sim` CI cases; phase3's turnstile is the
  hardware smoke test. Per the kernel-cleanup strategy (decision 2: the
  compiler gate only, "ESP32 / phase1–phase35 work is going to be overhauled
  after the compiler is done"), this toolchain *is* that overhaul — the
  scripts are not maintained in parallel, they are absorbed.
- The AtomVM patch set migrates from "restored in a local clone's working
  tree" to "baked into published images" (§3); the patch-check logic in
  `build-and-flash-c3.sh` survives as an assertion in the image *build*
  pipeline (maintainers' side), not the user path.

## 9. Open decisions (ledger)

1. **Packaging tech** — recommended: burrito-style self-contained
   binary (§2). Alternatives: plain escript + system OTP with `cure doctor`
   version enforcement (smaller download, breaks the no-Erlang story);
   brew/apt-only (platform coverage gaps). Decide at first release build.
2. **Image hosting / signing / channel** — GitHub Releases vs. dedicated CDN;
   minisign/sigstore signing on top of SHA-256; release channels (stable
   only in v1, or nightly too). Signing is required before any auto-download
   default ships.
3. **Device hot-swap depth** — v1 is whole-module swap + reflash fallback
   (§5). The deep version (stateful upgrade, FSM state migration, fleet
   rollout) waits for real AtomVM code-loading capabilities per chip and the
   OTA state-migration design (parent §6.11).
4. **LSP implementation host** — Elixir-side (inside the compiler process:
   trivially shares the macro registry and elaborator; recommended) vs.
   standalone (faster startup, harder registry sharing). Recommendation:
   Elixir-side, long-running, one process per workspace.
5. **Telemetry** — recommended: **none by default, opt-in prompt at first
   run**, crash reports only. Nothing burns hobbyist trust faster than a
   phoning-home compiler.
6. **Windows support** — WSL2-first at launch (esptool/serial pass-through is
   the pain point); native Windows ledgered until demand is demonstrated.
7. **Offline story** — images and deps cached in `~/.cure/`; `cure` must
   build and sim with zero network once a board's image is cached. Confirm
   the cache layout and a `cure image fetch <board>` pre-cache command.
8. **`cure doctor`** — recommended: include from v1. Diagnoses serial-port
   permissions, USB drivers, stale image cache, and (non-bundled installs)
   OTP version. Cheap goodwill; also the support-issue deflector.

## 10. Non-goals

- **Not replacing ESP-IDF for people who *build* AtomVM images.** Maintainers
  and board-image authors keep the IDF toolchain; users get prebuilt images.
  The IDF prereq moves from every user's machine to the image build pipeline.
- **No IDE beyond LSP + the VS Code extension.** No custom editor, no GUI
  flasher in v1 (the CLI path must be excellent first).
- **Package registry design is a separate future spec** — `[deps]` resolves
  git/path deps in v1; the registry (namespacing, `driver-*` conventions,
  publishing) gets its own document.
- **No sim fidelity beyond logic/concurrency/protocol** (§4) — no cycle
  timing, no electrical modeling, no RF simulation.
