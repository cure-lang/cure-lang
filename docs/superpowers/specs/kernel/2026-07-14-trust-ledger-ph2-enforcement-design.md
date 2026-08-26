# Trust Ledger Ph2 — Enforcement MVP

STATUS: DESIGN APPROVED 2026-07-14. Ready for writing-plans.

Turns the existing trust-ledger *reporting* tool (`cure audit trust`, Ph0/Ph1,
merged `7b82c9f`) into *executable policy*. This is the concrete first slice of
Gate 10 of the aspirational doctrine
(`2026-07-13-cure-evidential-systems-architecture.md`) — chosen as the
best-first-thing because it is TCB-additive (zero kernel risk), extends already
merged code rather than starting cold, and turns known TCB holes into
CI-catchable failures.

Companion: `2026-07-14-backend-decoupling-cureir-design.md` (the multi-backend
initiative this doctrine is the safety rail for).


## What already exists (do not rebuild)

`lib/cure/audit/` — a complete, deterministic *reporting* tool. Reads the
elaborated `Cure.Core.Env`, never source text (macro output is re-elaborated, so
Core.Env is the only vantage point that sees every axiom). Untrusted; outside the
TCB.

- **Transitive axiom closure is real.** `Ledger.reachable/2` + `collect/3` walk
  type + body refs from `roots(env)`, collecting every reachable `@extern` as an
  `Axiom{mfa, type, via, bucket}`. This IS the §137 closure graph.
- **`Refs` is a fail-closed Core-term walk** — one clause per `Core.Term.term?/1`
  former, `raise` on anything unknown. New Core grammar cannot silently drop
  axioms/holes.
- **Holes and absurd already collected** — `{:hole, name}` → `report.holes`,
  `{:absurd}` → `report.absurd`.
- **`not_proven_total`** — reachable defs not in `env.certified` (can't δ-unfold →
  can't inhabit a type). A completeness note, not an assumption.
- **`unresolved`** — a reachable global that is neither def, family, nor ctor:
  an axiom whose *type* names something nonexistent. A real defect class.
- **Determinism is load-bearing** — sorted, no timestamps/paths, every section
  prints even when empty. `cure audit trust Std.List | diff -` is the current
  (manual) ratchet. JSON output exists (`schema:1`).
- **Provenance buckets** — `otp` / `cure_runtime` / `cure_bridge` (by extern
  module prefix). Orthogonal to evidence class. `--target` availability filtering
  exists.

CLI philosophy, quoted from `Cure.Audit.CLI`: *"Never wired into `cure build`: a
compiler that refuses to build over an audit trains people to hate the audit."*
Ph2 preserves this — enforcement is opt-in, never in the default build.


## Ph2 scope — three capabilities, no kernel changes

### 1. Per-def closure (§137)

`audit_env/1` currently seeds the walk from `roots(env)` (all module-owned defs).
Parameterize it to accept an arbitrary root set; the axiom/hole/absurd/not-total
filters already operate over "the reachable set," so this is parameterization,
not new machinery.

Surface:

    cure audit trust Std.List --def foldl

→ a `Report` scoped to exactly what `foldl` reaches. `--def` with a name not
owned by the module is an error (exit nonzero, clear message), not an empty
report.

### 2. Axiom allowlist (§137)

A checked-in, deterministic file — default `priv/audit/allowlist` — of blessed
axioms keyed by `{mfa, type}`, the SAME key `Ledger` dedups on
(`Enum.uniq_by(fn a -> {a.mfa, a.type} end)`). Sorted, one entry per line, stable
across runs.

Bootstrap from current state:

    cure audit trust Std.Gpio --emit-allowlist

emits allowlist lines for that module's reachable axioms (sorted, deterministic),
to stdout, for appending/review. `--emit-allowlist` makes adoption cheap given
the large existing extern surface; it is a generator, never an auto-approver
(a human commits the file).

This replaces the *manual diff-review* ratchet with a *machine-checked* one.

### 3. Profiles (§138) — opt-in, never in `cure build`

Two named profiles, evaluated over a `Report`:

- **`dev`** (default): report only, always exit 0. Current behavior, unchanged.
- **`release`**: exit **1** if the reachable set contains ANY of:
  - a **hole** (`report.holes` non-empty),
  - an **unresolved** name (`report.unresolved` non-empty),
  - an **unaudited** module (`report.unaudited` non-empty — failed to elaborate),
  - an **axiom absent from the allowlist**.

  On failure, print exactly which items triggered it (grouped by category,
  deterministic order), then the normal report.

`release` deliberately does **NOT** fail on:

- `absurd` — kernel-checked impossibility proof (empty pattern context),
  legitimate, not an assumption;
- `not_proven_total` — general recursion legally lives in the computation
  stratum; a runtime def need not be total;
- builtins — kernel baseline;
- opaque types — legitimate;
- allowlisted axioms — blessed by definition.

Rationale traces directly to doctrine §138 (reject holes / sorry-equivalents /
unchecked stubs / untracked trusted plugins) — and NOT the legitimate categories.

### CLI / return shape

`Cure.Audit.CLI.run/2` today returns
`{:ok, text} | {:strict_failure, text} | {:error, :not_found}`.

Add `{:profile_failure, text}`. The escript clause in `Cure.CLI` maps it to
`System.halt(1)` (same treatment as `:strict_failure`). Pure `run/2` stays pure —
it decides pass/fail and returns text; only the escript halts.

New flags: `--def <name>`, `--profile <dev|release>`, `--emit-allowlist`,
`--allowlist <path>` (default `priv/audit/allowlist`).


## Scope boundaries (YAGNI — explicitly deferred)

- **Per-module gate only.** A program-wide `release` sweep is blocked regardless:
  ~40% of the stdlib is `UNAUDITED` (doesn't elaborate yet), so whole-program
  `release` cannot go green until that shrinks. A multi-module wrapper is a thin
  follow-up once elaboration completeness improves. NOT in Ph2.
- **No evidence-class taxonomy** (Proof/CheckedCertificate/Assumption/
  MonitorKnowledge/Test/TrustedClaim, doctrine §3). That is a conceptual relabel
  of every claim — Ph3. Provenance buckets stay as-is for Ph2.
- **No content-addressed evidence manifests** (source_hash/core_hash/…, §136).
  Ph3. The deterministic allowlist diff is the Ph2-level integrity mechanism.
- **No kernel/TCB changes.** The audit remains untrusted and outside the TCB.
  If Ph2 ever needs a kernel change, that is a signal to stop and re-scope.


## Testing (TDD, red before green — repo discipline)

Each gets a failing test first, then the implementation.

1. **Per-def closure isolates.** Module with two defs: `a` uses `@extern X`, `b`
   uses `@extern Y`. `--def a` reports X and not Y; `--def b` the reverse.
2. **Per-def unknown name errors.** `--def nonesuch` → nonzero, clear message,
   not an empty pass.
3. **Allowlist admits.** Axiom present in allowlist → `release` exits 0.
4. **Allowlist ratchet bites.** Same module, axiom removed from allowlist →
   `release` exits 1 and names exactly that `{mfa, type}`.
5. **Hole gated.** Def containing a `{:hole}` → `release` exits 1 (holes
   section), `dev` exits 0 and reports it.
6. **Legitimate categories pass.** A module whose only "unproved" items are
   `absurd` + `not_proven_total` (no holes, all axioms allowlisted) → `release`
   exits 0.
7. **`--emit-allowlist` deterministic.** Same input → byte-identical output;
   output sorted; feeding it back as the allowlist makes `release` pass.
8. **Determinism preserved** for all existing report output (regression).


## Definition of done

- `cure audit trust <M> --def <name>` scopes the report.
- `cure audit trust <M> --profile release` exits nonzero on hole / unresolved /
  unaudited / non-allowlisted axiom; zero otherwise.
- `cure audit trust <M> --emit-allowlist` bootstraps a deterministic allowlist.
- `priv/audit/allowlist` checked in for at least one real module as proof.
- All 8 test anchors green. No kernel/TCB diff. Default `cure build` untouched.
