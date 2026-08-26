# `schema` — Typed Persistent Storage & Totality-Checked Migrations

**Date:** 2026-07-08
**Status:** design (operator-requested). Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
(§7.2), **absorbing §6.11 (OTA device-state migration — same machinery)**;
built as a `macro` (§5), so zero compiler special-casing.

---

## 1. Purpose

Every persistent byte a hobbyist writes is a future crash: the config record
that gained a field between firmware v1 and v2, the counter that went negative
on flash, the row whose owner was deleted last Tuesday. `schema` makes stored
data a *typed, versioned* citizen: columns are refinements, references are
indices, and — the centerpiece — **schema evolution is a checked program**. A
migration from v2 to v3 is a total function between the two versions' record
types, verified by size-change termination (cannot hang mid-migration) and by
the dependent-records machinery against *both* schemas (cannot lose or corrupt
a field silently). The identical mechanism migrates a deployed device's
persisted FSM/reducer state across firmware versions: **update a fleet without
bricking state** — the parent's §6.11 promise, delivered here.

Per hiding principle 1, users declare shapes and mappings; the elaborator
manufactures the types. No user ever sees an index or writes a proof.

## 2. Surface — declaration

```cure
schema Pantry v3
  persist in sqlite("pantry.db")          # backend declaration, §5

  table User
    id:     Id(User)                      # primary key, generated
    name:   {s: String | len(s) > 0}
    age:    {n: Int | n >= 0}
    handle: String

  table Item
    id:    Id(Item)
    label: String
    qty:   {n: Int | n >= 0}
    owner: Ref(User) on_delete restrict   # or `cascade` — declared per ref
```

- Columns are ordinary Cure types, refinements included. A refinement is the
  row's invariant: it is checked on every write and *assumed* on every read —
  a `u.age` from this store is `{n: Int | n >= 0}`, so downstream arithmetic
  obligations discharge from the schema, not from runtime guards.
- `Ref(User)` is a typed foreign key. Honesty about what is checked where:
  the *type* makes cross-table confusion inexpressible at compile time (an
  `Id(Item)` cannot be stored where a `Ref(User)` is expected), while
  *existence* of the referent is enforced at write time by the store actor —
  within a transaction, inserting a dangling ref or deleting a still-referenced
  row is rejected before commit, per the declared `on_delete` policy. So:
  dangling refs are unrepresentable *in committed state*, typed at compile
  time, enforced at the single serialization point (§6).
- `Id(T)` / `Ref(T)` erase to native ints (the Nat→Int erasure work): zero
  bytes of type tax in flash or RAM.

## 3. Surface — queries

Typed pipe combinators, checked against the schema — **not** SQL strings:

```cure
fn adults(s: Store(Pantry)) -> List(%[name: String, age: Int]) =
  s.users
  |> where(fn(u) -> u.age >= 18)
  |> order_by(fn(u) -> u.name)
  |> select(fn(u) -> %[name: u.name, age: u.age])

fn stock(s: Store(Pantry), who: Ref(User)) -> Int =
  s.items |> where(fn(i) -> i.owner == who) |> sum(fn(i) -> i.qty)
```

The lambda's parameter type *is* the row type, so `u.agee` is an ordinary
field error and `u.age >= 18` is ordinary refinement-aware code — the LSP
hovers, completes, and errors like any record. On SQLite the pipeline compiles
to SQL; on ETS/NVS it compiles to match specs / a fold. Same surface, per
backend lowering. v1 combinator set: `where`, `select`, `order_by`, `limit`,
`sum`/`count`/`min`/`max`, and `join_on` over a declared `Ref` edge only
(arbitrary joins are ledgered, §11.1).

A raw-SQL escape hatch exists but requires `unsafe` (hiding principle 4) and
is itself a ledger item (§11.2): the string is unchecked, the result row shape
is asserted, and the call site is greppable.

## 4. Migrations — the centerpiece

Schemas are versioned: `schema Pantry v3`. Each version bump ships a
`migrate from` block; the chain `v1 → v2 → … → vN` is the store's history and
travels with the firmware/app.

```cure
schema Pantry v3
  ...                                     # tables as in §2

  migrate from v2
    table User
      handle renamed from nickname        # explicit rename, data preserved
      age: {n: Int | n >= 0} = 0          # new column: default for old rows
      drop legacy_flags                   # explicit drop — audited data loss

    table Item = fn(old: v2.Item) -> Item =
      Item{ id: old.id, label: old.label,
            qty: max(old.count, 0),       # v2.count : Int (unrefined)
            owner: old.owner }
```

Two forms, one meaning. The declarative form (renames/defaults/drops) covers
the common case and elaborates to a function; the function form handles
anything (splits, merges, recomputation). Either way the compiler checks:

1. **Totality.** The migration passes size-change termination like every Cure
   function — a migration provably cannot hang a device mid-flash-rewrite.
   This matters precisely because migrations run unattended on hardware.
2. **Type-correctness against BOTH schemas** (the landed dependent-records
   machinery): the domain is exactly `v2.Item`, the codomain exactly
   `v3.Item`, refinements included — `max(old.count, 0)` is *required*
   because `v2.count` was unrefined and `v3.qty` demands `n >= 0`. Writing
   `qty: old.count` is a compile error naming the refinement.
3. **No silent data loss.** Every old field must be mapped, renamed, or
   dropped **explicitly**. An unmapped `v2.User.nickname` is a compile error
   (§8 explainer) — the design's answer to the classic "migration ate my
   column" incident.
4. **Chain completeness.** `v3` must reach every version still deployed
   (fleet manifest, §9); a device on v1 migrates by composing v1→v2→v3 —
   composition of checked-total functions needs no further check.

Rollback is deliberately **not** a checked construct: reverse migrations are
lossy in general (a `drop` has no inverse) and pretending otherwise is a lie.
Recommended stance — forward-only migrations plus a pre-migration backup
snapshot written by the store actor before the chain runs; "rollback" is
restore-from-backup. Ledgered (§11.3).

## 4b. OTA device-state migration (absorbed §6.11)

The same machinery, pointed at the state a device already holds. A `reducer`
(parent §5.5) or `fsm` model can be declared persistent:

```cure
reducer Door fsm
  persistent in nvs                       # model shape joins the version chain
  ...
```

`persistent` registers `Door.Model` — the state-indexed dependent pair — in
the module's schema version chain **automatically**: the user writes no table.
On every firmware build, the compiler compares the model shape against the
previous released version (the release ratchet already tracks artifacts); a
changed shape without a `migrate from` block **fails the build**, not the
fleet. The migration maps old states to new states — including the honest
hard case, a *removed* state, which the function form handles by total match
(`v1.Opening{..} -> Closed{..}` — every old constructor must be covered,
which is just ordinary match coverage). At boot after OTA, the runtime loads
the stored version tag, runs the composed chain, and hands the reducer a
valid current-version model. A fleet mid-rollout (fleet spec §9) has devices
on mixed versions; each self-migrates on its own schedule — no coordination
needed because migration is node-local by construction.

## 5. Backends — one surface, honest per-target lowering

Declared once per schema: `persist in <backend>`.

| Backend | Target | Durability | Notes |
|---|---|---|---|
| `ets` | host + device | none (RAM) | default when `persist` omitted; AtomVM ETS via the project's `whereis` shim — no Registry, no persistent_term, ever |
| `dets` | host only | file | zero-dependency durable option on full BEAM |
| `sqlite("f.db")` | host only | file | via NIF (§11.4); the only backend with a real query engine — pipelines compile to SQL |
| `nvs` | device | flash KV | ESP32 NVS-style key-value; small, page-erased, finite write endurance |

Device size-realism: NVS is a few tens of KB of usable space with per-entry
limits — right for a reducer model, a config record, a small table of
setpoints; **wrong for logs or telemetry history**. The compiler computes a
worst-case serialized size per table from the schema (refinements bound it:
`Bounded(3)` is one byte, `{s: String | len(s) <= 16}` is 17) and emits a
budget report; an unbounded column (`String`, `List(T)`) in an `nvs` schema
is a *warning* with an explainer suggesting a length refinement. Write-budget
and wear notes are ledgered (§11.6). Serialization itself is the `codec`
macro (one blessed binary codec per backend; round-trip proved once,
centrally, inherited — parent §7.2).

## 6. Concurrency — an actor per store

BEAM idiom, no raw shared mutation: each `Store(Pantry)` is one actor owning
the backend handle. Reads are calls; writes are serialized through the
mailbox. A transaction is a function passed to the actor:

```cure
s |> transact(fn(tx) ->
  let u = tx.users |> get(uid)
  tx |> update(Item, iid, fn(i) -> Item{ ..i, owner: u.id }))
```

Isolation honesty: because all writes serialize through one actor, every
transaction is trivially serializable *per store* — that is the whole story,
stated plainly. Ref checks and refinement checks run inside `transact` before
commit; a violation aborts the function's effects (the backend write is
buffered until the function returns). There is no cross-store transaction
(§11.7, §12). Reads outside `transact` see the latest committed state.

## 7. What the dependent types do invisibly

- Refinement columns make row invariants ambient: reads *carry* them, writes
  *owe* them, and most write obligations discharge by computation or by a
  `when` guard flowing into the refinement context (parent §9.16 machinery).
- `Ref(T)` / `Id(T)` are phantom-indexed ints — cross-table key confusion is
  inexpressible; erasure makes them free.
- Migration checking is dependent records at full stretch: two versions of
  "the same" record are two distinct types, and the migration is the only
  typed bridge. Version tags on stored blobs are the runtime shadow of that
  index.
- A persistent reducer model is the state-indexed GADT pair; migrating it is
  a total function on a sum-of-records — match coverage *is* the "no state
  left behind" guarantee.
- Size budgets (§5) are read off refinements — the type system doing
  capacity planning.

## 8. Explainers (§4 of the parent — errors speak schema vocabulary)

```
error[E160]: migration v2 -> v3 does not say what happens to `User.nickname`
  --> pantry.cure:31
  Every old field must be handled. Choose one:
    handle renamed from nickname     # keep the data under a new name
    drop nickname                    # discard it — explicit and audited
    (or map it inside a `table User = fn(old) -> ...` migration)

error[E161]: this write can violate `qty >= 0`
  --> pantry.cure:58
  `i.qty - taken` may be negative when taken > i.qty.
  Guard it: `when taken <= i.qty ->` (the guard discharges the check).

error[E162]: cannot delete this User — 3 Items still reference it
  (runtime, transaction aborted)
  `Item.owner` is declared `on_delete restrict`. Delete or reassign the
  items first, or declare `on_delete cascade` if that is the intent.
```

## 9. `check` integration (parent §7.5 — the macro ships its templates)

- **Migration round-trip:** for every `migrate from v_{n-1}`, generate
  `v_{n-1}` records *from the old schema's refinements* (generators are free —
  the refinements are the generators) and check that each migrates without
  error and the result satisfies every `v_n` refinement. This is the test
  users would never write and always need; it runs on `cure test` with zero
  user code.
- **Query–refinement consistency:** generated rows in, every combinator
  pipeline out — results satisfy their stated types (guards SQL-lowering
  bugs, not user code; still shipped, per the packet/codec precedent).
- **Persistent-reducer template:** generated old-version models migrate to
  valid new-version models (match coverage already proves totality; the
  property exercises the refinements on payload fields).
- Static discharge applies as everywhere: a migration whose obligations all
  reduce reports *proved by construction — 0 runs*.

## 10. Relations

- **`workflow`** (parent §7.3): event-sourced persistence — the emissions log
  lives in a `schema` table; replay is `Signal.scan` over it. A native
  log-store mode is ledgered (§11.5).
- **`reducer`**: `persistent` models, §4b — the OTA story.
- **`config`** (parent §6.7): a config record is a one-row schema; versioning
  config across OTA reuses the version chain verbatim.
- **`fleet`**: mixed-version rollout (fleet §9) consults the migration chain
  to know which versions remain reachable; §4's chain-completeness check is
  the compile-time side of that handshake.
- **`codec`**: storage serialization of rows/models; round-trip proved once
  at the library level, inherited by every schema.

## 11. Open decisions (ledger)

1. **Query expressiveness bounds** — v1 ships `where`/`select`/`order_by`/
   `limit`/aggregates and `join_on` over declared `Ref` edges only. General
   joins, group-by, subqueries: decide after real programs exist.
2. **Raw-SQL escape hatch shape** — `unsafe sql("...")` with an asserted row
   type; whether parameters are at least injection-safe by construction
   (likely yes: typed placeholders, string splicing rejected).
3. **Rollback story** — recommended forward-only + pre-migration backup
   snapshot (restore is the rollback). Confirm snapshot placement per
   backend (NVS space may not afford a full copy — possibly page-swap).
4. **SQLite NIF availability** — vendor a pinned SQLite + NIF with the
   toolchain vs. system dependency; NIF crash isolation stance on full BEAM.
5. **Event-sourcing-native mode** — store = emission log + replay (snapshot
   as cache) vs. today's snapshot tables. Workflow wants it; decide whether
   it is a `schema` mode or a `workflow`-owned layer above it.
6. **NVS wear/write budget** — per-table write-rate warnings (a `scan`
   persisting at 10Hz murders flash); whether the cost-grade axis eventually
   carries a write-budget obligation.
7. **Multi-store composition** — several schemas in one app: separate actors
   (current answer), cross-store refs (currently inexpressible — keep it
   so?), and whether a module can mount another module's store.
8. **Indexing declarations** — `index on Item.owner` as a performance-only
   annotation (no semantic weight); v1 may auto-index `Ref` columns and stop
   there.

## 12. Non-goals

- **Not an ORM for external/shared databases** — `schema` owns its store;
  pointing it at a DBA-managed Postgres with concurrent foreign writers
  breaks every invariant the design rests on. Out of scope, permanently.
- **No distributed transactions** — cross-node coordination is flow-level
  (`fleet`'s ownership rules); a store belongs to one node, full stop.
- **No full SQL surface** — the combinators are the language; SQL is a
  lowering target and an `unsafe` escape hatch, not a macro goal.
- No schema inference from existing databases; no down-migrations (§11.3).
