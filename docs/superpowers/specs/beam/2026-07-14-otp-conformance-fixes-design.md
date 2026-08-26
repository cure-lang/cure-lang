# `Std.Otp` conformance fixes — design

**Date:** 2026-07-14
**Status:** approved (design gate); implementation pending
**Source:** `https://github.com/cure-lang/cure-otp/tree/main/docs/research/process-types/raw-algebra-conformance-checklist.md` (executed audit, 2026-07-14)
**Design being repaired:** `docs/superpowers/specs/beam/2026-07-09-typed-beam-process-algebra-design.md`
**TCB delta:** zero — every change is elaborator + stdlib. The kernel is untouched.

---

## 1. Problem

The executed conformance audit compared `lib/std/otp_raw.cure` (the sealed raw base)
and `lib/std/otp.cure` (the typed surface) against a machine-checked reference
semantics of Core Erlang, against the AtomVM source, and against probes of both the
real BEAM BIFs and the Cure elaborator. It found the typed layer **claiming things
the BEAM does not deliver**:

- **F-2c** `raw_whereis : Atom -> Effect(RawPid(m,m))` **asserts the lookup succeeds.**
  The BEAM returns the bare atom `undefined` for an unknown name (probed on OTP;
  `globalcontext.c:641` on AtomVM). A well-typed `Pid(m)` can therefore *be* the atom
  `undefined`, and the next `tell` emits `erlang:send(undefined, …)` → `badarg`.
- **F-2a** `Pid(m)` and `GenServer(q,r)` are **typealiases of the same constructor**,
  so `Pid(m)` *is* `GenServer(m,m)`. `call`/`cast`/`stop` on a plain spawned process
  typecheck; at runtime the caller blocks 5 s and then exits `timeout`.
- **F-4** Ten raw ops declare `Effect(Unit)` for BIFs that return real terms
  (`send` → the message, `link`/`exit`/`register`/… → `true`, `cast`/`stop` → `ok`,
  **`cancel_timer` → an `Int`**, the audit's own **F-4c**, its harshest-worded instance
  of this defect — "the worst of the `Unit` lies"). `emit.ex` performs no result
  coercion, so the value inhabiting `Unit` (runtime atom `unit`) is in fact an integer
  or a boolean. This violates the parent spec §3.1 ("every extern at its most
  permissive **honest** BEAM type"). *Label note:* F-4c is one instance of F-4, not a
  separate defect class — §3.4 fixes it as part of the same table, alongside the other
  nine.
- **F-3** `raw_exit`'s `reason` is fully polymorphic, erasing the
  `normal`/`kill`/other distinction that all three of the semantics' exit rules turn on.
- **F-5** `MonitorRef` and `TimerRef` are aliases of one `Ref` type, so
  `cancel_timer(monitor_ref)` typechecks; `demonitor` omits `flush`, so a stale `DOWN`
  can outlive it; and the module docstrings imply a delivery/ordering guarantee the
  BEAM does not give.

## 2. Scope

### In scope

F-2c, F-2a, F-4 (except the `start_link` return — see below), F-3, F-5, plus the
documentation of the two platform hazards the audit surfaced (AtomVM's broken
`send_after`/`cancel_timer` pairing, and `call`'s partiality). F-2a's kind split also
resolves the audit's own **F-2b** (`raw_stop`'s row: `stop` accepting any `Pid(m)`) as
a corollary, without a separate patch — see §3.3. *Label note:* the audit's own **F-2**
heading (checklist §4, "`call` is typed as a total function; `Pid` and `GenServer` are
the same type") bundles two symptoms under one finding: the type-collapse and `call`'s
totality. This document splits them, because it fixes only one: **"F-2a" is this
document's own coinage** for the type-collapse half (fixed in §3.3) — the audit never
uses "F-2a" — chosen to sit alongside the audit's real "F-2b"/"F-2c" sub-labels without
colliding with them. The other half keeps no F-number at all here; it is called "the
`call`-totality gap" (never "F-2b", which the audit already spent on the `stop` row)
and stays out of scope, below.

### Explicitly out of scope — and why

- **F-1 — the pid index is founded on nothing.** Every pid-producing op returns
  `Pid(m)` at a *free* implicit `m`; `spawn`'s thunk is `() -> Unit` and says nothing
  about messages. Grounding `m` is the parent spec's §4.2 code derivation, which is
  **Rung 2** and gated on the macro facility. Out of scope by the operator's own
  sequencing.
- **Honest `start_link` return (F-4b).** `gen_server:start_link` returns
  `{ok,Pid} | {error,Reason} | ignore`. Typing it honestly means producing a *typed*
  `GenServer(q,r)` from an untyped BEAM tuple — which is precisely the unfounded
  assertion F-1 describes. It is the same problem, and it is deferred with F-1 as one
  bundle. `raw_start_link` keeps `Effect(Tuple)` and gains a docstring stating the
  `ignore` lie on OTP.
- **The `call`-totality gap.** `gen_server:call` does not *return* an error; on
  timeout or server death it **exits the caller**. A crash produces no value, so
  `Effect(r)` is *partial*, not unsound — no wrongly-typed value is ever produced. The
  honest repair is an **additive** `try_call` over a `cure_std_otp` try/catch runtime
  shim (precedent: `cure_std_gen`, `cure_std_time`). That needs its own design and its
  own AtomVM verification, is additive, and blocks nothing. Deferred; `call`'s
  partiality is **documented at the op** in this batch.

## 3. Design

### 3.1 `@erases(<class>)` — a declared runtime shape for opaque FFI carriers

`Cure.Elab.Union` decides whether an anonymous union is discriminable by asking each
member for its **runtime class** — the Erlang guard that recognises its erasure
(`is_integer`, `is_atom`, `is_list`, …). `Union.class_of_data_name/1` currently answers
by *name*, for a fixed set (`Bool`, `Nat`, `Bounded`, `List`), and returns
`:unsupported` for everything else. `discriminable/1` **rejects** a union containing an
`:unsupported` member.

An `opaque type` has **zero constructors**. It has no Cure-side erasure to infer: its
values arrive only across an `@extern`. So its runtime shape must be **declared**.

Introduce an item-level decorator on opaque type declarations:

```cure
@erases(:pid)
opaque type RawPid(m, r, k)

@erases(:reference)
opaque type MonitorRef
```

*Forward reference:* both examples are written in their **post-batch** shape — the
3-arg `RawPid(m, r, k)` from §3.3's kind split, and `MonitorRef` from §3.6's reference
split. `@erases` itself needs neither; it is illustrated on the finished carriers because
that is what ships, not because either later change depends on `@erases` to work.

- **Admissible classes:** `:pid`, `:reference`, plus the existing
  `:integer`, `:float`, `:binary`, `:atom`, `:boolean`, `:list`. Each maps to exactly
  one total Erlang guard (`is_pid`, `is_reference`, …). An unrecognised class is a
  compile error at the declaration, naming the admissible set. Concretely, `emit.ex`'s
  `class_guard/1` (`emit.ex:335-340`) gains two clauses — `class_guard(:pid), do: :is_pid`
  and `class_guard(:reference), do: :is_reference` — alongside its existing six; this is
  the function `type_clause/1` calls (via `class_test/1`) to materialise the guard the
  discriminating `case` actually emits.
- **Where it is stored:** on the opaque family record (`Inductive.opaque_family/3`
  gains an `erasure` field, default `nil`).
- **Who reads it:** `Union` resolves `{:data, name, _, _}` → the family's declared
  `erasure`, falling back to today's name-based table and then to `:unsupported`.
- **Overlap rules:** `:pid` and `:reference` overlap **nothing** — not each other, not
  `:atom`, not `:unsupported` (a user ADT erases to a bare atom or a tagged tuple,
  never a pid or a reference). This makes `RawPid(...) | :undefined` a true `Union<…>`
  (disjoint erased value sets), not a `Disjoint<…>`.
- **Non-goal:** `@erases` is *not* a safety proof. It is an assertion by the author of
  a sealed `unsafe` FFI module that the foreign value has that shape — exactly the kind
  of claim the raw base exists to concentrate. Applying it to a *non-opaque* type is a
  compile error (a type with constructors already has an inferable erasure; a second,
  possibly contradictory, answer must not exist).

**Env threading.** `Union.runtime_class/1` is today pure on the member map, but members
are rebuilt from their family key by `Union.members_of/2` (`explode/2`), so the class
cannot simply be cached on the member at canonicalisation — it must be resolvable from
the key at every use. `runtime_class`, `disjoint_only?`, `family_key`, `discriminable`
and `discrimination_order` therefore all take `env`. In `Cure.Elab.Union` itself,
`canonicalise/3` (`union.ex:177`) and `declare/3` (`union.ex:458`) already bind `env`,
so widening the calls they make is mechanical. In `emit.ex`, only `extern_union_members/2`
(`emit.ex:232`) already has `env` — its caller `function_form/2` (`emit.ex:220`) binds it.
`type_clause/1` (`emit.ex:307`), its caller `union_dispatch/2` (`emit.ex:284`), and *its*
caller `extern_form/4` (`emit.ex:260`) currently carry **no** `env` at all: the raw remote
call is emitted from `union_members` alone, several frames removed from the nearest `env`
binding. All three gain an `env` parameter, threaded down from `function_form/2` through
`extern_form/4` and `union_dispatch/2` to `type_clause/1`'s call into `runtime_class`. Still
mechanical — no new control flow, no new failure mode — just a longer, fully-named
parameter chain than "already has one" suggested.

### 3.2 F-2c — `whereis` returns an `Option`

```cure
# Std.Otp.Raw — honest and permissive
@extern(:erlang, :whereis, 1)
fn raw_whereis({m: Type}, {r: Type}, {k: PidKind}, name: Atom)
  -> Effect(RawPid(m, r, k) | :undefined)

# Std.Otp — the typed facade reintroduces the failure case
fn whereis({m: Type}, name: Atom) -> Effect(Option(Pid(m)))
```

`emit.ex` already re-tags an extern's union return at the FFI boundary
(`union_dispatch/2`): the literal member `:undefined` is matched by exact value and
comes first; the type member `RawPid(...)` is matched by `is_pid`. There is
deliberately no catch-all — a shape outside the declared union is a `CaseClauseError`
naming the offending value, which is the honest outcome. The typed `whereis` matches
the union and returns `Some(pid)` / `None()`.

*Forward reference:* the raw signature above already carries `{k: PidKind}` and the
3-arg `RawPid(m, r, k)` — vocabulary this document does not define until §3.3. The two
fixes land in the same batch and `raw_whereis`'s parameter list is written post-split;
§3.3 explains why `whereis` stays `Plain`-only despite the raw op being kind-polymorphic.

### 3.3 F-2a — an erased kind index separates `Pid` from `GenServer`

```cure
type PidKind = Plain | Server           # erased; a phantom index

opaque type RawPid(m, r, k)             # k : PidKind

typealias Pid(m)          = RawPid(m, m, Plain)
typealias GenServer(q, r) = RawPid(q, r, Server)
```

`Pid(m)` and `GenServer(q,r)` are now **distinct types**. The op signatures split
accordingly:

- **`Server`-only:** `call`, `cast`, `stop` — the OTP-behaviour ops. Calling a plain
  spawned process is now a compile error, which is what F-2 asked for (this also
  resolves the audit's own **F-2b** — `raw_stop`'s row in the checklist table:
  "Typed `stop` accepts **any** `Pid(m)`... Same root cause as F-2 (`Pid` ≡
  `GenServer`)" — as a corollary of the same kind split, without a separate patch).
- **Kind-polymorphic** (`{k: PidKind}`): `tell`, `send_after`, `link`, `unlink`,
  `monitor`, `exit`, `is_alive`, `register`. Raw-sending to a gen_server is
  legitimate BEAM practice — it lands in `handle_info` — so `tell` must accept both
  kinds.
- `spawn`/`spawn_link`/`self` produce `Plain`.
- `whereis` stays **`Plain`-only** (§3.2: `Effect(Option(Pid(m)))`, no `{k: PidKind}`).
  A registered name is not statically known to be a `gen_server` — recovering a typed
  `GenServer(q,r)` handle from a bare `Atom` name needs a name→code association this
  batch does not build. That is the parent spec's own ledger item (§13.7: "`whereis`
  returns a `RawPid`; recovering a typed `Pid(m)` from a name needs a name→code
  association... Design when named-process use returns"), not reopened here.

The index is erased (0-quantity, phantom): **zero runtime cost, zero ESP32 footprint.**

This does *not* fix F-1 — a `GenServer(q,r)` value still has to come from somewhere,
and today it can only be a function parameter. What it does fix is the *collapse*: the
two handles can no longer be silently interchanged.

### 3.4 F-4 — honest raw result types

| raw op | was | becomes |
|---|---|---|
| `raw_send` | `Effect(Unit)` | `Effect(m)` — the BIF returns the message |
| `raw_link`, `raw_unlink`, `raw_exit`, `raw_register`, `raw_unregister`, `raw_demonitor` | `Effect(Unit)` | `Effect(Bool)` — returns `true` |
| `raw_cast`, `raw_stop` | `Effect(Unit)` | `Effect(Atom)` — returns `ok` |
| `raw_cancel_timer` | `Effect(Unit)` | `Effect(Int \| Bool)` — remaining ms, or `false` |
| `raw_start_link` family | `Effect(Tuple)` | unchanged; docstring records the `ignore` lie (deferred, §2) |

The typed wrappers keep their existing result types by **discarding** the raw result:

```cure
fn tell({m: Type}, {r: Type}, {k: PidKind}, dest: RawPid(m, r, k), msg: m) -> Effect(Unit) =
  let _sent = raw_send(dest, msg)
  unit()
```

The effect elaborator already supports this — a `let` sequences the effect, and a pure
value in an `Effect`-expected tail position is injected as `{:effect_pure, …}`
(`elaborator.ex`), which `emit.ex` lowers away entirely (`lower(env, {:effect_pure, a})
= lower(env, a)`). No new machinery, no runtime cost.

`cancel_timer` is the one whose typed result genuinely changes, because the information
is real and worth surfacing:

```cure
fn cancel_timer(ref: TimerRef) -> Effect(Option(Int))   # Some(ms_remaining) | None
```

*Forward reference:* `TimerRef` is §3.6's replacement for today's bare `Ref` parameter;
it is used here, ahead of its introduction, because the result-type fix (this section)
and the reference-type split (§3.6) land on the same signature in the same batch.

### 3.5 F-3 — a precise exit reason

The three exit rules of the reference semantics case on `reason ∈ {normal, kill, other}`
crossed with the target's `trap_exit` flag and the signal's link flag. A polymorphic
`reason` cannot express which of the three outcomes an `exit` can have.

The **raw** op stays permissive (spec §3.1 — the raw base is the *most permissive
honest* type), but the **typed** layer narrows to a real sum:

```cure
type ExitReason = Normal | Kill | Because(Atom)

fn exit({m: Type}, {r: Type}, {k: PidKind}, pid: RawPid(m, r, k), reason: ExitReason) -> Effect(Unit)
```

`exit` still — correctly — makes **no** type-level claim that the target dies. That was
already conformant and stays that way. What changes is that the reason is now legible.

`process_flag(trap_exit, _)` remains **absent** from the raw base. That omission is
intentional and currently sound (behaviours own the mailbox; raw `receive` is rejected
at elaboration with E043), and it is already on the parent spec's ledger. It is not
reopened here.

### 3.6 F-5 — the small honest things

- **Distinct reference types.** `opaque type MonitorRef` and `opaque type TimerRef`,
  both `@erases(:reference)`, replacing the single `Ref` aliased twice. `demonitor`
  takes a `MonitorRef`; `cancel_timer` takes a `TimerRef`; `monitor` and `send_after`
  produce the respective one. `cancel_timer(monitor_ref)` becomes a compile error.
  *"Replacing" is scoped to the typed layer:* it is `otp.cure`'s two typealiases
  (`typealias MonitorRef = Ref`, `typealias TimerRef = Ref`) that are replaced by two
  independent opaque types. The raw `opaque type Ref` in `Std.Otp.Raw` itself is
  untouched — see the `demonitor` bullet below, which keeps one raw op typed over it.
- **`demonitor` gains `flush`.** A new raw op, following the same full-arity pattern
  `raw_start_link_unnamed` already uses for its fixed `opts: List(Atom)` — the BIF's
  option list is a real Cure-visible parameter, not silently baked in:
  `raw_demonitor_flush(ref: MonitorRef, opts: List(Atom)) -> Effect(Bool)` →
  `@extern(:erlang, :demonitor, 2)`. Typed `demonitor` calls it as
  `raw_demonitor_flush(ref, assert_type [:flush] : List(Atom))` instead of calling
  `raw_demonitor`, so a stale `DOWN` cannot outlive the call. With only `flush` (no
  `info`) in the option list, the BIF always returns `true` — same honest type as the
  F-4-fixed `raw_demonitor`. AtomVM supports `flush` natively (`nifs.c:5022-5061`), so
  this is universal. `raw_demonitor : Ref -> Effect(Bool)` (arity-1, no options, F-4's
  fix applied) **stays** in the raw base alongside it — honest and unused by the typed
  layer is not a defect (`raw_term` is the existing precedent: present in `Std.Otp.Raw`,
  not driving any typed wrapper). `raw_demonitor_flush` joins the §4 regression-pin
  table (item 13) alongside it, both under their honest `Effect(Bool)` type.
- **Docstrings stop implying guarantees the BEAM does not give.** The `Std.Otp.Raw`
  header currently says the effect discipline "forbids duplicating, dropping, or
  reordering a `send`/`call`". That is about the *program's effect sequence*, not
  mailbox arrival, and a reader can easily mistake it for a delivery guarantee. It is
  reworded to state what the BEAM actually promises: **pairwise sender→target ordering
  only, and no delivery at all** (a send to a dead process silently succeeds).
- **The two platform hazards are documented at the ops**, not only in a research doc:
  - `send_after`: on AtomVM the returned ref is **not cancellable** — `send_after/3`
    registers the timer under a different ref than the one it hands back
    (`timer_manager.erl:87-91`), so `cancel_timer` returns `false` and the message
    fires anyway. Retargeting at `erlang:start_timer/3` would fix cancellability but
    changes the delivered message shape to `{timeout, Ref, Msg}`, which changes the
    receiver's accepted message set — so it is a *typed* change, deferred with the
    Rung-2 work, not a silent substitution.
  - `call`: partial. On timeout (default 5000 ms) or server death, **the caller
    exits**. No value is returned at the wrong type; there is simply no continuation.

## 4. Testing

Red-test-first throughout: for each numbered item below, write the test, run it, confirm
it fails for the stated reason, then change only the elaborator/stdlib code needed to make
it pass, refactoring afterward with the suite kept green. The existing
`test/cure/stdlib/otp_test.exs` is the model: programs are put through `Program.elaborate/1`
and asserted `{:ok, _}` or `{:error, _}`. Once a test is green it is immutable — a later step
never weakens or deletes a passing test to accommodate a regression. The two pre-existing
tests flagged below are the sole exception, and are named explicitly *because* they encode
the very defects this batch closes (not because a test may be edited whenever doing so is
convenient).

**Elaborator (`@erases` + Union):**
1. An opaque type with `@erases(:pid)` is a legal union member; without it the same
   union is rejected with `{:unsupported_member_shape, …}`.
2. `@erases` with an unrecognised class is a compile error naming the admissible set.
3. `@erases` on a **non-opaque** type is a compile error.
4. `RawPid(...) | :undefined` canonicalises to a `Union<…>` (disjoint erasures), not a
   `Disjoint<…>`.
5. Emission: the extern wrapper for a `pid | :undefined` return dispatches on
   `R =:= undefined` first, then `is_pid(R)`, and injects the matching constructor.

**Typed surface (`otp.cure`):**
6. `whereis` returns `Option(Pid(m))`; a program that `tell`s the result **without
   matching** is a compile error (this is the F-2c red test — it typechecks today).
7. `call` on a `Pid(m)` is a compile error; `call` on a `GenServer(q,r)` succeeds
   (F-2a red test — the former typechecks today).
8. `cast`/`stop` on a `Pid(m)` are compile errors.
9. `tell` on a `GenServer(q,r)` **succeeds** (kind-polymorphic — guards against
   over-narrowing).
10. `exit(pid, Normal)` succeeds; `exit(pid, 5)` is a compile error.
11. `cancel_timer(monitor_ref)` is a compile error; `demonitor(timer_ref)` is a compile
    error.
12. `cancel_timer` returns `Effect(Option(Int))`.

**Regression pin (the concrete `no_widening_narrow`):**
13. A test that asserts the **declared return type of every op in `Std.Otp.Raw`**
    against an explicit table. The parent spec's §12 `no_widening_narrow` validator
    cannot be automated in general — it would need an oracle for every BIF's return
    type — but pinning the audited table makes any future widening a failing test
    rather than a silent lie. This test carries a comment pointing at the audit as its
    source of truth.

The existing OTP tests that assert `start_link` returns `Effect(Tuple)` continue to
pass unchanged. Of the `beam_ops`-exercising tests in `test/cure/stdlib/otp_test.exs`,
most are unaffected, but this batch breaks two by construction and both need updating
alongside the implementation (they were exercising defects this batch closes, not
incidental damage):

- `"beam_ops expands every initial operation to ordinary algebra calls"` declares
  `fn stop_it(p: Pid(Cmd)) -> Effect(Unit) = beam_ops stop p`. Once `stop` is
  `Server`-only (§3.3), `p: Pid(Cmd)` no longer typechecks there — same fix as the
  `call`-on-`Pid` case: rewrite `stop_it` to take a `GenServer(Cmd, r)`.
- `"beam_ops expands lifecycle, timer, monitor, and link operations"` declares
  `cancel`/`observe`/`unobserve` over the bare type `Ref`, and asserts
  `cancel(r: Ref) -> Effect(Unit)`. Once `Ref` is retired for distinct `MonitorRef`/
  `TimerRef` (§3.6) and `cancel_timer`'s return becomes `Effect(Option(Int))` (§3.4),
  both the type name and `cancel`'s declared return type must change.

Every other `beam_ops` test (self, tell/send, cast, spawn, spawn_link, start_link,
start_statem, start_supervisor) is unaffected — none of them exercises `stop`, `Ref`,
or a bare `Pid` used where the new signatures now require a `GenServer`.

## 5. Consequences

- `Std.Supervisor` uses `Std.Otp.Raw` only for `RawTerm`/`raw_term` — unaffected.
- `Std.Fsm`, `Std.Actor`, `Std.Process`, `Std.App` reference `Std.Otp` only in
  docstrings — unaffected.
- `Cure.Stdlib.Preload` lists the modules; no change.
- **No kernel change. No TCB delta.** `Union` and `emit` are elaborator; the rest is
  stdlib.

## 6. Deferred, as one bundle

F-1 (code derivation grounding the pid index), the honest `start_link` return, `try_call`
over a `cure_std_otp` shim, and retargeting `send_after` at `start_timer/3`. All four
need either Rung 2 or a runtime shim with its own AtomVM verification. They are recorded
in §6 of the audit and remain there.

---

## 7. Planning amendments (2026-07-14)

Four of this spec's constructions were probed against the actual compiler while writing
the implementation plan. Three do not elaborate as written. The defects they close are
unchanged; the mechanisms are corrected here, and the plan implements *these*.

### 7.1 `PidKind` is a pair of phantom TAGS, not a kind

§3.3 declares `opaque type RawPid(m, r, k: PidKind)`. **Kinded type parameters do not
exist** — not on opaque types and not on ordinary ones. `type Box(a, b, k: Kind)` is
rejected with `{:conversion_failure, {:data, :Kind, [], []}, {:type, 0}}`: a type
parameter is always at kind `Type`. (Only *indices* may be kinded by a data type.)

Adding kinded parameters is a real language feature and is not in this batch's budget.
The same distinction is carried by **phantom tags at kind `Type`** — the standard
Haskell/Idris encoding that predates DataKinds:

```cure
opaque type Plain
opaque type Server
opaque type RawPid(m, r, k)          # k : Type, the default
```

`typealias Pid(m) = RawPid(m, m, Plain)` and `typealias GenServer(q, r) = RawPid(q, r, Server)`
are then distinct types, which is the entire content of F-2a. Kind-polymorphic ops
quantify `{k: Type}`.

What is lost: `k` may be instantiated with any type, so `RawPid(Cmd, Cmd, Int)` is
well-formed nonsense. It is **unreachable** nonsense — no operation produces one and no
typealias names one — and admitting it costs no soundness. Verified to elaborate:
ground union member, kind-polymorphic op, and `Server`-only op all check.

### 7.2 `whereis` returns an UNSENDABLE pid, not `Option(Pid(m))`

§3.2 declares `raw_whereis({m}, name: Atom) -> Effect(RawPid(m, m, Plain) | :undefined)`.
**A union member must be ground.** A member mentioning the type variable `m` is rejected
with `{:union_member_not_ground, …}`, and the restriction is principled: a union family is
generated per member *key*, so `RawPid(m, …)` would key by the variable's spelling and two
callers' unrelated `m`s would collide in one family. Loosening it means parameterised union
families — a feature, not a fix.

So the union cannot mention the message type, and the message type cannot be re-attached
afterwards either: `believe_me` was **deleted** with `Std.Access` (see `lib/std/optic.cure:6`),
and no BEAM identity BIF exists to smuggle a cast through an `@extern`.

This is not an obstacle to route around — it is the spec having tried to fix half a lie.
Today's `whereis` asserts **two** things: that the lookup succeeds (F-2c) *and* that the
result carries messages of type `m` (F-1). Nothing associates a registered name with a
message type; that association is precisely what F-1's code derivation would build, and
F-1 is deferred (§6). Fixing F-2c while preserving the `m` claim is therefore impossible
by construction.

The honest type drops both lies:

```cure
type NoMessage = |                                    # uninhabited
typealias BarePid = RawPid(NoMessage, NoMessage, Plain)

@extern(:erlang, :whereis, 1)
fn raw_whereis(name: Atom) -> Effect(BarePid | :undefined)

fn whereis(name: Atom) -> Effect(Option(BarePid))
```

`BarePid` is ground, so it is a legal union member. It is not a crippled type: `link`,
`unlink`, `monitor`, `exit` and `is_alive` accept it unchanged, because they are
message-type-polymorphic and never cared about `m`. Only `tell` becomes uncallable — it
would demand a `NoMessage` argument, and `NoMessage` has no constructors. That is the
correct and complete statement of what the BEAM registry gives you: *a handle you may
supervise but must not send to, until something founds its message type.*

This **removes** an unsound capability rather than preserving it, which is this batch's
mandate. Nothing in the tree uses the old signature (`lib/std/otp.cure:170` is the
definition; the only other mention is a name in a test list).

### 7.3 An `@extern` may return `Effect(<union>)` — new prerequisite

Every operation in `Std.Otp.Raw` is `Effect`-typed, and §3.2/§3.4 give two of them union
returns. **A union under `Effect` is currently rejected** with
`{:extern_returns_union, …}`: both the declaration check (`declarations.ex:437`) and the
wrapper emitter (`emit.ex:233`) match the codomain against a union family *exactly*, and
neither looks through `Effect`.

`Effect(T)` has no runtime representation — the elaborator injects `{:effect_pure, …}` and
`emit.ex` lowers it away — so an extern declared `Effect(Int | Bool)` hands back exactly the
same untagged Erlang value as one declared `Int | Bool`, and the re-tagging wrapper is
byte-for-byte identical. Both sites strip a single `{:effect_type, _}` before the check.

A union nested in a real structure (`List(Int | Bool)`) stays rejected — re-tagging would
have to walk the structure. `Effect` is not a structure.

This is a load-bearing prerequisite: **without it neither F-2c nor F-4's `cancel_timer`
is expressible at all**, since both need a union return on an `Effect`-typed extern.

### 7.4 A union match has no catch-all

§3.2 and §3.4 sketch `match … _ -> None()`. Union elimination requires **one arm per
member** — a type member as `n: Int -> …`, a literal member as the bare literal
`:undefined -> …` — and a non-exhaustive match is rejected by the coverage check. The
wildcard arms are replaced with exhaustive ones.
