# Cure's axiom surface — design

**Date:** 2026-07-10
**Status:** Phase 0 (ledger) and Phase 1 (conformance harness) landed on
`autopilot/axiom-surface` (unmerged, 2026-07-11); Phases 2–3 designed only.
**Thesis:** *No axiom should point at code we wrote.*

Supersedes the trust-ledger design of the same date, which is now Phase 0 of
this document.

## 1. Problem

Cure's claim is that the kernel checks everything: if it typechecks, it is
proved. That claim has holes, nothing enumerates them, and some of them are
false.

The largest hole is `@extern`. A bodyless `@extern` is a typed FFI postulate —
`lib/cure/elab/declarations.ex:234` says so in as many words: *"the signature IS
the type; there is no term to elaborate/check."* It asserts, without evidence,
that a BEAM function inhabits the declared Π type, is total, and is pure. The
stdlib carries 156 of them across 22 modules.

They divide by target:

| Bucket | Count | Targets |
|---|---:|---|
| `OTP` | 64 | `erlang` (31), `maps` (11), `math` (8), `string` (5), `unicode` (3), `rand` (2), `lists` (2), `os` (1), `io` (1) |
| `CURE RUNTIME` | 49 | `cure_std_crdt` (22), `cure_std_time` (9), `cure_std_regex` (7), `cure_std_http` (4), `cure_std_json` (3), `cure_std_gen` (3), `cure_std_test` (1) |
| `CURE BRIDGE` | 43 | `Elixir.Cure.FSM.Builtins` (17), `App` (9), `Actor` (8), `Sup` (7), `Process` (2) |

*(These counts are the design-time baseline. Phase 1 later retired `Std.Gen.shrink`
from an `@extern` to an `interface` (see §5.3), so the current totals are 155
externs / 48 `CURE RUNTIME`. The arithmetic below uses the baseline figures.)*

**92 of 156 — 59% — point at cure-lang's own Elixir, not at OTP.** Trusting
`erlang:length/1` is trusting OTP, which is reasonable and is not going to
change. Trusting `cure_std_crdt:or_add/4` is trusting 204 lines of Elixir in
this repository that nothing verifies. Those 92 could be tested, or replaced by
Cure, rather than assumed.

Nobody knew the number, because nobody could count.

## 2. Four axioms that are false

This is not hypothetical. Auditing the 49 `CURE RUNTIME` axioms by hand, against
the code they postulate, found four defects. Each is a signature the elaborator
believes and the implementation contradicts.

**`Std.CRDT.or_add` was impure.** It minted ORSet tags from a counter in the
process dictionary. The counter was keyed per *process*; tags are namespaced per
*node*, and a node is a logical replica, not an OS process. Two processes acting
as replica `:n1` minted identical tags, after which removing one element
tombstoned a different one. Fixed in `0377252` by making the tag a parameter, as
`stamp` already is on `lww_set/4`. **This axiom is now true.**

**`Std.Test.forall_shrunk` inhabits neither its type nor totality.** Declared
`fn forall_shrunk(gen: Atom -> t, property: t -> Bool, runs: Int) -> t`. At
`t = Int`, with a property that holds, it returns the atom `:ok`. With a property
that fails, it raises `{:property_failed_with_shrunk, _}`. Neither branch
produces a `t`. Verified:

```
forall_shrunk (t=Int, property holds) => :ok   is_integer? false
forall_shrunk (property fails)        => {:raised, ErlangError}
```

**`Std.Gen.shrink` violates parametricity.** Declared `∀t. t -> List(t)`, it
dispatches on the runtime representation of its argument (`is_integer`,
`is_list`, `is_tuple`, then a `[]` fallback). No parametric inhabitant of that
type can do this; the free theorem requires `shrink(g x) == map(g, shrink x)`
for every `g`. Verified with `g : Int -> String`:

```
shrink(g 4)      = []
map(g, shrink 4) = ["", "aa", "a", "aaa"]
```

Cure erases type arguments, so any future optimisation that appeals to
parametricity is unsound in the presence of this axiom.

**`Std.Http` postulates purity for network I/O.** All four externs are declared
with no effect — `fn get(url: String) -> Result(Response, HttpError)` — over an
implementation that calls `:httpc.request/4` and `:inets.start()`. This one
cannot be repaired by rewriting; see §7.

A fifth observation is structural rather than a defect. `Std.Time.now` *does*
carry an effect: `fn now() -> Instant ! Io`. But `declarations.ex` contains zero
occurrences of the string `effect`, so the dependent pathway drops the annotation
and postulates a pure function. The surface has an effect marker the kernel does
not model.

All four were found by hand, by reading types against code. That is exactly the
work Phase 1 mechanises.

## 3. Non-goals

- **No lockfile, no committed artifact, no `.cure/` tree.** The ledger prints to
  stdout. CI may capture and diff its output; that is CI's business, not a file
  every Cure library is forced to carry.
- **No `because:` justification field on `@extern`.** The ledger counts
  assumptions; it does not make you defend them in prose.
- **No effect system.** Modelling `! Io` in Core is the locked effects-in-Core
  decision (inert `Effect` former) and is out of scope here. This spec *reports*
  the gap and identifies which axioms depend on closing it.
- **Nothing in this spec enters the TCB.** `Cure.Audit.*` reads a kernel-checked
  environment and cannot influence checking. Its bugs produce a wrong report,
  never an unsound program.
- **The 43 `CURE BRIDGE` axioms are out of scope** — see §8.

## 4. Phase 0 — the ledger

The instrument. It answers *"what does this program assume without proof?"*, and
it is the only phase that depends on nothing.

```
cure audit trust <Module> [--format text|json] [--strict] [--target <t>]
```

Always exits 0 when a report was produced. `--strict` exits non-zero if
`UNAUDITED` is non-empty. **Never wired into `cure build`** — a compiler that
refuses to build over an audit trains people to hate the audit.

### 4.1 Why the collector reads `Core.Env`, not source

The cheap design — scan `.cure` files for `@extern` — is unsound in the near
future, and unsoundness in the *under-reporting* direction is the one failure a
trust ledger cannot survive.

Macros are intended to be expressive enough to contain arbitrary code, including
other macros, and therefore to emit arbitrary declarations. A macro can emit an
`@extern`. The macro facility design
(`docs/superpowers/specs/macros/2026-07-08-macro-facility-design.md` §9) places
expansion "entirely in the untrusted frontend, upstream of the elaborator," with
macro output "re-elaborated and kernel-checked exactly like hand-written code."

The elaborated `Core.Env` is therefore the only vantage point that observes every
axiom, today and after macros land. A macro-generated extern arrives in `env.defs`
as an `{:extern, {m, f, a}}` body, indistinguishable from a hand-written one.

**Cost, stated plainly, and it is worse than it looks.** A `Core.Env` ledger can
only audit code that dependent-elaborates. Measured on this branch, 2026-07-10:
**25 of 44** stdlib modules elaborate. The 19 that do not are `access`, `app`,
`core`, `crdt`, `equatable`, `gen`, `http`, `io`, `iter`, `json`, `match`,
`non_empty`, `ord`, `pair`, `regex`, `set`, `show`, `test`, `time`.

That list contains **every one of the seven `cure_std_*` modules**. So Phase 0,
on the day it ships, can audit zero of the 49 `CURE RUNTIME` axioms this document
exists to eliminate. They all land in `UNAUDITED`.

This is not a reason to scan source instead — a source scanner would report them
today and under-report silently forever once macros land, which is the trade in
the wrong direction. It is a reason to build Phase 1, which operates on the BEAM
functions themselves and needs no elaboration at all.

Phase 0 audits the axioms reachable from the 25 modules that do elaborate — among
them 34 of the 43 bridge axioms, `app.cure` being the exception — and *names*
what it cannot reach. Phase 1 covers the rest until #23 makes them visible.
(`app.cure` fails for an unrelated and already-diagnosed reason: it declares
`get_env/2` and `get_env/3`, and the dependent path has no arity overloading, so
it dies on `{:duplicate_definition, :get_env}`. Overloading is in flight on
another branch.)

`--strict` turns a non-empty `UNAUDITED` into a non-zero exit, and the list
doubles as a debt counter for #23/#18. It should shrink to nothing.

### 4.2 Trust classes

Ten things live in `Core.Env` (`lib/cure/core/inductive.ex:12`) — `families`,
`ctors`, `ctor_to_family`, `defs`, `certified`, `builtins`, `interfaces`,
`coherence`, `constrained`, `primitives`. Five classes drawn from them are
trust-relevant. Each is one pattern-match.

| Class | Detection | Meaning |
|---|---|---|
| `ffi_postulate` | `%{body: {:extern, {m,f,a}}}` | You assert BEAM's `m:f/a` inhabits this Π type, totally and purely. Nothing checks it. |
| `builtin_op` | `%{builtin_op: op}` when non-nil | You assert BEAM's operator implements Core's semantics. |
| `opaque_family` | `Inductive.opaque?/2` | An Agda-style `postulate` type. Sound only because `kernel.ex:238` refuses to eliminate it. |
| `hole` | `{:hole, _}` in a body | Incompleteness, not trust. Already blocks codegen. |
| `absurd` | `{:absurd}` in a body | Admitted only under an inconsistent context. Reported because it is the shape a soundness bug would exploit. |

**`builtin_op` is a fixed baseline, not a per-module contribution.**
`Env.register_builtin_op/3` (`inductive.ex:154`) is called from exactly three
sites, all in `lib/cure/core/builtins.ex`. No user code, and no macro, can grow
the set; every module probed reports exactly 31. The report prints a count and a
summary line, not 31 rows. A change to `builtins.ex` is a TCB change and shows up
as a changed count.

**`uncertified` is reported, but it is not an assumption.** `maybe_certify/2`
(`declarations.ex:203`) runs `Kernel.validate_certificate/2` opportunistically
and swallows failure, so `env.certified` means "passed size-change termination."
A def absent from it does not δ-unfold. That is a *completeness* limitation, not
a soundness one: type-level functions must certify or compilation fails
(`totality_closure.ex:34`), and value-level functions that fail simply never
δ-reduce, so the kernel cannot use them to inhabit a type. Empirically it is also
small — 4 of 82 defs in `Std.List`, 0 in `math`/`string`/`bool`/`option`. It gets
its own heading, *"cannot be used in proofs; not assumptions"*, and is never
conflated with the axioms.

### 4.3 Identity: key on the target, not the name

Def names in a freshly elaborated env are **bare atoms** (`:abs`, `:pi`); only
imported modules are rekeyed to `Mod#name` by `Resolution.rekey_module_env`. Names
are an unreliable identity.

An axiom's identity is **`(target MFA, elaborated type)`**. `erlang:length/1` at
`∀ {a}. List(a) -> Int` is the same assumption however the Cure wrapper is
spelled, and two wrappers of one MFA at two types are two assumptions. This
sidesteps the anonymous-instance provenance gap entirely: module attribution is a
best-effort *display* field, never part of an axiom's identity.

### 4.4 Origin tagging

The three buckets of §1 print separately. This split is the single most useful
thing the tool produces, and it is invisible today. It is also how progress is
measured: the `CURE RUNTIME` bucket going 49 → 0 *is* the thesis, and the
`CURE BRIDGE` bucket going 43 → 0 is #18 landing.

With the caveat from §4.1: until #23, those 49 sit in `UNAUDITED` rather than in
the `CURE RUNTIME` bucket, so the ledger shows the goal as a hole rather than a
count. The two numbers must be read together, and the report prints them
adjacently for that reason.

### 4.5 Target availability

Some OTP axioms do not exist on every BEAM. `:re`, `:inets`, `:httpc`,
`:persistent_term`, and `Registry` are absent on AtomVM. Today this is a
hand-maintained list in `esp32-beam/CLAUDE.md` warning readers not to "relearn
these the hard way."

The ledger already knows every axiom's target MFA, so it can compute that list.
`--target <t>` consults a capability table — a static map from target name to a
set of unavailable modules — and prints an `UNAVAILABLE ON TARGET` section.

```
$ cure audit trust Std.Time --target atomvm
UNAVAILABLE ON TARGET (1)
  re:run/3   via Std.Time.zone   — :re absent on AtomVM
```

The dependency is real: `cure_std_time.ex:137` calls `Regex.match?` inside
`zone/2`, so `Std.Time.zone` needs `:re` and is dead on AtomVM today, silently.
This is a portability wart, not a bug — on canonical BEAM it works — and deletion
is the wrong response. Non-portable modules stay in `Std`; the ledger reports
where they run.

The transcript above is aspirational, not achievable at v1: `time.cure` does not
elaborate (§4.1), so `Std.Time` reports as `UNAUDITED` and no axioms are reached.
`--target` is exercised on a fixture until #23 lands. It is specified now because
the capability table is the cheap half and the reachability is already built.

The table is data, not analysis. It is maintained by hand, and a wrong entry
produces a wrong report and nothing worse. Absent `--target`, the section is
omitted entirely.

### 4.6 Components

**`Cure.Audit.Refs` — a fail-closed walker.** `Program.global_refs/1`
(`program.ex:473–483`) ends in `defp global_refs(_leaf), do: []`. For codegen that is
benign. For a ledger it is fatal in the future tense: the day the Core grammar
grows a node, reachability silently under-reports and the ledger quietly stops
finding axioms. `Audit.Refs.refs/1` enumerates every node in `Core.Term.term?/1`
(`term.ex:57–97`, which includes the `hole` and `absurd` clauses §4.2 reports on)
explicitly and **raises** on anything else. It carries one extra
clause for the non-Core `{:extern, {m,f,a}}` sentinel that occupies a def's `body`
slot.

**`Cure.Audit.Ledger` — classification and reachability.** Reachability is *not*
`Program.reachable_def_names/2`. Its `collect_reachable/4` deliberately excludes
`builtin_op` defs ("never emitted as a function form") and type-level defs
("never emitted as a runtime function"). Both exclusions are correct for codegen
and catastrophic for a ledger: the first drops arithmetic, which is an axiom. The
ledger shares the *shape* of that walk and none of its filters.

An unresolved global is a **finding**, reported under `UNRESOLVED`.

This section previously said it was a raise, on the grounds that `Kernel.infer/2`
(`kernel.ex:151`) returns `{:error, :unknown_global}` for a dangling reference,
so the condition was unreachable on a kernel-checked env. **That was wrong**, and
building the tool proved it: `Std.Fsm` declares
`fn spawn(fsm_module: Atom) -> Pid` and sixteen siblings, where `Pid`, `Any`,
`Map`, `Tuple` and `String` are none of them a def, a family, or a constructor —
and the module elaborates. It elaborates precisely *because* a bodyless `@extern`
is a postulate: the signature is believed, never checked. All 17 of `Std.Fsm`'s
bridge axioms are typed with names that do not exist in Core.

So the ledger resolves a global against `env.defs`, then `env.families`, then
`env.ctors`, and reports what resolves to nothing. This is the single sharpest
thing the tool has found: an axiom whose type mentions a type that does not
exist. Raising would merely have made `Std.Fsm`, `Std.Actor`, `Std.Supervisor`
and `Std.Process` unauditable.

`UNRESOLVED` does not affect `--strict`, which still keys on `UNAUDITED` alone.

**`Cure.Core.Printer` — new, untrusted.** Nothing in the tree renders a
`Core.Term` to text. `Quote.reify/2` returns a term; call sites hand it to
`inspect`. Every kernel and elaborator error that mentions a type today prints a
raw Elixir tuple. The report needs readable types, so this spec adds a small
(~100 line) printer: de Bruijn indices back to names, Π-chains to arrows,
applications to spines. It is untrusted output, outside the TCB, and it
independently improves every dependent-pipeline error message. That second
benefit is why it belongs here rather than being faked.

### 4.7 Output

Deterministic: sorted, no timestamps, no absolute paths, no map-iteration order.
Determinism is load-bearing, because `cure audit trust Std.List | diff -` is the
ratchet. Every section prints even when empty, so a section going from `(0)` to
`(1)` is a diff rather than a new line appearing from nowhere.

```
$ cure audit trust Std.List

AXIOMS — OTP (1)
  erlang:length/1          ∀ {a}. List(a) -> Int

AXIOMS — CURE RUNTIME (0)

AXIOMS — CURE BRIDGE (0)

OPAQUE TYPES (0)

KERNEL BUILTINS
  31 builtin operators (Cure.Core.Builtins)

HOLES (0)

ABSURD (0)

NOT PROVEN TOTAL (4)   — cannot be used in proofs; not assumptions
  drop, last, reverse, take

UNRESOLVED (0)   — names a signature mentions that do not exist

UNAUDITED (0)
```

(Names are sorted. An earlier draft of this sample listed them in declaration
order, `reverse, last, drop, take`, which is not stable: it depends on the
reachability walk. Determinism is the whole point of the section, so the
implementation sorts and this sample follows it.)

`--format json` emits the same content with a `schema` version field, for CI.

### 4.8 Testing

Red-green, one failing test before each fix.

1. A fixture with one `@extern` yields exactly one `ffi_postulate` with the
   correct MFA and rendered type. Widen the extern's declared type; assert the
   rendered line changes.
2. **The divergence test.** A fixture using `+` yields a `builtin_op` entry, and
   `Program.reachable_def_names/2` on the same env does *not* mention it. This
   pins why the ledger owns its reachability, so nobody later "helpfully"
   deduplicates them.
3. `Audit.Refs.refs({:bogus})` raises. Then the real guard: every term Antigen's
   generator produces passes through `refs/1` without raising. Antigen already
   generates well-formed Core terms; this defends the fail-closed invariant and
   upgrades automatically as the grammar grows.
4. `opaque type` yields `opaque_family`; a genuinely-empty inductive does not
   (`opaque_family?/1` keys on the marker, not the constructor count —
   `inductive.ex:333`).
5. `Std.List` reports exactly `reverse, last, drop, take` as not-proven-total,
   under that heading, not among the axioms.
6. `Std.Time` — which does not elaborate — lands in `UNAUDITED`; `--strict` exits
   non-zero; the default exits 0.
7. A fixture postulating `@extern(:re, :run, 3)` reports it under
   `UNAVAILABLE ON TARGET` with `--target atomvm`, and omits the section without
   `--target`. A fixture postulating `@extern(:erlang, :length, 1)` never does.
8. Two runs over the same input produce byte-identical output.

## 5. Phase 1 — the shim conformance harness

The ledger counts assumptions. It does not discharge them. Phases 2 and 3
discharge them by deleting the code they point at — but that work is gated on
#23, and the shims exist in the meantime. §2 shows what "in the meantime" costs.

Phase 1 mechanically checks the `CURE RUNTIME` axioms against their
implementations, for as long as those implementations exist. It is a
**transitional safety net that shrinks as Phases 2 and 3 land**, not a permanent
fixture. When the last `:cure_std_*` module is gone, the harness goes with it.

### 5.1 The four properties

For each executed axiom, given generated well-typed arguments:

| Property | Check | Catches |
|---|---|---|
| Referential transparency | `f(args) == f(args)` | `or_add` |
| No hidden state | process dictionary unchanged; empty mailbox; no new ETS tables | `or_add` |
| Type conformance | result matches the declared return type's runtime shape | `forall_shrunk` |
| Totality | no raise, no exit, no timeout | `forall_shrunk` |

Parametricity — the `shrink` defect — is a fifth property, but it needs a function
argument `g` and two instantiations of `t`, so it applies only to axioms whose
declared type is universally quantified in a position the harness can
instantiate. Those are enumerated by hand rather than inferred.

**The harness executes 45 of the 49 axioms, not all of them.** The four `http`
axioms perform network I/O; running them in a test suite is not acceptable, and
mocking `:httpc` would test the mock. They are classified as effectful by
inspection — the classification §5.3 would have reached anyway — and excluded
from execution. Excluding them is stated in the harness's own output, so that
"45 axioms checked" never reads as "49 axioms checked".

`time.now` and `time.utc_now` *are* executed: they are effectful, and referential
transparency is precisely the property that detects it. They are expected to fail,
and the harness records an expected failure rather than a passing test, on the
convention Antigen already uses for deliberate violations.

### 5.2 Generators

Arguments are generated per shim module by hand: `ORSet`, `Instant`, `Regex` and
the rest are opaque, and nothing can infer a generator for them from the Cure
type. Six generator sets — the seven shim modules less `http`, which is not
executed.

Generators are written in **Antigen's generator descriptor language** —
`{:return, x}`, `{:member_of, xs}`, `{:one_of, gs}`, `{:frequency, ws}`,
`{:bind, g, f}`, `{:sized, f}` — and interpreted by
`Antigen.Backend.StreamData.sample_seeded/3`. Two reasons: it keeps the harness
backend-agnostic exactly as Antigen is, and it respects the architecture rule
that `StreamData` is named in one module only. Note that the rule as written
(`test/antigen/architecture_test.exs`) scopes to
`lib/antigen/{generators,assays}/**`, so it would not *catch* a leak from this
harness. Going through the backend is therefore a choice, and the rule should be
widened to cover the harness's directory.

### 5.3 The real output is a partition, not a pass/fail

Running the four properties — plus the hand-enumerated parametricity check
(§5.1) where it applies, which is what actually catches `shrink`: the four
alone would pass it, since it is deterministic, total, and shape-correct —
over 49 axioms sorts them into three sets, and that partition is what Phases 2
and 3 consume:

- **True and mechanically confirmed.** For a pure shim (§6), the axiom
  disappears outright on rewrite. For a mixed shim with a real OTP primitive
  underneath (§7), confirming the axiom true does not make the OTP dependency
  go away — it splits, per §7, rather than vanishing. Expected: most of `crdt`
  (22), `gen`'s two monomorphic shrinkers, and `json` (3) — the last of these
  is true as declared but still ends up in Phase 3 (§7), not Phase 2, because
  its marshalling wraps genuine `:erlang` calls.
- **False and repairable by changing the Cure signature.** `shrink` wants
  `interface Shrink t` rather than `∀t. t -> List(t)` — a typeclass method is
  permitted to dispatch on `t`, which is precisely what it does. `forall_shrunk`
  wants `-> Result(t, Counterexample)` rather than `-> t` and a raise. Both
  repairs are surface-level and land before any rewrite.
- **False and unrepairable without effects.** `time.now`, `time.utc_now`, and all
  four of `http`. These read the clock or the network. No signature over a pure
  Π type is true of them. They stay axioms until the inert `Effect` former lands,
  and the ledger should say so rather than let them sit indistinguishable from
  `erlang:length/1`.

That third set is the finding that justifies Phase 1 existing at all: **it tells
you which axioms cannot be discharged by the work in Phases 2 and 3**, before you
start that work.

### 5.4 Testing the harness

The harness's own red test is the history of §2: check out `0377252^`, point the
harness at `or_add`, and it must fail on both referential transparency and hidden
state. Then, against today's tree, `forall_shrunk` must fail type conformance at
`t = Int` and totality on the failing branch. A harness that does not reproduce
the defects that motivated it is not evidence of anything.

## 6. Phase 2 — retire the pure shims

**26 axioms: `crdt` (22), `gen` (3), `test` (1).**

These have no OTP primitive underneath at all. `cure_std_crdt` is `Enum`, `Map`,
and `MapSet`; `cure_std_gen` is list arithmetic; `cure_std_test` is a loop.
Written in Cure, all 26 axioms vanish outright — the functions become ordinary
definitions the kernel checks.

Two carry the signature repairs from §5.3: `shrink` becomes an interface method,
`forall_shrunk` returns a `Result`. `forall_shrunk`'s raise becomes a value, which
is the only reason it can be written in Cure at all.

**Gated on #23** (value-surface parity). None of these modules dependent-elaborate
today, and a rewrite in Cure must elaborate to be checked. Attempting Phase 2
before #23 buys nothing: the code would compile through the classic pipeline,
which is type-blind, and an axiom would be replaced by an unchecked definition.

## 7. Phase 3 — rebase the mixed shims onto OTP

**23 axioms: `time` (9), `regex` (7), `http` (4), `json` (3).**

Each of these is a real OTP primitive wrapped in a shim that also computes.
`:cure_std_regex` calls `:re` four times and spends the remaining 150 lines
marshalling results into Cure shapes. `cure_std_json` delegates to a 240-line
pure Elixir codec. The marshalling and the codec are computation, and computation
belongs in Cure.

The move is a **split**, not a deletion: let the axiom point at OTP, and pull the
computation into Cure.

| Module | Axioms now | OTP primitives underneath | Axioms after |
|---|---:|---|---:|
| `time` | 9 | `:erlang.system_time`, Elixir's `DateTime` (`from_iso8601`, `to_unix`, `to_iso8601`) | ~2 |
| `regex` | 7 | `:re.run`, `:compile`, `:replace`, `:split` | ~4 |
| `http` | 4 | `:httpc.request`, `:inets.start` | ~2 |
| `json` | 3 | `:erlang.float_to_binary`, `:iolist_to_binary` | ~2 |

The count only falls from 23 to about 10. **That is not the point.** The point is
what the surviving axioms assert. Today they assert totality and purity of 470
lines of Elixir in this repository that nothing tests. Afterwards they assert the
same of OTP, which has been load-bearing for thirty years. The `CURE RUNTIME`
bucket empties into `OTP`, and the thesis — *no axiom should point at code we
wrote* — is met.

Two residues survive and are honest about themselves. `time.now`, `time.utc_now`
(it delegates straight to `now/0`), and the four `http` axioms are effectful
(§5.3), so their post-split OTP axioms are still false as *pure* postulates.
They are correct as effectful ones, and they wait on the inert `Effect` former.
`Std.Regex` and `Std.Http` remain in `Std` and remain absent on AtomVM;
`--target` reports it (§4.5).

## 8. Out of scope: the 43 bridge axioms

`Elixir.Cure.FSM.Builtins` and its siblings are the bespoke fsm/actor/sup
machinery. All 43 axioms retire under **classic-pipeline-deletion (#18)** and the
locked typed-BEAM-process-algebra decision, which replaces them with typed Cure
libraries over a sealed `Std.Otp.Raw`. `Cure.FSM.Runtime` is 404 lines of our own
scheduler rather than an OTP wrapper, so that is a rewrite in the sense of Phase
2, not a rebase in the sense of Phase 3.

This spec plans none of it. #18 has a plan; two plans for one body of work will
drift. The ledger counts the 43 and watches them go to zero.

## 9. Sequencing

```
Phase 0 (ledger)      ── no dependencies ──────────────────► buildable now
Phase 1 (harness)     ── depends only on the shims ────────► buildable now
   │ produces the partition
   └─► signature repairs (shrink, forall_shrunk) ──────────► buildable now

Phase 2 (rewrite 26)  ── gated on #23 ─────────────────────► after parity
Phase 3 (rebase 23)   ── gated on #23; effectful residue
                          additionally gated on the Effect former
Phase — (bridges 43)  ── owned by #18
```

Phases 0 and 1 are independent of each other and of everything else. Both pay for
themselves before any rewrite happens: Phase 0 because nobody can currently count
the surface, Phase 1 because it already found three false axioms by hand and
would have found them mechanically.

They are also complementary rather than redundant, and §4.1 is why. Phase 0 sees
only what elaborates, which today excludes every module Phases 2 and 3 target.
Phase 1 sees only the BEAM functions, which is exactly those modules. Neither
alone covers the surface; together they do, and the overlap grows as #23 lands
until Phase 1 becomes unnecessary.

## 10. Known limitations

- **Ledger coverage is bounded by dependent-elaboration**, and the bound bites
  exactly where it hurts: 25/44 stdlib modules elaborate, and none of the seven
  `cure_std_*` modules do. Surfaced by `UNAUDITED`, never hidden (§4.1). Phase 1
  is the answer until #23 lands.
- **Module attribution is best-effort.** Bare-atom def names and
  `__impl_<I>_<H>_<m>` instance globals carry no module identity. Fixing that is
  the same change as the anonymous-instance provenance gap — thread the module
  through `Implementation.register/2`. The ledger does not block on it, because
  identity keys on the MFA (§4.3).
- **The harness cannot prove purity, only refute it.** Passing the four
  properties on generated arguments is evidence, not proof. It is strictly more
  than the zero evidence available today, and a rewrite in Cure is what turns
  evidence into proof.
- **A static purity lint would be cheaper for one class of defect.** `or_add`'s
  `Process.put` is visible in the source; grepping the shim modules for
  `Process.put`, `send`, `:ets`, `:rand`, and `:erlang.system_time` would have
  caught it deterministically with no generators. It cannot catch `forall_shrunk`
  or `shrink`, which are type defects rather than effect defects. Worth adding as
  a cheap first gate inside Phase 1; not worth having alone.
- **The capability table is hand-maintained.** A wrong entry yields a wrong
  portability report and nothing worse (§4.5).
- **Purity and totality of an extern remain assumed, not stated.** An `@extern`
  carries no effect annotation the kernel reads, and `! Io` is dropped (§2). The
  ledger reports the assumption; only the `Effect` former can let a signature
  state the truth.
