# Typeclasses as an Elaborator Feature — `proto`/`impl` Done Properly

**Date:** 2026-07-09
**Status:** design (operator-directed). The **fifth enabler** of the
[classic-pipeline deletion](2026-07-09-classic-pipeline-deletion-design.md);
corrects that spec's earlier miscategorization of `proto`/`impl` as macros.

**Decision (operator, 2026-07-09):** `proto`/`impl` become **real typeclasses
implemented as an elaborator feature** — dictionaries as ordinary Core records,
type-directed instance resolution in the untrusted E-layer, and dispatch resolved
to direct calls at compile time. **Not** a
macro (a macro is type-blind and can only emit runtime dispatch), and **not**
in the kernel (no dependent language puts instance resolution in its kernel).

---

## 1. Why this is the one construct that isn't a macro

fsm/actor/sup/app are effectful *code generators* — a macro (syntax→syntax,
upstream of the elaborator) fits them exactly. Typeclasses are *type-directed
elaboration*: resolving the `Stringify` instance for a value needs that value's
type and the ambient constraint context at the call site. The macro facility is
type-blind by design (that's its TCB-delta-zero property), so a macro can only
emit the version needing no type information — **runtime dispatch**, one BEAM
function per method with runtime type-guarded clauses, which is what classic
`codegen.ex:471-601` does today. That is Julia-style multiple dispatch, not a
typeclass, and it forecloses the three things that matter (§3).

Real typeclasses therefore live where every role-model language puts them —
Agda instance arguments, Idris 2 interfaces, Lean 4 classes, Coq classes: the
**core sees only dictionaries (records) and application**; **resolution is an
elaborator pass**. The kernel is untouched.

## 2. Architecture

Three layers, each mapping to prior art:

1. **Dictionaries = Core records** (Idris/Lean). A `proto` elaborates to a
   dependent record type; an `impl` elaborates to a record *value* (a
   dictionary) holding the method implementations. Cure already has dependent
   records (the `struct_ctor_sig` / GADT-ctor path), so the kernel already
   checks these terms — zero kernel delta.
2. **Resolution = E-layer instance search** (all four). A constrained call
   synthesizes the dictionary by type-directed search over a registered
   instance table. This is untrusted elaborator work, exactly like implicit
   argument resolution (which Cure already does — `resolve_deferred_slots`,
   `finish_global_app`).
3. **Static resolution.** A resolved instance becomes a **direct call to the
   concrete implementation**. The dependent pipeline does not contain a
   monomorphisation pass; dictionary elimination must therefore happen during
   elaboration or erasure, rather than relying on a later optimizer. This
   removes runtime lookup without claiming whole-program generic
   specialization.

## 3. What this buys over the macro/runtime-dispatch version

1. **Usable in dependent types.** A constraint may appear in a type, and a
   method's result type may depend on the instance — the dictionary is present
   at elaboration time, so it participates in type checking. Runtime dispatch
   is fundamentally too late. This is the reason the language exists.
2. **Zero device overhead** (§2.3) — resolved to direct calls,
   vs. a runtime shape-check on every protocol call today.
3. **Coherence and laws.** Resolution enforces one instance per type per class,
   and laws (Functor/Monad/Ord) become *statable and provable* against the
   dictionary record. Runtime dispatch has no coherence notion.

## 4. Surface (unchanged where possible)

Existing syntax stays valid:

```cure
proto Stringify(T)
  fn stringify(x: T) -> String

impl Stringify for Int
  fn stringify(x: Int) -> String = Std.String.from_int(x)

fn display(x: T) -> String = "Value: " <> stringify(x)   # T constrained by use
```

One addition to settle (ledger §8.1): **explicit constraint syntax**. Today
`display(x: T)` leaves the `Stringify(T)` requirement implicit in the body's
call to `stringify`. Real resolution wants the constraint on the signature so
it can add the dictionary parameter and resolve at each call site:

```cure
fn display(x: T) where Stringify(T) -> String = ...
```

Whether to *require* the `where` clause or *infer* it from method use in the
body (Idris infers within reason; Haskell historically required it) is a
surface decision, not a mechanism one.

## 5. Elaboration pipeline

For each construct:

- **`proto C(T)`** → a record type `Dict_C(T)` with one field per method
  (field type = the method signature with `Self`/`T` bound). Register `C` in
  the class table.
- **`impl C for τ`** → a dictionary value `dict_C_τ : Dict_C(τ)` whose fields
  are the given method bodies. Register `(C, τ) → dict_C_τ` in the instance
  table. Coherence check: reject a second instance for the same `(C, τ)`.
- **`fn f(...) where C(T)`** → add an implicit parameter `d : Dict_C(T)`; every
  in-body method call `m(a)` becomes `d.m(a)` (field projection).
- **A call `f(v)`** with `v : τ` → resolve `C(τ)`: look up `dict_C_τ`,
  synthesize and pass it as the implicit dictionary. Nested constraints
  (`C(T)` needs `D(T)`) resolve recursively.
- **Resolve** → select `dict_C_τ`, β-reduce its projections to direct calls,
  and erase the dictionary parameter when it is no longer needed.

The kernel re-checks the resulting dictionary-passing terms as ordinary
records + applications. Nothing in this pipeline is trusted beyond what already
exists.

## 6. Instance resolution details

Instance resolution is the **instance profile** of the shared type-directed
search engine — see
[`2026-07-09-type-directed-search-design.md`](2026-07-09-type-directed-search-design.md).
That engine (goal-directed search over hint databases, in the untrusted E-layer,
with results kernel-checked) is the reusable component; resolution is its
constrained, deterministic instantiation. This spec does not re-describe the
search loop; it fixes the instance-specific policy:

- **Database:** the `instances` set; a hint is a registered `dict_C_τ`.
- **Goal:** a class-headed `Dict_C(τ)`, driven by the head constructor of `τ`
  (`Stringify` for `List(τ)` matches `implementation Stringify for List(_)` and
  recurses on `τ`).
- **Determinism:** coherence (§8.2, one instance per `(class, type head)`, no
  overlap in v1) guarantees ≤1 matching instance, so resolution needs no
  backtracking — the predictability typeclass users expect. Nested constraints
  (`C(T)` needs `D(T)`) resolve recursively through the same engine.
- **Termination:** the engine's mandatory fuel bound, plus the instance-profile
  requirement of decreasing instance heads (Idris/Lean), so resolution
  terminates independently of fuel for well-formed instance sets. An
  unresolved constraint is a typed error, never a loop.
- **No solver.** Syntactic rule application, entirely distinct from the
  (dropped) SMT-refinement machinery — do not conflate the two.

## 7. Migration from runtime dispatch

The classic runtime-dispatch codegen (`codegen.ex:471-601`,
`protocol.ex`/`protocol_registry.ex`) is deleted with the rest of classic. The
surface is preserved, so existing `proto`/`impl` programs recompile unchanged;
their *dispatch* changes from runtime-guarded to compile-time-resolved.
Programs relying on genuinely *runtime* (value-directed, not
type-directed) dispatch — if any exist — need identifying; that pattern is a
different feature and would stay a runtime construct. Inventory required.

## 8. Ledger (open decisions)

1. **Constraint syntax** — require `where C(T)` vs. infer from method use (§4).
2. **Coherence / overlap / orphans** — v1 no-overlap; when to relax.
3. **Superclasses** (`proto Ord(T) requires Eq(T)`) — needed for a real Prelude;
   design the `requires` edge and its dictionary-field threading.
4. **Multi-parameter classes** / **associated types** / **functional deps** —
   defer; v1 is single-parameter.
5. **Default methods** — method with a body in the `proto`; dictionary-field
   defaulting.
6. **Dictionaries that must survive to runtime** — if elaboration cannot
   resolve a concrete implementation (for example, a genuinely dynamic type),
   determine whether Cure rejects the call or retains an explicit runtime
   dictionary.
7. **Interaction with `@derive`** — `@derive(Show, Eq, Ord)` should generate
   instances (dictionaries) through this same machinery; unifies with the
   cutover's open `derive.ex` question.

## 9. Non-goals

- No kernel changes — dictionaries are records the kernel already checks.
- No overlap/orphan machinery in v1.
- Not a macro — this is the one construct deliberately outside the macro facility.
- No SMT / solver involvement — resolution is syntactic type-directed search.
