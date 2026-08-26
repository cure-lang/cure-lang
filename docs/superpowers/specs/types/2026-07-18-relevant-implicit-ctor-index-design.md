# E2-residual — relevant implicit constructor indices (`{k : T}`) — design

**Date:** 2026-07-18 · **Branch:** `elaborator-gaps` · **Layer:** P + E + C, plus one
metadata field on the core ctor record (K-adjacent; the kernel *checker* ignores it).

## The gap (Idris-verified)

Idris distinguishes three multiplicities on a constructor's *implicit* binder:

```idris
data P : Type where
  MkP : {k : Nat} -> Vec k Nat -> P     -- k implicit, RELEVANT (retained, usable)
  -- vs {0 k : Nat} -> ...              -- k implicit, ERASED (dropped, unusable)
f : P -> Nat
f (MkP {k = kk} v) = kk                  -- accepts iff k is relevant
mkp0 : P
mkp0 = MkP [1]                           -- k OMITTED at construction, solved to 1
```

Cure has only two constructor-field categories, and they are welded to quantity:

| Cure category            | plicity (application/pattern) | quantity (erase/relevance) |
|--------------------------|-------------------------------|----------------------------|
| inferred index var       | implicit (solved, non-positional) | **erased (0)** — forced |
| explicit domain `(k: T)` | explicit (positional)          | **ω** — forced             |

There is **no way to spell the fourth quadrant** — implicit *and* ω. So a
constructor index that is (a) determined by the result index (redundant to pass
positionally) yet (b) needed at runtime must be written as an **explicit**
`(k: T)` field: the live workaround in `https://github.com/cure-lang/cure-otp/tree/main/metatheory/src/otp_conversation.cure`
(`CRStep : (t: Tag) -> …`, comment line 32 "carried explicitly … so the ordering
proof can name it"). Idris writes it `{t : Tag}`.

The `{0 k}` (erased) case is **not** a gap — it already maps to Cure's inferred
index var, and the `{:erased_used_relevantly}` rejection is a sound erasure gate
(oracle `nidot/ni06` is `rel=same`). Only the **relevant** implicit is missing.

## Root cause: plicity is conflated with quantity

Three sites derive "is this field positional?" from its quantity:

- `elaborator.ex:2494` — expected positional arg count = `count(q != :erased)`.
- `elaborator.ex:7115-7117` (`branch_scope`) — `:unrestricted`→consume a positional
  pattern var; `:erased`→synthesize a non-positional `$erased_…` name.
- `declarations.ex:1558-1560` — inferred ⇒ `:erased`, explicit ⇒ `:unrestricted`.

Because ω ⇒ positional and erased ⇒ non-positional are hard-wired, "implicit + ω"
is unrepresentable.

## Design: decouple plicity from quantity

Add a per-slot **plicity** to the constructor, parallel to `quantities`:

- `Inductive.ctor/…` gains `plicities :: [:implicit | :explicit]`, defaulting to
  all-`:explicit` for the arity (back-compat: existing `ctor/3,4` behavior is
  preserved by *deriving* plicity from quantity at the call in `declarations.ex`,
  see below — the record default only affects synthetic ctors that pass none).
- The kernel type-checker does **not** read `plicities` (plicity is an elaboration
  concern: how to insert args and bind patterns, not what type a ctor has). This
  keeps the change out of the soundness core even though the record lives in
  `lib/cure/core/`.

### Surface syntax

`{name : Type}` as a domain in a GADT constructor arrow chain, e.g.

```
CRStep : {t: Tag} -> SingleRecv(t, before, mid) -> ConvRecv(rest, mid, after, msgs)
         -> ConvRecv(PExpect(t, rest), before, after, MCons(t, msgs))
```

Parser distinguishes it from a refinement type `{x | P}` by the `{ ident :` lookahead
(refinements never have `ident :` after `{`). Yields `{:implicit_dom, name, inner}`.

Default quantity is **ω (relevant)** — matching Idris's default for `{k}`. (The
erased `{0 k}` form is intentionally *not* added: it already exists as the bare
inferred index. Erased-implicit surface syntax is out of scope.)

### Per-site changes

1. **Parser** (`parse_ctor_dom`) — recognise `{ ident : type }` → `{:implicit_dom,…}`.
2. **declarations.ex** (`elaborate_gadt_ctor`) — an `:implicit_dom` binder joins the
   telescope in **source position** (later domains/result reference it), is excluded
   from implicit *inference* (like a named explicit dom), gets quantity **ω** and
   plicity **:implicit**. Inferred index vars → quantity 0, plicity :implicit.
   Explicit doms / anonymous args → quantity ω, plicity :explicit.
3. **Application** (`elaborator.ex:2494` + insertion) — expected positional count and
   meta-insertion key off **plicity == :implicit**, not `quantity == :erased`. An
   omitted implicit (erased *or* relevant) is inserted as a metavariable and solved
   from the expected type / later argument types.
4. **branch_scope** — positional ⟺ plicity `:explicit`; an `:implicit` slot is
   non-positional (auto-named), bindable by name via the existing `{k = kk}`
   named-implicit pattern path. That path must bind at the slot's **actual quantity**
   (ω for a relevant implicit) rather than the hard-wired 0.
5. **erase.ex** — unchanged: it already retains ω and drops 0. A relevant implicit is
   ω ⇒ retained automatically; the runtime tuple gains the field.
6. **Coverage / motive / `get_ctor` consumers** — audit the remaining `!= :erased`
   and quantity-keyed-plicity sites; route them through a shared
   `ctor_explicit_arity/`positional helper.

## Verification plan (per cure-porting loop)

- **Oracle probe** `test/oracle/relimpl/`:
  - `relimpl01_relevant_implicit_accept` — `{k:Nat}` relevant implicit, construct with
    it omitted, pattern-bind by name, return it. `rel=same` (both accept).
  - `relimpl02_erased_implicit_reject` — the `{0 k}` / inferred-index analogue returning
    the erased index. `rel=same` (both reject) — the erasure gate stays sound.
- **Antibody** `relevant_implicit_ctor_index_antibody_test.exs`: REACH (relevant
  implicit retained + usable) + CONTROL (erased index used relevantly still rejected +
  plicity does not leak into the kernel's convertibility).
- **Workaround removal**: rewrite `https://github.com/cure-lang/cure-otp/tree/main/metatheory/src/otp_conversation.cure` `CRStep` to `{t: Tag}`
  and `conv_order` to bind `t` by named implicit; regenerate `priv/std`.
- **Gate**: full Antigen suite + full test suite (TCB-adjacent record change).

## Slices

1. Core record + parser (`{:implicit_dom,…}`), no behaviour yet — telescope/quantity
   plumbing with plicity all-`:explicit`/derived; full suite stays green.
2. declarations sets plicity/quantity for the three categories; `get_ctor` exposes
   plicities; shared positional-arity helper.
3. Application: meta-insertion + arity off plicity. Probe `relimpl01` construction side.
4. Pattern: branch_scope + named-implicit binding at actual quantity. Probe `relimpl01`
   pattern side green.
5. Oracle + antibody green; remove workaround; regenerate `priv/std`; full gate; commit.
