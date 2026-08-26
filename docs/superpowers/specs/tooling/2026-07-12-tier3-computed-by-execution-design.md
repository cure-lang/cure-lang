# Tier-3 `computed by` Execution — Architecture + Slice Decomposition

> **STATUS: DESIGN (grounding), locks the approach for the hardest region of the macro
> facility.** Recorded 2026-07-12 during the SP2 Tier-3 build, after slice 1 (parse
> `computed by`) landed. Tier-3's remaining work — actually *running* a Cure elab function
> at compile time to compute an expansion — is greenfield and touches the elaborator; this
> note decides how, so the concrete slice plans have a grounded spine. Decisions here are
> the driver's, revisable by the operator.

## 1. The problem

A `computed by <fn>` rule (parsed in slice 1 → `%{kind: :computed, elab, segments, …}`)
expands by **running the elab function** over the matched input and splicing its result.
The elab is *total Cure*, runs *staged on the host at compile time*, pure, full stdlib
available (base design §3, §5). Nothing about "run a Cure function at compile time" exists
yet. Two hard sub-questions: **(a) what value does the elab receive/return** (the quoted-AST
model), and **(b) how is it actually executed**.

## 2. Decision A — execute by ELABORATE + NORMALISE, not compile-and-load

The elab is run by: elaborate the elab reference to a Core term, apply it to the quoted
input (a Core value), and **normalise** the application with the kernel — the normal form
*is* the computed expansion.

- **Reuses the trusted normaliser** (`Cure.Core.Normalise.whnf`/full normalise — verified
  callable) instead of inventing a compile-`.beam`-and-`:code.load_binary` staging path.
  Cure-native, one mechanism, no new load/purge machinery.
- **Terminates**: elabs are size-change-certified total (§5), so normalisation of a total
  function applied to a value terminates — no fuel gymnastics needed for the engine itself.
- **TCB delta ZERO.** The normaliser is *already* TCB and is **not changed** — *calling* it
  to compute is not a `lib/cure/core/*` edit. The elab itself is untrusted Cure elaborated
  like any code; its **output** (reflected to surface AST) is re-elaborated + kernel-checked
  (K3 firewall). So the trusted base neither grows nor is bypassed.
- Rejected alternative — compile the elab to BEAM, load, call: heavier, adds a real
  side-effect (mutates the code server) at compile time, and duplicates evaluation the kernel
  already does. Only worth it if elabs needed effects/FFI the normaliser can't do — they
  don't (§5: elab functions are pure).

## 3. Decision B — a GENERIC `Syntax` value first; typed per-category records later

Design §3's *ideal* is **typed per-category derived records** ("`Syntax(Edge)` ≈ a `rec`
with one field per hole") — "derived typed ASTs, not a universal `Syntax` blob." But §3 also
says: *"A generic traversal API over any syntax value exists underneath for tooling."*

**Build that generic layer first.** A single `Std.Syntax` ADT reflecting the parser's
`{tag, meta, children}` node shape is enough to make `computed by` *work*; the typed
per-hole derived records are an **ergonomics + compile-time-safety layer on top**, deferred.
Rationale: the generic value is tractable and is the substrate the typed layer would derive
onto anyway; getting execution working end-to-end first is worth more than the typed sugar.

**Operator steer (2026-07-12) — the elab-facing API is the TYPED derived record, NOT a
generic stringly accessor.** The generic `Std.Syntax` VALUE is the substrate and stays, but
the interface an elab *author* sees must be the §3 derived record: from a rule's holes, the
facility synthesises `rec RuleSyntax { <hole>: Syntax(<Kind>), … }` (a `...` group → a
`List` of a sub-record) and threads it as the elab's parameter type, so the author writes
`a.name` / `a.messages.map(fn(m) -> m.body)` — typed record projection, **compile-checked**
(a misspelled field is a compile error, not an elab-run-time failure), self-documenting. A
typed field like `a.name : Syntax(Name)` is a typed *view* whose value is still a generic
`Syntax` node underneath — so slice 2's generic value + reflection bridge are unchanged and
un-wasted; what is explicitly rejected is shipping a generic `field("name")` accessor as the
elab API. The record derivation (type synthesised from the grammar; leans on the landed
dependent-records support) is its own slice, landing **with or immediately after** execution
so authors never touch a stringly form. (Corrects the `a.field("name")` shorthand used in the
§14.6 `actor` sketch discussions — the real spelling is `a.name`.)

`Std.Syntax` sketch (spelling deferred):

```
type Syntax =
  | Node(tag: Atom, children: List(Syntax))   # {tag, meta, [kids]}
  | Leaf(tag: Atom, value: SynLit)            # literals/vars: {tag, meta, scalar}
type SynLit = SInt(Int) | SStr(String) | SAtom(Atom) | SName(String) | ...
```

(`meta`/positions are carried opaquely or dropped — the K3 firewall re-elaborates output, so
positions in the computed expansion don't need to round-trip precisely.) A **reflection
bridge** (Elixir, in the elaborator/a support module) converts each way:
`to_syntax(parser_ast) :: Syntax_core_value` and `from_syntax(Syntax_core_value) ::
parser_ast`. These are the load-bearing new functions.

## 4. Decision C — `:computed` expands at ELABORATION time, not parse time

Tier-1/2 (`literal`/`becomes`) expand during the **parse** (two-phase parse, surface
rewrite) because they need nothing but the parser. Tier-3 needs the **elaborator + normaliser**
to run the elab — which don't exist at parse time. So:

- The parser **does** now harvest `:computed` rules (recognise their keyword at use-sites,
  match segments to bind the input) but emits a deferred node — call it
  `{:computed_use, meta, [elab_ref, bound_input_syntax]}` — **without expanding**.
- A **compile-time expansion pass** (in `lib/cure/elab/*`, after parse, before/within
  `Program.elaborate`) walks for `{:computed_use}` nodes and, for each: builds the `Syntax`
  input value → elaborates `elab_ref` → `normalise(app(elab, input))` → `from_syntax` the
  result → **splices** the surface AST in place → the normal elaboration then checks it.

This is a genuine phase distinction from Tier-1/2 and the main new surface area. It lives in
the **untrusted elaborator** (`lib/cure/elab/*`), so it is TCB-zero. (Slice 1 left `:computed`
totally inert; this reverses that — harvest + emit `{:computed_use}` — as its own step.)

## 5. Slice decomposition (remaining Tier-3)

1. **slice 1 — parse `computed by`** ✅ DONE (`ce62b17`).
2. **`Std.Syntax` generic value + reflection bridge** — the `Syntax` ADT (stdlib) +
   `to_syntax`/`from_syntax` (Elixir) with round-trip tests (`from_syntax(to_syntax(ast)) ≡
   ast` up to meta). No execution yet. *Next concrete plan.*
3. **Compile-time execution pass (the big one)** — harvest `:computed` + emit `{:computed_use}`
   at use-sites; the elaboration-time pass: elaborate elab, `normalise(app(elab, input))`,
   `from_syntax`, splice, re-elaborate. End-to-end: a `computed by` macro whose elab returns a
   constant `Syntax` expands and elaborates.
4. **`quote` / `$( )` surface** — sugar for building `Syntax` in elab bodies (§3). Deferrable:
   slice 3 can construct `Syntax` via ordinary constructors first; `quote` is ergonomics.
5. **`check … else fail C`** (§3.4) — semantic guards in elabs raising author `Diagnosis`
   points; ties Tier-3 to M1's exhaustiveness.
6. **Typed per-rule derived records** (§3 ideal, operator-steered elab API — see Decision B) —
   synthesise a `rec RuleSyntax { <hole>: Syntax(<Kind>), … }` from the rule's holes and thread
   it as the elab's parameter type, so authors write `a.name` (typed, compile-checked) not
   `field("name")`. Land WITH or immediately after slice 3 so no throwaway stringly API ships.
   Type-derivation from the grammar is the new machinery (leans on landed dependent records).

## 6. Open questions to verify before slice 3 (execution)

- **Where the expansion pass hooks** in `Program.elaborate` / `check_ast` (before declaration
  elaboration; must run on every module, recursively into nested exprs).
- **Elaborating a bare fn reference to a callable Core term** + applying it to a value — confirm
  the elaborator/normaliser compose to reduce `app(elab, syntax_value)` to a `Syntax` normal
  form (the crux; prototype it early).
- **`Syntax` as a Core value the normaliser reduces** — it must be an ordinary inductive/data
  value (so `to_syntax` yields a Core value, and the elab pattern-matches it). Confirm the
  `Syntax` ADT elaborates and that a value of it normalises.
- **Determinism / purity** — the pass must be pure + deterministic (§5); no ambient effects in
  elabs (the type system already forbids `Effect` in a total fn — confirm the elab signature
  is `Syntax -> Syntax`, not `... -> Effect(Syntax)`).
- **Recursion/fuel backstop** — a computed macro whose output contains more macro uses
  re-enters expansion; keep the design's bounded-depth fuel as a backstop beyond totality.

## 7. What this unblocks

Tier-3 execution is the gate for the container macros (`actor`/`sup`/`fsm`) sketched from
design §14.6 — those are `computed by` macros whose elab (with the reflection API, SP4, and
`lift module` + the behaviour/callback vocabulary, SP5) builds a gen_server/supervisor. So
this note's architecture is the foundation the SP5 ceiling rests on. It also stays fully
TCB-delta-zero and on the dependent pathway (post-#18 aligned).
