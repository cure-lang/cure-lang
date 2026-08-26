# Language Specs — Condensed Master

**Date:** 2026-07-21

**Scope.** This document condenses the 13 design specs in
`docs/superpowers/specs/language/` covering Cure's surface syntax and language
ergonomics: name resolution and module qualification, literals (char/string/
binary), the unified tuple surface, pattern-matching tails (named implicits,
guard coverage), canonical constructor spelling, the total parsing library and
parser self-hosting program, the axiom/trust surface, and the ergonomics batch
(`|>`, `where`, inference, `do`, `beam_ops`). It preserves every locked
decision, invariant, status marker, and non-negotiable constraint; it drops
executed implementation plans, line-number anchors, and verbose examples. Layer
key throughout: **P** = parser/lexer (`lib/cure/compiler/*`), **E** = elaborator
(`lib/cure/elab/*`), **K** = kernel/TCB (`lib/cure/core/*`).

---

## 1. Names, modules, and resolution

### 1.1 Global-def collision protection (2026-07-08 — Approved)

**Gap:** `Program.merge_env/2` merged imported `defs` with last-wins
`Map.merge`; the locked Approach-B shadowing machinery (E-layer resolution over
bare atoms, collision-triggered re-keying to `"Mod#Name"`) protected families
and constructors only. Two modules both defining `helper/1` silently ran
whichever slice merged last — proof-relevant code could call the wrong lemma.

**Design (no new mechanism — extend Approach B to `defs`):**
- Colliding imported defs re-key to `"Mod#name"`; slice-internal references
  rewritten via the existing `rekey_term/2` atom map. `quantities` travels for
  free (inside the def value); **`certified` is a separate top-level Env
  MapSet and must be explicitly re-keyed** or δ-unfolding is silently dropped.
- Resolution for a bare `foo`: (1) local def wins; (2) exactly one import →
  that one; (3) ≥2 imports, no local → **ambiguity error** (new E-code,
  expected E089) listing candidates + the qualified escape hatch. Never a
  silent winner. **Both resolution sites wired:** call position
  (`elaborate_named_call`) and bare-value position (`resolve_free`).
- Qualified *calls* (`A.foo(x)`) always resolve through module identity;
  bare-value qualified refs (`A.foo`, no parens) are a pre-existing general
  dot-syntax gap — out of scope. Kernel/TCB and AtomVM tags untouched;
  non-colliding defs keep bare keys.

### 1.2 Forced disambiguation of ambiguous bare names (2026-07-10 — SPEC, not implemented)

Supersedes part of the 2026-07-04 local-type-shadowing design (R1 and its
"qualifying defs" non-goal). **Decision:** generalize "import-vs-import ⇒
error" to local-vs-import, making the rule uniform: *a bare name with ≥2
distinct in-scope meanings must be qualified.* No implicit "local wins"
precedence survives Phase 2. Cure adopts design (A) syntactic-ambiguity ⇒
qualify (Haskell/Rust); type-directed disambiguation (Agda/Idris/Lean) is
locked out (bidirectional non-backtracking elaborator), and qualification is
forward-compatible with it if ever added.

**Requirements R8–R14:**
- R8: ambiguity computed per namespace (family / ctor / def / interface) and
  per name; same-entity-reached-twice (re-export, dup `use`) is not ambiguity.
- R9: **`Self.N`** resolves only to the current module's own declaration
  (module's own name accepted as equivalent spelling); never falls back to
  imports. `Self` is contextual, not reserved; future clash with
  `Self`-as-implementing-type in interfaces is recorded.
- R10: lazy diagnosis — declaring a collision is legal; only *bare use* fires.
- R11: lexical binders (params, `let`, pattern vars) shadow silently — the
  load-bearing scope limit.
- R12: staged rollout — Phase 1 warning **W089** (resolution unchanged),
  Phase 2 error under `--strict` then default.
- R13: `cure migrate` mechanically rewrites bare ambiguous names to the
  qualified form they already resolve to (semantics-preserving by
  construction — the property licensing Phase 2).
- R14: no runtime/TCB/codegen change; ctor tags stay bare (AtomVM invariant).

**P0 prerequisites (two real bugs, must land first):**
- **P0.1 — unchecked qualifier:** `resolve_qualified` falls back to the bare
  atom without verifying the prefix owns the name, so `Bogus.Z` resolves to
  `Std.Nat.Z` silently. Fix: gate the fallback on ownership
  (`{:qualifier_not_owner, …}` / `:no_such_local_name`).
- **P0.2 — ctor collisions never detected:** collision classification scans
  only families and defs; a module whose sole collision is a *constructor*
  name is never re-keyed, the local ctor clobbers the import's `env.ctors`
  entry, and (via P0.1) `Nat.S` silently resolves to the **wrong** ctor. Fix:
  classify a third namespace (`ctor_owners`), extend `ambiguous_modules/2` to
  `ctors`. Fix P0.2 before P0.1. Also fixes the import-vs-import ctor variant.

**Open:** auto-prelude noise (measure W089 count before Phase 2 — the single
gating fact; `hiding`/`no_prelude` must ship first if noisy), `hiding` syntax,
record field accessors as a namespace, `--strict` per-rule graduation.

### 1.3 `@group` decorator placement (2026-07-10 — Approved)

`@group(:core)` moves from first-statement-inside-`mod` to **above the `mod`
declaration** (a decorator annotates what follows; it annotates the module).
Parser attaches a pre-`mod` `@group` to the module container meta; **any other
placement is a hard parse error** — no back-compat path, migration of all 13
std files atomic with the parser change. Both consumers survive: the
position-agnostic `@group_regex` source scan (no change) and the classic
codegen `-group([:g])` BEAM attribute (now read from container meta). Classic
codegen touch is legitimate (grouping is a Preload/runtime concern, not
dependent-kernel).

---

## 2. Literals and the primitive value surface

### 2.1 Char & String (2026-07-09 design; Char representation superseded 2026-07-10)

**Locked (operator "Option A", deliberate divergence from Agda/Idris):**
`String` **is** `List(Char)` — a type alias, not a primitive — represented at
runtime as an Erlang **charlist** `[97,98,99]`. Recorded so review does not
"correct" it back to a packed primitive; the `to_binary`/`from_binary`
`@extern` bridge (`unicode:characters_to_binary/characters_to_list`, native
AtomVM NIFs) preserves a later packed-representation migration behind the
unchanged type.

**Char representation — supersession:** the 2026-07-09 spec shipped `Char` as a
bespoke kernel primitive (`{:char_type}`/`{:char_lit}`, option (b)), having
measured `Bounded(0x110000)` as blocked by the unary-Nat index tower (~370 MB
for the type index alone). The compact-Bounded workstream (option (a)) then
landed: **the final design is `Char = Bounded(0x110000)` with the compact
`{:bounded_lit, k}` value model (commit 425f0bb)** — `{:bounded_lit,k} :
Bounded(k+1)` minimal, checks against `Bounded(n)` iff `0 ≤ k < n`, erases to
the native integer. The 07-10 char-literal spec is authoritative for literals.

Still-standing decisions from the 07-09 spec:
- **Rejected:** `Char = Int` nominal-only (loses the type distinction).
  Deferred: grapheme clusters (AtomVM has no segmentation; would be a derived
  pure-Cure library) and surrogate-excluding refined `Char` (validity is a
  boundary invariant — the UTF-8 encoder rejects invalid codepoints at
  `to_binary`).
- String literals elaborate through the **one** generic list path
  (`desugar_list`) as a cons spine of char literals — no bespoke string path;
  emit is a genuine charlist. Interpolation desugars to `++` of parts,
  restricted to `String` parts (general `Show` rendering deferred to #21).
- **`Binary`** enters the dependent pipeline as a plain zero-constructor
  inductive `type Binary = |` in std (precedent: `Std.Decision.Empty`) —
  opaque, boundary-only, never `@builtin`, zero kernel change. Must live in a
  module with a dependent trigger or it routes to the classic pipeline.
- `Atom` was out of scope for this wave (later landed separately as an
  Int-tier primitive per the locked atom-primitive decision).
- **Known pre-existing miscompile (filed, not fixed here):** the pattern-matrix
  compiler silently drops literal-valued elements inside multi-element
  ctor/list patterns (`[1,2] -> …` with a catch-all becomes unreachable). Do
  not add string-literal patterns until fixed; only structural `[]`/`c :: cs`
  patterns are supported.

### 2.2 Char literal expressions (2026-07-10 — approved)

A char literal `'a'`/`'😀'` is **sugar for a bounded literal at the full
Unicode bound**: `{:bounded_lit, cp}` typed `Bounded(0x110000)`. No new kernel
type; `Char` is a `typealias` for `Bounded(1114112)` (stdlib canonical alias a
separate item). Key points:
- Infer-mode clause assigns `Bounded(0x110000)` via the registered `:bounded`
  builtin family (`{:char_literal_needs_bounded, _}` if absent); kernel `infer`
  returns the minimal `Bounded(cp+1)` — not a contradiction, downstream use
  validates via `check` (elaborator free to assign any type the kernel checks).
- `'a' : Bounded(n)` for any `n > cp` is deliberate, mirroring integer
  literals (char-ness is syntactic).
- **Range guard `0 ≤ cp ≤ 0x10FFFF` is required at every literal locus, not
  stylistic:** a negative `{:bounded_lit, k}` reaching the kernel raises an
  uncaught `FunctionClauseError` (kernel `infer` has no catch-all).
- **Lexer prerequisite (blocking):** `lex_char` read raw bytes, so any
  non-ASCII char literal failed as `:unterminated_char`; fix decodes full
  UTF-8 sequences in both the non-escape branch and the unrecognized-escape
  fallback. No `\u{...}` escape (out of scope).
- Char literal *patterns* were a separate wave item (the earlier spec's
  `try_literal_match`/`primitive_scrut_kind`/`literal_chain` additions —
  a distinct code path from expressions, easy to implement-and-forget).

---

## 3. Unified tuple (2026-07-09 — design; representability-probed)

Replaces `Std.Pair`'s honestly-untyped façade (`element(index, tuple) -> T`
with free-variable `T`). One surface `Tuple` over the **native flat BEAM
tuple** — a deliberate fork from Idris/Agda right-nested pairs, because
nesting would surrender O(1) `element/i` on the ESP32/AtomVM target for zero
type-theoretic gain.

**Locked decisions:**
- **One value syntax `%[…]` for every arity, dependent or not**; `.1 … .n`
  project; type syntax `Tuple(…)` is a telescope with optional per-position
  binders (`Tuple(m: Nat, Vector(Int, m))`).
- **Bidirectional mode disambiguation:** synthesis ⇒ always non-dependent
  (never forced dependent); checking against a dependent `Tuple(…)` ⇒
  dependent (substitute earlier values into later expected types). The one
  caveat (same as Idris): a bare `let p = %[n, vec]` is non-dependent —
  annotate to get dependency.
- **Surface `Sigma` retired to internal:** `Sigma` is the length-2 telescope
  instance; `@builtin(:sigma)` machinery remains the internal checking target.
  No subtyping introduced. Deprecation via the migration facility (warn-now,
  error-later).
- **Flat representation always; the telescope is a typing scaffold.** Checking
  unfolds `Tuple(shape)` to right-nested binary Sigma for the kernel; emit is
  one flat tuple. **Zero new TCB** — the kernel only ever checks binary Sigma.
- **`Tele` index with distinct `Ext` (non-dependent) / `Dep` (dependent)
  constructors** makes non-dependence a structural, decidable fact; `{0}`-
  erased, never a runtime value. API gating: fixed-arity ops (`swap`) bake an
  all-`Ext` skeleton; arity-generic ops take an erased `NonDep(shape)`
  witness, uninhabited at `Dep` (decidable walk, not proof search).
  **Dead-end recorded:** do NOT gate via `Tuple(embed(ts))` — `embed(?ts)` is
  a stuck neutral, strands the metavar.
- Projection/`match`/`get(i)` need no witness (total on every shape). Fork
  §3.6 (one type vs two-type Idris fallback): one type chosen; not reopened.
- Build items: n-ary flat `%[…]` elaboration; `Tuple(…)` type parsing; flat
  emit; `.3+` and chained projections (`x.2.1`); function-typed ctor fields
  (for `Tele.Dep`) incl. positivity. Deferred: `IndepAt(shape,i)` gating,
  homogeneous-collapse ops, anonymous positional dependent records.

---

## 4. Pattern matching tails

### 4.1 Dot-syntax / named-implicit tail (2026-07-08 — Approved; closes ledger row #5)

Three E-layer-only fixes to the landed `{k = .e}` forced-dot / named-implicit
machinery (kernel untouched):
- **C-a:** the carried-eq branch path skipped `check_named_implicits` — a
  wrong dot was silently accepted where Idris rejects. Fix: thread pattern +
  verdict substitution into `elaborate_carried_eq_branch`.
- **C-b:** substituting a raw surface pattern carrying `{:named_implicit_pat}`
  into expression position (two independent sites: `refine_scrutinee_in_body`
  AND `desugar_as_patterns` for `p @ MkP({k = kk}, v)`) spuriously rejected
  programs Idris accepts. Fix: strip annotation args to positional-only form
  before body substitution; the annotation is still checked on its own path.
- **C-c:** unforced named implicit `{k = kk}` with a bare-variable inner is
  **bound at quantity 0** (Idris binds; Cure's blanket reject was a genuine
  cure-stricter divergence with no soundness rationale). Dot/non-variable
  inner on an unforced slot keeps the error (nothing pinned to check).
  **Required companion:** `Relevance.check`'s `:case` clause must fold the
  matched ctor's own quantities into the tracked erased set per branch, or
  naming the erased slot reopens the M8.3-class silent-drop hole one level
  down. Still E-layer.
- Out of scope: first-class matching on erased positions; nested
  named-implicit patterns beyond current support.

### 4.2 Z3 guard-coverage lint + `bool_elim` retirement (guard-lint spec — approved)

The "match-embedded guards on inductive-Bool `:case`" roadmap item was mostly
already landed (variable/ctor/nested guard subsets, all lowering through
`bool_case` over registry Bool; `bool_elim` eliminator retired in `9fb19ad`).
The remainder, this spec:
- **Z3 untrusted guard-coverage lint** (E-layer, zero `lib/cure/core/`
  changes): where a guarded match group would reject `:non_exhaustive`, if Z3
  **proves** the guards cover (e.g. `x<y | x==y | x>y` trichotomy over machine
  Ints), the match is accepted — the final guarded arm becomes the direct
  fall-through, its provably-true test elided; the emitted term is exactly
  what an unguarded catch-all would have produced, kernel-checked as always.
  Any Z3 failure (refuted/unknown/timeout/untranslatable/binary absent) leaves
  behavior byte-identical. Independently, a guard implied by the disjunction
  of its predecessors gets a `{:guard_shadowed, i}` **warning** (process-dict
  accumulator in `lib/cure/elab/`, never an `Env` field).
- **K13 rule (normative):** untranslatable ⇒ not proven. The translator covers
  only linear Int arithmetic/comparisons and Bool ctors; anything else makes
  the query untranslatable. Structurally identical untranslatable guards may
  share one fresh uninterpreted constant (catches literal repetition) —
  distinct ones never unify.
- **Site scoping (K13-forced):** recovery lives at the `guard_chain` site only
  (guards elaborated with typing there); the two constructor-group
  desugar-time sites stay conservative byte-identical (untyped surface guards
  ⇒ every query untranslatable ⇒ recovery would be dead code).
- **Trust boundary (locked, reconfirmed):** Z3 is OUT of the TCB — a wrong Z3
  proof yields at worst a semantic deviation confined to programs previously
  rejected; no type-unsoundness, no kernel judgement influenced.
- **Deliberate Idris divergence, documented not oracle-probed:** Idris rejects
  the trichotomy-without-catch-all; post-lint Cure accepts. No oracle fixtures
  for lint-accepts (would poison the oracle contract's signal).
- Stale `bool_elim` vocabulary retired (comments/docs only; the test-pinned
  Antigen identifiers `diverging_bool_elim_branch`/
  `terminating_bool_elim_branch` are kept forever). Non-goals: SMTCoq proof
  reconstruction, counterexample-enriched errors, CLI warning presentation.
  Task #15 (prim→delta-globals) must update the lint's `{:prim,…}` recognizer.

---

## 5. Canonical constructor spelling batch (2026-07-09 — approved, TCB-gated; task #22)

Two below-the-judgement spelling fixes, resolving the ctor-spelling value
dichotomy (spine vs fields-only). TCB blanket approval applies (both align
with Agda: params dropped at elimination; normalization preserves
well-typedness).

- **Part A — fields-only constructor values are canonical.** The kernel was
  already fields-only at every load-bearing site; the only params-on-spine
  producer is the K6 ctor term form (kept, Lean-aligned). Fixes: (A1) ι-rule
  coercion — when a spine carries more args than the branch arity, bind only
  the last `arity` args (params precede fields); (A2) conversion tolerates
  mixed spellings by coercing each side to its last-F elements in the
  **:vctor callers** (signature threaded through the `same_*_no_delta?`
  family; never coerce the `:vdata` path — family params/indices are Part B's
  concern). Mixed spelling could only false-reject before, never false-accept
  (shared-type conversion invariant); A2 only adds acceptances.
- **Part B — signature-aware nf readback** (`nf_ill_typed` class): `Normalise`
  had four signature-less reify sites (incl. the public `quote/3` and the
  binder-body `quote_nf`) collapsing indexed families' param/index split so
  `nf` output failed re-inference. All four now reify with the context's
  signature; the Antigen equality-generator's deliberately-flat claimed types
  flipped to split shape in the same commit.
- Discipline: tests immutable except an enumerated flip ledger (tests pinning
  the flat readback of indexed families); any accept→reject change, oracle
  replay flip, or out-of-ledger test edit = STOP.

---

## 6. Parsing: library and self-hosting

### 6.1 `Std.Parse` / `Std.Lex` total parsing library (2026-07-09 — design; substrate partially landed; parked for 0.35)

Faithful port of idris2-parser (Höck). A dependently-typed library of
provably-total lexers/parsers — not a macro; the expressive substrate the
`parse` grammar macro lowers onto (revising that macro's "no public combinator
library" non-goal: `parse` is the declarative PEG skin, `Std.Parse` the
strictly more powerful layer beneath — a capability ladder, not two ways).

**Core mechanism:** track in the type whether a parser consumed input, and
recurse only under a proof that it did.
- `Consumed(strict, rem, orig)` — erased (`{0}`) suffix proof; at runtime the
  count of dropped elements (transitivity = integer addition; **no proof term
  on device**).
- Strictness bit forms a Bool algebra: sequence = `||`, ordered choice = `&&`,
  `some` = true, `many` = false. `many`/`some` over a possibly-empty parser is
  a **type error** (reproduces `parse`'s bespoke check as ordinary typing).
- `Step(strict, …)` — the suffix-carrying intermediate (deliberately not named
  `Result`; `run` returns ordinary `Result`).
- **Totality by well-founded accessibility (`Acc`) on the strict-suffix
  relation, not the size-change checker** — this is the crux: bodies may do
  arbitrary computation including monadic bind on parsed values
  (length-prefixed frames, tag dispatch — what PEG/`parse` cannot express) and
  remain total. No fuel, no runtime step budget.
- **Input split (approved):** char/lexer phase over the native binary via
  zero-copy sub-binaries and `/utf8` matching (ASCII-only char classes v1);
  parser phase over `List(Bounded(token))`. Two concrete instantiations, not
  one `interface Input` (typeclasses in-flight; unification ledgered).
- Lexers are reified data (`Recognise` algebra + `TokenMap`); parsers are
  direct functions (`Grammar`) — the reference's deliberate asymmetry.
- Errors: `Bounds` spans, structured `ParseError`/`InnerError`,
  farthest-failure; single error surface shared with the `parse` macro.
- Must-verify on AtomVM (sub-binaries, `/utf8`) before relying on it.
- **Implementation status (2026-07-17):** `Consumed`, strict drop, refl/trans,
  `Step`, `Acc` landed in `Std.Data.Suffix` (fixing a general family-
  application inference bug and unifying dependent-arrow parsing along the
  way). Next slice: honest `weaken`/`weakens` — currently blocked on a general
  dependent-match motive `:branch_type` rejection; **must not be replaced by
  an unchecked cast**.
- Ledgered separately: representation-selection optimization,
  `interface Input`, streaming input, the `Manual` perf layer. Non-goals: no
  regex (dead-end on AtomVM), no JSON/CBOR schema work (that is `codec`).

### 6.2 Cure-native parser, diagnostics, self-hosting (2026-07-17 — PARTIALLY UNPARKED)

Target Cure 0.35; the shared structured-diagnostic foundation moved into 0.34
under `2026-07-20-structured-compiler-diagnostics-design.md`; parser
self-hosting/bootstrap/cutover remain parked.

- **Locked dependency direction:** `Compiler.Diagnostic` ← `Std.Parse.Error`
  ← `Std.Parse`/`Std.Lex` ← `parse` macro & hand-written parsers ← Cure source
  lexer/parser. The compiler parser becomes a client of public libraries — no
  privileged compiler-only parser, no permanent "fast compiler parser" fork.
- **Diagnostic model:** stable code, severity, primary/secondary labelled
  spans, notes, suggestions, provenance, payload. Rendering separate from
  construction; human and machine renderers consume the same value; invented
  source locations forbidden; **diagnostic metadata must never participate in
  conversion/normalization or any accept-path soundness decision**.
- **Distinction (must survive into completion claims):** syntax diagnostics ≠
  type diagnostics; "parser self-hosted" must never be reported as
  "typed-hole development complete." Typed-hole candidates are untrusted
  search — every proposed term passes the ordinary elaborator + kernel.
- Migration is semantic-preservation: old/new pipelines must agree on token
  boundaries, verdicts, canonical AST, spans (differential + mutation gates);
  bootstrap via a checked-in compiler-generated parser artifact (derived
  output, never a second handwritten parser) with a reproducibility gate; the
  Elixir parser is temporary stage-0 with a deletion gate. Phases A–G; 11
  verification gates (verdict/AST parity, progress-safety, erasure,
  performance, bootstrap reproducibility, no-semantic-fork).

---

## 7. Ergonomics batch: `|>`, `where`, inference, `do`, `beam_ops` (2026-07-19 — DRAFT / approved-for-implementation)

All P + E + stdlib; **no K changes** — `Effect` itself unchanged. Recommended
order: inference → `do` → `|>` → `where` → `beam_ops` surface.

**§0 Effect model (verified invariants, govern `do`):**
- `Effect(T)` is a distinct type, congruence-only conversion — no
  `Effect(T) ≡ T`. Elimination is `let`-as-bind only; matching directly on an
  effect scrutinee is rejected. Only transparency: checking-mode auto-`pure`
  under an `Effect(R)` goal.
- `run` is an ordinary function at the language level. `Effect` erases and
  shares its runtime representation with `T`, so `run` adds no runtime wrapper;
  genuinely unsafe operations remain marked on their own declarations.
- Functional-core/effectful-shell corollary: reply *logic* stays pure
  (`handle : (r: Req) -> ReplyOf(r)` is pure/total); the effect wraps only
  `call`/`reply`/`receive`.

**§1 Leading `|>`:** lexer continuation-line detection — at a newline, if the
next non-blank line starts with `|>`, suppress the newline/indent/dedent so
the chain is one logical line (mechanism reserved for `.`-chains too); only
when a left operand precedes. Parser-only alternative rejected (indent-stack
risk).

**§2 `where` clauses:** post-body block of `fn` and `name = expr` bindings,
mutually recursive, scoped to the fn. Values → `let` chain (no value
self-reference initially); **functions → lambda-lifted to fresh private
top-level defs, NOT let-bound lambdas** — load-bearing: A6 freezing keeps the
decision-as-argument proof idiom working only when the helper is a global
application. Captured params become extra leading parameters; call sites
rewritten; gensym-namespaced, non-exported. Kernel never sees `where`.

**§3 let/where binding inference:** `let s = new_subject()` (return-only
implicit) currently fails `:let_needs_annotation`. Fix: postpone return-only
unsolved metavars past the `let`, solve from the body's constraints, require
all solved by the definition boundary (genuinely-ambiguous bindings still
rejected, now with a source-located "annotate it" message). Guard: never
postpone metavars relevant to erasure/coverage decisions at the binding.

**§4 `do`-notation — a STDLIB MACRO over a `Monad` interface
(`pure`/`and_then`), not a parser feature** (supersedes the earlier P-layer
framing). `pat <- e` → `and_then(e, fn(pat) -> rest)`; bare non-final `e` →
discard-bind; `let` stays pure; final expression auto-`pure`-lifts. One macro
covers `Effect`/`Option`/`Result`/`List`/`Parse`; `Effect`'s instance is the
existing `let`-as-bind; `do` never peels an effect scrutinee. P change: only
the `<-` token. **The real risk is span-stamping** — every generated node must
carry its statement's source span. Follow-on: Idris-style `!e` inline bind.

**§5 `beam_ops` evolution — subtractive:** retire the per-verb alias rules
(`call`/`cast`/… become plain functions inside `do`; deprecation window); keep
only a slim reserved-word bridge (`send`/`spawn`/`self`); add the one genuinely
macro-shaped piece — a typed `receive within … / timeout` block desugaring to
Selector build + `selector_receive` + `match`, built programmatically (avoids
the `becomes`-template walls), spans stamped per arm.

---

## 8. Axiom surface (2026-07-10 — Phases 0–1 landed on `autopilot/axiom-surface`, unmerged; Phases 2–3 designed)

**Thesis: no axiom should point at code we wrote.** Supersedes the same-day
trust-ledger design (now Phase 0). A bodyless `@extern` is a typed FFI
postulate — believed, never checked. Baseline: 156 externs; **92 (59%) point
at cure-lang's own Elixir**, not OTP (buckets: OTP 64 / CURE RUNTIME 49 /
CURE BRIDGE 43).

**Four axioms proven false by hand-audit:** `Std.CRDT.or_add` was impure
(process-dict tag counter; fixed `0377252` — tag is now a parameter);
`Std.Test.forall_shrunk` inhabits neither its type nor totality (returns `:ok`
at `t=Int`, raises on failure); `Std.Gen.shrink` violates parametricity
(dispatches on runtime representation under `∀t. t -> List(t)` — unsound with
erasure for any parametricity-based optimisation); `Std.Http` postulates
purity for network I/O. Also structural: surface `! Io` effect annotations are
dropped by the dependent pathway.

- **Phase 0 — the ledger** (`cure audit trust <Module>`): reads the elaborated
  `Core.Env`, not source (a source scan would silently under-report once
  macros emit externs — the one failure a trust ledger cannot survive). Only
  what dependent-elaborates is auditable (25/44 std modules at design time;
  the seven `cure_std_*` shims land in `UNAUDITED`). Trust classes:
  `ffi_postulate`, `builtin_op` (fixed baseline 31, only `builtins.ex` can
  grow it), `opaque_family`, `hole`, `absurd`; `uncertified` reported
  separately ("cannot be used in proofs; not assumptions"). Axiom identity =
  **(target MFA, elaborated type)**, never the wrapper name. `--target atomvm`
  flags axioms over modules absent on AtomVM (hand-maintained capability
  table). Output deterministic (sorted, no timestamps) — `diff` is the
  ratchet; never wired into `cure build`. `UNRESOLVED` is a finding, not a
  raise — `Std.Fsm`'s 17 bridge axioms are typed with names (`Pid`, `Any`, …)
  that don't exist in Core and elaborate anyway, precisely because postulates
  are believed. Adds the untrusted `Cure.Core.Printer` and a fail-closed
  `Audit.Refs` walker (raises on unknown Core nodes).
- **Phase 1 — shim conformance harness:** mechanically checks the CURE RUNTIME
  axioms against their implementations (referential transparency, no hidden
  state, type conformance, totality; parametricity hand-enumerated — what
  actually catches `shrink`). Executes 45/49 (`http` excluded). Output is a
  **partition**: true-and-confirmed / false-but-repairable-by-signature
  (`shrink` → `interface Shrink`, `forall_shrunk` → `Result`) /
  false-and-unrepairable-without-effects (`time.now`, `http` — wait on the
  inert `Effect` former). Transitional: dies with the shims. (Later retired
  `Std.Gen.shrink` to an interface → 155 externs.)
- **Phase 2 (gated on #23):** rewrite the 26 pure shims (`crdt`/`gen`/`test`)
  in Cure — axioms vanish outright. **Phase 3 (gated on #23; effectful residue
  on the Effect former):** split the mixed shims (`time`/`regex`/`http`/
  `json`) — axiom points at OTP, computation moves into Cure; count only falls
  23→~10, but survivors assert OTP, not our own untested Elixir.
- **Out of scope:** the 43 bridge axioms — owned by classic-pipeline-deletion
  (#18) and the locked typed-BEAM-process-algebra decision. Non-goals: no
  lockfile, no `because:` field, no effect system here, nothing enters the TCB.

---

## Source specs

- `2026-07-08-dotsyntax-tail-design.md` — three E-layer fixes (C-a/C-b/C-c) closing the named-implicit/dot-pattern caveats on ledger row #5, incl. quantity-0 binding of unforced named implicits and the required `Relevance.check` extension.
- `2026-07-08-global-def-collision-design.md` — extends the locked Approach-B re-keying to the `defs` namespace; two-site ambiguity errors; certified-set re-keying trap.
- `2026-07-08-guard-coverage-lint-design.md` — Z3 untrusted guard-exhaustiveness recovery + shadowed-guard warnings at the `guard_chain` site (K13 rule, Z3-out-of-TCB); `bool_elim` vocabulary retirement.
- `2026-07-09-canonical-spelling-design.md` — TCB batch: fields-only ctor values canonical (ι coercion + conversion completeness) and signature-aware `Normalise` readback for indexed families.
- `2026-07-09-string-char-value-surface-design.md` — locked String = List(Char) charlist (operator Option A), the Binary opaque boundary type, string-literal elaboration via the generic list path; its bespoke Char primitive was superseded by the Bounded representation.
- `2026-07-09-total-parsing-library-design.md` — `Std.Parse`/`Std.Lex`: erased strict-consumption index, Bool strictness algebra, `Acc`-based totality, binary/list input split; substrate partially landed, parked for 0.35.
- `2026-07-09-unified-tuple-design.md` — one `%[…]` tuple surface over the flat BEAM tuple; `Tele`/`NonDep` structural gating; nested-Sigma checking scaffold, zero new TCB.
- `2026-07-10-ambiguous-name-disambiguation-design.md` — uniform bare-name ambiguity rule (R8–R14), `Self.` qualifier, W089 staged rollout, and the two P0 resolution bugs (unchecked qualifier; undetected ctor collisions).
- `2026-07-10-axiom-surface-design.md` — the trust ledger (`cure audit trust`), the shim conformance harness, the four false axioms, and the phased plan to empty the CURE RUNTIME bucket.
- `2026-07-10-char-literal-expressions-design.md` — char literals as `{:bounded_lit, cp}` at `Bounded(0x110000)`; range-guard crash hazard; lexer UTF-8 decoding prerequisite.
- `2026-07-10-group-decorator-placement-design.md` — `@group` moves above `mod` with a hard-error cutover; both group consumers preserved.
- `2026-07-17-cure-native-parser-diagnostics-self-hosting-design.md` — 0.35 program: public parsing platform, shared structured diagnostics, parser self-hosting with bootstrap artifact; diagnostics foundation unparked into 0.34.
- `2026-07-19-ergonomics-batch-spec.md` — the Effect-model invariants (`pure` in, no safe `run` out) plus leading `|>`, `where` lambda-lifting, let-binding metavar postponement, `do` as a stdlib `Monad` macro, and the subtractive `beam_ops` evolution with a typed `receive`/`select` block.
