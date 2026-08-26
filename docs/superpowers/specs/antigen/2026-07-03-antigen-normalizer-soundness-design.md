# Antigen V1 — Normalizer Soundness (Phase 2) Design

**Status:** proceeding under the operator's roadmap resolution (V1 is Phase 2, and
open-question #2 resolved *include the intrinsic-law-only assay over the
untranslatable fragment*). Second phase of the untrusted-machinery initiative
([umbrella spec](2026-07-03-antigen-untrusted-machinery-design.md), task #66),
after V3 (elaborator soundness). Autonomous continuation via the `/loop` session —
the operator merges `autopilot/antigen-tier-b` and can course-correct before then.

## 1. Problem

`Cure.Types.Reduce` is the **untrusted** type-level normalizer the type checker
uses for definitional equality — e.g. deciding `Vector(T, 3 + 5) ≡ Vector(T, 8)`
at a call site without an SMT call. Its public surface:

- `normalize(ast, bindings) :: ast` — `do_substitute(ast, bindings)` (surface
  variable substitution) then `kernel_normalize/1`.
- `equal?(a, b, bindings) :: boolean` — `normalize(a) == normalize(b)`. **This is
  the front-door soundness consumer:** the type checker treats a `true` here as
  "these two types are definitionally equal" and accepts the program. A *false
  positive* (`equal?` returns `true` for two genuinely-unequal types) is a real
  unsoundness — it admits an ill-typed program — with no kernel backstop, exactly
  like an SMT false discharge.

The arithmetic itself is **not** the untrusted part: `kernel_normalize/1` calls
`CoreBridge.to_core(ast)` and, when it succeeds, delegates the whole reduction to
the **trusted kernel** (`Eval.eval([])` → `Quote.reify()`), reading the result
back with `CoreBridge.from_core/1`. When `to_core` returns `:error` (an
untranslatable former — named ref, refinement, n-ary tuple), it falls to
`structural_congruence/1`, which recurses into children through the kernel again.

So the untrusted surface under test is precisely: **(a) `do_substitute` (surface
substitution), (b) the `CoreBridge` translation round-trip
(`to_core`/`from_core`), and (c) `structural_congruence` (the untranslatable-
fragment fallback).** A bug in any of these can make `normalize`/`equal?` return a
wrong normal form even though the kernel's arithmetic is correct — a
translation/substitution/congruence bug, not an arithmetic bug.

## 2. The oracle and the three assay families

The trusted `Cure.Core` normalizer (`Eval.eval` / `Quote.reify` / `Conv`) is the
differential oracle for the **translatable** fragment. The **untranslatable**
fragment has no oracle, so it is pinned by intrinsic algebraic laws the module's
own contract guarantees.

**Independence, up front.** `Types.Reduce.normalize` itself calls
`CoreBridge.to_core(ast)` → `Eval.eval` → `Quote.reify` → `CoreBridge.from_core`
internally (§1). A naive "oracle" that re-derives its comparison value by calling
`to_core(ast)` on the *same* `ast` and re-running the kernel is only partly
independent: **both** routes inherit whatever `to_core` produced for that `ast`,
so a `to_core` mistranslation of the input is invisible to the comparison — it
shows up identically on both sides. And if the comparison additionally pins
`bindings` at `%{}`, it never exercises `do_substitute`'s actual substitution
logic at all, even though `do_substitute`/`Reduce.substitute` is real,
load-bearing production code: `Types.Pi` chains
`Reduce.substitute(ast, bindings) |> Reduce.normalize(bindings)` to compute a
dependent function's return type at a call site, and `Types.Dependent` calls
`Reduce.substitute` (without an immediate `normalize`, to keep verification
constraints in proposition shape for the SMT solver) when substituting a
dependent type's value parameters. What a same-`to_core`-call comparison *does*
still catch is a bug in the `from_core` ∘ `to_core` round trip — whether
translating the kernel's read-back result forward again reproduces something
Conv-equal to the kernel's own normal form of the input. That is a real
property, but narrower than "the untrusted bridge agrees with an independent
oracle," and it is silent on `to_core`'s forward translation and on
`do_substitute`.

To close both gaps, the `:translatable` generator (§3) builds each challenge as
a triple `{ast, bindings, core_expected}`: `ast` is the surface AST fed to
`Types.Reduce.normalize/2` (together with `bindings`); `core_expected` is a Core
term for the *same* expression with `bindings` already folded in, built by a
**second, hand-written surface→Core encoder that the generator owns** —
structurally mirroring `CoreBridge.to_core`'s grammar coverage, but independent
code, so a `to_core` bug that mistranslates a given surface shape does not
silently reproduce itself on the oracle side, and a `do_substitute` bug (wrong
or missing substitution) shows up as a mismatch against `core_expected` (which
never routes through `do_substitute`). This encoder is generator-owned
test-support code under `lib/antigen/generators/`, not a change to
`Cure.Types`/`Cure.Core` (§8's non-goals are unaffected).

### V1a — Differential `normalize` (translatable fragment)

**Property.** For a `{ast, bindings, core_expected}` triple from the
`:translatable` stream:

> `CoreBridge.to_core(Types.Reduce.normalize(ast, bindings))` and
> `Eval.eval(core_expected, []) |> Quote.reify()` are `Conv`-equal core terms.

Both routes normalize the same expression via two independently-built Core
encodings; V1a checks that surface substitution, the untrusted bridge round-trip,
and surface plumbing agree with the kernel's own normalization of an
independently-encoded equivalent term. An infection is a surface normal form
that translates to a core term the kernel says is *not* convertible to the
independent encoding's kernel normal form —
`{:normalize_disagrees_with_kernel, ast, …}`.

### V1b — Differential `equal?` (translatable fragment) — the soundness property

**Property (the load-bearing one).** For `{a, bindings, core_a}` and
`{b, bindings, core_b}` pairs built the same independent way as V1a:

> `Types.Reduce.equal?(a, b, bindings)` ⟺ `Conv.conv?(core_a, core_b, [], 0, nil)`
> is true — equivalently, `Conv.conv_values?` on `Eval.eval(core_a, [])` and
> `Eval.eval(core_b, [])`. (`Conv.conv?/5` takes Core **terms** and evaluates
> them internally; `Conv.conv_values?/4` takes pre-evaluated **values** — the
> two are not interchangeable inputs, so the plan picks one call consistently
> rather than "`conv?` on values.")

The **`true`-side is the soundness direction**: `equal?` returning `true` while
the kernel says *not convertible* is an unsound definitional-equality discharge →
`{:equal_unsound, a, b}` (admits an ill-typed program). The `false`-side is
*completeness* (a surface `equal?` returning `false` where the kernel says
convertible is an incompleteness/reach gap, surfaced but a weaker signal). Both
are reported, tagged distinctly; only the unsound `true` is a hard infection.

### V1c — Intrinsic laws (untranslatable fragment, no oracle)

For `ast` where `CoreBridge.to_core(ast) == :error` (so `structural_congruence`
governs), two algebraic laws pin its behavior without an oracle. Only one of
them is a literal moduledoc sentence — the other is a design-intent consequence,
and the two are tagged accordingly so the spec doesn't overclaim:

- **Monotone non-increase (moduledoc-guaranteed).** The moduledoc states
  verbatim: "The result is *always* syntactically smaller-or-equal to the
  input," so `term_size(normalize(ast, b)) <= term_size(ast)`. A congruence step
  that grows the term violates the stated contract → `{:size_increased, ast, …}`.
- **Idempotence (design-intent, not a literal moduledoc sentence).** The
  moduledoc does not state idempotence in so many words; it describes the module
  as performing "a small, terminating, syntactic reduction" that produces a
  normal form. A terminating normalizer's normal form is meant to be a fixpoint
  — `normalize(normalize(ast, b), b) == normalize(ast, b)` — and that is the law
  this check pins, but the plan should cite it as an inferred design contract,
  not a directly-quoted guarantee. A second pass that changes the term is a
  non-confluent / non-terminating congruence bug → `{:not_idempotent, ast, …}`.

These make the untranslatable fragment (which V1a/V1b cannot reach — no core
translation exists) non-vacuously covered, per the operator's open-Q2 resolution.

## 3. Generators

A new `Antigen.Generators.SurfaceExpr` producing type-level surface ASTs (the
`{tag, meta, children}` grammar `Types.Reduce` consumes), in two labelled
streams so the assay knows which family applies:

- **`:translatable`** — arithmetic/boolean/comparison expressions over integer &
  boolean literals and bound variables (with a `bindings` map), all inside the
  fragment `CoreBridge.to_core` accepts. Feeds V1a + V1b. Per §2's independence
  fix, each generated item is a `{ast, bindings, core_expected}` triple (for
  V1b, a *pair* of such triples): `core_expected` is built by the generator's
  own second surface→Core encoder (independent of `CoreBridge.to_core`), with
  `bindings` folded in directly at generation time — so both `to_core`'s forward
  translation and `do_substitute`'s substitution are actually exercised, not
  just the `from_core`∘`to_core` round trip. For V1b, pairs are generated both
  as *kernel-equal* (e.g. `3 + 5` vs `8`, must be `equal? = true`) and
  *kernel-unequal* (e.g. `3 + 5` vs `9`, must be `equal? = false`) so the
  soundness direction is exercised on real should-be-true and should-be-false
  inputs. For closed literal-arithmetic pairs (like `3 + 5` vs `8`/`9`) the label
  is knowable by plain Elixir arithmetic at generation time; for compound pairs
  (comparisons, booleans, function applications) the label is decided by feeding
  the pair's already-independent `core_a`/`core_b` encodings to the *trusted*
  kernel (`Conv`) once at generation time — still independent of `Reduce`/
  `CoreBridge` (the code under test), which is what matters, even though it is
  not independent of the kernel (the kernel is the TCB, not under test here).
- **`:untranslatable`** — expressions headed by a former `to_core` rejects
  (named type ref, refinement `{n | p}`, n-ary tuple — mirroring
  `CoreBridge`'s own moduledoc list of rejected formers; `test/cure/types/
  core_bridge_test.exs`'s `:refinement_marker` fixture is a concrete precedent
  for the shape) wrapping translatable sub-terms, so `structural_congruence`
  runs and V1c's laws are non-trivial. No `core_expected` is needed here — V1c
  has no oracle by design (§2).

The generator lives under `lib/antigen/generators/` (StreamData-permitted glob).
Wiring mirrors the existing families: an assay-id → module entry in the runner's
`assay_module/1`, and generator entries in `default_gen` (weight 1 each) so
`mix antigen` exercises V1 — unless grounding shows the surface grammar is better
run as a fixed catalog (like elab), in which case the plan reconciles to that.

## 4. Assay module

`Antigen.Assays.Normalizer`, assay ids `normalizer/differential`,
`normalizer/equal`, `normalizer/intrinsic`. Each `run/1` delegates to a `run/2`
with an injectable oracle-op map (`%{substitute, to_core, from_core, eval, reify,
conv, normalize, equal}`) — the Run C / V3 seam pattern — so a negative control
can inject a broken bridge/reducer/substituter without touching `Cure.Types.*`
or `Cure.Core.*` and without `:meck`. `substitute` (defaulting to
`&Cure.Types.Reduce.substitute/2` in `@real`) is included specifically because
§2's independence fix makes `do_substitute` a first-class part of what V1a/V1b
must be able to catch — without a `substitute` hook, a negative control cannot
demonstrate that a substitution bug (as opposed to a bridge/congruence bug)
actually trips the assay. Every kernel normalization runs under the committed
`@assay_fuel` 500_000 floor, matching the `elab`/`reflexivity` convention;
`:fuel_exhausted` is its own reported outcome. (The `:translatable` fragment
`CoreBridge` accepts has no `:case`/certified-global-unfolding path, so
`Eval.eval` over it is structurally terminating by construction — the floor is
defensive/for forward-compatibility with the assay conventions, not expected to
trip for this fragment in practice.)

## 5. Testing strategy (behavioral, immutable; strict TDD)

New `test/antigen/assays/normalizer_test.exs`:

1. **V1a baseline.** `normalize(3 + 5)` agrees with the kernel normal form of
   `3 + 5` → `:ok`.
2. **V1a negative control.** Via `run/2`, inject a `from_core` that corrupts the
   read-back (returns a wrong literal) → `{:normalize_disagrees_with_kernel, …}`.
   Proves V1a is load-bearing (non-vacuous: the comparison can fail).
3. **V1a substitution negative control.** Via `run/2`, inject a `substitute` that
   drops a binding (returns the AST with the free variable left unsubstituted)
   on a term with a non-empty `bindings` map whose `core_expected` has the
   binding folded in → `{:normalize_disagrees_with_kernel, …}`. This is the test
   that demonstrates §2's independence fix actually closes the
   `do_substitute`-blindness gap the naive same-`to_core`-call formulation had —
   without it, the fix is unverified by the test suite.
4. **V1b soundness baseline.** `equal?(3 + 5, 8) == true` and the kernel agrees →
   `:ok`; `equal?(3 + 5, 9) == false` and the kernel agrees → `:ok`.
5. **V1b negative control.** Inject a reducer stub whose `equal?` returns `true`
   for a kernel-unequal pair → `{:equal_unsound, …}`. The load-bearing proof.
6. **V1c idempotence.** An untranslatable-headed term: `normalize` is a fixpoint
   → `:ok`; a stubbed congruence that mutates on the second pass →
   `{:not_idempotent, …}`.
7. **V1c monotone size.** `normalize` output is size-≤ input → `:ok`; a stubbed
   congruence that grows the term → `{:size_increased, …}`.
8. **Determinism / regression.** `run/2` with the real op-map is byte-identical
   to `run/1`; existing `Types.Reduce` tests untouched.
9. **Runner wiring.** The three `normalizer/*` ids resolve through
   `assay_module/1`; a generated challenge flows through `explore/1`.

## 6. Invariants

- **Read-only TCB + read-only `Cure.Types`.** V1 tests the untrusted normalizer
  against the trusted kernel; neither is edited. The oracle is reached only
  through the assay's `@real` op-map.
- **Deterministic, banked, replayable.** Fixed fuel floor (500_000); no RNG/clock
  in the assay; the generator's StreamData seeds are corpus-banked like every
  other family — contingent on §7 item 6's `Challenge`/`Corpus` wiring actually
  landing, since the `{ast, bindings, core_expected}` payload shape doesn't fit
  an existing `Challenge.kind` today.
- **StreamData quarantine.** Assay under `lib/antigen/assays/` (no `StreamData`
  literal); generator under `lib/antigen/generators/` (StreamData allowed).
- **No new dependency, no `:meck`.** The `run/2` op-map is the only injection path.
- **Known-label + negative controls.** Translatable pairs carry their
  should-be-equal/unequal label; V1c terms carry `:untranslatable`. Tests
  #2/#3/#5/#6/#7 (§5) are the load-bearing negative controls.

## 7. Open items (for the plan / review to pin)

1. **`CoreBridge.to_core`/`from_core` exact signatures + the translatable grammar
   boundary** — the plan reads `lib/cure/types/core_bridge.ex` and pins which
   `{tag, meta, children}` heads translate, so the generator's `:translatable` and
   `:untranslatable` streams are provably on the right side of `to_core`.
2. **`Conv` entry for surface-derived core** — V1a/V1b compare core terms/values;
   the plan picks `Conv.conv?` (terms, evaluates internally) or `Conv.conv_values?`
   (pre-evaluated values) — not both loosely as "conv? on values" (§2) — and pins
   the `depth`/`sig` args. Since `CoreBridge` never emits `{:var, k}` or a
   certified `:global`, `depth = 0`, `env = []`, `sig = nil` are sufficient for
   this fragment; the plan confirms this rather than assuming it, mirroring V3.
3. **`term_size` for surface ASTs** — a simple node count over the
   `{tag, meta, children}` grammar (meta excluded); pin in the plan. Note the
   grammar is not uniformly list-shaped: composite nodes (`:binary_op`,
   `:unary_op`, `:tuple`, `:function_call`, …) have a list 3rd element that
   `do_substitute`/`structural_congruence` recurse into, but leaf nodes
   (`:literal`, `:variable`) have a scalar 3rd element (a number/boolean/string)
   that both functions treat as an opaque leaf — `term_size` must handle both
   shapes (recurse on list children, count 1 for a scalar-payload leaf) rather
   than assuming every node's 3rd element is a list.
4. **Generator wiring: `default_gen` vs fixed catalog** — decide from grounding
   whether `SurfaceExpr` is a StreamData generator in `default_gen` or a curated
   catalog like `elab_complete`; the plan reconciles.
5. **The independent second surface→Core encoder (§2)** — the plan designs a
   hand-written encoder, owned by the `:translatable` generator, that mirrors
   `CoreBridge.to_core`'s grammar coverage (§7 item 1 pins that grammar) but is
   independent code — not a call to `to_core` — so V1a/V1b are not circular. The
   plan pins its exact coverage (must match `to_core`'s accepted grammar 1:1, or
   V1a/V1b would spuriously reject items `to_core` accepts but the encoder
   doesn't, or vice versa) and how `bindings` are folded into `core_expected` at
   generation time. **Residual risk:** unlike `Eval`/`Quote`/`Conv` (TCB,
   trusted), this encoder is new test-support code and can itself be wrong —
   an encoder bug is a *new* false-positive source distinct from a real
   `Reduce`/`CoreBridge` bug. Keep it deliberately simple (a direct structural
   mirror of `to_core`'s cases, not a from-scratch design) and consider a small
   static smoke-corpus that checks the encoder's output against
   `CoreBridge.to_core` agreeing on ordinary inputs as a sanity check on the
   encoder itself (this does not reintroduce circularity into V1a/V1b, which
   still compare `Reduce.normalize`'s output against the encoder's independent
   output, not against `to_core`).
6. **`Challenge`/`Corpus` wiring for the new payload shape** — `Antigen.Challenge`
   is a closed `kind` union with explicit `to_pieces/1`/`from_pieces/7` clauses
   per kind, and `Corpus`'s `scaffold=` field round-trips through
   `:erlang.binary_to_term(_, [:safe])`, which refuses to mint atoms absent from
   `Challenge.@known_atoms`. §6's "deterministic, banked, replayable" invariant
   therefore requires the plan to: pick a `kind` for `SurfaceExpr` challenges
   (new, or reuse an existing one); add matching `to_pieces`/`from_pieces`
   clauses — `core_expected` is a real `Cure.Core.Term.t()` and should ride as a
   named piece (like `:typed_term`'s `type`/`term` fields), while the surface
   `ast`/`bindings`/label are not `Term.t()` and ride in the scaffold (like
   `:elab_program`'s string-keyed scaffold); and add any new tags/atoms the
   surface grammar introduces to `@known_atoms`. Without this, generated
   challenges cannot be banked/replayed even though §6 asserts they are.

## 8. Non-goals (Phase 2)

- No V2 (unifier), V4/V5/V6 — later phases.
- No `Types.Reduce` *fix*: V1 finds unsound/incorrect normalization; fixing any
  infection it banks is separate follow-up.
- No SMT (that is V6); V1 is the *pre-SMT* definitional-equality layer only.
- No new kernel/`Cure.Types` capability — read-only differential + intrinsic laws.
