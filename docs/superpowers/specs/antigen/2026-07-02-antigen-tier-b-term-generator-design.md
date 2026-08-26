# Antigen Tier B — the dependent term generator + differential assays

**Status:** design spec (parity ledger #22 / expansion A8 — "the capability
jump"). Successor to
[`2026-07-01-antigen-tier-a-design.md`](2026-07-01-antigen-tier-a-design.md);
realizes the "Tier B" half deferred there. Supersedes nothing — Tier A's
harness, stores, and verticals are unchanged and this engine plugs into them.

**Goal:** a general well-typed **dependent Core term generator**
`gen_term(Γ, T)` plus the first three **differential self-consistency assays**
it unlocks (`infer_check_agreement`, `subject_reduction`,
`normalization_stability`), with the health gate that makes a green run
credible. This turns Antigen from "these specific holes stay closed" into
"the kernel is self-consistent over a generated space" — the ledger's own
highest-leverage remaining item.

## 1. Scope

**In scope**

- `gen_term(Γ, T)`: generate well-typed Core terms at a goal type, by
  inverting the kernel's bidirectional rules (mode-directed), with INDIR
  head-first saturated elimination and a retained plain-application rule.
- A context generator (telescopes Γ) and a fixed, versioned **signature menu**
  (families + certified defs) both draw from.
- A new Challenge kind `:typed_term` with C2 serialization, coverage keying,
  and seed banking — generator-independent, like every existing kind.
- Three differential assays fed by `:typed_term`, wired into the Runner
  registry, `mix antigen`, and the static replayer.
- Health-gate extension: **binder-usage** and **reduction-activity** metrics
  joining the existing discard-rate/coverage summary, with committed floors.

**Explicitly deferred (follow-up spec, once yield is proven)**

- `conversion_termination` as a term-*pair* assay (the reflexivity vertical
  already probes halting with fuel; the pair variant adds little until the
  generator's reach is measured).
- `erasure_preservation` (crosses into the C layer — erased-arg typing and
  runtime-value comparison; heaviest of the five).
- The `Backend.ChoiceSeq` (Hypothesis-style) backend; StreamData's integrated
  shrinking suffices for the starting fragment.
- Ill-typed **mutation** corpus (mutate banked well-typed terms, assert
  rejection) — natural follow-up, not needed for the differential trio.
- The LLM proposal-generator backend (expert-iteration flywheel) — on file as
  a benchmark candidate; architecturally free later because both corpora are
  generator-independent.

## 2. Inherited locked decisions (do not re-litigate)

From the Antigen design + research synthesis (all 11 papers digested,
`docs/research/pbt-dependent-types/`):

1. Generator = **bidirectional-rule inversion** (head symbol ⇒ mode;
   constructor → check-mode, destructor/var → infer-mode) + **INDIR**
   (Pałka: pick a head from Γ/signature, read argument goals off its
   Π-telescope, substituting earlier args into later goal types).
2. **Keep a plain application rule** alongside INDIR — INDIR cannot build
   redexes, and `subject_reduction`/`normalization_stability` need firing
   redexes to say anything.
3. **Interleaved generation-and-checking**: semantic side conditions
   (index/conversion constraints) are discharged *during* generation via the
   kernel's own conv-checker under a fixed fuel budget — never re-derived by a
   parallel implementation.
4. Backend swappable: everything is an `Antigen.Gen` program; **nothing under
   `Antigen.Generators.*` / `Antigen.Assays.*` may reference `StreamData`**
   (the architecture test extends to the new modules).
5. Never trust the kernel against itself alone: differential assays are
   *self-consistency* evidence; known-label verticals (totality, positivity,
   universes) remain the ground-truth channel; reflexivity remains the halting
   probe. The three kinds together are the oracle strategy.
6. Two committed, never-pruned, C2-serialized, generator-independent stores
   (`corpus.sexp` antibodies, `seeds.sexp` coverage-deduped bank) plus
   `reach.sexp` pins. Fixed committed fuel decides verdicts; wall-clock
   killswitch is a safety net, never a verdict.
7. Health gate guards vacuous green (Well-Typed-Not-Useless: naive top-down
   generators use ~30% of binders vs ~95% in real code).

## 3. Approaches considered

**A. Interleaved mode-directed generator hosted in the Tier-A harness
(chosen).** Realize the locked research design minimally: generation rules
mirror `Kernel.infer/check` clauses one-for-one, semantic constraints
discharged at choice time by `Conv`, every dead end avoided by construction
via a canonical-inhabitant fallback (§6.4). Highest yield per generated
candidate; the discard path is nearly empty by design.

**B. Generate-then-filter.** Grammar-generate raw skeletons, run
`Kernel.infer` to keep the well-typed ones. Simplest possible build, but
well-typed density collapses exponentially with depth — the health gate would
report near-total discard and the banked terms would be trivially small. This
is exactly the failure mode the research pass rejected; kept here only as the
baseline the health metrics implicitly compare against.

**C. Derivation-tree generation (QuickChick POPL'18).** Reify every kernel
rule as a generation relation and extract terms from generated derivations.
Most principled — sound *and* complete by construction — but it is a second
implementation of the kernel's rule system, which drifts as K-layer work lands
(the `unfold_head` completion is already scheduled). Right shape for a distant
assurance milestone, wrong cost now.

A is the locked direction; B under-shoots and C over-shoots it.

## 4. Architecture

New modules (all pure `Antigen.Gen` programs / pure functions; StreamData
stays quarantined behind `Backend.StreamData`):

```
lib/antigen/
  generators/
    sig_menu.ex        # SignatureMenu — versioned family/def scaffolds + env_of/1
    context.ex         # Generators.Context — telescopes Γ over menu types
    term.ex            # Generators.Term — gen_term(Γ, T); the engine
  assays/
    term.ex            # Assays.Term — the three differential assays
  challenge.ex         # + :typed_term kind (to_pieces/from_pieces/@known_atoms)
  coverage.ex          # + terms_of/key clauses + binder/redex flags
  runner.ex            # + assay registry entries; health floors in summarize
```

Data flow (explore mode): `Generators.Term.typed_term/1` takes an assay id
(one of the three §7 registry ids) and emits a `%Challenge{kind: :typed_term,
assay: id}` drawn independently for that id — the existing one-challenge/
one-assay Runner contract (`c.assay` selects the module; `Mix.Tasks.Antigen`'s
private `default_gen/0`, `lib/mix/tasks/antigen.ex`, already composes
per-vertical generators this way) extends here by adding three more
`Gen.frequency` branches, one per assay id, each an
independent draw from the same `gen_term`/context engine. A drawn Challenge
→ Runner banks it in `seeds.sexp` (coverage-deduped) → its tagged assay runs
→ `:ok` or an infection that writes a `tmp/antigen/` report and appends an
antibody to `corpus.sexp`. Replay mode decodes stored records and re-runs
assays statically — no generation, no StreamData, exactly the Tier-A
discipline.

### 4.1 The `:typed_term` challenge

```elixir
payload: %{
  sig: :v1,          # menu version — env rebuilt deterministically via SignatureMenu.env_of/1
  ctx: [core_type],  # telescope in kernel order: index 0 is the most-recently-
                     # bound variable (innermost), matching Cure.Core.Context's own
                     # `types` list (extend/1 prepends; lookup/2's k=0 is "most
                     # recent"). Rebuilding a Context therefore walks this list
                     # OUTERMOST-first — i.e. Enum.reverse(ctx), evaluating and
                     # Context.extend/2-ing each entry in turn — so the last extend
                     # is ctx's index-0 entry and it lands back at the rebuilt
                     # Context's head; each entry's own de Bruijn indices are scoped
                     # to the context built from the entries after it (outer to it)
  type: core_type,   # the goal type T
  term: core_term    # the generated t with claimed  Γ ⊢ t : T
}
label: :well_typed   # Tier B generates only the positive direction (§1 deferred: mutation)
```

Serialization: pieces `{"type", T}`, `{"term", t}`, `{"ctx0", …}`,
`{"ctx1", …}` … with `sig` and ctx length in the scaffold channel. The menu's
family/ctor/def atoms join `Challenge.@known_atoms` so replay decodes in a
fresh process. Coverage `terms_of/1` returns `[type, term | ctx]`.

## 5. The signature menu (v1)

A fixed, versioned scaffold — richness lives here, and growing it later is a
new version, never a mutation (corpus records name the version they replay
against).

- **Families:** `Nat` (`Z`, `S`); `Bd` (`T`, `F` — two nullary ctors, gives
  `case` diversity without indices); `Vec(n: Nat)` — a Nat-indexed family of
  Nat entries (`vnil : Vec(Z)`, `vcons : (n: Nat) -> Nat -> Vec(n) ->
  Vec(S(n))`). Element type fixed to `Nat` deliberately: type-*parameter*
  generation adds a guessing dimension with no assay payoff in v1.
- **Certified defs:** `plus : Nat -> Nat -> Nat` (structural on arg 1) and
  `dbl : Nat -> Nat` — so δ/ι activity exists in generated terms and
  `subject_reduction` exercises `unfold_head`, including scrutinee positions
  (the reach-pinned normalizer incompleteness: stuck-case freezes are
  *expected* stucks, not violations — see §7.3).
- `SignatureMenu.env_of(:v1)` declares families, adds defs, certifies `plus`
  and `dbl` by running the real totality procedure — `Kernel.validate_certificate/2`
  (`check_def` + `Cure.Core.Certificate.terminating?` + `Env.certify`), the
  same real-procedure discipline `Antigen.Generators.Forcing` already follows
  for its focus defs — **never** a raw `Env.certify/2` bypass: locked decision
  #3/#5 (semantic conditions discharged by the kernel itself, never re-derived
  or asserted) applies to certification exactly as it does to conversion —
  and returns the `Env` — the `Generators.Indexed.env_of/1` idiom, but keyed
  by version instead of carried per-record.

Goal types generated over the menu: `Nat`, `Bd`, `Vec(i)` for a generated
index `i`, `Pi`/`Sigma` over these (nesting bounded by size), universes ≤
`Type 0` for goals (`Type 1` appears only as the sort of goal types, never as
a goal — universe soundness already has its own known-label vertical).

### 5.1 The context generator (`Generators.Context`)

Builds Γ as a genuinely **dependent** telescope, not a flat list of
independent types: a `Gen.sized`-bounded number of entries, each entry's type
generated by recursing into the engine itself — `gen_term(Γ_so_far, Type 0)`
against §6.1's `Type 0` row — with `Γ_so_far` the telescope built from the
entries *before* it, so a later entry's type may reference an earlier one
(e.g. an entry of type `Vec(n)` needs a preceding `n : Nat` entry already in
scope; this is exactly the mechanism, not a special case). Deliberate
shadowing (§6.5) is introduced here: some draws deliberately repeat the same
*type* at adjacent or nearby positions (two `Nat` entries back to back, etc.)
rather than always widening the type mix, so `Γ`'s de Bruijn indices get
exercised at consecutive/nearby depths — "reuse names" (§6.5) means reused
*type shape*, not surface names; Core has none (de Bruijn only). The
top-level `gen_term(Γ, T)` call then draws its own goal `T` (§5's list) over
the `Γ` this generator produced.

## 6. `gen_term(Γ, T)` — the engine

### 6.1 Mode-directed rule table

At each node the generator whnf's the goal type (certified env, fixed fuel)
and draws from the rules whose conclusion matches, weighted by
`Gen.frequency`:

| Goal `T` (whnf) | Check-mode intros | Infer-mode eliminations |
|---|---|---|
| `Pi(A, B)` | `lam` (recurse at `B` under `Γ,A`) | var whose type meets `T`; INDIR; plain app; `fst`/`snd` of a Γ-var of Sigma type whose component meets `T`; `case` (§6.5) — the full elimination menu |
| `Sigma(A, B)` | `pair` (gen `a : A`, then `b : B[a]`) | the full elimination menu |
| `data`/`Vec(i)` | constructor whose result index unifies (§6.3) | the full elimination menu |
| `Type 0` | a menu type former | var; INDIR **only** — deliberately narrower than the full menu: `case`/`fst`/`snd`/plain-app would need, respectively, a case-family whose branches can be `Type 0`-sorted, a Γ-var of Sigma type whose component is `Type 0`-sorted, or a function into `Type 0` — and the v1 menu never puts `Type 0` in a family, Sigma-component, or Pi-codomain position (§5: element type fixed to `Nat`, no type-parameter generation), so none of those forms ever have a candidate to offer at this goal; they're pruned here as dead weight for v1, not excluded on principle |

Infer-mode candidates produce a term with an *inferred* type value (from
`Kernel.infer`); the generator accepts one only if that value, reified to a
Core term via `Quote.reify`/`Normalise.quote` at the current depth (same for
the goal `T`, if it is being threaded as a value rather than the term already
on hand), converges with `T` under `Conv.conv_within?(inferred_term, T, env,
depth, sig, @gen_fuel)` returning `{:ok, true}` — `conv_within?/6`
(`lib/cure/core/conv.ex`) is Term-level and fuel-bounded; there is no
fuel-bounded value-level comparator (the kernel's own inferred-vs-expected
check, `Kernel.subtype?/3`, instead uses the *unfueled* `Conv.conv_values?/4`,
which is not the fit here since generation must stay bounded). This is the
interleaved-checking rule. Fuel exhaustion or `false` at
choice time means that candidate is simply not offered (not a discard, not a
violation — the option set shrinks, §6.4 guarantees it never empties).

### 6.2 INDIR (head-first saturated elimination)

Pick a head `h` from Γ or the certified-def menu whose type is a Π-telescope
ending (after whnf) in something convertible with `T` once arguments are
chosen. Walk the telescope left to right, generating each argument at its
domain type *with earlier arguments substituted into later domains and into
the result* — this is where dependent generation earns its name. Heads whose
result can never meet `T` at the current size are filtered before the draw.

### 6.3 Constructor choice under indices

For goal `Vec(i)`: a constructor is offered iff its result index unifies
first-order with `i` — `vnil` iff `conv(i, Z)`, `vcons` iff `i` whnf-reduces
to `S(j)` (then recurse with `j`). These are index constraints, so per locked
decision #3 they run under the same `@gen_fuel`-bounded kernel calls as
§6.1's acceptance rule (`Normalise.whnf`/`Conv.conv_within?`, not a separate
unbounded check) — `i` is generator-built and shallow in practice, but the
fuel bound is the same non-negotiable discipline, not an optimization to skip
here. When `i` is a stuck neutral (e.g. a variable), only infer-mode rules
apply — exactly the situation dependent matching lives in, and precisely the
terms the assays should see.

### 6.4 Totality: the canonical-inhabitant fallback

Define a cheap recursive predicate `inhabitable?(Γ, T)`: `Nat`, `Bd`, and
`Type 0` always; `Pi(A, B)` iff `inhabitable?((Γ, A), B)`; `Sigma(A, B)` iff
`inhabitable?(Γ, A)` and `inhabitable?` of the instantiated `B`; `Vec(i)` iff
the index whnf's to a closed numeral **or** Γ contains a variable whose type
is convertible with `Vec(i)` (or a Sigma/Pi projection/application chain the
elimination menu can reach in one step). The generator maintains the
invariant that **every goal it poses is inhabitable in its Γ**: any rule
whose subgoals would break the invariant is filtered before the frequency
draw (e.g. `vcons` at goal `Vec(S(x))` with stuck `x` is offered only when
`Vec(x)` is inhabitable — otherwise only the elimination menu remains, and
the invariant guarantees it is non-empty).

Canonical inhabitants then exist for every inhabitable goal with no search:
`Nat → Z`, `Bd → T`, `Vec(Z) → vnil`, `Vec(S j) → vcons(j, Z, canon(Vec(j)))`
(reaching `Vec(numeral)` or a Γ-var by the invariant), `Pi(A,B) →
lam(canon(B))`, `Sigma(A,B) → pair(canon(A), canon(B[canon(A)]))`, `Type 0 →
Nat`, and a Γ-var (or one-step projection) for stuck-indexed `Vec`. At size 0
or an empty option set the generator emits the canonical term. Consequence:
**generation is total — the discard path exists only for the Runner's
defensive `well_formed?` check.** Distribution skew toward canonical forms is
what the health gate measures, not something to hide.

### 6.5 Redexes and `case`

- **Plain application** (`Gen.frequency`-weighted alongside INDIR): generate
  `f : Pi(A, B)` where `B[a]` meets the goal, *allowing* `f` to be a fresh
  `lam` — this manufactures β-redexes INDIR cannot.
- **`case`**: generate a scrutinee of a menu family (sometimes a constructor
  value → ι-redex; sometimes a Γ-variable → stuck case), a motive from the
  goal by the constant-motive rule (v1: motive is `λx. T`; index-refining
  motives arrive with the mutation follow-up), and branch bodies at the
  motive's instantiations.
- **Deliberate shadowing:** binder-heavy contexts reuse names/levels so de
  Bruijn arithmetic is exercised (the Term.shift/subst literal-clause hole
  found in the banking run is exactly this class).

### 6.6 Size and determinism

`Gen.sized` splits the size budget across subgoals; `@gen_fuel 500`
(conversion discharge) and `@assay_fuel 500` are fixed committed constants,
distinct so a future tuning of one cannot silently change the other's
verdicts. No wall-clock anywhere in verdict paths.

## 7. The differential assays

All three consume `:typed_term`; registry ids `"term/infer_check"`,
`"term/subject_reduction"`, `"term/normalization"`. Each is pure
`Challenge → :ok | {:violation, detail}`, rebuilding the env via
`SignatureMenu.env_of/1`. Fuel exhaustion inside an assay is its own violation
class `{:fuel_exhausted, stage}` — a suspected non-normalization, triaged like
a reflexivity infection, never conflated with a mismatch.

### 7.1 `infer_check_agreement`

`Kernel.infer(Γ, t) = {:ok, A}` must imply `Kernel.check(Γ, t, A) = :ok`, and
`A` must be convertible with the generator's claimed `T`. Violations:
`{:infer_failed, e}` (see triage, §7.4), `{:check_disagrees, e}`,
`{:inferred_type_mismatch, A, T}`.

### 7.2 `subject_reduction`

With `A` inferred: `nf(t)` (certified env, fuel) must still check at `A`.
Violation `{:nf_ill_typed, e}` is the sharp one — a normalizer that breaks
typing is a soundness bug in the TCB's computational half.

### 7.3 `normalization_stability`

`nf(nf(t)) == nf(t)` (syntactic Core equality), `nf(t)` re-checks, and the C2
round-trip `decode(encode(t)) == t` holds. **Expected-stuck allowance:** a
`nf` result containing stuck `case`/`fst`/`snd` frames is *normal* under the
current reach-pinned normalizer (`reach.sexp`; the `unfold_head` seam is its
own scheduled TCB run) — stability is asserted about whatever `nf` returns,
so this assay stays green across that future kernel change unless idempotence
itself breaks. When that TCB run lands, re-running this assay over the banked
seed corpus is its regression net.

### 7.4 Triage rule (the kernel-as-own-oracle ambiguity)

A generated term failing `infer` is ambiguous: generator bug (mislabeled
claim) or kernel incompleteness (wrongly rejected). Mirroring the
indexed-case 4.3 precedent: reproduce minimally by hand; if the term is
genuinely well-typed, record `{:wrongly_rejected, …}` and pin it in
`reach.sexp` (rejection ≠ unsoundness); if the generator's claim was wrong,
fix the generator and add a generator self-test. **Neither outcome is
silently dropped** — every infection either becomes an antibody, a reach pin,
or a generator red-green fix.

## 8. Health gate

Per explore run, over *banked* (post-dedup) challenges. Of the three metrics
below, **discard rate keeps its existing whole-run scope** (all six
`default_gen/0` branches, §4) unchanged; **binder-usage and
reduction-activity are new and scoped to `:typed_term` challenges only** —
they measure `gen_term`'s output quality specifically (locked decision #7's
Well-Typed-Not-Useless concern), and Tier A's existing
`:def_group`/`:family`/`:forcing_pair` challenges are hand-constructed
known-label objects the new metrics say nothing useful about and must not
dilute the denominator:

- **discard rate** — existing; expected ≈ 0 given §6.4 (floor: < 10%).
- **binder-usage** — fraction of generated `lam`/`case`-branch binders whose
  variable occurs in the body (floor: ≥ 60% in v1; literature says naive ≈
  30%, real code ≈ 95% — tune upward as the engine matures).
- **reduction-activity** — fraction of banked terms with `nf(t) ≠ t` (a redex
  actually fired; floor: ≥ 25%). `Normalise.nf/3` can return the atom
  `:fuel_exhausted` instead of a term; that is **not** reduction activity (a
  bare atom is trivially `≠ t` under a naive comparison, which would inflate
  the metric on exactly the terms most worth scrutinizing) — a fuel-exhausted
  `nf(t)` counts toward neither the fired-redex numerator nor the denominator,
  and is instead reported alongside the three metrics as its own count (a
  non-zero rate here is itself a health-gate red flag, surfaced the same way
  discard rate is).

Enforcement in two places: (1) the explorer's summary line reports the three
metrics and stamps the run `:healthy` / `:vacuous` — a `:vacuous` run's green
assays are explicitly labeled non-evidence; (2) a committed ExUnit meta-test
replays the banked seed corpus **statically** and asserts the floors over it —
so vacuity is durably red in `mix test` without generation flakiness in CI.
Floors are module attributes on `Antigen.Runner`, next to `summarize/2` (§4:
"health floors in summarize") — **not** beside `@gen_fuel`/`@assay_fuel`,
which live in `Generators.Term`/`Assays.Term` respectively (§6.6) and belong
to a different module than the one that computes and enforces the floors.

## 9. Testing the engine itself

- **Architecture test** extends to the three new generator/assay modules (no
  `StreamData` reference).
- **Generator soundness meta-test** (Foundational-PBT "runnable soundness"):
  a fixed-count sample of `:typed_term` challenges must all `Kernel.check` at
  their claimed type; failures go through §7.4 triage. Canonical-fallback
  totality: `canon(T)` exists and checks for every *inhabitable* goal (§6.4),
  exercised over a fixed matrix of goals including stuck-indexed `Vec` with a
  matching Γ-var.
- **Corpus round-trip / replay determinism:** every new-kind record encodes →
  decodes → re-runs to the same verdict (existing test patterns, new kind).
- **Support-set checks:** `gen_term` is necessarily recursive (each rule's
  subgoals recurse into `gen_term` again), so it is built from `Gen.bind`
  throughout, and `Gen.support/1`'s `{:bind, _, _}` clause is unconditionally
  `:over_approx` — a verdict that is contagious upward through any enclosing
  `frequency`/`one_of` (`union_support`'s reduce-while halts on the first
  `:over_approx` branch). The engine's own support is therefore `:over_approx`
  top-to-bottom, same as Tier A's §6 anticipated ("[a general term generator]
  does need a distinguished fixed-point node for the static support-set pass
  to terminate on") — Tier B does **not** add that `Gen` primitive (§4 leaves
  `lib/antigen/gen.ex` untouched), so this is an accepted, named limit, not a
  claim of finiteness. What the meta-test actually asserts is narrower and
  does stay finite: the single, non-recursive *rule-choice* `Gen.frequency`
  node at one generation step — which head/rule to try next, before recursing
  into its subgoals — is `:finite` and its member set is exactly the menu +
  Γ + rule table (choice points inspectable), independent of `gen_term`'s
  overall (over-approximated) support.

## 10. Acceptance criteria

1. `mix antigen` explore — by this point `default_gen/0` (§4) draws from six
   `Gen.frequency` branches (Tier A's three known-label generators plus the
   three new `:typed_term`/assay-id branches, weight 1 each, no `--gen`
   filter exists or is added) — completes a `--count 500` run: every
   infection minted an antibody + report, every non-duplicate candidate
   banked as a seed, health metrics printed for the `:typed_term` subset of
   that run (expected ~250 of the 500 draws at equal weighting).
2. The banked seed corpus meets the §8 floors, and the static-replay
   meta-test enforcing them is green in `mix test`.
3. All three assays green over the banked corpus **or** each violation
   resolved per §7.4 (antibody + fix, or reach pin) — no open/xfail states,
   per the pure-verdict rule.
4. Architecture, soundness-meta, round-trip, and determinism tests green;
   full suite green.
5. The parity ledger row #22 and expansion rows A8/A10 updated (A10 partially:
   the term stream feeds the differential assays; feeding *existing* verticals
   from generated streams remains open).

## 11. Risks

- **Yield is the engineering unknown** (locked framing: correctness is not).
  Mitigated by construction-totality (§6.4) plus the health gate making
  weak distributions visible instead of silently green. If floors can't be
  met at v1 sizes, the spec's answer is frequency tuning and menu growth —
  not floor lowering — and that tuning is measurable inside acceptance run 1.
- **Shrinking through deep `bind`** is StreamData's weak spot; the small v1
  fragment keeps shrink chains short, and the type-preserving post-shrink
  pass from Tier A applies before an antibody is pinned. `ChoiceSeq` remains
  the long-term answer (deferred).
- **Kernel churn** (the scheduled `unfold_head` TCB run) — §7.3 is written so
  the assays survive it; the banked corpus doubles as that run's regression
  net, which is a feature, not a coupling.

## 12. Implementation base

Implement on a fresh worktree cut from the **transliteration-p0 merged
state** (it carries the universes vertical, the `Term` literal-clause fixes,
and the current ledger). This spec lives on the authoring branch and merges
wherever the run happens; nothing in it depends on unmerged authoring-branch
state.
