# Antigen V5 — Totality-Closure Soundness — Design

**Status:** design (Stage 0, autopilot Phase 4) · **Date:** 2026-07-03 · **Branch:** `autopilot/antigen-tier-b`
**Umbrella:** `2026-07-03-antigen-untrusted-machinery-design.md` §V5 · **Predecessors:** V3 (elab), V1 (normalizer), V2 (unifier)

## 1. Goal

Extend Antigen to the **untrusted totality-closure driver**
`Cure.Elab.TotalityClosure` — the module that decides *which* type-level functions
must be certified total, and submits each to the trusted kernel. Type-level
non-termination is a **logical-inconsistency** hole: if the type-checker δ-unfolds a
function it relies on for convertibility and that function does not terminate,
Normalise loops (or a mis-certified diverging function admits a false type
equality). The kernel re-checks each *certificate* (`Kernel.validate_certificate`,
trusted); what it does **not** do — the untrusted half of the external Cure design
spec's §7 (`2026-06-30-cure-dependent-types-frp-design.md`, not this document's own
§7) — is decide the
**closure**: the set of functions reachable from a type position that must be
submitted at all.

**What is already covered vs. what is new.** The existing
`Antigen.Assays.Totality` (`totality/diverging` + `totality/terminating`) tests the
per-function *decision procedure* `Cure.Core.Certificate.terminating?/3`. V5 does
**not** duplicate that. V5's target is the **driver** around it:

- `type_level_fns/1` — the untrusted transitive-closure walk over type positions.
- `certify_type_level/1` — the end-to-end driver that folds `validate_certificate`
  over that closure.

## 2. Target (verified against source: `lib/cure/elab/totality_closure.ex`)

- `type_level_fns(%Env{}) :: MapSet.t(atom())` — every global reachable from a
  **type position**, transitively. Type positions (verified): family
  `params`/`indices` telescopes, constructor `args` telescope, constructor
  `result_indices`; transitive callees via each reached def's `body`. Uses private
  `seed_globals/1`, `tele_globals/1`, `close/3`, `collect/1`.
- `certify_type_level(%Env{}) :: {:ok, Env.t()} | {:error, {:totality_required, atom()}}`
  — `type_level_fns |> Enum.reduce_while({:ok, env}, …)` calling
  `Kernel.validate_certificate(acc, name)` for each; the first `{:error, _}` halts
  with `{:error, {:totality_required, name}}`.
- **The moduledoc's own safety claim** (to test, not assume): "a function this walk
  misses simply stays uncertified (opaque to δ) — never a soundness hole." V5b puts
  a number on the walk's completeness against an independent oracle; a *missed*
  type-level function is at minimum a violation of the closure's stated
  transitive-closure contract (`2026-06-30-cure-dependent-types-frp-design.md` §7
  "Totality integration" — the "design spec §5, §7" the module doc cites; **not**
  this document's own §7, which is Non-goals), and the whole opacity-safety
  argument rests on the walk actually being the closure it claims.
- **Trusted boundary:** `Kernel.validate_certificate/2` (kernel.ex:379, "re-run the
  totality decision procedure on a registered, type-checked global") is TCB and
  re-derives totality — so it needs no pre-attached certificate. V5 treats it as
  the trusted re-check and does **not** test it directly (that is the kernel's own
  Antigen coverage); V5 tests the untrusted driver that feeds it.

## 3. Properties (two families)

### V5a — certification soundness (end-to-end, adversarial; oracle = known label)

Reusing the `totality/*` known-label construction: a **by-construction diverging**
function placed in a **type position** (so `type_level_fns` reaches it) must be
**rejected** by the whole driver. Correct behavior returns `:ok`; a wrongful
certification is the infection:

- `certify_type_level(env)` on a diverging-in-type-position env **must** return
  `{:error, {:totality_required, _}}`. If it returns `{:ok, _}`, the diverging
  function was certified (or, more insidiously, was *missed* by the closure so it
  was never submitted and the env passed vacuously) →
  `{:violation, {:diverging_certified, env_id}}`.

This is strictly stronger than the existing `totality/diverging` assay: that one
calls `Certificate.terminating?` **directly** on the focus def; V5a exercises the
**closure-reachability + submission** path — the diverging function is only found if
`type_level_fns` reaches it and only rejected if the driver actually submits it. A
closure that under-approximates (misses the diverging function in the type
position) turns a soundness rejection into a silent `{:ok}` — exactly the driver
bug V5a exists to catch.

### V5b — closure completeness (intrinsic; independent reachability oracle)

`type_level_fns(env)` must be a **superset** of an Antigen-owned, independently
written re-derivation of type-position reachability over the same env (walking
family `params`/`indices`, ctor `args`/`result_indices`, transitively via def
bodies — the external design spec's §7 contract (see §2 above), re-implemented in
the assay, independent of `TotalityClosure`'s private `collect`/`close`, the V1/V2
independent-oracle tactic):

- a global that the independent walk reaches from a type position but that is
  **absent** from `type_level_fns(env)` is `{:violation, {:closure_missed, name}}`.

The independent walk is deliberately a *superset-or-equal* oracle: V5b asserts
`independent ⊆ closure` (the closure misses nothing the contract requires). It does
**not** assert equality — the closure legitimately including *more* (a conservative
over-approximation) is not a soundness problem.

## 4. Assay & injectable seam

New module `Antigen.Assays.TotalityClosureAssay` (name avoids colliding with
`Cure.Elab.TotalityClosure`) with `run/1` → `run/2` (op-map seam), mirroring
`Antigen.Assays.{Elab,Normalizer,Unifier}`. Two assay ids:

| id | property | oracle |
|---|---|---|
| `totality_closure/soundness` | diverging-in-type-position ⟹ rejected | known label |
| `totality_closure/completeness` | `type_level_fns ⊇` independent reachability | independent walk |

No `@assay_fuel`/`Conv` needed — `certify_type_level` and `type_level_fns` are
static structural walks that terminate on their own (per the existing
`Antigen.Assays.Totality` moduledoc: "the certifier is a static structural analysis
that terminates on its own, so no fuel is needed"); the diverging *function's*
non-termination is by-construction (never actually run — the certifier rejects it
structurally).

**Op-map** (`@real`), injecting the **code-under-test** at the assay boundary:

```elixir
%{
  certify: &Cure.Elab.TotalityClosure.certify_type_level/1,
  type_level_fns: &Cure.Elab.TotalityClosure.type_level_fns/1
}
```

Negative controls prove each assay load-bearing:
- `totality_closure/soundness`: a `certify` stub returning `{:ok, env}`
  unconditionally → `{:diverging_certified,…}` on the diverging-in-type-position env.
- `totality_closure/completeness`: a `type_level_fns` stub returning
  `MapSet.new()` (or one dropping a known-reachable name) → `{:closure_missed,…}`.

## 5. Generator

New module `Antigen.Generators.ClosureEnv` producing **fixed catalogs** (the
established fixed-catalog reconciliation — no Corpus/Coverage surgery; reuse the
existing `:def_group` challenge kind if its payload fits, else a lightweight
`:closure_env` kind, typespec-only, wired via `assay_module/1` + a dedicated test):

- `soundness_challenges/0` — envs each carrying a by-construction diverging
  type-level function referenced from a **type position** (a family index telescope
  or a ctor `result_indices` mentioning `{:global, :loop}`), plus its definition.
  `certify_type_level` routes every submitted name through the TRUSTED
  `Kernel.validate_certificate` → `check_def`, which (verified: `kernel.ex` `infer`
  clause for `{:data, name, _, _}`) requires `name` to resolve via
  `Inductive.get_family/2` — a bare `{:data, …}`-typed def whose family isn't
  registered fails `check_def` with `{:unknown_family, …}` before
  `Certificate.terminating?` is ever reached. `Antigen.Generators.Totality.env_of/1`
  does **not** register families (it only folds `Env.add_def/4`), so its stock
  diverging-def bodies/types (`@dec`/`@nat`-typed: `diverging_mutual_pair`,
  `structural_terminating`, the W1/W2 set) would fail `check_def` this way — reusing
  that construction verbatim is **not sufficient** once the env is driven through
  `certify_type_level` rather than `Certificate.terminating?` directly.

  **Minimal sufficient construction (preferred for the baseline):**
  `certify_type_level` never calls `check_family`/`check_ctor` — `seed_globals`
  reads `env.families`/`env.ctors` map values' raw fields with no kernel
  validation — so the *vessel* (the family/ctor whose index/`result_indices`
  mentions `{:global, :loop}`) does **not** need to be `Inductive.declare`d in a
  kernel-checkable way; only `:loop`'s *own* `check_def` needs to pass. Give
  `:loop` (and the all-total control's counterpart) an `{:int_type}`-only
  signature: `loop : Int -> Int`, `loop = λx. loop x` (bare unconditional
  self-call, no `:case`, no `:data` anywhere) for the diverging case, and e.g.
  `total_id : Int -> Int`, `total_id = λx. x` (no self-call at all, so
  `Certificate.terminating?`'s `not calls?(name, body) -> true` fast path applies)
  for the all-total control. Neither needs any family/ctor registration:
  `infer`/`infer_sort` on `{:int_type}` needs no family lookup (kernel.ex line 58),
  and `:loop`'s self-call is still structurally rejected by
  `Certificate.terminating?` (`decreasing?` sees `{:var,0}` is not yet in the empty
  `smaller` set). This sidesteps open item #2's masking risk entirely — there is no
  `check_def`-vs-`Certificate.terminating?` ambiguity to guard against when neither
  def references a `:data` type.

  **Heavier alternative:** only needed for `:data`-typed (Nat/Vec-indexed) coverage
  variety — declare the family (+ constructors, since a `:case`-based diverging
  body also needs `Inductive.get_ctor`/coverage-checking to succeed) the way
  `Antigen.Generators.SigMenu.env_of(:v1)` already does (`Inductive.declare/3`, then
  `Env.add_def`) — that module is the codebase's existing, working template for a
  `check_def`-passable `:data`-typed env, not `Generators.Totality.env_of/1`. If
  this route is used, the all-total control must carry the **same** family/ctor
  registration or it will falsely fail `check_def` for an unrelated reason and lose
  its purpose (open item #2).

  Either way, the **new** generator work is the *env wiring* that places
  `{:global, :loop}` in a type position (open item #1) — not just def-list assembly.
- `completeness_challenges/0` — envs with globals genuinely in type positions
  (direct + one transitive-callee case: a type-position global whose body calls a
  second global), for which the independent walk and `type_level_fns` must agree
  (⊆).

## 6. Invariants (what must never regress)

- No `Cure.Core.*`, `Cure.Elab.*` edits — the driver reached read-only through the
  op-map. No `:meck`, no new dependency.
- `Antigen.Assays.TotalityClosureAssay` contains no literal `StreamData` token
  (the `architecture_test` grep — banked from V1's Stage-5 trip; comments too).
- Assay `run/1,2` returns only `:ok | {:violation, term()}` (matches the `@spec` and
  `Runner.replay_one/1`/`explore/1`'s no-catch-all dispatch). V5's incompleteness
  direction (a genuinely-total function the closure refuses, or the closure
  *over*-approximating) is out of scope — not surfaced as a third outcome.
- The whole clean catalog re-checks `:ok` under the real ops (a real infection ⟹
  STOP and report; do not weaken a test). In particular, if the real
  `certify_type_level` **fails to reject** a diverging-in-type-position env, that is
  a genuine V5a soundness finding — report it, do not adjust the catalog.

## 7. Non-goals

- No fix to the closure driver (V5 *finds*; a surfaced infection is reported, not
  patched, without separate authorization).
- No duplication of the existing `totality/diverging` + `totality/terminating`
  assays (which cover `Certificate.terminating?` directly) — V5 is strictly the
  driver around them. **Umbrella reconciliation:** the umbrella's V5 bullet lists
  two properties, "Soundness (differential)" and "Incompleteness (surfaced): a
  genuinely-total function the closure refuses to certify is a reach gap." The
  second is exactly what the pre-existing `totality/terminating` assay already
  tests (a by-construction-total def, incl. the W2 reach-pins for mutual/
  permuting recursion, that `Certificate.terminating?` conservatively rejects) —
  that rejection propagates unchanged through `certify_type_level`'s pass-through
  `{:error, _}` mapping, so it needs no new V5-owned assay; the umbrella's
  "closure refuses to certify" bullet is pre-existing coverage, not a V5 gap. V5's
  own two properties (V5a driver-soundness, V5b closure-completeness) are
  additional to, not a narrowing of, the umbrella's stated scope.
- No test of `Kernel.validate_certificate` (trusted TCB; the kernel's own coverage).
- No random env fuzzer — a curated fixed catalog (elab pattern). A
  generator-expansion follow-on could widen coverage.
- No SMT (that is V6).

## 8. Open items (for the plan / review to pin)

1. **Env construction placing a global in a type position — CONFIRMED requirement,
   not just a question to pin.** `%Env{}` is `families/ctors/ctor_to_family/defs/
   certified/builtins` (verified: `Cure.Core.Env` in `lib/cure/core/inductive.ex`);
   `families: %{atom => %{name, params, indices, level}}`,
   `ctors: %{atom => %{name, args, result_indices, result_params, quantities}}`,
   `Env.get_def/2` reads `defs`. For `soundness_challenges/0` the recommended,
   minimal construction (§5) gives `:loop`/its total counterpart an `{:int_type}`-
   only signature (no `:data` reference anywhere in the def under test), which
   needs **no** `Inductive.declare/3` at all — `infer`/`infer_sort` on `{:int_type}`
   never calls `Inductive.get_family`. The *vessel* family/ctor placing
   `{:global, :loop}` in a type position is likewise never kernel-checked by
   `certify_type_level` (it only calls `Kernel.validate_certificate` on
   `type_level_fns`'s members, never `check_family`/`check_ctor`), so it can be a
   bare map literal in `env.families`/`env.ctors`. `Inductive.declare/3` (and the
   `Antigen.Generators.SigMenu.env_of(:v1)` shape: declare, then `Env.add_def`) is
   needed only for the heavier `:data`-typed alternative (§5) — e.g. if a def under
   test's own type or a `:case` in its body references a family, that family (+
   constructors, for coverage-checking) must be registered or `check_def` fails
   with `{:unknown_family, …}` before `Certificate.terminating?` runs (see item 2).
   **`completeness_challenges/0` needs no kernel-checkable registration at all** —
   verified, `type_level_fns`/`seed_globals`/`close`/`collect` never call
   `Inductive.get_family`/`get_ctor` or any kernel check; they read
   `env.families`/`env.ctors` map values' `.params`/`.indices`/`.args`/
   `.result_indices` fields directly. A V5b env can use bare map literals
   throughout (no `Inductive.declare/3`) as long as the field shapes match.
   ("Bare map literal" means patching the `families`/`ctors` fields of an env still
   built from `Env.empty()`, not a raw `%Env{}` struct literal — `Env.empty/0` is
   the only place `certified: MapSet.new()` gets set (the bare `defstruct` default
   is `nil`), and the all-total control's successful certification path calls
   `Env.certify/2`, which does `MapSet.put(certified, name)` and would crash on a
   `nil` `certified` field.)
2. **Does the real `certify_type_level` actually reject a diverging-in-type-position
   env, and for the RIGHT reason?** `certify_type_level` maps *every*
   `Kernel.validate_certificate` `{:error, _}` — regardless of cause — to the same
   outward `{:error, {:totality_required, name}}`. `validate_certificate` itself is
   `with :ok <- check_def(env, name) do … Certificate.terminating?(…) … end`
   (kernel.ex:379), so if `check_def` fails first for a reason unrelated to
   divergence (e.g. `{:unknown_family, :Dec}` from a `:data`-typed def whose family
   isn't registered), the baseline test's expected
   `{:error, {:totality_required, :loop}}` is satisfied **without the termination
   check ever running** — a vacuous pass masquerading as a soundness confirmation.
   The item-1 minimal (`{:int_type}`-only) construction sidesteps this risk by
   construction (no `:data` reference means no `{:unknown_family, …}` failure mode
   exists to worry about). If the heavier `:data`-typed alternative is used instead,
   two guards are required: (a) the all-total control env (§5, catalog item 3) —
   built with the *same* family/ctor registration as the diverging env — must
   independently observe `{:ok, _}`; if it instead errors, `check_def` is failing
   for an env-construction reason unrelated to divergence, and the generator (not
   the assay) needs fixing; (b) tracing `validate_certificate(env, :loop)` under
   real ops during generator development to confirm the rejection reason is
   specifically `Certificate.terminating?` returning `false` (`check_def` returned
   `:ok` first). If, with (a) passing, the real driver still fails to reject the
   diverging env, that is a genuine V5a soundness finding — report it.
3. **Independent reachability walk fidelity.** The V5b oracle must match
   `TotalityClosure`'s type-position contract exactly (family params+indices, ctor
   args+result_indices, transitive via def bodies). **Do not derive the walk's
   term-clause checklist by transcribing `collect/1`'s current clauses** — verified,
   `collect/1` (totality_closure.ex) and `Certificate.calls?/2` (certificate.ex) both
   have **no clause for `{:prim, op, args}`** (`Cure.Core.Term`'s node taxonomy
   includes `:prim`; it carries an `args` list of subterms, e.g. used in
   `Antigen.Generators.Totality.diverging_bool_elim_branch`'s
   `{:prim, :eq, [...]}`), so both fall through their catch-all and silently drop
   any global nested inside a `:prim`'s args. A checklist built by mirroring
   `collect/1`'s existing clauses would inherit this exact blind spot — the
   "independent" walk would agree with the closure's under-collection instead of
   catching it, making a `:prim`-mediated closure-completeness bug undetectable by
   V5b as scoped. The plan must derive the checklist from `Cure.Core.Term`'s full
   node taxonomy (module doc's node list) instead, and the independent walk must
   recurse into `:prim`'s `args`.
4. **Challenge kind.** Decide `:def_group` reuse vs a new `:closure_env` kind by
   whether the existing payload (`%{focus, …}` + `Generators.Totality.env_of`) can
   carry a full pre-built `%Env{}`; if not, add `:closure_env` (typespec-only, like
   `:surface_expr`/`:unify_problem`).
5. **Atom interning for corpus replay.** `Challenge.@known_atoms` (challenge.ex)
   force-interns every literal name a generator produces so `String.to_existing_atom/1`
   can decode a banked record in a process that never loaded the generator (the
   documented Task 5 safety note; every existing generator module keeps this list in
   sync). Verified: `:loop` — the def name this spec's every example uses
   (`{:global, :loop}`, catalog items 1/2, open items 1–2) — is **not** currently in
   `@known_atoms` (grep confirmed; it only appears in unit tests and unrelated
   protocol code, which does not force-intern it for a fresh replay process).
   Whatever concrete names the `ClosureEnv` generator settles on (`:loop`,
   `:total_id`, any family/ctor names used in the vessel) must be added to
   `@known_atoms` — and, if `to_pieces`/`from_pieces` clauses are added for a new
   `:closure_env` kind (item 4), they must decode names via
   `String.to_existing_atom/1` the same way every other kind's `from_pieces` does,
   never `String.to_atom/1`.

## 9. Test catalog (for the plan — §5 of the plan will expand each)

1. V5a soundness baseline: diverging `:loop` in a family index → `certify` rejects → `:ok`.
2. V5a soundness baseline: diverging `:loop` in a ctor `result_indices` → rejects → `:ok`.
3. V5a all-total control env: `certify` returns `{:ok, _}` → `:ok` (rejection is divergence-specific).
4. V5a negative control: unconditional-`{:ok}` `certify` stub → `{:diverging_certified,…}`.
5. V5b completeness baseline: direct type-position global present in `type_level_fns` → `:ok`.
6. V5b completeness baseline: transitive-callee global present → `:ok`.
7. V5b negative control: empty `type_level_fns` stub → `{:closure_missed,…}`.
8. V5b negative control: `type_level_fns` stub dropping the transitive callee → `{:closure_missed,…}`.
9. Generator+wiring: each catalog non-empty & correctly tagged; `Runner.replay_one/1`
   dispatches both `totality_closure/…` ids and the whole clean catalog is `:ok`.

## 10. Next (umbrella roadmap)

After V5: **V4 erasure/relevance**, then **V6 SMT lint**. **No auto-merge.**
