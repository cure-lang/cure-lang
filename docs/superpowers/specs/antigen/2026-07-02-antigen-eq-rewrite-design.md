# Antigen Eq/rewrite vertical — design

**Date:** 2026-07-02
**Status:** approved design (operator gate passed); this is the ③ sub-project of
the Eq/rewrite–case-refinement work. It ships FIRST as the audit net for ②
(the case-refinement pattern-fragment unifier).
**Vertical name:** `rewrite`. **Assay key:** `rewrite/eq`.

## 1. Goal

A deep-cut Antigen soundness vertical that probes the kernel's **propositional
equality** surface — `{:eq}` / `{:refl}` / `{:rewrite}` in `Cure.Core.Kernel` —
known-label by construction, structurally mirroring the existing indexed-case
vertical (`Antigen.{Generators,Assays}.Indexed`). It is the **safety net** for
the forthcoming ② initiative: ② reworks `case`-refinement into a pattern-fragment
unifier and deliberately keeps `rewrite` as the *propositional escape hatch*, so
`rewrite`/`Eq` soundness must be pinned down by an automated net before ② touches
that region of the TCB.

## 2. Why

- The Antigen audit left "a proper Eq/rewrite obligation probing the reworked
  `{:rewrite,…}` normalization" explicitly on file (locked decision, Antigen
  memory). This is that obligation.
- ② is a trusted-kernel refactor. Per the locked decision it must be done "with
  the Antigen suite green as the net." Case-refinement (definitional) and
  `rewrite` (propositional) are **complementary**, not identical: unification
  discharges constructor-form equations and impossible branches; `rewrite`
  transports along an opaque proof `p : a = b`. ② keeps `rewrite` as the escape
  hatch — this vertical guards it.

## 3. Kernel surface under test (facts established by reading the code)

- `infer({:eq, ty, a, b})` — Eq formation: `ty` must be a sort; `a`, `b` must
  both `check` at `ty`; result `{:vtype, level}` (kernel.ex:96).
- `infer({:refl, a})` — `refl a : Eq A a a` where `A = infer(a)` (kernel.ex:105).
- `check({:refl, a}, {:veq, ty, av, bv})` — accepts **iff** `a : ty` AND
  `conv(av, bv)` AND `conv(eval a, av)` (kernel.ex:260). This is the audit's fix:
  the old checker accepted any atom as an equality proof. **This guard is what
  makes the proof-erasing computation rule sound** and is a primary probe target.
- `infer({:rewrite, proof, motive, body})` — `proof : Eq A a b`; `body` must
  `check` at `apply(M, a)`; result `apply(M, b)` (kernel.ex:112). Body mismatch →
  `:rewrite_premise`; non-equality proof → error via `ensure_eq`.
- **Computation rule:** `eval({:rewrite, _p, _m, body}) = eval(body)` (eval.ex:63)
  — transport is proof-erasing at the value level; only the *type* moves
  `M a → M b`. Consequence: a naive "normalize the body then re-check" assay
  would MISLABEL (the erased body has type `M a`, not the def's declared `M b`).
  **All obligations here are therefore stated as typing obligations**, never as
  value-reduction stability.

## 4. Obligations (known-label; run each def through `Kernel.check_def/2`)

Each builder emits a `Challenge` (kind `:rewrite_eq`) whose `:well_typed` /
`:ill_typed` label is correct by construction. The assay's oracle is the label:
the kernel must accept iff `:well_typed`. `:ill_typed` accepted = **soundness
infection** (antibody + red-green kernel fix); `:well_typed` rejected =
incompleteness (reported per criterion §5, patched only if cheap and sound).

### 4.1 Eq formation
`Eq A a b : Type` requires `a, b : A`.
- well-typed: `Eq Dec Causal Dcoupled` in a context where both are `: Dec`.
- ill-typed: an endpoint at the wrong type (e.g. `Eq Dec Causal MkFoo` with
  `MkFoo : Foo`) → rejected.

### 4.2 refl typing + reflexive-conversion guard (audit-fixed clause)
- well-typed: `refl a : Eq A a a`; and `refl a : Eq A a a'` where `a ≡ a'`
  definitionally (endpoints convertible but not syntactically identical — a
  redex/normalization case) → accepted (completeness of the conv check).
- ill-typed (**soundness**): `refl a` checked against `Eq A a b` with `a`, `b`
  **not** convertible → rejected (`:not_definitionally_equal`). This is the
  guard that keeps proof-erasing transport sound; its failure is the classic
  "any-atom-is-a-proof" hole. Isolates the guard's FIRST conjunct,
  `conv(av, bv)`.
- ill-typed (**soundness**): `refl a` checked against `Eq A a' a'` (endpoints
  trivially convertible to each other) where `a` itself is **not** convertible
  to `a'` (e.g. `a` is a different, unrelated constructor of `A`) → rejected
  (`:not_definitionally_equal`). Isolates the guard's SECOND conjunct,
  `conv(eval a, av)`, independently of the first: with only the first ill-typed
  case above, a regression that dropped this second conjunct while keeping the
  first would go undetected, since `av ≡ bv` here means the first conjunct is
  satisfied and can no longer mask the second's absence.

### 4.3 rewrite premise discipline
`rewrite (p : Eq A a b) (M) (body : M a) : M b`.
- well-typed: `body : M a` → accepted.
- ill-typed (**soundness**): `proof` is not an equality (e.g. a plain ctor) →
  rejected (`ensure_eq`).
- ill-typed (**soundness**): `body` does not check at `M a` → rejected
  (`:rewrite_premise`). Load-bearing precision (mirrors the indexed-case 4.1
  caution): `proof` in this sub-case must itself be a genuine, valid equality
  term (e.g. a bound variable of type `Eq A a b`, or `refl a`) — if `proof`
  were *also* the "not an equality" ctor from the bullet above, `ensure_eq`
  would reject first and the challenge would never reach the
  `check(body, expected_body)` step this sub-case exists to probe, giving a
  false "confirmed sound" reading without exercising the body-checking
  discipline at all.

### 4.4 transport result-type correctness (+ refl coherence)
The kernel must assign the **transported** type `M b`, not the source `M a`.
- well-typed: a def declared `: M b` with body `rewrite (p:a=b) M (body:M a)` →
  accepted.
- ill-typed (**soundness**): the SAME body declared at a non-convertible source
  type `M a` (with `a ≢ b`) → rejected. Accepting it would prove the kernel left
  the type at `M a` (no transport) — an unsoundness given `M a ≢ M b`.
- refl coherence: `rewrite (refl a) M (body : M a) : M a` (b = a) → accepted; the
  transport is vacuous, the def declared `: M a` typechecks.

## 5. Reporting criteria (same as prior verticals)

- **Infection** = kernel accepts an `:ill_typed` challenge, or rejects a
  `:well_typed` one ⇒ the assay returns `{:violation, …}` ⇒ **red** suite.
- A confirmed **soundness** hole (ill-typed accepted) ⇒ fix red-green in the
  kernel AND bank the counterexample as a never-pruned antibody in
  `test/antigen/corpus.sexp`.
- A pure **incompleteness** (well-typed rejected, no unsoundness) ⇒ reported;
  patched only if the fix is cheap and obviously sound, else documented (the
  indexed-case 4.3 precedent).

## 6. Architecture (mirror the indexed-case vertical)

- `Antigen.Generators.Rewrite` — one builder per obligation, returning
  `Challenge.t()` with kind `:rewrite_eq` and payload
  `%{families, def_name, def_type, def_body}`. Unlike `Generators.Indexed`
  (where every obligation is exactly one `:well_typed` + one `:ill_typed`
  challenge, so the builder's argument IS the label), §4's obligations here are
  not all 1-well/1-ill: 4.1 is 1+1, but 4.2 is 2 well-typed variants (base,
  redex) + 2 ill-typed variants (conjunct-1, conjunct-2), 4.3 is 1 well-typed +
  2 ill-typed variants, 4.4 is 2 well-typed variants (transport-correct, refl
  coherence) + 1 ill-typed. Each builder therefore takes a **variant atom**
  (e.g. `refl_typing(:base | :redex | :conjunct1_violation |
  :conjunct2_violation)`), not literally `:well_typed | :ill_typed`; every
  clause still sets the returned `Challenge`'s `label` field to the correct
  `:well_typed`/`:ill_typed` value — that field, not the variant atom, is the
  assay's oracle (§4's header). 12 challenges total across the four
  obligations (2 + 4 + 3 + 3). Reuse
  the `env_of/1` + private `challenge/6` helper *shape* from `Generators.Indexed`
  — `env_of/1`, `challenge/6`, `dec_family/0`, and `foo_family/0` are all `defp`
  in `Generators.Indexed`, so they cannot literally be imported; this module
  redefines the same handful of lines locally (`Generators.Indexed` itself
  duplicates no code from `Generators.Positivity` for the same reason — this is
  the established pattern, not a shortcut). Same conceptual families as
  `Generators.Indexed`: `Dec` (`Dcoupled`/`Causal`), `Foo` (`MkFoo`) for
  wrong-type endpoints, and a tiny index family for the motive `M` in 4.3/4.4
  (a fresh family local to this module — it does not need to be `Ix`
  specifically).
- `Antigen.Assays.Rewrite` — `run(%Challenge{kind: :rewrite_eq})`: rebuild env
  via `Generators.Rewrite.env_of/1`, `Kernel.check_def`, return `:ok` iff
  acceptance matches the label, else `{:violation, {:wrongly_accepted|:wrongly_rejected, …}}`.
- `Antigen.Challenge` — add kind `:rewrite_eq`; encode/decode uses the same
  tab-delimited base64 `Serialize` envelope + `@known_atoms` interning as
  `:indexed_case` (the payload shape is identical, so this is additive).
- `Antigen.Coverage` — add a `terms_of/1` clause for kind `:rewrite_eq` (same
  payload shape as `:indexed_case`, so it can mirror that clause's body).
  `Coverage.terms_of/1`'s dispatch is exhaustive on `kind` with no fallback
  clause — without this addition, `Runner.explore/1`'s `well_formed?/1` and
  `Coverage.key/1` raise `FunctionClauseError` on any `:rewrite_eq` challenge.
  This is a prerequisite, same status as the `Challenge` extension above, not
  an incidental detail.
- Wiring, stated against how `:indexed_case` actually ships today (not the
  `mix antigen` explorer): `Generators.Indexed` has no `gen/0` and is absent
  from `Mix.Tasks.Antigen`'s `default_gen/0` — its obligations are a fixed,
  exhaustively-enumerable known-label battery, not a population worth random
  exploration, so it is never wired into the explorer sweep. `Generators.Rewrite`
  follows the same pattern: no `gen/0`; do **not** add it to `default_gen/0`.
  Banking instead happens via a dedicated `test/antigen/rewrite_seed_test.exs`
  (mirroring `test/antigen/indexed_seed_test.exs`): call each obligation's
  builders directly, `Corpus.append/3` any confirmed-infection antibody into
  `corpus.sexp` and every correctly-handled challenge into `seeds.sexp`, then
  `Runner.replay/2` both stores against a local
  `%{"rewrite/eq" => Assays.Rewrite}` registry to prove every banked record
  already replays to `:ok`. Separately, add `"rewrite/eq" => Antigen.Assays.Rewrite`
  to **both** of the two existing hardcoded registries this depends on:
  `Antigen.Runner`'s private `assay_module/1` (backs `explore/1`, `generate/1`,
  `replay_one/1`) and `test/antigen/corpus_replay_test.exs`'s `@registry` map
  (the one that actually makes committed `:rewrite_eq` records replay on every
  plain `mix test`) — they are separate maps and both must be updated.
- **Arch rule (enforced):** nothing under `Antigen.Generators.*` /
  `Antigen.Assays.*` may import StreamData (existing architecture test).

## 7. Tests (TDD, mirror `test/antigen/{generators,assays}/…`)

Built and verified **one obligation at a time**, in order 4.1 → 4.2 → 4.3 →
4.4, following the indexed-case §5 loop: for each obligation, write the
generator self-test first (item 1 below) and confirm it fails (no builder
exists yet), then write only enough of the builder to make it pass; write the
assay test first (item 2) and confirm it fails (no assay exists yet), then
write only enough of the assay to make it pass; only then run that
obligation's tests against the real kernel and triage per §5 of this spec (fix
red-green + bank an antibody on a confirmed soundness hole; report, don't
silently patch, an incompleteness). Run the full suite once and commit before
starting the next obligation. Every test named below is immutable once green:
a red test is turned green by fixing the generator, assay, or (only on a
confirmed soundness hole) kernel code — never by loosening or deleting the
test. The sole exception is a test later proven to encode incorrect behavior,
which requires stating why before it is changed.

For each obligation:
1. **Generator self-test** — for every variant of this obligation (§6), a
   `:well_typed`-labelled variant's rebuilt env + def actually
   `check_def == :ok`; an `:ill_typed`-labelled variant's `check_def` returns
   `{:error, _}`. This proves the label is correct by construction (guards
   against a vacuous-green generator).
2. **Assay test** — for at least one variant of each label present in this
   obligation, `Assays.Rewrite.run/1` returns `:ok` on the correctly-labelled
   challenge and `{:violation, _}` on a deliberately mislabelled one.
3. **Wiring** — `:rewrite_eq` round-trips through `Challenge` encode/decode;
   `Coverage.terms_of/1` returns every embedded `Term` for a `:rewrite_eq`
   challenge; both `Antigen.Runner`'s `assay_module/1` and
   `corpus_replay_test.exs`'s `@registry` resolve `"rewrite/eq"` to
   `Assays.Rewrite`; a banked seed replays statically via
   `rewrite_seed_test.exs` (§6).
4. **Coverage/seed** — one seed per correctly-handled variant lands in
   `seeds.sexp` (up to 12 candidates total across the four obligations — see
   §6's per-obligation variant count — banked only if the assay already
   returns `:ok` on them, per `indexed_seed_test.exs`'s pattern); any
   wrongly-accepted `:ill_typed` variant is banked as a `corpus.sexp` antibody
   instead (§5).

## 8. Invariants (carried from the Antigen design bible)

- Known-label by construction; **no** term generator, **no** external oracle.
- Pure verdicts (infection ⇒ red; no xfail/open); non-halting explorer;
  read-only replayer.
- `corpus.sexp` / `seeds.sexp` are append-only and **never pruned**.
- Kernel edits happen **only** if an obligation surfaces a confirmed soundness
  hole, and then only red-green with a banked antibody (indexed-case 4.1
  protocol). Absent a hole, this vertical adds **zero** TCB change.
- Generators/Assays must not import StreamData.

## 9. Net role for ②

This suite is the acceptance net for the ② case-refinement unifier. ② keeps
`rewrite` as the propositional transport; any ② change that regresses `Eq` /
`refl` / `rewrite` soundness turns this suite red. ② is scheduled only once this
vertical is green and banked.
