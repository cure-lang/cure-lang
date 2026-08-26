# Antigen conversion-at-depth — design (sub-project B of "deep injection")

**Parity ledger:** deep-injection follow-on. Sub-project A (deep-propagation, shipped)
buries an *intrinsically-ill-typed* fault under nested checked contexts and tests
error **propagation**. B tests the kernel's **conversion / NbE** checker directly:
a subterm whose expected type is a **redex that must be reduced** before the
conversion comparison — a path A structurally cannot reach (A's fault dies at its
own `infer` before any expected type is consulted). Neither subsumes the other.

**Two polarities (both in this spec — operator-approved scope):**
- **Reject** → mutation corpus (`:mutant_term`, assay `mutation/rejection`): a
  well-typed filler whose type is **non-convertible** to the reduced expected type
  → `infer` must **REJECT**. Catches over-acceptance (a conversion hole that
  compares same-headed indexed families without correctly reducing/recursing).
- **Accept** → typed-term corpus (`:typed_term`, the three existing `term/*`
  assays): a well-typed term that is well-typed **only after** non-trivial
  reduction → `infer`/`check` must **ACCEPT**. Catches false-rejection
  (under-reduction: a kernel that compares a redex syntactically and wrongly
  rejects a convertible term).

**One-liner:** place the discriminating difference in an **index of a same-headed
type former, behind a `plus` redex**, at a drawn depth; supply a filler that (reject)
mismatches or (accept) matches the reduced index. The kernel must reduce to decide;
a survivor (reject) or a false violation (accept) is a real conversion bug.

---

## 1. Scope

New module `Antigen.Generators.Conversion` emitting **both** challenge kinds:
- `conv_reject/1` → `:mutant_term` (reuses `Antigen.Assays.Mutation` **unchanged**).
- `conv_accept/1` → `:typed_term` (reuses `Antigen.Assays.Term` **unchanged**; one
  entry per existing `term/*` assay).

**No new assay module** either polarity. **No `Cure.Core.Term` seam** — carriers are
closed forms with the filler at a **binder-free** hole (the A design's decomposition
intro guessed a seam would be needed — "Needs a `Term` seam", the line preceding its
`## 1. Scope` — probing showed it is not). Reuses A's menu (`SigMenu` v1: Nat/Bd/Vec,
`plus`).

**Non-goals (deferred):** eta / functions-as-values conversion; conversion under
binders (all holes are binder-free here — see §4); global-def unfolding beyond
`plus`; using A's `deepen` wrapper stack around conversion carriers (B's depth is
its own index/reduction depth — see §3).

---

## 2. The bug class and why A misses it

A's mismatches are at the **head** (`Nat` vs `Vec`) or intrinsic — `infer` fails
before comparing any *computed* expected type. B's carriers have the **same** type-
former head on both sides (`Vec` vs `Vec`); the only difference is an **index**, and
that index is written as a **redex** (`plus (S^a Z) (S^b Z)`) that reduces to
`S^{a+b} Z`. So the kernel must:
1. **reduce** the redex in the expected type (NbE), then
2. **recurse** into the index of a same-headed `Vec` to compare `S^{a+b} Z` against
   the filler's index.

A bug in either step — under-reduction, WHNF-only head comparison that skips index
recursion, an off-by-one or fuel cap in structural index comparison at depth —
makes a **reject** carrier wrongly accepted or an **accept** carrier wrongly
rejected. A never exercises this (its indices are literal numerals, no redex).

Probed against the live kernel (`Kernel.infer`, `Context.empty`):

| carrier | shape | verdict |
|---|---|---|
| `conv_index` reject | `vcons (plus (S Z) Z) k vnil` | `REJECT :index_mismatch` |
| `conv_index` accept | `vcons (plus (S Z) Z) k (vsz:Vec(S Z))` | `ACCEPT` |
| `conv_index` control | same accept shape, `vnil:Vec Z` filler | `REJECT` (index is the discriminator) |
| `conv_motive` reject | `case T:Bd of T→vnil ∣ F→vnil`, motive `λ_:Bd.Vec(plus(S Z)Z)` | `REJECT :branch_type` |
| `conv_motive` accept | same, bodies `vsz:Vec(S Z)` | `ACCEPT` |

The **control** row is the load-bearing evidence: the accept carrier and the control
have the *identical outer shape* and differ only in the filler's index, yet one
accepts and one rejects — so the kernel is genuinely discriminating on the
**reduced** index, and the accept is not a vacuous "accepts anything".

---

## 3. Mechanism — redex-carried index at drawn depth

`plus (S^a Z) (S^b Z)` reduces to `S^{a+b} Z`. **`conv_depth = a + b`** — the S-depth
of the reduced discriminating index, drawn uniformly in `0..@max_depth` (≈6, bounded
by `plus` reduction cost, not construction cost). Deeper ⇒ more reduction steps and a
deeper structural index comparison.

**Draw order (uniformity, not independence).** `a` and `b` are each an operand of
`plus`, so it is tempting to draw them independently and let `conv_depth = a + b`
fall out — but two independent uniform draws over `0..k` sum to a **triangular**
distribution (thin at 0 and `2k`, peaked in the middle), not a uniform one. A's spec
(`2026-07-02-antigen-deep-propagation-design.md` §6) explicitly credits genuine
uniformity for keeping its `depth ≥ @depth_floor` test non-flaky at ordinary batch
sizes; B's §7.5 depends on the same property. So the draw must go the other way:
**draw `conv_depth` uniformly in `0..@max_depth` first, then draw `a` uniformly in
`0..conv_depth` and set `b = conv_depth - a`** — this makes `conv_depth` itself
uniform by construction, with `a`/`b` as a (non-uniform, and that's fine —
`fault.depth` is what the floor test reads) split of it.

**Carrier set (2 — one per distinct reduction site):**

| `carrier` | reduction site | reject filler | accept filler |
|---|---|---|---|
| `:conv_index` | `vcons` telescope: 3rd arg `xs : Vec n`, `n = plus…` | `xs` index ≠ `S^{a+b}` (use `S^{a+b+1}`) | `xs` index = `S^{a+b}` |
| `:conv_motive` | `case` motive application `(λ_:Bd. Vec (plus…)) T` (β + `plus`) | branch body index ≠ `S^{a+b}` | branch body index = `S^{a+b}` |

- **`:conv_index`** — `{:ctor, :vcons, [plus(Sᵃ,Sᵇ), Z, filler]}`. The 3rd-arg
  expected type `Vec (plus (Sᵃ Z)(Sᵇ Z))` reduces to `Vec (S^{a+b} Z)`; `filler` is a
  well-typed `Vec (S^{a+b} Z)` (accept) or `Vec (S^{a+b+1} Z)` (reject), built by the
  §4 vec-builder.
- **`:conv_motive`** — `{:case, {:ctor,:T,[]}, {:lam, Bd, Vec(plus(Sᵃ,Sᵇ))},
  [{:T,0,filler},{:F,0,filler}]}`. Both branches arity-0 (no binder); each body is
  checked against `Vec (S^{a+b} Z)` after β-reducing the motive and `plus`.

Both filler indices are **closed numerals**, so reject non-convertibility
(`S^{a+b}` ≠ `S^{a+b+1}`) and accept convertibility (`S^{a+b}` = `S^{a+b}`) are
**decided at construction in Elixir** (§4) — never by the kernel-under-test.

**Depth is B's own** (reduction/index depth), not A's wrapper nesting. A's
`deepen` composes Nat→Nat wrappers; conversion carriers are `Vec`/type-headed, so
A-reuse is a non-goal (§1). "Reuses A's depth machinery" is reinterpreted as an
*analogous* depth notion, documented here rather than shared code.

---

## 4. Construction guarantees (both polarities decidable without the kernel)

A tiny Elixir vec-builder makes a closed `Vec (S^k Z)` value: `vec_of(0) = vnil`
(`: Vec Z`), `vec_of(k) = vcons(S^{k-1}Z, Z, vec_of(k-1))` (`: Vec (S^k Z)` — the
result index of `vcons` is `S n` where the tail is `Vec n`). This is well-typed by
construction; no kernel call.

- **Reject** (`:mutant_term`, `:ill_typed`): filler `= vec_of(a+b+1) : Vec S^{a+b+1}`;
  expected `Vec S^{a+b}`. Distinct closed numerals `a+b` vs `a+b+1` ⇒ non-convertible,
  decided syntactically. Guaranteed ill-typed.
- **Accept** (`:typed_term`, `:well_typed`): filler `= vec_of(a+b) : Vec S^{a+b}`;
  expected `Vec S^{a+b}`. Equal closed numerals ⇒ convertible. Guaranteed well-typed.
  The claimed `payload.type` is the **reduced** whole-term type (`conv_index`:
  `Vec (S^{a+b+1} Z)`; `conv_motive`: `Vec (S^{a+b} Z)`). The reduction stress is in
  `infer`/`check` of the **term itself**: the term carries the `plus` redex in the
  `vcons` index (or motive body), and the kernel must reduce it to type-check the
  filler against the same-headed `Vec` family.

> **Where the reduction actually happens (probed against the live kernel; an
> earlier draft of this spec claimed `infer` returns an already-normalized `Value`
> and is wrong).** `infer` does **not** return an already-normalized `Value`.
> `Eval.eval({:global, name}, _env)` (`lib/cure/core/eval.ex`) unconditionally
> yields an opaque neutral `{:vneutral, {:nglobal, name}}` — it never δ-unfolds,
> certified or not. The `Value` `infer` hands back for a `plus`-indexed `Vec` still
> carries the raw, un-reduced neutral (confirmed by probe: the index slot is
> literally `vneutral: {:napp, {:napp, {:nglobal, :plus}, …}, …}`); δ-unfolding
> happens lazily, later, wherever `Normalise.whnf_value`/`Cure.Core.Conv` are
> actually invoked. So the reduction stress lands in **two** places, not one:
> (1) inside the initial `infer(ctx, term)` call itself, in `check_ctor_app_rec`'s
> (or `check_case_branches`'s) nested `check(...)` → `Conv.conv_values?` step — this
> is what actually decides the accept/reject verdict, and (2) **again**,
> independently, in the accept-dual assay's later `converges?`/`check(term,
> inferred)` steps (`Antigen.Assays.Term`), since the quoted `inferred_term` fed to
> `converges?` still contains the un-reduced `plus` redex and only converges with
> the reduced `payload.type` because `Conv.conv_within?` forces the δ-unfold at
> comparison time. Both sites genuinely exercise conversion-at-depth; neither is a
> no-op.

> **Binder-free holes (no `Term.shift`).** `:conv_index` places the filler in the
> `vcons` 3rd argument (not under a λ); `:conv_motive` uses **arity-0** `Bd` branches.
> No binder scopes any hole, so fillers keep their closed de Bruijn form and need no
> shifting. This is why no `Term` seam is required.

---

## 5. `infer` / assay totality (no crashes)

The reject assay contract is `:ok | {:violation, …}`; the accept assay likewise runs
`infer`/`check`/`nf`. All carriers are built from well-formed constructor / case /
lambda forms over the v1 menu — no bare pairs, no out-of-scope vars — so `infer`
stays total (graceful `{:error,_}` or `{:ok,_}`), verified by probing. The reject
construction-guarantee test (§7.1) asserts `{:error,_}` and the accept one asserts a
non-violation; a crash surfaces loudly as a test error, so totality is enforced.

---

## 6. Challenge model + health gate

**Reject** reuses `:mutant_term`; extend the `fault` record:
```
fault = %{
  kind: :conv_index | :conv_motive,   # NEW conversion carriers
  witness: :conv,                      # NEW witness tag
  expected_index: non_neg_integer,     # a+b   (reduced expected S-depth)
  actual_index:   non_neg_integer,     # a+b+1 (filler S-depth)
  reduction: :required,                # marks the redex-carried expected type
  depth: non_neg_integer,              # conv_depth = a+b (reuses A's :depth key)
  carrier: :conv_index | :conv_motive
}
```
`:depth` reuses A's field (so `Runner.mutation_metrics/1`'s `max_depth` already
covers conversion mutants). `wrap_path` stays `[]` for conversion mutants (no A
wrappers). The §7.2 witness meta-test extends the existing kernel-independent check:
for `:conv`, assert `actual_index != expected_index` (reject) — decidable, no kernel.

The full `:mutant_term` payload is `%{sig: :v1, ctx: ctx_types, type: goal, term:
mutant_term, fault: fault}` (same shape v1/A use — `Challenge.to_pieces/1`'s
`:mutant_term` clause requires a genuine `Cure.Core.Term.t()` in `type`). As with
v1/A, this `type` is documentation-only — never a proven property of the mutant,
unused by `Assays.Mutation.run/1` (§6.1 of the mutation-corpus spec) — but it must
still be *some* well-formed menu term. Set it to `Vec (S^{expected_index} Z)` (the
site's own reduced-expected-index type, i.e. the same value named `expected_index`
above), mirroring `Antigen.Generators.Mutation.goal_of/1`'s existing per-kind
convention rather than inventing a new one.

**Accept** reuses `:typed_term` with `payload = %{sig, ctx, type, term}` (the claimed
`type` is the reduced whole-term type, §4). No fault field on `:typed_term`; accept
provenance rides only in the term shape. Wire one `conv_accept` entry per `term/*`
assay into `mix antigen`'s `default_gen`.

**New atoms to intern** in `Challenge.@known_atoms` (both keys and values, per the
A/v1 `[:safe]` lesson): `:conv_index, :conv_motive, :conv, :expected_index,
:actual_index, :reduction, :required, :carrier`. (`:Bd, :T, :F, :vcons, :vnil,
:Vec, :Z, :S, :depth, :typed_term` already interned.)

**Health gate.** Reject conversion mutants fold into the existing mutation health
line — `reason_diversity` counts `:conv_index`/`:conv_motive` alongside the v1/A
kinds (floor unchanged), and `max_depth` already covers `conv_depth`. Add one
**conversion-specific** vacuity signal computed over the conversion subset (both
polarities), surfaced in the run summary and gated in the static meta-test:
- **`conv_carrier_diversity`** — distinct carriers (`:conv_index`,`:conv_motive`)
  exercised; floor `≥ 2`.
- **`conv_both_polarities`** — at least one reject **and** one accept conversion
  challenge generated; a corpus with only one polarity is vacuous *for B*.

**Identifying the reject-side conversion subset** is direct: `fault.carrier` (or
`fault.kind`) tags every `:conv_reject`-produced `:mutant_term` challenge, same as
any other fault kind. **Identifying the accept-side conversion subset is not** — by
design (above), a `conv_accept` challenge is an ordinary `:typed_term` with no fault
field, indistinguishable by payload shape from one `Antigen.Generators.Term.
typed_term/1` produced. `conv_carrier_diversity`/`conv_both_polarities` must
therefore recognize accept challenges **structurally**: a `:typed_term` challenge
counts as a `:conv_index` accept iff its `term` is a `{:ctor, :vcons, [n, _, _]}`
whose `n` is headed by `{:app, {:app, {:global, :plus}, _}, _}`; as a `:conv_motive`
accept iff its `term` is a `{:case, _, {:lam, _, {:data, :Vec, _, [idx]}}, _}` whose
motive-body index `idx` is headed the same way. This shape check is safe in v1:
the ordinary `Term` generator's own Vec goals are always drawn from
`SigMenu.goal_types()`/context-variable types, which carry only closed numeral
indices (never a `plus` application), so it cannot accidentally misclassify an
ordinary typed-term challenge as a conversion carrier.

Neither folds a survivor into a stamp (survivors/false-violations stay separately
surfaced infections, per the v1 §6.2 rule).

**Masking caveat.** Because `reason_diversity` and `max_depth` are shared, whole-
subset metrics, folding B's contributions into them means a *regression that
collapses v1/A's own kind- or depth-diversity generation* could go undetected: B's
independently-drawn `conv_index`/`conv_motive` kinds and `conv_depth` draws can, on
their own, push `reason_diversity` up to its floor of 5 (2 new kinds plus as few as
3 surviving v1/A kinds) or `max_depth` up to its floor of 4, even if v1/A's own
generation were badly broken. This risk did not exist when those floors were
calibrated (A's spec), since only v1/A fed the pool then. This is an accepted
tradeoff for v1 of B — the two new conversion-specific signals above catch B's own
vacuity, and a wholesale v1/A regression is expected to also surface via the
existing per-vertical tests (§7.1–7.4 of the v1/A specs) — but it is a known gap in
`reason_diversity`/`max_depth`'s value as an *isolated* v1/A signal once B lands,
not a claim that folding is harmless.

---

## 7. Testing (TDD; artifact is executable code)

Red-green per plan step. Behaviors:

1. **Reject construction guarantee** — each reject carrier × a range of `conv_depth`
   (0,1,mid,`@max_depth`) `infer`-REJECTS. Load-bearing; also enforces §5.
2. **Reject witness (kernel-independent)** — each `:conv` fault has
   `actual_index != expected_index` and `reduction == :required`; the expected-index
   position is a `plus` **redex** (`{:app,{:app,{:global,:plus},_},_}`), not a numeral
   — the property that makes it conversion-at-depth. No kernel call.
3. **Accept construction guarantee** — each accept carrier `infer`-ACCEPTS **and**
   passes all three `term/*` assays (`Assays.Term.run/1` returns `:ok`) — proving the
   kernel reduces to accept. Includes the **control**: the same accept shape with the
   reject filler is `infer`-REJECTED (accept is not vacuous).
4. **Reduction-required (redex present)** — each accept carrier's index position is a
   `plus` **redex** (`{:app,{:app,{:global,:plus},_},_}`), not a numeral. Together with
   §7.3's control (identical shape + reject filler ⇒ REJECT), this establishes that
   acceptance depends on the kernel reducing that redex — not on syntactic equality.
   No kernel call (structural assertion).
5. **Depth reached** — a sample hits `conv_depth ≥ @depth_floor` (e.g. 4);
   `fault.depth` equals the constructed index depth.
6. **Serialization round-trip** — a `:conv_*` mutant's atoms survive
   `binary_to_term [:safe]` via a **genuine out-of-source blob** red test (atoms only
   in opaque bytes — the in-source round-trip is false-green, per the A Task-1 /
   v1 key-atom lesson).
7. **Health + seeds** — `conv_carrier_diversity` / `conv_both_polarities` reported and
   gated; bank reject **and** accept conversion seeds; a static-replay meta-test
   enforces both polarities replay correctly (rejects reject, accepts accept) and the
   floors hold. Also asserts the accept-side structural detector (§6) is not a false
   positive: a batch of ordinary `Antigen.Generators.Term.typed_term/1` challenges
   (no `plus` anywhere in the term) contributes **zero** to `conv_carrier_diversity`/
   `conv_both_polarities`' accept count.
8. **Backward compatibility** — the v1/A mutation and Tier-B typed-term suites and
   banked seeds stay green; conversion challenges are additive.

---

## 8. Architecture & integration

- **Create** `lib/antigen/generators/conversion.ex` — `conv_reject/1`, `conv_accept/1`,
  the 2 carrier builders, `vec_of/1`, `carriers/0`, `max_depth/0`, `conv_depth` draw.
  Backend-free (no `StreamData` literal — grep-enforced).
- **Modify** `lib/antigen/challenge.ex` — `@known_atoms` += the 8 conversion atoms.
- **Modify** `lib/antigen/runner.ex` — `mutation_metrics/1` (or a sibling
  `conversion_metrics/1`) computes `conv_carrier_diversity` + `conv_both_polarities`;
  health line + static meta-test include them.
- **Modify** `lib/mix/tasks/antigen.ex` — `default_gen` += `conv_reject` (1 entry) and
  `conv_accept` × 3 (`term/infer_check`, `term/subject_reduction`, `term/normalization`).
- **Modify** `test/antigen/seeds.sexp` — bank reject + accept conversion seeds.
- **Create/Extend tests** — `test/antigen/generators/conversion_test.exs` (new),
  plus extensions to `challenge_test.exs`, the mutation health/meta tests, and a
  conversion static-replay meta-test.

Constraints (verbatim): construction-guaranteed typedness (both polarities decidable
from the edit); StreamData quarantine (generators/assays); ghost-authored commits
(`Made In Heaven`, no `Co-Authored-By`); one full build/test run at a time; the
accept assays use fueled `nf` via `Assays.Term.assay_fuel()`.

---

## 9. Relationship to A and to the deep-injection arc

A (propagation, shipped) + B (conversion, here) are the two halves of "deep
injection": A threads an intrinsic rejection up nested checked positions; B forces
the kernel to **compute** an expected type by reduction and compare it into a same-
headed indexed family. Together they cover both the "does the error get back up"
and the "is the comparison itself correct at depth" failure modes. With B landed,
the deep-injection follow-on named in the mutation-corpus report is fully closed.
