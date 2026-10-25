# Remaining Cure soundness work
## 1. Status, baseline and purpose
Prepared 25 October 2026 against `da9d01dd0460bd72bfc1ba0c305f209eb2013bd6` (`Prove ambient residual checking and coherent caller closure`). This is a proposed implementation plan, not a claim that its milestones have been executed.
The recorded baseline has 223 checked Agda modules, the exact `funext`/legacy `tree-decides` inventory, ten passing hygiene regressions, reproducible generated artifacts and strict Credo coverage of 1,455 source files. These are historical checkpoint results, not measurements of percentage completion or universal executable soundness.
This document is the forward execution plan. `proof/NEXT-STEPS.md:1` retains the chronological developments and broader contract discussion; `proof/README.md:1` remains the proved-claim ledger; `docs/SOUNDNESS.md:1` must ultimately state the exact public theorem and trust boundary. Update these consistently as milestones land, rather than treating earlier checkpoint limitations as current requirements to reimplement.
Implementation began after this plan was written; see the per-milestone progress notes (currently `## 6`, M1). Production behavior changes still require separate review, and no native or executable semantics have been changed.
## 2. Preserve the completed foundation
Do not restart native substitution, context conversion, dependent preservation or progress. Reuse the following established layers:
* Native fixed-goal trace, fuel and guarded-tree safety: `proof/Proof/DependentSoundness.agda:30`, with its explicit specification evidence and fuel/tree agreement.
* Source-bound finite signature and certificate replay: `proof/Core/CheckedAdmission.agda:1`, `proof/Core/WireAdmission.agda:1` and the existing term/recipe/snapshot codecs. All raw bodies, including hidden bodies, remain checked.
* Positive recursive closure, constructor, exact-case, canonical data-spine and residual-case evaluation/readback: `proof/Core/ClosureEval.agda:1`, `proof/Core/ClosureQuote.agda:1` and `proof/Proof/ClosureQuotation.agda:1`.
* Residual normality modulo administrative native steps, separate from strict no-step normality: `proof/Core/ResidualNormal.agda:1` and `proof/Proof/ResidualNormal.agda:1`.
* Positive residual conversion, closed and ambient checking: `proof/Proof/ResidualConversion.agda:1`, `proof/Core/ResidualAdmission.agda:1` and `proof/Core/AmbientResidualAdmission.agda:87`.
* Fresh scope-bounded identity and coherent caller closure: `proof/Proof/FreshEnvironment.agda:1`, `proof/Core/ResidualCallerAdmission.agda:61` and `proof/Proof/DependentCoherence.agda:123`.
The remaining gap is not a shortage of examples. It is the connection between these models and actual release behavior, coverage of excluded behaviors, semantic certification and compiler/runtime refinement.
## 3. Target claims and non-negotiable invariants
### Claim ladder
* **G1: bounded checked Core path.** A mechanically delimited source/signature/caller fragment obtains native admission at its original goal through checked replay, with the implementation relationship and every remaining trusted adapter explicitly stated.
* **G2: actual kernel refinement.** Every successful release-admission path within the advertised coverage has related native evidence; actual evaluation and positive conversion satisfy the stated refinement. No excluded acceptance branch is silently included.
* **G3: compiler/runtime refinement.** Accepted relevant programs lower through typed erasure and the selected Erlang/BEAM boundary with the stated observable behavior and external assumptions.
G1 can be useful before G2/G3. A conditional G1 theorem with an openly named unverified adapter must not be labelled universal G2 refinement.
### Invariants
1. Keep the exact postulate inventory. Add no holes, unsolved metas, unsafe String imports, termination/positivity overrides or callbacks assuming the theorem being proved. Audit module parameters as well as declared axioms. New constructive safety results must not depend on legacy LPO.
2. Preserve the original expected goal. Normalize to establish conversion; never silently replace the caller's specification with the returned normal form.
3. Keep subject inference and BOTH inferred/expected kind guards before exact equality or normalization. Cumulativity and directed subtyping are not definitional equality.
4. Compare open types under related fresh slots. A particular closing assignment equating two variables is not a proof of open equality. Defined local values require a separate justified semantic-context relation.
5. Distinct readbacks are not non-conversion proofs. Exhaustion is not divergence, and positive-result simulation alone does not exclude implementation failure before returning a result.
6. Preserve the strict APIs and normal grammar. Residual cases can self-step administratively; syntactic endpoint equality alone also occurs in computational loops.
7. Use one related immutable signature across declaration replay, closure capture, readback, comparison, certification and lowering. Layout success, certification flags, hashes and body finality are not typing or termination proofs.
8. Preserve older artifact bytes unless a reviewed semantic/schema change requires migration. Never relabel raw operational observations as natively admitted programs.
## 4. Execution order and decision gates
Recommended main line: M0 boundary contract, then M1 argument checking, M2 representation fidelity, M3 semantic contexts, M4 execution correspondence and M6 bounded release integration. M5 normalization/conversion work extends the coverage of M4/M6 rather than blocking an explicitly no-delta/no-eta first theorem.
M7 language coverage expands the kernel claim in separately gated increments. M8 relevance/layout laws support both richer operational frames and M9 typed erasure; M9 precedes M10 lowering. M11 semantic certification can develop independently once representation and operational contracts are stable. M12 composes only completed, compatible claims.
Do not spend an indefinite sequence of increments adding examples while postponing M2/M4. Complete the first three M1 deliveries, then explicitly review the implementation-correspondence bottleneck.
A lead integrator owns shared theorem interfaces and final integration. No child-agent execution is proposed by this plan. Mathematical tracks may become independent after their interfaces are frozen; any later delegated implementation needs separate ownership and integration arrangements.
## 5. M0 — Freeze the bounded release contract and audit the trust boundary
**Priority/dependencies:** first; use the existing baseline, not a new proof-foundation rewrite.
**Existing anchors:** `lib/cure/core/kernel.ex:654`, `lib/cure/core/validator.ex:129`, `lib/cure/core/validator.ex:133`, `lib/cure/elab/emit.ex:420`, `lib/cure/project/proof/verifier.ex:26` and `lib/cure/compiler/artifacts.ex:1`.
**Work:**
* Enumerate publication, certification, serialization and emission entry paths. Record which enforce typing, relevance, finality and signature validity, and distinguish development `check_def_config` from strict release configuration.
* Turn the supported fragment into an explicit versioned profile: syntax, literal payloads, grades/plicities, names, signatures, caller construction, allowed conversions, coverage and external operations. Reuse existing support decisions; identify uncovered rules rather than imposing duplicate informal allowlists.
* Inventory semantic discrepancies: fresh-value versus ordinarily typed motives, directed `Any`/List subtyping, opaque elimination, effect continuation requirements, aliases, compact/indexed literals and erased/implicit frames.
* Audit the reachability and meaning of package `.cureproof` verification. Its equality-token checks and permissive SMT/totality branches are not `CheckedAdmission` evidence. Determine which consumers rely on them; keep them outside the claimed TCB or replace relevant acceptance with source-bound fail-closed semantic replay before relying on it.
* Likewise distinguish BEAM digest/provenance verification from semantic compiler correctness. Define the exact program/signature/context identity that a checked receipt must bind.
**Acceptance gate:** every release acceptance path is classified as proved, mechanically excluded or an explicit trusted/semantic decision. Existing permissive receipts, warnings or artifact hashes cannot close a typing obligation. Cover both types and bodies before information is erased.
**Decision:** preserve current semantics by default. Any stricter motive, effect, subtyping or release-gate policy requires a separate compatibility review; this plan does not authorize changing those rules implicitly.
## 6. M1 — Normalization-guided dependent argument checking
**Priority/dependencies:** next bounded proof increment after M0 fixes the profile. Existing caller arguments still pass the exact recipe spine in `proof/Core/ResidualCallerAdmission.agda:61` and `proof/Core/NativeRecipe.agda:644`.
**Work:**
* First prove a prefix-instantiation lemma. From a checked forward declaration telescope and a successfully typed prefix of actual arguments, derive scope and native kinding of the next declared type after the prefix substitution.
* Reuse `Coherent`, `instantiate-coherent` and general transport from `proof/Proof/DependentCoherence.agda:49`, `proof/Proof/DependentCoherence.agda:123` and `proof/Proof/DependentGeneralTransport.agda:1`. Do not substitute later arguments into earlier declaration types or infer coherence from list lengths.
* Specify data-only per-argument evidence for synthesis and inferred-kind discovery. Prefer deriving the expected kind from the checked declaration/prefix; if additional recipes are necessary, document and check them rather than accepting native proofs or asserted equality fields.
* At each argument, retain support, inference and both type-kind obligations, then exact equality or bounded residual comparison. Produce an actual native `Spine`, retaining the original instantiated expected type for every element.
* Compose the result into a separate opt-in caller path and preserve the current exact checker. Maintain declaration order externally and last-actual-at-zero internally.
* Extend codecs only after the record contract is settled. Preserve old formats or introduce an explicit versioned path; never reinterpret old fields silently.
**Acceptance gate:** a genuinely dependent caller whose later argument needs beta/zeta/residual conversion succeeds without an outer supplied conversion derivation. The resulting native spine reuses the existing coherent closing theorem and original-goal safety.
**Controls:** zero-budget exact success; nonexact exhaustion; malformed/surplus recipes; bad inferred/expected kinds; wrong dependent actuals; reversed arguments; escaped scopes; and coincident closing values that must not prove open equality.
**First three delivery units:** prefix kind/coherence lemma; positive argument comparator returning native spine evidence; caller/packet integration with independently replayed examples. Proposed new module names are to be chosen during implementation, not treated as existing files.

### M1 progress — 25 October 2026
`proof/Core/ArgumentAdmission.agda` implements the first three delivery units, and `proof/Proof/ArgumentAdmissionExamples.agda` instantiates them on the existing verified dependent caller.

**Delivery 1 (prefix kind/coherence) — DONE.** `CheckedPrefix` is the per-argument evidence: for each consumed argument, its finality and a native checking derivation at the type obtained by substituting the PRECEDING arguments only. `prefix-step` shows one declared entry plus one checked actual preserves native `Coherent`; `prefix-coherent` lifts that to an arbitrary telescope and yields the complete coherent frame; `prefix-kind` derives the instantiated next declared type's kind from the checked declaration entry. Later arguments are never substituted into earlier declaration types, and coherence is never inferred from list lengths.

**Delivery 2 (positive argument comparator) — DONE, with a scope correction.** `compare-argument` consumes the argument's REPLAYED inference derivation (never a checking derivation, never a conversion witness) and returns `ArgumentResult`. The EXACT branch needs zero fuel and no model evaluation. The NON-EXACT branch requires a bounded residual comparison — but of the argument's INFERRED TYPE against the declared expected type, not of the argument against its own specification. That is the only shape the existing `ResidualConversion`/`AmbientResidualAdmission` theorems support, and it is also the honest one: the argument is never re-normalized into the specification it is being checked against. `compared-converts` reuses the general comparison-to-conversion theorem under fresh caller slots.

**Delivery 3 (caller integration) — PARTIAL.** `prefix-spine` turns the comparator's evidence back into the EXISTING exact `Spine` judgment, and `instantiate` returns that spine together with the coherent complete frame, so the existing closing-substitution and original-goal safety theorems apply unchanged. The examples recover `CheckedPrefix` from the replayed spine plus supported-argument evidence, derive the complete frame by the new theorem (not by copying the caller path), and prove that frame equals `CallerAdmission`'s own substitution.

**Acceptance gate — CLOSED.** `Proof.ArgumentAdmissionExamples` now exhibits a genuinely dependent argument whose instantiated declared type is the beta-redex `(λ A → A) Atom` while the argument itself infers `Atom`. The two are proved distinct (`beta-distinct`), the declared type is proved well-kinded, and the comparator accepts the argument at the ORIGINAL declared type through the residual branch at fuel 4 — the first budget that reduces the redex. `beta-normalized` proves by computation that the acceptance really went through the comparison rather than exact syntax. Two controls pin the boundary: fuel 3 EXHAUSTS (inconclusive, not a false accept or reject), and the same convertible pair is REFUSED with the residual switch off. The converted argument then pushes into the coherent frame via `prefix-step`, so delivery 1 composes with a converted argument.

**Still open for M1.** (a) There is no separate opt-in CALLER driver that consumes `ArgumentResult`s end-to-end and emits a wire packet; the comparator composes at the spine/frame level, and the existing `CallerAdmission`/`ResidualCallerAdmission` drivers still use the exact spine. A `walk`-style driver was attempted and abandoned: threading the accumulated locals through the dependent `Step` index fought Agda's unification without converging, and a half-finished driver is worse than an honest gap. (b) No new codec was added, which is deliberate: the record contract is still settling, and old formats are untouched.
## 7. M2 — Universal representation and source identity
**Priority/dependencies:** begin early, using M0's profile; do not wait for every language feature.
**Existing anchors:** `lib/cure/core/proof_wire.ex:85`, `lib/cure/core/proof_recipe.ex:42`, `lib/cure/core/proof_snapshot.ex:32`, `lib/cure/core/proof_snapshot_wire.ex:22`, `proof/Core/ExecutableSnapshot.agda:101` and `proof/Core/WireAdmission.agda:1`.
**Work:**
* Separate host data, canonical formal data and native terms. Define representation relations for every admitted tuple/list/map payload, including grades, plicities, raw hidden bodies, certification visibility and constructor ownership/order.
* Relate actual registry access and name resolution to formal finite lookup. Handle canonical qualified identities, atom/string distinctions, aliases, duplicate keys, shadowing, missing names and stored constructor order explicitly.
* Prove encode/decode and extraction results for ALL related inputs in the selected profile, not merely generated vectors. Existing universal Agda codecs are reusable; universal correctness of the actual Elixir producer is still a distinct obligation.
* Choose an auditable implementation-proof mechanism: a semantics/translation of the relevant host subset with a proved connection to actual code, or a reviewed adapter that makes independently decoded canonical data authoritative. An additional Agda model alone does not verify the Elixir function it resembles.
* If the first deliverable keeps an adapter in the TCB, state its exact obligations in G1. Do not hide universal correspondence in a module parameter and call G2 complete.
* Bind program, expected goal, registry, certificate and later artifact identity to the same immutable data. Cached digests need a separately stated collision/integrity assumption or exact-content validation; a digest is not semantic evidence.
**Acceptance gate:** quantified fidelity for the named boundary, plus an exact statement of any remaining adapter/compiler trust. Source mutation, changed name table, omitted hidden body, reordered declaration and stale certificate controls must fail at the correct boundary.
## 8. M3 — Closure-valued semantic contexts and defined locals
**Priority/dependencies:** after the representation contracts are fixed; reuse the syntactic caller theorem rather than weakening fresh comparison.
**Existing anchors:** `lib/cure/core/context.ex:40`, `lib/cure/core/context.ex:58`, `proof/Core/FlatContext.agda:1`, `proof/Core/FlatContextTyping.agda:1`, `proof/Core/ClosureScope.agda:1` and `proof/Proof/ClosureWeakening.agda:1`.
**Work:**
* Generalize the flat context model to admitted closure, constructor, canonical data and residual-case values. Relate type store, value environment, grades, size and signature to one native context and typed substitution.
* Prove lookup, extension and weakening for both opaque bindings and actual defined values. Check every environment image at its substituted native type; scope alone is insufficient.
* Retain captured motive/branch environments and all captured raw-body scope. Defined values must survive later opaque extensions without being replaced by invented fresh neutrals.
* Establish actual `Context.extend`, `extend_def`, `env` and lookup correspondence through the implementation relationship from M2. Keep arbitrary caller-supplied semantic values outside the theorem unless this relation holds.
**Acceptance gate:** dependent defined locals containing functions, data and residual cases compose with open checking and coherent closure; later binders preserve original values and the original goal.
**Controls:** scoped-but-untyped environment images, wrong captured environments, unequal store lengths, changed signatures, escaped levels and replacement of defined slots by neutrals. The existing closing-coincidence rejection remains valid for abstract caller checking.
## 9. M4 — Universal positive execution and failure correspondence
**Priority/dependencies:** M2 representation; M3 for the broader context claim. Start with the already modeled beta/zeta/exact-iota/residual/data slice.
**Existing anchors:** `lib/cure/core/eval.ex:140`, `lib/cure/core/eval.ex:213`, `lib/cure/core/quote.ex:40`, `proof/Proof/ClosureEvaluation.agda:1` and `proof/Proof/ClosureQuotation.agda:1`.
**Work:**
* Define related actual values/closures independently of their fully quoted normal forms. Preserve evaluation order, caller capture, field reversal, binder levels and signature-aware parameter/index recovery.
* Prove every finite successful implementation evaluation/application/readback in the admitted profile has the corresponding positive model evidence or a direct native simulation. If model fuel is used, derive an adequate height from the finite derivation; do not equate it to the executable delta counter.
* Also relate finite execution prefixes and failure outcomes. Show that unbound lookup, non-function application, invalid constructor dispatch and missing coverage cannot occur on the related admitted pure fragment; result-only simulation would otherwise be vacuous for an implementation that always fails.
* Map scope/layout/budget/protocol failures without relabelling them as divergence or actual host exceptions. Treat host resource exhaustion as an explicit external bound.
* Compose checked admission with the general native path at the original goal for arbitrary related programs, signatures and callers in the profile.
**Acceptance gate:** quantified implementation/model execution and readback theorems, plus failure safety for the named inputs. Fixed fixtures remain regressions, not substitutes for the quantified connection. No unconditional normalization or evaluator-totality theorem is required for this partial-correctness milestone.
## 10. M5 — Certified unfolding, stuck cases and typed positive conversion
### M5a — Operational delta and normalization policy
**Dependencies:** M2/M4 and a precise snapshot/certification visibility contract.
**Anchors:** `lib/cure/core/normalise.ex:26`, `lib/cure/core/normalise.ex:82`, `lib/cure/core/conv.ex:49` and `lib/cure/core/inductive.ex:721`.
* Model certified/reducible/none modes, allowlists, weak-head versus full normalization, folded stuck cases, explicit exposure and reapplication.
* Derive each unfold from the actual visible body and native body typing; preserve closedness and the unchanged signature. Include the pre-delta identical-neutral shortcut and expose-on-demand comparison.
* Account for the actual fuel-spending sites, nested dynamic budget save/restore and exhaustion. This service does not bound all beta/iota work; do not advertise total-work bounds without a different proved resource model.
* Keep positive operational unfolding separate from M11's semantic termination theorem. A bounded sound unfold need not establish totality of the global or normalizer.
**Gate/controls:** general native simulation of successful policy steps; opaque/uncertified bodies stay folded; changed-body/cache cases, nested budgets, stuck/exposed equivalence and recursive self-loops preserve their exact classifications.
### M5b — Typed eta and structural conversion
**Dependencies:** stable context/value relations and an explicit shared expected type for eligible comparisons.
**Anchors:** `lib/cure/core/conv.ex:98`, `lib/cure/core/conv.ex:232`, `proof/Core/Typing.agda:1`, `proof/Core/TypeHeads.agda:1` and `proof/Proof/ReductionConversion.agda:1`.
* Inventory each actual positive conversion clause, including lambda grade equality, domain handling, motives instantiated without an extra binder, fresh branch opening and constructor alignment.
* Design a typed semantic/eta relation or another proved extension; first demonstrate rigid type-head separation and data/Pi component laws in a joint nonempty model.
* If the current unindexed conversion interface cannot express the needed premises, propose its migration explicitly and review it before changing typing, transport, inversion or soundness consumers.
* Prove positive actual conversion soundness for related well-typed inputs. Preserve the current strict and residual common-reduct paths as subcases where applicable.
**Gate/controls:** typed lambda/neutral eta, open dependent functions, motive/branch capture, wrong grades, distinct universes and raw comparisons without a common expected type. No completeness, rejection soundness or universal decidability follows from this positive theorem.
## 11. M6 — A bounded release-admission theorem, not only replay
**Priority/dependencies:** M0/M2/M4; include M1/M3/M5 only to the extent advertised by the chosen profile.
**Anchors:** `lib/cure/core/kernel.ex:654`, `proof/Core/CheckedAdmission.agda:1`, `proof/Core/NativeRecipe.agda:1`, `lib/cure/project/proof.ex:113` and `lib/cure/elab/emit.ex:94`.
**Work:**
* Enumerate and model the actual inference, checking, kinding, declaration and branch acceptance paths for the profile. Do not generalize from arbitrary calls to low-level `Kernel.check` with unrelated semantic goals.
* Produce replayable recipes from successful paths where useful. Recipe search can be untrusted because replay derives native evidence, but source identity and completeness of the covered acceptance paths still need proofs.
* State separate directions: replay acceptance implies native admission; actual covered kernel acceptance supplies related accepted evidence; related execution preserves the admitted goal. Do not collapse these into one unsupported implication.
* Review a bounded opt-in release driver that fails closed if source binding, full declaration/raw-body checking, caller validation, kinding or replay fails. Production integration is a separately approved behavior change, not a documentation-only assumption.
* Keep permissive package receipts distinct from these source-bound certificates and from artifact integrity metadata.
**Acceptance gate G1:** a useful restricted release path with exact coverage and an honest TCB. **Acceptance gate toward G2:** universal actual-acceptance correspondence for that coverage, not merely a driver that happens to emit a finite corpus of passing certificates.
Stop and fix the underlying theorem or mechanically exclude the branch if the needed evidence cannot be derived. Never insert a checker-success-to-typing callback as the missing bridge.
## 12. M7 — Expand kernel coverage in independently reviewed slices
### M7a — Names, literals and builtin computation
**Dependencies:** representation contracts, operational refinement and the appropriate native typing/reduction laws.
**Anchors:** `lib/cure/core/eval.ex:255`, `lib/cure/core/inductive.ex:1148`, `lib/cure/core/normalise.ex:424` and `proof/Core/LiteralExpansion.agda:1`.
* Relate canonical and builtin alias identities without permitting foreign-constructor matches. Prove full/shortened constructor alignment from declarations, not a length heuristic alone.
* Extend Nat, indexed Bounded, Char and both Int signs with faithful payloads, declared indices and typed widening. Do not identify unequal bounds by conversion; the current formal unindexed builtin fragment is not executable indexed Bounded.
* Resolve Float payload representation before inclusion. Specify supported numeric/equality behavior and excluded host payloads explicitly; never erase a payload to prove fidelity.
* Model saturated builtin folds, partial/overapplication and stuck behavior, including division/remainder by zero and registered-operation identity. Prove result typing and representation for each operation class.
**Gate/controls:** related typed literals/constructors and their eliminations, nominal character bounds, aliases, malformed indices, zero divisors, wrong arity and shadowed non-builtin globals. Rebuild the native joint model after each typing/reduction extension.
### M7b — Motives, opaque families, directed subtyping and effects
**Anchors:** `lib/cure/core/kernel.ex:225`, `lib/cure/core/kernel.ex:299`, `lib/cure/core/kernel.ex:1331`, `lib/cure/core/kernel.ex:2407` and `proof/Core/DependentTyping.agda:1`.
* Resolve the fresh-value versus ordinary typed-motive contract by proof or an approved semantic change. Preserve the stricter profile until the broader theorem exists.
* Add directed subtyping separately from equality, with transport and elimination safety. Model opaque metadata before admitting `Any`; constructor-less opaque types must not inherit empty-inductive ex-falso elimination.
* Address effect continuation grades and nondependence. Keep inert Core effect syntax distinct from runtime effects and FFI behavior.
**Gate/controls:** every newly included actual acceptance branch has native rules, preservation/progress support and implementation correspondence; misannotated motives, opaque empty cases, invalid subtyping elimination and dependent/incorrect-grade effects remain explicit controls.
### M7c — Indexed branch refinement and coverage
**Anchors:** `lib/cure/core/kernel.ex:1458`, `lib/cure/core/kernel.ex:1518` and the existing dependent branch/transport proofs.
* Model solved, impossible and undecided index constraints separately. Derive coherent refinement substitutions, context specialization and motive/goal specialization.
* Replace exhaustive native coverage only with evidence that every reachable constructor has a checked branch or a justified impossibility proof. Known-scrutinee specialization needs its own soundness case.
* Prove why omitted or unchecked unreachable bodies are irrelevant; do not trust an elaborator/unifier verdict or accept undecided omission.
**Gate/controls:** genuine GADT/dependent examples, computed indices and known constructors, with negative foreign-name, false-impossibility, missing-real-branch and ill-typed substitution cases. Reprove affected progress, preservation and conversion components.
## 13. M8 — Typed relevance and declaration/source/runtime frames
**Dependencies:** stable metadata and the selected typing profile; coordinate with M7 coverage. This supplies prerequisites for richer operational frames and erasure.
**Anchors:** `lib/cure/elab/relevance.ex:118`, `lib/cure/core/eval.ex:241`, `lib/cure/core/inductive.ex:1148` and `proof/Core/Grade.agda:1`.
**Work:**
* Formalize relevance/usage evidence for erased, linear, affine and unrestricted binders, including sequence, closure capture and branch alternatives. Runtime presence is `Grade.present?`, not equality to unrestricted.
* Relate full declaration fields, source spellings, parameter prefixes, implicit/explicit arguments and runtime survivors. Plicity is not quantity: a missing implicit argument is not automatically an erased argument.
* Prove omitted slots are computationally irrelevant, or reconstruct the required typed relevant witnesses. Only then justify erased placeholder padding and prefix filtering.
* Generalize opening/closing, last-field-at-zero and caller-tail preservation through this relation, retaining exact-arity all-present behavior as an embedding.
**Gate/controls:** parameter-bearing and indexed families with lambdas capturing outer variables; relevant implicit fields; linear/affine preservation; malformed shortened spines; relevant uses of erased slots; and unsupported placeholders. No runtime-relevant occurrence of a release hole may be justified by calling it an internal erased slot.
## 14. M9 — Typed erasure simulation
**Dependencies:** M8 and a stable relevant execution/observation contract; M4 for implementation correspondence.
**Anchors:** `proof/Proof/Erase.agda:195`, `lib/cure/elab/erase.ex:21`, `lib/cure/elab/erase.ex:65` and `lib/cure/elab/emit.ex:420`.
**Work:**
* Keep existing structural idempotence as a limited lemma. Define an erased runtime language, environment/layout relation and signature-indexed typed erasure judgment for the selected fragment.
* Prove simulation using the M8 frame relation and an appropriate administrative/stuttering account. Address signature-dependent filtering and partial/overapplication before optimizations.
* Add collapsible families, convoy discharge, type-level elimination and placeholders one at a time with preservation of runtime observations.
* Do not target false raw erasure-delta commutation. Distinguish value preservation from divergence/termination preservation: dropping eagerly evaluated erased computations may change termination without further hypotheses. Choose relevant-source semantics or prove the needed totality/stuttering conditions explicitly.
* Prove that release validation examines the required pre-erasure types/bodies and that forbidden leaves cannot be hidden by erasure.
**Acceptance gate:** general typed source/runtime simulation for a named fragment, with no dangling runtime variables and independently related actual `Erase.erase` outputs. Idempotence and successful examples alone do not establish this milestone.
## 15. M10 — Erlang lowering and the BEAM trust boundary
**Dependencies:** M9 erased language and observation relation; M2 identity/provenance contracts.
**Anchors:** `lib/cure/elab/emit.ex:94`, `lib/cure/elab/emit.ex:148`, `lib/cure/compiler/beam_writer.ex:26` and `lib/cure/compiler/artifacts.ex:1`.
**Work:**
* Define semantics for the emitted Erlang abstract-form subset: literals, atoms/tagged constructors, closures, application/calls, let sharing and case patterns.
* Prove lowering preserves variable environments, survivor arities, constructor tags, selected branches, local/remote identities and evaluated results. Relate type-level definition omission and optimized paths to M9 evidence.
* Relate actual generated forms and runtime-reference closure validation to the modeled lowering. Digest/export/provenance checks bind artifacts but do not prove this semantics.
* State the `:compile.forms`, loader and OTP VM boundary explicitly. Initially prove to abstract Erlang forms and make the remaining compiler/VM assumption conditional; an unconditional BEAM claim requires a further validated or proved connection.
* Handle externs, primitive operations, exceptions, effects, concurrency and host resources through explicit contracts or mechanically enforced exclusions. Preserve failure diagnostics without calling all host exceptions kernel stuck states.
**Gate/controls:** a compositional observation theorem for the selected emitted subset, closed runtime references, correct module/arity routing and no erased-slot leaks. Tampered artifacts, wrong owners, missing dependencies and stale provenance are distinct integrity controls, not semantic proof substitutes.
## 16. M11 — Semantic positivity and totality certification
**Dependencies:** stable representation/signature and call/execution semantics. These are independent semantic tracks; do not block existing finite-trace safety on a nonexistent general termination theorem.
### Positivity
* Relate `lib/cure/core/inductive.ex:1256` to a stated semantic strict-positivity condition for the chosen inductive fragment, including parameters, universes, nested families and mutual cycles.
* Check the through-constructor and instantiated-parameter cases; opaque/unknown polarity must remain conservative unless a sound variance certificate is available.
* Derive the semantic property rather than interpreting metadata booleans as evidence. Separate logical/termination guarantees from the already established operational safety specification.
### Totality and certified unfolding
* Reuse the EXISTING finite verifiers in `lib/cure/core/scc_certificate.ex:16` and `lib/cure/core/totality_certificate.ex:16`; do not plan to implement SCC/closure verification from scratch.
* Prove sound direct-call extraction and edge completeness, semantic meaning of size-change matrix entries, finite Base/Compose replay and saturation correctness, and the semantic descent principle needed for the selected data/measures.
* Connect verified components to actual certification and delta eligibility. Include dependency/body/checker-version cache identity, invalidation, atomic component updates and sealed/external boundaries.
* A primitive marked total by policy requires a justified primitive contract. Body finality and termination of selected globals do not establish termination of every host normalization routine.
**Gate/controls:** positive recursion and mutual recursion, nondecreasing cycles, omitted calls, forged matrices, stale bodies/dependencies, cyclic derivations and incorrect primitive certification. Derive the promised semantic theorem without adding a postulated size-change principle.
## 17. M12 — Compose, review and publish only the proved claim
**Dependencies:** the milestones required by the selected G1/G2/G3 scope, with compatible signatures, contexts, semantics and observations.
* Compose actual source identity and release admission, native safety, execution/conversion refinement, relevance/erasure and lowering. Keep original goals and observable results connected across every representation change.
* Publish explicit theorem statements, exclusions, TCB/compiler/VM/FFI assumptions and dependency audits. Distinguish operational safety, termination, logical consistency, positive conversion soundness and completeness.
* Check all release entry paths against the coverage ledger; no deprecated receipt verifier or unverified fallback may bypass the advertised path.
* Review changes to typing/conversion/coverage/relevance as mathematical interface migrations, not merely passing-code changes. Rebuild nonempty joint models and negative controls.
**Completion:** G1 requires a useful bounded, source-bound checked path; G2 additionally requires universal correspondence and coverage for the advertised kernel behavior; G3 additionally requires the stated erasure/lowering/runtime composition. Never remove an exclusion based only on corpus growth.
## 18. Validation and checkpoint delivery
For implementation checkpoints, retain all existing checks and their scope:
* Focused Agda: `agda -i proof -l standard-library +RTS -M24G -RTS proof/Proof/RelevantModule.agda`, substituting the actual module path. Keep expensive probes bounded and complete; do not introduce holes to diagnose elaboration.
* Complete proof runner: `./proof/check.sh`; register every new module exactly once and compare registration with all source directories.
* Trust and hygiene: `./proof/scripts/check-postulates.sh`, `python3 proof/scripts/test_hygiene.py` and `python3 proof/scripts/check-hygiene.py`.
* Syntax: `bash -n proof/check.sh proof/scripts/check-postulates.sh`.
* Standalone artifacts: `elixir -pa _build/test/lib/cure/ebin proof/scripts/generate-wire-certificate.exs --check`, using the configured compiled support dependencies. Preserve earlier bytes or explicitly review/version the migration.
* Static analysis: `mix credo --strict`; if parser files are skipped, rerun unchanged until complete coverage is obtained. Do not weaken exclusions, thresholds or warnings.
* Formatting and whitespace: run `mix format` as the last code-validation step before a requested commit, then `git --no-pager diff --check`. Include untracked new files in review.
The maintainer deliberately waives automatic Mix/ExUnit, documentation-snippet and stdlib/example verification for this effort. Do not run `mix test`, `mix check`, docs or stdlib/example suites without a new request; recording regression sources is not claiming those suites passed. This does not waive mathematical acceptance gates or change repository CI/release requirements.
Each checkpoint should contain one general result, a nonempty composed instance, rejection/counterexample controls, literal implementation observations where relevant, and updated claim/exclusion documentation. Fixtures supplement universal theorems; they do not replace them.
Do not commit automatically. When a commit is requested, validate, format last, use a comprehensive message with `Co-Authored-By: Warp <agent@warp.dev>`, then use an ordinary push. Do not change native/executable semantics, trust inventory or old artifacts merely to make a proof easier.
For this PLAN-only delivery, validate file presence, reference paths, consistency and whitespace. Do not report the historical 223-module checkpoint as a fresh run of implementation validation.
## 19. Risks, effort calibration and stop conditions
Taking completed soundness work as one effort unit, the previous rough estimates remain planning ranges: another 0.5–1 unit for a defensible restricted milestone, 1–3 for broad actual-kernel coverage, and 2–5 for the full planned certification/erasure/BEAM scope. These are inclusive scopes, not additive budgets, elapsed-time commitments or module-count percentages.
Re-estimate after M1, the M2 implementation-proof decision, the M5b eta prototype and the first M9 simulation. Representation fidelity, typed eta, semantic descent and divergence-sensitive erasure are the principal redesign risks; they can exceed these ranges.
Stop and obtain a reviewed scope/interface decision when a step requires a new axiom, changes accepted source behavior, replaces a stated exclusion with an unproved assumption, conflates fresh variables with definitions, weakens rigid-head/component laws, relies on permissive receipts, or claims executable correctness from model tests alone.
The preferred immediate sequence is M0's coverage/TCB audit, M1's prefix-kind lemma and normalized spine, then an explicit M2/M4 correspondence deliverable. This keeps the next increments useful without mistaking additional modeled features for completion of the implementation proof.
