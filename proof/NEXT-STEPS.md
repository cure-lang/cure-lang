# From native specification safety to executable Cure soundness
Research baseline: `eae88c138184c79f28248d07490e92095ca2b057` on `soundness-proof-4`, 20 October 2026. This is a future implementation roadmap, not a claim that the obligations below are discharged. Its repository counterpart is `proof/NEXT-STEPS.md`. File references are relative to the repository root; line references identify this baseline.
## Objective and current boundary
The next objective is a checked connection between actual release-admitted Cure programs and the native safety theorem, followed by a connection to execution of emitted BEAM code. Adding more specification examples alone does not establish either connection.
`proof/Proof/DependentSoundness.agda:30` packages native signature validity, data-component inversion, reduction/conversion compatibility, global body finality and builtin shapes. Its consumers prove fixed-goal finite-trace safety, typed fuel exhaustion/reached outcomes, guarded outcome trees and fuel/tree agreement. `DependentSoundnessModel`, `DependentSoundnessExamples` and `DependentSoundnessControls` jointly exercise dependent constructors, computed indices, typed globals and unindexed Nat/Bounded layouts.
General native substitution, context conversion, progress and recursive preservation are complete for the existing specification. Preserve these results rather than restarting the dependent-typing migration. Legacy closed-entry developments remain historical or separately scoped; they are not the admission interface for arbitrary executable signatures.
The recorded checkpoint passed 109 Agda modules, the exact two-name postulate inventory, nine hygiene tests, strict Credo and formatting. The full default replay passed 6,779 tests with eight exclusions and 355 documentation snippets. These are checkpoint results, not proofs of implementation refinement.
## First boundary foundation — 21 October 2026
The first implementation checkpoint adds `Core.CanonicalSnapshot`,
`Core.AdmissionBoundary`, `Proof.AdmissionBoundaryExamples` and
`Proof.CanonicalSnapshotExamples`. Finite family/constructor lookup agreement
and visible ownership are derived; unique-key snapshots reject duplicate
family/constructor/global keys. A name-allowlisted scoped grammar derives
scope and finality for terms and nested branches, and records supported
caller/declaration/global payloads. A genuinely dependent Atom-only case and a
typed nonempty global table inhabit the boundary alongside native admission.
Eleven executable audit tests pin snapshot, subtyping, opacity, effect, payload
and frame contracts without changing kernel behavior.
This is a representation foundation, not completion of Stage 0 or Stage 1.
`Eligible` requires an existing native derivation; it does not derive one from
syntax or from `Kernel.check`. The grammar currently excludes Int nodes,
Float literals, all compact literals, effects and development leaves.
Metadata (including opaque families, quantities and certification), actual
Elixir snapshot extraction, atom/string identities and aliases, semantic
contexts/frames and the complete acceptance-rule ledger remain unproved.
No evaluator/NbE correspondence, finite signature validator or whole-kernel
admission theorem is claimed. The next increment should connect a canonical
executable snapshot representation to this formal view and make the remaining
rule/metadata exclusions checkable, before broadening the admitted fragment.
## Executable capture and replay continuation
After pushed checkpoint `aed3cd9a0`, `Cure.Core.ProofSnapshot` adds a
fail-closed, opt-in whole-registry capture and deterministic Agda data renderer.
It checks canonical ASCII identities, map/name/owner/order consistency,
declaration/result/term scope and exact field arities. Unsupported metadata,
opaque families, builtins, aliases, externs and erased/implicit layouts are
rejected; hidden raw bodies are inspected rather than silently discarded.
`Core.ExecutableSnapshot` checks conservative metadata/layout restrictions and
finite unique keys before constructing the formal canonical snapshot. Its
body projection preserves declared types and distinguishes certification
visibility from totality claims; unproved positivity/universe flags are false.
The generated `Fixtures.ExecutableSnapshot` is checked by Agda and regenerated
byte-for-byte in ExUnit. Its dependent family has ordinary/computed
constructors and a nonempty global table. Formal replay examples establish
lookup/ownership/body visibility and supported payloads, with malformed-input
controls. An acceptance-contract ledger is maintained in `proof/README.md`.
This establishes a concrete artifact bridge, NOT universal extraction
refinement, declaration validation, kernel admission or semantic totality.
The next increment should mechanise syntax/payload replay and finite
declaration admission, retaining a separate representation relation and the
unproved executable motive, conversion and environment contracts.
## Constructive syntax and payload replay continuation
After pushed checkpoint `0641f74d5`, `Core.AdmissionReplay` adds total
proof-producing decisions for arbitrary snapshot-relative term/branch/spine,
forward telescope, declaration/global payload and caller support.
`Core.ExecutableReplay` separately checks complete projected payloads and
ALL raw bodies, including uncertified bodies, using fixed metadata evidence.
No proof-irrelevance axiom identifies different snapshot certificates.
Visible global body support, closedness and finality, and declared global
type closedness are derived from checked payloads and actual finite lookup.
The generated fixture now consumes replay-derived support rather than manual
trees, and its reduction-conversion model uses derived body closedness.
Controls show that metadata/projected success alone can hide arbitrary
unsupported raw terms, whereas complete replay rejects them. Positive
nested/open cases and negative name/scope/arity checks exercise the decisions.
This decides the existing representation grammar, not native typing or every
stricter exporter policy. Explicit controls retain syntax success for
ill-typed applications, Type2, missing constructor arguments and uncovered
cases. The next obligation is finite native declaration/admission evidence
with a representation relation, followed by the existing motive,
conversion/environment and operational refinement obligations.
Trust-guard discovery now includes every Agda source directory under
`proof/`, including generated fixtures; the two-name axiom inventory and
empty bypass allowlist remain unchanged, with a new discovery regression.
## Finite native certificate continuation
After pushed checkpoint `1670a39da`, `Core.NativeCertificate` derives native
signature validity and fixed-declared-goal raw-body admission from finite
per-family/constructor and raw-global proof evidence. The certificate has no
validity, arbitrary lookup-typing or preservation callbacks. Actual lookup
membership and checked replay supply ownership and scoping, including hidden
definitions. Native proof objects remain required; this is not a type
inference algorithm or a theorem about executable checker acceptance.
The exact generated snapshot now has a native finite certificate covering
ordinary/computed constructors, all four raw definitions, typed motives and
full local coverage. `Proof.NativeCertificateSafety` composes it with replay
finality and the existing conversion/components model to exercise fixed-goal
trace, fuel and guarded-tree safety, including computed indices and global
delta unfolding. Negative controls prove that complete representation replay
can still accept inputs for which native certification is impossible.
The next obligation is sound production/replay of native derivation
certificates from serialized untrusted inputs, with explicit conversion and
representation witnesses; whole-kernel acceptance, NbE/motive/context
refinement and semantic positivity/totality remain separate. No native or
executable semantics or generated fixture bytes are changed here.
## Bounded data-only recipe replay continuation
After pushed checkpoint `3c975fba8`, `Core.SyntaxEquality` derives constructive
full structural Term equality through a checked internal code retraction;
it is not conversion or an external decoder.
`Core.NativeRecipe` adds proof-free raw recipe/packet data and a total
case-free replayer constructing native inference, kind, checking and
dependent-spine proofs. Assertions, variable bounds, actual lookup, spine
alignment and explicit universe cumulativity are checked, not trusted.
Global packets are bound to actual entry types/raw bodies; missing hidden
body recipes fail. Three exported globals now replay, as does the local
computed-index kind. A clearly MIXED finite certificate retains manual
family/declaration evidence and the existing manual dependent-case proof;
it composes with native validity/admission and a fixed-goal safe trace.
Mutation controls reject forged annotations, invalid spines/indices/names
and body omission. All case recipes fail, and native typing can exist at a
beta-converted goal even when this exact-syntax protocol returns failure.
There is no byte/JSON parser or Elixir producer yet, and no completeness or
whole-kernel refinement claim. Checked conversion evidence and dependent
case/declaration recipes are the next protocol extensions; only then can
complete automated replay of the exported native certificate be claimed.
## Checked non-reflexive conversion replay continuation
`Core.NativeRecipe.ConvRecipe` is proof-free data whose constructors mirror
exactly the `Conversion` record's laws (`≈-refl`, `≈-sym`, `≈-trans`, the
Π/application/data/constructor/effect congruences, the compact-literal
identifications) plus the premise-free β/ζ rules and a δ rule whose only
premise is the ACTUAL signature body lookup. There is no
asserted-conversion constructor, no reduct/normalization oracle and no η
rule, so a recipe names a derivation the replayer reconstructs.

`Derive` now takes an explicit reduction witness
`∀ {t u} → _⇝_ sig t u → Conversion._≈_ conv t u` and exposes a checked
`conversion` decision. β/ζ replay additionally requires the asserted target
to be the actual reduct; `c-trans` checks both halves against its untrusted
intermediate term; a wrong direction/target, grade or family mismatch, spine
arity mismatch, absent or non-visible body, and mismatched compact literals
all fail. `r-convert` is an inference rule that reports an ASSERTED target
only with a replayed conversion from the type its child actually synthesizes,
so exact syntax still separates that target from the requested goal and
`kind` rejects universe inflation.

The examples replay a beta-converted goal, a Π codomain redex (conversion
under a binder), a dependent computed result index, a ζ/β transitivity chain,
compact-literal identifications, a δ goal against a local alias signature and
kind discovery through a β-redex declared type. Controls retain the
exact-syntax failure for the same beta-converted goal and add the rejections
above plus both attempted η derivations. The mixed certificate is unchanged
and its dependent case proof is still manual.

This is a replayable conversion-derivation language for the EXISTING record,
not an NbE/readback/η refinement, normalization algorithm or decision
procedure, and it has no byte/JSON parser or Elixir producer. It is a
conservative extension of the same bounded protocol: `Nothing` still means
only that this protocol failed. Native typing, reduction, executable source,
generated fixture bytes and the postulate/bypass inventories are unchanged.

## Declaration recipe replay continuation
Family and constructor DECLARATION recipes now replay. A recipe supplies one
kind derivation per telescope entry (parameters, fields, result parameters,
result indices) and the result spines; the telescope itself is read from the
actual declaration and recipes are consumed in declaration order, so surplus or
missing recipes fail. `declare`/`declare-below` rebuild `Declared` entries
forwards, deciding scope and checking every field level against the family's
declared level; `constructor-declaration` additionally checks result scoping,
the `parameterSlots` uniformity equation and both result spines.
`family-table`/`constructors`/`definitions`/`certificate` assemble the finite
evidence in lockstep with the actual tables.

The examples replay the exported `Boundary#Packed` family, both its
constructors (including the computed result index) and the parameter-bearing
`Box` declaration, and the mixed certificate takes its whole family half from
those recipes instead of manual proof objects. Controls reject short field
vectors, a non-kind field derivation, surplus/missing constructor recipes, a
wrong result-index recipe, field universe overflow and a non-uniform
result-parameter vector.

## Dependent case replay and the complete exported certificate
`Core.NativeRecipe.r-case` carries the scrutinee recipe, both scrutinee
spines, the motive LEVEL (asserted), a kind recipe for `motiveType … level`, a
motive recipe and one `(field kind recipes, body recipe)` pair per branch in
branch order. From those the replayer derives the scrutinee's data shape
through a checked view, `WellFormed` of the ambient context (reconstructed for
the empty context only), the family lookup and both spines, `Motive` (scope
decided, the motive type's sort replayed, the motive inferred at that exact
curried contract), `Branches` (constructor lookup, owner-name check, branch
arity against the constructor's field count, a branch context rebuilt entry by
entry with re-scoped/re-kinded specialised field types, and the body checked
at its `branchGoal`) and `CaseCoverage` (replayed by enumerating registered
constructors of the selected family and matching branch arity; a builtin-registered
environment is outside this protocol).

Two obligations that blocked this step are now discharged interface changes
rather than open questions. `Branches`'s `owner ≡ family` premise needs
constructor/family name uniqueness, so `Derive` takes an `owner-visible`
hypothesis: the canonical snapshot discharges it via
`Snapshot.owner-visible`, and `singleton-owner` discharges it for a one-family
table. And because a branch body is checked at `branchGoal`, each branch
recipe carries a CONVERSION recipe for that curried motive application; the
fixture needs two β steps for the ordinary constructor and three for the
computed index, with the interior redex named and both halves of each
`c-trans` checked.

The examples now replay the whole exported artifact -- family, both
constructors, all four globals (including the dependent case, whose
synthesized type is proved EQUAL to the curried motive application at the
scrutinee's index and value) and every branch body/context/coverage -- and
assemble one `Evidence` from recipes, from which signature validity and the
fixed-goal safe trace follow. Controls prove that ONLY a case recipe can
replay a case, and reject missing/surplus branch recipes, a wrong motive
recipe/level/kind, short field recipes, an unchecked branch body, a wrong
branch arity, an unknown branch constructor, real missing coverage, a
non-data scrutinee, a case under a binder and a well-justified conversion
smuggled in as the assertion.

This remains replay for represented inputs. Extraction fidelity, an Elixir
producer, η/NbE refinement, a derived (rather than per-field-recipe) account
of specialised field kinds, semantic positivity/totality, typed erasure and
lowering are separate obligations; none is claimed here.

## Wire-format core continuation
`Core.Wire` fixes a serialised format and proves the decoder properties that do
not depend on Elixir. Trees flatten to a prefix-free INSTRUCTION stream and are
decoded by a stack machine whose recursion is structural on the stream: no
fuel, no termination override, and `run-instructions` proves decoding inverts
encoding. The stream renders to characters (unary naturals plus bracketing),
and `render-injective` proves a single instruction's rendering is unambiguous,
so the characters cannot be read two ways. `Proof.WireExamples` pins one
worked example's exact instruction stream and character string and records the
rejections (stray close, unclosed lists, trailing junk).

Name handling is a documented finding: a character-faithful `String`
round-trip is NOT available (the stdlib has only injectivity, and
`Data.String.Unsafe` supplies the missing direction as a postulate this
development refuses to use), so names are INTERNED as table indices —
matching the snapshot's registry-driven canonical keys. `index-of-sound`
proves a written index reads back as the name written, and an absent name
cannot be interned.

The format is now executable END TO END for trees and terms. Scanning is a
fold over the character list (one character per step, structural recursion, no
fuel and no termination side condition); `scan-encode` proves it inverts the
rendering of any instruction stream and `decode-encode` composes it with the
stack machine, so `decode (encode t) ≡ just t` for every tree. Payloads travel
as the EXISTING proved `Core.SyntaxEquality.Code` reflection (whose
`roundtrip` is already a theorem) with names interned as sound table indices,
and `code-fidelity`/`kids-fidelity`/`term-fidelity`/`decode-term-fidelity`
carry that through to `term-to-wire`/`wire-to-term`/`decode-term`. The examples
run an `atom-literals` term through characters → tree → term and record the
payload rejections (absent name, out-of-range index, bare atom, truncated
code).

The PRODUCER side now exists: `Cure.Core.ProofWire` reflects a Core term to the
`Code` tree, interns names against a supplied table and renders the characters
`Core.Wire` decodes, and `test/cure/core/proof_wire_test.exs` pins thirteen
producer vectors. Both sides share one hand-checked cross-language vector — for
`tm-atom_lit "a"` under `["" , "a"]` they emit `(1111111111111111111;1;;)`, which
`Proof.WireExamples.cross-characters` and the Elixir test assert independently.
Validation scope for that run: one focused file, 13 tests, 0 failures, with
`PATH` pointed at the standalone Elixir/Erlang installs; the default suite,
documentation checks and the stdlib gate were not run and are not reported as
passing.

Still open for this item, and none of it claimed:

1. All current recipe, packet, declaration and whole-certificate layers now
   have proved Agda character codecs, described below. Their Elixir producer
   and a generated complete cross-language certificate artifact remain open;
   the current executable producer covers terms only.
2. Snapshot representation fidelity: registry-to-`Snapshot` correspondence
   (name identity, declaration order, first-match lookup, owner-qualified keys,
   context correspondence) is not proved; `ProofSnapshot` remains an executable
   audit.
3. The kernel-acceptance-to-checked-evidence direction is open: replay proves
   represented inputs have native derivations, not that every `Kernel.check`
   acceptance yields a replayable certificate.

## Validated wire boundaries and conversion-recipe codec
The 129-module baseline passed proof/trust validation. Review additionally
found and corrected decoder acceptance through the defaulting internal
syntax retraction: term wire decoding now checks that the decoded candidate
re-encodes to the exact input reflected code. Successful-code preservation
and existing valid round-trips are proved; malformed levels, grades,
children, names/attributes and nested branch codes have rejection controls.
The bounded Elixir producer now returns structured errors for invalid
shapes, names/tables and grades, and rejects real Float payloads (not yet
represented faithfully) instead of silently erasing them. New executable
regressions are recorded but not run under the maintainer's validation policy.
Case coverage reconstruction is now family-local rather than requiring
unrelated constructors; actual membership, owner-name and arity obligations
remain checked, with positive/negative multi-family controls.
`Core.WireConversion` gives all current conversion recipes an exact tagged
node codec and character-level encoder/decoder with conditional fidelity
proofs. Its checked replay composition validates decoded recipes against
the actual source/target and signature, including a zeta/beta chain and
visible delta on the exported snapshot, while rejecting false conversion
claims, hidden bodies, malformed payloads and name-table mismatches.
At that checkpoint only the ConvRecipe layer was complete. The ordinary
Recipe, Packet and declaration codecs now follow below; their Elixir
producer remains open. This proves no universal
snapshot/executable/NbE or semantic certification correspondence.
## Complete recipe and certificate character codec continuation
`Core.WireRecipe` now serializes every current ordinary recipe, including
nested dependent cases and their field-kind/body branch pairs. Exact tags and
child counts, strict levels 0/1/2, ordered recipe/term vectors, canonical term
payloads and the existing conversion codec keep malformed inputs fail-closed.
Mutually structural recipe/vector/branch fidelity composes with the existing
character/tree theorem; successful encoding round-trips under the same name
table without new axioms, fuel or checking overrides.
`Core.WireCertificate` adds optional-body packets, constructor/family
declaration vectors and a proof-free whole-certificate envelope. Its generic
container/vector fidelity preserves grouping, order and absent/present bodies.
Character decoding returns DATA; `Replay.checked` then invokes the existing
native certificate replayer against the actual accepted source and payloads.
`Proof.WireCertificateExamples` sends the complete exported fixture's recipes
through characters and proves an explicit equation connecting the result to
the extracted native certificate. Validity, raw-body admission, eligibility
and the fixed-goal safe trace derive from that certificate. Generic transport
and opaque evidence avoid expensive concrete proof-value rewriting during
type checking; no decoder/replayer computation is bypassed.
Controls cover all ordinary recipe shapes, nested cases, parameter witnesses,
all levels, invalid names/payloads/arity/branch pairs, malformed optional bodies
and trailing characters. Well-formed envelopes still fail semantic replay for
missing/surplus or reordered declarations/globals/branches and hidden-body
omission. A mismatched name table can parse but fails source-bound family
typing: interning does not authenticate the supplied table.
The current Agda character codec layers are complete. Elixir recipe/certificate
production and generated artifacts, universal source/snapshot/context
representation, kernel acceptance, evaluator/NbE/eta, semantic certification,
typed erasure and BEAM correspondence remain separate open obligations.
Native rules and the generated snapshot bytes are unchanged.
## Current remaining work, in priority order
1. Extend the Elixir term producer to recipes/certificates with a generated
   complete cross-language fixture, then prove representation fidelity,
   snapshot/context correspondence and the connection between actual kernel
   acceptance and checked native evidence. The character scanner and all
   current tree/term/conversion/recipe/container character codecs already exist.
2. Refine executable evaluation, normalization, readback and conversion,
   including eta, certified delta, stuck-case policy and builtin computation.
   Resolve the stricter native versus executable motive contracts explicitly.
3. Extend the proved executable fragment to the remaining literal/payload,
   subtyping/effect, indexed-coverage and filtered/erased-frame contracts.
4. Prove semantic positivity and totality certification, including extraction,
   size-change descent and linkage to actual certified unfolding; finite
   certificate replay and body finality are not those semantic theorems.
5. Prove typed relevance/erasure simulation and BEAM lowering/execution
   correspondence, with explicit effect, exception, FFI and host trust bounds.
The detailed stages below expand these obligations. Waived Mix/ExUnit/docs
and stdlib/example verification is not an additional outstanding proof task.
## Governing proof contracts
- Target admission only under a related, validated signature, a well-formed caller context and a well-kinded expected type. Arbitrary success of the low-level `Kernel.check/3` API on caller-supplied semantic values is not sufficient. See `lib/cure/core/kernel.ex:645` and `proof/Core/DependentTyping.agda:254`.
- Keep implementation observations, exported evidence, formal algorithm acceptance and declarative derivations separate. Differential tests and certificates generated by unverified Elixir code are useful evidence, not automatically a theorem about that code.
- Specify a formal executable algorithm or small-step implementation model, prove its refinement, and identify the remaining Elixir/model correspondence boundary explicitly. Independently replayed proof certificates can establish typing of represented inputs without proving that every Elixir acceptance produces such a certificate. Do not conflate these two claims.
- Preserve rigid type-head separation and data/Π injectivity. Directed subtyping, sort cumulativity and definitional equality are different relations.
- Extend an inhabited joint model and negative controls whenever a theorem interface changes. No new callback may simply assume the preservation or admission result it is intended to prove.
- Distinguish mathematical totality, operational partial correctness, bounded observation and practical host resource limits. Finite δ fuel is not a bound on all evaluator work.
## Stage 0 — Fix the supported fragment and acceptance contracts
Priority: immediate. Produce an explicit inclusion/exclusion judgment over terms, declarations, contexts, goals and conversion/admission rules. Prefer a bounded first milestone that preserves current executable behavior; any semantic strengthening of the kernel needs a separate reviewed decision.
### Resolve the motive discrepancy
The executable case gate applies evaluated closures to fresh indices and a scrutinee and checks the resulting type value. Native `Motive` instead requires an ordinarily typed curried Π function: `proof/Core/DependentTyping.agda:190`. The accepted misannotated motive at `test/cure/core/dependent_branch_correspondence_test.exs:211` is rejected under ordinary application and native typing.
Initially require the stricter typed-motive fragment and record its exclusions. For broader coverage, either formalize the fresh-value motive contract with the necessary substitution/typing laws, or intentionally strengthen executable admission and assess compatibility. Do not assert that the stricter judgment already covers every accepted case.
### Resolve subtyping and opaque elimination
`lib/cure/core/kernel.ex:2406` accepts arbitrary inferred types at registered `Any`, and recursively subtypes List arguments. Native checking currently has conversion and sort cumulativity only. Exclude these extra subtyping paths from the first admission theorem; do not encode `Float <: Any` as definitional equality.
A later directed subtyping judgment must preserve elimination safety. In particular, model opaque families and the non-eliminability guard at `kernel.ex:304` before broadening `Any` typing: a zero-constructor opaque top type must not become an empty-case eliminator. Revisit checking-to-inference recovery and canonical-data statements rather than assuming their present formulations survive unchanged.
### Audit remaining rule differences
Audit every infer/check clause and its failure behavior, not just constructors. Include effects: executable `effect_bind` exposes a Π without enforcing the native rule's unrestricted continuation grade (`kernel.ex:224`; `DependentTyping.agda:150`). Its nondependence condition must also be justified rather than inferred from a comment. Exclude unsupported effect forms initially; broaden the formal rule only with checked transport/preservation changes.
Record holes, absurd terms, opaque declarations, primitives, parameter-bearing constructors and normalization-dependent acceptance. Specify the publication/release entry point and required invariants instead of treating every internal API as a release gate.
Acceptance: a documented rule-by-rule coverage ledger, positive genuinely dependent examples, and existing motive/subtyping/opaque/effect controls classified as supported, deliberately excluded or awaiting a semantic decision. Exclusions must be mechanically visible, not prose-only.
## Stage 1 — Adequate representations and signature snapshots
Priority: foundational; follows the scope decision. Primary files: `proof/Core/Syntax.agda`, `proof/Core/Signature.agda`, `proof/Core/LocalFrame.agda`, `lib/cure/core/term.ex`, `lib/cure/core/context.ex` and `lib/cure/core/inductive.ex`.
Define relations for terms, binder grades, names, declaration telescopes, global types/bodies, builtin identities, certification visibility and contexts. `Cure.Core.Env` is defined inside `inductive.ex`, not a separate `env.ex`.
Prove that actual visible family/constructor/global lookup agrees with formal lookup. Address canonical owner-qualified identities, allowed builtin aliases, ambiguous or hidden bare names, shadowing, duplicate entries and declaration order; Elixir maps cannot simply be serialized as a list and assumed to preserve first-match semantics. Relate one immutable snapshot throughout checking and evaluation.
Relate semantic environments to native syntactic contexts using substitutions. Distinguish indices from fresh-neutral levels and `Context.extend/2` from `extend_def/3`: lets bind actual values, not fresh neutrals (`context.ex:45`). Establish closure extension, lookup, weakening and local-prefix instantiation laws.
Repair or scope syntax discrepancies. Formal Float literals currently have no payload, while executable conversion distinguishes payloads; select an explicit payload representation and equality contract before claiming faithful Float conversion or arithmetic. Executable Int literals inhabit registered inductive Int, not the formal primitive Int type, and peel through `FromNat`/`NegativeSuccessor` (`kernel.ex:2401`; `eval.ex:304`). Either exclude Int initially or migrate typing, canonical forms, conversion and reduction together. The universe ceiling already agrees at Type0/1/2; no universe generalization is needed for this bridge.
Acceptance: finite nonempty related snapshots with dependent declarations and a typed global; proved lookup/frame laws; round-trip tests only where justified; rejection of swapped slots, owner collisions, malformed arities, forward references and unsupported payloads. The bridge must not collapse distinguishable runtime values.
## Stage 2 — Evaluator, readback and conversion refinement
Priority: central prerequisite for general admission. Separate signature-free `Eval.eval` from signature-aware `Normalise`, then relate both to the formal semantics. Primary files: `lib/cure/core/eval.ex:235`, `lib/cure/core/normalise.ex:244`, `lib/cure/core/quote.ex:57`, `lib/cure/core/conv.ex:99`, `proof/Proof/ReductionConversion.agda` and native inversion modules.
First prove closure application, β/ζ, exact-frame ordinary ι and neutral construction for the supported fragment. State partial correctness on successful evaluation or use an explicit machine with fuel covering all recursive work. Existing `Normalise` fuel counts δ expenditure; it cannot justify totality of arbitrary β/ι evaluation.
Formalize certified δ, cache/snapshot assumptions, stuck-case preserve/expose behavior and lazy unfolding. Globals stay neutral in `Eval`; δ belongs to `Normalise`. Show that each exposed result has the required operational correspondence without assuming every formal observation follows executable strategy.
Prove readback scoping and its relation to evaluation in open contexts, including fresh levels under lambdas and branches. Pass the signature when reconstructing parameter/index splits: `Quote.reify/3` and the signature-free default are not interchangeable for indexed data.
Inventory every positive `Conv` path: structural comparison, guarded lambda grades, η, constructor aliases/spine alignment, compact-literal equations and exposed stuck cases. The current common-reduct conversion explicitly does not validate function η. Supply a typed semantic/η conversion model that still proves the needed head and component laws; migrate native consumers and rebuild the joint model. Do not recover raw syntax from an arbitrary convertible type.
Model saturated builtin operation folding separately: `Normalise.builtin_op_fold` and `Eval.fold` compute operations absent from current formal reductions. Specify result typing, literal payload arithmetic, arities and zero-divisor neutral/stuck behavior before inclusion. Initially omit these operations if their primitive semantics are not yet proved.
Acceptance: a precise positive-conversion soundness theorem on related well-typed inputs, plus evaluator/readback simulation and positive/negative η, grade, literal, alias and stuck-case controls. Completeness/decidability is separate and must not be claimed from positive soundness.
## Stage 3 — Bounded algorithmic admission into native typing
Priority: first end-to-end kernel-facing milestone. Depends on Stages 0–2 for the chosen rules; a smaller conversion-free slice may land earlier with an explicitly narrower statement.
Define a formal algorithmic checker or replayable admission derivation with explicit successful-rule evidence. Prove mutual inference/checking soundness into `Core.DependentTyping`, including declaration checking, parameter-seeded spines, result vectors, typed motives, branch goals, local coverage and conversion/cumulativity.
Derive finite signature validity from actual admitted declarations and global typings. Do not accept an arbitrary `SignatureValid` record as the purported verifier's output without deriving its fields. Handle recursive references through an explicit checked declaration block; finite lookup evidence is not a proof of positivity or semantic termination.
Relate export/replay inputs to the immutable executable snapshot. A certificate replay theorem establishes native typing for represented inputs; universal correspondence with the Elixir checker remains a separate theorem or explicit trusted boundary until proved. Keep the distinction in public status text.
Compose derived source typing and finality with `DependentSoundness` at one original goal. Start with ordinary dependent cases and typed globals, not only closed primitive expressions. Keep executable observation correspondence separate from native fuel/tree safety.
Acceptance: a non-vacuous admission-to-native-safety theorem for the named fragment, with complete assumptions and a concrete joint instance. Wrong-owner, ill-kinded, nonuniform, bad-result, missing-branch and misannotated-motive inputs must fail independently. No claim of whole-kernel admission until all excluded acceptance paths are covered.
## Stage 4 — Indexed literals, filtered frames and refined coverage
Priority: extend the first milestone toward actual standard-library programs. These features share frame and motive dependencies and should be integrated deliberately.
### Indexed Bounded, Char and Int
Executable Bounded inference synthesizes the minimum bound `k+1`; checking permits a concrete larger bound `n > k`. Char additionally enforces the nominal character range below `0x110000` (`kernel.ex:104`, `kernel.ex:455`). Current native Bounded is intentionally unindexed. Model widening as a directed checking rule, not equality of distinct indices.
Carry the actual erased index witnesses through `First`/`Next` peeling (`eval.ex:334`). For Int, include both signs and the compact Nat field of each constructor. Extend raw reduction, literal expansion/conversion, layouts, canonical forms, progress, preservation and examples together. Reprove any confluence or component-injectivity dependencies affected by new rules.
### Filtered constructor frames
`Eval.reduce_branch_body/4` removes parameter prefixes and restores missing erased slots with inert holes (`eval.ex:241`). `Inductive.align_ctor_spines` also aligns implicit/prefix-trimmed spines (`inductive.ex:1148`). The existing theorem covers exact fields-only arity, not these cases.
Define a declaration/source/runtime frame relation using grades and relevance evidence. Prove erased-slot non-observation, last-field-at-zero and ambient-slot preservation for parameter-bearing, reduced and full spines. Internal inert placeholders must not be confused with release-admitted source holes. Derive fresh opening/closing and ι safety through this relation; do not assume all runtime values carry full declaration arity.
### Index-based impossible branch omission
The executable can omit impossible constructors, specialize known scrutinees and skip impossible branch bodies (`kernel.ex:1459`, `kernel.ex:1635`). Native coverage currently requires every constructor of the family.
Replace this only with evidence that every reachable constructor has a checked branch or is refuted by index incompatibility. Formalize coherent branch substitutions and goal specialization. The executable unifier verdict and `validate_branch_substitution` filter are not automatically proofs of substitution typing or impossibility; uncertain cases must remain conservative.
Acceptance: one joint indexed-family model and kernel-checked source/intermediate/reduct fixtures at a fixed goal, including open parameters, erased witnesses, lambda capture and omitted impossible branches. Negative controls cover bad bounds, relevant use of erased fields, wrong refinement, unknown/foreign constructors and real missing coverage.
## Stage 5 — Typed erasure and BEAM execution
Priority: after a source fragment and its runtime frames are stable. Primary files: `proof/Proof/Erase.agda`, `lib/cure/elab/relevance.ex`, `lib/cure/elab/erase.ex:21` and `lib/cure/elab/emit.ex:420`.
The current formal erasure theorem is structural idempotence with administrative let collapse. `eraseTerm` does not call quantity-based spine filtering. Do not present it as a theorem for full `Erase.erase`.
Formalize relevance/usage acceptance and signature-dependent erasure, including erased arguments, partial/over-application, parameter prefixes, collapsible families, convoy branches and runtime binder maps. Prove a typed source/runtime simulation with administrative steps or stuttering and an appropriate observation relation. Raw erasure–δ commutation is a known false target. Treat preservation of divergence separately; finite simulation alone is insufficient.
The release firewall already exists: `Validator.release_config/0` and Emit's pre-erasure hole rejection cover erased positions (`validator.ex:97`; `emit.ex:420`). Prove and test those existing boundaries; do not replace them with checks after erasure has hidden source holes. Distinguish validator configuration used by `check_def` from strict release eligibility.
Define runtime semantics for the emitted subset and prove lowering preserves frames, literals, calls and case selection. Delimit exceptions, inert source effects versus runtime effects, extern/FFI operations, OTP concurrency and trusted BEAM behavior. Pure source safety does not automatically prove those external semantics.
Acceptance: checked source-to-erased simulation plus an explicit lowering theorem for a named emitted subset; independent runtime regressions for dependent cases, grades and layouts. Publish a trust ledger for unmodeled BEAM/FFI/effect behavior.
## Independent track — Positivity, totality and certified unfolding
Run this after the shared signature/operational contracts stabilize; it is not a reason to delay finite-trace specification safety.
For positivity, relate `Inductive.positive?` to a semantic strict-positivity condition and check recursive/mutual block validity, field universes and uniform parameters. Reuse existing formal positivity machinery where applicable, but prove correspondence with the executable checker rather than trusting metadata booleans.
For totality, retain the already implemented finite replay: `lib/cure/core/scc_certificate.ex:16` checks graph/component evidence, and `lib/cure/core/totality_certificate.ex:16` recomputes base/composed matrices, rejects cyclic derivations, checks saturation and bad idempotents. These verifiers are not missing.
The missing obligations are sound call/size extraction, completeness of the relevant call graph, semantic descent for matrix entries, the size-change termination principle and connection to actual certification and δ eligibility (`kernel.ex:846`; Env certification in `inductive.ex:715`). Prove cache validity and recertification under signature/body changes. Builtin operations need their own specified semantics and termination justification.
`BodiesFinal` only excludes development leaves in global bodies. The recursive native control deliberately satisfies it while diverging. Do not rename finality into a termination theorem. Termination of certified globals also does not by itself prove totality of all host normalization routines.
Acceptance: positive recursive examples and negative non-decreasing, incomplete-graph, stale-cache and malformed-certificate controls; a theorem connecting verified semantic descent to termination of the certified fragment. State any additional normalization assumptions explicitly.
## Dependencies and delivery policy
The critical path is scope contracts → adequate representation/context relations → evaluator/readback/conversion → bounded admission → composition with native safety. Indexed coverage and erased frames then expand that boundary; typed erasure precedes compiler/runtime composition. Positivity and totality are independent semantic tracks with shared snapshot/evaluator prerequisites.
The immediate implementation unit should be Stage 0 plus the smallest Stage 1 snapshot/lookup/frame bridge, with executable mismatch controls retained. Land that reviewed boundary before attempting a wholesale conversion rewrite. Subsequent units should each include one theorem, an inhabited instance, rejection controls and updated scope documentation.
The original roadmap preparation implemented none of the proposed source/proof changes; the first implemented boundary foundation is recorded above. Future parallel work is appropriate only after ownership and theorem interfaces stabilize; tightly coupled changes to syntax, conversion and native inversion should be integrated before downstream proof work proceeds.
## Validation and non-regression requirements
**Maintainer directive — 21 October 2026:** Mix/ExUnit test verification,
documentation-snippet checks and stdlib/example verification are not required
for this soundness-proof effort or its checkpoint commits. Do not
automatically run `mix test`, ExUnit suites, documentation checks or the
`mix check` stdlib/example gate unless subsequently requested by the
maintainer. Do not list the omission of these gates as outstanding proof
work, and do not describe waived or cancelled runs as passing. This directive
supersedes earlier local instructions to run those suites for every proof
checkpoint. Existing historical results remain historical.
For proof changes, run `./proof/check.sh`, `./proof/scripts/check-postulates.sh`, `python3 proof/scripts/test_hygiene.py` and `python3 proof/scripts/check-hygiene.py`. Register every new module in the runner. Use Agda 2.8.x and the configured standard library; retain the heap cap and explicit diagnostics for expensive checks.
The global postulate inventory remains exactly `funext` and legacy `tree-decides`; constructive native safety must not depend on LPO. No holes, unsolved metas, termination/positivity bypasses, raw-reflection oracle, global coverage oracle or callback assuming the target theorem may be introduced.
Run applicable static analysis (`mix credo --strict`), formatting and
`git diff --check`; run `mix format` as the last code-validation step before
an Elixir-project commit. Preserve default exclusions, warnings-as-errors
and performance thresholds. This local proof-validation policy does not
disable or alter repository CI, existing test configuration or release
requirements, and does not waive any mathematical soundness obligation.
Record the actual scope and exit status of checks performed.
The existing `.github/workflows/proof.yml` gates main pushes and main-target pull requests. Any broader branch-trigger policy is a separate CI decision, not a prerequisite silently claimed to be present.
Maintain a claim ledger in `proof/README.md` and the soundness documentation: theorem scope, related executable entry points, proved correspondence, exclusions and residual trust. Historical status prose should not be read as current certification.
## Definition of completion
A bounded milestone is complete when related validated release inputs in its mechanically named fragment yield native typing, executable observations refine the modeled semantics, and native fixed-goal safety applies through derived—not assumed—bridge evidence.
Whole-pipeline soundness additionally requires all release-admitted rules and layouts, certified-normalization obligations, typed erasure and lowering, and an explicit external/runtime trust boundary. The current specification theorem is a completed foundation for that work, not a substitute for it.
