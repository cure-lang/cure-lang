# Confluence of the Cure Core reduction relation

**Status: specification confluence is termination-checked, with no bypasses.**
`Proof.Confluence.Conf.confluence` retains its original statement and the
`ClosedBody sig` hypothesis. It now factors through genuine one-step parallel
reduction, a strong diamond, and a structurally checked closure theorem.
The checked construction preserves the literal-arity constraints. A subsequent
coupled typing/reduction migration changes field substitution to last-field-first,
with all confluence laws rechecked. No new postulates, unchecked options or termination
pragmas are used. The proof uses the existing function-extensionality root
through the substitution algebra; no classical principle is needed.

This is confluence of the **formal reduction specification**, not executable
NbE correctness or full kernel soundness. Dependent telescope/result
instantiation, filtered/erased frames, η, erasure simulation and semantic
totality remain separate obligations. The checked theorem now supports
`Proof.ReductionConversion`'s full formal reduction-compatible model and
`Proof.SoundnessModel`'s inhabited closed-entry instance; neither establishes
executable conversion refinement.

## Why the old recursion was not a proof

The historical `Core.Parallel._⇉_` permits multi-step reductions in β/ζ body
premises and in branch bodies. The old function called `⇉-diamond` returned
multi-step joins. That conclusion is **local confluence**, not a strong
one-step diamond. Without termination or a stronger argument, local
confluence cannot simply be iterated to prove confluence.

The old `⇉-diamond-star` recursively consumed generated joining paths rather
than structurally smaller inputs. Its `TERMINATING` pragma suppressed a real
missing argument. That implementation and its unchecked mutual block have
been removed, not renamed, hidden behind a new assumption, or moved elsewhere.

Creating a redex by substitution does not require contracting that new redex
in the same parallel step. A congruence step can leave it intact. This is why
a properly defined one-step substitution lemma suffices.

## The checked construction

### `Core.StrictParallel`
`_⇛_` has only **single-step** recursive premises, including branch bodies.
It covers β, ζ, ordinary constructor ι, all four compact-literal ι rules, δ,
and every structural congruence. Literal branch arities are enforced by the
actual lookup shape; ordinary constructor ι retains its local length witness.
There is no `Star` premise in its constructors.

The two simulation directions are checked:
- `from-small-star` translates an original small-step path to `Star _⇛_`.
- `to-small` translates `Star _⇛_` back to the original small-step closure.

The inclusion for a SINGLE original small step is deliberately into the
strict-parallel **closure**, not one strict step: `ξ-case-brs` may carry an
arbitrarily long finite path in each branch. `from-small-branches` handles
these paths structurally, and `at-star` handles non-head spine updates.
No original reduction rule was weakened to obtain a simpler inclusion.

`embed` maps each strict step into the historical wide parallel relation,
using only `Core.Parallel`'s independently checked simulation. The dependency
does not involve the removed confluence implementation or any typing model.

### `Proof.StrictConfluence`
The `Laws sig closed` module assumes exactly that a body returned by
`Signature.body` is closed. It derives:
- `rename-step`, including binder and branch renaming;
- `substitute`, with a **single strict-step conclusion** for pointwise
  strict-step substitutions, including β/ζ, every ι rule and δ;
- `substitute-top` and `substitute-args`, including argument duplication;
- `lookup-step`, preserving first-match branch identity and arity;
- `diamond`, with **one strict step on both joining sides**;
- the pointwise term-list and branch-list strong diamonds.

All recursive calls in the diamond consume subderivations. Selected branch
bodies are transported along the already constructed branch-list join;
they are not passed back into an unchecked join recursion.

### `Core.Relation`
`Diamond R` requires one-step joins. `Closure.strip` recurses only on its
input path; `Closure.confluent` recurses only on the first input path.
Both are checked independently of the strict-parallel proof. The actual
proved `diamond` supplies the parameter: there is no new diamond oracle.

Combining these results with both simulation directions gives confluence of
`_⇝_`, including its migrated last-field-first substitution.
`normal-forms-unique` is a checked corollary.
`Proof.Confluence.Conf` exposes this implementation under the existing
`confluence` entry point and `ClosedBody` interface.
The useful wide-parallel entry points `⇉-diamond`, `⇉-diamond-star` and
`⇉-confluent` are retained as consequences of this checked theorem and
both old simulation inclusions, not as unchecked closure recursion.

## Regression witnesses

`Proof.ConfluenceExamples` checks:
- β versus simultaneous reduction of the body and argument;
- one-step substitution of a reducible argument into two occurrences;
- a two-step branch path whose first β contraction exposes a new redex,
  together with a refutation of compressing that path into one strict step;
- ordinary ι versus branch reduction and two distinct constructor fields,
  including a non-head field update;
- all four compact-literal peels and wrong-arity rejection in strict parallel;
- an inhabited, nonempty recursive δ table and its confluence instance;
- normal-form uniqueness using two nontrivial β/ζ paths.

`Proof.LiteralCases` retains valid/malformed arity checks for small-step and
wide parallel reduction, and its literal/branch peak now invokes the checked
confluence theorem. `Proof.SpineLifting` retains the independent non-head,
symbolic-alignment and simulation regressions.

The field-order example pins **the last field at zero** with distinct values.
`Proof.FieldOrderExamples` separately checks active heterogeneous field types,
ordinary/literal preservation, weakening and nested-lambda capture avoidance.
`Core.LocalFrame.fields-agree` proves agreement with the exact-arity,
fields-only forward-push frame; parameter filtering, missing erased slots
and full executable refinement remain separate. The recursive δ example
demonstrates that closedness is **not** termination.

## Scope and trust

`proof/scripts/check-hygiene.py` now allows **no** check-bypass pragmas in
any proof module. Its regression tests reject reintroducing the retired
confluence override as well as bypasses in either parallel module or the
closure machinery. `proof/check.sh` checks all modules and fails on warnings.
The named-postulate guard still permits exactly `funext` and `tree-decides`;
module hypotheses and implementation correspondence must be assessed
separately. Passing these guards alone is not a kernel soundness certificate.

The reduction is not deterministic, but confluence does not imply
normalization. The theorem applies even to the closed recursive δ table in
the examples. It assumes no `Final`, `Certified`, typing, conversion,
positivity, global coverage or literal-arity oracle.

## Why confluence does not rescue the old classical soundness input

The removed `never-reached→no-value` input is false for this reduction,
which reduces under binders. Let `Ω = (λx. x x) (λx. x x)`. Then `Ω ⇝ Ω`,
and `tm-lam g d Ω` is a canonical `Value` that steps to itself forever.
It also reaches itself, a value, in zero steps. Thus `Value` does not mean
"cannot step". Confluence does not change that counterexample.

`Proof.SoundnessConfluence` instead supplies `NormalForm`,
`never-reached-not-nf`, positive `DivergesNF`, and the repaired outcome
statement over the existing conditional soundness tree. Its `Reached`
disjunct still promises a value, not a normal-form value. No false postulate
is reinstated by this confluence repair, and the full executable soundness
model remains open.
