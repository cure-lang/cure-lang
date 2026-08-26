# First-Class Holes (Holes-as-Stuck-Neutrals) — Design

**Date:** 2026-07-18
**Branch:** `implicit-goal-solving`
**Layer:** K (kernel/TCB) + E (elaborator) — HARD-STOP-and-review
**Status:** design approved (direction: "we're doing C"; TCB-size commitment explicitly relaxed in favour of user-friendliness)

## Goal

Make a hole (`?`) a **first-class term that survives elaboration and
normalization**: a hole-bearing program type-checks and normalizes (getting
*stuck* on the hole) instead of crashing the evaluator. This is the foundation
for typed-hole-driven assisted development (Agda/Idris/Hazel interaction
points): every incomplete program has a type and a dynamic meaning, so the
compiler can report a hole's goal and, later, help fill it.

This spec covers **Slice 1** only: the kernel substrate + safe identity.
Reporting goal-type/context (Slice 2) and interactive refine/case-split/auto
actions (Slice 3) are follow-on specs that build on this.

## Motivation / the crash it removes

`Cure.Core.Eval.eval` has no `{:hole,_}` clause. A body-position hole (the whole
function body) never reaches `eval`, so it survives today. But an
**argument-position** hole — e.g. `refine(multiply(refined_value(l),
refined_value(r)), ?)` — is embedded in an enclosing application that the
elaborator normalizes to type-check; `eval` then hits the hole and raises a
`FunctionClauseError`. Under the auto-lemma proof-search work, an undischarged
proof obligation must degrade to a *live hole*, not a crash or a
position-dependent hard error. Slice 1 makes that degradation sound and
uniform.

## Design: a hole is a neutral

Cure's NbE already models "stuck" computations as **neutrals**
(`{:nvar,level}`, `{:nglobal,name}`, `{:napp,n,v}`, `{:ncase,…}`) wrapped in
`{:vneutral, neutral}`. A hole is exactly a stuck computation, so it becomes a
**new neutral constructor** `{:nhole, id}` and reuses every existing pathway.

### Core (K) changes — additive clauses only

- **`eval.ex`**: `def eval({:hole, id}, _env), do: {:vneutral, {:nhole, id}}`.
  Application of a neutral already extends its spine
  (`apply({:vneutral,n}, v) → {:vneutral, {:napp, n, v}}`), so a hole applied to
  arguments accumulates them rather than crashing.
- **`conv.ex`**: two clauses, identity comparison —
  `conv_neutral?({:nhole, a}, {:nhole, b}, _, _) → a == b` and the analogous
  `same_neutral_no_delta?({:nhole, a}, {:nhole, b}, _, _) → a == b`. Every
  existing catch-all (`conv_neutral?(_,_,_,_) → false`, the `conv_struct?`
  fallback) already yields `false` for hole-vs-anything-else.
- **`quote.ex`**: `defp reify_neutral({:nhole, id}, _depth, _sig), do: {:hole, id}`.
  Read-back is the inverse of `eval`; a spined hole reads back as `{:hole,id}`
  applied to its (reified) arguments via the existing `{:napp,…}` arm.
- **`normalise.ex`**: **no change required.** `unfold_head`/`spine` see a
  `{:nhole,id}` head that is neither a global nor an eliminator, so it is
  `:stuck` and `whnf_value` returns the value unchanged; `nf_neutral`'s
  catch-all (`nf_neutral(neutral, …) → neutral`) preserves it. (A confirming
  antibody still exercises this path.)
- **`kernel.ex`**: **no change.** `check(_ctx, {:hole,_}, _expected) → :ok`
  already accepts a hole at any goal type; `infer(_ctx, {:hole,name})` stays
  `{:error, {:hole_in_inference_position, name}}` (a hole has no type to
  synthesize — refinement supplies one from the checking side).
- **`term.ex`**: `term?({:hole, name})` already requires `is_binary(name)`; ids
  are strings, so this is unchanged. `shift`/`subst` already treat `{:hole,_}`
  as an inert leaf (correct: a hole captures nothing and is copied verbatim,
  which is what makes its id stable under substitution).

### The soundness pivot: unique, deterministic hole identity

**Problem.** Today every hole lowers to `{:hole, ""}` (see
`declarations.ex:1045`, `Keyword.get(meta, :name, "")`). This is harmless only
because holes never reach `conv?`. Once holes are neutrals flowing through
conversion, two holes with the same id are **definitionally equal**, so
`refl : ?a = ?b` type-checks — and later filling `?a := 0`, `?b := 1` would have
"proven" `0 = 1`. Unsound.

**Fix.** Each source `?` lowers to a hole with a **unique, deterministic** id:

- Unnamed `?` → `"<module>.<def>:<line>:<col>"` (the lexer stamps line/col on
  every hole token — `Token.new(:hole, name, state.line, start_col)`; the
  elaborator knows the enclosing module + def name).
- Named `?foo` → `"<module>.<def>#foo"` (still qualified, so the same surface
  name in two defs is two holes; repeating `?foo` *within one def* is
  deliberately the *same* hole — a shared unknown, like an Idris named hole).

Determinism (a positional/name-derived id, **no** gensym counter) is required so
Antigen and the differential oracle replay identically run-to-run.

**Consequence.** Distinct ids ⇒ non-convertible ⇒ each hole behaves as **its own
fresh axiom of its checked type** — precisely Agda/Idris's one-postulate-per-hole
model. A hole is convertible only to *itself* (reflexivity preserved), never to
a different hole and never to any non-hole term.

### Codegen still blocked

`validator.ex`'s `no_hole: :reject` (K3) is **unchanged**. A hole type-checks and
normalizes, but a hole-bearing definition can never be emitted, run, or trusted
downstream. *Type-checks ≠ ships.* The `{:hole, "__pending__"}` def-body
placeholder (`declarations.ex:414`, forward-reference sentinel) is orthogonal:
it is swapped out before use and never user-visible; ids for user holes must not
collide with it (the qualified scheme guarantees this — `__pending__` is not a
`module.def:line:col`/`module.def#name` string).

## Antigen antibody (TCB gate)

A new antibody proves the change equates no distinct normal forms and
terminates:

1. **Distinct holes are not convertible** — two holes with different ids at the
   same type: `conv?` is `false`.
2. **Hole vs non-hole is not convertible** — a hole and any concrete term of the
   same type: `conv?` is `false`.
3. **Reflexivity preserved** — a hole is convertible to itself (same id):
   `conv?` is `true`.
4. **Stuck, not crashing** — normalizing the crash-repro
   `refine(multiply(refined_value(l), refined_value(r)), ?)` (and a bare applied
   hole `?h x y`) terminates and yields a stuck neutral, no raise.

Plus the standard TCB gate: full Antigen suite + full `mix test`, once, alone.
The direction (holes-as-stuck-neutrals) is aligned with Agda/Idris/Hazel, so it
falls under the "aligned with a real language" TCB approval; the gate still runs
in full.

## Elaborator (E) wiring — proof-search fit

`Cure.Elab.ProofSearch.resolve/3` is unchanged (it already only *builds* Core
terms the kernel re-checks). The elaborator's hole handling becomes:

- run the resolver on the hole's goal;
- `{:ok, term}` → use `term`;
- `:none` → emit `{:hole, id}` with the deterministic id (now eval-safe; it
  survives to the K3 codegen gate exactly like a body hole);
- `{:error, {:ambiguous_proof_search, …}}` → surface the ambiguity error.

This **replaces** the uncommitted Option-A branch that turned a declined
argument-hole into a hard `{:proof_hole_unresolved, _}` error. Under Slice 1 the
declined hole *survives* instead — the position-uniform `?` semantics the
north-star needs.

## Out of scope (follow-on slices)

- **Slice 2 — hole reporting:** record each hole's goal type + local context at
  its `check` site and expose a query/print path ("what goes here?"). This is
  the interactive payload; it needs a hole registry threaded through checking.
- **Slice 3 — refinement actions:** proof-search `auto` as one fill action among
  several (intro, case-split, refine), driven from the reported goal/context.

## Files

- Modify: `lib/cure/core/eval.ex` (one `eval` clause)
- Modify: `lib/cure/core/conv.ex` (two neutral-identity clauses)
- Modify: `lib/cure/core/quote.ex` (one `reify_neutral` clause)
- Modify: `lib/cure/elab/declarations.ex:1044-1046` (deterministic id lowering)
- Modify: the elaborator hole trigger (proof-search `:none` → surviving hole)
- Create: Antigen antibody for hole conversion + stuck normalization
- Test: `test/cure/core/*` unit coverage for eval/conv/quote hole clauses
- Test: revise `test/cure/elab/proof_hole_resolution_test.exs` (declined hole
  survives; assert no crash + hole present) — reverting the Option-A error
  assertion
