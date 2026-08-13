# Regex proof elaboration assessment

**Status:** assessed after the Concat acceptance theorem

**Date:** 2026-08-13

**Scope:** decide whether one small elaborator feature should precede the Group
and Repeat acceptance proofs, and identify the proof plumbing that should be
made reusable first.

## Decision

Do **not** add a new elaborator feature before Group and Repeat.

The Concat failures did not establish a missing reduction rule. They established
that destructuring an existential certificate can discard the exact identity
needed by a later dependent projection. The checked solution is an indexed view
whose result index retains the original certificate. Separately, the repeated
initial-edge normalization sequence is now represented by total checked
combinators:

- `NormalizedInitialActive` / `normalize_initial_active`;
- `NormalizedInitialAccepted` / `normalize_initial_accepted`.

These combinators recover the unfiltered routine, rebuild the boundary-filtered
edge with `Nil()` constraints, and transport the routine execution in one
typed result. Group and Repeat should consume these and their existing
projection-specific transport functions. Add an elaborator feature only when a
small red program from those proofs demonstrates that the remaining boilerplate
cannot be expressed by an ordinary indexed view, `Equivalent`, `rewrite`, or a
checked transport combinator.

## Evidence from Concat

The successful theorem required `ExactAcceptanceStartView`, indexed by:

```text
(machine, input, acceptance)
```

Each constructor returns the exact `active_acceptance_certificate(...)` or
`accepted_now_certificate(...)` from which its fields came. That index is
load-bearing: an ordinary `AcceptanceStartView` retained the payload but forgot
the equality between the caller's certificate and the reconstructed
certificate. A direct nested `Sigma` match likewise did not refine the later
`machine_state_thread` projection sufficiently.

Other failures in the same proof had different, local causes:

- implicit `inject_left` and `widen` terms normalized to a form different from
  the canonical `inject_left_at(left_count, right_count, state)` expected by the
  combined machine;
- publishing `widen` in the proof interface left an unsolved implicit
  metavariable during interface registration;
- direct proof of append associativity was weaker than the existing checked
  `InputPartition` / `partition_append_after` interface.

None is evidence that conversion should unfold more definitions globally.

## Existing compiler capability

The elaborator already has two relevant convoy mechanisms:

1. `with e proof p` over a non-indexed family constructs an Eq-arrow motive,
   binds `p : Equivalent(T, e, pattern)` in each branch, and transports
   dependent siblings. The kernel checks the resulting `case`, `rewrite`, and
   reflexivity term.
2. Indexed LHS-rematch clauses use `Kernel.branch_unify/5`, refine the branch
   goal and dependent siblings, and are checked again by the kernel's indexed
   case eliminator.

The current deliberate boundary rejects `with e proof p` when `e` belongs to
an indexed family. A branch constructor may refine the scrutinee's type indices,
so a whole-value equation between the original scrutinee and the branch value
is generally heterogeneous. Supporting that form is therefore not merely
surface syntax around the existing homogeneous `Equivalent`: the established
design requires either a restricted theorem about equal endpoint types or an
`HEq`-like kernel feature with its own soundness gate.

The Concat certificate itself unfolds to nested non-indexed `Sigma`, so the
existing proof-clause mechanism could be explored as alternate notation. It is
not needed for correctness, and replacing the exact indexed view with it would
trade an explicit result invariant for branch-local rewrites rather than remove
the underlying proof obligation.

## Why stronger reducible-index simplification is rejected

`expose_reducible_dependency/4` already performs bounded, selective unfolding
for convoy dependency discovery. Direct source inspection and the focused
Chiasmus call graph show it is reached from match dispatch and sibling/index
collection, not used as an unrestricted conversion policy. It unfolds only
published `@reducible` definitions with finite fuel and leaves opaque,
uncertified, open, and recursive definitions folded.

The exact-certificate failure persisted after the necessary reducers were
visible because normalization cannot invent a propositional relationship that
was erased from the result type. Broadening delta reduction would therefore:

- fail to restore the forgotten certificate identity;
- risk changing canonical forms used by elaboration and interface publication;
- increase work in an already expensive proof module; and
- make proof success depend on transparency policy instead of a stated
  invariant.

Keep reducer exposure targeted. If Group or Repeat produces a genuine
definitionally-equal index mismatch, preserve the smallest red example and fix
the single conversion or dependency-discovery authority rather than adding a
proof-module workaround.

## Gate before revisiting this decision

A compiler feature is justified only if all of the following are present:

1. a minimal failing `.cure` regression extracted from Group or Repeat;
2. a statement of the equality needed in the failing branch;
3. evidence that an indexed view or checked transport combinator merely
   restates information already available to the elaborator;
4. a Core term construction the existing kernel can independently check; and
5. a demonstrated reduction in the actual Group/Repeat proof, not only a toy
   example.

If the required equation is homogeneous and concerns refined indices rather
than the whole indexed value, the modest candidate is an authored binder for
the index equation already established by `branch_unify`. If it is a
whole-value equation across different indexed instances, stop: that is the
previously identified heterogeneous-equality boundary, not a modest
elaboration convenience.
