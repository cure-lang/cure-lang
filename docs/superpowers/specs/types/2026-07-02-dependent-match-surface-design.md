# Surface dependent matching: impossible clauses + full index refinement — design

**Status:** approved design (autopilot Stage 0). Sub-project ④ of the
case-refinement initiative. Kernel case-refinement unification is complete
(Task 1+2, `5646c63`/`f16d008`) and probed by Antigen (injectivity, no-confusion,
discharge). This surfaces that power into the `.cure` language, aligned with
Idris2.

## 1. Problem

The trusted kernel supports dependent `case` with full first-order index
unification: solution, deletion, injectivity, occurs-check, no-confusion, and
impossible-branch discharge. The **untrusted elaborator** (`Cure.Elab`) does not
surface any of it:

1. **No impossible clauses.** `check_coverage` (`kernel.ex:648`) requires
   `declared ⊆ covered`, so a user must write a branch for every constructor —
   even one that cannot occur at the scrutinee's index. There is no syntax to
   omit or mark such a branch, and `constructor_pattern/1` (`elaborator.ex:470`)
   crashes on any non-`function_call` pattern.
2. **Incomplete per-branch refinement.** This is two related but distinct
   gaps, both from the same weaker private copy of unification:
   - *Ctor-compound vs. bare-scrutinee* (e.g. matching `vcons : … -> Vec a
     (S n)` against a scrutinee `xs : Vec a m`, `m` a bare outer variable):
     the elaborator's own one-directional `branch_index_subst`
     (`elaborator.ex:491,536`) only solves "ctor telescope var := scrutinee
     term"; it cannot solve the reverse ("outer var := ctor's compound
     term"), which the elaborator's own comment concedes: "`S(n) := m`
     refinement is not invertible in this minimal pass" (`elaborator.ex:533`).
     Fixed by delegating `branch_expected_type`/`specialize_branch_context`
     to `branch_unify`'s bidirectional subst (§3) — no motive change needed,
     since these already do plain variable-keyed substitution with an
     arbitrary (possibly compound) right-hand side.
   - *Scrutinee-compound* (e.g. the scrutinee itself is `xs : Vec a (S m)`):
     `build_motive`/`generalize` generalizes the motive only over index
     positions that are *bare variables* (`elaborator.ex:314,331` —
     `{_non_var, _} -> acc` drops the rest), so a result type that reuses the
     scrutinee's compound index term verbatim does not refine — even though
     the kernel would accept the fully-built term. Fixed by extending
     `generalize` to whole-subterm matching (§3), scoped to verbatim reuse
     (see §3's correction on what this can and cannot solve).

Both are the same root cause: **the elaborator carries a weaker private copy of
index unification** than the kernel now has.

## 2. Goal / acceptance

A `.cure` program can:

- **(A) Omit impossible branches** — a `match` that lists only the reachable
  constructors elaborates and compiles; a `match` that omits a *reachable*
  constructor is rejected with a clear "missing branch" diagnostic.
- **(A) Mark a branch impossible** — `C(args) -> impossible` elaborates when the
  branch is genuinely unreachable and is rejected (`:reachable_impossible`) when
  it is not (Idris' verified `impossible`).
- **(Completeness) Refine constructor-headed indices** — a dependent `match`
  against a constructor with a compound result index unifies against a bare
  outer scrutinee index (the `S(n) := m` case, §1.2); and a dependent `match`
  whose scrutinee index is itself constructor-headed, where the per-branch
  result type reuses that same index term verbatim, elaborates and
  type-checks (the "inner variable" framing is narrowed to verbatim reuse —
  see §3's correction on `generalize`).

Idris alignment references (from the study): unification verdict taxonomy
`Core/Unify.idr:85`; injectivity/no-confusion `Unify.idr:1148`; case motive
`CaseTree.idr:20` + per-branch refinement `CaseBuilder.idr:909`; verified
`impossible` `ProcessDef.idr:999`; surface `lhs impossible`
(`tests/typedd-book/chapter08/Void.idr`).

## 3. Architecture — one kernel query, elaborator delegates

The kernel keeps ALL unification logic (TCB stays minimal). We add exactly one
public wrapper over the existing private `unify_indices/4`:

```elixir
# lib/cure/core/kernel.ex — the main TCB addition (no new unification logic;
# see §5/§8.1 for the second, one-line `{:absurd}` typing clause)
@spec branch_unify(Context.t(), atom(), atom(), [Cure.Core.Value.t()]) ::
        {:solved, map()} | :trivial | :impossible
def branch_unify(ctx, dname, cname, scrut_indices)
```

**Signature correction (verified against the kernel; an earlier draft wrote
`branch_unify(env, dname, cname)` — wrong).** `Cure.Core.Env.t()` (`inductive.ex:1`)
is only the *global signature* — registered families, constructors, and defs.
It carries no local variable bindings and no per-call-site data.
`unify_indices/4` (`kernel.ex:714`) needs two things `env`/`dname`/`cname`
cannot supply: (1) `ctx` (`Context.t()`), to compute
`outer_depth = Context.length(ctx)` for reifying and shifting the scrutinee's
index values into the branch's r/s term space; (2) `scrut_indices`, the
*actual, per-call-site* index **values** of the specific scrutinee being
matched (e.g. the concrete `m` in `xs : Vec a m` at this match expression) —
these vary per match site and are not recoverable from `dname`/`cname` alone,
which only name the family/constructor schema. `check_case_branches/6`
(`kernel.ex:659`) receives both as explicit parameters from its caller — "It
rebuilds the scrutinee/constructor index vectors exactly as
`check_case_branches` does" is only true once `branch_unify` is threaded the
same two inputs.

The corrected wrapper takes the caller's `ctx` and the scrutinee's
already-evaluated index values (the elaborator already has these as
`idx_vals` in `elaborate_match`, §5 step 1) and returns the same verdict
`unify_indices` produces — `{:solved, subst} | :trivial | :impossible` —
where `subst` is the branch refinement in the branch's de Bruijn frame
(`ctor-args ++ outer`, identical to how the kernel's `extend_with_telescope`
and the elaborator's `extend_context` build the branch context; the
frame-alignment invariant is §8). There is no separate "params" segment in
this frame: neither `extend_with_telescope` (`kernel.ex:571`) nor the
elaborator's `extend_context` (`elaborator.ex:518`) push the family's
parameters as distinct context binders — `scrut_params`/`param_vals` are used
only as seed *values* for evaluating the telescope's argument types, not as
new bindings in the context stack. (An earlier draft described the frame as
`params ++ ctor-args ++ outer`; that segment doesn't exist as stated — this
has been corrected here and in §8.3.)

The **elaborator delegates** to this query and stops using its own
`branch_index_subst`:

- **Impossibility (A):** `:impossible` ⇒ the branch is discharged (synthesized)
  / an explicit `-> impossible` is accepted; `{:solved,_}|:trivial` on an
  omitted constructor ⇒ "missing branch" error.
- **Refinement (completeness):** use the returned `subst` to compute
  `branch_expected` and to specialize the branch context — replacing the
  incomplete local `branch_index_subst`. `build_motive`/`generalize` is likewise
  extended to abstract each scrutinee index *term* (not only bare vars) into its
  motive binder (whole-subterm replacement up to shifting).

  **Correction: "depends on the refined inner variable" (§1.2/§2) is two
  different claims, and whole-subterm replacement only delivers one of them.**
  Traced against the current `generalize/4` (`elaborator.ex:351-402`) and
  `branch_index_subst`/`branch_expected_type` (`elaborator.ex:489,559`):
  - *(a) Verbatim reuse* — `ResultType` contains the scrutinee's own index
    term **as a literal subterm** (e.g. scrutinee `xs : Vec a (S m)`,
    `ResultType = Vec a (S m)` too, or `Fin (S m)`). Here "whole-subterm
    replacement" is well-defined: wherever the *exact* term `S(m)` (shifted
    to the current traversal depth) occurs in `ResultType`, replace it with
    the motive's binder variable. `branch_expected_type`/
    `specialize_branch_context` need no analogous change for this case —
    they already do plain variable-keyed substitution
    (`replace_branch_vars`, `elaborator.ex:571`) with an arbitrary
    (possibly compound) right-hand side, which is correct as soon as they
    are fed `branch_unify`'s richer bidirectional `subst` instead of the old
    one-directional `branch_index_subst`.
  - *(b) Bare inner variable* — `ResultType` mentions the variable *inside*
    the constructor head bare (e.g. scrutinee `xs : Vec a (S m)`,
    `ResultType = Vec a m`, as in a `tail`-shaped function). Traced through
    both mechanisms, **neither solves this**: whole-subterm matching looks
    for the literal term `S(m)` in `ResultType`, but `ResultType` here
    contains only bare `m`, not `S(m)` — zero matches, no-op generalization,
    same failure as today. `branch_expected_type`'s substitution is keyed by
    `branch_unify`'s subst, whose key for this branch is the *constructor's*
    telescope variable (e.g. `k` in `vcons`'s own `S(k)`, bound as `k :=
    m`) — not `m` itself — so `ResultType`'s occurrences of bare `m` are
    never rewritten either. Soundness reason this is hard in general, not
    just unimplemented: inverting the constructor head (recovering "the `m`
    such that `S(m)` is the index") is partial — it has no answer for the
    `vnil : Vec a Z` branch, where no `m` satisfies `S(m) = Z`. Idris/Agda
    solve this class with `with`-abstraction / an explicit `rewrite`, which
    is out of scope here (§9 already excludes flex-flex/postponed
    unification; this is the same family of problem).

  **Fix:** narrow the Slice 3 acceptance criterion (§2, §6) to case (a) —
  the scrutinee's own index term reused verbatim somewhere in the result
  type — and state case (b) as an explicit, intentional non-goal (added to
  §9). The illustrative example in §1.2 must change accordingly: replace
  "a result type depending on the inner variable" with a verbatim-reuse
  example, e.g. `def id_vec(xs : Vec a (S m)) : Vec a (S m) = match xs {
  vcons(x, rest) -> vcons(x, rest) }` (return type reuses the scrutinee's
  exact index term `S(m)`).

  **Algorithm for whole-subterm replacement (case (a)), not yet specified.**
  Even restricted to case (a), `generalize/4`'s current traversal only ever
  substitutes at `{:var, i}` leaves (`elaborator.ex:351-360`); matching a
  *compound* target term requires a different shape of recursion, and this
  is exactly the kind of place off-by-one shifting bugs hide in motive
  construction. The extension must specify, not assume:
  1. **Check before recursing, at every node** — not only at `{:var,...}`
     leaves: at each call `generalize(subterm, rebind, shift, depth)`, first
     shift each target index term (originally given at depth 0, in the
     outer frame) by `depth` (e.g. via `Subst.shift(target, depth, 0)`) and
     compare it for exact structural equality (plain `==`, since Core terms
     are closures-free tagged tuples/lists — `term.ex`/`subst.ex` confirm
     no term-equality helper exists yet, so this is a new, small utility)
     against `subterm`. On a match, return the motive binder variable
     (`{:var, binder + depth}`); only on no match, recurse structurally into
     `subterm`'s children as today.
  2. **Do not recurse into a matched subtree** — once a node is replaced by
     a binder reference, its children must not be independently visited
     (that would incorrectly hunt for, and rewrite, nested occurrences of
     the target's own free variables inside a term that no longer exists in
     the output).
  3. **Unify the bare-variable case as the degenerate, one-node instance of
     the same rule**, so there is exactly one substitution mechanism rather
     than two independent, divergence-prone code paths (today's
     `{:var, orig}, pos -> rebind` special case and the new whole-term
     match).
  4. **Multiple index positions with distinct compound targets** must each
     be checked at every node (not just the first match), so `generalize`
     abstracts all `k` index positions correctly when more than one is
     constructor-headed.

**Soundness stays in the kernel.** The elaborator's use of the query is a
convenience for producing a well-typed Core term; the kernel independently
re-checks (and independently discharges) the final `{:case,…}`. A wrong
elaborator decision cannot produce an accepted-but-ill-typed program — at worst
a spurious elaboration error, never unsoundness. This is the same trust boundary
as the rest of `Cure.Elab`.

## 4. Surface syntax

Reuse the existing `match`/arm grammar (`parser.ex:1362,1432`). Two additions:

1. **Omission** — no grammar change; a `match` may list a subset of
   constructors. Coverage of the *reachable* set is enforced by the elaborator
   (§5), the kernel remains the backstop.
2. **Explicit impossible arm** — `pattern -> impossible`, where `impossible` is a
   keyword body. Parsed as a normal arm with an `impossible: true` marker in the
   arm meta (no new statement form). Chosen over Idris' post-LHS `impossible`
   because Cure `match` is expression-arm-based, not clause-based; `-> impossible`
   is the natural fit.

   **Correction: this needs a lexer decision, not just a parser check.**
   Verified against `lexer.ex`: `impossible` is not in `@keywords`
   (`lexer.ex:47-56`), so today it lexes as a plain identifier and
   `parse_match_arm` (`parser.ex:1432`) has no `%Token{type: :keyword, ...}`
   to match on the way it does for `when` (`parser.ex:1440`). Two ways to
   make it recognizable, and the spec must pick one:
   - **Reserve it as a global keyword** (add to `@keywords`) — simplest, but
     a breaking change for any existing `.cure` code using `impossible` as an
     identifier (variable, field, or function name).
   - **Treat it as a contextual/soft keyword**, following this codebase's own
     existing precedent for exactly this tradeoff: `sup`/`app` are
     documented as soft keywords recognized only at a specific structural
     position, explicitly so identifier uses of the word keep compiling
     (`lexer.ex:40-46`). Recommended: recognize `impossible` only when it is
     the entire arm body in `parse_match_arm` (i.e. inspect the parsed body
     post-hoc, or peek for the identifier token in that position), the same
     non-reserving discipline as `sup`/`app`.
   Whichever is chosen, "needs only a keyword check in `parse_match_arm`"
   understates the work — it needs a lexer-level decision plus (if soft-
   keyword) a body-position check.

`_` / variable / literal patterns are out of scope here (constructor patterns
only, as today) EXCEPT that `constructor_pattern/1` must stop crashing on them —
it returns a clean `{:error, {:unsupported_pattern, …}}` instead (§5).

## 5. Elaborator behavior (untrusted)

`elaborate_match` gains a coverage/discharge pass:

1. Elaborate the scrutinee; get `dname`, params, indices (as today).
2. Partition declared constructors into **matched** (a surface arm), **explicit
   impossible** (`-> impossible` arm), and **omitted** (no arm).

   **Gap: this partition is driven by `dname`'s declared constructor set, not
   by the surface arms — it must not silently drop arms that don't belong to
   any declared constructor.** As written, "partition declared constructors"
   iterates `Inductive.ctors_of(dname)` and asks, per constructor, "is there
   an arm for this" — an arm whose pattern names a constructor that is
   *unknown* or belongs to a *different* family never corresponds to any
   `declared` entry, so it would never be visited and would be silently
   dropped from the emitted `{:case,…}` with no diagnostic at all. This would
   be a regression from today: `elaborate_branch` (`elaborator.ex:425-430`)
   currently visits every arm and already rejects a truly unknown constructor
   name (`{:error, {:unknown_pattern_constructor, cname}}`); it does not yet
   check the *family* (`Inductive.ctor_family/2`, used only by the kernel's
   `:foreign_ctor` check today), so a same-name-different-family arm
   currently surfaces late as a kernel type error rather than an early
   elaboration error — silent dropping would be strictly worse than either.
   Fix: before or during partitioning, validate every surface arm's pattern
   constructor against `Inductive.get_ctor/2` **and**
   `Inductive.ctor_family/2 == dname`, erroring
   (`{:error, {:unknown_pattern_constructor, cname}}` /
   `{:error, {:foreign_ctor, cname}}`) on any arm that doesn't name one of
   `dname`'s own declared constructors, before assembling the
   declared-constructor partition.

   **Also unspecified: two surface arms for the same constructor.** Nothing
   in the grammar (§4) prevents writing two arms for the same `cname`. Today
   every arm is independently elaborated and both would end up in
   `branches`, tolerated (if wastefully) by the kernel. The declared-
   constructor partition needs exactly one bucket per constructor, so it must
   say what happens on 2+ arms for one `cname` — recommended: reject with a
   dedicated `{:error, {:duplicate_branch, cname}}` (a user mistake is more
   likely than an intentional duplicate) rather than silently picking
   first-or-last.
3. For each **matched** constructor: elaborate its body against `branch_expected`
   computed from `branch_unify(ctx, dname, cname, idx_vals)`'s `subst` (not the
   old local subst).

   **Gap: this assumes `branch_unify` returns `{:solved,_}`/`:trivial` for
   every matched constructor, which the partition (step 2) doesn't
   guarantee.** Step 2 classifies "matched" purely by surface syntax (an arm
   exists and isn't `-> impossible`) — it says nothing about whether that
   constructor is actually reachable. A user can write a normal-looking body
   for a constructor that is genuinely unreachable without marking it
   `impossible`; the kernel's `check_case_branches` (`kernel.ex:676-678`)
   already tolerates this today — an `:impossible` verdict skips body
   *checking* unconditionally, regardless of what the body contains. If
   `branch_unify` also returns `:impossible` here, there is no `subst` to
   compute `branch_expected` from, and step 3 as written doesn't say what to
   do. Fix: when a **matched** constructor's `branch_unify` verdict is
   `:impossible`, elaborate the user's body unchecked against its own
   inferred type (`elaborate_expr_typed`, not `elaborate_expr_checked`) —
   mirroring the kernel's own "don't bother checking an unreachable branch"
   discipline — rather than either (a) computing a nonsensical
   `branch_expected` from a nonexistent `subst`, or (b) silently discarding
   the user's body in favor of a synthesized `{:absurd}` (which would throw
   away code the user deliberately wrote and can see was never flagged as
   impossible).
4. For each **explicit-impossible** constructor: require
   `branch_unify(ctx, dname, cname, idx_vals) == :impossible`; else
   `{:error, {:reachable_impossible, cname}}`. Emit a discharged branch.
5. For each **omitted** constructor: if `branch_unify(ctx, dname, cname, idx_vals)
   == :impossible`, synthesize a discharged branch; else
   `{:error, {:missing_branch, cname}}`.
6. Assemble `{:case, scrut, motive, branches}` with a branch for EVERY declared
   constructor (matched + discharged), so the kernel's `check_coverage` passes
   unchanged. The kernel then re-validates: it independently discharges the
   impossible ones and checks the reachable bodies.

**Discharged-branch body.** A synthesized/impossible branch needs a
structurally-valid placeholder body the kernel will not check (it discharges the
branch). Use a canonical marker term `{:absurd}` (new Core leaf, evaluated
never — it only ever sits in a discharged branch). The kernel's
`check_case_branches` already skips the body for `:impossible`.
*Alternative considered and rejected:* reuse `{:hole,_}` — rejected because
the kernel accepts holes at any type (`kernel.ex` hole rule), which would let
a *reachable* omitted branch slip through if the elaborator's verdict ever
disagreed with the kernel's; a body the kernel canNOT accept when checked is
the safer backstop.

**Correction: `{:absurd}` needs one explicit kernel clause, not zero, to be a
working backstop.** Verified against `kernel.ex`: `infer/2` (lines 41–238) has
no catch-all clause, and `check/3`'s catch-all (line 332) delegates to
`infer/2` for any term without a dedicated `check` rule. If `{:absurd}` were
added with *no* kernel rule at all (as an earlier draft of this doc claimed),
a reachable branch carrying it would make `infer(ctx, {:absurd})` raise an
unhandled `FunctionClauseError` — not return `{:error, _}`. There is no
`rescue`/`catch` around kernel type-checking calls (`kernel.ex` and
`elab/program.ex` have none; the only `rescue` in `cli.ex` guards an unrelated
`keys generate` command), so this would crash the compiling process rather
than produce the atom-taggable diagnostic §7's testing plan assumes
("Negatives assert the exact error atom"). Soundness is not at risk either
way — a crash still isn't acceptance of an ill-typed program — but a crash is
strictly worse than a clean rejection: it can't be asserted on in the surface
negative-test corpus, and it would surface as a compiler-crash bug report
rather than a user-facing type error. Fix: add exactly one trivial,
unconditionally-failing kernel clause,
`def infer(_ctx, {:absurd}), do: {:error, :absurd_in_reachable_position}`,
so `check/3`'s existing `{:error, _} -> {:halt, {:error, :branch_type}}` path
in `check_case_branches` handles it the same way as any other ill-typed body.
This is a second, deliberately trivial TCB addition alongside `branch_unify/4`
(§8.1's "TCB delta = one wrapper" is updated to "one wrapper + one
always-fails clause" accordingly) — with it, `{:absurd}` has no *positive*
typing rule (it never checks against anything), so a reachable branch
carrying it is cleanly rejected by the kernel — the belt to the elaborator's
suspenders.

**`{:absurd}` surface cost (must be handled in Slice 2).** A new Core leaf is
touched by more than the kernel: `Serialize` (`lib/cure/core/serialize.ex`;
`{:hole, name}` already has a dedicated `enc`/`build_node` pair there —
`{:absurd}` needs the same, discharged branches appear in serialized terms),
and codegen — verified: `Cure.Elab.Erase.erase/2` (`lib/cure/elab/erase.ex`)
has a catch-all (`def erase(_env, term), do: term`, line 74) so `{:absurd}`
passes through unerased with no change needed there, but
`Cure.Elab.Emit`'s `lower/3` (`lib/cure/elab/emit.ex:170`) has *no* catch-all —
its last clause is `defp lower(_env, term, _ctx), do: raise(ArgumentError, ...)`
— so Slice 2 MUST add an explicit `lower(_env, {:absurd}, _ctx)` clause
lowering to an `error/1`-style unreachable stub, or codegen crashes with an
`ArgumentError` the first time a discharged branch reaches emission. These are
enumerated so the plan covers them; besides the kernel's one always-fails
`infer` clause above, none add a *positive* typing rule. NOTE: because the
elaborator only synthesizes a discharged branch when `branch_unify ==
:impossible` — the SAME function the kernel discharges on — the elaborator and
kernel cannot disagree, so even the `{:hole,_}` alternative would never
actually be checked; `{:absurd}` is chosen purely for defense-in-depth (a body
the kernel rejects if the invariant ever broke). If the review judges the
new-leaf surface not worth that margin, falling
back to `{:hole,_}` is sound given the same-function invariant — this is the one
open decision for Stage-1 review.

## 6. Slices (implementation order)

- **Slice 1 — kernel query.** `branch_unify/4` + unit tests (mirrors the
  Ix/Foo fixtures in `case_soundness_index_test.exs` and the Antigen `IW`
  fixture, per §7). No behavior change yet.
- **Slice 2 — impossible clauses (A).** Parser `-> impossible`; elaborator
  coverage/discharge pass; `{:absurd}` Core leaf (elaborator-only, kernel
  discharge already handles it); harden `constructor_pattern`. Surface tests:
  omit-impossible compiles, omit-reachable errors, explicit-impossible verified,
  mis-marked-impossible rejected.
- **Slice 3 — refinement completeness.** Elaborator consumes `branch_unify`'s
  `subst` for `branch_expected`/context specialization (fixes the
  ctor-compound/bare-scrutinee `S(n) := m` case, §1.2 — no motive change
  needed for this half); extend `build_motive`/`generalize` to abstract a
  scrutinee's own constructor-headed index term where it is reused verbatim
  in the result type (§3's algorithm, restricted to case (a) — see the
  correction there for why bare-inner-variable dependence, case (b), is not
  attempted). Surface tests: (i) a match on a ctor with a compound result
  index against a bare scrutinee index elaborates + runs; (ii) a match whose
  scrutinee index is constructor-headed and whose result type reuses that
  exact index term elaborates + runs.

Each slice is independently green + committed. Slices 2 and 3 both depend on
Slice 1.

## 7. Testing

- Kernel: `branch_unify/4` unit tests (impossible / solved / trivial), reusing
  the Ix/Foo fixtures already in `test/cure/core/case_soundness_index_test.exs`
  and the IW fixture from the Antigen indexed-case generator
  (`lib/antigen/generators/indexed.ex`, exercised by
  `test/antigen/assays/indexed_test.exs` and
  `test/antigen/indexed_seed_test.exs`) — verified: `IW` is not defined in
  `case_soundness_index_test.exs` itself, only `Ix`/`Foo`/`Dec` are.
- Surface (`.cure` source through `Cure.Elab.Program.elaborate`): positive +
  negative programs per Slice 2/3 acceptance in §2. Negatives assert the exact
  error atom (`:missing_branch`, `:reachable_impossible`).
- Antigen: the existing indexed-case vertical (injectivity/discharge antibodies)
  and ③ `rewrite/eq` MUST stay green — they guard the kernel the elaborator now
  leans on. No new Antigen vertical required (this is surface/elaborator work,
  outside the TCB); a `.cure`-level regression corpus is the surface analogue.
- Full suite once per slice; baseline 2173, zero regressions.

## 8. Invariants / soundness boundary

1. **TCB delta = one wrapper + one always-fails clause.** `branch_unify/4`
   adds no unification logic; it reuses `unify_indices/4`. `{:absurd}` is an
   elaborator-only leaf with no *positive* kernel typing rule — but per §5's
   correction it does need one trivial `infer(_ctx, {:absurd}) ->
   {:error, _}` clause (never a `check` success), so that it is only ever
   valid in a discharged position and a reachable occurrence fails cleanly
   instead of crashing the kernel with an unmatched-clause exception.
2. **Kernel is the backstop.** Every emitted `{:case,…}` is fully re-checked and
   re-discharged by the kernel; the elaborator's coverage/impossibility decisions
   are ergonomic, never trusted for soundness. A disagreement yields an
   elaboration or kernel error, never an accepted ill-typed program.
3. **Frame alignment.** `branch_unify`'s `subst` is in the branch de Bruijn frame
   the elaborator's `extend_context` builds (`ctor-args ++ outer` — see §3's
   signature correction; there is no separate `params` segment). This only
   holds once `branch_unify` is given the caller's own `ctx` and the
   scrutinee's actual index values (§3) — `branch_unify` cannot derive either
   from `dname`/`cname` alone. Slice 1 tests pin the frame against a
   hand-built branch context before Slice 3 consumes it.
4. **No coverage weakening in the kernel.** `check_coverage` is unchanged; the
   elaborator always emits a full constructor set (matched + discharged).
5. Ghost-written commits; one build at a time; OTP 26–28.

## 9. Out of scope (future)

- Non-constructor patterns (`_`, literals, nested) — only cleaner rejection here.
- Nested/deep pattern compilation to a case tree (Cure matches one level today).
- Metavariable/postponed-constraint unification at the surface (Idris'
  flex-flex) — the elaborator's separate `Cure.Elab.Unify` already covers
  inference metas; branch refinement is first-order and complete without it.
- **Bare-inner-variable motive generalization** (§3's case (b)): a result
  type that depends on the *variable inside* a constructor-headed scrutinee
  index (e.g. scrutinee `Vec a (S m)`, result type `Vec a m`) rather than
  reusing the index term verbatim. Inverting the constructor head is partial
  (undefined for `vnil`'s `Z` index, which has no predecessor `m`) — this is
  the same class of problem as Idris/Agda's `with`-abstraction, not
  first-order whole-subterm matching, and is left for a future design.
