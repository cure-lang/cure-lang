# Sound first-order index unification for dependent `case` — design

**Status:** approved design (autopilot Stage 0). First of three sub-projects
surfaced from the Antigen indexed-case 4.3 finding; the other two
(`Eq`/`rewrite` application-layer consolidation; a new Antigen `rewrite`/`Eq`
known-label vertical) are out of scope here and listed in §10.

## 1. Goal

Make the kernel's dependent-`case` branch refinement **complete for GADT-style
matching** by replacing the one-directional `branch_index_subst` zip with a
sound **bidirectional first-order unifier** over the scrutinee-vs-constructor
index vectors. This closes the documented 4.3 incompleteness (a ground
constructor result index is dropped, so a hypothesis at the unrefined index is
wrongly rejected) and, using the same unifier, **discharges provably-unreachable
branches** (a constructor whose indices clash with the scrutinee's can never
match, so its body need not type-check).

## 2. Motivation — the confirmed incompleteness

Antigen's `indexed/case` obligation 4.3 (`refinement(:well_typed)`) is currently
rejected by the kernel with `{:violation, {:wrongly_rejected, {:refine,
:branch_type}}}`. The reproducing construction (family `Ix(n:Dec)`, constructor
`wrap : (p:Dec) -> Ix Causal`):

```
def_type = Π(n:Dec). Π(h:Ix n). Π(ix:Ix n). Ix n
motive   = λ(n':Dec). λ(ix':Ix n'). Ix n'
body     = λn. λh. λix. case ix of { wrap p -> h }
```

Inside the `wrap` branch the required type is `Ix Causal` (the motive at the
constructor's own ground result index `Causal`), but `h`'s type stays the
unrefined `Ix n`, so conversion fails. A sound, refinement-complete kernel
accepts this: matching `wrap` forces `n := Causal` in that branch, and `h : Ix n`
is then literally `h : Ix Causal`.

The cause is `branch_index_subst/4` (`lib/cure/core/kernel.ex`):

```elixir
defp branch_index_subst(ctx, result_indices, scrut_indices, arity) do
  depth = Context.length(ctx)
  result_indices
  |> Enum.zip(scrut_indices)
  |> Enum.reduce(%{}, fn
    {{:var, i}, scrut_value}, acc ->          # ctor result index is a bare var → solve ctor arg i
      replacement = scrut_value |> Quote.reify(depth) |> Term.shift(arity, 0)
      Map.put(acc, i, replacement)
    {_other, _scrut_value}, acc -> acc         # DROPS every other pair (the bug)
  end)
end
```

It is a one-directional positional zip: it fires only when the *constructor's*
result index is a bare `{:var, i}` (solving a constructor argument), and drops
every other pair — including the case where the constructor's result index is a
**ground/compound term** (`Causal`) and the **scrutinee's** index is a variable
`n` (which should solve `n := Causal`).

## 3. Reference algorithm (Idris 2, verified in the local clone)

Idris has no bespoke "index refinement" pass; it falls out of **symmetric
first-order unification of the two type heads' argument vectors** (verified in
`/Users/ch/Develop/Idris2`):

- `unifyNoEta` on two `NTCon` heads decomposes to `unifyArgs` over the index
  vectors (`src/Core/Unify.idr:1168`) — `Ix Causal ~ Ix n` becomes `Causal ~ n`.
- Each pair is solved whichever side is the unknown; `unifyApp` orients the
  solvable head via a `swap` flag (`convertErrorS`, `:185`), so "scrutinee-index
  var := constructor's ground index" and "constructor-arg var := scrutinee term"
  are the *same* code path.
- `occursCheck` (`:366`) refuses cyclic solutions.
- A rigid/constructor **clash** with no solution yields `convertError`
  (`unifyApp`, `:927`) / `impossibleOK` True (`src/TTImp/ProcessDef.idr:97`) —
  the branch is dropped as **impossible**.

We adopt the *algorithm* but keep Cure's elimination-style application: Cure's
scrutinee index is a rigid de Bruijn variable + an explicit motive (Coq/Lean
idiom), not a clause metavariable, so "solve `n := Causal`" is recorded as a
local context specialization (the existing `specialize_branch_context`), **not**
Idris-style global hole instantiation. No metavariable store, no postponement.

## 4. Design

### 4.1 One new function, existing consumers unchanged

Replace `branch_index_subst/4` with:

```
unify_indices(ctx, result_indices, scrut_indices, arity)
  :: {:solved, subst} | :trivial | :impossible
```

`subst` is the **same** `%{de_bruijn_index => term}` map that
`specialize_branch_context/2`, `specialize_branch_value/3`, and
`replace_branch_vars/2` already consume. The application layer (the syntactic
`replace_branch_vars` substitution) is **not** touched — that consolidation is
sub-project ② and explicitly out of scope (§10). `:trivial` is the empty-subst
case (equivalent to today's empty map).

### 4.2 Integration into `check_case_branches`

`check_case_branches` gains exactly **one new arm**. Today the per-branch body is:

```
subst = branch_index_subst(ctx, result_indices, scrut_indices, arity)
ctx_branch = specialize_branch_context(ctx_branch, subst)
... expected = specialize_branch_value(apply_motive(...), ctx_branch, subst) ...
check(ctx_branch, body, expected)
```

It becomes:

```
case unify_indices(ctx, result_indices, scrut_indices, arity) do
  :impossible ->
    {:cont, :ok}                       # unreachable branch: body NOT checked (vacuous)
  verdict ->                           # {:solved, subst} | :trivial
    subst = subst_of(verdict)          # %{} for :trivial
    ... existing specialize + check(ctx_branch, body, expected) ...
end
```

The family-scoping guard from obligation 4.1 (`{:foreign_ctor, _}`) is unchanged
and still runs **before** unification (a foreign constructor is rejected, not
unified). Arity check unchanged.

### 4.3 The unifier

First-order unification restricted to the constructor-index fragment. Compare
each positional pair `(r, s)` where `r` is a constructor result-index **term**
(over the branch's extended context, i.e. the ctor telescope is in scope) and
`s` is the scrutinee's index **value** (reified to a term at the appropriate
depth). Accumulate a substitution or short-circuit:

- **variable on either side vs any term** — a solvable variable is (a) a
  ctor-telescope de Bruijn index introduced by this branch (always the `r`
  side — `result_indices` only ever contains ctor-telescope variables), or (b)
  an outer-context index variable (always the `s` side — a rigid neutral var
  `{:vneutral, {:nvar, _}}` reified to `{:var, k}`; `scrut_indices` values are
  evaluated in the outer context and can never contain a ctor-telescope
  variable). Bind it to the other side after an **occurs-check** (the bound
  variable must not occur in its own solution). Record in `subst` keyed by the
  de Bruijn index, with the shifting discipline of §4.4. **When the `r` side is a
  bare ctor-telescope var** (whether `s` is a term or itself a variable) — bind
  the **ctor-telescope** variable (`r`) to `s`, i.e. treat `r` as the key. This
  is the pre-existing direction and it is load-bearing: Cure declares every
  `indexed type` with an EMPTY parameter telescope
  (`Inductive.family(name, [], index_tele, level)`, `lib/cure/elab/declarations.ex:405`),
  so a datatype's *uniform parameter* (e.g. `a` in `Vector(a: Type, n: Nat)`)
  is carried as an index and shows up here as a bare-var-vs-var pair. Binding the
  ctor's fresh var to the scrutinee (the caller's `a`) is a harmless no-op that
  keeps the parameter identical across the scrutinee, the return type, and other
  hypotheses. Binding the *other* direction (narrowing the caller's parameter to
  a branch-local var) corrupts that shared parameter and breaks well-typed stdlib
  code (`Std.Vector.append`). NOTE: an earlier draft of this spec mandated the
  reverse ("bind the outer var") as a determinism tie-break; that was wrong —
  Idris/Agda/Lean never unify parameters at all (they distinguish params from
  indices), but Cure has no such distinction, so the only safe orientation for a
  bare-var result index is the ctor-binding one. A genuine (non-uniform) index
  that is a bare var is handled by the same clause and refines correctly.
- **matching constructor/data heads** (`{:ctor, C, as}` vs `{:ctor, C, bs}` with
  equal head/arity, or two `:data` applications of the same family with equal
  arity) — recurse structurally over the pairwise-zipped argument **spine**,
  merging substitutions. For `:data` heads, compare the *flattened* spine
  (`params ++ indices` as one list), not a `ps`-vs-`is` split: `Eval.eval`
  already flattens a `{:data, name, params, indices}` term into a single-list
  `{:vdata, name, params ++ indices}` value (`lib/cure/core/eval.ex:39-40`),
  and `Quote.reify` cannot recover the split when reading a value back into a
  term — by its own comment it always emits the whole flattened list as
  `params` with `indices: []` (`lib/cure/core/quote.ex:45`). Since `s` is
  produced by `Quote.reify`, any nested `:data` term on that side would
  *always* have an empty `indices` list; unifying a real `is` (from `r`, a
  hand-written constructor result-index term) against an always-empty `is'`
  (from `s`) is a representation artifact, not a real structural mismatch, and
  must never be misread as an arity clash. Flattening both sides to one spine
  before recursing (mirroring `Conv`'s own `conv_spine?`) avoids this
  entirely — do not implement a `ps`-vs-`is` split.
- **rigid ground vs rigid ground, definitionally equal** (via the kernel's own
  `Conv`) — contribute no binding (consistent).
- **definite rigid head clash** — two distinct rigid constructor/data heads (or
  a constructor vs a distinct rigid value) that can never be equal → `:impossible`.
- **undecidable** — a stuck neutral application, an unsolved variable against a
  non-matching-but-not-rigidly-clashing term, or any pair the unifier cannot
  confidently classify → contribute **no** binding and do **not** signal
  `:impossible`. The branch then falls through to the existing conversion-based
  body check (today's behavior). This is the conservative escape hatch.
- **re-solving an already-bound variable** — a positional pair, or a pair
  produced by structural recursion, may name a de Bruijn key that an earlier
  pair (in the same `unify_indices` call) already bound. Merging substitutions
  is **not** a blind union: before adding `{key, new_term}` to the accumulator,
  if `key` already maps to `old_term`, decide via the same case analysis as any
  other pair — `old_term` and `new_term` definitionally equal (via `Conv`) →
  keep the existing binding, contribute nothing new; a definite rigid clash
  between them → the *whole* unification is `:impossible`; otherwise (neither
  decided) → drop back to undecidable for that key (no binding change, no
  `:impossible`). A naive `Map.merge` that lets the second binding silently
  clobber the first is **not** an implementation of this spec: it can produce
  an unsound `subst` (one where the two required equations are inconsistent)
  that is nonetheless applied as if solved.

The overall verdict: `:impossible` if any pair clashes (directly, or via a
same-key merge conflict per the previous bullet); otherwise `{:solved, subst}`
(or `:trivial` if `subst` is empty).

### 4.4 De Bruijn discipline (the main risk)

There is exactly **one** de Bruijn space `subst` lives in: `ctx_branch`'s own
numbering (the branch's context *after* `extend_with_telescope`, the same
numbering `specialize_branch_context`/`specialize_branch_value`/
`replace_branch_vars` already consume). Every entry — regardless of which side
of the unification produced it — must be a `{ctx_branch-relative index =>
ctx_branch-relative term}` pair before it enters `subst`. There is no second
"outer depth" that entries live at; solve-direction only changes **which half**
of a binding needs a shift to land in that one space:

- **Solving a constructor-telescope variable** (today's only case): the ctor's
  own args occupy `ctx_branch`'s lowest indices `0..arity-1` (they are the most
  recently bound; `extend_with_telescope` prepends them), so the bare-var *key*
  from `result_indices` is already `ctx_branch`-relative — no shift needed. The
  *replacement value* is a scrutinee-index value living at the outer depth
  (`Context.length(ctx)`, before the telescope extension), so it must be
  reified at that outer depth and then `Term.shift(arity, 0)`'d forward into
  `ctx_branch`'s numbering — exactly what `branch_index_subst` already does.
- **Solving an outer-context index variable** (the new case): here the
  *scrutinee value* is the rigid neutral var `{:vneutral, {:nvar, _}}` being
  solved, and it is the **key**, not the value, that needs the shift: reify it
  at the outer depth, then `Term.shift(arity, 0)` the resulting `{:var, k}` to
  get its `ctx_branch`-relative index. The *replacement term* is the
  constructor's result-index term `r`, which — being written over the ctor's
  own telescope — is already `ctx_branch`-relative and needs no shift.

Getting this backwards (e.g., recording the outer variable's key at its
*unshifted* outer-relative index) does not merely mis-refine — it produces a
`subst` key that either (a) never matches any variable `replace_branch_vars`
encounters while walking `ctx_branch`-numbered terms, so the substitution
silently no-ops, or (b) numerically collides with an unrelated
`ctx_branch`-local variable of the same small index, corrupting an unrelated
type. The substitution merge across structural recursion (§4.3) must preserve
this single coherent index space throughout. This is where correctness risk
concentrates; it is covered by dedicated de Bruijn unit tests (§8).

### 4.5 Coverage unchanged

`check_coverage` is **not** modified: every declared constructor must still have
a branch present. An impossible branch is *present but vacuous* — its body is not
checked. No absurd-pattern surface syntax, no change to exhaustiveness.

## 5. Soundness invariants (the TCB boundary)

1. **Refinement soundness.** Every entry of `subst` is a definitional
   consequence of the scrutinee bearing this constructor in this branch, so
   applying it to context types and the goal is sound (standard dependent
   pattern-match refinement).
2. **Impossible only on definite clash.** `:impossible` fires **only** when two
   rigid constructor/data heads genuinely cannot be equal. Uncertainty (stuck
   terms, undecidable pairs) is **never** `:impossible`, so a body check that was
   actually required is never skipped.
3. **Occurs-check.** A variable is never bound to a term containing itself.
4. **Monotonic degradation.** When the unifier is unsure it produces no binding
   and no `:impossible`; the branch is then checked exactly as today. So the
   change is never *less* sound than the current kernel — it only *adds* accepted
   (well-typed) programs and *discharges* provably-dead branches.
5. **Merge consistency.** If two positional pairs (or two branches of
   structural recursion within one `unify_indices` call) each produce a
   binding for the same de Bruijn key, the merged `subst` never keeps an
   arbitrarily-chosen one without checking the two candidate terms are
   definitionally equal; an inconsistency between them is a clash (yields
   `:impossible`), never a silent overwrite (§4.3).

## 6. Files touched

- `lib/cure/core/kernel.ex` — replace `branch_index_subst/4` with
  `unify_indices/4`; add the `:impossible` arm to `check_case_branches`. May add
  small private helpers (structural unify, occurs-check) local to the kernel.
- Reuse existing `Term.shift`, `Quote.reify`, `Conv`, `Inductive`,
  `replace_branch_vars`, `specialize_branch_context/value`. No new modules.
- `test/antigen/assays/indexed_test.exs` — the 4.3 assay assertion flips from
  expecting `{:violation, {:wrongly_rejected, _}}` to `assert :ok` (§8).
- `test/cure/core/case_soundness_test.exs` (new, or a sibling of
  `case_typing_test.exs`) — the seven kernel tests of §8.

## 7. Non-goals

- No change to the `rewrite`/transport application layer (`replace_branch_vars`
  stays; consolidation is sub-project ②).
- No coverage/exhaustiveness change; no absurd-pattern syntax.
- No new Antigen vertical here (sub-project ③).
- No higher-order/pattern unification, no metavariable store, no constraint
  postponement — first-order only, decided eagerly.

## 8. Testing strategy (TDD, red→green, behavioral & immutable)

The **ready-made red test** is the existing Antigen 4.3 probe: after the fix,
`Antigen.Assays.Indexed.run(Generators.Indexed.refinement(:well_typed))` returns
`:ok` instead of `{:violation, {:wrongly_rejected, _}}`. Its assay test assertion
becomes `assert :ok`, and the challenge is added to the seed bank.

New kernel tests in `test/cure/core/case_soundness_test.exs` (or a sibling):

1. **Positive refinement (4.3 core).** The `h : Ix n` reuse term is accepted by
   `check_def` — demonstrates the goal (§1/§2): the completeness gap is closed
   via a correctly-`:solved` subst.
2. **Refinement soundness (invariant §5.1).** A body that would only typecheck
   under an equation the match does **not** actually establish is still
   **rejected**: construct a branch whose expected type after correct
   refinement requires index `A`, feed a body that only typechecks under a
   *different*, unentailed index `B` (`A` and `B` distinct rigid ground terms),
   and confirm the kernel rejects it. This is the direction Test 1 does not
   cover (Test 1 only shows a previously-rejected *good* program now accepts;
   this test shows an actually-bad program is not newly, wrongly accepted by
   the same machinery).
3. **Impossible-branch discharge.** A `case` whose scrutinee's index rigidly
   clashes with a constructor's ground result index accepts even with a
   deliberately ill-typed body in that branch — proving the body is *not* checked.
   A companion test proves a *reachable* branch with the same ill-typed body is
   still **rejected** (so discharge is not a blanket bypass).
4. **Occurs-check.** A constructed pair that would require a cyclic solution is
   not mis-solved (documents the guard; the branch falls through rather than
   binding a cyclic term).
5. **Clash vs undecidable.** A definite head clash yields discharge (invariant
   §5.2's "only" direction); a stuck / undecidable index does **not** discharge
   and the body is still checked (invariant §5.4, monotonic degradation) —
   this test's two halves assert both invariants together, since they are the
   two faces of the same impossible/undecidable boundary.
6. **Merge consistency (invariant §5.5).** A family with two index positions
   whose ctor result-indices share one telescope variable in both positions
   (e.g. `mk : Π(p:Dec). Foo(p, p)`), matched against a scrutinee with two
   *distinct rigid ground* indices, e.g. `Foo(Causal, Reversed)` — both
   positional pairs are unambiguously ctor-var-vs-ground (no var-vs-var
   tie-break involved), so `p` gets two candidate bindings, `Causal` and
   `Reversed`, which are not definitionally equal. Confirms the conflicting
   bindings for the shared key yield `:impossible`, not a silently-picked,
   unsound `subst`.
7. **Regressions.** The 4.1 branch-family-discipline antibody (`{:foreign_ctor,
   _}` rejection) still **rejects**; every existing `case_typing_test.exs` case
   (the legit `Dec`/`Box` matches) still passes.

The full `indexed/case` Antigen suite + committed corpus/seeds are the standing
regression net. One `mix test` process at a time (never concurrent).

**Discipline for the implementer.** Write the flipped Antigen assertion and all
seven `case_soundness_test.exs` tests above **first**, against the
still-unmodified kernel (`branch_index_subst/4` in place) — before writing
`unify_indices/4`. These tests split into two kinds, and both must be written
up front:

- **New-capability tests (must observably go red→green):** Test 1 and the
  flipped Antigen assertion (today's kernel drops the `n := Causal` equation
  and rejects the program) and Test 3 and Test 5's clash-half (today there is
  no `:impossible` discharge at all, so a dead branch with a deliberately
  ill-typed body makes the whole `case` rejected, not accepted). Confirm each
  is actually red before implementing.
- **Test 6 needs care, not an assumed red.** Today's `branch_index_subst`
  processes the two `Foo(p, p)` index positions independently via a plain
  `Map.put` in an `Enum.reduce`; if it silently *overwrites* `p`'s binding on
  the second occurrence (rather than erroring), today's kernel may already
  proceed with an inconsistent, unsoundly-chosen substitution instead of
  cleanly rejecting — i.e., it may fail for a *different* reason than the one
  Test 6 checks for, not simply "not yet solved." Observe what today's kernel
  actually does for this construction before assuming it's a clean red; if it
  is already silently accepting something it shouldn't, treat that as a
  pre-existing bug this fix also happens to close, and say so in the test.
- **Invariant/regression tests (written first as a characterization net, but
  expected to already pass today and must keep passing):** Test 2 (soundness
  never regresses — today's under-refining `branch_index_subst` can only drop
  equations, never fabricate a false one, so it already can't wrongly accept),
  Test 4, Test 5's undecidable-half, and Test 7. Confirm these pass before
  *and* after the change; if one is unexpectedly red pre-fix, that is itself a
  finding to investigate (it means today's kernel is already less sound than
  assumed), not something to silence.

Only after writing all seven and confirming the above, implement
`unify_indices/4` and the `check_case_branches` integration arm, writing the
minimum needed to turn the new-capability tests green while keeping the
invariant tests green throughout — do not implement first and backfill tests.
Once a test is written and confirmed to correctly encode the behavior
described above, it is **immutable**: reaching green is achieved solely by
changing `lib/cure/core/kernel.ex`, never by weakening, skipping, or deleting a
test. The only exception is discovering a test itself encodes the wrong
behavior, which must be argued explicitly (what the correct behavior is, and
where the test diverges from it) before it may be edited.

## 9. Success criteria

1. `unify_indices/4` returns `{:solved, σ} | :trivial | :impossible` and replaces
   `branch_index_subst/4`; all its callers compile.
2. Antigen 4.3 `refinement(:well_typed)` replays `:ok`; the incompleteness
   finding is closed and its challenge seeded.
3. Impossible branches are discharged without body-checking; reachable ill-typed
   branches still rejected.
4. Invariants §5.1–§5.5 hold, each with a dedicated test: §8 test 2 → §5.1,
   test 3 → §5.2, test 4 → §5.3, test 5 → §5.2 and §5.4 (its clash/undecidable
   halves), test 6 → §5.5. Test 1 demonstrates the goal (§1/§2); test 7 is the
   general regression net.
5. Full suite green; the 4.1 branch-family-discipline antibody and all prior
   Antigen verticals still pass; no coverage/exhaustiveness behavior change.

## 10. Deferred sub-projects (not this run)

- **② `Eq`/`rewrite` application-layer consolidation** — collapse
  `replace_branch_vars` (case, syntactic) and `Eval.apply(motive, endpoint)`
  (rewrite, semantic transport) into one shared transport engine. Depends on and
  follows this work; wants ③'s probe as its net.
- **③ Antigen `rewrite`/`Eq` known-label vertical** — a Tier-A-style deep-cut
  probing Codex's merged rewrite normalization; the audit net for ②.
