# Neutral-Application Sort Inference (Sigma D1 kernel enabler) — Design

**Status:** approved design (operator standing batch authorization; TCB change pre-approved under the Agda/Lean-alignment blanket — this rule is exactly how both kernels type neutral type-valued applications — with the FULL verification gate mandatory).
**Layer:** K (TCB, `lib/cure/core/kernel.ex` — one new clause + one defensive one-liner, see §2.4 — nothing else) + tests/Antigen/oracle.
**Batch:** task #13 part D1, worktree `kernel-parity-batch`, branch `autopilot/kernel-parity-batch`. D2 (primitive-Sigma retirement) is a separate, chained spec that depends on this landing.

## §0 The gap (verified in this worktree, 2026-07-08)

`infer_type_value_sort/2` (`lib/cure/core/kernel.ex:606-665`) classifies motive-body values in `check_motive_wf/4` (`kernel.ex:591-604`). Its clauses: `{:vtype,_}` (606), `{:vneutral, {:nvar,_}}` (613 — bare variable only), `{:vint_type}`/`{:vfloat_type}` (622-623), `{:vdata,_,_}` (625), `{:vpi,…}` (643), `{:vsigma,…}` (654), fallthrough `{:error, :not_a_type_value}` (665). There is **no clause for a neutral APPLICATION** `{:vneutral, {:napp, …}}`.

Consequence: a dependent eliminator whose motive applies a type-family *variable* — the canonical case being Sigma's second projection, `second : (p: MySigma(a, b)) -> b(first(p))` with `b : (a) -> Type` — evaluates its motive body to `{:vneutral, {:napp, …}}`, hits the fallthrough, and `check_motive_wf` maps it to `{:error, :bad_motive}` (`kernel.ex:600-602`). This blocks ALL user-defined dependent eliminators into `b(x)`-shaped types, not just Sigma's. **Note for the implementer:** no MySigma probe file exists anywhere in this worktree (verified — a repo-wide search for `MySigma` finds nothing under `.cure`/`.ex`/`.exs`); the "probe-verified earlier" claim in an earlier draft of this section had no traceable artifact, exactly the kind of unattributable claim §0's own stale-scout warning exists to guard against. The gap's existence is instead established directly here from the code path: `infer_type_value_sort`'s clause list (above) has no `{:napp,…}` clause, `check_motive_wf`'s `case` (`kernel.ex:600-602`) maps any non-`{:ok,_}` result to `:bad_motive` unconditionally, and a `second`-shaped motive evaluates to exactly `{:vneutral, {:napp, …}}` (§2.4 works through the evaluation in detail for a related shape) — so the rejection is a direct, re-derivable consequence of the current clauses, not a claim resting on an unlocatable prior run. The MySigma `.cure`/`.idr` probe files this spec calls for (§3 item 4, §4) are new artifacts to be created as part of this change, not preexisting ones.

A load-bearing fact that dictates the design (verified at `kernel.ex:197-224`): the `:case` rule **never checks the motive as a term** — `motive_value = Eval.eval(motive, …)` (207) straight into `check_motive_wf` (209). The sort walk is the motive's ONLY validation. The new clause therefore may not trust anything about the application (the untrusted elaborator built it); it must fully validate, including the spine arguments.

**Stale-scout warning for reviewers/planners:** an earlier scoping report for this task read the MAIN repo checkout, not this worktree, and reported pre-batch facts (live `{:eq}`/`{:veq}` primitives, a `{:veq}` clause in this very function). Those are false here — the identity-type retirement IS complete in this tree (`ccbe2d0`, `727a673`, `11ea830`; validator `no_eq_node: :reject`). Every anchor in this spec was re-verified against the worktree; re-verify anything else against `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/kernel-parity-batch`, never the parent checkout.

## §1 Goal

`check_motive_wf` accepts a motive whose body is a neutral type-valued application — `b(x)`, `b(first(p))`, `F(n)` for a global type-family def — with the sort the head's Pi codomain assigns, while rejecting exactly as before: applications of non-type-valued heads (`g(x)` with `g : (a) -> Nat`), ill-typed arguments, and anything the kernel cannot fully validate. The MySigma `second` probe elaborates end-to-end; Idris agrees (differential probe).

## §2 Design — reify the neutral, run the trusted term-level `infer/2` (plus one defensive totality clause, §2.4)

```elixir
# A neutral APPLICATION is a valid type iff the kernel's own term-level
# judgement says so: reify the spine back to a term and infer it. `infer/2`'s
# `{:app, f, a}` rule (kernel.ex:125-132) resolves the head's type (ctx var or
# signature global), CHECKS each argument against the instantiated Pi domain,
# and returns the codomain — full validation, nothing trusted from the
# (untrusted) elaborator that assembled the motive. Accept only a `{:vtype, l}`
# result: `b(first(p))` with `b : (a) -> Type` sorts at `l`; `g(x)` with a
# non-type codomain infers to something else and stays `:not_a_type_value`.
defp infer_type_value_sort(ctx, {:vneutral, {:napp, _, _} = neutral}) do
  term = Quote.reify({:vneutral, neutral}, Context.length(ctx), Context.signature(ctx))

  case infer(ctx, term) do
    {:ok, {:vtype, level}} -> {:ok, level}
    _ -> {:error, :not_a_type_value}
  end
end
```

Placed with the other `infer_type_value_sort` clauses (after the `{:nvar}` clause at 613). **Verified against `lib/cure/core/quote.ex`:** there is no public `reify_neutral/2`. `reify_neutral/3` (quote.ex:96-113, handling `{:nvar}`/`{:nglobal}`/`{:napp}`/`{:nfst}`/`{:nsnd}`/`{:nprim}`/`{:ncase}`) is `defp` — unreachable from `kernel.ex`. The call must go through the public `reify/3` (quote.ex:40, `reify(value, depth \\ 0, sig \\ nil)`), which dispatches `{:vneutral, n}` to `reify_neutral(n, depth, sig)` internally (quote.ex:76). Passing `Context.signature(ctx)` as the third argument (not defaulting to `nil`) is required, not optional: quote.ex's own moduledoc documents that this signature-aware form exists precisely so a `{:vdata, name, args}` value occurring inside the reified term recovers its true param/index split via the family's parameter-telescope length (quote.ex:16-28, `split_data_args/3`) instead of collapsing everything into `params` with `indices = []`. Without `sig`, that collapse is exactly what produces the `:arg_arity` false rejection described in §2.2 below — so threading `Context.signature(ctx)` through eliminates the §2.2 corner for this clause entirely (see the revised §2.2).

### §2.1 Why reify+infer, not a head-codomain spine walk

The tempting lighter design — walk the spine to the head `{:nvar, level}`, look up its Pi in `ctx`, apply closures down the args, sort the final codomain — **does not validate the arguments**. Because the motive term is never term-checked (§0), unchecked arguments would flow into the case's result type (`apply_motive`, kernel.ex:223) and outward. Term-level `infer/2` is the kernel's already-trusted validator and does head resolution + argument checking in one move; reusing it makes the clause sound by construction rather than by a new argument. This mirrors Lean's `inferType` on `App` and Agda's sort inference on applied neutrals: head's Pi, arguments checked, instantiated codomain.

### §2.2 The known-lossy reify corner — closed by threading the signature

`Quote.reify/3` collapses `{:vdata, name, args}` to `{:data, name, args, []}` (no param/index split) **only when called with `sig = nil`** — the documented warning at `kernel.ex:632-642`, which is exactly why the Π/Σ clauses recurse on values instead of reifying. `Quote.reify` itself has a signature-aware mode for exactly this situation (quote.ex:16-28, `split_data_args/3`): given the family's parameter telescope, it recovers the true param/index split from a flat `{:vdata, name, args}` value. §2's clause passes `Context.signature(ctx)` as the third argument, so a spine **argument** that is itself an indexed-family *type value* (e.g. `F(Vec(a, n))` with `F : Type -> Type`) reifies with its split recovered, and re-inference does not hit `:arg_arity`. The corner is therefore **not** a residual limitation of this clause — it only reappears if a future caller reifies with `sig = nil`, which this clause does not do. (The general caveat that an *unknown* family — not registered in `sig` — still falls back to the flat split, per `split_data_args/3`'s own fallback, is inherent to `reify` and not specific to this clause; an unknown family cannot occur here anyway, since the argument's value would have had to originate from a `{:data, ...}` term the kernel already resolved against a registered family to produce it.)

### §2.3 What the clause newly accepts, precisely

Neutral applications whose reified term `infer`s to `{:vtype, l}`: variable heads bound at Pi-into-Type (the Sigma motive), global heads whose declared/inferred type is Pi-into-Type (type-level function defs — accepted automatically by the same judgement; no special casing), projection heads if `reify_neutral` supports them and `infer` types them. Everything else keeps rejecting with the same tags. No other kernel judgement changes; conversion, normalisation, coverage, and branch checking are untouched.

### §2.4 A crash the reify+infer design newly exposes: `infer/2` has no `{:pair, _, _}` clause

Verified against `kernel.ex`: `infer/2` has a clause for every term shape `Quote.reify`/`reify_neutral` can produce — `{:type,_}`, `{:var,_}`, `{:int_type}`/`{:int_lit,_}`, `{:float_type}`/`{:float_lit,_}`, `{:prim,_,_}`, `{:pi,_,_}`, `{:lam,_,_}`, `{:global,_}`, `{:sigma,_,_}`, `{:fst,_}`, `{:snd,_}`, `{:app,_,_}`, `{:data,_,_,_}`, `{:ctor,_,_}`, `{:case,_,_,_}` — **except `{:pair, a, b}`** (`reify({:vpair,a,b},…)`, quote.ex:59). By design, pairs are check-only (`check(ctx, {:pair,a,b}, {:vsigma,…})`, kernel.ex:252); `infer` never needed a `{:pair,…}` clause because ordinary elaboration only ever builds a pair term where the expected type is already known to be a Σ.

This clause breaks that invariant. Because the motive is never term-checked (§0), the untrusted elaborator can write a motive whose body applies a variable/global to a **pair literal** in a position whose real domain is not a Σ — e.g. `λv. b(pair(Z, Z))` where `b`'s kernel-resolved type is `(a) -> Type` for a plain type variable `a` (domain `{:vneutral,{:nvar,_}}`, not `{:vsigma,…}`). Evaluating that motive produces `{:vneutral, {:napp, …, {:vpair, {:vctor,:Z,[]}, {:vctor,:Z,[]}}}}`; reifying yields `{:app, head, {:pair, {:ctor,:Z,[]}, {:ctor,:Z,[]}}}`; `infer`'s `{:app,f,a}` rule resolves `dom` (not a Σ) and calls `check(ctx, {:pair,…}, dom)` (kernel.ex:128) — none of `check`'s Σ/hole/ctor clauses match (`dom` isn't `{:vsigma,…}`, term isn't a hole or ctor), so it falls through to the generic clause (kernel.ex:306), which calls `infer(ctx, {:pair, {:ctor,:Z,[]}, {:ctor,:Z,[]}})` — **no clause matches, and Elixir raises `FunctionClauseError`**, crashing the compiler instead of returning `{:error, …}`.

This is not hypothetical or pre-existing-and-unrelated: today, `infer`/`check` are never invoked this way because every other caller either type-checks the motive (they don't — that's §0's whole point) or never routes an unvalidated value-turned-term into `infer` at this generality. This clause is the first path that does, so it is the path responsible for keeping `infer` total over its own reified output.

**Fix (part of this same TCB change, not deferred):** add one defensive `infer/2` clause, ordered anywhere `infer` is otherwise unmatched:
```elixir
def infer(_ctx, {:pair, _, _}), do: {:error, :pair_not_inferable}
```
This mirrors the existing discipline (pairs are checked, not inferred) as an explicit rejection instead of a missing clause, and is required for the new `infer_type_value_sort` clause to be total over adversarial motives — the same standard §2.1 already holds the design to. `git diff` therefore shows **two** small `kernel.ex` additions: the `infer_type_value_sort` clause (§2) and this one-line `infer` clause (§6 acceptance criterion 5 is worded accordingly).

## §3 TCB gate (mandatory, blanket-approval conditions)

This is a kernel change. The blanket approval applies (Agda/Lean-aligned per §2.1), which waives the per-diff operator review but NOT the gate:

1. Strict red-green (the probe below fails `:bad_motive` today; the §2.4 pair-argument crash test fails with an uncaught `FunctionClauseError` today, until both the `infer_type_value_sort` clause and the defensive `infer(_,{:pair,_,_})` clause land).
2. **New Antigen antibody** (`lib/antigen/` + `test/antigen/`): (i) an accepting seed — a motive applying a type-family variable must pass `check_motive_wf` (the D1 shape); (ii) a rejecting seed — a motive applying a non-type-valued head (`g : (a) -> Nat`) must still reject `:bad_motive`; (iii) the standard no-defeq-collapse/termination obligations for a TCB change: run the full Antigen suite — the existing conv/nf idempotence and substitution-law families exercise the new value shape via the enlarged accept set.

   **Precedent to model both seeds on (verified present in-worktree):** `Antigen.Generators.DepMatch` (`lib/antigen/generators/dep_match.ex`) is the existing well-typed dependent-`case` generator that already drives `check_motive_wf` → `infer_type_value_sort` with dependent (non-constant) motives — it currently generates `:data`-shaped dependent motives (`λm.λv. Vec m`) but not yet a neutral-application motive; add a D1 accepting variant there (or as a sibling generator) rather than inventing new scaffolding. `Antigen.Generators.Malformed.case_bad_motive/1` (`lib/antigen/generators/malformed.ex`) is the existing reject-seed shape (`{:case, scrut, motive, branches}` with a motive that must fail `check_motive_wf` with `:bad_motive`, assay `"term/rejection"`, label `:ill_typed`) — add the `b : (a) -> Nat` variant as one more `tagged(case_bad_motive(...), ...)` entry in its `malformation/0` frequency list.
3. Full Antigen suite + full test suite, zero failures.
4. **Differential oracle probe**: a new `sg` cluster pair — `sg01_dependent_second.cure` (the MySigma family with `first`/`second`) and the faithful `.idr` transliteration (Idris: a custom `MySigma` record/data with dependent `second : (p : MySigma a b) -> b (first p)`; `%default total`, no module line) — expected relation `same` (both accept). The executor runs `mix cure.oracle sg` ONCE (alone; it regenerates only that cluster's verdicts.json — the standing destructive-command caution is about accidental regeneration of OTHER clusters; adding a new cluster is its intended use), then the replay test must be green. Any divergence (Cure accepts / Idris rejects or vice versa) is a STOP-and-report, per the oracle contract.

## §4 Tests

- **Unit (`test/cure/elab/dependent_eliminator_test.exs`, new):**
  - The MySigma probe program (family with function-typed param `b`, `mk_pair` GADT ctor, `first` by match, `second : (p: MySigma(a, b)) -> b(first(p))` by match) elaborates `{:ok, _}` — red today with `:bad_motive`.
  - `second(mk_pair(x, y))` reduces/runs correctly (BEAM execution of a monomorphic instance; also pins the `first(mk_pair(x,y)) → x` ι-reduction inside branch checking, which requires `first` to be δ-certified — structurally recursive, auto-certified).
  - Negative: the same shape with `b : (a) -> Nat` (non-type codomain) still rejects (`:bad_motive` — the `{:error, :not_a_type_value}` path preserved).
  - Negative: an ill-typed argument in the motive position (e.g. `b(w)` where `w`'s type doesn't match `b`'s domain) still rejects — the argument-checking half of §2.1 is observable.
  - Negative (§2.4): a motive applying a variable head to a **pair-literal** argument whose real domain is not a Σ (e.g. `λv. b(pair(Z, Z))` with `b : (a) -> Type`) rejects cleanly (`{:error, :bad_motive}` from the kernel, not an uncaught `FunctionClauseError`) — this is the red test that proves the §2.4 defensive `infer` clause is in place and doing its job.
- **Antigen antibody** per §3.2.
- **Oracle pair** per §3.4.
- Existing pins: full suite green; no existing test asserts `:bad_motive` for a *well-typed* neutral-app motive (they couldn't — the feature never worked), so no pin flips.

## §5 Non-goals

- D2 (primitive-Sigma retirement to `@builtin(:sigma)`) — separate chained spec; NOTE for its author: the prior scout's D2 inventory (site anchors, `:eq`-status claims) came from the stale parent checkout and must be re-swept in-worktree.
- Extending the signature-aware split (`split_data_args/3`) itself, or its behaviour for a spine argument whose head family is *unknown* to `sig` — inherent to `reify`, unrelated to this clause (§2.2).
- Any change to `conv.ex`, `normalise.ex`, `eval.ex`, coverage, or branch checking.
- Surface syntax work (the MySigma probe uses existing surface forms only).

## §6 Acceptance criteria

1. The `second` probe elaborates and runs; red→green documented.
2. All three §4 negatives still reject with today's tags (the pair-literal negative rejects cleanly rather than crashing).
3. Antigen: new antibody green; FULL Antigen suite green.
4. Oracle: `sg` cluster `same`/`same`; replay green.
5. Full `mix test` green; `git diff` shows exactly two new clauses in `kernel.ex` — the `infer_type_value_sort` clause (§2) and the defensive `infer(_ctx, {:pair, _, _})` clause (§2.4) — plus tests/Antigen/oracle fixtures; no other `lib/cure/core/` change.

## §7 D1b amendment (2026-07-09 adjudication): implicit insertion for global applications in return-type position

Execution of §2 STOPped on a verified elaborator gap: with both kernel clauses in
place, the canonical implicit-param probe STILL rejects `:bad_motive`, because the
motive the elaborator hands the kernel is **malformed (under-applied)** — not
because the kernel judgement is wrong.

### §7.1 The finding (verified in-source, this worktree)

- `function_signature` (`lib/cure/elab/declarations.ex:104`) lowers a fn's
  return-type annotation via `idx_to_core`.
- `idx_to_core`'s function-call fallthrough (`declarations.ex:915-916`) lowers an
  application of a term-level global as a **bare explicit-args spine**
  (`Enum.reduce(core_args, {:global, atom}, …)`) — NO implicit-argument insertion.
- Term position inserts implicits (`elaborate_named_call` →
  `elaborate_implicit_app_bidirectional/6` → `finish_global_app`,
  `lib/cure/elab/elaborator.ex:4102-4125`): the SAME surface `first(p)` in a body
  lowers to the full 3-arg spine.
- Consequence: `second : (p: MySigma(a,b)) -> b(first(p))` with implicit `{a}{b}`
  gets motive `{:lam, MySigma, {:app, {:var,2}, {:app, {:global,:first}, {:var,0}}}}`
  — `first` applied to 1 of 3 binders. The napp clause faithfully reifies it and
  `infer/2` correctly rejects (`:conversion_failure` checking the MySigma-typed
  argument against `first`'s first domain `Type`). The kernel work is right; the
  input is wrong.
- Kernel-side proof retained from execution: the identical probe with **explicit**
  type params (full spine in the annotation) elaborates `:ok`, and a hand-built
  global-free `λv. b(v)` motive now passes motive-wf (fails later at
  `:branch_type`, exactly the accept-pin behavior).

### §7.2 Alignment

In Idris/Agda/Lean, types ARE terms: one elaborator, implicit insertion in every
position including signatures. Cure's separate type-position lowering silently
lacking insertion is a parity defect. Fixing it is the faithful move (standing
directive: align with real languages).

### §7.3 Design (targeted delegation; lower-risk fork chosen)

1. In `function_signature`, after `elaborate_param_telescope` succeeds, build the
   kernel typing context for the params (`build_context(env, telescope)` — already
   the body-pass pattern at `declarations.ex:78`) and thread `{scope, ctx}` into
   the return-type lowering ONLY.
2. In `idx_to_core`'s function-call fallthrough (the `true ->` bare-spine branch),
   when (a) a ctx was threaded in, (b) the head resolves to a term-level global
   (not a family, ctor, or bound var — i.e. exactly this branch), and (c) that
   global's registered quantities contain an `:erased` slot, delegate the WHOLE
   application (surface arg ASTs, not pre-lowered args) to the term-position
   machinery via a narrow public wrapper over
   `elaborate_implicit_app_bidirectional/6` (no `expected`), and return its term
   (drop the returned result type).
3. The ctx threads through the return-type lowering RECURSION — in particular
   through `map_idx_to_core` and the applied-bound-var branch's arguments. This
   is the probe's actual shape: in `b(first(p))` the head `b` is a BOUND VAR
   (the `declarations.ex:902` branch); the implicit-carrying global `first` sits
   one level down, in an argument position. Delegation triggers at ANY
   function-call node in the recursion satisfying (a)-(c) of item 2.
4. Crossing a binder-introducing type form (`pi_type`, `sigma_type`, the
   `arrow_to_pi` nest) NULLs the threaded ctx for that sub-lowering: the scope
   gains binders the kernel context does not have, and reusing the stale ctx
   would mis-frame de Bruijn references. Under binders, behavior stays exactly
   today's (see §7.5).
5. Every other `idx_to_core` call site (ctor signatures, index telescopes) threads
   no ctx — byte-identical behavior. Globals with NO implicits keep the existing
   bare-spine path (today's working behavior, proven by the explicit-param probe).

Blast radius: strictly failure→success. Today an implicit-carrying global applied
in a return annotation ALWAYS yields an under-applied spine the kernel rejects, so
no currently-working program routes through the new branch.

Layer: **E only** (untrusted). The kernel re-checks the assembled Π and every
motive; an insertion bug degrades to rejection, never unsoundness. No new
`lib/cure/core/` change is part of D1b.

### §7.4 Registration-pass caveat (verification step, not an assumption)

`second`'s signature is lowered during the registration pass; the delegation
consults the env for `first`'s type+quantities, which must already be registered
(declaration order — `first` precedes `second`). If signature-only registration
does not populate `Env.get_def/2` with `%{type, quantities}`, the implementer must
locate what the registration pass DOES store and consult that — NOT silently skip
insertion. If neither is available at signature time, STOP and report.

### §7.5 Residual gap (non-goal, documented)

Implicit-carrying global applications in ctor-signature / index-telescope type
positions (no ctx available there); in **parameter-type annotations**
(`elaborate_param_telescope_rec`, `declarations.ex:530`, calls `idx_to_core/4` —
the ctx is threaded into the return-type lowering ONLY, per §7.3 item 1, never
into the param telescope, so a later param's type applying an implicit-carrying
global — e.g. `q: b(first(p))` as a fourth parameter — keeps today's bare spine
exactly like the return-type gap this spec fixes); and in return-type
subexpressions UNDER a binder-introducing form (`pi_type`/`sigma_type`/arrow —
ctx nulled per §7.3 item 4): all three keep today's bare spine. Follow-up
candidates, out of D1 scope.

### §7.6 Test-plan correction (executor-verified)

The §4 pair-literal negative MUST use a **function-typed** head applied to a pair
(`b : (a) -> Type` applied to `pair(Z, Z)`), as §4 already states. A Nat-typed
head (`{:var,0} : Nat` applied to a pair) fails `ensure_pi` BEFORE the pair is
examined and never exercises the §2.4 crash — such a test passes identically with
or without the defensive clause and proves nothing.

### §7.7 Acceptance deltas

§6 criteria stand unchanged, with §6.5 extended: the final diff additionally shows
the D1b elaborator change confined to `lib/cure/elab/declarations.ex` plus a
narrow public wrapper in `lib/cure/elab/elaborator.ex`; STILL exactly two new
clauses in `kernel.ex` and no other `lib/cure/core/` change.
