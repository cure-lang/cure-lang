# Primitive-Sigma Retirement (Sigma D2) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Retire the kernel-primitive Sigma (`{:sigma}`/`{:pair}`/`{:fst}`/`{:snd}` + `vsigma`/`vpair`/`nfst`/`nsnd`) in favor of a stdlib inductive registered `@builtin(:sigma)`, with surface behavior, oracle verdicts, and the BEAM bare-2-tuple ABI all invariant — spec `docs/superpowers/specs/kernel/2026-07-09-sigma-retirement-design.md` (hardened `466fd36`).

**Architecture:** Producers first, strip last, validator ratchet in between (spec §1.8): T1 registry+stdlib inductive → T2 elaborator re-point (crux) → T3 emit hooks → T4a `no_sigma_node: :warn` → T6 Antigen migration → T7 test/example sweep → T5 kernel/core+traversal strip → T4b `:reject` → full gate. Kernel work is REMOVAL-ONLY (no new judgements; the D1 napp clause survives, spec §1.3).

**Tech Stack:** Elixir, `Cure.Core.{Kernel,Builtins,Inductive,Validator}`, `Cure.Elab.{Elaborator,Declarations,Emit}`, ExUnit, Antigen, oracle replay.

## Global Constraints (every task implicitly includes these)

- Working dir: `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/kernel-parity-batch`, branch `autopilot/kernel-parity-batch`. **Never read or edit the parent checkout `/Users/ch/Develop/esp32-beam/cure-lang/lib/…`** (stale-scout precedent).
- **Two-pipeline steer:** dependent machinery ONLY in `lib/cure/elab/*` + `lib/cure/core/*`; `lib/cure/types/*` and `lib/cure/compiler/*` are the non-dependent decoy pipeline (same-named functions are decoys) — NO diff there, parser included (surface AST unchanged, spec §2.2).
- Strict red-green TDD; tests behavioral and immutable once green. Core-SHAPE pin flips are authorized ONLY where a task step enumerates them with a one-line justification (C-3 discipline, spec §3.3); surface-BEHAVIOR pins never flip.
- ONE `mix` command at a time, ever (past concurrent run caused a kernel panic). Scoped `mix test <paths>` per task; full suites once, alone, in the final gate.
- **NO `mix cure.oracle` run in this initiative** (spec §3.4): replay against frozen verdicts IS the invariance check. Any replay verdict change = STOP-and-report.
- Git: commit per task; EVERY commit `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`; NO trailers; explicit-pathspec staging only.
- Line anchors below are from the 2026-07-09 scout at `0171461`; earlier tasks shift later anchors — re-locate by the quoted code, not the number.
- STOP-and-report: any oracle replay divergence; any pre-existing test failing (except one non-reproducible Antigen-seed flake — re-run once alone, note honestly); any need for a NEW kernel judgement clause (this plan only deletes); any `lib/cure/types/*` or `lib/cure/compiler/*` diff; the §1.1 universe-haircut survey turning up a real >level-0 sigma user; the T2b projection-naming decision failing BOTH options in Step T2b.1.
- Record `git rev-parse HEAD` at Task 1 Step 0 as `<pre-d2-commit>` for final diff verification.

## File Structure

- `lib/cure/core/builtins.ex` — `:sigma` schema + seed (T1).
- `lib/std/sigma.cure` — NEW: `@builtin(:sigma)` decl + projection fns (T1).
- `lib/cure/elab/elaborator.ex` — checked-tuple path, scope-based tuple, `sigma_projection`, branch-body tuple (T2).
- `lib/cure/elab/declarations.ex` — `elaborate_body` tuple fallback, `idx_to_core` sigma_type + type-position projections, `type_to_core` (T2).
- `lib/cure/elab/emit.ex` — `sigma_ctor?` hook, branch clause, projection inlining (T3).
- `lib/cure/core/validator.ex` — `no_sigma_node` clause (T4a/T4b).
- Antigen: 18 lib files + `test/antigen/seeds.sexp`/`corpus.sexp` (T6; scout §6 table is the checklist).
- Strip (T5): kernel.ex, eval.ex, quote.ex, conv.ex, normalise.ex, term.ex, serialize.ex, value.ex, inductive.ex, certificate.ex, meta_check.ex, validator.ex (ONLY the 4-tuple grade clause + `grade_on_binders` sigma — the 3-tuple `children` descend-walker clauses survive permanently, see T4a/T5 Step 2); elab traversals (elaborator/unify/subst/resolution/relevance/totality_closure); erase.ex (per-line list, NOT ranges — spec §2.3).
- Tests: `test/cure/core/sigma_test.exs` rewrite, Core-shape pin flips per T7's enumeration, `test/cure/elab/sigma_inductive_test.exs` NEW (T1/T2 red-green driver), `examples/sigma_pairs.cure` rewrite (T7).

---

### Task 1: registry seed + stdlib inductive + drift pin

**Files:** Modify `lib/cure/core/builtins.ex`; Create `lib/std/sigma.cure`; Modify the preload registry (`Cure.Stdlib.Preload.module_groups()` — locate in `lib/cure/stdlib/preload.ex`); Test: `test/antigen/builtin_sigma_drift_test.exs` (NEW — the byte-equal seed-vs-prelude COMPARISON MECHANISM to mirror is `test/cure/elab/builtin_prelude_seed_test.exs` (plain Elixir `==` on `Inductive.get_family/2` maps + `Enum.sort_by(&1.name)` ctor lists — no metadata to strip since Core terms are bare tuples/maps), NOT `builtin_bool_drift_test.exs` (review-verified: that file only checks `eval.ex`'s hardcoded `:True`/`:False` atoms against the schema's ctor-name list — a narrower, unrelated antibody. `builtin_bool_drift_test.exs` is fine only as a location/naming precedent for where a new antigen-directory drift file lives). Today `builtin_prelude_seed_test.exs` is exercised only for `:Bool` (0 params, nullary ctors) — this task is the FIRST time the mechanism runs against a family with params and a function-typed field; write it expecting to have to generalize the comparison, not assume it already handles this shape.

**Interfaces produced:** `Inductive.builtin(env_or_sig, :sigma)` → `:Sigma` family id; ctors `mk_pair/2`; stdlib globals for projections (names fixed in T2b Step 1 — this task defines them in `lib/std/sigma.cure` under the names T2b chooses; write the stdlib file LAST in this task if executing strictly in order, or revisit).

- [ ] **Step 0:** `git rev-parse HEAD` → record `<pre-d2-commit>`. Read `builtins.ex` in full (117 lines, review-corrected — re-verify at execution time since earlier tasks shift line counts) and `lib/std/equivalent.cure` (the `@builtin` decl precedent).
- [ ] **Step 1 (red):** write `test/antigen/builtin_sigma_drift_test.exs`: (a) the seeded `:sigma` family exists with ctor `mk_pair/2`; (b) the prelude-compiled `Std.Sigma` declaration produces a family/ctor-signature representation equal to the seed's — plain Elixir `==` on `Inductive.get_family/2` maps and `Enum.sort_by(&1.name)` ctor lists, the `builtin_prelude_seed_test.exs` mechanism (NOT `builtin_bool_drift_test.exs` — see Files note above); (c) `Inductive.builtin(env, :sigma)` resolves after seeding. Run scoped: fails (no schema/seed).
- [ ] **Step 2:** `builtins.ex`: add `sigma: [{:mk_pair, 2}]` to `@schemas`; add `|> maybe_seed(:sigma, sigma_family(), sigma_ctors(), exclude)` to `seed/2`; add:

```elixir
  # Sigma : (a : Type) -> (b : (a) -> Type) -> Type   (2 params, no indices)
  #   mk_pair : (x : a) -> b(x) -> Sigma(a, b)
  # The library dependent pair (spec 2026-07-09-sigma-retirement), replacing the
  # primitive {:sigma}/{:pair}/{:fst}/{:snd} Core forms. Level-0 like Equivalent.
  # Source of truth is the @builtin(:sigma) decl in Std.Sigma; this seed is its
  # byte-for-byte mirror, pinned by the conformance drift test.
  defp sigma_family,
    do: Inductive.family(:Sigma, [a: {:type, 0}, b: {:pi, {:var, 0}, {:type, 0}}], [], 0)

  defp sigma_ctors,
    do: [
      Inductive.ctor(
        :mk_pair,
        [x: {:var, 1}, y: {:app, {:var, 1}, {:var, 0}}],
        [],
        [:present, :present],
        [{:var, 3}, {:var, 2}]
      )
    ]
```

De Bruijn frames (verify against the eq template at builtins.ex:112-119 and iterate against the drift test — the STDLIB DECL is the source of truth, adjust the SEED to match what `type Sigma(a: Type, b: (a) -> Type) indices ()` + `mk_pair : (x: a) -> b(x) -> Sigma(a, b)` elaborates to): field `x`'s type in frame `[a, b]` → `a = {:var, 1}`; field `y`'s type in frame `[a, b, x]` → `b(x) = {:app, {:var, 1}, {:var, 0}}`; result params in frame `[a, b, x, y]` → `[a, b] = [{:var, 3}, {:var, 2}]`. If `Inductive.ctor/5`'s argument convention differs (check a 5-arg caller), adapt — the drift test arbitrates.
- [ ] **Step 3:** create `lib/std/sigma.cure`:

```
mod Std.Sigma

@builtin(:sigma)
type Sigma(a: Type, b: (a) -> Type) indices ()
  mk_pair : (x: a) -> b(x) -> Sigma(a, b)

fn <proj1>({a: Type}, {b: (a) -> Type}, p: Sigma(a, b)) -> a = match p
  mk_pair(x, y) -> x

fn <proj2>({a: Type}, {b: (a) -> Type}, p: Sigma(a, b)) -> b(<proj1>(p)) = match p
  mk_pair(x, y) -> y

end
```

`<proj1>`/`<proj2>` are the projection names chosen in T2b Step 1 (do T2b Step 1's naming decision NOW if executing linearly — it is a read-only decision) — bare surface identifiers as they appear in `.cure` source (e.g. `first`/`second`). Task 2 Step 5 below reuses this SAME decision as `<proj1_atom>`/`<proj2_atom>` — the Elixir atom form of the identical chosen name (e.g. `:first`), not a separate open decision. These are the D1-proven shapes verbatim (sg01 fixture). Register the module in `Cure.Stdlib.Preload.module_groups()` following how `Std.Equivalent`/`Std.Bool` are keyed; check whether equivalent.cure's auto-prelude EXCLUSION (program.ex:230-240) applies — Sigma must be seeded programmatically regardless (the seed carries availability), so mirror eq's arrangement.
- [ ] **Step 4:** run scoped: drift test green. Then `mix test test/antigen/` — all green (seeding must not disturb existing envs; the `exclude` mechanism guards local redeclarations — note D1's probe declares its OWN `MySigma`, different name, unaffected; any test declaring a family literally named `Sigma` will collide → check with `grep -rn '"Sigma' test/ lib/antigen/` and report).
- [ ] **Step 5:** commit: `feat(stdlib): Sigma builtin-inductive — registry seed + Std.Sigma + drift pin (D2 T1)`.

---

### Task 2: elaborator re-point (T2a construction/types, T2b projections)

**Files:** Modify `lib/cure/elab/elaborator.ex`, `lib/cure/elab/declarations.ex`; Test: `test/cure/elab/sigma_inductive_test.exs` (NEW).

**Interfaces consumed:** `Inductive.builtin(env, :sigma)`; `Kernel.normalize/2`; `Elaborator.elaborate_implicit_global_app/5` (the type-position ctx-threading wrapper documented at `declarations.ex:861-868`, "spec 2026-07-08 §7.3" — review-verified: NOT literally named "D1b" anywhere in source; do not grep for that label, it will find nothing). **Produced:** every surface `%[..]`/`Sigma(…)`/`.1`/`.2` lowers to `{:ctor, mk_pair, …}` / `{:data, Sigma, …}` / projection-global spines. NO primitive-node producer remains in elaborator.ex/declarations.ex EXCEPT the mechanical traversals (stripped in T5).

- [ ] **Step 1 (red):** write `test/cure/elab/sigma_inductive_test.exs`, all via `Program.elaborate` + Core-shape asserts on the elaborated def (obtain defs the way `sigma_surface_test.exs` does):
  1. `fn dep() -> Sigma(n: Nat, Vector(Nat, n)) = %[S(Z()), …]`-style dependent pair (crib the exact working surface from `test/cure/elab/sigma_surface_test.exs` / oracle `dpair/dpp01`): elaborates; body Core contains `{:ctor, :mk_pair, _}` and NO `{:pair, _, _}`; the def's Pi codomain contains `{:data, :Sigma, _, _}` and NO `{:sigma, _, _}`. (`mk_pair`/`Sigma` are the FIXED, already-decided ctor/family names — not placeholders like `<proj1>`/`<proj2>`; angle brackets dropped here to avoid reading them as an open decision.)
  2. `.1` and `.2` on a Sigma-typed param: elaborate; Core contains no `{:fst|:snd, _}`.
  3. Type-position projection (`SF(as, bs, p.1)`-shaped, crib from sigma_surface_test.exs:52's program): elaborates, no `{:snd, _}` in the signature Core.
  4. Runtime: `Emit.compile_and_load` a module with `fn use() -> Nat = %[Z(), S(Z())].2`-equivalent (via the working surface) asserting the runtime VALUE is unchanged from today. There is no "Step 0" in this task (Task 2 starts at Step 1) — capture today's runtime value FIRST, before writing this test and before any other Task 2 edit lands: with the codebase AS-IS (primitive `{:pair}`/`{:fst}`/`{:snd}` still compiling to bare-tuple/`element/2`, spec §1.5), compile-and-run the equivalent primitive-path program (or read what `frp_beam`/`dependent_surface_codegen` tests already pin for it) and hardcode THAT observed value as this test's expected value. This runtime test goes green only after T3 (T2 alone routes `%[..]` through the generic tagged-ctor path, emit.ex:158-175, which does NOT match the captured value yet); mark it clearly as T3's red (same combined-red discipline D1 used: never commit while red).
  Run scoped: shape asserts fail (Core still primitive).
- [ ] **Step 2 (T2a):** checked-mode `%[a, b]` (`elaborate_expr_checked({:tuple, …})`, elaborator.ex:918-935): replace the `{:sigma, dom, cod}` normalize-match with the builtin data match; second component's expected type is an APPLICATION, not a binder instantiation (spec §2.2):

```elixir
  def elaborate_expr_checked({:tuple, _meta, [a_ast, b_ast]} = expr, expected_core, names, ctx, env) do
    sigma_fam = Inductive.builtin(env, :sigma)

    case Kernel.normalize(ctx, expected_core) do
      {:data, fam, [dom, b_fn], []} when fam == sigma_fam and not is_nil(sigma_fam) ->
        [%{name: mk_pair} | _] = Inductive.ctors_of(env, sigma_fam)

        with {:ok, a_term} <- elaborate_expr_checked(a_ast, dom, names, ctx, env),
             cod_inst = {:app, b_fn, a_term},
             {:ok, b_term} <- elaborate_expr_checked(b_ast, cod_inst, names, ctx, env),
             term = {:ctor, mk_pair, [a_term, b_term]},
             :ok <- Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
          {:ok, term}
        end

      _ ->
        elaborate_expr_checked_fallback(expr, expected_core, names, ctx, env)
    end
  end
```

Frame/shape check (verified by reading `Normalise.nf`/`Quote.reify`, not assumed): `Kernel.normalize/2` delegates to `Normalise.nf/3`, which calls `Quote.reify(value, depth)` with the 2-arg form — `sig` defaults to `nil`. `Quote.reify`'s `{:vdata,...}` clause (quote.ex:64-92) needs `sig` to split a data value's flattened args back into `(params, indices)`; with `sig = nil` it puts EVERYTHING into `params` and leaves `indices = []` (quote.ex:85). This is harmless ONLY because Sigma has zero indices (`Inductive.family(:Sigma, [a:.., b:..], [], 0)`) — the "everything is params" default happens to be exactly correct when there are no indices to lose. Do NOT generalize this checked-tuple pattern to any future INDEXED builtin family without first passing `sig` through `normalize`/`reify` — for a family with real indices, the 2-arg `Kernel.normalize` call used here would silently mis-split params vs indices.

Scope-based `%[..]` (elaborator.ex:4715-4724 `elaborate_expr({:tuple,…})`): emit `{:ctor, mk_pair, [a_core, b_core]}` (resolve `mk_pair` the same registry way; if `Inductive.builtin` needs an env the scope-builder lacks, thread or resolve at the caller — report which). Branch-body tuple (elaborator.ex:3557) routes through checked — inherits Step 2. `declarations.ex` `elaborate_body` tuple fallback (declarations.ex:344-361): the checked call inherits the change; the FALLBACK branch (:355-360, reached only when checked errors — no codomain in hand, spec §2.2 as review-corrected) becomes `{:ok, {:ctor, mk_pair, [a_term, b_term]}}`.
- [ ] **Step 3 (T2a types):** `idx_to_core({:sigma_type, [binder: bname], [dom_ast, body_ast]}, …)` (declarations.ex:974-979): body was elaborated with `bname` in scope (`[bname | scope]`) — de Bruijn frame already matches one lambda binder:

```elixir
  defp idx_to_core({:sigma_type, [binder: bname], [dom_ast, body_ast]}, scope, fam, env, _ctx) do
    with {:ok, dom} <- idx_to_core(dom_ast, scope, fam, env),
         {:ok, body} <- idx_to_core(body_ast, [bname | scope], fam, env) do
      {:ok, {:data, :Sigma, [dom, {:lam, dom, body}], []}}
    end
  end
```

(Resolve `:Sigma` via registry if an env-independent atom is wrong here — `idx_to_core` HAS `env`; use `Inductive.builtin(env, :sigma)` and STOP if nil.) `type_to_core` twin (declarations.ex:1195-1200): same reshape; its telescope is non-dependent (no binder in scope, review-verified) so the wrap is a constant lambda — same code, different justification, keep the existing rejection comment accurate.
- [ ] **Step 4 (T2b Step 1 — projection naming decision, read-only):** the projections must be callable as globals from elaborator-generated Core. Decide between: (a) `first`/`second` in `Std.Sigma` — check what global atom a `Std.Sigma` def gets (read how `Std.Pair`'s `first` is keyed in the env and what task #10's collision machinery does with the `Std.Pair.first` clash: grep `resolution.ex` re-keying + the collision-fix tests); (b) collision-free names `sigma_first`/`sigma_second` (surface users never type them — `.1`/`.2` is the surface). Pick whichever yields an unambiguous `{:global, atom}` the emit hook can key on; document the choice in the commit message. If BOTH fail (no resolvable unambiguous atom): STOP.
- [ ] **Step 5 (T2b):** `sigma_projection/5` (elaborator.ex:670-676) — replace the primitive node with the ctx-threading wrapper (`elaborate_implicit_global_app`) over the chosen global (surface AST in, full implicit spine out):

```elixir
  defp sigma_projection(which, inner, names, ctx, env) do
    gname = if which == :fst, do: <proj1_atom>, else: <proj2_atom>
    Cure.Elab.Elaborator.elaborate_implicit_global_app(env, gname, [inner], names, ctx)
  end
```

(It already returns `{:ok, term, result_type}` — the same contract, review-verified at elaborator.ex:670-675: `sigma_projection` today returns `{:ok, term, type}` and `elaborate_implicit_global_app` returns `{:ok, term, result_type}` — identical shape. `elaborate_implicit_global_app` is in THIS module; drop the module prefix.) The literal-tuple β-shortcut (elaborator.ex:423-433) is representation-independent — UNTOUCHED.

Type-position `p.1`/`p.2` (`idx_to_core` attribute_access, declarations.ex:1007-1028): replace `{:fst|:snd, inner}` (lines 1020-1021) with the same projection-global spine.

CONFIRMED (traced by hand, not assumed): the ctx-threading is real and DOES reach this exact clause. `function_signature` builds a real `ctx` via `build_context(env, telescope)` (declarations.ex:547-561) and threads it into `idx_to_core` for RETURN-TYPE positions only (declarations.ex:861-868's doc comment, "spec 2026-07-08 §7.3"; every other caller keeps the 4-arg form → `ctx` defaults to `nil`, declarations.ex:869). For a `function_call` node whose head is a plain type family (e.g. `SF(as, bs, p.1)` — `SF` is a family, not `implicit_global?`, since "families/ctors never carry def quantities" per the comment at :899-900), control falls to `map_idx_to_core(args, scope, fam, env, ctx)` (declarations.ex:908), which forwards the SAME non-nil `ctx` to every argument, including `p.1` (`map_idx_to_core/5`, declarations.ex:1093-1100, calls `idx_to_core(e, scope, fam, env, ctx)` per element). So `idx_to_core` reaches the attribute_access clause (declarations.ex:1007) with a genuine, usable `Context.t()` in exactly the `sigma_surface_test.exs:52`-style fixture the plan's own T2 Step 1 red test #3 exercises.

The CURRENT bug (today, harmless, because today's `.1`/`.2` build the ctx-free primitive `{:fst,inner}`/`{:snd,inner}` node): the clause head pattern is `defp idx_to_core({:attribute_access, ...} = node, scope, fam, env, _ctx)` — it discards whatever `ctx` arrives, by naming it `_ctx`. The fix must (a) stop discarding it — rename to `ctx` in the head — and (b) when `ctx != nil`, route through `elaborate_implicit_global_app(env, gname, [inner_ast], scope, ctx)` exactly as `sigma_projection` does (surface AST in, not the already-lowered `inner` term — do not call `idx_to_core(inner_ast, ...)` first). This ctx-available branch is NOT optional or deferred — it is REQUIRED for T2 Step 1's red test #3 (and for `sigma_surface_test.exs:52`'s existing "recover" fixture) to pass, since ctx is confirmed non-nil there.

The remaining, genuinely open sub-case is ctx **actually nil** — a `.1`/`.2` in an index/type position that is NOT reached via a threaded return-type ctx (e.g. a family's INDEX telescope position, which `idx_to_core` lowers via the 4-arg form with no ctx at all). Report whether any existing test exercises `p.1` in such a non-return-type position; if none, leave that sub-case erroring with a precise tag and note it as a spec §7.5-class residual — do NOT guess a frame.
- [ ] **Step 6:** run scoped: `mix test test/cure/elab/sigma_inductive_test.exs` — shape tests green (runtime test still red until T3, expected). Then `mix test test/cure/elab/` — pre-existing surface tests (sigma_surface, sigma_field, tuple_pattern, tuple_scrutinee_match, dependent_construction, dependent_routing) must be green EXCEPT enumerated Core-shape pins; authorized flips here (each because the Core shape legitimately changed, behavior identical): `sigma_surface_test.exs:40` `{:pair,…}` → ctor shape; `sigma_surface_test.exs:52` `{:snd,_}` → projection-global/case shape. Any OTHER failure = investigate; genuine behavior change = STOP.
- [ ] **Step 7:** run `mix test test/oracle_replay_test.exs` — all verdicts unchanged (dpair/sg/mt13-19/er02 are the sensitive rows). Divergence = STOP.
- [ ] **Step 8:** commit: `feat(elab): lower Sigma surface to the builtin inductive — %[..]:=mk_pair, Sigma(..):=data, .1/.2:=projection globals (D2 T2)`.

---

### Task 3: emit/erase builtin hooks (ABI preservation)

**Files:** Modify `lib/cure/elab/emit.ex`; Test: the T2 Step 1.4 runtime test + `test/cure/e2e/frp_beam_test.exs` + `test/cure/compiler/dependent_surface_codegen_test.exs` (existing, immutable — the ABI gate).

- [ ] **Step 1 (red carried):** T2's runtime test is red (pairs currently emit TAGGED `{:mk_pair, A, B}` through the generic ctor path, emit.ex:158-175).
- [ ] **Step 2:** add the registry hook (pattern `nat_ctor?`, emit.ex:404-406):

```elixir
  # The canonical Sigma family (registry-keyed, nominal): its values are the bare
  # BEAM 2-tuples the primitive pair always compiled to (spec 2026-07-09 D2 §1.5)
  # — Std.Pair's element/2 interop and AtomVM depend on the untagged shape.
  defp sigma_ctor?(env, name) do
    fam = Inductive.builtin(env, :sigma)
    fam != nil and Inductive.ctor_family(env, name) == fam
  end
```

In `lower(env, {:ctor, name, args}, ctx)` add a branch BEFORE the generic tagged case: `sigma_ctor?(env, name) -> {:tuple, @line, Enum.map(args, &lower(env, &1, ctx))}` (arity is always 2 — both fields present). In `branch_clause/3`: `sigma_ctor?` → a clause whose pattern is `{:tuple, @line, [v0, v1]}` binding both fields into the de Bruijn frame (adapt `generic_branch_clause`'s fresh-var/underscore logic — read it fully first; erased-field handling is moot, both present).

Projection globals — CORRECTED framing (review-verified against erase.ex, the original "spine head ... value argument last" framing was wrong): `function_form` (emit.ex:121-135) runs `Erase.erase(env, body)` ONCE, before any `lower/3` recursion — by the time emit.ex's `lower({:app,...})` sees a call, erasure has ALREADY happened. `Erase.erase`'s application clause (erase.ex:42-63) drops every arg whose formal quantity is `:erased` and rebuilds the spine from what's left (`Enum.reduce({:global, name}, fn arg, acc -> {:app, acc, arg} end)`, erase.ex:59-63). `first`/`second` have quantities `[:erased, :erased, :present]` — so a SATURATED surface call `first({a},{b},p)` is, by the time emit.ex runs, already the single-argument node `{:app, {:global, :first}, p}` — there is no 3-slot spine with implicits still visible to detect "value argument last" within. The correct hook is NOT a multi-arg spine match; it is a 1-argument match mirroring `connective_inline`'s existing 1-arg `{:global, :not}` clause (emit.ex:220-241): when the `{:app,...}` head is `{:global, <proj1_atom>}` (resp. proj2) applied to exactly one argument `P`, emit `element(1|2, P)` (reuse `element/2`, emit.ex:304-306). A reference to `first`/`second` with 0 arguments (the bare global passed as a value, not called) is the only "unsaturated" case at this arity and keeps the plain global reference.
- [ ] **Step 3:** run scoped: T2 runtime test green; then `mix test test/cure/e2e/frp_beam_test.exs`, then `mix test test/cure/compiler/dependent_surface_codegen_test.exs` (one at a time) — green UNCHANGED (these pin the 2-tuple ABI; a failure = ABI break = fix before proceeding, never flip these).
- [ ] **Step 4:** commit: `feat(emit): sigma builtin hooks — bare 2-tuple ctor/branch lowering + element/2 projection inlining (D2 T3)`.

---

### Task 4a: validator `no_sigma_node` at `:warn`

**Files:** Modify `lib/cure/core/validator.ex`; Test: `test/cure/core/validator_test.exs` (locate; add clauses following its no_eq_node cases).

- [ ] **Step 1 (red):** add validator tests: each of the four nodes yields a `no_sigma_node` diagnostic at `:warn` in wave0 and `:reject` in `release_config` (mirror the existing no_eq_node test shape). Run scoped: fails (clause unknown).
- [ ] **Step 2:** `@clauses` gains `:no_sigma_node`; `@wave0_config` gains `no_sigma_node: :warn`; `@release_config` chain gains `|> Map.put(:no_sigma_node, :reject)`; predicates next to the eq ones:

```elixir
  defp violation(:no_sigma_node, {:sigma, _, _}),
    do: "primitive :sigma node; use inductive Sigma (D2)"

  defp violation(:no_sigma_node, {:pair, _, _}),
    do: "primitive :pair node; use ctor mk_pair (D2)"

  defp violation(:no_sigma_node, {:fst, _}), do: "primitive :fst node; use projection (D2)"
  defp violation(:no_sigma_node, {:snd, _}), do: "primitive :snd node; use projection (D2)"
```

KEEP the `children` walker clauses for sigma/pair/fst/snd (descend-and-report, eq precedent) PERMANENTLY, even past `:reject` — only the 4-tuple grade clause dies later (T5). Precise anchors (review-verified, the scout's line-range for T5 is WRONG — see T5 Step 2's corrected text): `children({:sigma, a, b})` at validator.ex:110 is the 3-tuple descend-walker (KEEP forever); `children({:sigma, _grade, a, b})` at validator.ex:111 is the actual 4-tuple grade clause (this is the one that dies, in T5); `children({:pair, a, b})`/`children({:fst, p})`/`children({:snd, p})` at :113-115 (KEEP forever, same as :110).
- [ ] **Step 3:** run scoped validator tests green, then `mix test test/cure/core/` — green (warn mode must not fail anything; Antigen still legitimately builds primitive nodes until T6 — `:warn` is why the ratchet has two stages).
- [ ] **Step 4:** commit: `feat(validator): no_sigma_node clause at :warn (D2 T4a)`.

---

### Task 5 (executed AFTER Task 6 and Task 7 — order per spec §5): kernel/core + traversal strip

**Files:** Modify (removal-only): `lib/cure/core/{kernel,eval,quote,conv,normalise,term,serialize,value,inductive,certificate,meta_check,validator}.ex`; `lib/cure/elab/{elaborator,unify,subst,resolution,relevance,totality_closure,erase}.ex`; `test/cure/elab/dependent_eliminator_test.exs` (retire the §2.4 pair-crash test HERE, in this commit — spec §1.3 requires it die "in the same commit" as `kernel.ex:125-128`'s defensive clause, not earlier; T7 explicitly does NOT touch this file, see T7 Files note). Tests: the T7-rewritten suites are the green gate; NO other new tests (deletion task).

- [ ] **Step 1:** re-verify zero producers remain: shape-aware grep for constructors (`{:sigma,` with 2 commas, `{:pair,` 2-element, `{:fst,`/`{:snd,` 1-element, `{:vpair`, `{:vsigma`, `{:nfst`, `{:nsnd`) across `lib/cure/core/ lib/cure/elab/ lib/antigen/` EXCLUDING the consumer/traversal clauses this task deletes. Any producer left (a test env builder, a forgotten branch) → fix it FIRST (that's a T2/T6 escape, not a strip candidate).
- [ ] **Step 2:** strip, per the scout §1/§3 inventory (removal-only; re-locate every anchor by code): kernel.ex — `infer` sigma formation (:100), fst (:109), snd (:116-123), the D1 defensive pair clause (:125-128), `check` pair (:257), `ensure_sigma` (:474), `infer_type_value_sort` vsigma (:677), `rigid_index?` sigma (:947), `replace_branch_vars` arms (:1022-1032). **The napp clause (~:636) STAYS — spec §1.3.** eval.ex :33-37, :150-154. quote.ex :54-59, :102-103. conv.ex :82, :88, :129-130, :170-171. normalise.ex :156-164, :181-182, :255-264, :304-313 (the ncase arms directly above each STAY). term.ex :18-20 docs, :54-57, :102-106, :136, :176-182, :214-221, :270-276. serialize.ex :27-30, :153-156 (ONLY after T6's corpus migration is committed). value.ex :17-18, :28 docs, :45-46, :61-62. inductive.ex :311, :374-378. certificate.ex :189-196, :579-583 walker arms. meta_check.ex :46, :51-52. validator.ex: ONLY the 4-tuple grade clause `children({:sigma, _grade, a, b})` (:111) and `grade_on_binders` sigma (:184). Do NOT delete :110/:113-115 (`children({:sigma,a,b})`/`children({:pair,a,b})`/`children({:fst,p})`/`children({:snd,p})`) — those are the descend-and-report walker T4a said to keep permanently (spec §2.4); the scout's original "(:110-115)" range was wrong (it swept in the 3-tuple clauses along with the 4-tuple one) — this is the corrected anchor — but the `no_sigma_node` PREDICATES stay (T4b flips them to :reject). Elab traversals: elaborator.ex :602, :739, :1185-1186, :1226, :2034-2044, :3929-3939, :4660-4663; unify.ex :128, :253-257, :301 (FIRST confirm the Σ–Σ congruence is exercised by a dpair-cluster replay AFTER T2 — i.e. nothing reaches it anymore; if replay only passes WITH it, a producer escaped Step 1), :393-399; subst.ex :53-63, :97-107; resolution.ex :35-39; relevance.ex :122-127, :172; totality_closure.ex :82-86. erase.ex: delete the sigma/pair/fst/snd clauses ONLY — the `{:pi,…}` clause at :83 and `{:app,…}` at :141 sit BETWEEN them and MUST SURVIVE (spec §2.3 as review-corrected; delete by exact clause, never by range).
- [ ] **Step 3:** run `mix test test/cure/core/` then `mix test test/cure/elab/` then `mix test test/antigen/` (one at a time) — all green (T6/T7 already migrated everything that referenced the deleted forms).
- [ ] **Step 4:** relevance probe (spec §2.2 last bullet): confirm a dependent `Sigma(n: Nat, Vector(a, n))`-style def still passes relevance (no spurious erased-binder-use on the `b` param) — it's covered by the T2 suite being green here; note explicitly in the report.
- [ ] **Step 4b:** delete TWO pins together, in this commit (both guard the exact clause deleted in Step 2, so both retire with it per spec §1.3's "same commit"): (1) `dependent_eliminator_test.exs`'s §2.4 pair-crash test (the one asserting `{:error, :pair_not_inferable}`/`:bad_motive` rejection with no `FunctionClauseError`, pinning `kernel.ex:125-128`); (2) the Malformed napp seed's Nat-head reject row referenced in T6 Step 5 (locate it — an Antigen seed/mutation-test pin exercising the same defensive clause; T6 Step 5 left it in place deliberately for this task). Both WITH a note: the node leaves the grammar in this same commit, a strictly stronger guarantee than the clean rejection either pin checked (the adversarial term becomes inexpressible, not just rejected) — spec §1.3. Run the affected files' remaining tests green.
- [ ] **Step 5:** commit: `refactor(kernel)!: strip primitive Sigma from Core — grammar, judgements, values, neutrals (D2 T5)`.

---

### Task 6 (executed after T4a, before T7): Antigen migration

**Files:** the scout §6 table is the authoritative checklist — `lib/antigen/generators/{term,sig_menu,mutation,conv_pair,equality,dep_match,check_mode,type_former,positivity,totality,delta_reduce,beta_subst,surface_expr}.ex`, `lib/antigen/assays/{delta_reduce,unifier,totality_closure_assay}.ex`, `lib/antigen/{shrink,runner}.ex` (shrink/runner traversal arms may defer to T5), `test/antigen/seeds.sexp`, `test/antigen/corpus.sexp`, the antigen test-side pins. Test: the EXISTING Antigen suite is the oracle; plus one NEW antibody file.

- [ ] **Step 1 (port-first guard):** `delta_reduce` (generator :27-37 + assay :25 `kpair : {:sigma,Nat,Nat}` certified global): re-encode as the inductive — `kpair : Sigma(Nat, const-Nat)` via ctor, projections as single-branch cases; run `mix test test/antigen/` scoped to its assay tests RED-GREEN (these guard the Θ(2ᵈ)-avoidance δ+ι engine BEFORE its nfst/nsnd arms die in T5; the ncase arms take over).
- [ ] **Step 2:** migrate the generators, file by file (each: re-encode Σ goals/fields as `{:data, :Sigma, [dom, b], []}`, pair intros as ctor, projections as single-branch `:case` with the appropriate motive; the D1 `neutral_app_motive_case` and sig_menu conventions are the frame reference): term.ex (intro :135-145, elim :356-358, check-mode-only marker :69), sig_menu.ex (:32, :116, :215-236), dep_match.ex (:40, :93, :98, :103-104), check_mode.ex (:33-35), type_former.ex (:50 — level-0 data former; a former above level 0 is PRUNED per spec §1.1), positivity.ex (:61-70, :200, :211; `sigma_negative_family` :284-289 re-encoded as an inductive-Sigma negative or an equivalent non-Σ negative-position family), totality.ex (:114ff), beta_subst.ex (:42 σ-law row → a `{:data,:Sigma,…}` shift row), equality.ex (:109, :119-121 neutral endpoints → case-neutrals), surface_expr.ex (:46 tuple encoder → ctor), mutation.ex (:102, :124, :163, :189, :251 → inductive-shaped malformations: ill-typed case on non-Sigma scrutinee, wrong-component ctor, Σ-goal via data).
- [ ] **Step 3 (corpus):** investigate how seeds.sexp/corpus.sexp are (re)generated — `git show 11ea830` is the precedent (the `:rewrite` retirement migrated the serialization shape menu). Regenerate or migrate the 132+3 serialized primitive-node seeds to inductive shapes; keep serialize.ex decode clauses ALIVE until this commit lands (T5 ordering). Check serialize.ex's other consumers (grep callers) for wire-form dependence.
- [ ] **Step 4 (new antibody — CONFIRMATORY, not a TDD driver; testing-discipline note):** written and run AFTER Steps 1-3 have already migrated the generators/corpus, so this file is expected to be GREEN on first run, not red-then-green — if it comes up red, that is a residual migration gap from Steps 1-3 to fix, not new behavior for this step to drive. `test/antigen/sigma_retirement_test.exs`: (a) positive — the seeded builtin Sigma round-trips under the property families (a `{:data,:Sigma,…}`-typed challenge with ctor intro + case elim runs through the standard corpus assay green); (b) the D1 napp accept-pin still holds post-migration (motive `b(m)` over context type-family, NOT `:bad_motive`); (c) ratchet pin — a hand-built primitive `{:sigma,…}` term fed to `Validator` yields the `no_sigma_node` diagnostic (`:warn` now; T4b flips config, the test asserts via `release_config` so it is ALREADY `:reject` there — no flip needed later).
- [ ] **Step 5:** `mix test test/antigen/` — FULL antigen green (test-side pins in challenge/corpus/coverage/mutation_health_gate/generator tests updated where they pin generator OUTPUT SHAPES — enumerate each flip with justification "generator now emits inductive shape"). The retired D1 §2.4 pair-crash pin (`dependent_eliminator_test.exs` pair test + the Malformed napp seed's Nat-head reject row) are NOT touched here — they still pass while the nodes exist; T5 handles their retirement with the node (moved from T7, review-corrected — spec §1.3 requires "the same commit" as the clause deletion; see T5 Files/Step 4b).
- [ ] **Step 6:** commit: `test(antigen): migrate Sigma seeding to the builtin inductive + retirement antibody (D2 T6)`.

---

### Task 7 (after T6, before T5): test/example/docs sweep

**Files:** rewrite `test/cure/core/sigma_test.exs`; enumerated pin flips in `test/cure/core/{eval,quote,serialize,term,value,stuck_elim_delta}_test.exs`, `test/cure/elab/{miller_unify,unify_meta_completeness}_test.exs`; a doc/comment-only update (NOT a pin flip — review-verified: `subject_reduction_test.exs`'s `@corpus` currently has ZERO sigma/pair Core-shape assertions to flip, only a stale comment excluding sigma/pair terms "until a later wave" — update that comment to reflect the retirement, nothing to flip); rewrite `examples/sigma_pairs.cure`; update the parity-ledger roadmap spec §2 Sigma row. **`test/cure/elab/dependent_eliminator_test.exs`'s §2.4 pair-crash test is NOT retired here** — spec §1.3 requires it die "in the same commit" as the kernel clause it pins (`kernel.ex:125-128`), so its retirement moved to T5 (see T5 Files/Step 2/Step 5 below); T7 does not touch this file.

- [ ] **Step 1:** rewrite `sigma_test.exs` as the inductive-Sigma kernel suite: formation (family app sorts at level 0), intro (ctor checks against `{:data,:Sigma,…}`), dependent snd via case + napp motive, ι-reduction (`Normalise.nf` of a projection-case on a ctor), mismatch negative. The old untyped-`{:pair,{:type,0},{:type,1}}` iota sub-test is DROPPED (review-verified untranslatable under the level-0 haircut — note in the commit message).
- [ ] **Step 2:** flip the enumerated Core-shape pins file by file (each flip = one line in the report: file:test, old shape → new shape, justification). `stuck_elim_delta`'s nfst/nsnd δ rows re-encode over case-neutrals (T6 Step 1 already proved the engine equivalent). serialize_test rows for sigma/pair/fst/snd become NEGATIVE decode tests only AFTER T5 (do the positive-row removal here, add the "unknown node" negative in T5 if serialize has that behavior — check how it handles unknown tags first). Named flips confirmed by direct read (do these; both files DO contain literal Core-shape assertions, unlike `subject_reduction_test.exs` — see Files note above): `miller_unify_test.exs:76,79` — constructed `{:sigma,...}` Core terms feeding a `Unify.zonk` assertion → flip to `{:data,:Sigma,...}` construction, same zonk assertion, justification "Sigma is now a data node, zonk behavior unchanged for a rigid family head". `unify_meta_completeness_test.exs:36-39` — 4 literal zonk-equality assertions on `{:sigma,...}`/`{:pair,...}`/`{:fst,...}`/`{:snd,...}` → flip each to its `{:data,:Sigma,...}`/`{:ctor,:mk_pair,...}`/projection-global-spine equivalent, same justification (representation change only, unification behavior over the new shapes is unchanged since both are ordinary rigid/ctor/neutral-spine forms already handled generically).
- [ ] **Step 3:** rewrite `examples/sigma_pairs.cure` to demonstrate actual dependent Sigma (declare via `Sigma(n: Nat, Vector(Nat, n))`-style return, construct with `%[..]`, project with `.1`/`.2`), keeping it host-compilable (read `examples/` conventions; no start needed if the file is illustrative — match whatever the example set does).
- [ ] **Step 4:** `mix test test/cure/` — green. `mix test test/oracle_replay_test.exs` — verdicts unchanged.
- [ ] **Step 5:** commit: `test: inductive-Sigma kernel suite + pin flips + sigma_pairs example rewrite (D2 T7)`.

---

### Task 8: T4b validator `:reject` + full gate + final verification

- [ ] **Step 1:** flip `@wave0_config` `no_sigma_node: :warn → :reject` (mirror the no_eq_node Phase-C comment style: the kernel has no clauses left, a node is smuggled grammar). Run scoped validator tests.
- [ ] **Step 2 (full gates, ONE at a time, alone, in order):** 1. `mix test test/antigen/` — green (count re-derived, expect prior + drift test + retirement antibody − any retired pins; report exact). 2. `mix test` — green, 0 failures (count re-derived and explained vs the 3249 baseline: NEW tests added (T1 drift, T2 suite, T6 antibody, T7 rewrites) minus retired (§2.4 pair pin, untranslatable iota row, …) — every delta enumerated). One known non-reproducible Antigen-seed flake rule applies.
- [ ] **Step 3 (final verification):** from `<pre-d2-commit>`:
  - Shape-aware grep (spec §3.5): zero `{:sigma,`/`{:vsigma`/`{:vpair`/`{:nfst`/`{:nsnd` constructors under `lib/cure/core/` + `lib/cure/elab/` (pair/fst/snd verified by `Term.term?` + validator `:reject`, not grep — surface look-alikes exist).
  - `git diff --stat <pre-d2-commit> HEAD -- lib/cure/types/ lib/cure/compiler/` — EMPTY.
  - The D1 napp clause present (grep `napp` kernel.ex) and its antibody green.
  - `git log --format='%an %ae' <pre-d2-commit>..HEAD` — ghost author only.
  - Oracle replay green, zero verdict changes.
- [ ] **Step 4:** commit the flip: `feat(validator): no_sigma_node -> :reject — primitive Sigma fully retired (D2 T4b)`. Update the parity-ledger roadmap row + memory notes per its instructions.

---

## Self-review notes (spec-coverage map)

- §1.1 haircut → T6 type_former prune + T7 iota-row drop. §1.2 grade forms → T5 validator/meta_check strips. §1.3 napp survives / defensive dies → T5 Step 2 + Task 8 Step 3; §2.4 pin retirement → T5 Step 4b (review-corrected: moved from T7 to T5 — spec §1.3 requires "the same commit" as the clause deletion, so it cannot land in an earlier task). §1.4 registry lookups → T2/T3 hooks. §1.5 ABI → T3 + its immutable gate. §1.6 seed+decl+drift → T1. §1.7 invariance → T2 Step 7, T7 Step 4, Task 8. §1.8 ordering → task numbering (T5 after T6/T7; serialize strip gated on corpus migration). §1.9/§4 non-goals — no task touches them. §2.2 producer list → T2 (incl. the review-corrected fallback-branch and type_to_core notes). §2.3 erase per-line discipline → T5 Step 2. §2.4 ratchet → T4a/T4b. §2.6 checklist → T6. §2.7 → T7. §3 gate → Task 8. §3.4 no-oracle-run → Global Constraints. §3.5 grep semantics → Task 8 Step 3 (review-corrected: term?/validator authoritative for pair/fst/snd).
- Known decision points left in-task by design (each with STOP fallback): T2b projection naming (Step 4), `Inductive.ctor/5` convention (T1 Step 2, drift test arbitrates), corpus regeneration mechanism (T6 Step 3, 11ea830 precedent), serialize unknown-tag behavior (T7 Step 2).
- Latitude: surface framing of NEW tests; exact de Bruijn frames in T1 seed and T6 generator re-encodings (iterate against drift/property tests, which are immutable); enumerated pin flips ONLY as listed with per-flip justification; gate-count re-derivation. All report-required.
