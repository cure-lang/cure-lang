# Unified Tuple (non-dependent, scope A) — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Give the dependent pipeline an honestly-typed surface tuple — `Tuple(T, U, …)` over the flat BEAM tuple — so the value-surface stdlib (`Std.List`, `Std.Tuple`, `match`) compiles on the dependent pipeline. This is scope **(A) minimal-honest** from `2026-07-09-unified-tuple-design.md`; the dependent `Tele`/`NonDep` layer (scope **B**) lands *immediately after #18* (operator decision 2026-07-10) and is out of scope here.

**Architecture:** Two increments. **Increment 1 (arity-2):** `Tuple(T, U)` is a *parser alias* for the existing non-dependent `Sigma(_: T, U)` — which already elaborates and emits a flat 2-tuple `{a,b}` — so arity-2 needs zero new elaboration/emit/TCB. **Increment 2 (arity ≥ 3):** per-arity flat inductive families `Tuple3…Tuple8` (ordinary inductives, exactly how Haskell/Rust/OCaml bound tuples; zero kernel change), with `%[a,b,c]` → `mk_tupleN(a,b,c)` distinguishable from nested `%[a,%[b,c]]` → `mk_tuple2(a, mk_tuple2(b,c))`, all emitting flat `{…}`.

**Tech Stack:** Elixir; Cure dependent elaborator (`lib/cure/elab/*`) + kernel (`lib/cure/core/*`); shared parser (`lib/cure/compiler/parser.ex`). Spec: `docs/superpowers/specs/language/2026-07-09-unified-tuple-design.md`.

## Global Constraints

- **Ghost-writer commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, NO `Co-Authored-By`, no Claude signature.
- **Explicit-pathspec staging only:** `git add -- <path>`; NEVER `git add -A`/`git add .` (a concurrent agent shares this worktree).
- **Branch:** stay on `autopilot/kernel-parity-batch` (no new worktree).
- **One build at a time.** Never run two `mix` suites concurrently. Prefer scoped `mix test <file>`; full suite once, alone, at the gate. **Warnings are errors under `mix test`** — keep clauses of the same function contiguous, no unused vars.
- **Strict red-green TDD.** Failing test first, watch it fail for the right reason, minimal implementation, green, commit. Behavioural tests (elaborate real `.cure`; assert Core shape and/or run emitted BEAM), not implementation-coupled.
- **Tests immutable once green** unless a test provably encodes wrong behavior (state why first).
- **Two pipelines:** dependent machinery is ONLY `lib/cure/elab/*` + `lib/cure/core/*`. The shared frontend `lib/cure/compiler/{lexer,parser}.ex` IS in scope. IGNORE `lib/cure/compiler/{codegen,pattern_compiler}.ex` and `lib/cure/types/*` (classic decoys — their `Tuple`/tuple handling is a trap).
- **TCB discipline:** **no `lib/cure/core/*` change is anticipated** — arity-2 reuses Sigma; n-ary uses ordinary inductive families. A native variadic tuple Core node would be a TCB change that does NOT align with Agda/Lean (they use nested Σ), so it is **forbidden** here. If a kernel change seems necessary, STOP and report (red-green + Antigen antibody + full Antigen suite gate; pre-approved only if it aligns with Agda/Lean).

## File Structure

- `lib/cure/compiler/parser.ex` — `Tuple(…)` type-position parsing (Task 1: arity-2 → `sigma_type`; Task 3: n-ary). Anchors: type dispatcher `parser.ex:4585`, `parse_sigma_type` `parser.ex:4629`.
- `lib/std/list.cure` — `uncons` → `Option`, `split_first` → honest `Tuple(t, List(t))` (Task 2).
- `lib/std/tuple.cure` *(new, Task 3/Increment 2)* — `Std.Tuple` honest API; `Std.Pair` deprecation is a **follow-on** (§Deferred).
- `lib/cure/core/builtins.ex` — seed `Tuple3…Tuple8` families + `@schemas` entries (Task 4). Anchors: `@schemas` `builtins.ex:14-25`, `seed/2` `builtins.ex:116-125`, `sigma_family/0` `builtins.ex:258`.
- `lib/cure/elab/elaborator.ex` — n-ary literal elaboration (Task 4) + n-ary projection `.i` (Task 5). Anchors: checked tuple clause `elaborator.ex:1137-1160`, synth `elaborator.ex:5129-5134`, projection dispatch `elaborator.ex:465-471`, `sigma_projection` `elaborator.ex:857`.
- `lib/cure/elab/emit.ex` — n-ary flat ctor emit + `.i` inline + n-ary branch (Task 4/5). Anchors: sigma ctor emit `emit.ex:199-200`, projection inline `emit.ex:392-396`, `element/2` builder `emit.ex:449-451`, `sigma_branch_clause` `emit.ex:473-481`, `sigma_ctor?` `emit.ex:644-647`.
- `lib/std/match.cure` — migrate its arity-3 literals/patterns onto the n-ary surface (Task 6).
- `test/cure/elab/*`, `test/cure/stdlib/*` — tests per task.

**Task dependency order:** 1 → 2 (Increment 1, independently shippable) → 3 → 4 → 5 → 6 (Increment 2). Each task ends green and committed before the next.

---

## Increment 1 — Arity-2 honest `Tuple` (the #18 unblock)

### Task 1: `Tuple(T, U)` type surface (parser alias → non-dependent Sigma)

**Files:** Modify `lib/cure/compiler/parser.ex` (type dispatcher ~4585; add `parse_tuple_type` beside `parse_sigma_type` ~4629). Test: `test/cure/elab/tuple_type_surface_test.exs` (new).

**Interfaces:**
- Produces: a type-position `Tuple(dom, body)` parses to `{:sigma_type, [binder: "_"], [dom_ast, body_ast]}` (non-dependent, binder unused); `Tuple(x: dom, body)` parses to `{:sigma_type, [binder: "x"], [dom_ast, body_ast]}` (dependent arity-2, later position may name `x`). Both reuse `type_to_core({:sigma_type, …})` (`declarations.ex:1477`) and `idx_to_core` (`declarations.ex:1187`) unchanged — no elaborator change.

- [ ] **Step 1: Write the failing test**

```elixir
defmodule Cure.Elab.TupleTypeSurfaceTest do
  # `Tuple(T, U)` is the honest arity-2 surface tuple type. Increment 1 makes it a
  # parser alias for the existing non-dependent Sigma, so `%[a,b]` already
  # elaborates/emits against it (probe A confirmed arity-2 works vs a defined Sigma).
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  test "a fn returning Tuple(Int, Int) elaborates and emits a flat 2-tuple" do
    src = """
    mod M
      fn mk(a: Int, b: Int) -> Tuple(Int, Int) = %[a, b]
      fn fst(a: Int, b: Int) -> Int = mk(a, b).1
      fn snd(a: Int, b: Int) -> Int = mk(a, b).2
    """
    assert {:ok, env} = Program.elaborate(src)
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.M", functions: [:mk, :fst, :snd])
    assert apply(m, :mk, [7, 9]) == {7, 9}
    assert apply(m, :fst, [7, 9]) == 7
    assert apply(m, :snd, [7, 9]) == 9
  end

  test "dependent arity-2 Tuple(m: Nat, Vector(Int, m)) still checks the later position" do
    src = """
    mod M
      type Nat = Zero | Suc(Nat)
      type Vector(a: Type) indices (n: Nat)
        empty : Vector(a, Zero)
        prepend : a -> Vector(a, n) -> Vector(a, Suc(n))
      fn one(v: Vector(Int, Suc(Zero))) -> Tuple(m: Nat, Vector(Int, m)) = %[Suc(Zero()), v]
    """
    assert {:ok, _env} = Program.elaborate(src)
  end
end
```

- [ ] **Step 2: Run it, watch it fail**

Run: `mix test test/cure/elab/tuple_type_surface_test.exs`
Expected: FAIL — `Tuple(Int, Int)` at type position is parsed as an ordinary `{:function_call, [name: "Tuple"], …}` and elaborates to an unknown/unbound type (`:unknown_global` / `ctor_requires_checking_mode`), because only `Sigma(…)` is special-cased in the type dispatcher.

- [ ] **Step 3: Add the `Tuple(…)` type dispatch + `parse_tuple_type`**

In `parser.ex`, at the type-position dispatcher (~4585, beside the `base_name == "Sigma"` arm), add:
```elixir
base_name == "Tuple" and match?(%Token{type: :lparen}, peek(state)) ->
  parse_tuple_type(state)
```
Add `parse_tuple_type/1` beside `parse_sigma_type/1` (~4629). For Increment 1 it accepts **exactly two** positions (n-ary is Task 3), each optionally binder-named:
```elixir
# Tuple(T, U) — non-dependent arity-2 (binder "_"); Tuple(x: T, U) — dependent
# arity-2 (later position may mention x). Both alias to the existing sigma_type
# node so type_to_core/idx_to_core need no change. Arity != 2 is deferred to the
# n-ary path (Task 3) and until then errors via the normal too-many/few tokens.
defp parse_tuple_type(state) do
  state = advance(state)
  {binder, state} =
    case {peek(state), peek_at(state, 2)} do
      {%Token{} = t, %Token{type: :colon}} ->
        s = advance(advance(state))
        {to_string(t.value), s}
      _ ->
        {"_", state}
    end
  {dom_type, state} = parse_type_expr(state)
  state = expect(state, :comma)
  {body_type, state} = parse_type_expr(state)
  state = expect(state, :rparen)
  {{:sigma_type, [binder: binder], [dom_type, body_type]}, state}
end
```

- [ ] **Step 4: Run green**

Run: `mix test test/cure/elab/tuple_type_surface_test.exs`
Expected: PASS (2 tests).

- [ ] **Step 5: Scoped regression + commit**

Run: `mix test test/cure/compiler/ test/cure/elab/`
Expected: PASS.
```bash
git add -- lib/cure/compiler/parser.ex test/cure/elab/tuple_type_surface_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(parser): Tuple(T,U) type surface aliases non-dependent Sigma (arity-2)"
```

---

### Task 2: `Std.List.uncons` → `Option`, `split_first` honest; `use Std.List` elaborates

**Files:** Modify `lib/std/list.cure` (`uncons` ~228, `split_first` ~234). Test: `test/cure/stdlib/list_tuple_surface_test.exs` (new).

**Interfaces:**
- Consumes Task 1's `Tuple(T, U)` type.
- Produces: `uncons : (List(t)) -> Option(Tuple(t, List(t)))` (`[h|t] -> Some(%[h,t])`, `[] -> None()`); `split_first : (List(t), t) -> Tuple(t, List(t))` (both branches now share the honest type — `[h|t] -> %[h,t]`, `[] -> %[default, []]`). No callers exist in `lib/std` (grep-confirmed: only doc mentions), so no downstream breakage.

- [ ] **Step 1: Write the failing test**

```elixir
defmodule Cure.Stdlib.ListTupleSurfaceTest do
  # uncons is Idris/Haskell `Maybe (a, List a)` — the empty case is None, not the
  # type-incoherent `%[[],[]]` the classic untyped `Tuple` allowed. This makes the
  # whole Std.List module elaborate on the DEPENDENT pipeline (previously it died at
  # uncons's `%[h,t]` : bare undefined `Tuple` -> unsupported_expression).
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  test "Std.List elaborates on the dependent pipeline" do
    assert {:ok, _env} = Program.elaborate(File.read!("lib/std/list.cure"))
  end

  test "uncons returns Some(%[h, t]) / None and runs" do
    src = """
    mod M
      use Std.List
      use Std.Option
      fn head_or(xs: List(Int), d: Int) -> Int =
        match Std.List.uncons(xs)
          Some(p) -> p.1
          None()  -> d
    """
    assert {:ok, env} = Program.elaborate(src)
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.M", functions: [:head_or])
    assert apply(m, :head_or, [[5, 6, 7], 0]) == 5
    assert apply(m, :head_or, [[], 0]) == 0
  end
end
```

- [ ] **Step 2: Run it, watch it fail**

Run: `mix test test/cure/stdlib/list_tuple_surface_test.exs`
Expected: FAIL — `Std.List` still returns bare `Tuple`; `Program.elaborate(list.cure)` errors `{:unsupported_expression, {:tuple, …}}` at `uncons` (line ~231).

- [ ] **Step 3: Rewrite `uncons` / `split_first`**

In `lib/std/list.cure`, add `use Std.Option` to the module header if not present, then:
```cure
## Split `list` into `Some(%[head, tail])`, or `None` when empty.
fn uncons(list: List(t)) -> Option(Tuple(t, List(t))) =
  match list
    [h | t] -> Some(%[h, t])
    []      -> None()

## Split `list` into `%[head, tail]`, substituting `default` for the head when empty.
fn split_first(list: List(t), default: t) -> Tuple(t, List(t)) =
  match list
    [h | t] -> %[h, t]
    []      -> %[default, []]
```
Update the two doc-comment examples (list.cure:35, ~233) to the `Some`/`None` form.

- [ ] **Step 4: Run green**

Run: `mix test test/cure/stdlib/list_tuple_surface_test.exs`
Expected: PASS. **If `Program.elaborate(list.cure)` now fails for a reason UNRELATED to tuples** (some other Std.List construct the dependent pipeline can't yet handle), STOP and report it as a distinct blocker — do not paper over it; Task 2's deliverable is "tuple issues fixed + the blocker named."

- [ ] **Step 5: Scoped regression + commit**

Run: `mix test test/cure/stdlib/ test/cure/elab/`
Expected: PASS.
```bash
git add -- lib/std/list.cure test/cure/stdlib/list_tuple_surface_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(std): Std.List.uncons -> Option, split_first honest Tuple(t,List(t))"
```

**End of Increment 1 — independently shippable. `Tuple(T,U)` is a real type and Std.List elaborates on the dependent pipeline (removes one blocker from typeclass Task 8/functor).**

---

## Increment 2 — N-ary (arity ≥ 3) flat tuples

### Task 3: n-ary `Tuple(T, U, V, …)` type surface + `Std.Tuple` skeleton

**Files:** Modify `lib/cure/compiler/parser.ex` (`parse_tuple_type` → n-ary). Create `lib/std/tuple.cure`. Test: `test/cure/elab/tuple_type_nary_test.exs` (new).

**Interfaces:**
- Produces: `Tuple(T1, …, Tn)` (n ≥ 3) parses to `{:tuple_type, [arity: n], [t1, …, tn]}`; arity-2 keeps aliasing to `sigma_type` (Task 1). `type_to_core`/`idx_to_core` gain a `{:tuple_type, …}` clause lowering to the `TupleN` family data type from Task 4.

- [ ] **Step 1: Write the failing test** — `Tuple(Int, Int, Int)` at type position parses to `{:tuple_type, [arity: 3], [_, _, _]}` (assert via `Parser.parse` on tokens, mirroring `typeclass_parse_test.exs`); and a `-> Tuple(Int,Int,Int)` fn is (still) rejected only at elaboration (family not seeded yet), not at parse.
- [ ] **Step 2: Run it, watch it fail** — `Tuple(Int,Int,Int)` currently hits `parse_tuple_type`'s single-`comma` path and errors at the second comma (`expected :rparen, got :comma`).
- [ ] **Step 3: Generalize `parse_tuple_type`** to parse a `[binder?: type]` list of length ≥ 2 until `:rparen`; length 2 → `{:sigma_type, …}` (unchanged), length ≥ 3 → `{:tuple_type, [arity: n], types}`. Create `lib/std/tuple.cure` with the `@group(:collections)` header and a doc block (API filled in Task 5/6).
- [ ] **Step 4: Run green; commit** (`parser.ex`, `lib/std/tuple.cure`, test).

### Task 4: per-arity flat families `Tuple3…Tuple8` + n-ary literal elaboration + flat emit

**Files:** Modify `lib/cure/core/builtins.ex` (seed `Tuple3…Tuple8` + `@schemas`), `lib/cure/elab/elaborator.ex` (n-ary `{:tuple, _, elems}` synth + checked clauses), `lib/cure/elab/emit.ex` (flat ctor emit + n-ary branch). Test: `test/cure/elab/tuple_nary_literal_test.exs` (new).

**Interfaces:**
- Produces: `%[a1,…,an]` (3 ≤ n ≤ 8) elaborates to `{:ctor, :"mk_tuple#{n}", [a1,…,an]}` of family `:"Tuple#{n}"`; synth → all-positions inferred; checked against `Tuple(T1..Tn)` → each element checked at `Ti` (earlier values substituted into later positions for the dependent-binder form, mirroring the arity-2 `cod_inst` line at `elaborator.ex:1146`). Emit lowers `mk_tupleN(…)` → flat `{…}` (generalizes `emit.ex:199-200`, already `Enum.map`-based). Arity > 8 → `{:error, {:tuple_arity_exceeded, n}}`. `%[a,%[b,c]]` stays `mk_tuple2(a, mk_tuple2(b,c))` → `{a,{b,c}}` (distinct from flat-3).

- [ ] **Step 1: Write the failing test** — `%[1,2,3]` in a `-> Tuple(Int,Int,Int)` fn elaborates, emits, and `apply` returns the flat `{1,2,3}`; nested `%[1, %[2,3]]` : `Tuple(Int, Tuple(Int,Int))` returns `{1, {2,3}}` (distinctness pin); `.1/.2/.3` project; arity-9 literal → `{:tuple_arity_exceeded, 9}`.
- [ ] **Step 2: Run it, watch it fail** — `%[1,2,3]` → `{:unsupported_expression}` (probe C), no `Tuple3` family exists.
- [ ] **Step 3: Seed families + elaborate + emit.** In `builtins.ex`: add `@schemas` entries `tuple3..tuple8` (`tupleN: [{:"mk_tupleN", N}]`) and a `seed_tuples/1` that seeds a parametric family per arity 3..8 (`Inductive.family(:"Tuple#{n}", element-type params, [], 0)`), added to the `seed/2` pipeline. In `elaborator.ex`: add `{:tuple, _, elems}` clauses (checked + synth) for `length(elems) in 3..8`, building the `mk_tupleN` ctor (reuse the arity-2 checked substitution loop, folded over the telescope); `length > 8` → the arity error. In `emit.ex`: add a `tuple_ctor?/2` predicate (any `mk_tupleN`) → flat tuple lowering (mirror `sigma_ctor?`/`emit.ex:199`), and an n-ary `tuple_branch_clause` generalizing `sigma_branch_clause` (`emit.ex:473`).
- [ ] **Step 4: Run green; commit.** *(This is the representation crux; if arity-2-vs-nested distinctness cannot be preserved without a kernel change, STOP per the TCB rule.)*

### Task 5: n-ary projection `.i` (i ≥ 3) + n-ary patterns

**Files:** Modify `lib/cure/elab/elaborator.ex` (projection dispatch ~465-471; a `tuple_projection` beside `sigma_projection` ~857), `lib/cure/elab/emit.ex` (projection inline ~392). Fill `lib/std/tuple.cure` API (`get`/`first`/`second`/`third`/`swap`). Test: `test/cure/elab/tuple_nary_projection_test.exs`.

**Interfaces:** `t.i` for `i ≥ 3` on a `TupleN` value → `element(i, t)` (not `record_projection`, which currently errors `{:projection_not_a_record}` at `elaborator.ex:894`); `%[a,b,c]` patterns in `match` bind positionally. `Std.Tuple.get(i, t)`/`swap` provided.

- [ ] Steps: failing test (`%[10,20,30].3 == 30`; a 3-tuple `match %[a,b,c] -> …`) → route `.i` (i≥3) on a `TupleN`-typed scrutinee to a `tuple_projection` lowering to `element(i)` → green → commit.

### Task 6: migrate `match.cure` (the non-#18 arity-3 consumer) + verify

**Files:** `lib/std/match.cure`. Test: `test/cure/stdlib/match_nary_test.exs`.

**Interfaces:** `match.cure`'s arity-3 literals/patterns (lines ~50, 67-75) elaborate through the n-ary surface with honest `Tuple(…)` return types. (app/supervisor/fsm arity-3 users are the bespoke modules #18 reimplements as macros — NOT migrated here; note that in the commit.)

- [ ] Steps: failing test (elaborate `match.cure`; run a representative `head_tail`/`first_two`) → give its helpers honest `Tuple(…)` return types → green → commit. If a helper is type-incoherent like the old `uncons` (a fabricated empty-case value), fix it to `Option` (align with real languages) and note it.

---

## Final gate (Increment 2)

- [ ] Run the full suite ONCE, alone: `mix test`. Expected: green. Confirm arity-2 and arity-3..8 tuples elaborate/emit flat; nested pairs stay distinct; `Std.List`, `Std.Tuple`, `match` elaborate on the dependent pipeline.

## Deferred (separate follow-on plans — do NOT do here)

- **Scope (B):** dependent `Tele`/`NonDep`/`Dep`/witness-gated generic API (`reverse`/`to_list`/`map_uniform`), function-typed ctor fields (`parse_ctor_dom` → `parse_type_expr`), chained `x.2.1` inference. **Lands immediately after #18** (operator decision 2026-07-10).
- **`Std.Pair` → `Std.Tuple` deprecation** via the migration facility (warn-now/error-later).
- **`Std.Vector`** 3-tuple internal rep onto the n-ary surface.
- **Arity cap > 8** (records/lists for wider products) — intentional v1 limit, matches Haskell/OCaml/F#.
