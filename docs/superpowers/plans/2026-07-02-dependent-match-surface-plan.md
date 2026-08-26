# Surface dependent matching: impossible clauses + full index refinement — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Surface the kernel's complete first-order index unification into the `.cure` language — impossible clauses (omission + verified `-> impossible`) and constructor-headed index refinement — with the trusted kernel (TCB) gaining only one thin wrapper and one always-fails typing clause.

**Architecture:** The kernel keeps all unification logic. We add one public wrapper `Cure.Core.Kernel.branch_unify/4` over the existing private `unify_indices/4`. The untrusted elaborator (`Cure.Elab.Elaborator`) delegates coverage, discharge, and per-branch refinement to that query, stops using its weaker private `branch_index_subst`, and synthesizes discharged branches carrying a new `{:absurd}` Core leaf. The kernel independently re-checks and re-discharges every emitted `{:case,…}`, so a wrong elaborator decision can only yield a spurious error, never an accepted ill-typed program.

**Tech Stack:** Elixir; the Cure compiler under `lib/cure/`; ExUnit tests under `test/cure/`. `mix test` runs the suite.

## Global Constraints

- Ghost-written commits — never co-sign; commits appear from the user only. (verbatim from spec §8.5)
- One full build/test run at any moment — NEVER launch concurrent `mix test`/`mix compile` (a past concurrent full-suite run caused a kernel panic).
- Compile Cure with OTP 26–28.
- Entry point is `start/0`, not `main/0`.
- Avoid `Registry`/`persistent_term` on AtomVM targets (not touched by this work, but no new use).
- TCB (`lib/cure/core/*`) edits are limited to exactly two additions total: `branch_unify/4` (no new unification logic) and one `infer(_ctx, {:absurd}) -> {:error, _}` always-fails clause. No other kernel behavior changes; `check_coverage` is unchanged (spec §8.1, §8.4).
- Tests are immutable once green: fix the implementation, not the test. Pre-green de Bruijn / fixture adjustment is permitted before a test first passes.
- Baseline suite: **2173 tests, zero regressions.** Run the full suite once per slice (spec §7).
- The Antigen `indexed/case` and `rewrite/eq` verticals MUST stay green — they guard the kernel the elaborator now leans on (spec §7).

## Source of truth

Design spec (hardened): `docs/superpowers/specs/types/2026-07-02-dependent-match-surface-design.md`. Section references below (§N) point into it.

## File Structure

- **Modify** `lib/cure/core/kernel.ex` — add `branch_unify/4` (Task 1) and the `{:absurd}` `infer` clause (Task 2). No other change.
- **Modify** `lib/cure/core/serialize.ex` — add `{:absurd}` `enc`/`build_node` pair (Task 2).
- **Modify** `lib/cure/elab/emit.ex` — add `lower(_env, {:absurd}, _ctx)` clause before the raising catch-all (Task 2).
- **Modify** `lib/cure/compiler/parser.ex` — recognize `-> impossible` as an arm body, marking `impossible: true` in arm meta (Task 3). No lexer change (soft keyword, §4).
- **Modify** `lib/cure/elab/elaborator.ex` — coverage/discharge partition pass + arm validation + `constructor_pattern` hardening (Task 4); delegate `branch_expected_type`/`specialize_branch_context` to `branch_unify` (Task 5); extend `generalize` to whole-subterm replacement (Task 6).
- **Create** `test/cure/core/branch_unify_test.exs` — Task 1 kernel unit tests.
- **Create** `test/cure/core/absurd_leaf_test.exs` — Task 2 leaf round-trip + reachable-rejection tests.
- **Modify** `test/cure/compiler/parser_test.exs` — Task 3 arm-meta test (append a test; do not alter existing tests).
- **Create** `test/cure/elab/dependent_match_surface_test.exs` — Task 4 + Task 6 surface `.cure` tests.

## Reference facts (verified against the tree at authoring time)

- `Cure.Core.Context`: `Context.signature(ctx)` → `%Env{}` (`context.ex:33`); `Context.length(ctx)` → depth (`context.ex:46`); `Context.empty(sig)` builds a context (`context.ex:29`); `Context.extend(ctx, type_value)` pushes a binder (`context.ex:37`).
- `Cure.Core.Inductive`: `get_ctor(sig, cname)` → `%{args: telescope, result_indices: […], quantities: […]}` or `nil`; `ctor_family(sig, cname)` → family atom; `get_family`, `param_count`, `ctors_of` (`lib/cure/core/inductive.ex:157,161,153,211,225`).
- Kernel private `unify_indices(ctx, result_indices, scrut_indices, arity)` returns `{:solved, subst} | :trivial | :impossible`; `scrut_indices` are **values** (it reifies them internally via `Quote.reify(outer_depth)` then `Term.shift(arity, 0)`) (`kernel.ex:714-723`).
- Kernel `check_case_branches` already skips body checking on an `:impossible` verdict (`kernel.ex:676-678`); `check/3`'s `{:error,_}` path maps to `{:error, :branch_type}` (`kernel.ex:698-700`).
- Kernel `infer/2` has no catch-all (lines 41–238); `check/3`'s catch-all delegates to `infer/2`. A `{:absurd}` with no clause would raise `FunctionClauseError` and crash the compile — there is no `rescue` around kernel calls (§5 correction).
- Elaborator `elaborate_match/6` (`elaborator.ex:277`) already computes `idx_vals` (index **values**) and `param_vals` via `Enum.split(combined_vals, pc)` (line 286). `branch_unify` consumes `ctx` + `idx_vals`.
- Elaborator `constructor_pattern/1` (`elaborator.ex:470`) matches only `{:function_call, meta, args}` and crashes on any other pattern shape.
- Elaborator branch de Bruijn frame is `ctor-args ++ outer` (no separate params segment): neither `extend_with_telescope` (`kernel.ex:571`) nor `extend_context` (`elaborator.ex:518`) push params as binders (§3, §8.3).
- Surface entry: `Cure.Elab.Program.elaborate(source_string)` → `{:ok, env} | {:error, reason}` (`lib/cure/elab/program.ex:16`). Parser entry: `Cure.Compiler.Lexer.tokenize(src, emit_events: false)` then `Cure.Compiler.Parser.parse(tokens, emit_events: false)` (see `test/cure/compiler/bin_segment_test.exs:97`).
- Fixtures for kernel tests: `Ix`/`wrap`/`Dec` family in `lib/antigen/generators/indexed.ex:73` and `Ix`/`Foo`/`Dec` in `test/cure/core/case_soundness_index_test.exs:5-13`. `wrap : (p:Dec) -> Ix(Causal)`; `Dec = Dcoupled | Causal`.

## Slice / Task overview

- **Slice 1 — Task 1:** `branch_unify/4` kernel wrapper + unit tests. No behavior change.
- **Slice 2 — Tasks 2–4:** impossible clauses (A). `{:absurd}` leaf (Task 2); parser `-> impossible` (Task 3); elaborator coverage/discharge pass + validation + `constructor_pattern` hardening (Task 4).
- **Slice 3 — Tasks 5–6:** refinement completeness. Delegate `branch_expected`/context specialization to `branch_unify` subst (Task 5); extend `generalize` to whole-subterm replacement for verbatim reuse (Task 6).

Each slice ends green + committed; the full suite runs once per slice. Slices 2 and 3 both depend on Slice 1.

---

## Task 1: `branch_unify/4` kernel wrapper (Slice 1)

**Files:**
- Modify: `lib/cure/core/kernel.ex` (add public `branch_unify/4` near the private `unify_indices/4`, ~line 714)
- Test: `test/cure/core/branch_unify_test.exs` (create)

**Interfaces:**
- Produces: `Cure.Core.Kernel.branch_unify(ctx :: Context.t(), dname :: atom(), cname :: atom(), scrut_indices :: [Value.t()]) :: {:solved, map()} | :trivial | :impossible`. `scrut_indices` are the scrutinee's **index values** (post param/index split). Consumed by Tasks 4 and 5.

- [ ] **Step 1: Write the failing tests**

Create `test/cure/core/branch_unify_test.exs`. Build the `Ix`/`wrap`/`Dec` signature inline (same shape as `case_soundness_index_test.exs`). Three verdict cases, the compound-solved case that stands in for spec §6 Slice 3(i), and a wrapper-level misuse guard (cname/dname family mismatch):

```elixir
defmodule Cure.Core.BranchUnifyTest do
  @moduledoc """
  Unit tests for the public branch_unify/4 wrapper (spec §3). It reuses the
  private unify_indices/4; these pin the three verdicts, the compound-solved
  case the elaborator consumes for constructor-headed refinement (§6 Slice
  3(i)), and the wrapper's own dname/cname family-mismatch guard.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Context, Env, Inductive, Kernel, Eval}

  # Dec = Dcoupled | Causal ;  Ix(n:Dec) with wrap : (p:Dec) -> Ix(Causal)
  @dec {:data, :Dec, [], []}

  defp sig do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Dec, [], [], 0),
         [Inductive.ctor(:Dcoupled, [], []), Inductive.ctor(:Causal, [], [])])
    |> Inductive.declare(Inductive.family(:Ix, [], [{:n, @dec}], 0),
         [Inductive.ctor(:wrap, [{:p, @dec}], [{:ctor, :Causal, []}])])
  end

  defp causal_val, do: Eval.eval({:ctor, :Causal, []}, [])
  defp dcoupled_val, do: Eval.eval({:ctor, :Dcoupled, []}, [])

  test ":trivial when the scrutinee index equals wrap's ground result index (Causal)" do
    ctx = Context.empty(sig())
    assert :trivial = Kernel.branch_unify(ctx, :Ix, :wrap, [causal_val()])
  end

  test ":impossible on a rigid ground clash (wrap's Causal vs scrutinee Dcoupled)" do
    ctx = Context.empty(sig())
    assert :impossible = Kernel.branch_unify(ctx, :Ix, :wrap, [dcoupled_val()])
  end

  test "{:solved, subst} binds a bare outer scrutinee index var to wrap's compound result index" do
    # ctx has one outer binder (a Dec); its value is a neutral var reified as {:var,0}.
    ctx = Context.extend(Context.empty(sig()), Eval.eval(@dec, []))
    outer_idx_val = {:vneutral, {:nvar, 0}}
    assert {:solved, subst} = Kernel.branch_unify(ctx, :Ix, :wrap, [outer_idx_val])
    # The outer index var (shifted past wrap's 1 arg → key 1) is bound to Causal.
    assert subst == %{1 => {:ctor, :Causal, []}}
  end

  test ":impossible when cname exists but does not belong to dname's family" do
    # Dcoupled/Causal are Dec's own constructors, not Ix's — a caller passing the
    # wrong dname for a real cname must not silently get a verdict computed
    # against the wrong family's schema (the wrapper is new TCB code; its own
    # doc comment already guards the "unknown constructor" case, so the
    # "known constructor of a different family" case must be guarded too).
    ctx = Context.empty(sig())
    assert :impossible = Kernel.branch_unify(ctx, :Ix, :Causal, [causal_val()])
  end
end
```

- [ ] **Step 2: Run the tests to verify they fail**

Run: `mix test test/cure/core/branch_unify_test.exs`
Expected: FAIL — `Kernel.branch_unify/4` is undefined.

- [ ] **Step 3: Implement `branch_unify/4`**

In `lib/cure/core/kernel.ex`, immediately above the private `defp unify_indices(ctx, …)` (~line 708, before its doc comment), add the public wrapper. It looks up the constructor's schema from the context's signature and delegates — no new unification logic:

```elixir
@doc """
Public branch-refinement query (spec §3). Given the caller's `ctx`, the
scrutinee's family `dname` and a branch constructor `cname`, plus the
scrutinee's actual index **values** `scrut_indices`, return the same verdict
`unify_indices/4` produces: `{:solved, subst} | :trivial | :impossible`, where
`subst` is in the branch de Bruijn frame `ctor-args ++ outer`. The elaborator
delegates to this instead of carrying its own weaker index unification. Adds no
unification logic — it reuses the private `unify_indices/4`. Guards two misuse
shapes rather than trusting the caller: an unknown constructor (`nil` from
`get_ctor`) and a constructor that exists but belongs to a different family
than `dname` (`Inductive.ctor_family/2` mismatch) both verdict `:impossible`
rather than proceeding against the wrong schema. Both are impossible in
practice given the elaborator's own pre-validation, but this is new trusted-
kernel code and `dname` is part of the signature precisely to be checked, not
merely documented.
"""
@spec branch_unify(Context.t(), atom(), atom(), [Cure.Core.Value.t()]) ::
        {:solved, map()} | :trivial | :impossible
def branch_unify(ctx, dname, cname, scrut_indices) do
  sig = Context.signature(ctx)

  with %{args: tele, result_indices: result_indices} <- Inductive.get_ctor(sig, cname),
       ^dname <- Inductive.ctor_family(sig, cname) do
    unify_indices(ctx, result_indices, scrut_indices, length(tele))
  else
    _ -> :impossible
  end
end
```

- [ ] **Step 4: Run the tests to verify they pass**

Run: `mix test test/cure/core/branch_unify_test.exs`
Expected: PASS (4 tests).

- [ ] **Step 5: Run the full suite once**

Run: `mix test`
Expected: baseline + 4 new = green, zero regressions.

- [ ] **Step 6: Commit**

```bash
git add lib/cure/core/kernel.ex test/cure/core/branch_unify_test.exs
git commit -m "feat(kernel): branch_unify/4 public wrapper over unify_indices"
```

---

## Task 2: `{:absurd}` Core leaf (Slice 2)

**Files:**
- Modify: `lib/cure/core/kernel.ex` (add one `infer` clause near the other leaf clauses, ~line 58)
- Modify: `lib/cure/core/serialize.ex` (add `enc` at ~line 34 area and `build_node` at ~line 152 area)
- Modify: `lib/cure/elab/emit.ex` (add `lower` clause before the raising catch-all at line 170)
- Test: `test/cure/core/absurd_leaf_test.exs` (create)

**Interfaces:**
- Produces: the Core leaf term `{:absurd}` — kernel `infer` returns `{:error, :absurd_in_reachable_position}` for it (never a `check` success); `Serialize` round-trips it; `Emit.lower` emits an unreachable stub. Consumed by Task 4 (discharged branch bodies).

- [ ] **Step 1: Write the failing tests**

Create `test/cure/core/absurd_leaf_test.exs`:

```elixir
defmodule Cure.Core.AbsurdLeafTest do
  @moduledoc """
  The {:absurd} leaf (spec §5): it only ever sits in a discharged branch. It has
  NO positive typing rule — inferring it in a reachable position must return a
  clean {:error, _}, never crash the kernel — and it must serialize round-trip.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Context, Env, Kernel, Serialize}

  test "infer/2 rejects {:absurd} cleanly instead of raising" do
    ctx = Context.empty(Env.empty())
    assert {:error, :absurd_in_reachable_position} = Kernel.infer(ctx, {:absurd})
  end

  test "{:absurd} serializes and parses back to itself" do
    assert {:ok, {:absurd}} = Serialize.decode(Serialize.encode({:absurd}))
  end
end
```

Verified against the tree: the public entry points are `Serialize.encode/1` (`serialize.ex:19`, returns a bare `binary()`, delegates to `enc/1`) and `Serialize.decode/1` (`serialize.ex:68`, returns `{:ok, term} | {:error, term}`, delegates through `build_node/2`) — not `to_string`/`parse`. Use these exact names.

- [ ] **Step 2: Run the tests to verify they fail**

Run: `mix test test/cure/core/absurd_leaf_test.exs`
Expected: FAIL — `infer(ctx, {:absurd})` raises `FunctionClauseError` (no clause), and `enc({:absurd})`/`build_node` are missing.

- [ ] **Step 3: Add the kernel `infer` clause**

In `lib/cure/core/kernel.ex`, alongside the other nullary-leaf `infer` clauses (near line 58, after `infer(_ctx, {:bool_type})`), add exactly one always-fails clause (§5 correction, §8.1). It has no `check` counterpart, so `{:absurd}` never checks against any type:

```elixir
# {:absurd} is an elaborator-only marker sitting in a discharged (unreachable)
# case branch, which check_case_branches never checks. It has no positive typing
# rule; a reachable occurrence fails cleanly here rather than crashing the kernel
# with an unmatched-clause exception (spec §5/§8.1).
def infer(_ctx, {:absurd}), do: {:error, :absurd_in_reachable_position}
```

- [ ] **Step 4: Add the `Serialize` enc/build_node pair**

In `lib/cure/core/serialize.ex`, mirror the `{:hole, name}` pair. Add next to the `enc({:hole, …})` clause (line 34):

```elixir
defp enc({:absurd}), do: "(absurd)"
```

and next to the `build_node("hole", …)` clause (line 152):

```elixir
defp build_node("absurd", []), do: {:ok, {:absurd}}
```

- [ ] **Step 5: Add the `Emit.lower` clause**

In `lib/cure/elab/emit.ex`, add a clause BEFORE the raising catch-all at line 170. A discharged branch is never executed at runtime; lower it to a call that raises if it somehow is reached:

```elixir
# A discharged (impossible) case branch. Never executed at runtime; emit an
# unreachable stub so codegen doesn't hit the raising catch-all (spec §5).
defp lower(_env, {:absurd}, _ctx),
  do: {:call, @line, {:atom, @line, :error}, [{:atom, @line, :absurd}]}
```

- [ ] **Step 6: Run the tests to verify they pass**

Run: `mix test test/cure/core/absurd_leaf_test.exs`
Expected: PASS (2 tests).

- [ ] **Step 7: Commit** (full-suite run happens at the end of Slice 2, Task 4)

```bash
git add lib/cure/core/kernel.ex lib/cure/core/serialize.ex lib/cure/elab/emit.ex test/cure/core/absurd_leaf_test.exs
git commit -m "feat(core): {:absurd} discharged-branch leaf across kernel/serialize/emit"
```

---

## Task 3: Parser `-> impossible` arm (Slice 2)

**Files:**
- Modify: `lib/cure/compiler/parser.ex` (`parse_match_arm/1`, line 1432)
- Test: `test/cure/compiler/parser_test.exs` (append one test; do not modify existing tests)

**Interfaces:**
- Produces: a `-> impossible` arm parses to `{:match_arm, meta, [body]}` where `meta` contains `impossible: true`. The `body` slot for an impossible arm is a placeholder (`nil`) — the elaborator (Task 4) reads the `impossible: true` flag and never elaborates the body. `impossible` remains a normal identifier everywhere else (soft keyword, §4).

- [ ] **Step 1: Write the failing test**

Append to `test/cure/compiler/parser_test.exs` (match the file's existing `alias`/helper conventions — it already uses `Lexer.tokenize` + `Parser.parse`):

```elixir
test "a `-> impossible` arm body is marked impossible in arm meta" do
  src = """
  fn f(xs: Foo) -> Nat = match xs
    bar() -> impossible
  """

  {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
  {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)
  arm = find_match_arm(ast)
  assert Keyword.get(elem(arm, 1), :impossible) == true
end

test "`impossible` is still usable as a normal identifier in an arm body" do
  src = """
  fn f(xs: Foo) -> Nat = match xs
    bar() -> impossible + 1
  """

  {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
  {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)
  arm = find_match_arm(ast)
  refute Keyword.get(elem(arm, 1), :impossible) == true
end
```

Add a small helper near the top of the test module (or inline) that walks the AST to the first `:match_arm` tuple:

```elixir
defp find_match_arm(ast) do
  {:match_arm, _, _} = arm =
    ast |> deep_find(fn {:match_arm, _, _} -> true; _ -> false end)
  arm
end

# deep_find: first node (tuple/list) satisfying pred, depth-first.
defp deep_find(node, pred) do
  cond do
    pred.(node) -> node
    is_tuple(node) -> node |> Tuple.to_list() |> deep_find_list(pred)
    is_list(node) -> deep_find_list(node, pred)
    true -> nil
  end
end

defp deep_find_list(list, pred) do
  Enum.find_value(list, fn el -> deep_find(el, pred) end)
end
```

(If `parser_test.exs` already has an AST-walking helper, reuse it instead of adding `deep_find`.)

- [ ] **Step 2: Run the tests to verify they fail**

Run: `mix test test/cure/compiler/parser_test.exs`
Expected: the first new test FAILS (`impossible` currently parses as an ordinary identifier body → no `impossible: true` in meta). The second should already pass.

- [ ] **Step 3: Implement soft-keyword recognition in `parse_match_arm/1`**

In `lib/cure/compiler/parser.ex`, after `state = expect(state, :arrow)` and `state = skip_newlines(state)` (lines 1450–1451), recognize `impossible` ONLY when it is the entire arm body — i.e. the next token is the identifier `impossible` and the token after it terminates the arm (newline, comma, `}`, dedent, or eof). This mirrors the `sup`/`app` soft-keyword discipline (no `@keywords` change). Replace the body-parse block (lines 1453–1459) with:

```elixir
    # `impossible` is a soft keyword recognized only as an entire arm body
    # (spec §4): `pat -> impossible`. Any other use stays an ordinary identifier.
    if impossible_body?(state) do
      state = advance(state)
      meta = if guard, do: [pattern: pattern, guard: guard, impossible: true], else: [pattern: pattern, impossible: true]
      {{:match_arm, meta, [nil]}, state}
    else
      {body, state} = parse_expr_or_block(state)
      meta = if guard, do: [pattern: pattern, guard: guard], else: [pattern: pattern]
      {{:match_arm, meta, [body]}, state}
    end
  end

  # True iff the next token is the identifier `impossible` AND the token after it
  # ends the arm — so `impossible` alone is the body, but `impossible + 1` is not.
  defp impossible_body?(state) do
    case peek(state) do
      %Token{type: :identifier, value: "impossible"} ->
        case peek_at(state, 1) do
          %Token{type: type} when type in [:newline, :comma, :rbrace, :dedent, :eof] -> true
          nil -> true
          _ -> false
        end

      _ ->
        false
    end
  end
```

Verified against the tree (no new helper needed): the parser already has a two-arg lookahead accessor, `defp peek_at(%{tokens: tokens, pos: pos}, offset)` (`parser.ex:4276`), distinct from the one-arg `peek/1` (`parser.ex:4270-4274`). `peek_at/2` returns `nil` past the end of the token stream (rather than `peek/1`'s synthesized `:eof` token), which is exactly what the `nil -> true` clause above already handles — use `peek_at/2` as written, no new function required. The identifier token shape is `%Token{type: :identifier, value: "impossible"}` (lexer emits `{:identifier, word}` at `lexer.ex:617`).

- [ ] **Step 4: Run the tests to verify they pass**

Run: `mix test test/cure/compiler/parser_test.exs`
Expected: both new tests PASS; existing parser tests unchanged.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/compiler/parser.ex test/cure/compiler/parser_test.exs
git commit -m "feat(parser): recognize `-> impossible` arm body as soft keyword"
```

---

## Task 4: Elaborator coverage/discharge pass (Slice 2)

**Files:**
- Modify: `lib/cure/elab/elaborator.ex` (`elaborate_match/6` line 277; `elaborate_branches`/`elaborate_branch` lines 404–453; `constructor_pattern/1` line 470)
- Test: `test/cure/elab/dependent_match_surface_test.exs` (create)

**Interfaces:**
- Consumes: `Kernel.branch_unify/4` (Task 1); arm meta `impossible: true` (Task 3); `{:absurd}` leaf (Task 2); `Inductive.get_ctor/2`, `Inductive.ctor_family/2`, `Inductive.ctors_of/2`.
- Produces: `elaborate_match` emits a `{:case, scrut, motive, branches}` with a branch for EVERY declared constructor (matched + discharged), and returns the new error atoms `{:missing_branch, cname}`, `{:reachable_impossible, cname}`, `{:duplicate_branch, cname}`, `{:foreign_ctor, cname}`, `{:unsupported_pattern, shape}`.

- [ ] **Step 1: Write the failing surface tests**

Create `test/cure/elab/dependent_match_surface_test.exs`. These fixtures were probed against the current tree — their pre-implementation results are noted so the RED state is unambiguous:

```elixir
defmodule Cure.Elab.DependentMatchSurfaceTest do
  @moduledoc """
  Surface acceptance for sub-project ④ (spec §2, §6). Programs go through the
  real pipeline via Cure.Elab.Program.elaborate/1. Negatives assert the exact
  error atom (spec §7).
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  @vec """
  type Nat = Z | S(Nat)
  type Vector(a: Type) indices (n: Nat)
    empty : Vector(a, Z)
    prepend : a -> Vector(a, n) -> Vector(a, S(n))
  """

  # Pre-impl: {:error, :coverage}. Post: {:ok, _} — prepend is unreachable at Z,
  # so the elaborator discharges it and the kernel's coverage check passes.
  test "(A) a match omitting an impossible constructor elaborates" do
    src = @vec <> """
    fn only_empty({a: Type}, xs: Vector(a, Z)) -> Nat = match xs
      empty() -> Z()
    """
    assert {:ok, _env} = Program.elaborate(src)
  end

  # Pre-impl: {:error, :coverage} (kernel). Post: {:error, {:missing_branch, :prepend}}.
  test "(A) a match omitting a REACHABLE constructor is a missing-branch error" do
    src = @vec <> """
    fn bad({a: Type}, {n: Nat}, xs: Vector(a, n)) -> Nat = match xs
      empty() -> Z()
    """
    assert {:error, {:missing_branch, :prepend}} = Program.elaborate(src)
  end

  # Pre-impl: {:error, :unknown_global} (impossible lexes as an identifier body).
  # Post: {:ok, _} — the branch is genuinely unreachable and accepted.
  test "(A) an explicit `-> impossible` on an unreachable branch elaborates" do
    src = @vec <> """
    fn ei({a: Type}, xs: Vector(a, Z)) -> Nat = match xs
      empty() -> Z()
      prepend(x, rest) -> impossible
    """
    assert {:ok, _env} = Program.elaborate(src)
  end

  # Pre-impl: {:error, :unknown_global}. Post: {:error, {:reachable_impossible, :prepend}}.
  test "(A) a mis-marked `-> impossible` on a reachable branch is rejected" do
    src = @vec <> """
    fn mi({a: Type}, {n: Nat}, xs: Vector(a, n)) -> Nat = match xs
      empty() -> Z()
      prepend(x, rest) -> impossible
    """
    assert {:error, {:reachable_impossible, :prepend}} = Program.elaborate(src)
  end
end
```

- [ ] **Step 2: Run the tests to verify they fail**

Run: `mix test test/cure/elab/dependent_match_surface_test.exs`
Expected: all four FAIL with the pre-impl results above (`:coverage` / `:unknown_global`), none matching the asserted post atoms.

- [ ] **Step 3: Harden `constructor_pattern/1`**

Replace the single-clause `constructor_pattern/1` (`elaborator.ex:470-474`) so it returns a clean error instead of crashing on non-`function_call` patterns (§4). Change its callers to handle the `{:error,_}`:

```elixir
defp constructor_pattern({:function_call, meta, args}) do
  cname = meta |> Keyword.fetch!(:name) |> String.to_atom()
  vars = Enum.map(args, fn {:variable, _meta, v} -> v end)
  {:ok, {cname, vars}}
end

defp constructor_pattern(other), do: {:error, {:unsupported_pattern, pattern_shape(other)}}

defp pattern_shape(p) when is_tuple(p) and tuple_size(p) > 0, do: elem(p, 0)
defp pattern_shape(_), do: :unknown
```

- [ ] **Step 4: Rewrite `elaborate_branches` as a coverage/discharge partition pass**

Rework `elaborate_match/6` (line 293-296) to call a new partition-driven assembler, and replace `elaborate_branches/8` (line 404) accordingly. The pass implements spec §5 steps 2–6. Full code:

```elixir
# In elaborate_match/6, replace the `with {:ok, branches} <- elaborate_branches(...)`
# block (lines 293-296) with:
          with {:ok, branches} <-
                 elaborate_branches(
                   arms, names, ctx, env, dname,
                   idx_vals, idx_terms, param_vals, scrut_term, result_type_term
                 ) do
            {:ok, {:case, scrut_term, motive, branches}}
          end
```

```elixir
# Replace elaborate_branches/8 (elaborator.ex:404) with this partition pass.
# `idx_vals` are the scrutinee's index VALUES (for branch_unify); `idx_terms`
# are the reified index TERMS (for branch_expected/context, as before).
defp elaborate_branches(arms, names, ctx, env, dname, idx_vals, idx_terms, param_vals, scrut_term, result_type_term) do
  with {:ok, arm_map} <- partition_arms(arms, ctx, env, dname) do
    sig = Context.signature(ctx)

    sig
    |> Inductive.ctors_of(dname)
    |> Enum.map(& &1.name)
    |> Enum.reduce_while({:ok, []}, fn cname, {:ok, acc} ->
      verdict = Kernel.branch_unify(ctx, dname, cname, idx_vals)

      case Map.get(arm_map, cname) do
        {:matched, pattern, body_expr} ->
          case elaborate_matched_branch(
                 verdict, pattern, body_expr, names, ctx, env,
                 idx_terms, param_vals, scrut_term, result_type_term
               ) do
            {:ok, branch} -> {:cont, {:ok, acc ++ [branch]}}
            {:error, _} = err -> {:halt, err}
          end

        {:impossible_marked, pattern} ->
          if verdict == :impossible do
            {arity, _} = ctor_arity(env, pattern)
            {:cont, {:ok, acc ++ [{cname, arity, {:absurd}}]}}
          else
            {:halt, {:error, {:reachable_impossible, cname}}}
          end

        nil ->
          # omitted constructor
          if verdict == :impossible do
            {arity, _} = ctor_arity(env, cname)
            {:cont, {:ok, acc ++ [{cname, arity, {:absurd}}]}}
          else
            {:halt, {:error, {:missing_branch, cname}}}
          end
      end
    end)
  end
end

# Build a map cname => {:matched, pattern, body} | {:impossible_marked, pattern}.
# Validates every arm names one of dname's OWN declared constructors (spec §5
# step 2 gap) and rejects duplicate arms.
defp partition_arms(arms, ctx, env, dname) do
  sig = Context.signature(ctx)

  Enum.reduce_while(arms, {:ok, %{}}, fn {:match_arm, arm_meta, body}, {:ok, acc} ->
    pattern = Keyword.fetch!(arm_meta, :pattern)

    case constructor_pattern(pattern) do
      {:error, _} = err ->
        {:halt, err}

      {:ok, {cname, _vars}} ->
        cond do
          Inductive.get_ctor(env, cname) == nil ->
            {:halt, {:error, {:unknown_pattern_constructor, cname}}}

          Inductive.ctor_family(sig, cname) != dname ->
            {:halt, {:error, {:foreign_ctor, cname}}}

          Map.has_key?(acc, cname) ->
            {:halt, {:error, {:duplicate_branch, cname}}}

          Keyword.get(arm_meta, :impossible) == true ->
            {:cont, {:ok, Map.put(acc, cname, {:impossible_marked, pattern})}}

          true ->
            {:cont, {:ok, Map.put(acc, cname, {:matched, pattern, single_body(body)})}}
        end
    end
  end)
end

# Arity of a constructor named directly or by a pattern (spec §5 steps 4/5).
defp ctor_arity(env, {:function_call, _, _} = pattern) do
  {:ok, {cname, _}} = constructor_pattern(pattern)
  ctor_arity(env, cname)
end

defp ctor_arity(env, cname) when is_atom(cname) do
  %{args: tele} = Inductive.get_ctor(env, cname)
  {length(tele), cname}
end
```

- [ ] **Step 5: Implement `elaborate_matched_branch`**

This adapts the existing `elaborate_branch/9` body-elaboration logic (lines 425-452), adding the spec §5 step-3 gap: a matched-but-`:impossible` constructor's body is elaborated UNCHECKED via `elaborate_expr_typed` (it is never checked by the kernel either). Add:

```elixir
defp elaborate_matched_branch(verdict, pattern, body_expr, names, ctx, env, scrut_indices, scrut_param_vals, scrut_term, result_type_term) do
  {:ok, {cname, pattern_vars}} = constructor_pattern(pattern)
  %{args: telescope, quantities: quantities, result_indices: result_indices} = Inductive.get_ctor(env, cname)
  branch_names = branch_scope(quantities, pattern_vars) ++ names

  case verdict do
    :impossible ->
      # Matched arm on a genuinely unreachable constructor the user did NOT mark
      # impossible: elaborate the body unchecked (the kernel discharges it too).
      branch_ctx = extend_context(ctx, telescope, scrut_param_vals)

      with {:ok, body_term, _type} <- elaborate_expr_typed(body_expr, branch_names, branch_ctx, env) do
        {:ok, {cname, length(telescope), body_term}}
      end

    _solved_or_trivial ->
      branch_ctx =
        ctx
        |> extend_context(telescope, scrut_param_vals)
        |> specialize_branch_context(result_indices, scrut_indices, length(telescope))

      branch_expected =
        result_type_term
        |> branch_expected_type(scrut_term, cname, length(telescope), result_indices, scrut_indices)
        |> then(&Kernel.normalize(branch_ctx, &1))

      with {:ok, body_term} <- elaborate_branch_body(body_expr, branch_expected, branch_names, branch_ctx, env) do
        {:ok, {cname, length(telescope), body_term}}
      end
  end
end
```

Note: `elaborate_branch/9` (line 425) and the old `elaborate_branches/8` signature are now unused — delete `elaborate_branch/9`; keep `elaborate_branch_body`, `branch_scope`, `extend_context`, `specialize_branch_context`, `branch_expected_type`, and helpers (still used). In Slice 3, `specialize_branch_context`/`branch_expected_type` get rewired to `branch_unify`; here they keep their current signatures.

- [ ] **Step 6: Run the tests to verify they pass**

Run: `mix test test/cure/elab/dependent_match_surface_test.exs`
Expected: all four PASS.

- [ ] **Step 7: Run the full suite once (end of Slice 2)**

Run: `mix test`
Expected: baseline 2173 + new tests, zero regressions. In particular the existing `test/cure/elab/vec_dependent_test.exs` (`append`, full-coverage matches) must stay green — full-coverage matches are the `nil`-verdict-never-hit path where every constructor is `{:matched, …}` with `:solved`/`:trivial`.

- [ ] **Step 8: Commit**

```bash
git add lib/cure/elab/elaborator.ex test/cure/elab/dependent_match_surface_test.exs
git commit -m "feat(elab): coverage/discharge pass for impossible clauses (④ Slice 2)"
```

---

## Task 5: Delegate refinement to `branch_unify` subst (Slice 3)

**Files:**
- Modify: `lib/cure/elab/elaborator.ex` (`branch_expected_type` line 489, `specialize_branch_context` line 535; both currently call `branch_index_subst` line 559)
- Test: covered by Task 1's compound-solved unit test and Task 6's end-to-end verbatim test (see the realization note below).

**Interfaces:**
- Consumes: `Kernel.branch_unify/4` subst.
- Produces: `branch_expected_type` and `specialize_branch_context` use `branch_unify`'s bidirectional subst instead of the one-directional `branch_index_subst`. Same de Bruijn frame (`ctor-args ++ outer`), so downstream `replace_branch_vars` is unchanged.

**Realization note (spec §6 Slice 3(i)).** The spec lists a standalone surface test for the "ctor-compound result index against a bare scrutinee index" case (e.g. `Ix`/`wrap` from Task 1: scrutinee `xs : Ix(n)` with `n` a bare outer variable, `wrap : (p:Dec) -> Ix(Causal)`). Probed against the current tree with the concrete fixture

```
type Dec = Dcoupled | Causal
type Ix indices (n: Dec)
  wrap : (p: Dec) -> Ix(Causal)

fn f({n: Dec}, xs: Ix(n)) -> Dec = match xs
  wrap(p) -> Causal()
```

this already elaborates today (pre-Slice-5) — not because `branch_expected_type` computed the right thing (its one-directional `branch_index_subst` cannot solve `Causal := n`, per §1.2), but because `build_motive`'s *existing, unmodified* bare-var generalization already abstracts the bare scrutinee index `n` into the motive binder (`elaborator.ex:326-332`), and the **kernel's own `check_case_branches`** independently re-instantiates that motive per branch via its own complete `unify_indices` (`kernel.ex:690-705`) — the same mechanism Task 1 unit-tests directly. So for a body whose type is inferred (`Causal()`'s own type) rather than checked precisely against a `branch_expected` that needed the refined index, the kernel's independent recheck already accepts the branch regardless of what (possibly-too-weak) `branch_expected` the elaborator handed it. Probes that instead force the *elaborator's* `branch_expected` to matter (e.g. a nullary-constructor body needing implicit-argument inference against the refined type) fail on an unrelated, pre-existing bug (`{:unsolved_metavariables, :empty}`, `elaborator.ex:687`), not on the refinement gap this task closes. A dedicated red-for-the-right-reason surface fixture that isolates *only* the elaborator's delegation to `branch_unify` (as opposed to the kernel's independent backstop, which already covers this shape) is therefore not reliably constructible with the current surface's implicit-argument inference. This plan realizes §6 Slice 3(i) as **Task 1's `{:solved, subst}` compound unit test** (proves `branch_unify` produces the bidirectional binding the elaborator now consumes) plus **Task 6's end-to-end verbatim program** (proves the elaborator feeds that subst through `branch_expected_type` correctly for the case where it *is* load-bearing). This is a plan-level realization decision, surfaced here with the reproducing fixture rather than left as an unverifiable empirical claim; the §2 acceptance property (constructor-headed index refinement works) is still machine-proven — end-to-end at the kernel, and at the elaborator for the verbatim-reuse shape.

- [ ] **Step 1: Confirm the current behavior is preserved by a full-coverage regression**

Before changing anything, confirm `test/cure/elab/vec_dependent_test.exs` is green (it exercises `branch_index_subst` via `append`). This is the regression guard for Task 5 — the swap to `branch_unify` must keep it green.

Run: `mix test test/cure/elab/vec_dependent_test.exs`
Expected: PASS.

- [ ] **Step 2: Rewrite `branch_expected_type` to use `branch_unify`**

`branch_expected_type` (line 489) and `specialize_branch_context` (line 535) currently compute `subst = branch_index_subst(result_indices, scrut_indices, arity)`. Change both to take a precomputed `subst` (the `branch_unify` result) so the query runs once per branch in the caller. Update `elaborate_matched_branch` (Task 4) to compute the subst from the verdict and thread it in.

In `elaborate_matched_branch`'s `_solved_or_trivial` arm, derive the subst:

```elixir
    verdict ->
      subst =
        case verdict do
          {:solved, s} -> s
          :trivial -> %{}
        end

      branch_ctx =
        ctx
        |> extend_context(telescope, scrut_param_vals)
        |> specialize_branch_context(subst)

      branch_expected =
        result_type_term
        |> branch_expected_type(scrut_term, cname, length(telescope), subst)
        |> then(&Kernel.normalize(branch_ctx, &1))

      with {:ok, body_term} <- elaborate_branch_body(body_expr, branch_expected, branch_names, branch_ctx, env) do
        {:ok, {cname, length(telescope), body_term}}
      end
```

Change `branch_expected_type` to accept the subst directly:

```elixir
defp branch_expected_type(result_type_term, scrut_term, cname, arity, subst) do
  shifted = Subst.shift(result_type_term, arity, 0)

  subst =
    case scrut_term do
      {:var, i} -> Map.put(subst, i + arity, branch_constructor_term(cname, arity))
      _other -> subst
    end

  replace_branch_vars(shifted, subst)
end
```

Change `specialize_branch_context` to accept the subst directly (it becomes structurally identical to the kernel's own `specialize_branch_context/2`):

```elixir
defp specialize_branch_context(ctx, subst) when map_size(subst) == 0, do: ctx

defp specialize_branch_context(ctx, subst) do
  depth = Context.length(ctx)
  env = Context.env(ctx)

  types =
    Enum.map(ctx.types, fn type_value ->
      type_value
      |> Quote.reify(depth)
      |> replace_branch_vars(subst)
      |> Eval.eval(env)
    end)

  %{ctx | types: types}
end
```

Delete the now-unused `branch_index_subst/3` (line 559). Note: `branch_unify`'s subst is already in the `ctor-args ++ outer` frame with keys shifted by `arity` (the kernel's `unify_indices` does `Term.shift(arity, 0)` on the s-side), so no additional shifting is needed here — the same frame the old `branch_index_subst` produced via its own `Subst.shift(scrut_idx, arity, 0)`.

**Dangling parameter (CI-only failure mode).** This rewrite removes the only remaining use of `elaborate_matched_branch`'s `scrut_indices` parameter (bound to `idx_terms` at its call site) — the `:solved`/`:trivial` arm now derives `subst` from `verdict` alone, and the `:impossible` arm never referenced it. An unused function parameter is only a *warning* under a bare `mix test`/`mix compile` (this repo's `mix.exs` does not set `elixirc_options: [warnings_as_errors: true]`), so the plan's own verification steps would stay green — but CI (`.github/workflows/ci.yml:66`, `mix compile --warnings-as-errors`) treats it as a build failure. In this step, also update the function head introduced in Task 4 Step 5 from

```elixir
defp elaborate_matched_branch(verdict, pattern, body_expr, names, ctx, env, scrut_indices, scrut_param_vals, scrut_term, result_type_term) do
```

to

```elixir
defp elaborate_matched_branch(verdict, pattern, body_expr, names, ctx, env, _scrut_indices, scrut_param_vals, scrut_term, result_type_term) do
```

(the call site in `elaborate_branches` keeps passing `idx_terms` positionally unchanged — Elixir doesn't care about the callee's parameter name).

- [ ] **Step 3: Run the regression + full suite once (end of Slice 3 depends on Task 6; run full suite there)**

Run: `mix test test/cure/elab/vec_dependent_test.exs test/cure/elab/dependent_match_surface_test.exs test/cure/core/branch_unify_test.exs`
Expected: all green — the `append` refinement still works, now via `branch_unify`.

- [ ] **Step 4: Commit**

```bash
git add lib/cure/elab/elaborator.ex
git commit -m "feat(elab): delegate branch refinement to branch_unify subst (④ Slice 3)"
```

---

## Task 6: Extend `generalize` to whole-subterm replacement (Slice 3)

**Files:**
- Modify: `lib/cure/elab/elaborator.ex` (`build_motive` line 314, `generalize/4` lines 351-402)
- Test: `test/cure/elab/dependent_match_surface_test.exs` (append the verbatim-reuse test)

**Interfaces:**
- Consumes: nothing new.
- Produces: `build_motive` abstracts each scrutinee index *term* (not only bare vars) into its motive binder, via whole-subterm structural matching up to shifting (spec §3 case (a), 4-step algorithm). Restricted to verbatim reuse; bare-inner-variable dependence (case (b)) stays out of scope (§9).

- [ ] **Step 1: Write the failing test**

Append to `test/cure/elab/dependent_match_surface_test.exs`. Probed pre-impl result: `{:error, :coverage}` today (empty is omitted and not yet discharged pre-Slice-2; post-Slice-2 the discharge works but the motive does not abstract the compound index `S(m)`, so it still fails until this task):

```elixir
# Verbatim reuse (spec §3 case (a) / §6 Slice 3 test (ii)): the result type reuses
# the scrutinee's own constructor-headed index term S(m). empty is discharged
# (S(m) can never be Z); the prepend body must check against Vector(a, S(m)) with
# the motive abstracting the whole subterm S(m). Pre-impl: {:error, _}. Post: {:ok}.
test "(completeness) a match reusing a constructor-headed index term verbatim elaborates" do
  src = @vec <> """
  fn idv({a: Type}, {m: Nat}, xs: Vector(a, S(m))) -> Vector(a, S(m)) = match xs
    prepend(x, rest) -> prepend(x, rest)
  """
  assert {:ok, _env} = Program.elaborate(src)
end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/cure/elab/dependent_match_surface_test.exs`
Expected: the new test FAILS (the motive leaves `S(m)` un-abstracted, so the prepend branch body's type does not match the motive instantiation).

- [ ] **Step 3: Extend `build_motive` + `generalize` for whole-subterm replacement**

Per spec §3's 4-step algorithm. In `build_motive` (line 314), the current `rebind` map keys scrutinee index *variables* to motive binders. Add a parallel list of `{target_term, binder}` pairs for compound (non-var) index terms, and pass it to `generalize`. Replace the `rebind` construction (lines 326-340) and the `generalize` call (line 340):

```elixir
    # Bare-var index positions: map the scrutinee index var to its motive binder.
    # Compound index positions (e.g. S(m)): record the whole term → binder for
    # whole-subterm replacement (spec §3 case (a)). The scrutinee binder (index 0)
    # is handled the same way when the scrutinee itself is a bare var.
    {rebind, targets} =
      idx_terms
      |> Enum.with_index()
      |> Enum.reduce({%{}, []}, fn {idx_term, pos}, {rb, ts} ->
        binder = k - pos
        case idx_term do
          {:var, orig} -> {Map.put(rb, orig, binder), ts}
          compound -> {rb, [{compound, binder} | ts]}
        end
      end)

    rebind =
      case scrut_term do
        {:var, orig} -> Map.put(rebind, orig, 0)
        _other -> rebind
      end

    body = generalize(result_type_term, {rebind, targets}, k + 1, 0)
```

Change `generalize/4` so the second argument carries both the bare-var `rebind` map and the compound `targets` list, and add a check-before-recursing head that fires at EVERY node (spec §3 steps 1, 2, 4). The bare-var case becomes the degenerate one-node instance (step 3). Prepend one clause and thread `{rebind, targets}` everywhere `rebind` was threaded:

```elixir
# Whole-subterm generalization (spec §3). At every node, first try to match a
# compound target index term (shifted to the current depth); on a match, return
# its motive binder and DO NOT recurse into the replaced subtree. Otherwise fall
# through to the structural clauses. `gen` is `{rebind, targets}`.
defp generalize(term, {_rebind, targets} = gen, shift, depth) do
  case match_target(term, targets, depth) do
    {:ok, binder} -> {:var, binder + depth}
    :no_match -> generalize_struct(term, gen, shift, depth)
  end
end

# Try each compound target: shift it from the outer frame (depth 0) to `depth`
# and compare structurally. First match wins (step 4 handles multiple positions).
defp match_target(_term, [], _depth), do: :no_match

defp match_target(term, [{target, binder} | rest], depth) do
  if term == Subst.shift(target, depth, 0),
    do: {:ok, binder},
    else: match_target(term, rest, depth)
end
```

Then rename the existing clauses `generalize({:var, i}, …)` … `generalize(leaf, …)` (lines 351-402) to `generalize_struct(...)`, keeping their bodies, but:
- change the `{:var, i}` clauses to read `rebind` out of the `gen` tuple: `defp generalize_struct({:var, i}, {_rebind, _targets}, _shift, depth) when i < depth, do: {:var, i}` and `defp generalize_struct({:var, i}, {rebind, _targets} = _gen, shift, depth) do … Map.fetch(rebind, orig) … end`;
- in every recursive clause, pass the whole `gen` tuple through unchanged (e.g. `defp generalize_struct({:pi, d, c}, gen, s, depth), do: {:pi, generalize(d, gen, s, depth), generalize(c, gen, s, depth + 1)}` — note the recursive calls go back through `generalize/4`, not `generalize_struct/4`, so the target check runs at every node).

**Why this covers all 16 clauses, not just the `:pi` example above (completeness argument — verified against the current tree, `elaborator.ex:351-402` has exactly 16 clauses: `{:var,i}` when `i<depth`, `{:var,i}` general, `:pi`, `:lam`, `:sigma`, `:app`, `:pair`, `:fst`, `:snd`, `:data`, `:ctor`, `:case`, `:eq`, `:refl`, `:rewrite`, `:prim`, and the leaf catch-all).** Every clause other than the two `{:var, i}` ones only *forwards* its second parameter opaquely to recursive calls — it never inspects `rebind`'s contents. Elixir resolves a call by `name/arity`, not by which clause originally executed it, so mechanically: rename each `defp generalize(pattern, ...)` head to `defp generalize_struct(pattern, ...)` and leave every call *expression* inside the body exactly as `generalize(sub, gen_or_rb, s, depth[+n])` — do **not** also rewrite those inner call sites to say `generalize_struct(...)`. Since `generalize/4` now names the new check-before-recurse dispatcher, those untouched inner calls automatically re-enter it, so the target check fires at every node with zero additional per-clause editing beyond the head rename and the parameter name `rb`/`rebind` → `gen` (cosmetic only, since these clauses never destructure it). This includes the `:case` clause (`{:case, scr, m, brs}`, line 386), whose three recursive positions — `generalize(scr, gen, s, depth)`, `generalize(m, gen, s, depth)`, and each branch body at `generalize(b, gen, s, depth + ar)` (the per-branch arity-shifted depth) — need no special-case treatment beyond this same mechanical rename; the `depth + ar` shift is orthogonal to the `gen` tuple threading and is preserved verbatim.

Confirm `Subst.shift/3` accepts `(term, amount, cutoff)` — it does. Verified: the elaborator's `alias Cure.Elab.{…, Subst, …}` (line 17) resolves `Subst` to `Cure.Elab.Subst`, which is a genuinely distinct module from the kernel's `Cure.Core.Term` — it does **not** delegate, but reimplements a full parallel set of structural-recursion `shift/3` clauses (plus an extra `{:meta, _}` passthrough clause `Term.shift` lacks), starting at `lib/cure/elab/subst.ex:91` (`def shift(term, 0, _cutoff), do: term`). Same signature shape as `Cure.Core.Term.shift/3` (`term.ex:88`), so `match_target`'s call to `Subst.shift(target, depth, 0)` resolves correctly to `Cure.Elab.Subst.shift/3` with no further change needed.

- [ ] **Step 4: Run the test to verify it passes**

Run: `mix test test/cure/elab/dependent_match_surface_test.exs`
Expected: all Task 4 tests plus the new verbatim test PASS.

- [ ] **Step 5: Run the full suite once (end of Slice 3)**

Run: `mix test`
Expected: baseline 2173 + all new tests, zero regressions. Existing motive tests (constant motive, bare-var generalization in `vec_dependent_test.exs`) must stay green — they are the degenerate cases of the unified rule (step 3).

- [ ] **Step 6: Commit**

```bash
git add lib/cure/elab/elaborator.ex test/cure/elab/dependent_match_surface_test.exs
git commit -m "feat(elab): whole-subterm motive generalization for verbatim index reuse (④ Slice 3)"
```

---

## Self-Review

**Spec coverage check (§ by §):**
- §2 (A) omit impossible → Task 4 test 1. (A) omit reachable → Task 4 test 2. (A) explicit impossible verified → Task 4 test 3. (A) mis-marked rejected → Task 4 test 4. (Completeness) compound/bare-scrutinee → Task 1 compound-solved unit test + Task 5 delegation (realization note). (Completeness) verbatim reuse → Task 6 test.
- §3 `branch_unify/4` signature + frame → Task 1. Whole-subterm algorithm (4 steps) → Task 6. Case (b) excluded → not implemented (documented, §9).
- §4 soft keyword (no `@keywords` change) → Task 3. `constructor_pattern` clean error → Task 4 step 3.
- §5 partition gap (arm-family validation) → Task 4 `partition_arms`. Duplicate arms → `{:duplicate_branch,_}`. Matched-but-impossible → `elaborate_matched_branch` `:impossible` arm (unchecked `elaborate_expr_typed`). `{:absurd}` kernel clause → Task 2. `{:absurd}` serialize/emit surface → Task 2.
- §6 slices → Tasks map: Slice 1 = Task 1; Slice 2 = Tasks 2–4; Slice 3 = Tasks 5–6.
- §7 testing: kernel unit (Task 1), surface positive+negative asserting exact atoms (Task 4/6), Antigen verticals stay green (full-suite runs), full suite once per slice (Tasks 1/4/6 step "run full suite once").
- §8 invariants: TCB delta = wrapper + always-fails clause (Tasks 1/2). Kernel backstop unchanged (`check_coverage` untouched). Frame alignment pinned by Task 1 tests.

**Placeholder scan:** No TBD/TODO. Every code step shows complete code. Two items that were originally flagged as "confirm against the tree before finalizing" (Task 3's arm-terminator lookahead; Task 6's `Subst` module identity) have been resolved during hardening: Task 3 uses the tree's existing `peek_at/2` (not a nonexistent `peek/2`), and Task 6 cites `Cure.Elab.Subst.shift/3` (`subst.ex:91`) directly rather than the kernel's distinct `Cure.Core.Term.shift/3` (`term.ex:88`).

**Type consistency:** `branch_unify/4` verdict shape `{:solved, map()} | :trivial | :impossible` is consistent across Tasks 1, 4, 5. `elaborate_matched_branch` produces `{cname, arity, body_term}` branch tuples matching the kernel's `{c, ar, b}` shape (`kernel.ex:660`). Error atoms `{:missing_branch,_}`, `{:reachable_impossible,_}`, `{:duplicate_branch,_}`, `{:foreign_ctor,_}`, `{:unsupported_pattern,_}` are used consistently in Task 4 code and asserted in Task 4 tests.

**Known realization deviation from spec §6:** Slice 3(i) is realized as a unit test + end-to-end program rather than a standalone surface fixture — documented in Task 5's realization note with a concrete reproducing `.cure` fixture and the structural reason (the kernel's own independent motive-based recheck already subsumes this shape), not a bare unreproducible empirical claim.
