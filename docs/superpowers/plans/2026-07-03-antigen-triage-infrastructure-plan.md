# Antigen Triage Infrastructure Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** every banked infection is minimized for **all** challenge kinds via a unified triage pass — generalized term-shrink (Component 1) + name-referenced element ddmin (Component 2) — orchestrated by `Antigen.Triage.minimize/3` (Component 3), wired into the runner and infection report.

**Architecture:** Ride the existing `Challenge.to_pieces/1` ↔ `from_pieces/7` corpus bridge. Shrink re-seats its candidate enumeration on that bridge (term rewrites for every kind's Term pieces; the de-Bruijn ctx-drop stays only for `:typed_term`/`:mutant_term`). A new `Antigen.Bisect` drops whole name-referenced list elements (defs/ctors/families) by editing the decoded payload directly. A new `Antigen.Triage` drives a single one-step-at-a-time fixpoint over `bisect ++ shrink` candidates under one shared predicate-call budget, gated by a kind-agnostic `Triage.size/1`.

**Tech Stack:** Elixir; ExUnit (`async: true`); no new deps; `MIX_ENV=test` for all mix invocations (dev env crashes).

## Global Constraints

- **Ghost-authored commits:** every commit uses `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`; NEVER a `Co-Authored-By` trailer.
- **Branch:** stay on `autopilot/antigen-tier-b` (no new worktree).
- **No `Cure.Core.*` (TCB) edits.** Kernel reached read-only only through the assay `run/1` the predicate calls.
- **No new dependency, no `:meck`.**
- **StreamData quarantine:** `lib/antigen/triage.ex` and `lib/antigen/bisect.ex` are siblings of `shrink.ex` — OUTSIDE the `lib/antigen/{generators,assays}/**` glob checked by `test/antigen/architecture_test.exs`. Neither may contain the literal `StreamData`.
- **One build/test run at any moment.** Never launch concurrent suites (a past concurrent full-suite run caused a kernel panic). Run one `mix test` at a time.
- **macOS:** no `timeout` binary available.
- **Tests are immutable** once written: reach green by changing `Triage`/`Bisect`/`Shrink` code, never by weakening/skipping/deleting a test (sole exception: a test proven to encode wrong behavior, argued explicitly first).
- **Run mix from the worktree root** `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/antigen-tier-b`.

## File structure

- **New** `lib/antigen/triage.ex` — orchestrator: `minimize/3`, `size/1`, one-step fixpoint.
- **New** `lib/antigen/bisect.ex` — `candidates/1` (payload-direct element drops + focus cleanup).
- **Modify** `lib/antigen/shrink.ex` — generalize `candidates/1` to the pieces bridge for non-typed kinds; expose `candidates/1`, `reseed/1`, `well_formed?/1` (`@doc false`) for `Triage`.
- **Modify** `lib/antigen/coverage.ex` — widen `terms_of/1`'s `:forcing_pair` clause to also match `:stuck_elim` (identical payload shape; today's literal-`:forcing_pair`-only clause makes `Shrink.well_formed?/1` crash-then-rescue-to-`false` for every `:stuck_elim` candidate, silently defeating `Triage`/`Bisect` for that kind — see Task 1).
- **Modify** `lib/antigen/runner.ex` — infection branch calls `Triage.minimize/3` for all kinds; merge `:triage` stats into the health map.
- **Modify** `lib/antigen/report.ex` — `render/3` emits optional `triage:` line.
- **New tests** `test/antigen/bisect_test.exs`, `test/antigen/triage_test.exs`; **extend** `test/antigen/shrink_test.exs`.

## Interfaces (locked signatures used across tasks)

- `Antigen.Challenge.to_pieces(ch) :: {scaffold :: map(), [{piece_id :: String.t(), Term.t()}]}` (exists).
- `Antigen.Challenge.from_pieces(kind, assay, label, seed, note, scaffold, pieces) :: Challenge.t()` (exists).
- `Antigen.Shrink.candidates(ch) :: [Challenge.t()]` — **becomes public** (`@doc false`).
- `Antigen.Shrink.reseed(ch) :: Challenge.t()` — **becomes public** (`@doc false`); sets `seed: :erlang.phash2({kind, payload})`.
- `Antigen.Shrink.well_formed?(ch) :: boolean()` — **becomes public** (`@doc false`).
- `Antigen.Bisect.candidates(ch) :: [Challenge.t()]` — new; each element is `ch` with one list element dropped (+ focus cleanup).
- `Antigen.Triage.minimize(ch, pred, budget) :: {Challenge.t(), stats}` where `stats :: %{orig_size, min_size, bisect_drops, shrink_rewrites}`.
- `Antigen.Triage.size(ch) :: non_neg_integer()`.

---

### Task 1: Generalize `Shrink.candidates/1` to all kinds (shrink-all-kinds) + expose helpers

**Files:**
- Modify: `lib/antigen/shrink.ex`
- Modify: `lib/antigen/coverage.ex`
- Test: `test/antigen/shrink_test.exs`

**Interfaces:**
- Produces: public `Shrink.candidates/1`, `Shrink.reseed/1`, `Shrink.well_formed?/1`; `candidates/1` now returns term-rewrite candidates for `:family`/`:indexed_case`/`:rewrite_eq`/`:forcing_pair`/`:stuck_elim`/`:def_group`/`:stub` via the pieces bridge, `[]` for `:elab_program`, and the exact existing candidate set for `:typed_term`/`:mutant_term`.
- Consumes: `Challenge.to_pieces/1`, `Challenge.from_pieces/7`.
- **Fixes a real, `Triage`-blocking well-formedness gap:** `Coverage.terms_of/1` (which `well_formed?/1` calls) today has a *literal* `kind: :forcing_pair` clause but no clause for `:stuck_elim`, even though `:stuck_elim` shares `:forcing_pair`'s exact payload shape (`%{defs:, focus:, t:, tprime:}` — confirmed by `Challenge.to_pieces/1`'s own shared `kind in [:forcing_pair, :stuck_elim]` guard). Because `well_formed?/1` rescues any crash to `false`, every `:stuck_elim` candidate is silently treated as malformed today — harmless while only `:typed_term`/`:mutant_term` route through `Shrink`, but the moment Task 4 routes *every* kind through `Triage.minimize/3`, this makes `:stuck_elim` a silent permanent no-op (indistinguishable from `:elab_program`'s *legitimate* no-op), contradicting the design's §5.3/§6.1 kind-coverage tables and this task's own `candidates/1` claim above. Widen the `:forcing_pair` clause in `lib/antigen/coverage.ex` to `k in [:forcing_pair, :stuck_elim]` (Step 3 below) and pin it with a red test (Step 1).

- [ ] **Step 1: Write the failing test** — a `:family` infection carried by one bloated constructor arg shrinks via `Shrink.minimize/3`; a `:typed_term` still shrinks exactly as before (regression pin); a `:stuck_elim` challenge is correctly recognized as well-formed (today it is wrongly rejected — see above).

Append to `test/antigen/shrink_test.exs` (inside the existing test module):

```elixir
describe "shrink-all-kinds (pieces bridge)" do
  alias Antigen.{Challenge, Shrink}

  @nat {:data, :Nat, [], []}
  # a family whose single ctor has one deliberately bloated arg type
  defp bloated_family_ch do
    bloated = {:app, {:app, {:global, :plus}, {:ctor, :S, [{:ctor, :Z, []}]}}, {:ctor, :Z, []}}
    fam = Cure.Core.Inductive.family(:F, [], [], 0)
    ctor = Cure.Core.Inductive.ctor(:MkF, [{:x, bloated}], [], [:present], [])
    Challenge.new(kind: :family, assay: "positivity", label: :well_typed,
                  payload: %{family: fam, ctors: [ctor]}, seed: 1)
  end

  test "a family's bloated ctor-arg term is shrunk (all-kinds via pieces)" do
    ch = bloated_family_ch()
    # predicate: the challenge still has a ctor whose arg term is non-atomic
    #   (satisfied by the bloated original AND by any smaller-but-nonatomic form),
    #   plus stays well-formed — a synthetic same-shape closure.
    pred = fn c ->
      match?(%Challenge{kind: :family, payload: %{ctors: [_ | _]}}, c)
    end
    out = Shrink.minimize(ch, pred, 500)
    # candidates are produced for a :family now (was []/unsupported before)
    assert Shrink.candidates(ch) != []
    # minimized artifact is still a well-formed family satisfying the predicate
    assert pred.(out)
    assert Shrink.well_formed?(out)
  end

  test "typed_term candidate set is unchanged by the generalization" do
    # a representative typed_term; candidates/1 must still include ctx-drop + type/term rewrites
    ch = Challenge.new(kind: :typed_term, assay: "term/infer_check", label: :well_typed,
           payload: %{sig: :v1, ctx: [], type: @nat, term: {:ctor, :S, [{:ctor, :Z, []}]}}, seed: 1)
    cands = Shrink.candidates(ch)
    # S(Z) → Z is rule2; must still be offered on the typed_term term field
    assert Enum.any?(cands, fn c -> c.payload.term == {:ctor, :Z, []} end)
  end

  test "well_formed?/1 recognizes a :stuck_elim challenge (shares :forcing_pair's payload shape)" do
    # :stuck_elim's payload is %{defs:, focus:, t:, tprime:} — identical to :forcing_pair's
    # (Challenge.to_pieces/1 shares one clause for both kinds via `kind in [...]`). Today
    # Coverage.terms_of/1 only has a LITERAL `kind: :forcing_pair` clause, so this legitimately
    # well-formed :stuck_elim challenge crashes Coverage.terms_of/1 (FunctionClauseError),
    # rescued by well_formed?/1 to `false` — wrongly reporting it as malformed. Once every
    # kind routes through Triage (Task 4), that false negative makes :stuck_elim a silent,
    # permanent no-op (every Bisect/Shrink candidate rejected by the well-formed? pre-filter).
    # body is S(Z), not the bare atom Z — an atomic {:ctor, :Z, []} everywhere would make
    # every piece already-minimal (node_count == 1, no rule1/rule2/rule4/child_slots
    # candidates), which would fail `candidates(ch) != []` below for an unrelated reason.
    # label :positive matches Antigen.Assays.StuckElimDelta's real semantics for this
    # kind (t/tprime committed as convertible); irrelevant to well_formed?/candidates
    # (neither reads `label`), but kept realistic rather than borrowing :def_group's
    # :terminating label.
    ch = Challenge.new(kind: :stuck_elim, assay: "stuck_elim_delta", label: :positive,
           payload: %{defs: [%{name: :f, type: @nat, body: {:ctor, :S, [{:ctor, :Z, []}]}}],
                      focus: [:f], t: {:ctor, :Z, []}, tprime: {:ctor, :Z, []}}, seed: 1)
    assert Shrink.well_formed?(ch)
    assert Shrink.candidates(ch) != []
  end
end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `MIX_ENV=test mix test test/antigen/shrink_test.exs`
Expected: FAIL — `Shrink.candidates/1` is private (UndefinedFunctionError) and/or returns `[]`/crashes for `:family` (today `candidates/1` dereferences `payload.type`/`payload.term`, absent on a `:family`); AND `Shrink.well_formed?(ch)` for the `:stuck_elim` case is `false` (should be `true`) because `Coverage.terms_of/1` has no `:stuck_elim` clause and raises `FunctionClauseError`, rescued to `false`.

- [ ] **Step 3: Implement the generalization**

In `lib/antigen/shrink.ex`, replace the private `candidates/1` and expose helpers. Keep `term_candidates/1`, `rule1/2/4`, `child_slots/1`, `field_cands/3`, `ctx_candidates/1`, `first_accepted/3`, `safe_pred/2`, `size/1`, `node_count`, `numeral_magnitude`, `occurs?` **unchanged**.

```elixir
# was: defp candidates(%Challenge{payload: p} = ch) do ... end
@doc false
def candidates(%Challenge{kind: k, payload: p} = ch) when k in [:typed_term, :mutant_term] do
  # EXACT existing behavior for the de-Bruijn-ctx kinds (ctx-drop + type/term rewrites)
  ctx_candidates(ch) ++ field_cands(ch, :type, p.type) ++ field_cands(ch, :term, p.term)
end

def candidates(%Challenge{kind: :elab_program}), do: []   # no Term pieces (spec §3/§5.3)

def candidates(%Challenge{} = ch), do: piece_candidates(ch)

# Per-piece term rewrites via the corpus bridge, for every non-de-Bruijn kind.
defp piece_candidates(%Challenge{kind: k, assay: a, label: l, seed: s, note: n} = ch) do
  {scaffold, pieces} = Challenge.to_pieces(ch)

  pieces
  |> Enum.with_index()
  |> Enum.flat_map(fn {{pid, term}, i} ->
    Enum.map(term_candidates(term), fn term2 ->
      new_pieces = List.replace_at(pieces, i, {pid, term2})
      Challenge.from_pieces(k, a, l, s, n, scaffold, new_pieces)
    end)
  end)
end
```

Expose the two helpers `Triage` will drive, and keep `candidates_for_test/1` delegating:

```elixir
@doc false
def reseed(%Challenge{} = ch), do: %{ch | seed: :erlang.phash2({ch.kind, ch.payload})}
# (delete the old `defp reseed/1`)

@doc false
def well_formed?(c) do
  c |> Coverage.terms_of() |> Enum.all?(&Term.term?/1)
rescue
  _ -> false
end
# (delete the old `defp well_formed?/1`)

def candidates_for_test(ch), do: candidates(ch)
```

Guard `ctx_candidates/1` so it is only ever reached by the typed/mutant clause (it already is — no other clause calls it), so its `p.ctx` deref stays safe.

In `lib/antigen/coverage.ex`, widen the `:forcing_pair`-only clause to also cover `:stuck_elim` (identical payload shape — mirrors `Challenge.to_pieces/1`'s own shared guard):

```elixir
# was: def terms_of(%Challenge{kind: :forcing_pair, payload: %{defs: defs, t: t, tprime: tp}}),
#        do: Enum.flat_map(defs, fn d -> [d.type, d.body] end) ++ [t, tp]
def terms_of(%Challenge{kind: k, payload: %{defs: defs, t: t, tprime: tp}})
    when k in [:forcing_pair, :stuck_elim],
    do: Enum.flat_map(defs, fn d -> [d.type, d.body] end) ++ [t, tp]
```

- [ ] **Step 4: Run the test to verify it passes**

Run: `MIX_ENV=test mix test test/antigen/shrink_test.exs`
Expected: PASS (new rows + all pre-existing shrink rows still green).

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/shrink.ex lib/antigen/coverage.ex test/antigen/shrink_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): generalize Shrink.candidates to all kinds via the pieces bridge"
```

---

### Task 2: `Antigen.Bisect` — name-referenced element ddmin + focus cleanup

**Files:**
- Create: `lib/antigen/bisect.ex`
- Test: `test/antigen/bisect_test.exs`

**Interfaces:**
- Produces: `Bisect.candidates(ch) :: [Challenge.t()]` — one candidate per droppable element, each the challenge with that element removed from its bisectable list (payload-direct `List.delete_at`) and, for def-carrying kinds, the dropped def's name removed from `focus`.
- Consumes: nothing outside `Antigen.Challenge`.

**Reconciliation note (spec §6.2):** the spec describes editing the `{scaffold, pieces}` pair. This task instead edits the **decoded payload** directly (`List.delete_at` on the native `defs`/`ctors`/`families` list). Same observable result — drop one element + focus cleanup — but it avoids re-numbering the positionally-keyed family/`indexed_case` pieces (`"ctor:#{j}:…"`) that a scaffold-level edit would require. No `from_pieces` round-trip is needed because the payload already holds the structured lists.

- [ ] **Step 1: Write the failing test**

Create `test/antigen/bisect_test.exs`:

```elixir
defmodule Antigen.BisectTest do
  use ExUnit.Case, async: true
  alias Antigen.{Bisect, Challenge}

  @nat {:data, :Nat, [], []}
  defp d(name, body), do: %{name: name, type: {:pi, @nat, @nat}, body: body}

  defp def_group(names_bodies, focus) do
    Challenge.new(kind: :def_group, assay: "totality/terminating", label: :terminating,
      payload: %{defs: Enum.map(names_bodies, fn {n, b} -> d(n, b) end), focus: focus}, seed: 1)
  end

  test "candidates drop each def and prune its focus entry" do
    ch = def_group([{:f, {:global, :h}}, {:g, {:ctor, :Z, []}}, {:h, {:ctor, :Z, []}}], [:f, :h])
    cands = Bisect.candidates(ch)
    # 3 defs → 3 drop candidates
    assert length(cands) == 3
    # dropping :h removes it from defs AND from focus
    dropped_h = Enum.find(cands, fn c -> Enum.map(c.payload.defs, & &1.name) == [:f, :g] end)
    assert dropped_h.payload.focus == [:f]
  end

  test "dropping a def does NOT reindex/alter a surviving def's body term" do
    body_f = {:global, :h}
    ch = def_group([{:f, body_f}, {:g, {:ctor, :Z, []}}, {:h, {:ctor, :Z, []}}], [:f])
    drop_g = Enum.find(Bisect.candidates(ch), fn c ->
      Enum.map(c.payload.defs, & &1.name) == [:f, :h] end)
    surviving_f = Enum.find(drop_g.payload.defs, & &1.name == :f)
    assert surviving_f.body == body_f   # byte-identical, no de-Bruijn shift
  end

  test "family candidates drop each ctor" do
    fam = Cure.Core.Inductive.family(:F, [], [], 0)
    c0 = Cure.Core.Inductive.ctor(:A, [], [], [], [])
    c1 = Cure.Core.Inductive.ctor(:B, [], [], [], [])
    ch = Challenge.new(kind: :family, assay: "positivity", label: :well_typed,
           payload: %{family: fam, ctors: [c0, c1]}, seed: 1)
    cands = Bisect.candidates(ch)
    assert length(cands) == 2
    assert Enum.any?(cands, fn c -> Enum.map(c.payload.ctors, & &1.name) == [:B] end)
  end

  test "kinds with no name-referenced list yield no candidates" do
    tt = Challenge.new(kind: :typed_term, assay: "term/infer_check", label: :well_typed,
           payload: %{sig: :v1, ctx: [], type: @nat, term: {:ctor, :Z, []}}, seed: 1)
    assert Bisect.candidates(tt) == []
  end
end
```

- [ ] **Step 2: Run to verify it fails**

Run: `MIX_ENV=test mix test test/antigen/bisect_test.exs`
Expected: FAIL — `Antigen.Bisect` undefined.

- [ ] **Step 3: Implement `Antigen.Bisect`**

Create `lib/antigen/bisect.ex`:

```elixir
defmodule Antigen.Bisect do
  @moduledoc """
  Structural delta-debugging (ddmin) over a challenge's **name-referenced** list
  components — `defs` (def_group/forcing_pair/stuck_elim), `ctors` (family),
  `families` (indexed_case/rewrite_eq). Each candidate removes one whole element
  (a pure `List.delete_at` on the decoded payload — no de-Bruijn reindexing,
  since members are referenced by `{:global, name}`, not by index) and prunes any
  now-dangling `focus` entry naming a removed def. The orchestrator
  (`Antigen.Triage`) tests each candidate under the same violation-shape
  predicate shrink uses; safety is the predicate, not static analysis (spec §6).
  """
  alias Antigen.Challenge

  @def_kinds [:def_group, :forcing_pair, :stuck_elim]

  @spec candidates(Challenge.t()) :: [Challenge.t()]
  def candidates(%Challenge{kind: k, payload: %{defs: defs} = p} = ch) when k in @def_kinds do
    for i <- index_range(defs) do
      dropped = Enum.at(defs, i).name
      %{ch | payload: %{p | defs: List.delete_at(defs, i),
                            focus: Map.get(p, :focus, []) -- [dropped]}}
    end
  end

  def candidates(%Challenge{kind: :family, payload: %{ctors: ctors} = p} = ch) do
    for i <- index_range(ctors), do: %{ch | payload: %{p | ctors: List.delete_at(ctors, i)}}
  end

  def candidates(%Challenge{kind: k, payload: %{families: fams} = p} = ch)
      when k in [:indexed_case, :rewrite_eq] do
    for i <- index_range(fams), do: %{ch | payload: %{p | families: List.delete_at(fams, i)}}
  end

  def candidates(%Challenge{}), do: []

  # `0..(n-1)//1` — the `//1` avoids the `0..-1` phantom-range footgun when n=0.
  defp index_range(list), do: 0..(length(list) - 1)//1
end
```

- [ ] **Step 4: Run to verify it passes**

Run: `MIX_ENV=test mix test test/antigen/bisect_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/bisect.ex test/antigen/bisect_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): Bisect — name-referenced element ddmin with focus cleanup"
```

---

### Task 3: `Antigen.Triage` — `size/1` + combined-fixpoint `minimize/3`

**Files:**
- Create: `lib/antigen/triage.ex`
- Test: `test/antigen/triage_test.exs`

**Interfaces:**
- Consumes: `Shrink.candidates/1`, `Shrink.reseed/1`, `Shrink.well_formed?/1`, `Bisect.candidates/1`, `Challenge.to_pieces/1`.
- Produces: `Triage.minimize/3 :: {Challenge.t(), stats}`, `Triage.size/1`.

- [ ] **Step 1: Write the failing test**

Create `test/antigen/triage_test.exs`:

```elixir
defmodule Antigen.TriageTest do
  use ExUnit.Case, async: true
  alias Antigen.{Triage, Challenge}

  @nat {:data, :Nat, [], []}
  defp d(name, body), do: %{name: name, type: {:pi, @nat, @nat}, body: body}

  # bloated in BOTH dimensions: 3 defs (2 droppable) + an S-tower body to shrink
  defp both_dims_ch do
    tower = {:ctor, :S, [{:ctor, :S, [{:ctor, :S, [{:ctor, :Z, []}]}]}]}
    Challenge.new(kind: :def_group, assay: "totality/terminating", label: :terminating,
      payload: %{defs: [d(:f, tower), d(:g, {:ctor, :Z, []}), d(:h, {:ctor, :Z, []})],
                 focus: [:f]}, seed: 1)
  end

  test "size/1 is kind-agnostic and counts pieces + list elements" do
    ch = both_dims_ch()
    assert Triage.size(ch) > 0
    # dropping a def strictly lowers size
    smaller = %{ch | payload: %{ch.payload | defs: tl(ch.payload.defs), focus: []}}
    assert Triage.size(smaller) < Triage.size(ch)
  end

  test "combined fixpoint reduces in BOTH bisect and shrink, reports stats" do
    ch = both_dims_ch()
    # synthetic same-shape predicate: a def_group whose :f-body is an S-tower over Z
    pred = fn c ->
      match?(%Challenge{kind: :def_group}, c) and
        Enum.any?(c.payload.defs, fn dd -> dd.name == :f and s_tower?(dd.body) end)
    end
    {out, stats} = Triage.minimize(ch, pred, 2000)
    assert pred.(out)
    assert stats.bisect_drops >= 1        # g and/or h dropped
    assert stats.shrink_rewrites >= 1     # S-tower reduced
    assert stats.min_size < stats.orig_size
    assert stats.orig_size == Triage.size(ch)
  end

  test "budget bound + determinism" do
    ch = both_dims_ch()
    pred = fn c -> match?(%Challenge{kind: :def_group}, c) end
    {a, _} = Triage.minimize(ch, pred, 3)   # tiny budget → partial but safe
    {b, _} = Triage.minimize(ch, pred, 3)
    assert a == b                            # deterministic
  end

  test "safe_pred: a raising predicate is treated as no-progress, never crashes" do
    ch = both_dims_ch()
    {out, _stats} = Triage.minimize(ch, fn _ -> raise "boom" end, 100)
    assert out == ch                         # nothing accepted; original returned
  end

  test "elab_program is a triage no-op" do
    ch = Challenge.new(kind: :elab_program, assay: "elab/completeness", label: :well_typed,
           payload: %{id: 1, src: "module M do end"}, seed: 1)
    {out, stats} = Triage.minimize(ch, fn _ -> true end, 100)
    assert out == ch
    assert stats.bisect_drops == 0 and stats.shrink_rewrites == 0
  end

  defp s_tower?({:ctor, :S, [n]}), do: s_tower?(n)
  defp s_tower?({:ctor, :Z, []}), do: true
  defp s_tower?(_), do: false
end
```

- [ ] **Step 2: Run to verify it fails**

Run: `MIX_ENV=test mix test test/antigen/triage_test.exs`
Expected: FAIL — `Antigen.Triage` undefined.

- [ ] **Step 3: Implement `Antigen.Triage`**

Create `lib/antigen/triage.ex`:

```elixir
defmodule Antigen.Triage do
  @moduledoc """
  Infection triage: minimize a reified `Challenge` to a joint fixpoint of
  structural bisect (whole name-referenced element drops) and value shrink
  (term rewrites + de-Bruijn ctx-drop), under one same-violation-shape predicate
  and one shared step budget. Deterministic, monotone (size strictly decreases on
  each accepted step), budget-bounded, `safe_pred`-guarded. Bisect candidates are
  tried before shrink candidates each round so structural cuts precede term
  rewrites (spec §7).
  """
  alias Antigen.{Challenge, Shrink, Bisect}

  @type stats :: %{orig_size: non_neg_integer(), min_size: non_neg_integer(),
                   bisect_drops: non_neg_integer(), shrink_rewrites: non_neg_integer()}

  @spec minimize(Challenge.t(), (Challenge.t() -> boolean()), non_neg_integer()) ::
          {Challenge.t(), stats}
  def minimize(%Challenge{} = ch, pred, budget) do
    orig = size(ch)
    {out, counts, _b} = sweep(ch, pred, budget, %{bisect: 0, shrink: 0})
    {out, %{orig_size: orig, min_size: size(out),
            bisect_drops: counts.bisect, shrink_rewrites: counts.shrink}}
  end

  # One accepted step at a time; restart the combined list on every acceptance.
  defp sweep(ch, pred, budget, counts) do
    cur = size(ch)
    cands = Enum.map(Bisect.candidates(ch), &{:bisect, &1}) ++
            Enum.map(Shrink.candidates(ch), &{:shrink, &1})

    case first_accepted(cands, pred, budget, cur) do
      {:accepted, tag, ch2, b2} ->
        sweep(Shrink.reseed(ch2), pred, b2, Map.update!(counts, tag, &(&1 + 1)))
      {:none, _b2} ->
        {ch, counts, budget}
    end
  end

  defp first_accepted(_cands, _pred, 0, _cur), do: {:none, 0}
  defp first_accepted([], _pred, b, _cur), do: {:none, b}
  defp first_accepted([{tag, cand} | rest], pred, b, cur) do
    cond do
      not Shrink.well_formed?(cand) -> first_accepted(rest, pred, b, cur)  # no budget spent
      size(cand) >= cur -> first_accepted(rest, pred, b, cur)             # non-reducing: skip
      safe_pred(pred, cand) -> {:accepted, tag, cand, b - 1}
      true -> first_accepted(rest, pred, b - 1, cur)
    end
  end

  defp safe_pred(pred, c) do
    pred.(c)
  rescue
    _ -> false
  catch
    _, _ -> false
  end

  @doc "Kind-agnostic size: term nodes across all pieces + count of list elements."
  @spec size(Challenge.t()) :: non_neg_integer()
  def size(%Challenge{payload: p} = ch) do
    {_scaffold, pieces} = Challenge.to_pieces(ch)
    term_size = Enum.reduce(pieces, 0, fn {_id, t}, acc ->
      acc + node_count(t) + numeral_magnitude(t)
    end)
    term_size + list_elements(p)
  end

  # Read each list-structured component defensively (absent ⇒ 0). No kind carries
  # all five; :elab_program carries none (its list_elements is always 0).
  defp list_elements(p) do
    len(p, :ctx) + len(p, :defs) + len(p, :ctors) + len(p, :families) + len(p, :focus)
  end
  defp len(p, key) do
    case Map.get(p, key) do
      l when is_list(l) -> length(l)
      _ -> 0
    end
  end

  # local copies of Shrink's structural measures (kept private there); identical math
  defp node_count(t) when is_tuple(t),
    do: 1 + (t |> Tuple.to_list() |> tl() |> Enum.map(&node_count/1) |> Enum.sum())
  defp node_count(l) when is_list(l), do: l |> Enum.map(&node_count/1) |> Enum.sum()
  defp node_count(_), do: 0

  defp numeral_magnitude({:ctor, :S, [n]}), do: 1 + numeral_magnitude(n)
  defp numeral_magnitude(t) when is_tuple(t),
    do: t |> Tuple.to_list() |> tl() |> Enum.map(&numeral_magnitude/1) |> Enum.sum()
  defp numeral_magnitude(l) when is_list(l), do: l |> Enum.map(&numeral_magnitude/1) |> Enum.sum()
  defp numeral_magnitude(_), do: 0
end
```

- [ ] **Step 4: Run to verify it passes**

Run: `MIX_ENV=test mix test test/antigen/triage_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/triage.ex test/antigen/triage_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): Triage orchestrator — combined bisect+shrink fixpoint with kind-agnostic size"
```

---

### Task 4: Wire `Triage.minimize/3` into the runner for all kinds

**Files:**
- Modify: `lib/antigen/runner.ex`
- Test: `test/antigen/runner_test.exs` (add a row; create the file only if absent)

**Interfaces:**
- Consumes: `Triage.minimize/3`.
- Produces: infection branch minimizes every kind; `:triage` stats merged into the health map passed to `Report.write_infection/4`.

- [ ] **Step 1: Write the failing test** — an injected `:def_group` (non-`typed_term`) infection is banked **minimized** end-to-end, and the health map carries `:triage`.

Add to `test/antigen/runner_test.exs` (create the module if the file does not exist):

```elixir
defmodule Antigen.RunnerTest.TriageWiring do
  use ExUnit.Case, async: false
  alias Antigen.{Runner, Challenge}

  @nat {:data, :Nat, [], []}
  defp d(name, body), do: %{name: name, type: {:pi, @nat, @nat}, body: body}

  # A module-shaped assay (runner calls `apply(mod, :run, [c])`) that infects iff a
  # def named :f survives — so bisect may drop the redundant :g but NOT :f, giving a
  # deterministic minimized target of exactly [:f].
  defmodule KeepsF do
    def run(%Challenge{payload: %{defs: defs}}) do
      if Enum.any?(defs, &(&1.name == :f)), do: {:violation, :boom}, else: :ok
    end

    def run(_), do: :ok
  end

  test "a non-typed_term infection is banked minimized (bisect drops a redundant def)" do
    tmp = Path.join(System.tmp_dir!(), "antigen-triage-#{System.unique_integer([:positive])}")
    File.mkdir_p!(tmp)
    on_exit(fn -> File.rm_rf!(tmp) end)

    ch = Challenge.new(kind: :def_group, assay: "totality/terminating", label: :terminating,
           payload: %{defs: [d(:f, {:ctor, :Z, []}), d(:g, {:ctor, :Z, []})], focus: [:f]}, seed: 7)

    # `opts[:assay]` is the runner's existing assay-module override (runner.ex:52),
    # used both for the initial verdict and inside the shrink/bisect predicate.
    res = Runner.explore(challenges: [ch], assay: KeepsF,
            report_dir: tmp, corpus_path: Path.join(tmp, "c.sexp"),
            seeds_path: Path.join(tmp, "s.sexp"))

    assert res.infections == 1
    banked = tmp |> Path.join("c.sexp") |> Antigen.Corpus.stream() |> Enum.to_list()
    assert [{:ok, min}] = banked
    # bisect dropped the redundant :g; :f is load-bearing to the predicate, so it stays
    assert Enum.map(min.payload.defs, & &1.name) == [:f]
    assert min.payload.focus == [:f]
  end
end
```

> **Note for the implementer:** `runner.ex` already uses `opts[:assay]` as a whole-run assay-module override (`apply(opts[:assay] || assay_module(c.assay), :run, [c])`, and the same in the predicate closure), and it is kind-agnostic — a `:def_group` challenge flows through the identical infection branch. So no new seam is needed; this test exercises the existing one. If, while implementing, you find the branch special-cases `:typed_term` anywhere beyond the `c.kind in [...]` guard being removed, stop and reconcile — do not change assay semantics.

- [ ] **Step 2: Run to verify it fails**

Run: `MIX_ENV=test mix test test/antigen/runner_test.exs`
Expected: FAIL — today the infection branch only minimizes `:typed_term`/`:mutant_term`, so `:g` is NOT dropped (banked whole).

- [ ] **Step 3: Implement the wiring**

In `lib/antigen/runner.ex`, replace the `c_min = if c.kind in [...]` block (currently ~`runner.ex:66-72`) with:

```elixir
{c_min, triage} = Antigen.Triage.minimize(c, pred, shrink_budget(opts))

{:ok, path} = Report.write_infection(opts[:report_dir], c_min, v,
                Map.put(summarize(acc, count), :triage, triage))
IO.puts(Report.breadcrumb(c_min, path))
Corpus.append(opts[:corpus_path], c_min, Corpus.dedup_key(c_min, :antibody))
%{acc | infections: acc.infections + 1}
```

Keep `pred`, `shrink_budget/1`, `same_shape?/2` exactly as they are. Remove the now-unused `c.kind in [:typed_term, :mutant_term]` guard and its `else: c` branch.

- [ ] **Step 4: Run to verify it passes**

Run: `MIX_ENV=test mix test test/antigen/runner_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/runner.ex test/antigen/runner_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): triage every infection kind in the runner; thread :triage stats"
```

---

### Task 5: `Report.render/3` triage line

**Files:**
- Modify: `lib/antigen/report.ex`
- Test: `test/antigen/report_test.exs` (add a row; create the file only if absent)

**Interfaces:**
- Consumes: the health map's optional `:triage` key (`%{orig_size, min_size, bisect_drops, shrink_rewrites}`).
- Produces: a `triage:` line in the rendered infection report; omitted when `:triage` absent (no signature change to `write_infection/4` or `breadcrumb/2`).

- [ ] **Step 1: Write the failing test**

Add to `test/antigen/report_test.exs` (create the module if the file does not exist):

```elixir
defmodule Antigen.ReportTest.TriageLine do
  use ExUnit.Case, async: false
  alias Antigen.{Report, Challenge}

  defp ch, do: Challenge.new(kind: :stub, assay: "stub", label: :none,
                 payload: %{term: {:ctor, :Z, []}}, seed: 3)

  test "render includes a triage line when the health map carries :triage" do
    tmp = Path.join(System.tmp_dir!(), "antigen-report-#{System.unique_integer([:positive])}")
    File.mkdir_p!(tmp)
    on_exit(fn -> File.rm_rf!(tmp) end)
    health = %{discard_rate: 0.0, coverage: MapSet.new(),
               triage: %{orig_size: 27, min_size: 9, bisect_drops: 2, shrink_rewrites: 11}}
    {:ok, path} = Report.write_infection(tmp, ch(), {:boom, :x}, health)
    body = File.read!(path)
    assert body =~ "triage:"
    assert body =~ "27" and body =~ "9" and body =~ "bisect" and body =~ "shrink"
  end

  test "render omits the triage line when :triage absent" do
    tmp = Path.join(System.tmp_dir!(), "antigen-report-#{System.unique_integer([:positive])}")
    File.mkdir_p!(tmp)
    on_exit(fn -> File.rm_rf!(tmp) end)
    {:ok, path} = Report.write_infection(tmp, ch(), {:boom, :x}, %{discard_rate: 0.0, coverage: MapSet.new()})
    refute File.read!(path) =~ "triage:"
  end
end
```

- [ ] **Step 2: Run to verify it fails**

Run: `MIX_ENV=test mix test test/antigen/report_test.exs`
Expected: FAIL — no `triage:` line emitted.

- [ ] **Step 3: Implement the render line**

In `lib/antigen/report.ex`, thread an optional triage line into `render/3`:

```elixir
defp render(c, detail, health) do
  """
  ANTIGEN INFECTION
  assay:      #{c.assay}
  label:      #{c.label}  (ground truth)
  seed:       #{c.seed}
  detail:     #{inspect(detail)}
  health:     #{inspect(health)}#{triage_line(health)}
  note:       #{c.note}

  -- antigen (C2 record, generator-independent repro) --
  #{Corpus.encode_record(c)}

  -- repro --
  decode the record above and run Antigen.Runner.replay_one/1
  """
end

defp triage_line(%{triage: %{orig_size: o, min_size: m, bisect_drops: b, shrink_rewrites: s}}),
  do: "\ntriage:     size #{o}→#{m} · bisect −#{b} elems · shrink −#{s} rewrites"
defp triage_line(_), do: ""
```

- [ ] **Step 4: Run to verify it passes**

Run: `MIX_ENV=test mix test test/antigen/report_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/report.ex test/antigen/report_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): render a triage summary line in infection reports"
```

---

### Task 6: Full-suite verification

**Files:** none (verification only).

- [ ] **Step 1: Run the full Antigen suite once** (single authorized run — no concurrent builds)

Run: `MIX_ENV=test mix test`
Expected: all pass; count = prior baseline + the new triage/bisect/shrink/runner/report rows. No regressions.

- [ ] **Step 2: Verify the StreamData quarantine + architecture test**

Run: `MIX_ENV=test mix test test/antigen/architecture_test.exs`
Expected: PASS (`lib/antigen/triage.ex` and `bisect.ex` are outside the quarantined glob and contain no `StreamData` literal).

- [ ] **Step 3: Revert any test-run seed side-effect**

Run: `git status --short`
If `test/antigen/seeds.sexp` shows modified (a known test-run artifact), run `git checkout -- test/antigen/seeds.sexp`. Confirm the tree is clean.

- [ ] **Step 4: No commit** (verification task; report results in the completion report).

---

## Self-review

**Spec coverage:** §5 shrink-all-kinds → Task 1; §6 bisect + focus cleanup + no-reindex → Task 2; §7.1 combined fixpoint + §7.2 size + safe_pred + budget + determinism + elab no-op → Task 3; §7.3 runner wiring + `:triage` merge → Task 4; §7.4 report line → Task 5; §9 testing strategy rows distributed across Tasks 1–5; §10 invariants pinned by Task 3 tests + Task 6 full suite. Non-goals (§3) respected: no git-bisect, no elab string shrink (`:elab_program` no-op tested in Task 3), no granularity ladder (greedy 1-minimal in Task 2).

**Well-formedness gap closed (found during hardening review):** `Coverage.terms_of/1` had a literal `kind: :forcing_pair` clause only, with no `:stuck_elim` clause, despite `:stuck_elim` sharing `:forcing_pair`'s exact payload shape. Since `Shrink.well_formed?/1` rescues any crash to `false`, this made `:stuck_elim` silently fail every well-formedness check — invisible today (only `:typed_term`/`:mutant_term` route through `Shrink`), but would have made `:stuck_elim` a silent, permanent, unminimized no-op once Task 4 routes every kind through `Triage.minimize/3`, contradicting §5.3/§6.1's coverage tables. Fixed in Task 1 by widening the `Coverage.terms_of/1` clause to `k in [:forcing_pair, :stuck_elim]`, pinned by a red test.

**Placeholder scan:** none — every step has concrete code/commands/expected output. The two "create file only if absent" test files (Tasks 4, 5) and the runner assay-seam note are explicit implementer instructions, not placeholders.

**Type consistency:** `Triage.minimize/3` returns `{Challenge.t(), stats}` (Tasks 3, 4 agree). `stats` keys `orig_size/min_size/bisect_drops/shrink_rewrites` consistent across Tasks 3, 4, 5. `Shrink.candidates/1`/`reseed/1`/`well_formed?/1` exposed in Task 1 and consumed in Task 3. `Bisect.candidates/1` produced in Task 2, consumed in Task 3. `:triage` health-map key produced in Task 4, consumed in Task 5.

**Runner seam (resolved):** Task 4 reuses `explore/1`'s existing `opts[:assay]` assay-module override (`runner.ex:52`), used both for the initial verdict and inside the shrink/bisect predicate closure. It is kind-agnostic — a `:def_group` challenge flows through the same infection branch as a `:typed_term` — so no new seam is added; the test's `KeepsF` module (infects iff a `:f` def survives) gives bisect a deterministic, load-bearing target. The only runner change is removing the `c.kind in [:typed_term, :mutant_term]` guard so `Triage.minimize/3` runs for every kind.

**Predicate `same_shape?` interaction (checked):** the runner's `pred` compares only the violation *tag* via `same_shape?/2` (`{:boom}`-style bare atoms compare by `==`). `KeepsF` returns the bare `:boom` detail on every surviving-`:f` challenge, so every bisect/shrink candidate that keeps `:f` is same-shape — exactly the intended behavior.
