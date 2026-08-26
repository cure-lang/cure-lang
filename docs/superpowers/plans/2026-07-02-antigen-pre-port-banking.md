# Antigen Pre-Port Banking Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Bank, before any transliteration port lands, every Antigen antibody expressible with today's surface/Core forms: the W1 adversarial diverging set, the W2 reach pins (new `reach.sexp` store), the W3 deletion/occurs antibodies, the W4 positivity escape hatches (with a likely kernel fix), and the W5 universes vertical — per `docs/superpowers/specs/antigen/2026-07-02-antigen-pre-port-banking-design.md`.

**Architecture:** Antigen challenges are hand-built Core-term programs whose label (`:diverging`/`:terminating`, `:well_typed`/`:ill_typed`, `:positive`/`:negative`) is correct *by construction*; assays run the kernel and report `:ok` iff the kernel's verdict matches the label. Antibodies are banked as append-only records in `test/antigen/corpus.sexp` (replayed to `:ok` forever); reach pins go in a new third store `test/antigen/reach.sexp` whose replay test pins today's *documented violation*.

**Tech Stack:** Elixir 1.20 / ExUnit; the Cure kernel (`Cure.Core.*`); the Antigen apparatus (`Antigen.{Challenge,Corpus,Runner,Assays,Generators}`).

## Global Constraints

- **Ghost-writer commits:** every `git commit` uses `--author="Made In Heaven <madeinheaven@madeinheaven.com>"` and NO `Co-Authored-By` trailer.
- **Banked stores are append-only:** never edit or delete an existing line of `test/antigen/corpus.sexp`, `seeds.sexp`, or `reach.sexp`. Banking tests are idempotent via `Corpus.append/3` dedup.
- **Closed atom set:** every new generator-produced name (def names, family names, ctor names, telescope binder names) MUST be added to `@known_atoms` in `lib/cure/elab/../../antigen/challenge.ex` (`lib/antigen/challenge.ex:26-42`) or `:safe` corpus decode crashes in processes that never loaded the generator.
- **Full suite before every commit:** `mix test` (not just `test/antigen`). Any task touching `lib/cure/core/` is a TCB change — say so in the commit body with a `TCB:` line.
- **Labels state mathematical truth** (spec D3): a well-founded def is `:terminating` even while the checker rejects it. Every new challenge's `@doc` states its by-construction ground-truth argument.
- Work happens on a dedicated worktree branched from `autopilot/case-index-unification` (creation via superpowers:using-git-worktrees at execution time). Roadmap edits in this plan touch ONLY §3 of `docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md` plus the status cells (and stale-hole parenthetical of row 13) of §2 rows 13, 19, 23 — all other §2 text belongs to the parallel P0 plan (keeps the merge trivial).
- **D4 symmetric reroute (hardened spec D4/gate 4):** a must-*accept*-today challenge (W3's `deletion(:well_typed)`; W5's `:well_typed` probes — NOT W2, whose pins are expected-rejected) that the kernel wrongly rejects is an *incompleteness surprise*, not a soundness hole: keep its `:well_typed` label (D3), pin its current documented violation, and bank it in `test/antigen/reach.sexp` instead of `corpus.sexp`/`seeds.sexp`; the affected ledger row stays open in Task 11 (gate 5). Never relabel, never silently drop.
- **Tests are immutable once they correctly encode intended/observed behavior:** make a red test green by changing implementation code only (or, for a reach/pin entry, by the sanctioned reach→corpus migration in the port that achieves it) — never by deleting, skipping, or weakening an assertion. The one exception is a test that is provably wrong. Reach/pin/audit tests are characterizations of *current* kernel behavior by design (D2/D3): if a Step-1 prediction of the exact violation shape doesn't match what the kernel actually returns on the first red run, correcting the literal to the observed truth *before that entry is banked* is the intended workflow, not a violation of this rule — the record becomes immutable only once committed (append-only, above).

---

### Task 1: W6 — retire the stale hole narrative

**Files:**
- Modify: `lib/antigen/generators/totality.ex` (moduledoc + `diverging_mutual_pair/0` doc/note)
- Modify: `docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md` (§3.1 table cell, §3.2 A1 row, §3.3 first bullet)

**Interfaces:**
- Consumes: nothing.
- Produces: corrected docs only — no code behavior changes. Later tasks write their `@doc`s against this corrected narrative.

- [ ] **Step 1: Confirm the current (stale) text and the green reality**

Run: `mix test test/antigen/assays/totality_test.exs`
Expected: `2 tests, 0 failures` (the assay already asserts the post-fix behavior; only the *generator docs* and the *roadmap §3* still narrate a live hole).

- [ ] **Step 2: Fix the generator moduledoc and `diverging_mutual_pair/0`**

In `lib/antigen/generators/totality.ex`, replace the `@doc` of `diverging_mutual_pair/0`:

```elixir
  @doc """
  The banked 2-cycle: `f = λx. g x`, `g = λx. f x` over `Dec → Dec`. Neither body
  references its own name, so single-body analysis alone cannot witness the cycle;
  `Cure.Core.Certificate` detects it through the signature (mutual-cycle detection,
  the fix for the once-live hole — see `d13d718`) and certifies neither. The pair
  genuinely diverges under δ. Label `:diverging`. Kept forever as the permanent
  regression guard for that fix.
  """
```

and change the `note:` field of the same function from
`"mutual cycle f->g->f (confirmed hole)"` to
`"mutual cycle f->g->f (hole fixed d13d718; permanent regression guard)"`.

(The already-banked corpus record keeps its old note — records are never edited; dedup keys ignore the note, so nothing re-appends.)

In the same file's `@moduledoc`, replace the sentence
`— the generator IS the oracle (umbrella §6), so the deterministic constructors below are cross-checked against the real certifier in the Task-12 self-tests.`
— keep it, but ALSO delete any remaining wording in the file implying the hole is live (grep the file for `confirmed hole` — zero matches after this step).

- [ ] **Step 3: Fix roadmap §3 (three spots)**

In `docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md`:

1. §3.1 table — replace the row
`| `totality/diverging` | non-terminating defs rejected | `diverging_mutual_pair` | 🔴 checker fails it — confirmed hole |`
with
`| `totality/diverging` | non-terminating defs rejected | `diverging_mutual_pair` + W1 adversarial set | solid (hole fixed `d13d718`; antibodies = permanent regression guards) |`

2. §3.2 — in row A1, replace the Priority cell `🔴 highest` with `✅ done (`d13d718`; antibody replays `:ok`)`.

3. §3.3 — replace the bullet
`- **A1 is the only red item** — a known hole whose antibody is already banked, waiting on the checker fix.`
with
`- **A1 is closed** (`d13d718`): the checker conservatively rejects every mutual cycle and the banked antibody replays `:ok`. What remains of mutual recursion is *reach* (accepting well-founded groups — transliteration program P1), not soundness.`

4. §2 row 13 (gate 5 names this; the parallel P0 plan also carries it — whichever runs first does it, and P0 has not run: the row still shows 🔴). Change the row's parenthetical `(confirmed hole; antibody banked, checker must be fixed)` to `(hole fixed `d13d718`; antibody banked as permanent regression guard)` and its status cell `🔴` → `✅`. Touch nothing else in the row (P0 scope-split). If the row is ALREADY corrected (P0 ran first), verify it matches this wording and skip.

- [ ] **Step 4: Run the full suite**

Run: `mix test`
Expected: PASS (docs-only change).

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/generators/totality.ex docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md
git commit -m "docs(antigen): retire the stale mutual-recursion hole narrative (W6/A1 closed)" --author="Made In Heaven <madeinheaven@madeinheaven.com>"
```

---

### Task 2: W1 — five adversarial diverging generators

**Files:**
- Modify: `lib/antigen/generators/totality.ex` (five new public functions)
- Modify: `lib/antigen/challenge.ex` (`@known_atoms`: add `:total_id`)
- Test: `test/antigen/assays/totality_test.exs` (six new tests)

**Interfaces:**
- Consumes: `Antigen.Challenge.new/1`, `Antigen.Assays.Totality.run/1`, `Cure.Core.Certificate.terminating?/3`, `Antigen.Generators.Totality.env_of/1` (existing).
- Produces: `Antigen.Generators.Totality.diverging_three_cycle/0`, `diverging_mediated_cycle/0`, `diverging_permuting_pair/0`, `diverging_regrowing_self/0`, `diverging_one_leg_pair/0` — each returns a `Challenge.t()` with `assay: "totality/diverging"`, `label: :diverging`. Task 3 banks exactly these five.

- [ ] **Step 1: Write the failing tests**

Append to `test/antigen/assays/totality_test.exs` (inside the module):

```elixir
  # -- W1: the adversarial diverging set (pre-port banking spec §4 W1) --------
  # Every one must replay :ok — i.e. the certifier certifies NO focus member.
  # These are the Lee–Jones–Ben-Amram discriminators, banked BEFORE the P1
  # size-change port so the permissiveness transition is born inside the net.

  test "W1: 3-cycle f→g→h→f is not certified" do
    assert :ok == A.run(G.diverging_three_cycle())
  end

  test "W1: cycle mediated through a total helper is not certified" do
    assert :ok == A.run(G.diverging_mediated_cycle())
  end

  test "W1: the total mediator itself still certifies (non-cyclic subroutine)" do
    c = G.diverging_mediated_cycle()
    env = G.env_of(c)

    assert Cure.Core.Certificate.terminating?(
             :total_id,
             Cure.Core.Env.get_def(env, :total_id).body,
             env
           )
  end

  test "W1: argument-permuting size-preserving pair is not certified" do
    assert :ok == A.run(G.diverging_permuting_pair())
  end

  test "W1: constructor-regrowing self-call is not certified" do
    assert :ok == A.run(G.diverging_regrowing_self())
  end

  test "W1: one-leg-decreasing mutual pair is not certified" do
    assert :ok == A.run(G.diverging_one_leg_pair())
  end
```

- [ ] **Step 2: Run to verify they fail**

Run: `mix test test/antigen/assays/totality_test.exs`
Expected: FAIL — `UndefinedFunctionError` for `diverging_three_cycle/0` etc.

- [ ] **Step 3: Implement the five generators**

Append to `lib/antigen/generators/totality.ex` (before `env_of/1`):

```elixir
  # -- W1: adversarial diverging set (pre-port banking spec §4 W1) ------------
  # Each is diverging BY CONSTRUCTION (argument in @doc). All are rejected by
  # today's conservative certifier (mutual cycles rejected wholesale; the
  # self-call variants fail the fixed-position structural guard) — and must
  # STAY rejected forever, including after the P1 size-change port.

  @doc """
  Diverging 3-cycle `f → g → h → f` over `Dec → Dec`. No body references its own
  name; only signature-level cycle detection sees it (generalizes the banked
  2-cycle). Diverges on every input: `f x → g x → h x → f x → …`. Label `:diverging`.
  """
  @spec diverging_three_cycle() :: Challenge.t()
  def diverging_three_cycle do
    ty = {:pi, @dec, @dec}
    bf = {:lam, @dec, {:app, {:global, :g}, {:var, 0}}}
    bg = {:lam, @dec, {:app, {:global, :h}, {:var, 0}}}
    bh = {:lam, @dec, {:app, {:global, :f}, {:var, 0}}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/diverging",
      label: :diverging,
      payload: %{
        defs: [
          %{name: :f, type: ty, body: bf},
          %{name: :g, type: ty, body: bg},
          %{name: :h, type: ty, body: bh}
        ],
        focus: [:f, :g, :h]
      },
      note: "W1 3-cycle f->g->h->f; every body self-call-free"
    )
  end

  @doc """
  Diverging cycle whose every direct callee looks innocent: `f = λx. total_id (g x)`,
  `g = λx. f x`, with `total_id = λx. x` genuinely total. The cycle f→g→f exists but
  is interleaved with a plain subroutine call. `total_id` is deliberately NOT in
  `focus` — it must keep certifying (asserted separately). Diverges on every input.
  Label `:diverging`.
  """
  @spec diverging_mediated_cycle() :: Challenge.t()
  def diverging_mediated_cycle do
    ty = {:pi, @dec, @dec}
    b_id = {:lam, @dec, {:var, 0}}
    bf = {:lam, @dec, {:app, {:global, :total_id}, {:app, {:global, :g}, {:var, 0}}}}
    bg = {:lam, @dec, {:app, {:global, :f}, {:var, 0}}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/diverging",
      label: :diverging,
      payload: %{
        defs: [
          %{name: :total_id, type: ty, body: b_id},
          %{name: :f, type: ty, body: bf},
          %{name: :g, type: ty, body: bg}
        ],
        focus: [:f, :g]
      },
      note: "W1 cycle f->g->f mediated by a total helper (total_id excluded from focus)"
    )
  end

  @doc """
  Argument-permuting, size-preserving mutual pair over `Dec → Dec → Dec`:
  `f x y = g y x`, `g x y = f x y`. Every argument-to-argument flow is `≤`, none
  is `<` — the classic size-change discriminator: a naive "some argument shrinks
  somewhere" analysis wrongly certifies it, LJB composition does not. Diverges on
  every input pair. Label `:diverging`.
  """
  @spec diverging_permuting_pair() :: Challenge.t()
  def diverging_permuting_pair do
    ty = {:pi, @dec, {:pi, @dec, @dec}}
    # inner frame: y = var 0, x = var 1
    bf = {:lam, @dec, {:lam, @dec, {:app, {:app, {:global, :g}, {:var, 0}}, {:var, 1}}}}
    bg = {:lam, @dec, {:lam, @dec, {:app, {:app, {:global, :f}, {:var, 1}}, {:var, 0}}}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/diverging",
      label: :diverging,
      payload: %{
        defs: [%{name: :f, type: ty, body: bf}, %{name: :g, type: ty, body: bg}],
        focus: [:f, :g]
      },
      note: "W1 permuting pair f x y = g y x; g x y = f x y — all flows ≤, none <"
    )
  end

  @doc """
  Constructor-regrowing self-call: `h = λn. case n of {Z -> Z; S y -> h (S y)}`
  over `Nat → Nat`. The self-call re-wraps the just-unpacked field, so descent is
  claimed by shape and refuted by size: `h (S m) → h (S m) → …` diverges on every
  `S`-input. Label `:diverging`.
  """
  @spec diverging_regrowing_self() :: Challenge.t()
  def diverging_regrowing_self do
    motive = {:lam, @nat, @nat}

    body =
      {:lam, @nat,
       {:case, {:var, 0}, motive,
        [
          {:Z, 0, {:ctor, :Z, []}},
          {:S, 1, {:app, {:global, :h}, {:ctor, :S, [{:var, 0}]}}}
        ]}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/diverging",
      label: :diverging,
      payload: %{defs: [%{name: :h, type: {:pi, @nat, @nat}, body: body}], focus: [:h]},
      note: "W1 regrowing self-call h (S y) — diverges on every S input"
    )
  end

  @doc """
  One-leg-decreasing mutual pair: `f = λn. case n of {Z -> Z; S y -> g y}` and
  `g = λn. f (S n)` over `Nat → Nat`. The f→g call strictly decreases; the g→f
  call regrows; the COMPOSED cycle is non-decreasing: `f (S m) → g m → f (S m) → …`.
  LJB's motivating case — certification must consider cycle composition, not
  individual calls. Label `:diverging`.
  """
  @spec diverging_one_leg_pair() :: Challenge.t()
  def diverging_one_leg_pair do
    motive = {:lam, @nat, @nat}

    bf =
      {:lam, @nat,
       {:case, {:var, 0}, motive,
        [{:Z, 0, {:ctor, :Z, []}}, {:S, 1, {:app, {:global, :g}, {:var, 0}}}]}}

    bg = {:lam, @nat, {:app, {:global, :f}, {:ctor, :S, [{:var, 0}]}}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/diverging",
      label: :diverging,
      payload: %{
        defs: [
          %{name: :f, type: {:pi, @nat, @nat}, body: bf},
          %{name: :g, type: {:pi, @nat, @nat}, body: bg}
        ],
        focus: [:f, :g]
      },
      note: "W1 one-leg pair: f decreases, g regrows; composed cycle non-decreasing"
    )
  end
```

- [ ] **Step 4: Add `:total_id` to the closed atom set**

In `lib/antigen/challenge.ex`, in `@known_atoms`, change the line
`    :f, :g, :h, :Dec, :Nat, :Z, :S, :Causal,`
to
`    :f, :g, :h, :total_id, :Dec, :Nat, :Z, :S, :Causal,`

- [ ] **Step 5: Run the tests**

Run: `mix test test/antigen/assays/totality_test.exs`
Expected: `8 tests, 0 failures`.

- [ ] **Step 6: Full suite and commit**

Run: `mix test` — expected PASS.

```bash
git add lib/antigen/generators/totality.ex lib/antigen/challenge.ex test/antigen/assays/totality_test.exs
git commit -m "test(antigen): W1 adversarial diverging set (LJB discriminators, pre-P1 net)" --author="Made In Heaven <madeinheaven@madeinheaven.com>"
```

---

### Task 3: bank the W1 antibodies in corpus.sexp

**Files:**
- Create: `test/antigen/totality_seed_test.exs`
- Modify (generated, then committed): `test/antigen/corpus.sexp`

**Interfaces:**
- Consumes: Task 2's five generator functions; `Antigen.Corpus.append/3`, `Antigen.Runner.replay/2`.
- Produces: five new committed records in `corpus.sexp` (assay `totality/diverging`). No API.

- [ ] **Step 1: Write the banking test**

Create `test/antigen/totality_seed_test.exs`:

```elixir
defmodule Antigen.TotalitySeedTest do
  @moduledoc """
  Banks the W1 adversarial diverging antibodies (pre-port banking spec §4 W1) and
  guards that every banked totality record replays through the kernel to `:ok`.
  Idempotent: on a fresh checkout the committed records are already present, so
  `Corpus.append/3` dedups and writes nothing (keeping `mix test` git-clean).
  These five must keep replaying `:ok` FOREVER — including after the P1
  size-change port makes the certifier more permissive; that transition is the
  only moment they can go red, and catching it is their entire purpose.
  """
  use ExUnit.Case, async: false
  alias Antigen.{Corpus, Runner, Assays}
  alias Antigen.Generators.Totality

  @corpus "test/antigen/corpus.sexp"

  @antibodies [
    Totality.diverging_three_cycle(),
    Totality.diverging_mediated_cycle(),
    Totality.diverging_permuting_pair(),
    Totality.diverging_regrowing_self(),
    Totality.diverging_one_leg_pair()
  ]

  test "W1 diverging antibodies are banked and every totality record replays :ok" do
    for a <- @antibodies, do: Corpus.append(@corpus, a, Corpus.dedup_key(a, :antibody))

    reg = %{"totality/diverging" => Assays.Totality, "totality/terminating" => Assays.Totality}
    results = Runner.replay([@corpus], reg)

    tot =
      Enum.filter(results, fn r ->
        match?(%Antigen.Challenge{assay: "totality/" <> _}, r.entry)
      end)

    # the pre-existing mutual-pair antibody + the five W1 records
    assert length(tot) >= 6

    assert Enum.all?(tot, &(&1.verdict == :ok)),
           "totality replay produced a non-:ok verdict: " <>
             inspect(tot |> Enum.reject(&(&1.verdict == :ok)) |> Enum.map(& &1.verdict))
  end
end
```

- [ ] **Step 2: Run it twice (bank, then prove idempotence)**

Run: `mix test test/antigen/totality_seed_test.exs` — expected PASS (first run appends 5 records).
Run again: `mix test test/antigen/totality_seed_test.exs && git diff --stat test/antigen/corpus.sexp`
Expected: PASS, and the diff shows the file changed once (5 added lines) and is now stable.

- [ ] **Step 3: Full suite** — `mix test`, expected PASS (in particular `corpus_replay_test.exs`'s three invariants over the grown corpus).

- [ ] **Step 4: Commit**

```bash
git add test/antigen/totality_seed_test.exs test/antigen/corpus.sexp
git commit -m "test(antigen): bank W1 adversarial diverging antibodies (5 records)" --author="Made In Heaven <madeinheaven@madeinheaven.com>"
```

---

### Task 4: W2 — reach-pin generators (well-founded, conservatively rejected today)

**Files:**
- Modify: `lib/antigen/generators/totality.ex` (three new functions)
- Modify: `lib/antigen/challenge.ex` (`@known_atoms`: add `:even, :odd, :ack`)
- Test: `test/antigen/assays/totality_test.exs` (three new tests)

**Interfaces:**
- Consumes: same as Task 2.
- Produces: `Antigen.Generators.Totality.wellfounded_even_odd/0`, `wellfounded_ackermann/0`, `wellfounded_permuted_pair/0` — `Challenge.t()` with `assay: "totality/terminating"`, `label: :terminating` (ground truth), whose `Assays.Totality.run/1` verdict TODAY is `{:violation, {:wrongly_rejected, focus}}`. Task 5 banks them in `reach.sexp`.

- [ ] **Step 1: Write the failing tests**

Append to `test/antigen/assays/totality_test.exs`:

```elixir
  # -- W2: reach pins (pre-port banking spec §4 W2, D2/D3) --------------------
  # Labels state mathematical truth (:terminating — each IS well-founded); the
  # assertions pin today's CONSERVATIVE REJECTION. P1 (size-change) flips these
  # to :ok by migrating the banked records from reach.sexp into corpus.sexp —
  # at which point these assertions are updated to assert :ok in the same commit.

  test "W2 reach pin: even/odd structural mutual pair is conservatively rejected today" do
    assert {:violation, {:wrongly_rejected, [:even, :odd]}} ==
             A.run(G.wellfounded_even_odd())
  end

  test "W2 reach pin: Ackermann (lexicographic two-argument descent) is conservatively rejected today" do
    assert {:violation, {:wrongly_rejected, [:ack]}} == A.run(G.wellfounded_ackermann())
  end

  test "W2 reach pin: permuted well-founded pair is conservatively rejected today" do
    assert {:violation, {:wrongly_rejected, [:f, :g]}} ==
             A.run(G.wellfounded_permuted_pair())
  end
```

- [ ] **Step 2: Run to verify they fail** — `mix test test/antigen/assays/totality_test.exs`, expected FAIL (`UndefinedFunctionError`).

- [ ] **Step 3: Implement the three generators**

Append to `lib/antigen/generators/totality.ex`:

```elixir
  # -- W2: reach pins (pre-port banking spec §4 W2) ----------------------------
  # Ground-truth :terminating (argument in each @doc), conservatively rejected by
  # today's certifier (mutual groups rejected wholesale; multi-argument descent
  # fails the fixed-position guard). Banked in test/antigen/reach.sexp, NOT
  # corpus.sexp; P1 migrates them. Labels are truth, not checker behavior (D3).

  @doc """
  Well-founded structural mutual pair: `even = λn. case n of {Z -> Z; S y -> odd y}`,
  `odd = λn. case n of {Z -> S Z; S y -> even y}` over `Nat → Nat` (Nat-valued to
  stay in one family). Every cross-call passes the strict predecessor, so the
  composed cycle strictly decreases: total. Label `:terminating` — rejected today
  only because the certifier rejects all mutual cycles.
  """
  @spec wellfounded_even_odd() :: Challenge.t()
  def wellfounded_even_odd do
    motive = {:lam, @nat, @nat}

    be =
      {:lam, @nat,
       {:case, {:var, 0}, motive,
        [{:Z, 0, {:ctor, :Z, []}}, {:S, 1, {:app, {:global, :odd}, {:var, 0}}}]}}

    bo =
      {:lam, @nat,
       {:case, {:var, 0}, motive,
        [
          {:Z, 0, {:ctor, :S, [{:ctor, :Z, []}]}},
          {:S, 1, {:app, {:global, :even}, {:var, 0}}}
        ]}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/terminating",
      label: :terminating,
      payload: %{
        defs: [
          %{name: :even, type: {:pi, @nat, @nat}, body: be},
          %{name: :odd, type: {:pi, @nat, @nat}, body: bo}
        ],
        focus: [:even, :odd]
      },
      note: "W2 reach pin: well-founded mutual even/odd (P1 target)"
    )
  end

  @doc """
  Ackermann over `Nat → Nat → Nat`:
  `ack Z n = S n; ack (S m') Z = ack m' (S Z); ack (S m') (S n') = ack m' (ack (S m') n')`.
  Total by the lexicographic measure (m, n): every call either decreases m, or
  keeps m and decreases n. Rejected today: no SINGLE fixed argument position
  decreases at every self-call (the inner call's first argument is `S m'`, a
  constructor, not a bound variable). Label `:terminating`.
  """
  @spec wellfounded_ackermann() :: Challenge.t()
  def wellfounded_ackermann do
    motive = {:lam, @nat, @nat}

    # frame under λm. λn.: m = var 1, n = var 0
    body =
      {:lam, @nat,
       {:lam, @nat,
        {:case, {:var, 1}, motive,
         [
           # Z: S n
           {:Z, 0, {:ctor, :S, [{:var, 0}]}},
           # S m' (binds m' at 0; n shifts to 1, m to 2)
           {:S, 1,
            {:case, {:var, 1}, motive,
             [
               # n = Z: ack m' (S Z)
               {:Z, 0,
                {:app, {:app, {:global, :ack}, {:var, 0}}, {:ctor, :S, [{:ctor, :Z, []}]}}},
               # n = S n' (binds n' at 0; m' shifts to 1): ack m' (ack (S m') n')
               {:S, 1,
                {:app, {:app, {:global, :ack}, {:var, 1}},
                 {:app, {:app, {:global, :ack}, {:ctor, :S, [{:var, 1}]}}, {:var, 0}}}}
             ]}}
         ]}}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/terminating",
      label: :terminating,
      payload: %{
        defs: [%{name: :ack, type: {:pi, @nat, {:pi, @nat, @nat}}, body: body}],
        focus: [:ack]
      },
      note: "W2 reach pin: Ackermann, lexicographic (m, n) descent (P1 target)"
    )
  end

  @doc """
  Permuted well-founded pair over `Nat`: `f = λn. λm. case n of {Z -> m; S y -> g m y}`
  and `g = λa. λb. f b a`. Descent is visible only by tracking arguments across the
  swap: `f (S y) m → g m y → f y m` — f's first argument strictly decreases every
  round trip. Total; rejected today as a mutual cycle. The accept-side twin of W1's
  `diverging_permuting_pair`. Label `:terminating`.
  """
  @spec wellfounded_permuted_pair() :: Challenge.t()
  def wellfounded_permuted_pair do
    motive = {:lam, @nat, @nat}

    # f frame: n = var 1, m = var 0; S-branch binds y at 0 (m -> 1, n -> 2)
    bf =
      {:lam, @nat,
       {:lam, @nat,
        {:case, {:var, 1}, motive,
         [
           {:Z, 0, {:var, 0}},
           {:S, 1, {:app, {:app, {:global, :g}, {:var, 1}}, {:var, 0}}}
         ]}}}

    # g a b = f b a; frame: a = var 1, b = var 0
    bg = {:lam, @nat, {:lam, @nat, {:app, {:app, {:global, :f}, {:var, 0}}, {:var, 1}}}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/terminating",
      label: :terminating,
      payload: %{
        defs: [
          %{name: :f, type: {:pi, @nat, {:pi, @nat, @nat}}, body: bf},
          %{name: :g, type: {:pi, @nat, {:pi, @nat, @nat}}, body: bg}
        ],
        focus: [:f, :g]
      },
      note: "W2 reach pin: descent visible only across the argument swap (P1 target)"
    )
  end
```

- [ ] **Step 4: Add `:even, :odd, :ack` to `@known_atoms`**

In `lib/antigen/challenge.ex`, change the (Task-2-updated) line
`    :f, :g, :h, :total_id, :Dec, :Nat, :Z, :S, :Causal,`
to
`    :f, :g, :h, :total_id, :even, :odd, :ack, :Dec, :Nat, :Z, :S, :Causal,`

- [ ] **Step 5: Run** — `mix test test/antigen/assays/totality_test.exs`, expected `11 tests, 0 failures`.

- [ ] **Step 6: Full suite and commit**

```bash
mix test
git add lib/antigen/generators/totality.ex lib/antigen/challenge.ex test/antigen/assays/totality_test.exs
git commit -m "test(antigen): W2 reach-pin generators (well-founded mutual/lex/permuted, P1 targets)" --author="Made In Heaven <madeinheaven@madeinheaven.com>"
```

---

### Task 5: the reach store — `reach.sexp` + pinned replay

**Files:**
- Create: `test/antigen/reach_pin_test.exs`
- Create (generated, then committed): `test/antigen/reach.sexp`

**Interfaces:**
- Consumes: Task 4's three generators; `Corpus.append/3`, `Corpus.stream/1`, `Assays.Totality.run/1`.
- Produces: the third store `test/antigen/reach.sexp` (3 records) + the migration contract P1 executes. No API.

- [ ] **Step 1: Write the reach replay test**

Create `test/antigen/reach_pin_test.exs`:

```elixir
defmodule Antigen.ReachPinTest do
  @moduledoc """
  Banks + replays `test/antigen/reach.sexp` (pre-port banking spec D2): challenges
  whose ground-truth label the checker does not yet achieve. Each entry's replay
  is pinned to its DOCUMENTED current violation, so drift in EITHER direction is
  loud: an accidental acceptance (permissiveness appearing without P1) and an
  accidental new rejection shape both fail this test.

  MIGRATION CONTRACT (spec D2): the port run that achieves an entry (P1 for all
  initial entries) appends the byte-identical record line to corpus.sexp, removes
  it here, and deletes the matching pin below — in the same commit. Records are
  never edited in place.
  """
  use ExUnit.Case, async: false
  alias Antigen.{Corpus, Assays}
  alias Antigen.Generators.Totality

  @reach "test/antigen/reach.sexp"

  @pins [
    Totality.wellfounded_even_odd(),
    Totality.wellfounded_ackermann(),
    Totality.wellfounded_permuted_pair()
  ]

  # keyed by focus — the pinned CURRENT verdict for each banked entry
  @expected %{
    [:even, :odd] => {:violation, {:wrongly_rejected, [:even, :odd]}},
    [:ack] => {:violation, {:wrongly_rejected, [:ack]}},
    [:f, :g] => {:violation, {:wrongly_rejected, [:f, :g]}}
  }

  test "reach pins are banked and replay to their documented conservative rejection" do
    for c <- @pins, do: Corpus.append(@reach, c, Corpus.dedup_key(c, :antibody))

    decoded = @reach |> Corpus.stream() |> Enum.map(fn {:ok, c} -> c end)
    assert length(decoded) == map_size(@expected)

    for c <- decoded do
      assert Assays.Totality.run(c) == Map.fetch!(@expected, c.payload.focus),
             "reach pin #{inspect(c.payload.focus)} drifted from its pinned verdict"
    end
  end
end
```

- [ ] **Step 2: Run twice** — `mix test test/antigen/reach_pin_test.exs` twice; expected PASS both times, `test/antigen/reach.sexp` created with 3 lines on the first run, unchanged on the second.

- [ ] **Step 3: Full suite** — `mix test`, expected PASS. (`corpus_replay_test.exs` reads only `corpus.sexp`/`seeds.sexp`, so the reach store — whose entries deliberately do NOT replay `:ok` — does not trip its invariant test.)

- [ ] **Step 4: Commit**

```bash
git add test/antigen/reach_pin_test.exs test/antigen/reach.sexp
git commit -m "test(antigen): reach.sexp store + pinned replay for P1 reach targets (W2)" --author="Made In Heaven <madeinheaven@madeinheaven.com>"
```

---

### Task 6: W3 — deletion-rule antibody + occurs-check pin

**Files:**
- Modify: `lib/antigen/generators/indexed.ex` (`ixn_family/0` + `deletion/1`)
- Modify: `lib/antigen/challenge.ex` (`@known_atoms`: add `:IxN, :wrapn, :delete, :i`)
- Modify: `test/antigen/assays/indexed_test.exs` (two tests)
- Modify: `test/antigen/indexed_seed_test.exs` (extend `@antibodies` / `@seed_candidates`)
- Create: `test/cure/core/branch_unify_occurs_test.exs`
- Modify (generated): `test/antigen/corpus.sexp`, `test/antigen/seeds.sexp`
- Modify (conditional — only if Step 5's D4 reroute fires): `test/antigen/reach_pin_test.exs`, `test/antigen/reach.sexp`

**Interfaces:**
- Consumes: `Antigen.Generators.Indexed.challenge/6` (existing private helper), `Cure.Core.Kernel.branch_unify/4` (public), `Cure.Core.{Context, Env, Inductive, Eval}`.
- Produces: `Antigen.Generators.Indexed.deletion(:well_typed | :ill_typed) :: Challenge.t()` (assay `"indexed/case"`, def_name `:delete`).

**Background for the implementer:** the kernel's case-index unifier (`lib/cure/core/kernel.ex:749-847`) has a *deletion* rule — `unify_one(r, s, _arity, subst) when r == s → {:ok, subst}` (syntactically equal index pair is consistent, no refinement) — and an *occurs check* — `bind_index` degrades a cyclic solve to `:undecided` (`kernel.ex:810`). Constructor-headed equal pairs are consumed by the injectivity clause first, so the deletion rule is exercised by index terms that are equal but NOT constructor/data-headed: integer literals. Roadmap A2/#23 wants a *named* antibody for each rule.

**Divergence from spec W3's literal framing, and why:** §4 W3 describes both antibodies as `:indexed_case` challenges "named in the assay tests." The occurs-check antibody below instead goes directly through the public `Kernel.branch_unify/4` in a standalone kernel-level test (Step 6), not through `Antigen.Generators.Indexed`/`Assays.Indexed`. Reason: the occurs check guards an out-of-telescope index reference — a signature shape `Inductive.declare/3` does not itself validate (confirmed: `declare/3` is a plain metadata insertion, `lib/cure/core/inductive.ex:132-143`), but one that a challenge built and typechecked through the normal Antigen apparatus would never organically produce (well-formed elaborator output always closes result indices over their own telescope). Reaching the kernel's defensive branch therefore requires constructing the adversarial signature directly, bypassing the challenge layer. The antibody still runs on every `mix test` and is a permanent regression guard; it is just not corpus-banked or assay-dispatched. Task 11 records it as an "occurs pin," distinct from the deletion "antibody," to keep this distinction visible in the ledger.

- [ ] **Step 1: Write the failing assay tests**

Append to `test/antigen/assays/indexed_test.exs`:

```elixir
  # -- W3: deletion rule (pre-port banking spec §4 W3; roadmap A2/#23) --------
  test "W3 deletion: equal literal indices are consistent — branch reachable, well-typed body accepted" do
    assert :ok == A.run(G.deletion(:well_typed))
  end

  test "W3 deletion: equal literal indices never discharge the branch — ill-typed body rejected" do
    assert :ok == A.run(G.deletion(:ill_typed))
  end
```

(Match the file's existing alias names: it aliases `Antigen.Assays.Indexed, as: A` and `Antigen.Generators.Indexed, as: G`; if it uses different aliases, follow the file.)

- [ ] **Step 2: Run to verify failure** — `mix test test/antigen/assays/indexed_test.exs`, expected FAIL (`deletion/1` undefined).

- [ ] **Step 3: Implement `deletion/1`**

Append to `lib/antigen/generators/indexed.ex` (before the private `challenge/6`):

```elixir
  # -- W3: deletion rule (pre-port banking spec §4 W3) -------------------------
  # IxN is indexed by a raw integer; wrapn's GROUND result index is the literal 3.
  # A scrutinee at `IxN 3` yields the index equation `3 ~ 3`, which no other
  # unifier clause consumes (not a var, not ctor/data-headed) — it is discharged
  # by the DELETION rule (r == s ⇒ consistent, kernel.ex `unify_one`). The branch
  # is therefore REACHABLE with no refinement.
  defp ixn_family,
    do:
      {Inductive.family(:IxN, [], [{:i, {:int_type}}], 0),
       [Inductive.ctor(:wrapn, [{:p, @dec}], [{:int_lit, 3}])]}

  @doc """
  Deletion-rule obligation. `:well_typed`: the reachable-via-deletion branch has a
  well-typed body and must be ACCEPTED — the antibody against deletion degrading
  to `:impossible` (which would discharge a live branch and, on the ill side,
  wrongly accept). `:ill_typed`: the same reachable branch with an ill-typed body
  (`{:type,0}` where `Dec` is expected) must be REJECTED — deletion must never
  skip the body check.
  """
  @spec deletion(:well_typed | :ill_typed) :: Challenge.t()
  def deletion(label) do
    ixn3 = {:data, :IxN, [], [{:int_lit, 3}]}
    motive = {:lam, {:int_type}, {:lam, {:data, :IxN, [], [{:var, 0}]}, @dec}}
    def_type = {:pi, ixn3, @dec}

    branch_body =
      case label do
        :well_typed -> {:ctor, :Dcoupled, []}
        :ill_typed -> {:type, 0}
      end

    body = {:lam, ixn3, {:case, {:var, 0}, motive, [{:wrapn, 1, branch_body}]}}

    challenge(label, [dec_family(), ixn_family()], :delete, def_type, body,
      "deletion rule: index equation 3 ~ 3 is consistent (r==s); branch reachable, body #{label}")
  end
```

- [ ] **Step 4: Add `:IxN, :wrapn, :delete, :i` to `@known_atoms`**

In `lib/antigen/challenge.ex`, change
`    :Wr, :MkWr, :IW, :iw, :w,`
to
`    :Wr, :MkWr, :IW, :iw, :w, :IxN, :wrapn, :delete, :i,`

- [ ] **Step 5: Run the assay tests** — `mix test test/antigen/assays/indexed_test.exs`, expected PASS. If `deletion(:well_typed)` fails with `{:wrongly_rejected, …}`, inspect the reason: this is D4's *incompleteness surprise* (kernel wrongly rejects a must-accept-today challenge), likely in how the kernel evaluates/reifies literal index values. Apply the D4 symmetric reroute (Global Constraints): keep the `:well_typed` label, change this test to pin the exact current violation, bank the entry in `reach.sexp` instead of `seeds.sexp` in Step 8, record the surprise in the run report, and have Task 11 leave A2/#23 open rather than ✅. Do NOT relabel, do NOT stop the task.

  Extending `test/antigen/reach_pin_test.exs` for this entry is not a one-line addition: that file (Task 5) hardcodes a single assay dispatch (`Assays.Totality.run(c)`) and keys `@expected` by `c.payload.focus`, and `indexed/case` challenges have neither. Generalize it: replace the hardcoded call with a per-entry dispatch keyed by `c.assay` (a small registry, e.g. `%{"totality/terminating" => Assays.Totality, "indexed/case" => Assays.Indexed}`, mirroring `corpus_replay_test.exs`'s `@registry`), and replace the `focus`-keyed `@expected` map with a shape-agnostic key such as `c.note` (every entry's note is already a unique, human-legible identifier) so both `focus`-bearing and `def_name`-bearing entries key uniformly.

  Symmetrically: if `deletion(:ill_typed)` instead fails by wrongly ACCEPTING (the deletion rule discharges the branch without checking its ill-typed body), that is a soundness hole, not an incompleteness surprise — apply D4's default rule (spec D4, first sentence): stop, do not bank, report it, and fix it red-green in the kernel (mirror Task 7/8's audit-then-fix pattern and its `TCB:` commit-body line) before proceeding to Step 6.

- [ ] **Step 6: Write the occurs-check pin (kernel-level named antibody)**

Create `test/cure/core/branch_unify_occurs_test.exs`:

```elixir
defmodule Cure.Core.BranchUnifyOccursTest do
  @moduledoc """
  Named occurs-check/cycle antibody (pre-port banking spec §4 W3; roadmap A2/#23).

  In well-formed signatures a ctor's result indices are closed over its own
  telescope (vars < arity), so a cyclic solve cannot arise from elaborator
  output — the kernel's occurs check (`bind_index` → `:undecided`) is a
  DEFENSIVE rule against adversarial signatures, reachable through the public
  `Kernel.branch_unify/4`. This test constructs exactly that adversary: a ctor
  whose result index references a variable OUTSIDE its telescope, producing the
  equation `MkWr(x) ~ x` whose only solve is the cyclic `x := MkWr(x)`. Pinned
  behavior: the kernel neither loops nor fabricates the solve — the equation
  degrades and the verdict is `:trivial` (no refinement), never `{:solved, _}`.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Context, Env, Eval, Inductive, Kernel}

  @dec {:data, :Dec, [], []}
  @wr {:data, :Wr, [], []}

  test "a cyclic index equation degrades (occurs check): :trivial, never a solve, never a loop" do
    env =
      Env.empty()
      |> Inductive.declare(Inductive.family(:Dec, [], [], 0), [
        Inductive.ctor(:Dcoupled, [], []),
        Inductive.ctor(:Causal, [], [])
      ])
      |> Inductive.declare(Inductive.family(:Wr, [], [], 0), [
        Inductive.ctor(:MkWr, [{:d, @dec}], [])
      ])
      # adversarial: result index {:ctor, :MkWr, [{:var, 1}]} references var 1,
      # OUTSIDE the 1-slot telescope (arity 1 ⇒ own vars are < 1)
      |> Inductive.declare(Inductive.family(:IW, [], [{:w, @wr}], 0), [
        Inductive.ctor(:iw, [{:p, @dec}], [{:ctor, :MkWr, [{:var, 1}]}])
      ])

    ctx = Context.empty(env) |> Context.extend(Eval.eval(@wr, []))
    # scrutinee index value: the neutral outer variable x itself
    scrut_index = {:vneutral, {:nvar, 0}}

    assert :trivial = Kernel.branch_unify(ctx, :IW, :iw, [scrut_index])
  end
end
```

- [ ] **Step 7: Run it** — `mix test test/cure/core/branch_unify_occurs_test.exs`, expected PASS (the occurs check exists; this pins it). If it FAILS by returning `{:solved, _}` or hanging: that is a discovered kernel defect — apply D4 (stop, report, red-green fix in `bind_index`), and note the TCB diff in the commit.

If the neutral-value shape `{:vneutral, {:nvar, 0}}` fails to decode/reify (a `FunctionClauseError` from `Quote.reify/2`), check `Cure.Core.Context.env/1` (`lib/cure/core/context.ex:53-56`) for the canonical neutral constructor shape and use exactly that.

- [ ] **Step 8: Bank the deletion pair**

In `test/antigen/indexed_seed_test.exs`, extend `@antibodies` with `Indexed.deletion(:ill_typed)` and `@seed_candidates` with `Indexed.deletion(:well_typed)`:

```elixir
  @antibodies [
    Indexed.branch_family(:ill_typed),
    Indexed.discharge(:ill_typed),
    Indexed.injectivity(:ill_typed),
    Indexed.deletion(:ill_typed)
  ]
```
and add `Indexed.deletion(:well_typed)` as the last entry of `@seed_candidates`.

Run: `mix test test/antigen/indexed_seed_test.exs` (twice — bank, then idempotence). Expected PASS; `corpus.sexp` +1 line, `seeds.sexp` +1 line.

- [ ] **Step 9: Full suite and commit**

```bash
mix test
git add lib/antigen/generators/indexed.ex lib/antigen/challenge.ex \
  test/antigen/assays/indexed_test.exs test/antigen/indexed_seed_test.exs \
  test/cure/core/branch_unify_occurs_test.exs test/antigen/corpus.sexp test/antigen/seeds.sexp
git commit -m "test(antigen): named deletion-rule antibody + kernel occurs-check pin (W3, closes #23)" --author="Made In Heaven <madeinheaven@madeinheaven.com>"
```

If Step 5's D4 reroute fired, also `git add test/antigen/reach_pin_test.exs test/antigen/reach.sexp` into this same commit (or a follow-up commit before moving on) — the reroute is not a separable, deferrable change.

---

### Task 7: W4 — positivity escape-hatch generators + audit (expect red)

**Files:**
- Modify: `lib/antigen/generators/positivity.ex` (three new functions + `@decd`)
- Modify: `lib/antigen/assays/positivity.ex` (one new `run/1` clause for multi-family challenges)
- Modify: `lib/antigen/challenge.ex` (`@known_atoms`: add `:b`)
- Test: `test/antigen/assays/positivity_test.exs` (three tests)

**Interfaces:**
- Consumes: `Antigen.Challenge.new/1`; the `:indexed_case` record shape (multi-family serialization) from `lib/antigen/challenge.ex:105-119`; `Antigen.Generators.Indexed.env_of/1`; `Cure.Core.Inductive.positive?/2`.
- Produces: `Antigen.Generators.Positivity.double_negation_family/0`, `sigma_negative_family/0` (kind `:family`), `through_constructor_negative/0` (kind `:indexed_case`, assay `"positivity"`, **subject family = last of `families`** — a convention the new assay clause encodes). Task 8 consumes the red tests; Task 9 banks all three.

**Audit prediction (verify, don't assume):** `Cure.Core.Inductive.strictly_positive?/2` (`lib/cure/core/inductive.ex:254-257`) checks arrow domains with a *shallow* `occurs?` that never expands other families' constructors, and has NO `:sigma` clause (falls to the `true` catch-all). Expect: `double_negation` correctly rejected (green); `through_constructor` and `sigma_negative` wrongly ACCEPTED (red) — two live positivity holes. D4 applies: Task 8 fixes; do not relabel.

- [ ] **Step 1: Write the audit tests (these are the red tests of the red-green cycle)**

Append to `test/antigen/assays/positivity_test.exs` (follow the file's existing aliases; it tests `Antigen.Assays.Positivity` with `Antigen.Generators.Positivity`):

```elixir
  # -- W4: classic positivity escape hatches (pre-port banking spec §4 W4) ----
  # All three are :negative by construction; :ok means the kernel rejected them.
  # AUDIT (D4): if a test fails with {:wrongly_accepted, :Bad}, that is a LIVE
  # positivity hole — fixed red-green in the kernel by the next task, then these
  # become its permanent regression guards.

  test "W4: double negation ((Bad -> Dec) -> Dec) is rejected" do
    assert :ok == Antigen.Assays.Positivity.run(
             Antigen.Generators.Positivity.double_negation_family()
           )
  end

  test "W4: negative occurrence hidden under a sigma is rejected" do
    assert :ok == Antigen.Assays.Positivity.run(
             Antigen.Generators.Positivity.sigma_negative_family()
           )
  end

  test "W4: through-constructor negative occurrence (Bad -> via Box) is rejected" do
    assert :ok == Antigen.Assays.Positivity.run(
             Antigen.Generators.Positivity.through_constructor_negative()
           )
  end
```

- [ ] **Step 2: Implement the generators**

In `lib/antigen/generators/positivity.ex`, add under the existing module attributes:

```elixir
  @decd {:data, :Dec, [], []}
```

and append the three builders:

```elixir
  # -- W4: classic escape hatches (pre-port banking spec §4 W4) ----------------

  @doc """
  Double negation: `MkBad : ((Bad -> Dec) -> Dec) -> Bad`. `Bad` sits two arrow-
  domains deep — positive by naive polarity-flip counting, NEGATIVE for strict
  positivity (any occurrence in an arrow domain is banned). Genuinely unsound to
  admit (Curry-paradox family). Label `:negative`.
  """
  @spec double_negation_family() :: Challenge.t()
  def double_negation_family do
    fam = Inductive.family(:Bad, [], [], 0)
    field = {:pi, {:pi, @bad, @decd}, @decd}
    ctors = [Inductive.ctor(:MkBad, [{:f, field}], [])]

    Challenge.new(
      kind: :family,
      assay: "positivity",
      label: :negative,
      payload: %{family: fam, ctors: ctors},
      note: "W4 double negation: Bad in an arrow domain (two deep) — strict positivity rejects"
    )
  end

  @doc """
  Negative occurrence hidden under a Σ: `MkBad : (Σ (Bad -> Dec). Dec) -> Bad`.
  The arrow-left occurrence of `Bad` sits inside a sigma component. Strict
  positivity must traverse Σ (covariant in both components) and reject. Label
  `:negative`.
  """
  @spec sigma_negative_family() :: Challenge.t()
  def sigma_negative_family do
    fam = Inductive.family(:Bad, [], [], 0)
    field = {:sigma, {:pi, @bad, @decd}, @decd}
    ctors = [Inductive.ctor(:MkBad, [{:f, field}], [])]

    Challenge.new(
      kind: :family,
      assay: "positivity",
      label: :negative,
      payload: %{family: fam, ctors: ctors},
      note: "W4 sigma-hidden negative: Bad left of an arrow inside a Σ component"
    )
  end

  @doc """
  Through-constructor escape: `Box` has `mk : (Bad -> Dec) -> Box`, and
  `Bad` has `MkBad : Box -> Bad` — so `Bad ≅ (Bad -> Dec)` one type layer down.
  Rejecting requires expanding `Box`'s constructor fields during `Bad`'s
  positivity check. Multi-family, so it uses the `:indexed_case` record shape
  (subject family LAST; the def slot is an inert well-typed placeholder — the
  positivity assay ignores it). Label `:negative`.
  """
  @spec through_constructor_negative() :: Challenge.t()
  def through_constructor_negative do
    box = {Inductive.family(:Box, [], [], 0),
           [Inductive.ctor(:mk, [{:f, {:pi, @bad, @decd}}], [])]}

    bad = {Inductive.family(:Bad, [], [], 0),
           [Inductive.ctor(:MkBad, [{:b, {:data, :Box, [], []}}], [])]}

    dec = {Inductive.family(:Dec, [], [], 0),
           [Inductive.ctor(:Dcoupled, [], []), Inductive.ctor(:Causal, [], [])]}

    Challenge.new(
      kind: :indexed_case,
      assay: "positivity",
      label: :negative,
      payload: %{
        families: [dec, box, bad],
        def_name: :probe,
        def_type: {:type, 0},
        def_body: {:data, :Dec, [], []}
      },
      note: "W4 through-constructor: Bad -> Dec hidden inside Box's ctor; subject = Bad (last family)"
    )
  end
```

- [ ] **Step 3: Add the multi-family clause to the positivity assay**

In `lib/antigen/assays/positivity.ex`, add a second `run/1` clause after the existing one:

```elixir
  # Multi-family positivity challenge (W4 through-constructor shape): reuses the
  # :indexed_case record shape; the SUBJECT family is by convention the LAST
  # entry of payload.families. The def slot is an inert placeholder.
  def run(%Challenge{kind: :indexed_case, assay: "positivity", label: label, payload: %{families: families}} = c) do
    env = Generators.Indexed.env_of(c)
    {%{name: subject}, _ctors} = List.last(families)
    verdict = Inductive.positive?(env, Inductive.get_family(env, subject))

    case {label, verdict} do
      {:positive, :ok} -> :ok
      {:negative, {:error, _}} -> :ok
      {:positive, {:error, reason}} -> {:violation, {:wrongly_rejected, reason}}
      {:negative, :ok} -> {:violation, {:wrongly_accepted, subject}}
    end
  end
```

(`alias Antigen.Generators` is already in the file's alias list as `Generators`; keep it.)

- [ ] **Step 4: Add `:b` to `@known_atoms`**

In `lib/antigen/challenge.ex`, change
`    :Natp, :Zp, :Sp, :pred, :Bad, :MkBad, :present, :erased,`
to
`    :Natp, :Zp, :Sp, :pred, :Bad, :MkBad, :b, :present, :erased,`
(`:Box`, `:mk`, `:probe`, `:f`, `:Dec` are already interned.)

- [ ] **Step 5: Run the audit and RECORD the result**

Run: `mix test test/antigen/assays/positivity_test.exs`

Expected per the audit prediction: `double negation` PASSES; `sigma` and `through-constructor` FAIL with `{:violation, {:wrongly_accepted, :Bad}}`. Record exactly which failed in the working notes for Task 8 (and ultimately the run report — a confirmed live kernel hole is a headline finding). If ALL THREE pass, the audit prediction was wrong in the good direction: skip Task 8, go to Task 9, and note it.

**Do not commit yet** — the red tests and the fix travel together (Task 8).

---

### Task 8: W4 — kernel fix: deep strict positivity (TCB change)

**Files:**
- Modify: `lib/cure/core/inductive.ex:231-257` (the strict-positivity section)
- (carries Task 7's uncommitted files into its commit)

**Interfaces:**
- Consumes: Task 7's red tests; `ctors_of/2`, `occurs?/2` (existing privates in the same module).
- Produces: `Inductive.positive?/2` — same public signature and return type (`:ok | {:error, {:non_strictly_positive, ctor_name}}`), now traversing Σ and expanding other families' constructors. Everything downstream (declarations, Antigen positivity assay) is signature-compatible.

- [ ] **Step 1: Replace the positivity walk**

In `lib/cure/core/inductive.ex`, replace `positive?/2` and the two `strictly_positive?/2` clauses (lines 240-257) with:

```elixir
  @spec positive?(Env.t(), family()) :: :ok | {:error, {:non_strictly_positive, atom()}}
  def positive?(env, %{name: fname}) do
    Enum.reduce_while(ctors_of(env, fname), :ok, fn %{name: cname, args: args}, :ok ->
      if Enum.all?(args, fn {_n, ty} -> strictly_positive?(env, fname, ty, MapSet.new()) end) do
        {:cont, :ok}
      else
        {:halt, {:error, {:non_strictly_positive, cname}}}
      end
    end)
  end

  # A field type is strictly positive in `fname` when, at every function arrow,
  # `fname` does not occur in the domain — not even hidden behind another
  # declared family's constructor fields (the through-constructor rule) — and
  # the codomain stays strictly positive. Σ is covariant in both components. A
  # field headed by ANOTHER family is checked by expanding that family's
  # constructor fields (`seen` breaks family cycles); `fname` occurring in
  # another family's parameters/indices is conservatively rejected.
  defp strictly_positive?(env, fname, {:pi, dom, cod}, seen),
    do: not occurs_deep?(env, fname, dom, seen) and strictly_positive?(env, fname, cod, seen)

  defp strictly_positive?(env, fname, {:sigma, a, b}, seen),
    do: strictly_positive?(env, fname, a, seen) and strictly_positive?(env, fname, b, seen)

  defp strictly_positive?(_env, fname, {:data, fname, _ps, _is}, _seen), do: true

  defp strictly_positive?(env, fname, {:data, other, ps, is}, seen) do
    cond do
      Enum.any?(ps ++ is, &occurs?(fname, &1)) ->
        false

      MapSet.member?(seen, other) ->
        true

      true ->
        seen2 = MapSet.put(seen, other)

        env
        |> ctors_of(other)
        |> Enum.all?(fn %{args: args} ->
          Enum.all?(args, fn {_n, ty} -> strictly_positive?(env, fname, ty, seen2) end)
        end)
    end
  end

  defp strictly_positive?(_env, _fname, _other, _seen), do: true

  # Does `fname` occur anywhere in `ty`, including inside the constructor fields
  # of other families referenced by `ty`? Used for arrow DOMAINS, where any
  # reachable occurrence is a negative position.
  defp occurs_deep?(env, fname, ty, seen) do
    occurs?(fname, ty) or
      Enum.any?(data_heads(ty), fn other ->
        other != fname and not MapSet.member?(seen, other) and
          env
          |> ctors_of(other)
          |> Enum.any?(fn %{args: args} ->
            Enum.any?(args, fn {_n, t} ->
              occurs_deep?(env, fname, t, MapSet.put(seen, other))
            end)
          end)
      end)
  end

  # Every family name appearing as a `{:data, …}` head anywhere in the term.
  defp data_heads(term), do: term |> gather_data_heads(MapSet.new()) |> MapSet.to_list()

  defp gather_data_heads({:data, n, ps, is}, acc),
    do: Enum.reduce(ps ++ is, MapSet.put(acc, n), &gather_data_heads/2)

  defp gather_data_heads(t, acc) when is_tuple(t),
    do: t |> Tuple.to_list() |> Enum.reduce(acc, &gather_data_heads/2)

  defp gather_data_heads(l, acc) when is_list(l), do: Enum.reduce(l, acc, &gather_data_heads/2)
  defp gather_data_heads(_t, acc), do: acc
```

- [ ] **Step 2: Run the W4 tests** — `mix test test/antigen/assays/positivity_test.exs`, expected: all PASS (including the previously-red sigma/through-constructor tests).

- [ ] **Step 3: Run the FULL suite** — `mix test`.

Expected: PASS. This is the over-rejection guard: existing families (Natp/Sp, Vector, every stdlib family, the ④ surface tests) must all still declare. If any existing test fails with `{:non_strictly_positive, _}`, the fix over-rejects — diagnose which clause fired (likely the params/indices conservative rejection) and report before weakening anything; do NOT ship an over-rejecting kernel silently.

- [ ] **Step 4: Commit (Task 7 + Task 8 together — red tests + fix)**

```bash
git add lib/cure/core/inductive.ex lib/antigen/generators/positivity.ex \
  lib/antigen/assays/positivity.ex lib/antigen/challenge.ex test/antigen/assays/positivity_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "fix(core): deep strict positivity — expand through ctors, traverse sigma (W4/#19)" -m "Audit (D4) confirmed the through-constructor and sigma-hidden escapes were live:
Inductive.positive? accepted both. Red antibodies first, then the fix; the three
W4 challenges are now its permanent regression guards.

TCB: lib/cure/core/inductive.ex strict-positivity walk extended (env-aware,
visited-set family expansion, sigma traversal). No signature changes."
```

(If Task 7's audit found NO holes, commit generators+tests only, message `test(antigen): W4 positivity escape-hatch antibodies (audit: kernel already rejects)`.)

---

### Task 9: W4 — bank the positivity antibodies

**Files:**
- Create: `test/antigen/positivity_seed_test.exs`
- Modify (generated): `test/antigen/corpus.sexp`
- Modify: `docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md` (§3.1 positivity row)

**Interfaces:**
- Consumes: Task 7's three generators (now green through the Task 8 kernel).
- Produces: three committed corpus records (assay `"positivity"`).

- [ ] **Step 1: Write the banking test**

Create `test/antigen/positivity_seed_test.exs`:

```elixir
defmodule Antigen.PositivitySeedTest do
  @moduledoc """
  Banks the W4 positivity escape-hatch antibodies (pre-port banking spec §4 W4)
  and guards that every banked positivity record replays to `:ok`. Idempotent
  via Corpus.append dedup. These three guard the deep-positivity kernel walk:
  if it ever regresses to the shallow pre-fix walk, through-constructor and
  sigma replay to {:wrongly_accepted, :Bad} and this goes red.
  """
  use ExUnit.Case, async: false
  alias Antigen.{Corpus, Runner, Assays}
  alias Antigen.Generators.Positivity

  @corpus "test/antigen/corpus.sexp"

  @antibodies [
    Positivity.double_negation_family(),
    Positivity.sigma_negative_family(),
    Positivity.through_constructor_negative()
  ]

  test "W4 positivity antibodies are banked and every positivity record replays :ok" do
    for a <- @antibodies, do: Corpus.append(@corpus, a, Corpus.dedup_key(a, :antibody))

    results = Runner.replay([@corpus], %{"positivity" => Assays.Positivity})

    pos =
      Enum.filter(results, fn r ->
        match?(%Antigen.Challenge{assay: "positivity"}, r.entry)
      end)

    assert length(pos) >= 3

    assert Enum.all?(pos, &(&1.verdict == :ok)),
           inspect(pos |> Enum.reject(&(&1.verdict == :ok)) |> Enum.map(& &1.verdict))
  end
end
```

- [ ] **Step 2: Run twice (bank + idempotence)** — `mix test test/antigen/positivity_seed_test.exs` twice; expected PASS, `corpus.sexp` +3 lines then stable.

- [ ] **Step 3: Update roadmap §3.1 positivity row**

Replace
`| \`positivity\` | strict positivity of datatypes | positivity gen challenges | partial |`
with
`| \`positivity\` | strict positivity of datatypes | positivity gen challenges + W4 escape hatches (arrow-left, double-negation, sigma-hidden, through-constructor) | strong (deep walk; W4 holes found + fixed) |`
(adjust the parenthetical to the actual Task 7 audit outcome).

- [ ] **Step 4: Full suite and commit**

```bash
mix test
git add test/antigen/positivity_seed_test.exs test/antigen/corpus.sexp docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md
git commit -m "test(antigen): bank W4 positivity escape-hatch antibodies (A3/#19)" --author="Made In Heaven <madeinheaven@madeinheaven.com>"
```

---

### Task 10: W5 — the universes vertical

**Files:**
- Create: `lib/antigen/generators/universes.ex`
- Create: `lib/antigen/assays/universes.ex`
- Modify: `lib/antigen/runner.ex` (assay registry)
- Modify: `test/antigen/corpus_replay_test.exs` (`@registry`)
- Modify: `lib/antigen/challenge.ex` (`@known_atoms`: add `:u`)
- Test: `test/antigen/assays/universes_test.exs`
- Create: `test/antigen/universes_seed_test.exs`
- Modify (generated): `test/antigen/corpus.sexp`, `test/antigen/seeds.sexp`
- Modify (conditional — only if Step 6's D4 reroute fires): `test/antigen/reach_pin_test.exs`, `test/antigen/reach.sexp`

**Interfaces:**
- Consumes: `Cure.Core.Kernel.check_def/2`, `Kernel.check_family/2`, `Kernel.check_ctor/3`, `Cure.Core.Universe` (ceiling 2, `succ` errors `:universe_ceiling`), the `:indexed_case` and `:family` record shapes.
- Produces: `Antigen.Generators.Universes.{type_in_type/1, ceiling/1, cumulativity/1, stratification/1, ctor_field/1}` and `Antigen.Assays.Universes.run/1` under assay id `"universes"`.

- [ ] **Step 1: Write the failing tests**

Create `test/antigen/assays/universes_test.exs`:

```elixir
defmodule Antigen.Assays.UniversesTest do
  use ExUnit.Case, async: true
  alias Antigen.Assays.Universes, as: A
  alias Antigen.Generators.Universes, as: G

  test "Type 0 : Type 0 is rejected (no Type-in-Type)" do
    assert :ok == A.run(G.type_in_type(:ill_typed))
  end

  test "a def cannot be annotated AT the ceiling (Type 2 has no sort)" do
    assert :ok == A.run(G.ceiling(:ill_typed))
  end

  test "cumulativity: Nat : Type 0 is accepted at Type 1" do
    assert :ok == A.run(G.cumulativity(:well_typed))
  end

  test "stratification: Type 0 : Type 1 is accepted" do
    assert :ok == A.run(G.stratification(:well_typed))
  end

  test "two-universe ctor-field rule: a Type-0 field does not fit a level-0 family" do
    assert :ok == A.run(G.ctor_field(:ill_typed))
  end

  test "two-universe ctor-field rule: a Type-0 field fits a level-1 family" do
    assert :ok == A.run(G.ctor_field(:well_typed))
  end
end
```

- [ ] **Step 2: Run to verify failure** — `mix test test/antigen/assays/universes_test.exs`, expected FAIL (modules don't exist).

- [ ] **Step 3: Implement the generator**

Create `lib/antigen/generators/universes.ex`:

```elixir
defmodule Antigen.Generators.Universes do
  @moduledoc """
  Known-label universe-rule challenges (pre-port banking spec §4 W5): the fixed
  cumulative hierarchy `Type 0 : Type 1 : Type 2` (`Cure.Core.Universe`), no
  Type-in-Type, the ceiling, and the two-universe constructor-field rule —
  roadmap #20's rules, previously with zero Antigen coverage (A4).

  Def-shaped probes reuse the `:indexed_case` record shape (families + one def,
  checked by `Kernel.check_def`); family-shaped probes (ctor fields) use the
  `:family` shape (checked by `Kernel.check_family` + `check_ctor`). Labels are
  `:well_typed`/`:ill_typed`, correct by construction (argument in each @doc).
  """
  alias Antigen.Challenge
  alias Cure.Core.{Env, Inductive}

  @nat {:data, :Nat, [], []}

  defp nat_family,
    do:
      {Inductive.family(:Nat, [], [], 0),
       [Inductive.ctor(:Z, [], []), Inductive.ctor(:S, [{:n, @nat}], [])]}

  @doc "Girard guard: `def u : Type 0 = Type 0` must be rejected — Type 0 inhabits Type 1 only."
  @spec type_in_type(:ill_typed) :: Challenge.t()
  def type_in_type(:ill_typed) do
    def_challenge(:ill_typed, [], {:type, 0}, {:type, 0},
      "Type-in-Type: Type 0 : Type 0 must reject (Type 0 : Type 1)")
  end

  @doc """
  Ceiling: `def u : Type 2 = Type 1` must be rejected — a def's TYPE must itself
  be well-sorted, and `Type 2` has no successor sort in the fixed 0..2 hierarchy
  (`Universe.succ/1` → `:universe_ceiling`). The ceiling is a classifier of last
  resort, not an annotatable def type.
  """
  @spec ceiling(:ill_typed) :: Challenge.t()
  def ceiling(:ill_typed) do
    def_challenge(:ill_typed, [], {:type, 2}, {:type, 1},
      "ceiling: Type 2 has no sort — a def cannot be annotated AT Type 2")
  end

  @doc "Cumulativity: `Nat : Type 0` accepted at `Type 1` (`Type 0 <: Type 1`)."
  @spec cumulativity(:well_typed) :: Challenge.t()
  def cumulativity(:well_typed) do
    def_challenge(:well_typed, [nat_family()], {:type, 1}, @nat,
      "cumulativity: Nat (level 0) accepted at Type 1")
  end

  @doc "Exact stratification: `def u : Type 1 = Type 0` accepted."
  @spec stratification(:well_typed) :: Challenge.t()
  def stratification(:well_typed) do
    def_challenge(:well_typed, [], {:type, 1}, {:type, 0},
      "stratification: Type 0 : Type 1 accepted")
  end

  @doc """
  Two-universe constructor-field rule (`Kernel.check_ctor` → `:universe_level`):
  a field of type `Type 0` has sort level 1, so it fits a level-1 family
  (`:well_typed`) and does NOT fit a level-0 family (`:ill_typed`).
  """
  @spec ctor_field(:well_typed | :ill_typed) :: Challenge.t()
  def ctor_field(label) do
    level = if label == :well_typed, do: 1, else: 0
    fam = Inductive.family(:Foo, [], [], level)
    ctors = [Inductive.ctor(:MkFoo, [{:x, {:type, 0}}], [])]

    Challenge.new(
      kind: :family,
      assay: "universes",
      label: label,
      payload: %{family: fam, ctors: ctors},
      note: "two-universe rule: field x : Type 0 (sort level 1) vs family level #{level}"
    )
  end

  @doc "Rebuild the Env for a def-shaped universes challenge."
  @spec env_of(Challenge.t()) :: Env.t()
  def env_of(%Challenge{kind: :indexed_case, payload: %{families: families, def_name: dn, def_type: dt, def_body: db}}) do
    env = Enum.reduce(families, Env.empty(), fn {fam, ctors}, e -> Inductive.declare(e, fam, ctors) end)
    Env.add_def(env, dn, dt, db)
  end

  defp def_challenge(label, families, def_type, def_body, note) do
    Challenge.new(
      kind: :indexed_case,
      assay: "universes",
      label: label,
      payload: %{families: families, def_name: :u, def_type: def_type, def_body: def_body},
      note: note
    )
  end
end
```

- [ ] **Step 4: Implement the assay**

Create `lib/antigen/assays/universes.ex`:

```elixir
defmodule Antigen.Assays.Universes do
  @moduledoc """
  `universes` (pre-port banking spec §4 W5). Oracle = the known label. Def-shaped
  challenges run `Kernel.check_def`; family-shaped ones run `Kernel.check_family`
  plus `Kernel.check_ctor` per constructor. The kernel must accept iff
  `:well_typed`: an accepted `:ill_typed` (e.g. Type-in-Type) is a soundness
  infection; a rejected `:well_typed` (e.g. cumulativity) is an incompleteness bug.
  """
  alias Antigen.{Challenge, Generators}
  alias Cure.Core.{Env, Inductive, Kernel}

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :indexed_case, label: label, payload: %{def_name: dn}} = c) do
    env = Generators.Universes.env_of(c)
    judge(label, Kernel.check_def(env, dn), dn)
  end

  def run(%Challenge{kind: :family, label: label, payload: %{family: fam, ctors: ctors}}) do
    env = Inductive.declare(Env.empty(), fam, ctors)

    verdict =
      with :ok <- Kernel.check_family(env, fam) do
        Enum.reduce_while(ctors, :ok, fn ctor, :ok ->
          case Kernel.check_ctor(env, fam, ctor) do
            :ok -> {:cont, :ok}
            {:error, _} = err -> {:halt, err}
          end
        end)
      end

    judge(label, verdict, fam.name)
  end

  defp judge(:well_typed, :ok, _n), do: :ok
  defp judge(:ill_typed, {:error, _}, _n), do: :ok
  defp judge(:well_typed, {:error, reason}, n), do: {:violation, {:wrongly_rejected, {n, reason}}}
  defp judge(:ill_typed, :ok, n), do: {:violation, {:wrongly_accepted, n}}
end
```

- [ ] **Step 5: Wire the registries and the atom**

1. `lib/antigen/runner.ex` — after `defp assay_module("rewrite/eq"), do: Antigen.Assays.Rewrite` add:
   `defp assay_module("universes"), do: Antigen.Assays.Universes`
2. `test/antigen/corpus_replay_test.exs` — add to `@registry`: `"universes" => Assays.Universes`
3. `lib/antigen/challenge.ex` — in `@known_atoms`, change the last group
   `    :rewrite_eq, :eq_formation, :refl_typing, :rewrite_premise, :transport_type, :P`
   to
   `    :rewrite_eq, :eq_formation, :refl_typing, :rewrite_premise, :transport_type, :P,`
   `    # universes vertical`
   `    :u`
   (`:Foo`, `:MkFoo`, `:x`, `:n`, `:Nat`, `:Z`, `:S` are already interned.)

- [ ] **Step 6: Run the assay tests** — `mix test test/antigen/assays/universes_test.exs`, expected `6 tests, 0 failures`. Any failure is an audit finding on roadmap #20's claims (D4): report it. If it is a wrongly-ACCEPTED `:ill_typed`, stop for a red-green kernel fix before banking (soundness hole). If it is a wrongly-REJECTED `:well_typed` (cumulativity/stratification/ctor_field), apply the D4 symmetric reroute (Global Constraints): keep the label, pin the exact current violation in this test, bank that entry in `reach.sexp` (extend `reach_pin_test.exs` per the generalization described in Task 6 Step 5 — dispatch by `c.assay` via a small registry, key `@expected` by `c.note` rather than `focus`, since `universes` entries carry neither a uniform `focus` list nor always a `def_name`) — do NOT rely on Step 7's `:ok` seed filter to silently drop it — and have Task 11 leave A4 open rather than ✅.

- [ ] **Step 7: Bank**

Create `test/antigen/universes_seed_test.exs`:

```elixir
defmodule Antigen.UniversesSeedTest do
  @moduledoc """
  Banks the W5 universes vertical (pre-port banking spec §4 W5; roadmap A4 —
  first Antigen coverage of the universe rules). Ill-typed probes are antibodies
  (corpus.sexp); well-typed probes are known-good seeds (seeds.sexp). Idempotent.

  Store deltas: corpus +3 antibodies, seeds +2 (NOT +3). `stratification(:well_typed)`
  and `ctor_field(:well_typed)` are coverage-equivalent under the plateauing seed
  key (`ctors=[type]|depth=b0_2|flags=[]|label=well_typed`), so only the first
  banks as a seed — by design, one seed per coverage cell (the coverage key IS the
  seed store's identity; making it finer would orphan every stored key).
  `ctor_field(:well_typed)`'s acceptance remains guarded on every run by the assay
  test in `universes_test.exs`.
  """
  use ExUnit.Case, async: false
  alias Antigen.{Corpus, Runner, Assays}
  alias Antigen.Generators.Universes

  @corpus "test/antigen/corpus.sexp"
  @seeds "test/antigen/seeds.sexp"

  @antibodies [
    Universes.type_in_type(:ill_typed),
    Universes.ceiling(:ill_typed),
    Universes.ctor_field(:ill_typed)
  ]

  @seed_candidates [
    Universes.cumulativity(:well_typed),
    Universes.stratification(:well_typed),
    Universes.ctor_field(:well_typed)
  ]

  test "universes antibodies + seeds are banked and every one replays :ok" do
    for a <- @antibodies, do: Corpus.append(@corpus, a, Corpus.dedup_key(a, :antibody))

    for s <- @seed_candidates, Assays.Universes.run(s) == :ok do
      Corpus.append(@seeds, s, Corpus.dedup_key(s, :seed))
    end

    results = Runner.replay([@corpus, @seeds], %{"universes" => Assays.Universes})

    uni =
      Enum.filter(results, fn r ->
        match?(%Antigen.Challenge{assay: "universes"}, r.entry)
      end)

    # 3 antibodies + 2 seeds: stratification(:well_typed) and ctor_field(:well_typed)
    # share one coverage cell (see moduledoc), so the seed store holds one of them.
    assert length(uni) >= 5

    assert Enum.all?(uni, &(&1.verdict == :ok)),
           inspect(uni |> Enum.reject(&(&1.verdict == :ok)) |> Enum.map(& &1.verdict))
  end
end
```

Run twice (bank + idempotence): `mix test test/antigen/universes_seed_test.exs`. Expected store deltas on the first run: `corpus.sexp` +3 lines, `seeds.sexp` +2 lines (byte-stable on the second run). If a `Coverage.key/1` clause error surfaces on the `:family`-kind seed (coverage keys are computed on banking), inspect `lib/antigen/coverage.ex` — the positivity vertical already banks `:family` seeds, so the path exists; match its usage.

> **Execution-time correction (sanctioned by the Global Constraints immutability carve-out — a wrong predicted literal corrected to first-observed truth before the entry is committed):** the plan originally predicted seeds +3 and asserted `length(uni) >= 6`. First red run showed seeds +2: `stratification(:well_typed)` and `ctor_field(:well_typed)` collide on the coverage-plateau seed dedup key (`ctors=[type]|depth=b0_2|flags=[]|label=well_typed`). This is the seed store's *intended* semantics (one seed per coverage cell; the persisted key string is each record's identity, so a finer key would orphan every stored key and break dedup for all existing seed tests). Resolution: correct the count literal to `>= 5` and document the collision — do NOT touch the generators or `Coverage` to defeat dedup. Apparatus-design observation, not a kernel finding; the W5 audit itself was fully green (no holes, no D4 reroute — A4 closes unconditionally).

- [ ] **Step 8: Full suite and commit**

```bash
mix test
git add lib/antigen/generators/universes.ex lib/antigen/assays/universes.ex \
  lib/antigen/runner.ex lib/antigen/challenge.ex test/antigen/corpus_replay_test.exs \
  test/antigen/assays/universes_test.exs test/antigen/universes_seed_test.exs \
  test/antigen/corpus.sexp test/antigen/seeds.sexp
git commit -m "test(antigen): universes vertical — Type-in-Type, ceiling, cumulativity, ctor-field rule (W5/A4)" --author="Made In Heaven <madeinheaven@madeinheaven.com>"
```

If Step 6's D4 reroute fired, also `git add test/antigen/reach_pin_test.exs test/antigen/reach.sexp` into this same commit — the reroute is not a separable, deferrable change.

---

### Task 11: close the ledger (§3) + final gate

**Files:**
- Modify: `docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md` (§3.1 table rows, §3.2 rows A2/A3/A4/A9, §2 row 19 status cell only, §2 row 23 status cell only)

**Interfaces:** consumes all prior tasks' outcomes; produces the corrected ledger.

- [ ] **Step 1: Update §3.2 rows**

Per gate 5, every ✅ below is conditional: if a D4 incompleteness reroute sent one of that row's entries to `reach.sexp`, mark the row `partial (…)` naming the rerouted entry instead of ✅.

- A2: Priority cell → `✅ done (deletion antibody + occurs pin banked)`
- A3: Priority cell → `✅ done (three escape hatches banked; holes found+fixed per W4 audit)` — match the actual Task 7/8 outcome.
- A4: Priority cell → `✅ done (universes vertical banked)`
- A9: Priority cell → `✅ done (subsumed by W1 adversarial set)` (unconditional — W1 has no reroute branch)

- [ ] **Step 2: Update §3.1 table**

- `totality/terminating` row, challenges cell: append ` + W2 reach pins (reach.sexp, P1 targets)`.
- Add a new row at the bottom:
  `| \`universes\` | fixed hierarchy: no Type-in-Type, ceiling, cumulativity, two-universe ctor-field rule | \`type_in_type\`, \`ceiling\`, \`cumulativity\`, \`stratification\`, \`ctor_field\` | strong |`

- [ ] **Step 3: Update §2 status cells for rows 19 and 23** (status column ONLY — row text belongs to P0's plan scope-split):

- Row 19: `⬜` → `✅ (W4: audited, holes fixed, antibodies banked)` — match the audit outcome.
- Row 23: `⬜` → `✅ (W3: deletion antibody + occurs pin)` — if the Task 6 Step 5 reroute fired, use `partial (occurs pin banked; deletion well-typed rerouted to reach.sexp)` instead.

- [ ] **Step 4: Final gate**

Run: `mix test`
Expected: full PASS. Then re-run all five banking/pin test files once more (`totality_seed_test.exs`, `reach_pin_test.exs`, `indexed_seed_test.exs`, `positivity_seed_test.exs`, `universes_seed_test.exs`) and `git status --short` — expected: clean tree (all stores stable).

- [ ] **Step 5: Commit**

```bash
git add docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md
git commit -m "docs(roadmap): pre-port banking run complete — A2/A3/A4/A9 done, #19/#23 closed" --author="Made In Heaven <madeinheaven@madeinheaven.com>"
```
