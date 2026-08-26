# Antigen elab-tier dot-forcing vertical — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a source-level dot-forcing family to the existing `:elab_program` Antigen tier so call-site wiring of the named-implicit check (the C-a defect class) is covered by randomized-tier challenges entering at `Cure.Elab.Program.elaborate/1`.

**Architecture:** One new generator (`Antigen.Generators.ElabDotForcing`, fixed deterministic catalog + metamorphic variants, mirroring `ElabErasure`), two new `run/1` clauses in `Antigen.Assays.Elab` for assay `"elab/dot_forcing"` (catalog with `expect_error` head-check; `:same`/`:flip` relations), one registry line in `Antigen.Runner`, one test file. Spec: `docs/superpowers/specs/antigen/2026-07-08-antigen-elab-dot-forcing-design.md` (hardened `5bd5b7b`).

**Tech Stack:** Elixir / ExUnit; no new deps.

## Global Constraints

- **Layer A only.** NO changes under `lib/cure/` — if an elaborator behavior contradicts a catalog label, STOP and report (spec §4); do not patch the elaborator.
- **Two pipelines steer:** the dependent machinery is `lib/cure/elab/*` + `lib/cure/core/*`; `lib/cure/compiler/*` and `lib/cure/types/*` are the non-dependent decoy pipeline. (Read-only relevance here, but binding for any investigation.)
- **Ghost commits:** `git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>"`, NO Co-Authored-By or any trailer.
- **Explicit-pathspec staging only:** `git add -- <path>`; never `-A`/`.`.
- **ONE `mix` invocation at a time**, scoped during TDD; the full suite once, alone, at the Task 4 gate.
- **Tests immutable once green.** The pinned error shape `{:named_implicit_unforced, "m"}` (2-tuple) must not be disturbed (it is not one of this catalog's heads — spec §2.3).
- **Fixture provenance:** catalog sources are copied verbatim from landed fixtures in `test/cure/elab/named_implicit_tail_test.exs` (#12 commits `7a2febe`/`8568d4b`); the landed text wins over any sketch.

## File Structure

- Modify: `lib/antigen/assays/elab.ex` — two `run/1` clauses + `reject_head/1` helper (insert after the `elab/erasure` relation clause, before `elab/soundness`).
- Modify: `lib/antigen/runner.ex` — one `assay_module` line after the `"elab/erasure"` entry (`:349`; relocate by content, not number).
- Modify: `lib/antigen/challenge.ex` — add `"expect_error" => :expect_error` to the `@elab_keys` whitelist (Task 4) so a dot-forcing reject-cell payload (which carries a key no existing `elab/*` family ever used) round-trips through `to_pieces`/`from_pieces` instead of raising.
- Create: `lib/antigen/generators/elab_dot_forcing.ex`.
- Create: `test/antigen/elab_dot_forcing_test.exs` (directly under `test/antigen/`, NOT `test/antigen/generators/` — spec §5).

---

### Task 1: Assay clauses + runner registry

**Files:**
- Modify: `lib/antigen/assays/elab.ex`
- Modify: `lib/antigen/runner.ex`
- Test: `test/antigen/elab_dot_forcing_test.exs` (new)

**Interfaces:**
- Consumes: `Antigen.Assays.Elab.elaborate/1` (existing private helper), `verdict_bit/1` (existing), `Antigen.Challenge.new/1`, `Antigen.Generators.ElabErasure.source/1` (existing public — reused as inert accept/reject sources for discrimination tests; the clause under test dispatches on the assay string, not source content).
- Produces: `Antigen.Assays.Elab.run/1` clauses for `"elab/dot_forcing"` (catalog: payload `%{id, src, expect}` + optional `expect_error`; relation: payload `%{id, transform, relation, base_src, variant_src}`); violation tags `{:dot_forcing_verdict_wrong, id, %{expected, actual}}`, `{:dot_forcing_wrong_reject_reason, id, got}`, `{:dot_forcing_relation_wrong, id, transform, %{relation, base, variant}}`; `Antigen.Runner.assay_module_for("elab/dot_forcing") == Antigen.Assays.Elab`. Tasks 2–4 consume all of these.

- [ ] **Step 1: Write the failing tests**

Create `test/antigen/elab_dot_forcing_test.exs`:

```elixir
defmodule Antigen.ElabDotForcingTest do
  @moduledoc """
  Tests for the source-level dot-forcing vertical (spec
  2026-07-08-antigen-elab-dot-forcing-design): challenges entering at
  Program.elaborate/1 so the named-implicit check's CALL-SITE WIRING (the C-a
  defect class) is covered — the value-level forcing/dot oracle is structurally
  blind to a caller that skips the check. These test the VERTICAL (assay
  discrimination, catalog verdicts, metamorphic relations); the catalog gate
  doubles as a regression gate on #12's C-a/C-c fixes.
  """
  use ExUnit.Case, async: true

  alias Antigen.Assays.Elab
  alias Antigen.Challenge
  alias Antigen.Generators.ElabErasure

  # Grammar-stage typo: lexes fine, fails in the PARSER, whose error payload is
  # a LIST (parser.ex `{:error, Enum.reverse(errors)}`) — the §2.3 non-tuple
  # guard's target shape.
  @grammar_broken "mod P\n  fn\nend\n"

  defp catalog_challenge(id, src, expect, extra \\ %{}) do
    Challenge.new(
      kind: :elab_program,
      assay: "elab/dot_forcing",
      label: expect,
      payload: Map.merge(%{id: id, src: src, expect: expect}, extra)
    )
  end

  describe "assay discrimination (red-green of the vertical itself)" do
    test "catalog clause is :ok when the actual verdict matches the expected one" do
      assert :ok = Elab.run(catalog_challenge("acc", ElabErasure.source("type_position"), :accept))
      assert :ok = Elab.run(catalog_challenge("rej", ElabErasure.source("returned"), :reject))
    end

    test "catalog clause fires on a verdict contradiction, both directions" do
      assert {:violation, {:dot_forcing_verdict_wrong, "w1", %{expected: :reject, actual: :accept}}} =
               Elab.run(catalog_challenge("w1", ElabErasure.source("type_position"), :reject))

      assert {:violation, {:dot_forcing_verdict_wrong, "w2", %{expected: :accept, actual: :reject}}} =
               Elab.run(catalog_challenge("w2", ElabErasure.source("returned"), :accept))
    end

    test "expect_error head match passes; a mismatched head is wrong_reject_reason" do
      # source("returned") rejects with head :erased_used_relevantly.
      assert :ok =
               Elab.run(
                 catalog_challenge("h1", ElabErasure.source("returned"), :reject, %{
                   expect_error: :erased_used_relevantly
                 })
               )

      assert {:violation, {:dot_forcing_wrong_reject_reason, "h2", :erased_used_relevantly}} =
               Elab.run(
                 catalog_challenge("h2", ElabErasure.source("returned"), :reject, %{
                   expect_error: :forced_pattern_mismatch
                 })
               )
    end

    test "non-tuple (parser-list) reject never matches a head and never crashes" do
      assert {:violation, {:dot_forcing_wrong_reject_reason, "h3", :non_tuple_error}} =
               Elab.run(
                 catalog_challenge("h3", @grammar_broken, :reject, %{
                   expect_error: :forced_pattern_mismatch
                 })
               )
    end

    test "relation clause: :flip with an identical variant fires" do
      src = ElabErasure.source("type_position")

      c =
        Challenge.new(
          kind: :elab_program,
          assay: "elab/dot_forcing",
          label: :none,
          payload: %{id: "f1", transform: "identity", relation: :flip, base_src: src, variant_src: src}
        )

      assert {:violation,
              {:dot_forcing_relation_wrong, "f1", "identity",
               %{relation: :flip, base: :accept, variant: :accept}}} = Elab.run(c)
    end

    test "relation clause: :same with agreeing sources is :ok" do
      src = ElabErasure.source("type_position")

      c =
        Challenge.new(
          kind: :elab_program,
          assay: "elab/dot_forcing",
          label: :none,
          payload: %{id: "s1", transform: "identity", relation: :same, base_src: src, variant_src: src}
        )

      assert :ok = Elab.run(c)
    end
  end

  describe "registry wiring" do
    test "the runner maps elab/dot_forcing to the Elab assay module" do
      assert Antigen.Runner.assay_module_for("elab/dot_forcing") == Antigen.Assays.Elab
    end
  end
end
```

- [ ] **Step 2: Run tests to verify they fail for the right reason**

Run: `mix test test/antigen/elab_dot_forcing_test.exs`
Expected: FAIL — every `Elab.run/1` call raises `FunctionClauseError` (no `"elab/dot_forcing"` clause), and the registry test raises `FunctionClauseError` from `Antigen.Runner.assay_module_for/1`.

- [ ] **Step 3: Add the two assay clauses + helper**

In `lib/antigen/assays/elab.ex`, insert after the `elab/erasure` relation clause (the `def run(%Challenge{kind: :elab_program, assay: "elab/erasure", payload: %{relation: rel} = p})` block) and before the `elab/soundness` clause:

```elixir
  # elab/dot_forcing — catalog form (spec 2026-07-08-antigen-elab-dot-forcing):
  # the actual verdict must match the expected one. Reject cells carrying
  # `expect_error` also pin the error HEAD, so a fixture that rots into
  # rejecting for an unrelated reason (parse error, unbound name) infects
  # instead of passing silently.
  def run(%Challenge{kind: :elab_program, assay: "elab/dot_forcing", payload: %{expect: expect} = p}) do
    result = elaborate(p.src)
    actual = verdict_bit(result)

    cond do
      actual != expect ->
        {:violation, {:dot_forcing_verdict_wrong, p.id, %{expected: expect, actual: actual}}}

      actual == :reject and Map.has_key?(p, :expect_error) ->
        got = reject_head(result)

        if got == p.expect_error do
          :ok
        else
          {:violation, {:dot_forcing_wrong_reject_reason, p.id, got}}
        end

      true ->
        :ok
    end
  end

  # elab/dot_forcing — relation form: `:same` (verdict invariant under a
  # typing-preserving perturbation) or `:flip` (an accepting base must reject
  # after the targeted mutation — the call-site-wiring / load-bearing pin).
  def run(%Challenge{kind: :elab_program, assay: "elab/dot_forcing", payload: %{relation: rel} = p}) do
    base = verdict_bit(elaborate(p.base_src))
    variant = verdict_bit(elaborate(p.variant_src))

    ok? =
      case rel do
        :same -> base == variant
        :flip -> base == :accept and variant == :reject
      end

    if ok? do
      :ok
    else
      {:violation,
       {:dot_forcing_relation_wrong, p.id, p.transform, %{relation: rel, base: base, variant: variant}}}
    end
  end
```

And add the private helper next to `verdict_bit/1` at the bottom of the module:

```elixir
  # Error head of a rejecting elaboration result. Non-tuple hardening (spec
  # §2.3): parser grammar failures carry a LIST, and a normalized raise has no
  # head — neither can ever match an `expect_error` atom, so both land in the
  # wrong-reject-reason violation instead of crashing `elem/2`.
  defp reject_head({:error, e}) when is_tuple(e) and tuple_size(e) > 0, do: elem(e, 0)
  defp reject_head({:error, _non_tuple}), do: :non_tuple_error
  defp reject_head({:raise, _}), do: :raised_error
```

- [ ] **Step 4: Add the runner registry line**

In `lib/antigen/runner.ex`, directly after `defp assay_module("elab/erasure"), do: Antigen.Assays.Elab`:

```elixir
  defp assay_module("elab/dot_forcing"), do: Antigen.Assays.Elab
```

- [ ] **Step 5: Run tests to verify they pass**

Run: `mix test test/antigen/elab_dot_forcing_test.exs`
Expected: PASS (7 tests).

- [ ] **Step 6: Regression on the shared assay module**

Run: `mix test test/antigen/elab_erasure_test.exs test/antigen/elab_completeness_test.exs test/antigen/runner_test.exs`
Expected: PASS (no existing clause disturbed).

- [ ] **Step 7: Commit**

```bash
git add -- lib/antigen/assays/elab.ex lib/antigen/runner.ex test/antigen/elab_dot_forcing_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): elab/dot_forcing assay clauses + runner registry"
```

---

### Task 2: Catalog generator (six cells)

**Files:**
- Create: `lib/antigen/generators/elab_dot_forcing.ex`
- Test: `test/antigen/elab_dot_forcing_test.exs` (extend)

**Interfaces:**
- Consumes: Task 1's clauses; `Antigen.Challenge`.
- Produces: `Antigen.Generators.ElabDotForcing` — `module(:carried | :exist, body)`, `dot_forcing_challenges/0`, `catalog/0` (`[{id, expect}]`), `source/1`, `body/1` (body text by id — Task 3's transforms need bodies, not full modules). Six cell ids: `"forced/carried/right"`, `"forced/carried/wrong"`, `"forced/plain/right"`, `"forced/plain/wrong"`, `"unforced/bind_erased"`, `"unforced/bind_relevant"`.

**Fixture provenance (spec §2.2, landed text wins):** carried cells are verbatim the Task-2 unit fixtures (`named_implicit_tail_test.exs:59-79`, bodies `Z()` — never `j`, which trips `{:erased_used_relevantly, …}` and confounds the axes). Plain cells use the landed C-b `Vec` right-dot fixture (`:20-29`, the only *landed* plain right-dot program) and its wrong-dot derivative — NOT the H-family-minus-sibling variant, whose accept verdict is unverified. Unforced cells are verbatim the Task-4 `Pack` fixtures (`:134-153`). Two preambles: `:carried` (Nat+SList+app+H+G) and `:exist` (the landed `@exist_preamble`: Nat+Vec+Pack — Vec serves the plain cells, Pack the unforced cells).

- [ ] **Step 1: Write the failing tests**

Append to `test/antigen/elab_dot_forcing_test.exs`:

```elixir
  describe "catalog gate (all six cells hold on today's post-#12 elaborator)" do
    alias Antigen.Generators.ElabDotForcing

    test "the catalog has exactly the six specced cells" do
      assert ElabDotForcing.catalog() |> Enum.map(&elem(&1, 0)) |> Enum.sort() == [
               "forced/carried/right",
               "forced/carried/wrong",
               "forced/plain/right",
               "forced/plain/wrong",
               "unforced/bind_erased",
               "unforced/bind_relevant"
             ]
    end

    test "the catalog is genuinely two-sided" do
      verdicts = ElabDotForcing.catalog() |> Enum.map(&elem(&1, 1)) |> Enum.uniq() |> Enum.sort()
      assert verdicts == [:accept, :reject]
    end

    test "every catalog entry elaborates to its expected verdict (and error head)" do
      violations =
        ElabDotForcing.dot_forcing_challenges()
        |> Enum.map(fn c -> {c.payload.id, Elab.run(c)} end)
        |> Enum.reject(fn {_id, v} -> v == :ok end)

      assert violations == [],
             "dot-forcing catalog verdict wrong (call-site wiring or check regressed):\n" <>
               Enum.map_join(violations, "\n", &inspect/1)
    end

    test "reject cells carry their expected error heads" do
      by_id = Map.new(ElabDotForcing.dot_forcing_challenges(), &{&1.payload.id, &1.payload})
      assert by_id["forced/carried/wrong"].expect_error == :forced_pattern_mismatch
      assert by_id["forced/plain/wrong"].expect_error == :forced_pattern_mismatch
      assert by_id["unforced/bind_relevant"].expect_error == :erased_used_relevantly
      refute Map.has_key?(by_id["forced/carried/right"], :expect_error)
    end
  end
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `mix test test/antigen/elab_dot_forcing_test.exs`
Expected: the four new tests FAIL with `UndefinedFunctionError` (`Antigen.Generators.ElabDotForcing` not available); Task 1's tests still PASS.

- [ ] **Step 3: Implement the generator (catalog half)**

Create `lib/antigen/generators/elab_dot_forcing.ex`:

```elixir
defmodule Antigen.Generators.ElabDotForcing do
  @moduledoc """
  Source-level dot-forcing vertical (spec 2026-07-08-antigen-elab-dot-forcing):
  `:elab_program` challenges entering at `Cure.Elab.Program.elaborate/1`, so the
  named-implicit check's CALL-SITE WIRING is probed — the class the value-level
  `forcing/dot` oracle is structurally blind to (it calls the check directly and
  can never observe a dispatch path that skips it, as C-a's carried-eq path did
  pre-#12).

  Six two-sided catalog cells (labels correct-by-construction — the generator
  writes both the forced solution and the written dot value):

    * forced axis, {plain, carried} × {right, wrong} — `wrong` cells pin error
      head `:forced_pattern_mismatch`;
    * unforced C-c axis, {bind_erased, bind_relevant} — `bind_relevant` pins
      `:erased_used_relevantly` (the quantity gate, not a named-implicit error).

  Sources are verbatim the #12-landed fixtures (`named_implicit_tail_test.exs`);
  carried cells are the only landed programs reaching
  `elaborate_carried_eq_branch`. Metamorphic layer: `corrupt_dot` /
  `promote_use` are `:flip` relations (the C-a-class causal pin — base held
  fixed, only the checked property mutated); `alpha_rename` /
  `extra_unused_param` are `:same` perturbations. Transforms operate on the
  probe-fn BODY only, never `preamble <> body` (first-match regex safety —
  spec §2.2 structural note).
  """

  alias Antigen.Challenge

  # Carried + forced mixed shape (#12 Task 2): H's first index is ctor-pinned
  # (forced m := j), the second is a stuck function index carried via the
  # sibling `w : G(app(p, q))` (detect_carried_index).
  @carried_preamble """
    type Nat = Z | S(Nat)
    type SList = SNil | SCons(Nat, SList)
    fn app(xs: SList, ys: SList) -> SList = match xs
      SNil() -> ys
      SCons(h, t) -> SCons(h, app(t, ys))
    type H indices (n: Nat, xs: SList)
      hmk : H(S(m), app(as, bs))
    type G indices (xs: SList)
      gwrap : G(cs)
  """

  # Vec (plain forced cells) + Pack (unforced C-c cells) — the landed
  # @exist_preamble of #12 Task 4.
  @exist_preamble """
    type Nat = Z | S(Nat)
    type Vec(a: Type) indices (n: Nat)
      vnil : Vec(a, Z)
      vcons : a -> Vec(a, n) -> Vec(a, S(n))
    type Pack(a: Type) indices ()
      pk : Vec(a, m) -> Pack(a)
  """

  defp preamble(:carried), do: @carried_preamble
  defp preamble(:exist), do: @exist_preamble

  @doc "Wrap a probe-`fn` body into a self-contained, elaborable module."
  @spec module(:carried | :exist, String.t()) :: String.t()
  def module(pre, body), do: "mod P\n" <> preamble(pre) <> body <> "end\n"

  # -- Two-sided catalog: {id, expect, expect_error | nil, preamble, note, body}
  @catalog [
    {"forced/carried/right", :accept, nil, :carried,
     "right dot on the carried-eq path (over-rejection guard)",
     """
       fn g({j: Nat}, {p: SList}, {q: SList}, v: H(S(j), app(p, q)), w: G(app(p, q))) -> Nat = match v
         hmk({m = .j}) -> Z()
     """},
    {"forced/carried/wrong", :reject, :forced_pattern_mismatch, :carried,
     "wrong dot on the carried-eq path (the C-a cell — pre-#12 this ACCEPTED)",
     """
       fn f({j: Nat}, {p: SList}, {q: SList}, v: H(S(j), app(p, q)), w: G(app(p, q))) -> Nat = match v
         hmk({m = .(S(j))}) -> Z()
     """},
    {"forced/plain/right", :accept, nil, :exist,
     "right dot on the plain dispatch path (landed C-b shape)",
     """
       fn f({a: Type}, {k: Nat}, v: Vec(a, S(k))) -> Vec(a, S(k)) = match v
         vcons({n = .k}, h, t) -> v
     """},
    {"forced/plain/wrong", :reject, :forced_pattern_mismatch, :exist,
     "wrong dot on the plain dispatch path",
     """
       fn f({a: Type}, {k: Nat}, v: Vec(a, S(k))) -> Vec(a, S(k)) = match v
         vcons({n = .(S(k))}, h, t) -> v
     """},
    {"unforced/bind_erased", :accept, nil, :exist,
     "unforced bare-variable named implicit bound at quantity 0, used only erasedly",
     """
       fn f({a: Type}, p: Pack(a)) -> Nat = match p
         pk({m = mm}, v) -> Z()
     """},
    {"unforced/bind_relevant", :reject, :erased_used_relevantly, :exist,
     "quantity-0 binding used relevantly rejects via Relevance (C-c gate)",
     """
       fn g({a: Type}, p: Pack(a)) -> Nat = match p
         pk({m = mm}, v) -> mm
     """}
  ]

  @doc "All two-sided catalog challenges as `%Challenge{}` structs (deterministic)."
  @spec dot_forcing_challenges() :: [Challenge.t()]
  def dot_forcing_challenges do
    Enum.map(@catalog, fn {id, expect, err, pre, note, body} ->
      payload = %{id: id, src: module(pre, body), expect: expect}
      payload = if err, do: Map.put(payload, :expect_error, err), else: payload

      Challenge.new(
        kind: :elab_program,
        assay: "elab/dot_forcing",
        label: expect,
        payload: payload,
        note: note
      )
    end)
  end

  @doc "The catalog ids paired with their expected verdicts."
  @spec catalog() :: [{String.t(), :accept | :reject}]
  def catalog, do: Enum.map(@catalog, fn {id, expect, _e, _p, _n, _b} -> {id, expect} end)

  @doc "Look up a catalog entry's full module source by id."
  @spec source(String.t()) :: String.t() | nil
  def source(id) do
    case entry(id) do
      {_id, _e, _err, pre, _n, body} -> module(pre, body)
      nil -> nil
    end
  end

  @doc "Look up a catalog entry's probe-fn BODY by id (transform input)."
  @spec body(String.t()) :: String.t() | nil
  def body(id) do
    case entry(id) do
      {_id, _e, _err, _pre, _n, body} -> body
      nil -> nil
    end
  end

  defp entry(id), do: Enum.find(@catalog, fn {i, _, _, _, _, _} -> i == id end)
end
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `mix test test/antigen/elab_dot_forcing_test.exs`
Expected: PASS (11 tests). The catalog-gate test failing here means an elaborator behavior contradicts a landed-fixture-derived label — that is the spec §4 STOP-and-report condition (with one narrow exception: if ONLY `"forced/plain/wrong"` fails — the single cell without a verbatim landed twin — first verify by hand that `Program.elaborate` on that source returns something other than `{:error, {:forced_pattern_mismatch, _, _}}`, and report what it returns instead of guessing).

- [ ] **Step 5: Commit**

```bash
git add -- lib/antigen/generators/elab_dot_forcing.ex test/antigen/elab_dot_forcing_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): elab dot-forcing catalog generator (six cells)"
```

---

### Task 3: Metamorphic layer (flips + perturbations)

**Files:**
- Modify: `lib/antigen/generators/elab_dot_forcing.ex`
- Test: `test/antigen/elab_dot_forcing_test.exs` (extend)

**Interfaces:**
- Consumes: Task 2's `@catalog` / `module/2` / `body/1`.
- Produces: `metamorphic_challenges/0` — `:flip` challenges `corrupt_dot` (on both forced `right` bases) and `promote_use` (on `unforced/bind_erased`); `:same` challenges `alpha_rename` + `extra_unused_param` on every base. Relation payload `%{id, transform, relation, base_src, variant_src}`.

- [ ] **Step 1: Write the failing tests**

Append to `test/antigen/elab_dot_forcing_test.exs`:

```elixir
  describe "metamorphic gates" do
    alias Antigen.Generators.ElabDotForcing

    test "every metamorphic relation holds (flips flip, sames stay)" do
      violations =
        ElabDotForcing.metamorphic_challenges()
        |> Enum.map(fn c -> {c.payload.id, c.payload.transform, c.payload.relation, Elab.run(c)} end)
        |> Enum.reject(fn {_id, _t, _r, v} -> v == :ok end)

      assert violations == [],
             "dot-forcing metamorphic relation broken:\n" <>
               Enum.map_join(violations, "\n", &inspect/1)
    end

    test "the C-a causal pin exists: corrupt_dot flips BOTH dispatch paths" do
      flips =
        ElabDotForcing.metamorphic_challenges()
        |> Enum.filter(fn c -> c.payload.transform == "corrupt_dot" end)
        |> Enum.map(fn c -> c.payload.id end)
        |> Enum.sort()

      assert flips == ["forced/carried/right", "forced/plain/right"]
    end

    test "the C-c load-bearing pin exists: promote_use flips bind_erased" do
      assert [%{payload: %{id: "unforced/bind_erased", relation: :flip}}] =
               ElabDotForcing.metamorphic_challenges()
               |> Enum.filter(fn c -> c.payload.transform == "promote_use" end)
    end
  end
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `mix test test/antigen/elab_dot_forcing_test.exs`
Expected: the three new tests FAIL with `UndefinedFunctionError` (`metamorphic_challenges/0` not exported); all earlier tests PASS.

- [ ] **Step 3: Implement the metamorphic half**

Append to `lib/antigen/generators/elab_dot_forcing.ex` (inside the module, after `entry/1`):

```elixir
  # -- Metamorphic challenges --------------------------------------------------

  @doc """
  Metamorphic challenges.

    * `corrupt_dot` (`:flip`) — on each forced-axis ACCEPTING base, corrupt only
      the written dot value; the verdict must flip. Holding the program fixed
      and varying only the checked value pins "the check runs and compares" on
      that dispatch path (the carried instance is the C-a detector).
    * `promote_use` (`:flip`) — on the bind_erased base, use the quantity-0
      binding relevantly; must flip (the C-c gate is load-bearing).
    * `alpha_rename` / `extra_unused_param` (`:same`) — typing-preserving frame
      perturbations on EVERY base; the verdict must not change.

  All transforms take the probe-fn BODY only (never `preamble <> body`), so the
  first-match regexes can never collide with the preamble's helper `fn app`.
  """
  @spec metamorphic_challenges() :: [Challenge.t()]
  def metamorphic_challenges do
    Enum.flat_map(@catalog, fn {id, expect, _err, pre, _note, body} ->
      base_src = module(pre, body)

      invariance =
        [{"alpha_rename", alpha_rename(body)}, {"extra_unused_param", prepend_unused_param(body)}]
        |> Enum.filter(fn {_t, b} -> is_binary(b) and b != body end)
        |> Enum.map(fn {t, vbody} -> challenge(id, t, :same, base_src, module(pre, vbody)) end)

      flips =
        case {id, expect} do
          {_, :accept} ->
            [{"corrupt_dot", corrupt_dot(body)}, {"promote_use", promote_use(body)}]
            |> Enum.filter(fn {_t, b} -> is_binary(b) and b != body end)
            |> Enum.map(fn {t, vbody} -> challenge(id, t, :flip, base_src, module(pre, vbody)) end)

          _ ->
            []
        end

      invariance ++ flips
    end)
  end

  defp challenge(id, transform, relation, base_src, variant_src) do
    Challenge.new(
      kind: :elab_program,
      assay: "elab/dot_forcing",
      label: :none,
      payload: %{
        id: id,
        transform: transform,
        relation: relation,
        base_src: base_src,
        variant_src: variant_src
      },
      note: "#{id} #{relation} under #{transform}"
    )
  end

  # -- Metamorphic transforms (probe-fn BODY input only) ------------------------

  # Corrupt the written dot value on a forced right-dot base: the forced
  # solution is `j` (carried, `{m = .j}`) or `k` (plain, `{n = .k}`); wrap it
  # in one more S so it can no longer be convertible with the pinned value.
  # nil on bodies with no right-dot to corrupt (unforced cells).
  defp corrupt_dot(body) do
    cond do
      String.contains?(body, "{m = .j}") -> String.replace(body, "{m = .j}", "{m = .(S(j))}")
      String.contains?(body, "{n = .k}") -> String.replace(body, "{n = .k}", "{n = .(S(k))}")
      true -> nil
    end
  end

  # Use the quantity-0 binding relevantly: bind_erased's arm `pk({m = mm}, v)
  # -> Z()` becomes `-> mm` (the landed bind_relevant fixture's exact body
  # motion). nil on bodies without the bound-and-discarded shape.
  defp promote_use(body) do
    if String.contains?(body, "pk({m = mm}, v) -> Z()") do
      String.replace(body, "pk({m = mm}, v) -> Z()", "pk({m = mm}, v) -> mm")
    else
      nil
    end
  end

  # Rename the bound value `v` consistently (α-equivalence); standalone `v`
  # only, so type names and `vcons`/`vnil` are untouched.
  defp alpha_rename(body), do: String.replace(body, ~r/\bv\b/, "vv0")

  # Prepend an unused erased implicit to the probe `fn` (every catalog body's
  # first fn IS the probe fn and starts with a `{…}` implicit list), shifting
  # every de Bruijn index by one — a frame perturbation a correct elaborator
  # absorbs. Mirrors ElabErasure.prepend_unused_param/1.
  defp prepend_unused_param(body) do
    if Regex.match?(~r/fn \w+\(\{/, body) do
      String.replace(body, ~r/(fn \w+\()\{/, "\\1{z_unused: Nat}, {", global: false)
    else
      nil
    end
  end
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `mix test test/antigen/elab_dot_forcing_test.exs`
Expected: PASS (14 tests). A `:same` violation here means a perturbation is NOT typing-preserving for these fixtures — inspect the variant source by hand (`IO.puts`), and if the transform itself is unsound for a body shape (not an elaborator bug), exclude that {transform, cell} pair with a comment stating why. This is a narrower version of the discipline `ElabComplete`'s moduledoc documents for its own metamorphic suite (it never implements a `let`-wrap transform at all, precisely because Cure's surface syntax requires the dependent match to be the `fn` body head, so wrapping it would itself be non-preserving — a blanket exclusion with a stated reason, not a per-cell one): the reasoning pattern is the same (prove non-preservation, state it, exclude with a comment), but here the exclusion is scoped to one {transform, cell} pair rather than dropping the transform outright, since the other cells are unaffected. A `:flip` violation is the spec §4 STOP-and-report (it is exactly the defect class this vertical exists to catch).

- [ ] **Step 5: Commit**

```bash
git add -- lib/antigen/generators/elab_dot_forcing.ex test/antigen/elab_dot_forcing_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): elab dot-forcing metamorphic flips + perturbations"
```

---

### Task 4: Corpus round-trip + gate

**Files:**
- Modify: `lib/antigen/challenge.ex`
- Test: `test/antigen/elab_dot_forcing_test.exs` (extend)

**Interfaces:**
- Consumes: everything above; `Antigen.Challenge.to_pieces/1` / `from_pieces/7` (existing).
- Produces: the finished vertical; `lib/antigen/challenge.ex`'s `@elab_keys` whitelist gains an `"expect_error" => :expect_error` entry; task #16 closes.

**Known gap this task must close:** `@elab_keys` (`lib/antigen/challenge.ex`) today whitelists only `id`/`src`/`transform`/`base_src`/`variant_src`/`expect`/`relation` — every key the `elab/erasure` family ever produced. This catalog's reject cells introduce a NEW payload key, `expect_error`, that no existing `elab/*` family has. `from_pieces(:elab_program, ...)` maps every scaffold key through this whitelist and `raise`s `ArgumentError` on an unrecognized one, so round-tripping a reject-cell payload (e.g. `"forced/carried/wrong"`) crashes today. Picking only the catalog's first entry (`"forced/carried/right"`, an accept cell with no `expect_error` key) for the round-trip test — as a naive port of `elab_erasure_test.exs`'s single-entry pick would do — hides this gap entirely, since that one payload round-trips fine under the existing whitelist. Step 1 below therefore tests BOTH an accept cell (no `expect_error`) and a reject cell (`expect_error` present) so the gap is actually exercised.

- [ ] **Step 1: Write the corpus round-trip tests**

Append to `test/antigen/elab_dot_forcing_test.exs` (serialization parity, mirroring `elab_erasure_test.exs`'s single-entry test, but split into two cases — one per payload shape this family produces):

```elixir
  describe "corpus round-trip (serialization parity)" do
    test "an accept catalog challenge (no expect_error key) survives to_pieces/from_pieces" do
      c =
        Antigen.Generators.ElabDotForcing.dot_forcing_challenges()
        |> Enum.find(&(&1.payload.id == "forced/carried/right"))

      {scaffold, pieces} = Challenge.to_pieces(c)
      back = Challenge.from_pieces(:elab_program, c.assay, c.label, c.seed, c.note, scaffold, pieces)
      assert back.payload == c.payload
      assert back.assay == c.assay
    end

    test "a reject catalog challenge carrying expect_error survives to_pieces/from_pieces" do
      c =
        Antigen.Generators.ElabDotForcing.dot_forcing_challenges()
        |> Enum.find(&(&1.payload.id == "forced/carried/wrong"))

      {scaffold, pieces} = Challenge.to_pieces(c)
      back = Challenge.from_pieces(:elab_program, c.assay, c.label, c.seed, c.note, scaffold, pieces)
      assert back.payload == c.payload
      assert back.assay == c.assay
    end
  end
```

- [ ] **Step 2: Run the file to see which case is actually red**

Run: `mix test test/antigen/elab_dot_forcing_test.exs`
Expected: the FIRST test (no `expect_error`) PASSES immediately — every key in that payload (`id`/`src`/`expect`) is already in `@elab_keys`. The SECOND test (reject cell, `expect_error` present) FAILS, raising `ArgumentError` from `Antigen.Challenge.from_pieces/7` with message `"unknown elab payload key \"expect_error\""`. All 14 earlier tests still PASS.

- [ ] **Step 3: Add `expect_error` to the `@elab_keys` whitelist**

In `lib/antigen/challenge.ex`, extend the existing map (do not introduce a second whitelist or a fallback `String.to_atom`):

```elixir
  @elab_keys %{
    "id" => :id,
    "src" => :src,
    "transform" => :transform,
    "base_src" => :base_src,
    "variant_src" => :variant_src,
    "expect" => :expect,
    "relation" => :relation,
    "expect_error" => :expect_error
  }
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `mix test test/antigen/elab_dot_forcing_test.exs`
Expected: PASS (16 tests). If the round-trip still fails (e.g. `expect_error`'s VALUE, not just its key, is lost or mistyped), STOP and report — do not change the payload shape to dodge serialization.

- [ ] **Step 5: Gate — full Antigen directory (alone)**

Run: `mix test test/antigen/`
Expected: PASS (existing 459 + the new 16; "immune response" console lines are expected injected violations, not failures).

- [ ] **Step 6: Gate — full suite (alone)**

Run: `mix test`
Expected: PASS, 0 failures (~3195 tests). A single Antigen-seed flake that vanishes on one re-run is the documented known-flaky seed; anything reproducible is a STOP.

- [ ] **Step 7: Commit**

```bash
git add -- lib/antigen/challenge.ex test/antigen/elab_dot_forcing_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "test(antigen): elab dot-forcing corpus round-trip; vertical gate green"
```

---

## Self-review notes

- Spec §5 mandated a plan-time wiring re-grep: it found ONE point beyond the test file — `Antigen.Runner.assay_module/1`'s explicit registry (`"elab/erasure"` has an entry; `elab_erasure_test.exs:115-119` asserts it). Task 1 adds the line + the parity test. No corpus/e2e/health-gate registration exists for `elab/*` (verified at spec-review time; re-confirmed by the same grep).
- All six catalog bodies are byte-copies of landed fixtures except `forced/plain/wrong` (a one-token dot change from the landed C-b right-dot program); Task 2 Step 4 carries its dedicated contingency.
- Both `:flip` variant sources are themselves landed programs (`corrupt_dot` on carried = the landed carried-wrong fixture; `promote_use` = the landed bind_relevant fixture), so a flip failure indicts the elaborator or the wiring, never the fixture.
- Types/names consistent across tasks: `dot_forcing_challenges/0`, `catalog/0`, `source/1`, `body/1`, `metamorphic_challenges/0`; violation tags fixed in Task 1 and asserted verbatim in Tasks 1–3.
