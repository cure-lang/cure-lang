# Antigen Eq/rewrite vertical — implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to
> implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax.

**Goal:** Ship the `rewrite` Antigen vertical (assay key `rewrite/eq`) — a
known-label soundness battery over the kernel's `{:eq}`/`{:refl}`/`{:rewrite}`
surface — as the regression net for the ② case-refinement unifier.

**Architecture:** Mirror the indexed-case vertical exactly:
`Antigen.Generators.Rewrite` hand-builds Core `Challenge`s (kind `:rewrite_eq`,
payload `%{families, def_name, def_type, def_body}`) whose `:well_typed`/
`:ill_typed` label is correct by construction; `Antigen.Assays.Rewrite` runs the
def through `Cure.Core.Kernel.check_def/2` and reports an infection iff
acceptance ≠ label. Wiring is additive (Challenge kind, Coverage clause, two
registries).

**Tech stack:** Elixir; `Cure.Core.{Kernel,Inductive,Env}`; `Antigen.*`.

## Global Constraints

- Known-label by construction; NO term generator, NO external oracle.
- Kernel edits ONLY on a confirmed soundness hole, and then red-green + bank a
  never-pruned antibody in `test/antigen/corpus.sexp` (indexed-case 4.1 protocol).
  Absent a hole, this vertical is **zero** TCB change.
- `corpus.sexp` / `seeds.sexp` are append-only, never pruned.
- Nothing under `Antigen.Generators.*` / `Antigen.Assays.*` may import StreamData
  (enforced by `test/antigen/architecture_test.exs`).
- Tests are immutable once green (fix generator/assay/kernel, never the test),
  except a test proven to encode wrong behavior (state why first).
- **One `mix` build/test run at a time** — never concurrent (a past concurrent
  full-suite run caused a kernel panic).
- Compile with OTP 26–28. Ghost-writer commits (no co-sign).
- Build and verify **one obligation at a time**, order 4.1 → 4.2 → 4.3 → 4.4;
  full suite once + commit before the next.
- `Generators.Rewrite` gets **no `gen/0`** and is **not** added to
  `Mix.Tasks.Antigen`'s `default_gen/0` — it mirrors `Generators.Indexed`,
  which ships the exact same way (a fixed, exhaustively-enumerable known-label
  battery banked via a dedicated seed test, not a population wired into the
  `mix antigen` explorer sweep). Do not add this wiring by analogy with
  verticals that do have `gen/0`.

---

### Task 1: Scaffolding + wiring + Obligation 4.1 (Eq formation)

**Files:**
- Create: `lib/antigen/generators/rewrite.ex`
- Create: `lib/antigen/assays/rewrite.ex`
- Modify: `lib/antigen/challenge.ex` (`@known_atoms`, `to_pieces`, `from_pieces`)
- Modify: `lib/antigen/coverage.ex` (`terms_of/1`)
- Modify: `lib/antigen/runner.ex` (`assay_module/1`)
- Modify: `test/antigen/corpus_replay_test.exs` (`@registry`)
- Create: `test/antigen/generators/rewrite_test.exs`
- Create: `test/antigen/assays/rewrite_test.exs`

**Interfaces:**
- Produces: `Antigen.Generators.Rewrite.{env_of/1, eq_formation/1}`,
  `Antigen.Assays.Rewrite.run/1`, Challenge kind `:rewrite_eq`.
- Consumes: `Cure.Core.{Inductive,Env,Kernel}`, `Antigen.Challenge`.

- [ ] **Step 1: Write the generator self-test (red).**

`test/antigen/generators/rewrite_test.exs`:

```elixir
defmodule Antigen.Generators.RewriteTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.Rewrite
  alias Cure.Core.Kernel

  defp checks?(c), do: Kernel.check_def(Rewrite.env_of(c), c.payload.def_name)

  test "4.1 eq_formation: well-typed accepted, ill-typed rejected, labels correct" do
    wt = Rewrite.eq_formation(:well_typed)
    it = Rewrite.eq_formation(:ill_typed)
    assert wt.label == :well_typed and it.label == :ill_typed
    assert wt.kind == :rewrite_eq and wt.assay == "rewrite/eq"
    assert :ok == checks?(wt)
    assert {:error, _} = checks?(it)
  end
end
```

- [ ] **Step 2: Run it to confirm it fails** (module missing).

Run: `mix test test/antigen/generators/rewrite_test.exs`
Expected: FAIL (`Antigen.Generators.Rewrite` undefined).

- [ ] **Step 3: Create `Antigen.Generators.Rewrite`** with the shared shape
duplicated from `Generators.Indexed` (those helpers are `defp` — this is the
established duplication pattern), plus the 4.1 builder.

```elixir
defmodule Antigen.Generators.Rewrite do
  @moduledoc """
  Known-label `Eq`/`refl`/`rewrite` generator (spec 2026-07-02-antigen-eq-rewrite).
  Each builder hand-constructs a Core def whose `:well_typed`/`:ill_typed` label
  is correct by construction; `Assays.Rewrite` checks the kernel accepts iff
  well-typed. No elaborator, no term generator.
  """
  alias Antigen.Challenge
  alias Cure.Core.{Env, Inductive}

  @dec {:data, :Dec, [], []}
  @causal {:ctor, :Causal, []}
  @dcoupled {:ctor, :Dcoupled, []}

  # -- shared families (duplicated from Generators.Indexed; those are defp) ----
  defp dec_family,
    do: {Inductive.family(:Dec, [], [], 0),
         [Inductive.ctor(:Dcoupled, [], []), Inductive.ctor(:Causal, [], [])]}

  defp foo_family, do: {Inductive.family(:Foo, [], [], 0), [Inductive.ctor(:MkFoo, [], [])]}

  # P : Dec -> Type, an empty (constructor-free) index family; `P a` is a valid
  # type whose inhabitants are only ever hypotheses (Pi domains). Used as the
  # rewrite motive family in 4.3/4.4.
  defp p_family, do: {Inductive.family(:P, [], [{:n, @dec}], 0), []}

  @doc "Rebuild the Env: declare every family, then add the def under test."
  @spec env_of(Challenge.t()) :: Env.t()
  def env_of(%Challenge{payload: %{families: families, def_name: dn, def_type: dt, def_body: db}}) do
    env = Enum.reduce(families, Env.empty(), fn {fam, ctors}, e -> Inductive.declare(e, fam, ctors) end)
    Env.add_def(env, dn, dt, db)
  end

  # -- 4.1 Eq formation -------------------------------------------------------
  @doc """
  Eq-formation obligation. The `Eq` type sits in a Pi domain so check_def's
  type-formation pass exercises `infer({:eq,…})` on its endpoints.
  """
  @spec eq_formation(:well_typed | :ill_typed) :: Challenge.t()
  def eq_formation(:well_typed) do
    eq = {:eq, @dec, @causal, @dcoupled}
    challenge(:well_typed, [dec_family()], :eq_formation,
      {:pi, eq, @dec}, {:lam, eq, @causal},
      "Eq Dec Causal Dcoupled — both endpoints : Dec")
  end

  def eq_formation(:ill_typed) do
    eq = {:eq, @dec, @causal, {:ctor, :MkFoo, []}}
    challenge(:ill_typed, [dec_family(), foo_family()], :eq_formation,
      {:pi, eq, @dec}, {:lam, eq, @causal},
      "ill-typed: Eq Dec Causal MkFoo — MkFoo : Foo, not Dec")
  end

  defp challenge(label, families, name, def_type, def_body, note) do
    Challenge.new(
      kind: :rewrite_eq,
      assay: "rewrite/eq",
      label: label,
      payload: %{families: families, def_name: name, def_type: def_type, def_body: def_body},
      note: note
    )
  end
end
```

- [ ] **Step 4: Run the generator test.**

Run: `mix test test/antigen/generators/rewrite_test.exs`
Expected: PASS. **If the `:ill_typed` case shows `:ok`** (check_def does not
sort-check the Pi domain), the label is not being exercised — rework the term so
the ill-typed `Eq` sits in a definitely-checked position (e.g. make the body
`{:refl, endpoint}` so `infer({:refl,…})`→`infer({:eq,…})` runs). Adjusting an
unproven term to encode the intended label is permitted (pre-green).

- [ ] **Step 5: Write the assay self-test (red).**

`test/antigen/assays/rewrite_test.exs`:

```elixir
defmodule Antigen.Assays.RewriteTest do
  use ExUnit.Case, async: true
  alias Antigen.{Assays, Generators}

  test "run/1: :ok on correctly-labelled, {:violation,_} on mislabelled" do
    wt = Generators.Rewrite.eq_formation(:well_typed)
    it = Generators.Rewrite.eq_formation(:ill_typed)
    assert :ok == Assays.Rewrite.run(wt)
    assert :ok == Assays.Rewrite.run(it)
    # deliberately mislabel: an ill-typed def wearing a :well_typed label must infect
    mislabelled = %{it | label: :well_typed}
    assert {:violation, {:wrongly_rejected, _}} = Assays.Rewrite.run(mislabelled)
  end
end
```

- [ ] **Step 6: Run it, confirm failure** (assay missing).

Run: `mix test test/antigen/assays/rewrite_test.exs` → FAIL.

- [ ] **Step 7: Create `Antigen.Assays.Rewrite`** (mirror `Assays.Indexed`):

```elixir
defmodule Antigen.Assays.Rewrite do
  @moduledoc """
  `rewrite/eq` (spec 2026-07-02-antigen-eq-rewrite). Oracle = the known label.
  The kernel must accept a challenge's def iff it is `:well_typed`.
  """
  alias Antigen.{Challenge, Generators}
  alias Cure.Core.Kernel

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :rewrite_eq, label: label, payload: %{def_name: dn}} = c) do
    env = Generators.Rewrite.env_of(c)

    case {label, Kernel.check_def(env, dn)} do
      {:well_typed, :ok} -> :ok
      {:ill_typed, {:error, _}} -> :ok
      {:well_typed, {:error, reason}} -> {:violation, {:wrongly_rejected, {dn, reason}}}
      {:ill_typed, :ok} -> {:violation, {:wrongly_accepted, dn}}
    end
  end
end
```

- [ ] **Step 8: Run the assay test.** Expected: PASS.

- [ ] **Step 9: Wire `:rewrite_eq` into Challenge / Coverage / registries.**

`lib/antigen/challenge.ex`:
- Add `:rewrite_eq` to the `@type kind` union and to `@known_atoms` (kinds group).
- **Also add every new atom this vertical introduces that `decode_record` /
  `Serialize.decode` will reconstruct via `String.to_existing_atom` on a cold
  process** (mirror the existing "indexed-case vertical" `@known_atoms` block,
  which lists its def-names and family/ctor names alongside its kind — not just
  `:indexed_case` itself; `Antigen.Corpus.decode_record/1`'s own comment
  documents exactly this hazard: "a replay in a process that has not yet
  loaded `Challenge`... fails to decode"). Concretely add: the four def_name
  atoms `:eq_formation, :refl_typing, :rewrite_premise, :transport_type`, and
  the new family name `:P` (introduced by `p_family`). If the Task 3 fallback
  ever introduces a dummy constructor (see Task 3 Step 4), add its name too.
  Skipping this step will not surface until a fresh-process replay (e.g.
  `corpus_replay_test.exs` run without the generator already loaded) raises
  `ArgumentError` decoding a committed record — verify by grepping the final
  `@known_atoms` list for all of the above before Task 1's commit.
- The payload is identical to `:indexed_case`, so share the bodies. Change the
  two `to_pieces`/`from_pieces` `:indexed_case` heads to also match `:rewrite_eq`:

```elixir
# to_pieces: match both kinds (identical payload)
def to_pieces(%__MODULE__{kind: k, payload: p}) when k in [:indexed_case, :rewrite_eq] do
  # ... existing indexed_case body unchanged ...
end
```

```elixir
# from_pieces: add a rewrite_eq head that reuses the indexed_case logic
def from_pieces(:rewrite_eq, assay, label, seed, note, scaffold, pieces),
  do: from_pieces(:indexed_case, assay, label, seed, note, scaffold, pieces)
        |> Map.put(:kind, :rewrite_eq)
```

(The `Map.put(:kind, :rewrite_eq)` on the result is valid as written: `new/1`
returns a plain `%Challenge{}` struct, and `Map.put/3` on a struct for an
already-declared field key — `:kind` is declared via `defstruct` — is
ordinary, idiomatic Elixir; it returns an updated struct of the same type. No
inline `new(kind: :rewrite_eq, …)` rewrite is needed.)

`lib/antigen/coverage.ex` — add a `terms_of` clause mirroring `:indexed_case`:

```elixir
def terms_of(%Challenge{kind: k, payload: p}) when k in [:indexed_case, :rewrite_eq] do
  # ... existing indexed_case body ...
end
```

(Collapse the existing `:indexed_case` clause into this guard.)

`lib/antigen/runner.ex` — add before the fallthrough:

```elixir
defp assay_module("rewrite/eq"), do: Antigen.Assays.Rewrite
```

`test/antigen/corpus_replay_test.exs` — add to `@registry`:

```elixir
"rewrite/eq" => Assays.Rewrite,
```

- [ ] **Step 10: Write the wiring test** (append to `assays/rewrite_test.exs`):

```elixir
  test "rewrite_eq round-trips through Challenge encode/decode and Coverage" do
    c = Generators.Rewrite.eq_formation(:well_typed)
    {scaffold, pieces} = Antigen.Challenge.to_pieces(c)
    rebuilt = Antigen.Challenge.from_pieces(:rewrite_eq, c.assay, c.label, nil, c.note, scaffold, pieces)
    assert rebuilt.kind == :rewrite_eq
    assert :ok == Assays.Rewrite.run(rebuilt)
    assert is_list(Antigen.Coverage.terms_of(c)) and Antigen.Coverage.terms_of(c) != []
  end
```

- [ ] **Step 11: Run the vertical's tests + the full antigen suite.**

Run: `mix test test/antigen/`
Expected: PASS (existing green + the new tests). Triage any 4.1 infection per
§5 of the spec.

- [ ] **Step 12: Commit.**

```bash
git add lib/antigen/generators/rewrite.ex lib/antigen/assays/rewrite.ex \
        lib/antigen/challenge.ex lib/antigen/coverage.ex lib/antigen/runner.ex \
        test/antigen/corpus_replay_test.exs test/antigen/generators/rewrite_test.exs \
        test/antigen/assays/rewrite_test.exs
git commit -m "feat(antigen): rewrite/eq vertical scaffolding + Eq-formation obligation"
```

---

### Task 2: Obligation 4.2 (refl typing + two-conjunct guard)

**Files:** Modify `lib/antigen/generators/rewrite.ex`; extend
`test/antigen/generators/rewrite_test.exs`.

**Interfaces:** Produces `Rewrite.refl_typing/1` with variants
`:base | :redex | :conjunct1_violation | :conjunct2_violation`.

- [ ] **Step 1: Write the self-test (red).** Append:

```elixir
  test "4.2 refl_typing: base + redex well-typed; both conjunct violations rejected" do
    for v <- [:base, :redex] do
      assert :ok == checks?(Rewrite.refl_typing(v)), "variant #{v} should typecheck"
    end

    for v <- [:conjunct1_violation, :conjunct2_violation] do
      c = Rewrite.refl_typing(v)
      assert c.label == :ill_typed
      assert {:error, _} = checks?(c), "variant #{v} should be rejected"
    end
  end
```

- [ ] **Step 2: Run, confirm failure** (`refl_typing` undefined).

- [ ] **Step 3: Implement `refl_typing/1`.** The four variants probe
`check({:refl, a}, {:veq, ty, av, bv})` (kernel.ex:260), which requires
`conv(av,bv)` (conjunct 1) AND `conv(eval a, av)` (conjunct 2).

```elixir
  # -- 4.2 refl typing + reflexive-conversion guard ---------------------------
  @spec refl_typing(:base | :redex | :conjunct1_violation | :conjunct2_violation) :: Challenge.t()
  # base: refl Causal : Eq Dec Causal Causal, in a def that checks the refl.
  def refl_typing(:base) do
    eq = {:eq, @dec, @causal, @causal}
    challenge(:well_typed, [dec_family()], :refl_typing, eq, {:refl, @causal},
      "refl Causal : Eq Dec Causal Causal")
  end

  # redex: endpoint is a redex that normalizes to Causal — conv is up-to-nf.
  # (λx:Dec. x) Causal ≡ Causal, so refl Causal : Eq Dec Causal ((λx.x) Causal).
  def refl_typing(:redex) do
    redex = {:app, {:lam, @dec, {:var, 0}}, @causal}
    eq = {:eq, @dec, @causal, redex}
    challenge(:well_typed, [dec_family()], :refl_typing, eq, {:refl, @causal},
      "refl Causal against Eq Dec Causal ((λx.x) Causal) — conv up-to-normalization")
  end

  # conjunct-1 violation: endpoints not convertible (Causal vs Dcoupled), a = Causal.
  def refl_typing(:conjunct1_violation) do
    eq = {:eq, @dec, @causal, @dcoupled}
    challenge(:ill_typed, [dec_family()], :refl_typing, eq, {:refl, @causal},
      "ill-typed: refl Causal : Eq Dec Causal Dcoupled — endpoints not convertible (conjunct 1)")
  end

  # conjunct-2 violation: endpoints equal to each other (Dcoupled,Dcoupled) so
  # conjunct 1 holds, but refl's subject `a`=Causal is not convertible to them.
  def refl_typing(:conjunct2_violation) do
    eq = {:eq, @dec, @dcoupled, @dcoupled}
    challenge(:ill_typed, [dec_family()], :refl_typing, eq, {:refl, @causal},
      "ill-typed: refl Causal : Eq Dec Dcoupled Dcoupled — conjunct 1 holds, subject≠endpoints (conjunct 2)")
  end
```

Note: these use the `Eq` type as the def_type directly and `{:refl, …}` as the
body, so `check_def` checks the refl against the Eq (`check({:refl,…},{:veq,…})`).
Confirm a bare `Eq` is a legal `def_type` (a def whose type is a proposition);
if `check_def` demands the def_type be a *type* first, that is satisfied — `Eq …`
infers to `{:vtype, _}`. If the base variant is unexpectedly rejected, wrap as
`{:pi, eq, @dec}` / `{:lam, eq, …}` around a hypothesis of the Eq (pre-green
term adjustment).

- [ ] **Step 4: Run the test.** Expected: PASS. Triage infections per §5.
- [ ] **Step 5: Full antigen suite** (`mix test test/antigen/`). Expected: PASS.
- [ ] **Step 6: Commit** `feat(antigen): rewrite/eq refl-typing obligation (both conjuncts)`.

---

### Task 3: Obligation 4.3 (rewrite premise discipline)

**Files:** Modify `lib/antigen/generators/rewrite.ex`; extend the generator test.

**Interfaces:** Produces `Rewrite.rewrite_premise/1` with variants
`:well_typed | :proof_not_eq | :body_mismatch`.

- [ ] **Step 1: Self-test (red).** Append:

```elixir
  test "4.3 rewrite_premise: well-typed accepted; proof-not-eq and body-mismatch rejected" do
    assert :ok == checks?(Rewrite.rewrite_premise(:well_typed))
    for v <- [:proof_not_eq, :body_mismatch] do
      c = Rewrite.rewrite_premise(v)
      assert c.label == :ill_typed
      assert {:error, _} = checks?(c), "variant #{v} should be rejected"
    end
  end
```

- [ ] **Step 2: Run, confirm failure.**

- [ ] **Step 3: Implement `rewrite_premise/1`.** Motive `M = λx:Dec. P x`; the
equality proof is a hypothesis `p : Eq Dec Causal Dcoupled` (Causal≠Dcoupled has
no ground proof, so it must be assumed). de Bruijn under `[p, h]`: `h`=var0, `p`=var1.

```elixir
  # -- 4.3 rewrite premise discipline -----------------------------------------
  @p_causal {:data, :P, [], [{:ctor, :Causal, []}]}
  @p_dcoupled {:data, :P, [], [{:ctor, :Dcoupled, []}]}
  @motive {:lam, @dec, {:data, :P, [], [{:var, 0}]}}
  @eq_cd {:eq, @dec, {:ctor, :Causal, []}, {:ctor, :Dcoupled, []}}

  @spec rewrite_premise(:well_typed | :proof_not_eq | :body_mismatch) :: Challenge.t()
  # def : Π(p:Eq Dec Causal Dcoupled). Π(h:P Causal). P Dcoupled
  #     = λp.λh. rewrite p (λx.P x) h
  def rewrite_premise(:well_typed) do
    dt = {:pi, @eq_cd, {:pi, @p_causal, @p_dcoupled}}
    body = {:lam, @eq_cd, {:lam, @p_causal, {:rewrite, {:var, 1}, @motive, {:var, 0}}}}
    challenge(:well_typed, [dec_family(), p_family()], :rewrite_premise, dt, body,
      "rewrite p (λx.P x) h : P Dcoupled from h : P Causal")
  end

  # proof is `h : P Causal`, not an equality → ensure_eq rejects.
  def rewrite_premise(:proof_not_eq) do
    dt = {:pi, @p_causal, @p_causal}
    body = {:lam, @p_causal, {:rewrite, {:var, 0}, @motive, {:var, 0}}}
    challenge(:ill_typed, [dec_family(), p_family()], :rewrite_premise, dt, body,
      "ill-typed: rewrite proof is h : P Causal, not an equality")
  end

  # proof IS a genuine equality (so we reach the body check), but the body
  # `Causal : Dec` does not check at M a = P Causal → :rewrite_premise.
  def rewrite_premise(:body_mismatch) do
    dt = {:pi, @eq_cd, @p_dcoupled}
    body = {:lam, @eq_cd, {:rewrite, {:var, 0}, @motive, {:ctor, :Causal, []}}}
    challenge(:ill_typed, [dec_family(), p_family()], :rewrite_premise, dt, body,
      "ill-typed: rewrite body Causal:Dec, not P Causal → :rewrite_premise")
  end
```

- [ ] **Step 4: Run the test.** Expected: PASS. `p_family`'s empty ctor list is
NOT at risk of `check_family`/positivity rejection here: `env_of/1` builds the
env via `Inductive.declare/2,3` alone, which is bare registration (stores the
family/ctor maps) and never calls `Kernel.check_family/2` or
`Inductive.positive?/2` — those are invoked only by the elaborator
(`lib/cure/elab/declarations.ex`) and by the dedicated `Antigen.Generators/
Assays.Positivity` vertical, neither of which is in this pipeline. So no
fallback is needed on that front. (If, for some other reason, `p_family` needs
a ctor later, add `mkP : P(Causal)` — it would not affect the obligations,
since `h` stays a hypothesis — but the check_family/positivity concern itself
does not apply.) Triage per §5.
- [ ] **Step 5: Full antigen suite.** Expected: PASS.
- [ ] **Step 6: Commit** `feat(antigen): rewrite/eq premise-discipline obligation`.

---

### Task 4: Obligation 4.4 (transport result-type + refl coherence)

**Files:** Modify `lib/antigen/generators/rewrite.ex`; extend the generator test.

**Interfaces:** Produces `Rewrite.transport_type/1` with variants
`:transport_correct | :refl_coherence | :left_at_source`.

- [ ] **Step 1: Self-test (red).** Append:

```elixir
  test "4.4 transport_type: transport-correct + refl-coherence accepted; left-at-source rejected" do
    for v <- [:transport_correct, :refl_coherence] do
      assert :ok == checks?(Rewrite.transport_type(v)), "variant #{v} should typecheck"
    end

    lat = Rewrite.transport_type(:left_at_source)
    assert lat.label == :ill_typed
    assert {:error, _} = checks?(lat)
  end
```

- [ ] **Step 2: Run, confirm failure.**

- [ ] **Step 3: Implement `transport_type/1`.**

```elixir
  # -- 4.4 transport result-type correctness ----------------------------------
  @spec transport_type(:transport_correct | :refl_coherence | :left_at_source) :: Challenge.t()
  # identical body to 4.3 well-typed; the point is the DECLARED codomain P Dcoupled.
  def transport_type(:transport_correct) do
    dt = {:pi, @eq_cd, {:pi, @p_causal, @p_dcoupled}}
    body = {:lam, @eq_cd, {:lam, @p_causal, {:rewrite, {:var, 1}, @motive, {:var, 0}}}}
    challenge(:well_typed, [dec_family(), p_family()], :transport_type, dt, body,
      "declared P Dcoupled; rewrite moves the type to M b")
  end

  # refl coherence: rewrite (refl Causal) (λx.P x) h : P Causal (b = a).
  def transport_type(:refl_coherence) do
    dt = {:pi, @p_causal, @p_causal}
    body = {:lam, @p_causal, {:rewrite, {:refl, {:ctor, :Causal, []}}, @motive, {:var, 0}}}
    challenge(:well_typed, [dec_family(), p_family()], :transport_type, dt, body,
      "rewrite (refl Causal) M h : P Causal — vacuous transport")
  end

  # left-at-source: SAME transport body but declared codomain P Causal (= M a).
  # The kernel must reject: the rewrite's type is P Dcoupled ≢ P Causal.
  def transport_type(:left_at_source) do
    dt = {:pi, @eq_cd, {:pi, @p_causal, @p_causal}}
    body = {:lam, @eq_cd, {:lam, @p_causal, {:rewrite, {:var, 1}, @motive, {:var, 0}}}}
    challenge(:ill_typed, [dec_family(), p_family()], :transport_type, dt, body,
      "ill-typed: declared P Causal but rewrite yields P Dcoupled — accepting = no transport")
  end
```

- [ ] **Step 4: Run the test.** Expected: PASS. A `:left_at_source` acceptance is
a **soundness infection** (the kernel failed to move the type): fix red-green in
the kernel and bank an antibody per §5 (unlikely — the existing conv check should
reject; but this is exactly the obligation's purpose). Triage per §5.
- [ ] **Step 5: Full antigen suite.** Expected: PASS.
- [ ] **Step 6: Commit** `feat(antigen): rewrite/eq transport-result-type obligation`.

---

### Task 5: Seed banking + full-suite verification

**Files:** Create `test/antigen/rewrite_seed_test.exs`; final full-suite run.

**Interfaces:** Consumes every `Generators.Rewrite` builder; banks seeds and
replays them.

- [ ] **Step 1: Write the seed/replay test** (mirror
`test/antigen/indexed_seed_test.exs`). Enumerate all variants, run each through
the assay, bank correctly-handled challenges into `seeds.sexp` (and any
`:wrongly_accepted` into `corpus.sexp`), and replay both stores against a local
registry to prove every banked record replays to `:ok`.

```elixir
defmodule Antigen.RewriteSeedTest do
  use ExUnit.Case, async: false
  alias Antigen.{Generators.Rewrite, Assays, Corpus, Runner}

  @variants [
    {:eq_formation, [:well_typed, :ill_typed]},
    {:refl_typing, [:base, :redex, :conjunct1_violation, :conjunct2_violation]},
    {:rewrite_premise, [:well_typed, :proof_not_eq, :body_mismatch]},
    {:transport_type, [:transport_correct, :refl_coherence, :left_at_source]}
  ]

  @registry %{"rewrite/eq" => Assays.Rewrite}

  test "every rewrite/eq obligation is correctly handled and its seed replays" do
    challenges = for {f, vs} <- @variants, v <- vs, do: apply(Rewrite, f, [v])

    for c <- challenges do
      assert :ok == Assays.Rewrite.run(c),
        "assay must be :ok on correctly-labelled #{c.note}"
    end

    # Bank each as a coverage-deduped seed, then replay statically.
    paths = Corpus.append_seeds(challenges)   # PLACEHOLDER — see note below
    for path <- List.wrap(paths) do
      for {_c, res} <- Runner.replay([path], @registry), do: assert res == :ok
    end
  end
end
```

**This whole block from the `# Bank each...` comment down is illustrative
pseudocode, not code to transcribe as-is — two concrete, confirmed mismatches
against the real APIs (verified by reading `lib/antigen/corpus.ex` and
`lib/antigen/runner.ex` directly):**
1. `Corpus.append_seeds/1` does not exist. The real `Corpus.append/3` takes a
   fixed path, a challenge, and a dedup key, and returns `:appended |
   :duplicate` — it does not discover or return "paths". The real pattern
   (`indexed_seed_test.exs`) declares `@seeds`/`@corpus` as fixed module
   attributes and calls `Corpus.append(@seeds, c, Corpus.dedup_key(c, :seed))`
   (or `:antibody`) once per challenge.
2. `Runner.replay/2` returns a list of **maps** `%{entry: c, verdict: v}`, not
   `{c, res}` 2-tuples — `for {_c, res} <- Runner.replay(...)` would silently
   match zero elements (a `for` generator skips non-matching elements rather
   than raising) and the `assert` would never run, a vacuous-pass bug. The real
   pattern filters/asserts over `r.entry`/`r.verdict` (see
   `indexed_seed_test.exs`'s `Enum.filter(results, fn r -> match?(...) end)` /
   `Enum.all?(indexed, fn r -> r.verdict == :ok end)`).

**Before writing:** read `test/antigen/indexed_seed_test.exs` in full and port
its exact `Corpus`/`Runner` usage (fixed `@seeds`/`@corpus` attributes,
per-challenge `Corpus.append/3` + `Corpus.dedup_key/2`, `Runner.replay/2`'s
map-shaped results filtered/asserted via `Enum.filter`/`Enum.all?`) — do not
invent an API and do not trust any line above except the `@variants` table and
the top-level `assert :ok == Assays.Rewrite.run(c)` loop, which are correct as
written.

- [ ] **Step 2: Run the seed test.** Expected: PASS; `seeds.sexp` grows
(append-only). Confirm no seed is pruned.
- [ ] **Step 3: Full suite ONCE.**

Run: `mix test`
Expected: baseline (2158) + all new rewrite/eq tests, **zero failures**. If any
pre-existing test regresses, fix the implementation (never the test).

- [ ] **Step 4: Commit** `test(antigen): bank + statically replay rewrite/eq seeds`.

---

## Self-Review

**Spec coverage:** §3 surface facts → Tasks 1–4 term designs; §4.1→T1, §4.2→T2
(both conjuncts), §4.3→T3 (proof-not-eq + body-mismatch, proof genuine per the
load-bearing note), §4.4→T4 (transport-correct + refl-coherence + left-at-source);
§5 triage → each task's "triage per §5" step; §6 wiring (Challenge/Coverage/two
registries/no-explorer) → T1 Step 9 + T5 seed test (no `default_gen` entry); §7
per-obligation TDD loop + immutability → task ordering + Global Constraints; §8
invariants → Global Constraints; §9 net role → out of code scope.

**Placeholder scan:** T5's "Bank each..." block is the only deliberately-illustrative
code — flagged with two confirmed mismatches against the real `Corpus`/`Runner`
APIs (`Corpus.append_seeds/1` doesn't exist; `Runner.replay/2`'s map-shaped
results don't match the shown `{_c, res}` tuple destructure) and an explicit
instruction to port `indexed_seed_test.exs`'s exact usage instead of trusting
either line. Every other step has concrete, verified code, path, and command.

**Type consistency:** `challenge/6`, `env_of/1`, `check_def/2`, `Challenge.new/1`
kind `:rewrite_eq` + assay `"rewrite/eq"` used identically across all tasks;
`p_family`/`@motive`/`@eq_cd`/`@p_causal`/`@p_dcoupled` defined in T3 and reused
in T4 (T4 depends on T3 having introduced them — noted).
