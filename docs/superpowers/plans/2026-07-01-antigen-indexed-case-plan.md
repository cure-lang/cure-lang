# Antigen indexed-family `case` soundness — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add an Antigen "deep cut" vertical that probes the Cure kernel's dependent-`case` typing for soundness holes across four obligations, fixing any hole found and banking a permanent regression antibody.

**Architecture:** Reuse the Tier-A harness. Add one new `Antigen.Challenge` kind (`:indexed_case`) with its serialization, one generator (`Antigen.Generators.Indexed`) that hand-builds known-label GADT `case` challenges as raw Core, and one assay (`Antigen.Assays.Indexed`) that runs each challenge through `Kernel.check_def/2` and asserts accept-iff-well-typed. Each obligation is built and run one at a time; a wrongly-accepted `:ill_typed` challenge is a soundness infection — fix the kernel, add its own red→green kernel test, and bank the reproducing term as a corpus antibody.

**Tech Stack:** Elixir, ExUnit, the existing `Cure.Core.*` kernel and `Antigen.*` harness.

## Global Constraints

- Compile Cure with OTP 26–28 (already the environment).
- One `mix test` / `mix compile` process at any moment — NEVER run two concurrently (a past concurrent full-suite run caused a kernel panic). Serialize every build/test invocation.
- Ghost-written commits — NO `Co-Authored-By` / co-author trailers of any kind.
- Antibodies in `test/antigen/corpus.sexp` are never pruned once committed.
- Tests are immutable once green: make a failing test pass by changing the implementation (kernel, `Antigen.Challenge`/`Antigen.Coverage`, generator, or assay), never by weakening/skipping/deleting the test. The sole exception is a test proven to encode wrong behavior, which must be justified in the commit message before changing.
- Entry point convention elsewhere in the repo is `start/0`, but this work is pure kernel/test Elixir — no `.cure` entry points involved.
- Force-intern every new atom (kind, label, family names, ctor names, def names) in `Antigen.Challenge.@known_atoms` so `:safe` corpus replay in a fresh process can decode records.

## Reference facts (verified against the codebase — rely on these; do not re-derive)

**Core term tuples** (`lib/cure/core/term.ex`): `{:type, level}` (level 0..2), `{:var, k}` (de Bruijn, k≥0, 0 = innermost), `{:pi, dom, cod}`, `{:lam, dom, body}`, `{:app, f, a}`, `{:data, name, params, indices}`, `{:ctor, name, args}`, `{:case, scrut, motive, branches}` with `branches :: [{ctor_name, arity, body}]`, `{:global, name}`.

**`Cure.Core.Inductive`** builders/accessors (`lib/cure/core/inductive.ex`):
- `Inductive.family(name, params, indices, level)` → `%{name, params, indices, level}`; `params`/`indices` are telescopes `[{atom, Term}]`.
- `Inductive.ctor(name, args, result_indices)` → `%{name, args, result_indices, quantities}` (quantities default `:present` per arg). `args` is a telescope; `result_indices` is `[Term]`.
- `Inductive.declare(env, family, ctors)` registers a family + its ctors into an `Env`, threading `ctors` and `ctor_to_family`.
- `Inductive.get_family(env, name)`, `Inductive.get_ctor(env, name)`, `Inductive.ctor_family(env, cname)` → family atom or nil, `Inductive.ctors_of(env, fname)` → `[ctor]`.

**`Cure.Core.Env`**: `Env.empty()`, `Env.add_def(env, name, type_term, body_term)` (stores `%{name, type, body, quantities}`), `Env.get_def(env, name)`. The `Env` struct itself is the signature threaded through `Context`.

**`Cure.Core.Kernel`**: `check_def(env, name) :: :ok | {:error, term()}` — infers the def type's sort then `check`s the body against the evaluated declared type in the empty context. A def whose body is a `{:case, ...}` over a **closed** scrutinee exercises the full case path (`infer/2`'s `{:case,...}` clause → `check_motive_wf` → `check_coverage` → `check_case_branches`). `validate_certificate/2` is unrelated here.

**Case-checker internals under test** (`lib/cure/core/kernel.ex`):
- `check_coverage(sig, dname, branches)` — only `MapSet.subset?(declared, covered)` (declared = family's ctor names; covered = branch ctor names). Does NOT reject `covered` having *extra* names. Returns `{:error, :coverage}` on failure.
- `check_case_branches(ctx, sig, motive_value, branches, scrut_indices)` — for each `{cname, arity, body}`: looks up `Inductive.get_ctor(sig, cname)` in the **global** ctor namespace (not scoped to `dname`), checks arity, then `check`s `body` against the motive applied to that ctor's own computed `result_indices` ++ ctor value. Errors: `{:unknown_ctor, cname}`, `:branch_arity`, `:branch_type`.
- `branch_index_subst(ctx, result_indices, scrut_indices, arity)` — records a refinement substitution ONLY when a ctor result index is a bare `{:var, i}`; the `{_other, _}` clause silently drops compound/ground result indices.
- `check_motive_wf(ctx, motive_value, family)` — applies the motive to fresh indices + scrutinee and requires the body be a sort via `infer_type_value_sort/2` (catch-all → `{:error, :bad_motive}`). Under-applying the motive (too few `:lam` layers) raises `FunctionClauseError` in `Eval.apply/2` — AVOID that construction (see Task 5).

**Existing `:family` challenge serialization** (`lib/antigen/challenge.ex`) is the template for the new kind — pieces are `{scaffold_map, [{piece_id_string, Term}]}`; `to_pieces/1` and `from_pieces/7` clauses per kind; `Antigen.Coverage.terms_of/1` returns every embedded Term; `Antigen.Corpus.encode_record/2`+`decode_record/1` bridge pieces ↔ base64 C2 (`Cure.Core.Serialize.encode/decode`).

**Assay verdict shape** (mirror `Antigen.Assays.Positivity`): `:ok | {:violation, {:wrongly_accepted, reason}} | {:violation, {:wrongly_rejected, reason}}`.

**Replay registry** (`test/antigen/corpus_replay_test.exs` `@registry`): add `"indexed/case" => Assays.Indexed`.

---

## File structure

- **Create** `lib/antigen/generators/indexed.ex` (`Antigen.Generators.Indexed`) — one builder per obligation (both labels) + `env_of/1`.
- **Create** `lib/antigen/assays/indexed.ex` (`Antigen.Assays.Indexed`) — `run/1`.
- **Modify** `lib/antigen/challenge.ex` — new `:indexed_case` kind, `to_pieces/1` + `from_pieces/7` clauses, `@known_atoms` additions.
- **Modify** `lib/antigen/coverage.ex` — `terms_of/1` clause for `:indexed_case`.
- **Modify** `test/antigen/corpus_replay_test.exs` — register `"indexed/case" => Assays.Indexed`.
- **Create** `test/antigen/generators/indexed_test.exs` — generator self-tests (label correct by construction).
- **Create** `test/antigen/assays/indexed_test.exs` — assay accept/reject tests.
- **Modify** `test/antigen/challenge_test.exs` + `test/antigen/coverage_test.exs` — `:indexed_case` round-trip + `terms_of` coverage.
- **Create (conditionally, at fix time)** `test/cure/core/case_soundness_test.exs` — red→green kernel tests for any hole found.
- **Modify (conditionally, at fix time)** `lib/cure/core/kernel.ex` — the fix for any confirmed hole.
- **Modify (Task 6)** `test/antigen/seeds.sexp` / `test/antigen/corpus.sexp` — seeded well-typed challenges / banked antibodies.

The payload shape for `:indexed_case` (used across all tasks):

```elixir
# Challenge.payload for kind: :indexed_case
%{
  families: [ {family_map, [ctor_map]} ],  # each declared via Inductive.declare/3, in order
  def_name: atom(),                        # the global def under test
  def_type: Cure.Core.Term.t(),            # its declared type
  def_body: Cure.Core.Term.t()             # its body (contains the {:case, ...})
}
```

`env_of/1` builds the Env by folding `Inductive.declare/3` over `families` then `Env.add_def(env, def_name, def_type, def_body)`.

---

### Task 1: `:indexed_case` Challenge kind + Coverage + round-trip tests (prerequisite infra)

**Files:**
- Modify: `lib/antigen/challenge.ex`
- Modify: `lib/antigen/coverage.ex`
- Test: `test/antigen/challenge_test.exs`, `test/antigen/coverage_test.exs`

**Interfaces:**
- Produces: `Challenge` with `kind: :indexed_case`, `payload: %{families: [{family_map, [ctor_map]}], def_name, def_type, def_body}`; `Challenge.to_pieces/1` + `from_pieces/7` clauses for it; `Coverage.terms_of/1` clause returning every embedded Term.
- Consumes: existing `Inductive.family/4`, `Inductive.ctor/3`, `Challenge.new/1`.

- [ ] **Step 1: Write the failing round-trip test** in `test/antigen/challenge_test.exs`:

```elixir
test "indexed_case challenge round-trips through to_pieces/from_pieces" do
  dec = {:data, :Dec, [], []}
  fam = Cure.Core.Inductive.family(:Dec, [], [], 0)
  ctors = [Cure.Core.Inductive.ctor(:Dcoupled, [], []), Cure.Core.Inductive.ctor(:Causal, [], [])]

  payload = %{
    families: [{fam, ctors}],
    def_name: :probe,
    def_type: dec,
    def_body: {:case, {:ctor, :Causal, []}, {:lam, dec, dec},
               [{:Dcoupled, 0, {:ctor, :Causal, []}}, {:Causal, 0, {:ctor, :Dcoupled, []}}]}
  }

  c = Antigen.Challenge.new(kind: :indexed_case, assay: "indexed/case", label: :well_typed, payload: payload)
  {scaffold, pieces} = Antigen.Challenge.to_pieces(c)
  back = Antigen.Challenge.from_pieces(:indexed_case, "indexed/case", :well_typed, nil, nil, scaffold, pieces)

  assert back.kind == :indexed_case
  assert back.payload.def_name == :probe
  assert back.payload.def_type == dec
  assert back.payload.def_body == payload.def_body
  assert back.payload.families == [{fam, ctors}]
end
```

- [ ] **Step 2: Run it, verify it fails**

Run: `mix test test/antigen/challenge_test.exs -v`
Expected: FAIL (no `to_pieces`/`from_pieces` clause for `:indexed_case`; `new/1` may also reject the kind via `@type` — the struct itself won't enforce it, but `@known_atoms`/dialyzer will not fail at runtime; the real failure is `FunctionClauseError` on `to_pieces`).

- [ ] **Step 3: Add the `:indexed_case` kind + `@known_atoms`** in `lib/antigen/challenge.ex`:

Change the kind type and known atoms:

```elixir
@type kind :: :stub | :def_group | :family | :forcing_pair | :indexed_case
@type label :: :terminating | :diverging | :positive | :negative | :none | :well_typed | :ill_typed
```

Append to `@known_atoms` (keep existing entries):

```elixir
  # indexed-case vertical: kind, labels, family/ctor/def names
  :indexed_case, :well_typed, :ill_typed,
  :Dcoupled, :Foo, :MkFoo, :Box, :mk, :d, :x,
  :probe, :branch_family, :coverage_gap, :refine, :motive_wf
```

(`:Dec`, `:Causal`, `:Nat`, `:Z`, `:S` already present — do not duplicate; add only the missing ones. Verify against the current list before editing.)

- [ ] **Step 4: Add `to_pieces/1` clause** for `:indexed_case` in `lib/antigen/challenge.ex` (generalizes the `:family` clause to a list of families + a trailing def). Add a private helper `family_pieces/2` and reuse it:

```elixir
def to_pieces(%__MODULE__{kind: :indexed_case, payload: p}) do
  %{families: families, def_name: dn, def_type: dt, def_body: db} = p

  {fam_scaffolds, fam_pieces} =
    families
    |> Enum.with_index()
    |> Enum.reduce({[], []}, fn {{fam, ctors}, i}, {scaffs, pcs} ->
      {s, ps} = family_pieces(fam, ctors, "fam:#{i}")
      {scaffs ++ [s], pcs ++ ps}
    end)

  scaffold = %{"families" => fam_scaffolds, "def_name" => Atom.to_string(dn)}
  pieces = fam_pieces ++ [{"def_type", dt}, {"def_body", db}]
  {scaffold, pieces}
end

# One family's scaffold + Term pieces, keyed under `prefix` (e.g. "fam:0").
defp family_pieces(fam, ctors, prefix) do
  param_pieces = fam.params |> Enum.with_index() |> Enum.map(fn {{_n, t}, k} -> {"#{prefix}:param:#{k}", t} end)
  index_pieces = fam.indices |> Enum.with_index() |> Enum.map(fn {{_n, t}, k} -> {"#{prefix}:index:#{k}", t} end)

  ctor_pieces =
    ctors
    |> Enum.with_index()
    |> Enum.flat_map(fn {ct, j} ->
      args = ct.args |> Enum.with_index() |> Enum.map(fn {{_n, t}, k} -> {"#{prefix}:ctor:#{j}:arg:#{k}", t} end)
      ridx = ct.result_indices |> Enum.with_index() |> Enum.map(fn {t, k} -> {"#{prefix}:ctor:#{j}:ridx:#{k}", t} end)
      args ++ ridx
    end)

  ctor_scaffold =
    Enum.map(ctors, fn ct ->
      %{
        "name" => Atom.to_string(ct.name),
        "arg_names" => Enum.map(ct.args, fn {n, _t} -> Atom.to_string(n) end),
        "ridx_count" => length(ct.result_indices),
        "quantities" => Enum.map(ct.quantities, &Atom.to_string/1)
      }
    end)

  scaffold = %{
    "fam_name" => Atom.to_string(fam.name),
    "fam_level" => fam.level,
    "fam_param_names" => Enum.map(fam.params, fn {n, _t} -> Atom.to_string(n) end),
    "fam_index_names" => Enum.map(fam.indices, fn {n, _t} -> Atom.to_string(n) end),
    "ctors" => ctor_scaffold
  }

  {scaffold, param_pieces ++ index_pieces ++ ctor_pieces}
end
```

- [ ] **Step 5: Add `from_pieces/7` clause** for `:indexed_case` + a `rebuild_family/3` helper:

```elixir
def from_pieces(:indexed_case, assay, label, seed, note, scaffold, pieces) do
  pmap = Map.new(pieces)

  families =
    scaffold["families"]
    |> Enum.with_index()
    |> Enum.map(fn {fam_scaffold, i} -> rebuild_family(fam_scaffold, "fam:#{i}", pmap) end)

  payload = %{
    families: families,
    def_name: String.to_existing_atom(scaffold["def_name"]),
    def_type: Map.fetch!(pmap, "def_type"),
    def_body: Map.fetch!(pmap, "def_body")
  }

  new(kind: :indexed_case, assay: assay, label: label, payload: payload, seed: seed, note: note)
end

# Rebuild one {family, [ctor]} from its scaffold + the piece map, keyed under `prefix`.
defp rebuild_family(fam_scaffold, prefix, pmap) do
  params =
    fam_scaffold["fam_param_names"]
    |> Enum.with_index()
    |> Enum.map(fn {n, k} -> {String.to_existing_atom(n), Map.fetch!(pmap, "#{prefix}:param:#{k}")} end)

  indices =
    fam_scaffold["fam_index_names"]
    |> Enum.with_index()
    |> Enum.map(fn {n, k} -> {String.to_existing_atom(n), Map.fetch!(pmap, "#{prefix}:index:#{k}")} end)

  fam = Inductive.family(String.to_existing_atom(fam_scaffold["fam_name"]), params, indices, fam_scaffold["fam_level"])

  ctors =
    fam_scaffold["ctors"]
    |> Enum.with_index()
    |> Enum.map(fn {cs, j} ->
      args =
        cs["arg_names"]
        |> Enum.with_index()
        |> Enum.map(fn {n, k} -> {String.to_existing_atom(n), Map.fetch!(pmap, "#{prefix}:ctor:#{j}:arg:#{k}")} end)

      ridx = for k <- 0..(cs["ridx_count"] - 1)//1, do: Map.fetch!(pmap, "#{prefix}:ctor:#{j}:ridx:#{k}")
      quantities = Enum.map(cs["quantities"], &String.to_existing_atom/1)
      Inductive.ctor(String.to_existing_atom(cs["name"]), args, ridx, quantities)
    end)

  {fam, ctors}
end
```

(Note: `for k <- 0..(count-1)//1` with `count == 0` yields `[]` correctly in Elixir; nullary ctors round-trip fine.)

- [ ] **Step 6: Run the round-trip test, verify it passes**

Run: `mix test test/antigen/challenge_test.exs -v`
Expected: PASS.

- [ ] **Step 7: Write the failing `Coverage.terms_of` test** in `test/antigen/coverage_test.exs`:

```elixir
test "terms_of returns every embedded term of an indexed_case challenge" do
  dec = {:data, :Dec, [], []}
  fam = Cure.Core.Inductive.family(:Box, [], [{:d, dec}], 0)
  ctors = [Cure.Core.Inductive.ctor(:mk, [{:x, dec}], [{:var, 0}])]
  body = {:case, {:ctor, :mk, [{:ctor, :Causal, []}]}, {:lam, dec, {:lam, {:data, :Box, [], [{:var, 0}]}, dec}},
          [{:mk, 1, {:var, 0}}]}

  c = Antigen.Challenge.new(kind: :indexed_case, assay: "indexed/case", label: :well_typed,
        payload: %{families: [{fam, ctors}], def_name: :probe, def_type: dec, def_body: body})

  terms = Antigen.Coverage.terms_of(c)
  assert dec in terms           # family index type
  assert {:var, 0} in terms     # ctor result index
  assert body in terms          # def body
end
```

- [ ] **Step 8: Run it, verify it fails**

Run: `mix test test/antigen/coverage_test.exs -v`
Expected: FAIL with `FunctionClauseError` (no `terms_of` clause for `:indexed_case`).

- [ ] **Step 9: Add the `terms_of/1` clause** in `lib/antigen/coverage.ex`:

```elixir
def terms_of(%Challenge{kind: :indexed_case, payload: p}) do
  fam_terms =
    Enum.flat_map(p.families, fn {fam, ctors} ->
      Enum.map(fam.params, fn {_n, t} -> t end) ++
        Enum.map(fam.indices, fn {_n, t} -> t end) ++
        Enum.flat_map(ctors, fn ct -> Enum.map(ct.args, fn {_n, t} -> t end) ++ ct.result_indices end)
    end)

  fam_terms ++ [p.def_type, p.def_body]
end
```

- [ ] **Step 10: Run both test files, verify pass**

Run: `mix test test/antigen/challenge_test.exs test/antigen/coverage_test.exs -v`
Expected: PASS.

- [ ] **Step 11: Commit**

```bash
git add lib/antigen/challenge.ex lib/antigen/coverage.ex test/antigen/challenge_test.exs test/antigen/coverage_test.exs
git commit -m "feat(antigen): indexed_case challenge kind + serialization + coverage"
```

---

### Task 2: `Assays.Indexed` + obligation 4.1 (branch-family discipline)

**Files:**
- Create: `lib/antigen/assays/indexed.ex`
- Create: `lib/antigen/generators/indexed.ex`
- Test: `test/antigen/generators/indexed_test.exs`, `test/antigen/assays/indexed_test.exs`

**Interfaces:**
- Produces: `Antigen.Assays.Indexed.run(challenge) :: :ok | {:violation, {:wrongly_accepted | :wrongly_rejected, term}}`; `Antigen.Generators.Indexed.branch_family(:well_typed | :ill_typed)` and `env_of/1`.
- Consumes: `Kernel.check_def/2`, `Inductive.*`, `Env.*`, the `:indexed_case` Challenge from Task 1.

- [ ] **Step 1: Create the assay** `lib/antigen/assays/indexed.ex`:

```elixir
defmodule Antigen.Assays.Indexed do
  @moduledoc """
  `indexed/case` (spec 2026-07-01-antigen-indexed-case). Oracle = the known label.
  The kernel must accept a challenge's def iff it is well-typed: a `:ill_typed`
  challenge that `check_def` accepts is a **soundness infection**; a `:well_typed`
  challenge that `check_def` rejects is an incompleteness bug.
  """
  alias Antigen.{Challenge, Generators}
  alias Cure.Core.Kernel

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :indexed_case, label: label, payload: %{def_name: dn}} = c) do
    env = Generators.Indexed.env_of(c)
    verdict = Kernel.check_def(env, dn)

    case {label, verdict} do
      {:well_typed, :ok} -> :ok
      {:ill_typed, {:error, _}} -> :ok
      {:well_typed, {:error, reason}} -> {:violation, {:wrongly_rejected, {dn, reason}}}
      {:ill_typed, :ok} -> {:violation, {:wrongly_accepted, dn}}
    end
  end
end
```

- [ ] **Step 2: Create the generator** `lib/antigen/generators/indexed.ex` with `env_of/1` and the branch-family builders. Family `Dec` has ctors `Dcoupled`,`Causal`; family `Foo` has ctor `MkFoo`. The `:ill_typed` case covers both `Dec` ctors correctly then adds a foreign `MkFoo` branch (additive form — see spec §4.1):

```elixir
defmodule Antigen.Generators.Indexed do
  @moduledoc """
  Known-label indexed-family `case` generator (spec 2026-07-01-antigen-indexed-case).
  Each builder hand-constructs a GADT `case` challenge as raw Core whose
  `:well_typed`/`:ill_typed` label is correct by construction; the assay checks
  the kernel accepts iff well-typed. No elaborator, no term generator.
  """
  alias Antigen.Challenge
  alias Cure.Core.{Env, Inductive}

  @dec {:data, :Dec, [], []}

  # -- shared families --------------------------------------------------------
  defp dec_family, do: {Inductive.family(:Dec, [], [], 0),
                        [Inductive.ctor(:Dcoupled, [], []), Inductive.ctor(:Causal, [], [])]}

  defp foo_family, do: {Inductive.family(:Foo, [], [], 0), [Inductive.ctor(:MkFoo, [], [])]}

  @doc "Rebuild the Env: declare every family, then add the def under test."
  @spec env_of(Challenge.t()) :: Env.t()
  def env_of(%Challenge{payload: %{families: families, def_name: dn, def_type: dt, def_body: db}}) do
    env = Enum.reduce(families, Env.empty(), fn {fam, ctors}, e -> Inductive.declare(e, fam, ctors) end)
    Env.add_def(env, dn, dt, db)
  end

  # -- 4.1 branch-family discipline ------------------------------------------
  @doc "Branch-family obligation. `:ill_typed` adds a foreign `Foo` branch to a Dec case."
  @spec branch_family(:well_typed | :ill_typed) :: Challenge.t()
  def branch_family(:well_typed) do
    body =
      {:case, {:ctor, :Causal, []}, {:lam, @dec, @dec},
       [{:Dcoupled, 0, {:ctor, :Causal, []}}, {:Causal, 0, {:ctor, :Dcoupled, []}}]}

    challenge(:well_typed, [dec_family()], :branch_family, @dec, body,
      "well-typed Dec case, all branches from Dec")
  end

  def branch_family(:ill_typed) do
    body =
      {:case, {:ctor, :Causal, []}, {:lam, @dec, @dec},
       [
         {:Dcoupled, 0, {:ctor, :Causal, []}},
         {:Causal, 0, {:ctor, :Dcoupled, []}},
         {:MkFoo, 0, {:ctor, :Dcoupled, []}}
       ]}

    challenge(:ill_typed, [dec_family(), foo_family()], :branch_family, @dec, body,
      "ill-typed: extra branch names MkFoo, a constructor of family Foo, not Dec")
  end

  defp challenge(label, families, name, def_type, def_body, note) do
    Challenge.new(
      kind: :indexed_case,
      assay: "indexed/case",
      label: label,
      payload: %{families: families, def_name: name, def_type: def_type, def_body: def_body},
      note: note
    )
  end
end
```

- [ ] **Step 3: Write the generator self-test** (label correct by construction — the foreign branch genuinely names a non-`Dec` ctor) in `test/antigen/generators/indexed_test.exs`:

```elixir
defmodule Antigen.Generators.IndexedTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.Indexed
  alias Cure.Core.Inductive

  test "4.1 branch_family :ill_typed genuinely contains a foreign-family branch" do
    c = Indexed.branch_family(:ill_typed)
    env = Indexed.env_of(c)
    {:case, _scrut, _motive, branches} = c.payload.def_body
    branch_ctors = Enum.map(branches, fn {cn, _ar, _b} -> cn end)

    # MkFoo is present as a branch, and it really belongs to Foo, not Dec.
    assert :MkFoo in branch_ctors
    assert Inductive.ctor_family(env, :MkFoo) == :Foo
    assert Inductive.ctor_family(env, :Causal) == :Dec
    # ...and every Dec ctor is still covered (so coverage passes; the additive form).
    assert :Dcoupled in branch_ctors and :Causal in branch_ctors
  end

  test "4.1 branch_family :well_typed draws all branches from Dec" do
    c = Indexed.branch_family(:well_typed)
    env = Indexed.env_of(c)
    {:case, _s, _m, branches} = c.payload.def_body
    assert Enum.all?(branches, fn {cn, _ar, _b} -> Inductive.ctor_family(env, cn) == :Dec end)
  end
end
```

- [ ] **Step 4: Run the self-test, verify pass** (it asserts structure, not kernel behavior)

Run: `mix test test/antigen/generators/indexed_test.exs -v`
Expected: PASS (pure structural assertions).

- [ ] **Step 5: Write the assay test** in `test/antigen/assays/indexed_test.exs`:

```elixir
defmodule Antigen.Assays.IndexedTest do
  use ExUnit.Case, async: true
  alias Antigen.Assays.Indexed, as: A
  alias Antigen.Generators.Indexed, as: G

  test "4.1 well-typed branch-family case is accepted (no violation)" do
    assert :ok == A.run(G.branch_family(:well_typed))
  end

  test "4.1 ill-typed foreign-branch case must be rejected by the kernel" do
    # SOUNDNESS assertion: the kernel must NOT accept a Dec case with a Foo branch.
    # If this returns a {:wrongly_accepted, _} violation, the kernel has a hole —
    # apply the Step 8 fix, then this returns :ok.
    assert :ok == A.run(G.branch_family(:ill_typed))
  end
end
```

- [ ] **Step 6: Run the assay test — this is the probe**

Run: `mix test test/antigen/assays/indexed_test.exs -v`
Expected: One of two outcomes —
- **(sound)** both PASS → the kernel already rejects the foreign branch (likely via `:branch_type` because the motive at `MkFoo`'s indices mismatches). Record "4.1 sound" and skip to Step 9.
- **(infection)** the ill-typed test FAILS with `{:violation, {:wrongly_accepted, :branch_family}}` → confirmed hole. Proceed to Steps 7–8.

- [ ] **Step 7 (only if infection): Write the red kernel test** in `test/cure/core/case_soundness_test.exs`:

```elixir
defmodule Cure.Core.CaseSoundnessTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive, Kernel}

  @dec {:data, :Dec, [], []}

  test "a case branch naming a constructor of a foreign family is rejected" do
    env =
      Env.empty()
      |> Inductive.declare(Inductive.family(:Dec, [], [], 0),
           [Inductive.ctor(:Dcoupled, [], []), Inductive.ctor(:Causal, [], [])])
      |> Inductive.declare(Inductive.family(:Foo, [], [], 0), [Inductive.ctor(:MkFoo, [], [])])
      |> Env.add_def(:probe, @dec,
           {:case, {:ctor, :Causal, []}, {:lam, @dec, @dec},
            [{:Dcoupled, 0, {:ctor, :Causal, []}}, {:Causal, 0, {:ctor, :Dcoupled, []}},
             {:MkFoo, 0, {:ctor, :Dcoupled, []}}]})

    assert {:error, _} = Kernel.check_def(env, :probe)
  end
end
```

Run: `mix test test/cure/core/case_soundness_test.exs -v` → expected FAIL (`check_def` returns `:ok`).

- [ ] **Step 8 (only if infection): Fix `check_case_branches`** in `lib/cure/core/kernel.ex` to scope the ctor lookup to the scrutinee's family. Thread `dname` into `check_case_branches` (it is already available at the `infer` `{:case,...}` call site) and reject a foreign ctor before checking its body:

```elixir
# at the infer/2 {:case,...} call site, pass dname:
:ok <- check_case_branches(ctx, sig, dname, motive_value, branches, scrut_indices)

# updated head + a family-scoping guard, binding the ctor lookup ONCE (not
# re-fetched inside the existing body) so the nil/foreign/arity checks and the
# per-branch checking body all share the same `ctor` value:
defp check_case_branches(ctx, sig, dname, motive_value, branches, scrut_indices) do
  Enum.reduce_while(branches, :ok, fn {cname, arity, body}, :ok ->
    case Inductive.get_ctor(sig, cname) do
      nil ->
        {:halt, {:error, {:unknown_ctor, cname}}}

      ctor ->
        cond do
          Inductive.ctor_family(sig, cname) != dname ->
            {:halt, {:error, {:foreign_ctor, cname}}}

          length(ctor.args) != arity ->
            {:halt, {:error, :branch_arity}}

          true ->
            %{args: tele, result_indices: result_indices} = ctor
            # ... existing per-branch checking body, unchanged (extend_with_telescope,
            # branch_index_subst, specialize_branch_context/value, then
            # `case check(ctx_branch, body, expected) do :ok -> {:cont, :ok}; {:error, _} -> {:halt, {:error, :branch_type}} end`) ...
        end
    end
  end)
end
```

This binds `Inductive.get_ctor(sig, cname)` exactly once per branch (the original code's `%{args: tele, result_indices: result_indices} when length(tele) == arity -> ...` / `%{} -> {:halt, {:error, :branch_arity}}` two-clause match is now the explicit `length(ctor.args) != arity` guard inside the `cond`, using the already-bound `ctor`, and the family-scoping guard runs before it). Run the kernel test → PASS. Then bank the antibody: append the ill-typed challenge to `test/antigen/corpus.sexp` via a one-off `mix run`-free ExUnit helper OR (simpler) a temporary IEx-free script — but the sanctioned path is Task 6's seeding step; for now just note the antibody is due and let Task 6 write it. Re-run the assay test (Step 5) → both PASS.

- [ ] **Step 9: Full suite once**

Run: `mix test`
Expected: green (2100 existing + new tests). If 4.1 was an infection, the fix must not regress `test/cure/core/case_typing_test.exs` (which exercises legit `Dec`/`Box` cases).

- [ ] **Step 10: Commit**

```bash
git add lib/antigen/assays/indexed.ex lib/antigen/generators/indexed.ex \
        test/antigen/generators/indexed_test.exs test/antigen/assays/indexed_test.exs
# plus, if a fix was applied:
git add lib/cure/core/kernel.ex test/cure/core/case_soundness_test.exs
git commit -m "feat(antigen): indexed/case assay + branch-family obligation (4.1)"
```

---

### Task 3: obligation 4.2 (coverage exactness)

**Files:**
- Modify: `lib/antigen/generators/indexed.ex`
- Test: `test/antigen/generators/indexed_test.exs`, `test/antigen/assays/indexed_test.exs`

**Interfaces:**
- Produces: `Generators.Indexed.coverage(:well_typed | :ill_typed)`.

- [ ] **Step 1: Add the builder** in `lib/antigen/generators/indexed.ex`. A three-ctor family `Tri` (`A`,`B`,`C`, nullary); `:ill_typed` omits `C`:

```elixir
defp tri_family, do: {Inductive.family(:Tri, [], [], 0),
                      [Inductive.ctor(:A, [], []), Inductive.ctor(:B, [], []), Inductive.ctor(:C, [], [])]}

@tri {:data, :Tri, [], []}

@doc "Coverage obligation. `:ill_typed` omits a required branch (expects {:error, :coverage})."
@spec coverage(:well_typed | :ill_typed) :: Challenge.t()
def coverage(:well_typed) do
  body = {:case, {:ctor, :A, []}, {:lam, @tri, @tri},
          [{:A, 0, {:ctor, :A, []}}, {:B, 0, {:ctor, :A, []}}, {:C, 0, {:ctor, :A, []}}]}
  challenge(:well_typed, [tri_family()], :coverage_gap, @tri, body, "exhaustive Tri case")
end

def coverage(:ill_typed) do
  body = {:case, {:ctor, :A, []}, {:lam, @tri, @tri},
          [{:A, 0, {:ctor, :A, []}}, {:B, 0, {:ctor, :A, []}}]}
  challenge(:ill_typed, [tri_family()], :coverage_gap, @tri, body, "non-exhaustive: C omitted")
end
```

Add `:Tri, :A, :B, :C` to `@known_atoms` in `lib/antigen/challenge.ex`.

- [ ] **Step 2: Add self-tests** to `test/antigen/generators/indexed_test.exs`:

```elixir
test "4.2 coverage :ill_typed genuinely omits a declared ctor" do
  c = Antigen.Generators.Indexed.coverage(:ill_typed)
  env = Antigen.Generators.Indexed.env_of(c)
  declared = env |> Cure.Core.Inductive.ctors_of(:Tri) |> Enum.map(& &1.name) |> MapSet.new()
  {:case, _s, _m, branches} = c.payload.def_body
  covered = branches |> Enum.map(fn {cn, _, _} -> cn end) |> MapSet.new()
  refute MapSet.subset?(declared, covered)
end

test "4.2 coverage :well_typed covers every declared ctor" do
  c = Antigen.Generators.Indexed.coverage(:well_typed)
  env = Antigen.Generators.Indexed.env_of(c)
  declared = env |> Cure.Core.Inductive.ctors_of(:Tri) |> Enum.map(& &1.name) |> MapSet.new()
  {:case, _s, _m, branches} = c.payload.def_body
  covered = branches |> Enum.map(fn {cn, _, _} -> cn end) |> MapSet.new()
  assert MapSet.subset?(declared, covered)
end
```

- [ ] **Step 3: Run self-tests, verify pass**

Run: `mix test test/antigen/generators/indexed_test.exs -v`
Expected: PASS.

- [ ] **Step 4: Add assay tests** to `test/antigen/assays/indexed_test.exs`:

```elixir
test "4.2 exhaustive Tri case is accepted" do
  assert :ok == Antigen.Assays.Indexed.run(Antigen.Generators.Indexed.coverage(:well_typed))
end

test "4.2 non-exhaustive Tri case must be rejected" do
  assert :ok == Antigen.Assays.Indexed.run(Antigen.Generators.Indexed.coverage(:ill_typed))
end
```

- [ ] **Step 5: Run assay tests — the probe**

Run: `mix test test/antigen/assays/indexed_test.exs -v`
Expected: both PASS (existing `check_coverage` already returns `{:error, :coverage}` for the omitted branch — confirmed by `case_typing_test.exs`'s "non-exhaustive case" test). This obligation is expected **sound**; if the ill-typed test fails, follow the Task 2 triage pattern (red kernel test + fix + antibody-due note).

- [ ] **Step 6: Full suite once + commit**

Run: `mix test` → green.
```bash
git add lib/antigen/generators/indexed.ex lib/antigen/challenge.ex \
        test/antigen/generators/indexed_test.exs test/antigen/assays/indexed_test.exs
git commit -m "feat(antigen): coverage-exactness obligation (4.2)"
```

---

### Task 4: obligation 4.3 (compound-index refinement — the crown jewel)

**Files:**
- Modify: `lib/antigen/generators/indexed.ex`
- Test: `test/antigen/generators/indexed_test.exs`, `test/antigen/assays/indexed_test.exs`

**Interfaces:**
- Produces: `Generators.Indexed.refinement(:well_typed | :ill_typed)`.

**Background (from the Box/mk fixture in `case_typing_test.exs`):** `Box(d : Dec)` with `mk : (x : Dec) -> Box(x)` (result index `[{:var, 0}]`). A `case` on `mk Causal : Box(Causal)` with motive `λ(d:Dec). λ(bx : Box d). <T>` refines `d := Causal` in the `mk` branch. The `mk` branch body is checked against the motive applied to the ctor's own result index (`x`, the field) — this is the refinement path. `branch_index_subst` records the substitution because `mk`'s result index is `{:var, 0}` (a bare var). To exercise the *compound-index* drop, use a family whose ctor result index is a **non-variable computed term**.

**Construction.** Family `Ix(n : Dec)` (index is a `Dec`); ctor `wrap : (p : Dec) -> Ix(Causal)` — result index is the *ground* term `{:ctor, :Causal, []}`, NOT a bare var, so `branch_index_subst` drops it.

**First attempt, traced and rejected (recorded so it is not re-tried):** a def whose declared return type is `Eq Dec n Causal`, scrutinee `ix : Ix n` (variable index `n`), motive `λn.λix. Eq Dec n Causal`, body `refl` in the `wrap` branch. Tracing `check_case_branches`: the per-branch `expected` type is computed as `apply_motive(motive_value, s_values ++ [ctor_value])`, where `s_values` are evaluated **directly from the ctor's own declared result-index term** (`{:ctor, :Causal, []}` → the value `Causal`) — via ordinary function application, *not* via `branch_index_subst`. So `expected` already reduces to `Eq Dec Causal Causal` regardless of whether `branch_index_subst` records anything, and `refl` discharges it either way. **This construction never touches the drop** — it would be accepted by both the current kernel and a hypothetically-fixed one, giving zero signal. The bug only manifests in `specialize_branch_context`/`specialize_branch_value`, which refine *other, pre-existing context bindings* whose types mention the scrutinee's original (unrefined) index variable — not the motive's own direct application to the ctor's computed index. A probe must include such an external binding.

**Corrected construction.** Add a Π-bound hypothesis `h : Ix n` *before* the scrutinee, and require the `wrap` branch to produce a value of type `Ix Causal` — the SAME family, at the ground index the ctor forces, but re-using `h`, which was declared (outside the case, before any refinement) at the unrefined index `Ix n`. Concretely:

```
def_type = Π(n : Dec). Π(h : Ix n). Π(ix : Ix n). Ix n
motive   = λ(n' : Dec). λ(ix' : Ix n'). Ix n'        -- "the same family, at whichever index came in"
body     = λ(n : Dec). λ(h : Ix n). λ(ix : Ix n). case ix of { wrap p -> h }
```

Tracing this: the **overall** case-expression's inferred type is `apply_motive(motive_value, scrut_indices ++ [scrut_value])` = `Ix(n)` (using the scrutinee's own, unrefined index value `n` — this matches the declared codomain `Ix n` trivially, independent of the bug). But the **per-branch** `expected` type (inside `check_case_branches`, for the `wrap` branch) is `apply_motive(motive_value, s_values ++ [ctor_value])` = `Ix(Causal)` (using the ctor's own computed index, `Causal`). Meanwhile `h`'s type, as recorded in `ctx_branch.types`, is whatever it was declared as **before** the case — `Ix(n)` — because `branch_index_subst` only fires for a bare-`{:var, i}` result index, and `wrap`'s result index is the ground `{:ctor, :Causal, []}`, so it is dropped and `specialize_branch_context` is a no-op. So `check(ctx_branch, h, Ix(Causal))` falls to the generic `check` clause, infers `h`'s (unrefined) type `Ix(n)`, and finds it **not convertible** to `Ix(Causal)` (`n` is a free/neutral variable, not the concrete value `Causal`) — `{:error, :branch_type}`.

A **sound, refinement-complete** kernel — one that also used the `wrap` ctor's *ground* result index to refine `h`'s type from `Ix(n)` to `Ix(Causal)` inside the branch (the natural generalization of `branch_index_subst` to non-bare-var, i.e. ground, result indices) — would accept this: `h`, once known (inside this branch) to have index `Causal`, literally has the required type, and reusing it as the branch body is valid. So: **a sound kernel accepts; the current, dropping kernel rejects.** That is an **incompleteness** manifestation (rejection, not acceptance) — matching the same "report, don't silently patch" resolution as before, but now via a construction that actually depends on the drop.

- `:well_typed` — the `Π(h : Ix n)...case ix of {wrap p -> h}` term above. A sound, refinement-complete kernel accepts it; the current kernel is expected to wrongly reject it (incompleteness, reported not fixed per spec §5 step 4 / success criterion 5).
- `:ill_typed` — an independent soundness probe, unrelated to the refinement gap: a `wrap` branch body of the wrong type outright (e.g. body `{:type, 0}` where a `Dec` is expected) — must be rejected with `:branch_type` regardless. This keeps the obligation bidirectional with a real soundness assertion.

- [ ] **Step 1: Add the builders** in `lib/antigen/generators/indexed.ex`:

```elixir
defp ix_family, do: {Inductive.family(:Ix, [], [{:n, @dec}], 0),
                     [Inductive.ctor(:wrap, [{:p, @dec}], [{:ctor, :Causal, []}])]}

@doc """
Compound-index refinement obligation. The `wrap` ctor's result index is the
GROUND term `Causal` (not a bare var), so `branch_index_subst` drops the
refinement equation.
"""
@spec refinement(:well_typed | :ill_typed) :: Challenge.t()
def refinement(:well_typed) do
  # Refinement-complete but genuinely legal: `h`, bound before the case at the
  # unrefined type `Ix n`, is reused in the `wrap` branch where the required
  # type is `Ix Causal`. Only the dropped ground-index equation (n := Causal)
  # bridges them. A sound, refinement-complete kernel accepts this by refining
  # h's context type; the current kernel drops the equation and is expected to
  # reject (incompleteness, reported not fixed).
  ix_of_0 = {:data, :Ix, [], [{:var, 0}]}
  ix_of_1 = {:data, :Ix, [], [{:var, 1}]}
  ix_of_2 = {:data, :Ix, [], [{:var, 2}]}

  def_type = {:pi, @dec, {:pi, ix_of_0, {:pi, ix_of_1, ix_of_2}}}
  motive = {:lam, @dec, {:lam, ix_of_0, ix_of_1}}
  body = {:lam, @dec, {:lam, ix_of_0, {:lam, ix_of_1, {:case, {:var, 0}, motive, [{:wrap, 1, {:var, 2}}]}}}}

  challenge(:well_typed, [dec_family(), ix_family()], :refine, def_type, body,
    "refinement-complete: reusing h : Ix n as Ix Causal in the wrap branch needs n:=Causal")
end

def refinement(:ill_typed) do
  # soundness probe independent of the refinement gap: wrong-typed branch body.
  motive = {:lam, @dec, {:lam, {:data, :Ix, [], [{:var, 0}]}, @dec}}
  body = {:case, {:ctor, :wrap, [{:ctor, :Dcoupled, []}]}, motive, [{:wrap, 1, {:type, 0}}]}
  challenge(:ill_typed, [dec_family(), ix_family()], :refine, @dec, body,
    "ill-typed: wrap branch body {:type,0} where Dec is expected")
end
```

Add `:Ix, :wrap, :n, :p` to `@known_atoms`.

De Bruijn check for `:well_typed` (counting from the point of use, 0 = innermost): `def_type` = `Π(n:Dec). Π(h:Ix n). Π(ix:Ix n). Ix n` — in `ix_of_0` (h's domain), only `n` is bound so far, so `{:var,0}` = n; in `ix_of_1` (ix's domain), `h` has added one more binder, so `n` is now `{:var,1}`; in `ix_of_2` (the final codomain), `ix` has added yet another binder, so `n` is now `{:var,2}`. `motive` mirrors this with its own two lambdas (`n'` then `ix'`), fully self-contained (no free variables into the outer context — it is evaluated once via `Eval.eval(motive, Context.env(ctx))` and applied twice by the kernel, so it must not depend on the surrounding binders). In `body`, before the `case`, the binder order (innermost first) is `ix`(0), `h`(1), `n`(2); the `wrap` branch adds one new binder (`p`, arity 1), shifting everything else by 1, so `h` — referenced inside the branch — is `{:var, 2}` (1 + 1), not `{:var, 1}`.

- [ ] **Step 2: Add self-tests** to `test/antigen/generators/indexed_test.exs` asserting the structural facts (the `wrap` result index is a non-variable ground term; `h`'s declared domain genuinely needs refining to match the branch's required output; the ill-typed body is `{:type, 0}`):

```elixir
test "4.3 refinement family's wrap ctor has a NON-variable (ground) result index, and h needs it" do
  c = Antigen.Generators.Indexed.refinement(:well_typed)
  env = Antigen.Generators.Indexed.env_of(c)
  [ridx] = Cure.Core.Inductive.get_ctor(env, :wrap).result_indices
  refute match?({:var, _}, ridx)          # it's {:ctor, :Causal, []}, so refinement is DROPPED
  assert ridx == {:ctor, :Causal, []}

  # def_type: Π(n:Dec). Π(h:Ix n). Π(ix:Ix n). Ix n — h's declared domain is
  # `Ix n` (the SAME shape the wrap branch requires, `Ix _`), differing only in
  # which index term fills the hole; only the dropped n:=Causal equation could
  # ever bridge `Ix n` (h's declared type) to `Ix Causal` (the branch's goal).
  {:pi, _dec, {:pi, h_dom, {:pi, _ix_dom, _cod}}} = c.payload.def_type
  assert h_dom == {:data, :Ix, [], [{:var, 0}]}
end

test "4.3 ill-typed refinement body is a deliberately wrong-typed term" do
  c = Antigen.Generators.Indexed.refinement(:ill_typed)
  {:case, _s, _m, [{:wrap, 1, body}]} = c.payload.def_body
  assert body == {:type, 0}
end
```

- [ ] **Step 3: Run self-tests, verify pass**

Run: `mix test test/antigen/generators/indexed_test.exs -v`
Expected: PASS.

- [ ] **Step 4: Add assay tests** to `test/antigen/assays/indexed_test.exs`. The ill-typed (wrong-body) case is a hard soundness assertion; the well-typed (refinement-complete) case is expected to expose incompleteness:

```elixir
test "4.3 ill-typed wrap-branch (wrong body type) must be rejected" do
  assert :ok == Antigen.Assays.Indexed.run(Antigen.Generators.Indexed.refinement(:ill_typed))
end

test "4.3 refinement-complete well-typed case — records kernel's verdict" do
  # A sound + refinement-complete kernel returns :ok (h, refined from Ix n to
  # Ix Causal, matches the wrap branch's required type). The current kernel
  # drops the ground-index equation, so it is expected to return
  # {:violation, {:wrongly_rejected, _}} — an INCOMPLETENESS finding (not
  # unsoundness). Either way, assert the result is NOT a soundness infection
  # ({:wrongly_accepted, _} would be the alarming case).
  result = Antigen.Assays.Indexed.run(Antigen.Generators.Indexed.refinement(:well_typed))
  refute match?({:violation, {:wrongly_accepted, _}}, result)
end
```

- [ ] **Step 5: Run assay tests — the crown-jewel probe**

Run: `mix test test/antigen/assays/indexed_test.exs -v`
Expected:
- The ill-typed (wrong-body) test PASSES (kernel rejects `{:type,0}` where `Dec` expected, via `:branch_type`).
- The refinement-complete test PASSES the `refute wrongly_accepted` assertion. Its underlying `run` is expected to return `{:violation, {:wrongly_rejected, {:refine, :branch_type}}}` (h's unrefined `Ix n` fails conversion against the branch's required `Ix Causal`) — that is the **incompleteness finding**: record it in the Stage-5 report for the operator (spec success criterion 5). Do NOT change the kernel to fix incompleteness without operator sign-off.
- If, unexpectedly, the ill-typed test fails with `{:wrongly_accepted, _}`, that is a genuine soundness infection — follow the Task 2 triage (red kernel test + fix + antibody-due note).

- [ ] **Step 6: Full suite once + commit**

Run: `mix test` → green.
```bash
git add lib/antigen/generators/indexed.ex lib/antigen/challenge.ex \
        test/antigen/generators/indexed_test.exs test/antigen/assays/indexed_test.exs
git commit -m "feat(antigen): compound-index refinement obligation (4.3)"
```

---

### Task 5: obligation 4.4 (motive well-formedness)

**Files:**
- Modify: `lib/antigen/generators/indexed.ex`
- Test: `test/antigen/generators/indexed_test.exs`, `test/antigen/assays/indexed_test.exs`

**Interfaces:**
- Produces: `Generators.Indexed.motive_wf(:well_typed | :ill_typed)`.

**Construction (spec §4.4):** the `:ill_typed` motive must be caught by `infer_type_value_sort/2`'s catch-all as `{:error, :bad_motive}` — use an **over-applied** motive (more `:lam` layers than `index_arity + 1`, leaving a residual `{:vlam,...}` after `apply_motive`), NOT an under-applied one (which crashes `Eval.apply/2`). `Dec` has index arity 0, so a well-formed motive is `λ(x : Dec). <sort>` (1 layer). An over-applied motive is `λ(x : Dec). λ(y : Dec). Dec` (2 layers).

- [ ] **Step 1: Add the builders** in `lib/antigen/generators/indexed.ex`:

```elixir
@doc """
Motive well-formedness obligation. `:ill_typed` over-applies the motive (an extra
`:lam` layer beyond index_arity+1), so `apply_motive` leaves a residual `{:vlam,...}`
which `infer_type_value_sort` rejects as {:error, :bad_motive}. (Do NOT under-apply
— that crashes Eval.apply; see spec §4.4.)
"""
@spec motive_wf(:well_typed | :ill_typed) :: Challenge.t()
def motive_wf(:well_typed) do
  body = {:case, {:ctor, :Causal, []}, {:lam, @dec, @dec},
          [{:Dcoupled, 0, {:ctor, :Causal, []}}, {:Causal, 0, {:ctor, :Dcoupled, []}}]}
  challenge(:well_typed, [dec_family()], :motive_wf, @dec, body, "well-formed motive λx:Dec. Dec")
end

def motive_wf(:ill_typed) do
  over = {:lam, @dec, {:lam, @dec, @dec}}   # one lam too many for a 0-index family
  body = {:case, {:ctor, :Causal, []}, over,
          [{:Dcoupled, 0, {:ctor, :Causal, []}}, {:Causal, 0, {:ctor, :Dcoupled, []}}]}
  # def_type is irrelevant to the motive check; use @dec (check fails before it matters).
  challenge(:ill_typed, [dec_family()], :motive_wf, @dec, body, "over-applied motive → :bad_motive")
end
```

- [ ] **Step 2: Add self-tests** to `test/antigen/generators/indexed_test.exs` (structural: the ill-typed motive has one more `:lam` layer than the well-typed one):

```elixir
test "4.4 ill-typed motive has an extra lambda layer (over-applied)" do
  good = Antigen.Generators.Indexed.motive_wf(:well_typed)
  bad = Antigen.Generators.Indexed.motive_wf(:ill_typed)
  {:case, _s, {:lam, _, good_inner}, _} = good.payload.def_body
  {:case, _s2, {:lam, _, bad_inner}, _} = bad.payload.def_body
  # good_inner is a plain type; bad_inner is itself another lambda (the extra layer).
  refute match?({:lam, _, _}, good_inner)
  assert match?({:lam, _, _}, bad_inner)
end
```

- [ ] **Step 3: Run self-tests, verify pass**

Run: `mix test test/antigen/generators/indexed_test.exs -v`
Expected: PASS.

- [ ] **Step 4: Add assay tests** to `test/antigen/assays/indexed_test.exs`:

```elixir
test "4.4 well-formed motive is accepted" do
  assert :ok == Antigen.Assays.Indexed.run(Antigen.Generators.Indexed.motive_wf(:well_typed))
end

test "4.4 over-applied (malformed) motive must be rejected" do
  assert :ok == Antigen.Assays.Indexed.run(Antigen.Generators.Indexed.motive_wf(:ill_typed))
end
```

- [ ] **Step 5: Run assay tests — the probe**

Run: `mix test test/antigen/assays/indexed_test.exs -v`
Expected: both PASS (existing `check_motive_wf` → `infer_type_value_sort` catch-all returns `{:error, :bad_motive}` for the residual `{:vlam,...}`). Expected **sound**. If the ill-typed test raises instead of returning a violation (i.e. `check_def` crashed), that is the `Eval.apply` robustness gap — note it as a follow-up hardening item for the report (spec §4.4), and adjust the construction to ensure over-application (not under-application) was used. If it returns `{:wrongly_accepted, _}`, follow Task 2 triage.

- [ ] **Step 6: Full suite once + commit**

Run: `mix test` → green.
```bash
git add lib/antigen/generators/indexed.ex lib/antigen/challenge.ex \
        test/antigen/generators/indexed_test.exs test/antigen/assays/indexed_test.exs
git commit -m "feat(antigen): motive-wellformedness obligation (4.4)"
```

---

### Task 6: Replay wiring + corpus/seed banking + final coverage

**Files:**
- Modify: `test/antigen/corpus_replay_test.exs`
- Modify: `test/antigen/seeds.sexp` (append well-typed seeds)
- Modify: `test/antigen/corpus.sexp` (append any antibodies from Tasks 2–5, if infections were found)
- Test: `test/antigen/corpus_replay_test.exs` (existing invariant test now covers `indexed/case`)

**Interfaces:**
- Consumes: `Antigen.Corpus.encode_record/1`, the four `Generators.Indexed` builders, `Assays.Indexed`.

- [ ] **Step 1: Register the assay** in `test/antigen/corpus_replay_test.exs` `@registry`:

```elixir
@registry %{
  "stub" => Assays.Stub,
  "totality/diverging" => Assays.Totality,
  "totality/terminating" => Assays.Totality,
  "positivity" => Assays.Positivity,
  "reflexivity" => Assays.Reflexivity,
  "indexed/case" => Assays.Indexed
}
```

- [ ] **Step 2: Write a seeding test** that appends each well-typed challenge (and each ill-typed challenge that the kernel correctly rejects — those are valid "known-good behavior" seeds) to `seeds.sexp`, and any confirmed antibody to `corpus.sexp`, using `Antigen.Corpus.encode_record/1`. Guard with existence so it is idempotent (do not duplicate a record whose `key=` already present). Add to `test/antigen/corpus_replay_test.exs` OR a small `test/antigen/indexed_seed_test.exs`:

```elixir
defmodule Antigen.IndexedSeedTest do
  use ExUnit.Case, async: false
  alias Antigen.{Corpus, Generators.Indexed, Assays}

  @seeds "test/antigen/seeds.sexp"

  @challenges [
    Indexed.branch_family(:well_typed), Indexed.branch_family(:ill_typed),
    Indexed.coverage(:well_typed), Indexed.coverage(:ill_typed),
    Indexed.refinement(:well_typed), Indexed.refinement(:ill_typed),
    Indexed.motive_wf(:well_typed), Indexed.motive_wf(:ill_typed)
  ]

  test "indexed/case seeds are present in seeds.sexp and all replay :ok" do
    existing = if File.exists?(@seeds), do: File.read!(@seeds), else: ""

    lines =
      @challenges
      |> Enum.filter(fn c -> Assays.Indexed.run(c) == :ok end)   # only seed known-good behavior
      |> Enum.map(&Corpus.encode_record/1)
      |> Enum.reject(fn line -> key_present?(existing, line) end)

    if lines != [], do: File.write!(@seeds, existing <> Enum.join(lines, "\n") <> "\n")

    # every indexed/case seed now decodes + replays to :ok
    # (Runner.replay/2 returns `%{entry: challenge, verdict: verdict}` maps — the
    # assay id lives on `entry`, e.g. `r.entry.assay`, NOT a top-level `r.assay`.)
    reg = %{"indexed/case" => Assays.Indexed}
    results = Antigen.Runner.replay([@seeds], Map.merge(reg, %{"stub" => Assays.Stub}))
    indexed = Enum.filter(results, fn r -> r.entry.assay == "indexed/case" end)
    refute indexed == []
    assert Enum.all?(indexed, fn r -> r.verdict == :ok end)
  end

  defp key_present?(existing, line) do
    key = line |> String.split("\t") |> Enum.find(&String.starts_with?(&1, "key=")) 
    key != nil and String.contains?(existing, key)
  end
end
```

(The `refinement(:well_typed)` challenge is intentionally excluded from the seed list if it triggers the incompleteness rejection — the `Assays.Indexed.run(c) == :ok` filter handles that automatically: only challenges the kernel currently handles correctly get seeded, so replay stays green. Note the exclusion in the Stage-5 report.)

- [ ] **Step 3: Run the seeding test once** (it writes the seeds file)

Run: `mix test test/antigen/indexed_seed_test.exs -v`
Expected: PASS; `git status` shows `test/antigen/seeds.sexp` modified.

- [ ] **Step 4: If any Task 2–5 infection produced an antibody**, append its ill-typed challenge to `corpus.sexp` the same way (a parallel guarded write for the *confirmed-infection* challenge, which post-fix replays `:ok`). If no infections were found across 2–5, `corpus.sexp` is unchanged and this step is a no-op.

- [ ] **Step 5: Full suite once**

Run: `mix test`
Expected: green — including `corpus_replay_test.exs`'s "every committed entry satisfies its assay invariant" now exercising the new `indexed/case` seeds, and the "decode without error" / "git-clean" replay tests. Confirm `git status` is clean after the run (replay must not mutate the committed files).

- [ ] **Step 6: Commit**

```bash
git add test/antigen/corpus_replay_test.exs test/antigen/seeds.sexp test/antigen/indexed_seed_test.exs
# plus test/antigen/corpus.sexp if antibodies were banked
git commit -m "feat(antigen): register indexed/case assay + seed corpus/seeds"
```

---

## Self-review

**Spec coverage:** §3 architecture (new kind + generator + assay) → Tasks 1,2. §4.1 branch-family → Task 2. §4.2 coverage → Task 3. §4.3 compound-index refinement → Task 4 (with the label-inversion subtlety resolved: the refinement gap manifests as *incompleteness* not unsoundness, so 4.3 carries a separate wrong-body soundness probe). §4.4 motive-wf → Task 5 (over-application form per spec). §5 per-obligation loop (self-test → assay → run → triage → suite → commit) → the step structure of Tasks 2–5. §6 corpus/seed → Task 6. §8 testing (challenge/coverage round-trip, generator self-tests, assay tests, kernel red→green, replay) → Tasks 1–6. §9 success criteria → all tasks; criterion 5 (incompleteness reported, not patched) → Task 4 Step 5 + Stage-5 report. §10 constraints → Global Constraints.

**Placeholder scan:** every code step has concrete Core terms and complete function bodies. The only conditionals are the "if infection" fix branches (Tasks 2–5 triage), which are inherent to the spec's catch-then-fix loop and carry the full fix recipe (Task 2 Step 8) — not placeholders.

**Type consistency:** `Generators.Indexed.env_of/1`, `branch_family/1`, `coverage/1`, `refinement/1`, `motive_wf/1`, `challenge/6` (private) used consistently; `Assays.Indexed.run/1` verdict shape matches `Assays.Positivity`; payload shape `%{families, def_name, def_type, def_body}` identical across generator, assay, `to_pieces`/`from_pieces`, `terms_of`; `Inductive.family/4`, `ctor/3`, `declare/3`, `ctor_family/2`, `ctors_of/2`, `get_ctor/2` used with the arities from the reference sheet; `Challenge.new/1` / `from_pieces/7` / `to_pieces/1` arities match `lib/antigen/challenge.ex`.
