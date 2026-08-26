# Type-Directed Overload Resolution (Ph1) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Let several functions share a name and have the call site pick the right one from the argument types (Idris2 elaborate-and-prune), for both same-module and cross-module overload sets, greening `test/cure/elab/type_directed_overload_test.exs`.

**Architecture:** An **overload discriminator** — a `~<ordinal>` suffix on the base name — threads through four existing single-winner touch points so a set of same-name members has distinct identities end-to-end. Members register under discriminated canonical keys (`Mod#plus~0`, `Mod#plus~1`) instead of colliding on `Mod#plus`; the pre-elaboration duplicate gate is relaxed and a precise overlap check runs after signature elaboration (where telescopes exist); the bare-name resolver gains a candidate-gathering primitive; the applied term-position call site prunes candidates by inferred argument type; and emission derives a distinct BEAM function name from each discriminated key for free (both def-site and call-site go through `Name.base`, so they agree). Size-one sets are byte-identical to today.

**Tech Stack:** Elixir; Cure elaborator (`lib/cure/elab/*`); ExUnit. No `lib/cure/core/*` (kernel/TCB) change.

## Global Constraints

- **ZERO TCB.** Do not modify `lib/cure/core/*`. This is surface + elaborator + emit only. No new Core former, no Antigen antibody.
- **Overload separator is `~` (tilde), a non-identifier byte.** Cure identifiers are `[A-Za-z0-9_]`; `~` cannot appear in any user-writable name, so a discriminated emitted name (`:"plus~0"`) can never collide with a user function named `plus_0` or similar. Do not use `_` or any identifier-legal delimiter.
- **Size-one inertness.** A name with a single definition MUST keep its exact current canonical key (`Mod#plus`, no discriminator) and its exact current BEAM name. No golden/emit test may move for non-overloaded code.
- **Alignment target: Idris2.** Argument-type-directed disambiguation, first-order only. Not Agda/Lean (the TCB-binding alignment law does not apply; nothing in `core/*` changes).
- **Out of scope, do not build:** argument labels; the `+`/operator ergonomic (no `+`→overload desugar, no new special case in `elaborate_expr_typed`); return-type-directed resolution; sibling-module (one-file multi-`mod`) overload sets (`check_no_sibling_collision` at `program.ex:189` stays untouched); extending elaborate-and-prune to bare *unapplied* references or the dependent-index applied path (`applied_def_key`) — those are documented Ph1 limitations.
- **Tests are behavioral and immutable.** Assert through public entry points (`Cure.Compiler.compile_and_load`, `Cure.Elab.Program.elaborate`) — returned values, runtime results, error tuples — never private helper state or call counts. A later task may not weaken/skip/delete an earlier task's test; the sole exception is the taxonomy migration in Task 4 (the spec deliberately redefines an error code) and proving a test encoded wrong behavior.
- **One build/test run at a time.** Never launch concurrent suites.

---

## File Structure

- `lib/cure/elab/name.ex` — **modify.** Owns canonical-name spelling. Add the overload discriminator helpers (`overload_key/2`, `overload_member?/1`, `overload_base/1`). Central so registration, resolution, and emit share one convention.
- `lib/cure/elab/resolution.ex` — **modify.** Add `overload_candidates/2` (gather all providers of a bare name, `prefer_direct` applied); generalize the three suffix matchers (`resolve_canonical_suffix`, `shadowed_origin`, `ambiguous_modules`) to also see `#name~<ord>` keys.
- `lib/cure/elab/overload.ex` — **create.** The prune engine: given a gathered candidate list and inferred argument types, return `{:ok, winner_key}` | `{:no_matching_overload, …}` | `{:ambiguous_overload, …}`. Pure over `Env` + already-elaborated argument types; no side effects. Keeps `elaborator.ex` from growing another tangled cond arm.
- `lib/cure/elab/type_conv.ex` — **create.** `Cure.Elab.TypeConv.convertible?/3`: the ONE shared telescope/type-convertibility check, a thin wrapper over the existing normal-form/unify facility (confirm which during Task 4). Both `check_overload_legality/1` (Task 4, `program.ex`) and `Cure.Elab.Overload.resolve/4` (Task 5, `overload.ex`) call this public function — neither defines its own private copy. Public and named identically everywhere it is referenced so the two tasks cannot drift into duplicate implementations.
- `lib/cure/elab/declarations.ex` — **modify.** `function_signature/2` builds a discriminated bare name from an `:overload_ordinal` meta key so `Env.add_def`'s `owned_name` qualification yields `Mod#plus~0`.
- `lib/cure/elab/program.ex` — **modify.** Relax `check_no_duplicate_defs`; add the ordinal-annotation pre-pass and the post-signature `check_overload_legality` (emits `:overlapping_overload`).
- `lib/cure/elab/elaborator.ex` — **modify.** In `elaborate_named_call/5`, add the overload-dispatch clause that calls `Cure.Elab.Overload` and routes the winner through the existing `elaborate_global_app`.
- `test/cure/elab/type_directed_overload_test.exs` — **modify** (delete `@tag :skip`; add cross-module, no-match, ambiguous, overlap, inertness cases).
- `test/cure/elab/name_overload_test.exs`, `test/cure/elab/resolution_overload_test.exs`, `test/cure/elab/overload_test.exs` — **create** (unit coverage for the three new library pieces).
- Existing tests migrated in Task 4: `test/cure/elab/dup_def_test.exs`, `test/cure/elab/imported_module_dup_test.exs`, `test/cure/elab/global_namespace_soundness_test.exs`, `test/cure/elab/cross_module_names_test.exs`.

**Interfaces produced (referenced by later tasks):**
- `Cure.Elab.Name.overload_key(base_key :: atom, ordinal :: non_neg_integer) :: atom` — appends `~<ordinal>` to the base part of a (bare or qualified) key: `:plus` → `:"plus~0"`, `:"Mod#plus"` → `:"Mod#plus~0"`.
- `Cure.Elab.Name.overload_member?(key :: atom | String.t) :: boolean` — true iff the base part contains `~`.
- `Cure.Elab.Name.overload_base(key :: atom) :: String.t` — the base with any `~<ord>` stripped: `:"Mod#plus~0"` → `"plus"`, `:"Mod#plus"` → `"plus"`.
- `Cure.Elab.Resolution.overload_candidates(env, bare :: atom) :: [atom]` — every in-scope canonical def key providing `bare` (local + `prefer_direct` imports), including all members of an overload set. `[]` when unknown; `[key]` for a single provider; `[k0, k1, …]` for a set.
- `Cure.Elab.Overload.resolve(env, bare :: atom, arg_types :: [Cure.Core.Term.t()], candidates :: [atom]) :: {:ok, atom} | {:error, {:no_matching_overload, atom, [term]}} | {:error, {:ambiguous_overload, atom, [String.t()]}}`.
- `Cure.Elab.TypeConv.convertible?(env, t1 :: Cure.Core.Term.t(), t2 :: Cure.Core.Term.t()) :: boolean` — the ONE shared type-convertibility check; introduced in Task 4, consumed by both Task 4's `check_overload_legality/1` and Task 5's `Overload.resolve/4`.

---

### Task 1: Overload discriminator helpers in `Cure.Elab.Name`

**Files:**
- Modify: `lib/cure/elab/name.ex`
- Test: `test/cure/elab/name_overload_test.exs` (create)

**Interfaces:**
- Produces: `overload_key/2`, `overload_member?/1`, `overload_base/1` (signatures above).
- Consumes: existing `split/1`, `base/1`, `qualify/2`.

Design note: `base/1` already returns the full base after the first `#` (`base(:"Mod#plus~0") == "plus~0"`). Keep that — emit relies on it to produce the *distinct* BEAM name `:"plus~0"`. `overload_base/1` is the *stripped* form used only for resolution grouping.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/elab/name_overload_test.exs
defmodule Cure.Elab.NameOverloadTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Name

  test "overload_key appends ~ordinal to a bare base" do
    assert Name.overload_key(:plus, 0) == :"plus~0"
    assert Name.overload_key(:plus, 1) == :"plus~1"
  end

  test "overload_key appends ~ordinal to the base of a qualified key" do
    assert Name.overload_key(:"Mod#plus", 0) == :"Mod#plus~0"
  end

  test "overload_member? detects the discriminator, ignores plain keys" do
    assert Name.overload_member?(:"Mod#plus~0")
    assert Name.overload_member?(:"plus~2")
    refute Name.overload_member?(:"Mod#plus")
    refute Name.overload_member?(:plus)
  end

  test "overload_base strips the discriminator to the plain base name" do
    assert Name.overload_base(:"Mod#plus~0") == "plus"
    assert Name.overload_base(:"plus~1") == "plus"
    assert Name.overload_base(:"Mod#plus") == "plus"
    assert Name.overload_base(:plus) == "plus"
  end

  test "base/1 still returns the full discriminated base (emit distinctness)" do
    assert Name.base(:"Mod#plus~0") == "plus~0"
    assert Name.owner(:"Mod#plus~0") == "Mod"
  end
end
```

- [ ] **Step 2: Run it, verify it fails**

Run: `mix test test/cure/elab/name_overload_test.exs`
Expected: FAIL — `overload_key/2` undefined.

- [ ] **Step 3: Implement**

```elixir
# lib/cure/elab/name.ex — add near the top with the other module attributes
@overload_separator "~"

# ... and add these public functions (e.g. after base/1):

@doc "Append an overload discriminator (`~<ordinal>`) to the base of a key."
@spec overload_key(atom() | String.t(), non_neg_integer()) :: atom()
def overload_key(base_key, ordinal) when is_integer(ordinal) and ordinal >= 0 do
  String.to_atom(to_string_name(base_key) <> @overload_separator <> Integer.to_string(ordinal))
end

@doc "Whether a key's base part carries an overload discriminator."
@spec overload_member?(atom() | String.t()) :: boolean()
def overload_member?(key) do
  key |> base() |> to_string() |> String.contains?(@overload_separator)
end

@doc "The base name with any `~<ordinal>` overload discriminator removed."
@spec overload_base(atom() | String.t()) :: String.t()
def overload_base(key) do
  key |> base() |> to_string() |> String.split(@overload_separator, parts: 2) |> hd()
end

defp to_string_name(k) when is_atom(k), do: Atom.to_string(k)
defp to_string_name(k) when is_binary(k), do: k
```

Note: `overload_base/1` calls `base/1` first, so it operates on the base part only and never mistakes a `~` that (cannot) appear in an owner. Guard against a `nil` base: `base/1` returns the original bare name for a bare atom, so `to_string(nil)` never occurs for atom/binary inputs.

- [ ] **Step 4: Run it, verify it passes**

Run: `mix test test/cure/elab/name_overload_test.exs`
Expected: PASS (5 tests).

- [ ] **Step 5: Commit**

```bash
git add lib/cure/elab/name.ex test/cure/elab/name_overload_test.exs
git commit -m "feat(elab): overload discriminator helpers in Cure.Elab.Name"
```

---

### Task 2: Candidate gathering + overload-aware suffix matching in `Cure.Elab.Resolution`

**Files:**
- Modify: `lib/cure/elab/resolution.ex`
- Test: `test/cure/elab/resolution_overload_test.exs` (create)

**Interfaces:**
- Produces: `overload_candidates/2`.
- Consumes: `Cure.Elab.Name.overload_base/1` (Task 1); existing `prefer_direct/2`, `Env` fields `defs`/`ctors`/`families`/`module_owner`/`import_modules`.

Two changes. (a) The three suffix matchers filter keys by the literal `String.ends_with?(s, "#plus")`; a discriminated key `Mod#plus~0` does not end with `#plus`, so add an OR on the infix `"#plus~"` (cheap, no `split`). (b) A new `overload_candidates/2` returns *all* providers (not collapsed to one/ambiguous) for the applied call site to prune.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/elab/resolution_overload_test.exs
defmodule Cure.Elab.ResolutionOverloadTest do
  use ExUnit.Case, async: true
  alias Cure.Core.Env
  alias Cure.Elab.Resolution

  # A minimal env with two overload members of `plus` owned by "M" and a single
  # `solo`, plus one import "M".
  defp env_with_overloads do
    %{Env.empty() | module_owner: "M", import_modules: MapSet.new(["M"])}
    |> put_def(:"M#plus~0")
    |> put_def(:"M#plus~1")
    |> put_def(:"M#solo")
  end

  defp put_def(env, key) do
    %{env | defs: Map.put(env.defs, key, %{name: key, type: {:type, 0}, body: {:hole, "x"}, quantities: nil})}
  end

  test "overload_candidates returns every member of a set, most-specific-owner first" do
    env = env_with_overloads()
    assert Enum.sort(Resolution.overload_candidates(env, :plus)) == [:"M#plus~0", :"M#plus~1"]
  end

  test "overload_candidates returns the single provider for a non-overloaded name" do
    assert Resolution.overload_candidates(env_with_overloads(), :solo) == [:"M#solo"]
  end

  test "overload_candidates returns [] for an unknown name" do
    assert Resolution.overload_candidates(env_with_overloads(), :nope) == []
  end

  test "ambiguous_modules still finds an overloaded name's owner (structural recovery)" do
    # A bare unapplied reference must still surface an actionable owner list,
    # never a silent :none. (Same owner twice collapses to one entry.)
    assert Resolution.ambiguous_modules(env_with_overloads(), :plus) == ["M"]
  end
end
```

- [ ] **Step 2: Run it, verify it fails**

Run: `mix test test/cure/elab/resolution_overload_test.exs`
Expected: FAIL — `overload_candidates/2` undefined; and `ambiguous_modules` returns `[]` (the literal `#plus` suffix does not match `M#plus~0`).

- [ ] **Step 3: Implement**

Add the gather primitive and generalize the matchers. Factor the "does key `s` provide bare name `b`" test into one helper used by all four:

```elixir
# lib/cure/elab/resolution.ex

# A key provides bare name `b` iff its base is exactly `b` (size-one, ends with
# "#b" or is the bare atom `b`) or an overload member of `b` (base "b~<ord>",
# so the string contains "#b~" or starts "b~"). Cheap string ops, no split.
defp provides_bare?(s, b) do
  exact = "##{b}"
  ovl = "##{b}~"
  bare_ovl = "#{b}~"
  s == b or String.ends_with?(s, exact) or String.contains?(s, ovl) or
    String.starts_with?(s, bare_ovl)
end

@doc """
Every in-scope canonical def key that provides `bare`: the local module's
members and, if none local, `prefer_direct`-scoped import providers. Returns
[] (unknown), [key] (single provider), or [k0, k1, …] (an overload set). Used
by the applied call site to prune by argument type.
"""
@spec overload_candidates(Env.t(), atom()) :: [atom()]
def overload_candidates(%Env{} = env, bare) do
  b = Atom.to_string(bare)

  Map.keys(env.defs)
  |> Enum.filter(fn key -> is_atom(key) and provides_bare?(Atom.to_string(key), b) end)
  |> Enum.map(fn key -> {Cure.Elab.Name.owner(key), key} end)
  |> prefer_direct(env.import_modules)
  |> prefer_local(env.module_owner)
  |> Enum.map(&elem(&1, 1))
  |> Enum.uniq()
end

# A member owned by the current module shadows same-named imports entirely.
defp prefer_local(matches, owner) when is_binary(owner) do
  case Enum.filter(matches, fn {o, _key} -> o == owner end) do
    [] -> matches
    locals -> locals
  end
end

defp prefer_local(matches, _owner), do: matches
```

Then update the filter in `resolve_canonical_suffix/2`, `shadowed_origin/2`, and `ambiguous_modules/2` to use `provides_bare?/2`. Each currently reads like:

```elixir
suffix = "##{Atom.to_string(bare)}"
# ... String.ends_with?(Atom.to_string(key), suffix) ...
```

Replace the per-key predicate with `provides_bare?(Atom.to_string(key), Atom.to_string(bare))`. Concretely in `resolve_canonical_suffix/2`:

```elixir
defp resolve_canonical_suffix(env, bare) do
  b = Atom.to_string(bare)

  matches =
    [env.ctors, env.families, env.defs]
    |> Enum.flat_map(&Map.keys/1)
    |> Enum.filter(fn key -> is_atom(key) and provides_bare?(Atom.to_string(key), b) end)
    |> Enum.uniq()
    |> Enum.map(fn key -> {Cure.Elab.Name.owner(key), key} end)
    |> prefer_direct(env.import_modules)

  case matches do
    [{_owner, key}] -> {:ok, key}
    [] -> :none
    many -> {:ambiguous, Enum.map(many, &elem(&1, 0)) |> Enum.uniq()}
  end
end
```

Apply the analogous `provides_bare?` swap in `shadowed_origin/2` (its `String.ends_with?(…, suffix)`) and `ambiguous_modules/2` (its `String.ends_with?(…, suffix)`). This keeps a bare, unapplied overloaded reference surfacing `{:ambiguous, [owners]}` / a non-empty `ambiguous_modules` list — the actionable diagnostic — instead of silently degrading to `:none`/`:unknown_global` (spec §9 key-format-ripple risk).

Note: `resolve_canonical_suffix/2` returning `{:ambiguous, ["M"]}` for a same-module overload set means a *bare unapplied* `plus` (no args) is reported ambiguous. That is the intended Ph1 behavior (§4 bare-unapplied limitation): only the applied path (Task 5) prunes.

- [ ] **Step 3b:** Run the full existing `resolution` and name-resolution suites to confirm the `provides_bare?` generalization did not change any single-provider outcome:

Run: `mix test test/cure/elab/ --only resolution 2>/dev/null; mix test test/cure/elab/cross_module_names_test.exs test/cure/elab/imported_module_dup_test.exs`
Expected: no *new* failures beyond the 4 taxonomy tests migrated in Task 4 (which still assert the old `:duplicate_definition` until then — run this step BEFORE Task 4 lands and treat only pre-existing green tests as the baseline).

- [ ] **Step 4: Run the unit test, verify it passes**

Run: `mix test test/cure/elab/resolution_overload_test.exs`
Expected: PASS (4 tests).

- [ ] **Step 5: Commit**

```bash
git add lib/cure/elab/resolution.ex test/cure/elab/resolution_overload_test.exs
git commit -m "feat(elab): overload candidate gathering + overload-aware name resolution"
```

---

### Task 3: Register overload members under discriminated keys

**Files:**
- Modify: `lib/cure/elab/program.ex` (ordinal pre-pass; relax `check_no_duplicate_defs`)
- Modify: `lib/cure/elab/declarations.ex` (`function_signature/2` reads `:overload_ordinal`)
- Test: `test/cure/elab/type_directed_overload_test.exs` (add a registration probe)

**Interfaces:**
- Consumes: `Cure.Elab.Name.overload_key/2` (Task 1); `Env.add_def`'s `owned_name` qualification.
- Produces: two same-name `fn` defs register under distinct keys `Mod#name~0`/`Mod#name~1` without overwrite; `check_no_duplicate_defs` no longer rejects a same-name group outright.

Mechanism: a per-module pre-pass tags each `:function_def` in a name-group of size ≥2 with `overload_ordinal: <declaration-order index>` in its meta. `function_signature/2` (`declarations.ex:672`) turns the bare `name` into `Name.overload_key(name, ord)` when the tag is present, so `Env.add_def` → `owned_name` qualifies it to `Mod#name~ord`. Size-one groups are untagged and unchanged.

The pre-elaboration `check_no_duplicate_defs` (`program.ex:344`) can no longer be the enforcer (it has no telescopes to tell an overload set from a true duplicate). Relax it to a no-op for `:function_def` names; the precise `:overlapping_overload` check lands in Task 4 after signatures are elaborated. (The other `first_dup_per_module` callers — `:duplicate_type`, `:duplicate_constructor` — are untouched.)

- [ ] **Step 1: Write the failing test** (append to `type_directed_overload_test.exs`, a new `@tag :overload` un-skipped test)

```elixir
test "two same-name defs both register (no silent overwrite)" do
  src = """
  mod OverloadReg
    type Meters = MkM(Int)
    type Grams = MkG(Int)
    fn plus(a: Meters, b: Meters) -> Meters = a
    fn plus(a: Grams, b: Grams) -> Grams = a
    fn only_m() -> Meters = plus(MkM(1), MkM(2))
  end
  """

  # Elaboration must no longer fail with duplicate_definition; both plus members
  # are registered so the (type-distinct) program is well-formed.
  assert {:ok, _env} = Cure.Elab.Program.elaborate(src)
end
```

(If `Cure.Elab.Program.elaborate/1` is not the public entry, use the same `compile_and_load` form as the pin but assert `{:ok, _}`; confirm the entry name against `program.ex` before writing. The behavior asserted — no duplicate_definition — is the point.)

- [ ] **Step 2: Run it, verify it fails**

Run: `mix test test/cure/elab/type_directed_overload_test.exs --include overload -k "both register"`
Expected: FAIL with `{:duplicate_definition, :plus}` (pre-elab gate) — or, once the gate is relaxed but before keying, an overwrite/arity error.

- [ ] **Step 3a: Relax the pre-elab duplicate gate**

```elixir
# lib/cure/elab/program.ex — check_no_duplicate_defs/1
# Same-name function defs are no longer rejected here: a type-distinct pair is a
# legal overload set, and telling a set from a true duplicate needs elaborated
# telescopes (see check_overload_legality/1, run after the register pass). This
# gate keeps rejecting nothing for :function_def; overlap is caught later.
defp check_no_duplicate_defs(_ast), do: :ok
```

Leave `first_dup_per_module/4` and its `:duplicate_type`/`:duplicate_constructor` callers intact.

- [ ] **Step 3b: Add the ordinal pre-pass** (annotate before `register_pass`)

In `elaborate_declarations/3` (`program.ex:1913`), thread the items through an annotator before `register_pass`:

```elixir
# lib/cure/elab/program.ex
defp elaborate_declarations(items, env, prelude?) do
  items = annotate_overload_ordinals(items)
  with {:ok, env1, fn_decls} <- register_pass(items, env, prelude?),
       # ... unchanged ...
end

# Tag each :function_def in a same-name group of size >= 2 with its declaration-
# order ordinal within that group. Size-one names are left untouched (inert).
defp annotate_overload_ordinals(items) when is_list(items) do
  names =
    items
    |> Enum.flat_map(fn
      {:function_def, meta, _} when is_list(meta) -> [Keyword.fetch!(meta, :name)]
      _ -> []
    end)

  overloaded = for {n, c} <- Enum.frequencies(names), c >= 2, into: MapSet.new(), do: n

  {tagged, _counters} =
    Enum.map_reduce(items, %{}, fn
      {:function_def, meta, body} = decl, counters when is_list(meta) ->
        name = Keyword.fetch!(meta, :name)

        if MapSet.member?(overloaded, name) do
          ord = Map.get(counters, name, 0)
          {{:function_def, Keyword.put(meta, :overload_ordinal, ord), body},
           Map.put(counters, name, ord + 1)}
        else
          {decl, counters}
        end

      other, counters ->
        {other, counters}
    end)

  tagged
end

defp annotate_overload_ordinals(items), do: items
```

Confirm the shape `items` has at this point (list of top-level decls for one module). If `elaborate_declarations` receives a wrapped container, annotate the inner decl list; match the existing `declarations/1` normalization already applied upstream. Only `:function_def` nodes are tagged, so wrapping is irrelevant to other node kinds.

Safety precondition: grouping purely by bare `Keyword.fetch!(meta, :name)` is only sound because `items` can never contain two DIFFERENT sibling modules sharing a function name — `check_no_sibling_collision` (`program.ex:189`) rejects that combination before `elaborate_declarations` runs (both current call sites, `program.ex:370` and `:1518`, are reached through `check_ast/2`, which runs `check_declarations/1` — including `check_no_sibling_collision` — first). Do not call `annotate_overload_ordinals/1` from any new entry point that reaches `elaborate_declarations` without that precondition already having been checked.

- [ ] **Step 3c: Consume the ordinal in `function_signature/2`**

```elixir
# lib/cure/elab/declarations.ex — function_signature/2, replace the first line
name =
  case Keyword.get(meta, :overload_ordinal) do
    nil -> meta |> Keyword.fetch!(:name) |> String.to_atom()
    ord -> Cure.Elab.Name.overload_key(meta |> Keyword.fetch!(:name) |> String.to_atom(), ord)
  end
```

`Env.add_def(env, name, …)` then qualifies `:"plus~0"` to `:"Mod#plus~0"` via `owned_name`. The body-elaboration pass (second pass over `fn_decls`) already carries the same `meta`, so its own `function_signature`/lookup uses the same discriminated key — verify the body pass keys off `sig.name`, not a re-derived bare name (read `elaborate_function_body`/the second pass; if it re-derives the bare name it must adopt the same ordinal branch).

- [ ] **Step 4: Run it, verify it passes**

Run: `mix test test/cure/elab/type_directed_overload_test.exs --include overload -k "both register"`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/elab/program.ex lib/cure/elab/declarations.ex test/cure/elab/type_directed_overload_test.exs
git commit -m "feat(elab): register same-name overload members under discriminated keys"
```

---

### Task 4: Overlap check + error-taxonomy migration

**Files:**
- Modify: `lib/cure/elab/program.ex` (add `check_overload_legality/1` after the register pass)
- Modify: `test/cure/elab/dup_def_test.exs`, `test/cure/elab/imported_module_dup_test.exs`, `test/cure/elab/global_namespace_soundness_test.exs`, `test/cure/elab/cross_module_names_test.exs` (taxonomy migration)
- Test: `test/cure/elab/type_directed_overload_test.exs` (add overlap-rejection case)

**Interfaces:**
- Consumes: elaborated signatures in `env.defs` after `register_pass`; `Cure.Elab.Name.overload_base/1`; the kernel's unifier/conversion to test telescope indistinguishability (use the existing elaborator-side unify entry — confirm the exact function; `Cure.Elab` already unifies parameter types elsewhere. If no elaborator-level "do these two closed telescopes unify" helper exists, compare via `Cure.Core.Normalise` normal-form equality of each parameter type, which is sound-enough for the accidental-duplicate case Ph1 must catch).
- Produces: `{:error, {:overlapping_overload, name, arity}}` for a same-arity, mutually-indistinguishable pair.

Definition: two members of the same overload group **overlap** iff they have equal arity and, position-by-position, their parameter types are convertible (mutually unify) — no argument could ever tell them apart. This is the safety the old `:duplicate_definition` gate protected, now precise because telescopes are elaborated.

- [ ] **Step 1: Write the failing test** (overlap rejection, in `type_directed_overload_test.exs`)

```elixir
test "same-arity indistinguishable overloads are rejected as overlapping" do
  src = """
  mod OverlapReject
    fn dup(a: Int, b: Int) -> Int = a
    fn dup(a: Int, b: Int) -> Int = b
  end
  """

  assert {:error, {:overlapping_overload, :dup, 2}} = elaborate_error(src)
end
```

Provide these two test helpers, defined once (module-level `defp` in `type_directed_overload_test.exs`) and reused verbatim by Tasks 5 and 6 below — do NOT redefine either name a second time in the same file, Elixir will reject the duplicate `defp`:

```elixir
# Strips the {:codegen_error, inner} wrapper Cure.Compiler.compile_and_load/2
# adds around an elaboration error (see the existing pattern at
# test/cure/project/compile_project_test.exs:179), so assertions can match
# the same inner tuple regardless of which entry point produced the error.
defp unwrap({:codegen_error, inner}), do: inner
defp unwrap(other), do: other

defp elaborate_error(src) do
  {:error, err} = Cure.Elab.Program.elaborate(src)
  {:error, unwrap(err)}
end
```

`Cure.Elab.Program.elaborate/1` does not add a `:codegen_error` wrapper (`check_overload_legality/1`'s error propagates unwrapped through `check_ast/2`'s `with` chain), so `unwrap/1` is a no-op pass-through on this path — it exists to give `elaborate_error/1` (and the two helpers Tasks 5/6 add below) one consistent inner-tuple shape to assert on regardless of entry point.

- [ ] **Step 2: Run it, verify it fails**

Run: `mix test test/cure/elab/type_directed_overload_test.exs --include overload -k "overlapping"`
Expected: FAIL — currently registers two `dup~n` keys and elaborates (Task 3 relaxed the gate), so no error is raised.

- [ ] **Step 3: Implement `check_overload_legality/1`** and call it after `register_pass` (before body elaboration, so an overlap is reported before wasted work):

```elixir
# lib/cure/elab/program.ex — inside elaborate_declarations/3, after register_pass:
with {:ok, env1, fn_decls} <- register_pass(items, env, prelude?),
     :ok <- check_overload_legality(env1),
     # ... existing steps ...

# Group registered def keys by their overload base + owner; within each group,
# reject any same-arity pair whose parameter telescopes are position-wise
# convertible (a genuine duplicate masquerading as an overload).
defp check_overload_legality(env) do
  env.defs
  |> Enum.filter(fn {k, _} -> is_atom(k) and Cure.Elab.Name.overload_member?(k) end)
  |> Enum.group_by(fn {k, _} -> {Cure.Elab.Name.owner(k), Cure.Elab.Name.overload_base(k)} end)
  |> Enum.reduce_while(:ok, fn {{_owner, base}, members}, :ok ->
    case first_overlapping_pair(env, members) do
      nil -> {:cont, :ok}
      arity -> {:halt, {:error, {:overlapping_overload, String.to_atom(base), arity}}}
    end
  end)
end

# Returns the shared arity of the first overlapping pair, or nil.
defp first_overlapping_pair(env, members) do
  defs = Enum.map(members, fn {_k, d} -> d end)

  Enum.reduce_while(pairs(defs), nil, fn {a, b}, nil ->
    with ta <- param_types(a.type),
         tb <- param_types(b.type),
         true <- length(ta) == length(tb),
         true <- Enum.all?(Enum.zip(ta, tb), fn {x, y} -> Cure.Elab.TypeConv.convertible?(env, x, y) end) do
      {:halt, length(ta)}
    else
      _ -> {:cont, nil}
    end
  end)
end

defp pairs(list), do: for(i <- 0..(length(list) - 1), j <- (i + 1)..(length(list) - 1)//1, i < j, do: {Enum.at(list, i), Enum.at(list, j)})
```

Implement `param_types/1` by walking the stored `:pi` telescope (`{:pi, _grade, domain, codomain}` → collect `domain`, recurse into `codomain`; stop at the non-`:pi` return) — collect *every* domain unconditionally, exactly as shown in the snippet above. Do NOT mirror `typealias_parameter_count/1` (`declarations.ex:2125`) for this: that function's walk is guarded on `{:type, _level}` domains only (it counts a typealias's own `Type`-kinded parameters) and would silently return `[]` for an ordinary value-typed telescope like `(a: Meters, b: Meters)` — the two functions solve different problems and must not share a shape.

Implement the shared convertibility check as `Cure.Elab.TypeConv.convertible?/3` in the new `lib/cure/elab/type_conv.ex` (see File Structure) using the existing normal-form/conversion facility (confirm: `Cure.Core.Normalise.nf/2` + structural equality, or the elaborator's unify — pick the one already used for parameter-type comparison; do NOT add a kernel function). Make it a **public** function in its own module from the start, not a private `defp` inside `program.ex` — Task 5's `Cure.Elab.Overload.resolve/4` calls this exact same function, and a private helper in a different module cannot be reused, which would force Task 5 to duplicate the logic the plan says to share. Erased/implicit leading binders auto-generated by `auto_generalize` are part of the telescope for both members equally, so they compare position-wise like any other.

- [ ] **Step 4a: Run the overlap test, verify it passes**

Run: `mix test test/cure/elab/type_directed_overload_test.exs --include overload -k "overlapping"`
Expected: PASS.

- [ ] **Step 4b: Migrate the four taxonomy tests**

For each file, find the assertion targeting a **same-arity, same-type duplicate function** within one module (or an imported module) and change the expected tuple from `{:duplicate_definition, name}` to `{:overlapping_overload, name, arity}` (with the correct arity). Leave every other assertion (`:duplicate_type`, `:duplicate_constructor`, `:sibling_module_collision`, `:constructor_function_collision`) unchanged. Confirm by reading each file which specific case moves:

```bash
grep -n "duplicate_definition" test/cure/elab/dup_def_test.exs \
  test/cure/elab/imported_module_dup_test.exs \
  test/cure/elab/global_namespace_soundness_test.exs \
  test/cure/elab/cross_module_names_test.exs
```

Run each migrated file:

Run: `mix test test/cure/elab/dup_def_test.exs test/cure/elab/imported_module_dup_test.exs test/cure/elab/global_namespace_soundness_test.exs test/cure/elab/cross_module_names_test.exs`
Expected: PASS (all, with migrated expectations).

- [ ] **Step 5: Commit**

```bash
git add lib/cure/elab/program.ex test/cure/elab/*.exs
git commit -m "feat(elab): overlapping-overload check + duplicate_definition taxonomy migration"
```

---

### Task 5: Call-site elaborate-and-prune (term position) — greens the same-module pin

**Files:**
- Create: `lib/cure/elab/overload.ex`
- Modify: `lib/cure/elab/elaborator.ex` (`elaborate_named_call/5`)
- Test: `test/cure/elab/overload_test.exs` (create, unit); `test/cure/elab/type_directed_overload_test.exs` (un-skip the pin; add no-match + ambiguous)

**Interfaces:**
- Produces: `Cure.Elab.Overload.resolve/4` (signature above).
- Consumes: `Resolution.overload_candidates/2` (Task 2); argument inference via the elaborator's existing `map_present_args/4` + `elaborate_expr_typed/4`; dispatch via existing `elaborate_global_app/4`.

The pin's `plus(MkM(3), MkM(4))` goes through `elaborate_named_call/5` (`elaborator.ex:179`). Insert an overload clause **before** the generic global paths but **after** the ctor/method/constrained/qualified special cases, so a size-≥2 set is pruned by argument type and the winner dispatched.

- [ ] **Step 1: Write the failing unit test for the prune engine**

```elixir
# test/cure/elab/overload_test.exs
defmodule Cure.Elab.OverloadTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Overload

  # Build an env whose two `plus` members take (Meters,Meters) and (Grams,Grams).
  # Use the real elaborator to register them so telescopes are genuine.
  setup do
    src = """
    mod OvlEngine
      type Meters = MkM(Int)
      type Grams = MkG(Int)
      fn plus(a: Meters, b: Meters) -> Meters = a
      fn plus(a: Grams, b: Grams) -> Grams = a
    end
    """
    {:ok, env} = Cure.Elab.Program.elaborate(src)
    types = fn tname -> Cure.Elab.OverloadTest.Helper.data_type(env, tname) end
    {:ok, env: env, types: types}
  end

  test "one matching member resolves to its discriminated key", %{env: env, types: types} do
    cands = Cure.Elab.Resolution.overload_candidates(env, :plus)
    m = types.("Meters")
    assert {:ok, key} = Overload.resolve(env, :plus, [m, m], cands)
    assert Cure.Elab.Name.overload_base(key) == "plus"
    assert to_string(key) =~ "Meters" == false  # key is ordinal-based, not type-based
  end

  test "no member matches → :no_matching_overload", %{env: env, types: types} do
    cands = Cure.Elab.Resolution.overload_candidates(env, :plus)
    int = types.("Int") || Cure.Elab.OverloadTest.Helper.int_type()
    assert {:error, {:no_matching_overload, :plus, _}} = Overload.resolve(env, :plus, [int, int], cands)
  end
end
```

(Provide a tiny `Helper` module in the test file exposing `data_type/2` — look up a nullary data family's `{:vdata, key, []}`/`{:data, key, [], []}` type value from `env` — and `int_type/0`. Keep it behavioral: it reads only public `Env`/`Inductive` accessors. If constructing these type terms proves fiddly, assert the engine indirectly through the pin/no-match/ambiguous integration tests below and keep `overload_test.exs` to the pure list-arithmetic cases the engine supports without hand-built terms — e.g. candidate count and the empty-candidates short-circuit. Do not block the task on hand-rolling kernel terms.)

- [ ] **Step 2: Run it, verify it fails**

Run: `mix test test/cure/elab/overload_test.exs`
Expected: FAIL — `Cure.Elab.Overload` undefined.

- [ ] **Step 3a: Implement the prune engine**

```elixir
# lib/cure/elab/overload.ex
defmodule Cure.Elab.Overload do
  @moduledoc """
  Type-directed pruning of an overload set at an applied call site (Ph1, Idris2
  elaborate-and-prune). Pure over an already-elaborated Env and the inferred
  argument types; never rewrites Core, never touches the kernel/TCB.
  """
  alias Cure.Core.Env

  @spec resolve(Env.t(), atom(), [Cure.Core.Term.t()], [atom()]) ::
          {:ok, atom()}
          | {:error, {:no_matching_overload, atom(), [term()]}}
          | {:error, {:ambiguous_overload, atom(), [String.t()]}}
  def resolve(%Env{} = env, bare, arg_types, candidates) do
    survivors =
      Enum.filter(candidates, fn key ->
        case Env.get_def(env, key) do
          %{type: pi} -> params_match?(env, param_types(pi), arg_types)
          _ -> false
        end
      end)

    case survivors do
      [key] -> {:ok, key}
      [] -> {:error, {:no_matching_overload, bare, arg_types}}
      many -> {:error, {:ambiguous_overload, bare, owners(many)}}
    end
  end

  defp params_match?(_env, ptypes, atypes) when length(ptypes) != length(atypes), do: false

  defp params_match?(env, ptypes, atypes) do
    Enum.all?(Enum.zip(ptypes, atypes), fn {p, a} -> types_unify?(env, p, a) end)
  end

  # Walk the stored Pi telescope to its parameter domains: collect every
  # domain unconditionally (do NOT reuse typealias_parameter_count/1's
  # {:type, _level}-guarded shape — see Task 4's note; that guard would drop
  # ordinary value-typed domains like Meters/Grams).
  defp param_types({:pi, _grade, domain, codomain}), do: [domain | param_types(codomain)]
  defp param_types(_return), do: []

  defp owners(keys), do: keys |> Enum.map(&Cure.Elab.Name.owner/1) |> Enum.uniq()

  # First-order unification of an argument's inferred type against a parameter
  # type. Calls the SAME shared facility Task 4 uses (Cure.Elab.TypeConv,
  # lib/cure/elab/type_conv.ex) rather than a local copy; do NOT add a kernel
  # function.
  defp types_unify?(env, param_type, arg_type) do
    Cure.Elab.TypeConv.convertible?(env, param_type, arg_type)
  end
end
```

`Cure.Elab.TypeConv.convertible?/3` is implemented once, in Task 4, as a public function (see Task 4 Step 3 and File Structure) — Task 5 only calls it, it does not reimplement or wrap it under a different name. Note the erased-leading-implicit subtlety: `param_types/1` yields *every* Pi domain including auto-generalized `{a : Type}` implicits, but the inferred `arg_types` correspond only to the *explicit* arguments. Align them: drop leading erased/implicit domains from `param_types` (quantity 0) before zipping, OR compare only the trailing `length(arg_types)` domains. Confirm which by inspecting a stored `sig.pi` for a function with an auto-generalized implicit; the pin's `plus(a: Meters, b: Meters)` has no free type variable so no implicit is inserted (both domains are explicit `Meters`), but the no-match/cross-module cases must still align correctly. Add a test asserting resolution works for a member with a leading implicit if the stdlib fixture needs it.

- [ ] **Step 3b: Wire the clause into `elaborate_named_call/5`**

Insert as a new `cond` branch immediately before the `ambiguous_modules >= 2` clause (currently `elaborator.ex:305`) — i.e. after the ctor clause (`:239`) AND after the dot-qualified-global clause's entire body ends (that clause starts at `:271` and its `with`/`case`/retry body runs through `:304`; do not insert inside it — `elaborator.ex:299` sits mid-body of that clause, not between clauses, and is the wrong anchor). The new clause's own guard already excludes dotted names (`not String.contains?(name, ".")`), so it is mutually exclusive with the dot-qualified clause regardless of exact position; the hard requirement is only that it precedes `ambiguous_modules >= 2` and everything after it:

```elixir
# An applied call to a bare overloaded name (a set of >= 2 members): infer the
# argument types once, prune by first-order unification, dispatch the winner.
(cands = Cure.Elab.Resolution.overload_candidates(env, atom)) |> length() >= 2 and
    not String.contains?(name, ".") ->
  with {:ok, present} <- map_present_args(args, names, ctx, env),
       arg_types = Enum.map(present, fn {_term, ty} -> ty end),
       {:ok, winner} <- Cure.Elab.Overload.resolve(env, atom, arg_types, cands) do
    elaborate_global_app(env, winner, present, ctx)
  else
    {:error, {tag, _, _}} = err when tag in [:no_matching_overload, :ambiguous_overload] -> err
    {:error, _} = err -> err
  end
```

Confirm the exact shape `map_present_args/4` returns (a list of `{core_term, type}` pairs, or a struct) by reading it near `elaborator.ex:241` — adapt `arg_types`/the `elaborate_global_app` arg accordingly. A guard-bound assignment inside a `cond` may need restructuring to a preceding `cond do` variable or a helper predicate `overloaded_applied?(env, name, atom)`; if Elixir rejects the inline assignment in the guard, compute `cands` once above the `cond` and branch on `length(cands) >= 2 and not String.contains?(name, ".")`.

Important ordering: this clause must sit **below** `method?`/`constrained?` (an interface method is not an overload set) and the ctor clause (`Inductive.get_ctor(env, resolved)`), and **above** the `ambiguous_modules >= 2` clause — otherwise a same-module set (whose members share one owner, so `ambiguous_modules` may return `["M"]` of length 1, not ≥2) or a cross-module set is misrouted. Verify with the ambiguous integration test below.

- [ ] **Step 3c: Un-skip the pin and add no-match + ambiguous integration tests**

Delete `@tag :skip` from the existing pin test. Add:

```elixir
test "no overload matches the argument types" do
  src = """
  mod OvlNoMatch
    type Meters = MkM(Int)
    type Grams = MkG(Int)
    fn plus(a: Meters, b: Meters) -> Meters = a
    fn plus(a: Grams, b: Grams) -> Grams = a
    fn bad() -> Int = match plus(1, 2)
      _ -> 0
  end
  """
  assert {:error, err} = compile_and_load_error(src)
  assert match?({:no_matching_overload, :plus, _}, unwrap(err))
end
```

Add the helper this test calls (reuses `unwrap/1` from Task 4; do not redefine `unwrap/1` here):

```elixir
defp compile_and_load_error(src) do
  Cure.Compiler.compile_and_load(src, emit_events: false)
end
```

This is intentionally a thin, same-shape pass-through (`compile_and_load/2` already returns `{:error, {:codegen_error, inner}}` on failure, per the existing pattern at `test/cure/project/compile_project_test.exs:179`) — its purpose is a stable, greppable name paired with `unwrap/1`, not new logic.

(An ambiguous integration case is exercised in Task 6 across modules, where two direct imports both provide a matching `plus`; a same-module set cannot be ambiguous by type since Task 4 rejects same-arity indistinguishable members at declaration. Keep the ambiguous assertion in Task 6.)

- [ ] **Step 4: Run the pin + unit + no-match**

Run: `mix test test/cure/elab/overload_test.exs test/cure/elab/type_directed_overload_test.exs --include overload --include skip`
Expected: PASS — including `add_m() == 7` and `add_g() == 30` (proves emit produced distinct BEAM names `plus~0`/`plus~1` and the call sites targeted the right one).

- [ ] **Step 5: Commit**

```bash
git add lib/cure/elab/overload.ex lib/cure/elab/elaborator.ex test/cure/elab/overload_test.exs test/cure/elab/type_directed_overload_test.exs
git commit -m "feat(elab): type-directed overload resolution at applied call sites"
```

---

### Task 6: Cross-module pin + ambiguous-across-modules

**Files:**
- Modify: `test/cure/elab/type_directed_overload_test.exs` (cross-module + ambiguous cases)
- Possibly modify: `lib/cure/elab/resolution.ex` / `lib/cure/elab/overload.ex` only if the cross-module gather surfaces a gap

**Interfaces:**
- Consumes: everything from Tasks 1–5; the multi-file test harness patterns.

The cross-module case proves the parent spec's motivation: two `use`d modules each export `to_int` on a different type, and an unqualified `to_int(x)` resolves by `x`'s type. `overload_candidates/2` already scans all `env.defs` keys and applies `prefer_direct`, so cross-module members are gathered without new resolution code — this task is primarily the test, plus fixing any gather/ordering gap it reveals.

- [ ] **Step 1: Write the failing cross-module test**

Follow the multi-file-fixture pattern already proven in `test/cure/project/multi_file_link_test.exs`: write `.cure` files under a temp `src/` dir plus a minimal `Cure.toml`, then `Cure.Project.load(dir)` followed by `Cure.Project.compile_project(project, output_dir: ebin, check_types: false)`, which returns `{:ok, %{modules: [atom(), ...]}}` and writes one `.beam` per module under `output_dir`. Do NOT model this on `test/cure/project/compile_project_test.exs` or `test/cure/elab/cross_module_coherence_test.exs`: the former's `compile_project/2` tests only assert `.app`/`.beam` file *existence* and never load or run the compiled code, and the latter's `stdlib_source_dir` override is for `use Std.X` stdlib resolution, an unrelated concern — neither demonstrates the load-and-invoke step this task needs. Read `multi_file_link_test.exs` first to copy its exact fixture-writing and `compile_project` invocation. Structure:

```elixir
test "an unqualified call resolves across two used modules by argument type" do
  # Module A exports to_int(Char); Module B exports to_int(String); consumer
  # uses both and calls to_int on each — resolves by argument type.
  # (Faithful mirror of Std.Char.code_point vs Std.String.to_int.)
  files = %{
    "a.cure" => """
    mod OvlCharMod
      fn to_int(c: Char) -> Int = 65
    end
    """,
    "b.cure" => """
    mod OvlStrMod
      fn to_int(s: String) -> Int = 3
    end
    """,
    "main.cure" => """
    mod OvlXConsumer
      use OvlCharMod
      use OvlStrMod
      fn from_char() -> Int = to_int('A')
      fn from_str() -> Int = to_int("abc")
    end
    """
  }

  assert {:ok, mod} = compile_multi(files, "Cure.OvlXConsumer")
  assert apply(mod, :from_char, []) == 65
  assert apply(mod, :from_str, []) == 3
end
```

No existing test loads a `compile_project`-produced `.beam` and invokes it (confirmed: no test in the suite calls `Code.load_file`/`:code.load_binary`/`:code.load_file` on a project-compiled module) — `compile_multi/2` must add that step itself, it is not reusable off the shelf:

```elixir
defp compile_multi(files, start_module) do
  # ... write `files` under tmp/src, write a minimal Cure.toml, then:
  with {:ok, project} <- Cure.Project.load(tmp),
       {:ok, %{modules: modules}} <-
         Cure.Project.compile_project(project, output_dir: ebin, check_types: false) do
    Code.prepend_path(ebin)
    Enum.each(modules, fn m -> {:module, ^m} = :code.load_file(m) end)
    {:ok, String.to_existing_atom(start_module)}
  end
end
```

`start_module` is the `Cure.<ModName>` atom (mirrors `run-on-unix.sh`'s convention noted in the pin) — e.g. `"Cure.OvlXConsumer"`.

- [ ] **Step 2: Run it, verify it fails** (before any fix) — expected FAIL, most likely `{:ambiguous_name, :to_int, …}` (the pre-overload ambiguity path fires) or `:no_matching_overload` if gather/ordering is off.

Run: `mix test test/cure/elab/type_directed_overload_test.exs --include overload -k "across two used modules"`

- [ ] **Step 3: Fix any gap.** Likely the `elaborate_named_call` clause ordering: the `ambiguous_modules >= 2` clause (`elaborator.ex:305`) may intercept a cross-module set before the overload clause. Ensure the overload clause (Task 5) precedes it AND that `overload_candidates` returns both members here. If two direct imports each provide a *type-distinct* `to_int`, the overload clause prunes to one; if both matched the same argument type it must return `{:ambiguous_overload, :to_int, ["OvlCharMod", "OvlStrMod"]}`. Add that ambiguous assertion:

```elixir
test "genuinely ambiguous cross-module overloads report :ambiguous_overload" do
  # Both modules export foo(Int); an unqualified foo(1) cannot be disambiguated.
  files = %{
    "a.cure" => "mod OvlAmbA\n  fn foo(x: Int) -> Int = 1\nend\n",
    "b.cure" => "mod OvlAmbB\n  fn foo(x: Int) -> Int = 2\nend\n",
    "main.cure" => """
    mod OvlAmbC
      use OvlAmbA
      use OvlAmbB
      fn pick() -> Int = foo(1)
    end
    """
  }
  assert {:error, err} = compile_multi_error(files)
  assert match?({:ambiguous_overload, :foo, _}, unwrap(err))
end

test "qualifying resolves the ambiguity (escape hatch)" do
  # Same modules as the ambiguous case above, but a dot-qualified call names
  # the provider directly (OvlAmbA.foo(1)), routed through the existing
  # dot-qualified-global clause (elaborator.ex:271, Resolution.resolve_qualified/3)
  # rather than the overload clause — bypasses the ambiguity entirely.
  files = %{
    "a.cure" => "mod OvlAmbA\n  fn foo(x: Int) -> Int = 1\nend\n",
    "b.cure" => "mod OvlAmbB\n  fn foo(x: Int) -> Int = 2\nend\n",
    "main.cure" => """
    mod OvlAmbD
      use OvlAmbA
      use OvlAmbB
      fn pick() -> Int = OvlAmbA.foo(1)
    end
    """
  }
  assert {:ok, mod} = compile_multi(files, "Cure.OvlAmbD")
  assert apply(mod, :pick, []) == 1
end
```

Add the helper the first test above calls (reuses `unwrap/1` from Task 4; do not redefine `unwrap/1` here). `compile_multi/2`'s `with` chain (Step 1 above) short-circuits and returns `Cure.Project.compile_project/2`'s `{:error, reason}` unchanged when a module fails to elaborate, without ever evaluating `start_module`, so passing a placeholder start-module string here is safe:

```elixir
defp compile_multi_error(files) do
  {:error, _} = compile_multi(files, "unused")
end
```

Confirm empirically (Step 2 below) what `reason` actually is for a per-module elaboration failure inside `compile_project/2` — it may already be `{:codegen_error, {:ambiguous_overload, ...}}` (matching `unwrap/1`'s existing clause) or a differently-tagged wrapper (e.g. `{:module_compile_failed, mod, {:codegen_error, ...}}}`). If it is a shape `unwrap/1` does not already handle, add one more `unwrap/1` clause for it (still in Task 4's single definition site) rather than special-casing here.

- [ ] **Step 4: Run cross-module cases, verify pass**

Run: `mix test test/cure/elab/type_directed_overload_test.exs --include overload`
Expected: PASS (all overload cases).

- [ ] **Step 5: Commit**

```bash
git add lib/cure/elab test/cure/elab/type_directed_overload_test.exs
git commit -m "feat(elab): cross-module overload resolution + ambiguity diagnostics"
```

---

### Task 7: Inertness guard, oracle probe, full suite

**Files:**
- Test: `test/cure/elab/type_directed_overload_test.exs` (inertness case); oracle harness (optional)

**Interfaces:** none new.

- [ ] **Step 1: Inertness regression test** (a single-def module compiles and runs unchanged — guards the key-format ripple)

```elixir
test "a single-definition module is unaffected by the overload machinery" do
  src = """
  mod OvlInert
    fn double(x: Int) -> Int = x + x
    fn quad(x: Int) -> Int = double(double(x))
  end
  """
  assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
  assert apply(mod, :quad, [3]) == 12
end
```

Run: `mix test test/cure/elab/type_directed_overload_test.exs --include overload`
Expected: PASS. (This must pass at every prior task too; run it as a canary after Tasks 1–6.)

- [ ] **Step 2: Oracle probe (best-effort).** Add an `idris2 --check` transcription of the same-module and cross-module cases to the existing OTP/oracle harness IF one accepts new cases cheaply; otherwise record a skip with reason (Idris unavailable). Do not block the suite on Idris. Check for the harness:

```bash
grep -rln "idris2" test/ scripts/ 2>/dev/null | head
```

If a harness exists, add the two cases; if not, note in the completion report that the oracle probe was deferred (no harness) — do not build one for Ph1.

- [ ] **Step 3: Full suite (once, serial)**

Run: `mix test`
Expected: green (plus the standing Antigen count). Investigate any regression before proceeding — a moved single-provider outcome means the `provides_bare?` generalization is too broad; a moved golden/emit test means a size-one key changed (constraint violation).

- [ ] **Step 4: Commit**

```bash
git add test/
git commit -m "test(elab): overload inertness guard + oracle probe"
```

---

## Self-Review

**Spec coverage:** §1 scope (same+cross-module, operator/labels out) → Global Constraints + Tasks 5/6; §4.1 discriminator → Task 1; §4.2 overload-set construction + gate transform → Tasks 3/4; §4.3 elaborate-and-prune → Task 5; §4.4 emission → free via `Name.base`, validated by Task 5 runtime assertions; §5 cross-module pin → Task 6; §6 taxonomy (`:overlapping_overload`/`:no_matching_overload`/`:ambiguous_overload` + migration) → Tasks 4/5/6; §7 non-goals → Global Constraints; §8 test plan items 1–7 → Tasks 3–7; §9 risks (key-format ripple, double-elaboration, ambiguity-where-match-expected) → Task 2 structural matcher + `ambiguous_modules` test, Task 5 infer-once, Task 5/6 actionable-error tests.

**Placeholder scan:** the confirm-during-implementation notes (exact `map_present_args` return shape; the convertibility facility; the multi-file harness; whether `elaborate_declarations` sees a wrapped list; the body pass's key derivation) are explicit verification steps against named code, not TBDs — each names the file/function to read and the fallback. Acceptable for a plan whose executor reads the tree; the Stage 3 review will tighten any that resolve to a concrete choice.

**Type consistency:** `overload_key/2`, `overload_member?/1`, `overload_base/1`, `overload_candidates/2`, `Overload.resolve/4`, `Cure.Elab.TypeConv.convertible?/3` used with identical signatures and identical module names across tasks (Task 4 defines `TypeConv.convertible?/3` once, public; Task 5 calls the same function, no second name or local copy). Error tuples consistent: `{:overlapping_overload, name, arity}`, `{:no_matching_overload, name, arg_types}`, `{:ambiguous_overload, name, owners}` in both spec §6 and Tasks 4/5/6.
