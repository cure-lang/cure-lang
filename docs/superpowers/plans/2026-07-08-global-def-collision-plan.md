# Global-Def Collision Protection Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Close the E-layer soundness gap where cross-module same-named global functions silently overwrite, by extending the locked Approach-B collision-triggered re-keying from families/ctors to `defs` — with the ambiguity trichotomy enforced at BOTH bare-reference resolution sites.

**Architecture:** `shadow_resolved_imports/1` (program.ex) gains a def-ownership scan parallel to `family_owners`; `Resolution.classify/2` output for defs drives `rekey_module_env` to move colliding def KEYS (and their `certified` membership) to `"Mod#name"` atoms; `ambiguous_modules/2` generalizes to consult `defs`; the trichotomy (local wins → unique import → E089 ambiguity) is enforced in `elaborate_named_call/5` (call position — extends the existing R7 check) and `resolve_free/2` (bare-value position — currently has zero checking). Orthogonal to the trichotomy (which governs BARE references only): qualified CALLS to plain defs (`A.foo(x)`) do not resolve at all today, independent of any collision — verified on this checkout (`resolve_qualified(env, name, :value)` is ctor-only; `elaborate_named_call/5` never consults its qualified `resolved` value outside the ctor clause). Task 2 closes this as a prerequisite for "qualified always reaches the import," since Approach B's escape hatch is meaningless for defs if it never worked in the first place.

**Spec:** `docs/superpowers/specs/language/2026-07-08-global-def-collision-design.md` (hardened). §2.1-2.2 are the contract; §4 names the red tests.

## Global Constraints

- One build/test run at a time, always sequential. OTP 26–28.
- Kernel/TCB untouched: no changes under `lib/cure/core/` EXCEPT none — even the `certified` re-key happens in `lib/cure/elab/resolution.ex` by rebuilding the Env struct field (the Env struct itself is not modified).
- TDD: red first for the stated reason, minimal green, refactor; tests immutable once correct (escape hatch only for a test proven wrong before ever green, argued explicitly).
- Commits authored as the user only, NO co-author trailers.
- Worktree root: `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/kernel-parity-batch`.

## Verified ground truth (2026-07-08 — trust these)

- `merge_env/2` blind-merges defs: `program.ex:629`.
- Ownership/classify/rekey flow for families: `shadow_resolved_imports/1` at `program.ex:532-590` — `family_owners` map (`owned_family_names(path)` per transitive module, `program.ex:489`), `Resolution.classify(family_owners, local)` → `%{losers, ambiguous}`, per-slice `Resolution.rekey_module_env(s, owner_mod, owned_losers, local_ctors)`, then `drop_bare_family` cleanup.
- `rekey_module_env/4` (`resolution.ex:79-103`): builds bare→`Mod#name` `amap`, rewrites `families`/`ctors`/`ctor_to_family`/`defs`(references only)/`builtins`. Does NOT touch `certified`.
- `ambiguous_modules/2` (`resolution.ex:285-300`): families-only; returns `[]` when the bare key exists, else origin modules providing `Mod#bare`.
- Call-position resolution + R7 precedent: `elaborate_named_call/5` (`elaborator.ex:231`); ambiguity check at `elaborator.ex:304-305` produces `{:error, {:ambiguous_name, atom, modules}}`.
- Bare-value resolution: `resolve_free/2` (`elaborator.ex:4641-4649`), zero checking, falls through to `{:global, atom}`. It has exactly TWO callers (grep-verified, both read): `elaborate_expr_typed/4`'s `{:variable,...}` clause (`elaborator.ex:55`, inside a `with {:ok, term} <- resolve_free(...), {:ok, type} <- Kernel.infer(...) do ... end` — a `with` chain, so an `{:error, _}` return already short-circuits and flows out as the function's own `{:error, _}` result, matching its own `@spec`) and `elaborate_expr/3`'s `{:variable,...}` clause (`elaborator.ex:4576`, a bare `case ... nil -> resolve_free(name, env)` whose result IS the function's return value, and `elaborate_expr/3` already returns `{:error, {:unsupported_expression, ...}}` from a sibling clause, so `{:error, _}` is a normal, already-handled shape here too). **Both call sites are already transparent to a new `{:error, _}` return with zero code changes** — the "grep every caller and thread the error through" caution in Task 3 Step 3 is correct discipline to keep but, on this checkout, resolves to "no caller needs editing"; state that in the report rather than treating it as open risk.
- `local_def_names/1` is public (`program.ex:153-154`).
- `{:ambiguous_name, _, _}` has NO `format_error/2` clause and no E-code in `lib/cure/compiler/errors.ex` yet (grep verified) — it currently hits the catch-all. E089 is free (grep-verified against the full `lib/cure/compiler/errors.ex` catalog: E080, E085, E087 exist; no E086/E088/E089 catalog entries — E086/E088 are warnings W086/W088, consistent with the spec's numbering note).
- **`resolve_qualified(env, name, :value)` does NOT consult `defs` today — verified both by reading `resolution.ex:190-195` and empirically.** Its `try_keys` presence predicate for the `:value` slot is `fn k -> not is_nil(Inductive.get_ctor(env, k)) end` (`resolution.ex:305`) — ctors only, never `env.defs`. Empirical proof (throwaway test against this checkout, since deleted — not part of this plan's deliverable): `mod P\n  use Std.Nat\n  fn f() -> Nat = Std.Nat.plus(S(Z()), Z())\nend\n` — a qualified call to the real, non-ctor stdlib function `plus/2` — elaborates to `{:error, :unknown_global}` on this checkout TODAY, independent of any collision. This falsifies the spec §2.2 rule 4 claim ("qualified CALL references always work... regardless of collisions") for the **def** case specifically (it is true for ctors, which is all today's tests exercise — grep of `test/` and `test/oracle/` for a qualified dotted call to a lower-case, non-ctor name returns zero hits). See Task 2 Step 4/5 below — this is corrected from "may already work, verify" to "does not work, two concrete gaps, both required."
- **`elaborate_named_call/5`'s qualified branch computes `resolved` (`elaborator.ex:238`) but only ONE downstream `cond` clause consults it: the ctor clause at `elaborator.ex:275` (`Inductive.get_ctor(env, resolved)`).** Every other clause (`ambiguous_modules(env, atom)` at 304, `implicit_def?(env, atom)` at 311, and the catch-all at 340-343, which re-elaborates via `elaborate_expr({:function_call, [name: name], args}, ...)` using the raw dotted `name`) uses the ORIGINAL `atom`/`name`, not `resolved`. So even after `resolve_qualified` is extended to also match `env.defs` (previous bullet), a qualified call to a plain def still has no `cond` clause that acts on the def-shaped `resolved` value — the catch-all recomputes from scratch via `resolve_free(name, env)` with the still-dotted `name`, which can never find a `Mod#name`-or-bare `defs` key literally spelled `"Mod.name"`. **A new `cond` clause is required in `elaborate_named_call`**, mirroring the existing ctor clause's shape but keyed on `Map.has_key?(env.defs, resolved)` — see Task 2 Step 5 (new).
- K12 probe file: `test/cure/elab/global_namespace_soundness_test.exs` (`check/1` helper: lex→parse→`Program.check_ast/1`). **`Cure.Elab.CrossModuleNamesTest` (read in full) is NOT the right precedent for Task 1's fixture** — it never imports across files at all: both its "sibling modules share a name" tests declare `mod A ... end mod B ... end` as TWO `mod` blocks in ONE source string, checked in one `Program.check_ast/1` call, no `use` anywhere. That mechanism cannot produce the `use A; use B` cross-file `merge_env` collision this design is about. The dependent elaborator's only import path (`import_source_path/1`, `program.ex:607-627`) resolves a source string of the exact shape `"Std.<Name>"` to `<Paths.source_dir()>/<downcase(Name)>.cure` — there is no user-facing "arbitrary local module" import, only `Std.*`. The REAL, already-established precedent for pointing that resolution at fixture files is the `Application.put_env(:cure, :stdlib_source_dir, tmp_dir)` + `on_exit` restore pattern used in `test/cure/stdlib/paths_test.exs` (setup/on_exit block, lines 9-30) and `test/cure/stdlib/preload_test.exs` — **not previously used in `test/cure/elab/` for a full elaboration run**. One load-bearing gotcha: `Paths.source_dir/0` is `List.first(source_dirs())` and `configured_source_dir()` (the `:stdlib_source_dir` override) is FIRST in that list — once set, it is the ONLY candidate consulted, with no fallback to the bundled/real stdlib dir for files it doesn't contain. Every module auto-imports `Std.Bool` and `Std.Nat` (`auto_prelude_imports/1`, `program.ex:246`, exercised by `test/cure/elab/auto_prelude_test.exs`) regardless of its own `use` list, so a tmp dir containing ONLY `colla.cure`/`collb.cure` breaks auto-prelude for every fixture module (`{:error, {:missing_stdlib_source, "Std.Bool", ...}}`) and the collision tests would fail for the wrong reason. Task 1 Step 1 is rewritten below to require copying the real stdlib source dir into the tmp override before adding the two fixture files.

---

### Task 1: Red tests — the gap, pinned at all three surfaces

**Files:**
- Modify: `test/cure/elab/global_namespace_soundness_test.exs` (append a new `describe "cross-module global collisions"`)

**Interfaces produced:** none (tests only — they encode §4.1/§4.2/§4.4 of the spec).

- [ ] **Step 1:** Build the cross-module fixture using the REAL precedent — `Application.put_env(:cure, :stdlib_source_dir, tmp_dir)` + `on_exit` restore, as done in `test/cure/stdlib/paths_test.exs` (setup/on_exit block) and `test/cure/stdlib/preload_test.exs` (NOT `cross_module_names_test.exs`, which declares sibling `mod` blocks in one source and never exercises cross-file `use` — it is not a precedent for this fixture at all). Concretely, in a `setup` block:
  1. `tmp = Path.join(System.tmp_dir!(), "cure_global_coll_test_#{System.unique_integer([:positive])}")`, `File.mkdir_p!(tmp)`.
  2. Copy the REAL stdlib source dir's contents into `tmp` (`File.cp_r!(Cure.Stdlib.Paths.source_dir(), tmp)`) BEFORE adding the fixture files — required because `Paths.source_dir/0` returns only the FIRST candidate in `source_dirs/0`, and the `:stdlib_source_dir` override is first in that list with no fallback: once set, every module's auto-prelude (`Std.Bool` + `Std.Nat`, `auto_prelude_imports/1`, exercised by `test/cure/elab/auto_prelude_test.exs`) resolves ONLY inside `tmp`, so omitting the copy breaks every fixture module with `{:error, {:missing_stdlib_source, "Std.Bool", ...}}` before the collision logic is ever reached.
  3. Write `Path.join(tmp, "colla.cure")` and `Path.join(tmp, "collb.cure")` (the lowercase filename convention `import_source_path/1` expects for `Std.CollA`/`Std.CollB`, `program.ex:607-627`), each `mod Std.CollA ... fn helper(x: Nat) -> Nat = ... end` (mirroring the real stdlib's own `mod Std.Nat` header convention — read one real stdlib file first, e.g. `lib/std/nat.cure`, to confirm the header shape) with observably different bodies: `Std.CollA.helper` returns `Z()`, `Std.CollB.helper` returns `S(Z())` — AND a certified-total-compatible shape (plain structural, no recursion). The `fixture_local_shadow()` helper (Step 2) additionally needs a LOCAL `helper(x: Nat) -> Nat = S(S(Z()))` in the importing (in-memory, not on disk) test module — a THIRD distinct shape, so the local-shadow test can tell "resolved to local" apart from "resolved to either import" (see Step 2's fix note). `colla.cure` ALSO needs a second, non-colliding function `lonely_helper(x: Nat) -> Nat` (any body) for `fixture_no_collision()` (Step 2's last test) — that fixture's importing module `use`s only `Std.CollA` (not `Std.CollB`), so `lonely_helper` has exactly one owner and must keep its bare key.
  4. `previous = Application.get_env(:cure, :stdlib_source_dir)`, `Application.put_env(:cure, :stdlib_source_dir, tmp)`, `on_exit(fn -> (case previous do nil -> Application.delete_env(:cure, :stdlib_source_dir); v -> Application.put_env(:cure, :stdlib_source_dir, v) end); File.rm_rf!(tmp) end)`.
  Async must be `false` for this describe block (`:stdlib_source_dir` is process-global `Application` state — same reasoning as the `paths_test.exs` moduledoc comment).
- [ ] **Step 2:** Append tests (adjust ONLY the fixture plumbing to match the mechanism found in Step 1; the assertions are immutable). **Finding fixed here:** the original draft's "qualified calls reach their own module's body" and "local def shadows the imports" tests asserted only `{:ok, _env}` — but since `helper`'s colliding bodies are all `Nat -> Nat` and equally well-typed, a WRONG resolution (e.g. the pre-fix last-merge-wins behavior, or a qualified call silently falling back to whichever bare `helper` happens to be in scope) would ALSO elaborate to `{:ok, _}`. A bare-success assertion cannot distinguish "reached the right body" from "reached A body" — exactly the class of silent-wrong-binding this whole design exists to close, so the test must not reproduce that blind spot. Fixed by giving each of the three bodies (`Std.CollA`, `Std.CollB`, and the local shadow) an OBSERVABLY DISTINCT constructor shape and asserting on the resolved `env.defs[key].body` directly — the same pattern already established by `test/cure/elab/bool_connective_lowering_test.exs` (`env.defs[name].body`), so this is consistent with house style, not a deviation into implementation internals: `add_def` stores the whole parameter-wrapped lambda as `body` (`Env.add_def(env, sig.name, sig.pi, lambda, ...)`, `lib/cure/elab/declarations.ex:61,84`), so for a single-param `fn helper(x: Nat) -> Nat = <ctor-expr>` the stored body is exactly `{:lam, _dom, <ctor-expr-core>}` — one `:lam` layer, verified against `Env.add_def/5`'s shape.

```elixir
  describe "cross-module global def collisions (design 2026-07-08)" do
    test "bare call of a doubly-imported name is an ambiguity error, not last-merge-wins" do
      # use Std.CollA + use Std.CollB, body: helper(Z())
      # TODAY: silently binds the last-merged helper -> {:ok, _}
      # AFTER: {:error, {:ambiguous_name, :helper, mods}} with both modules listed
      assert {:error, {:ambiguous_name, :helper, mods}} = check(fixture_bare_call())
      assert Enum.sort(mods) == ["Std.CollA", "Std.CollB"]
    end

    test "bare VALUE reference (higher-order arg) raises the same ambiguity error" do
      # fn ap(f: Nat -> Nat, x: Nat) -> Nat = f(x)  ... ap(helper, Z())
      assert {:error, {:ambiguous_name, :helper, _}} = check(fixture_bare_value())
    end

    test "qualified calls reach their own module's body despite the collision" do
      # Std.CollA.helper(x) = Z(); Std.CollB.helper(x) = S(Z()) (Step 1's fixture bodies).
      # A wrong resolution (e.g. both qualified calls silently landing on the same
      # slice) is well-typed too, so the assertion must inspect WHICH body each
      # qualified key resolved to, not just overall success.
      {:ok, env} = check(fixture_qualified_both())
      assert match?({:lam, _, {:ctor, :Z, []}}, env.defs[:"Std.CollA#helper"].body)
      assert match?({:lam, _, {:ctor, :S, [{:ctor, :Z, []}]}}, env.defs[:"Std.CollB#helper"].body)
    end

    test "local def shadows the imports; qualified still reaches them" do
      # Local helper(x) = S(S(Z())) -- a THIRD shape, distinct from both imports',
      # so a bare call resolving to the local body (correct) is distinguishable
      # from it resolving to either import's body (the bug this design fixes).
      {:ok, env} = check(fixture_local_shadow())
      assert match?({:lam, _, {:ctor, :S, [{:ctor, :S, [{:ctor, :Z, []}]}]}}, env.defs[:helper].body)
      assert match?({:lam, _, {:ctor, :Z, []}}, env.defs[:"Std.CollA#helper"].body)
      assert match?({:lam, _, {:ctor, :S, [{:ctor, :Z, []}]}}, env.defs[:"Std.CollB#helper"].body)
    end

    test "non-colliding imported defs keep bare keys (no blanket re-keying)" do
      {:ok, env} = check(fixture_no_collision())
      assert Map.has_key?(env.defs, :lonely_helper)
      refute Enum.any?(Map.keys(env.defs), fn k ->
               String.ends_with?(Atom.to_string(k), "#lonely_helper")
             end)
    end
  end
```

The `describe` block's `setup` (Step 1) supplies `tmp`; each `fixture_*` helper writes its own `mod ... use Std.CollA\n  use Std.CollB ... end` source string as a plain function returning that string (no additional file I/O — only `colla.cure`/`collb.cure` live on disk; the importing test module itself is an ordinary in-memory source passed to `check/1`, exactly like every other test in this file). If the actual stored `body` shape observed when these tests are first run differs from the single-`:lam`-layer prediction above (e.g. an extra wrapping this review didn't anticipate), that is grounds to fix the ASSERTION'S shape to match reality, per the plan's own immutability escape hatch — not to weaken it back to a bare `{:ok, _}` check, which would silently reintroduce the blind spot this fix exists to close.

- [ ] **Step 3:** Run: `mix test test/cure/elab/global_namespace_soundness_test.exs 2>&1 | tail -15`
Expected red: the two ambiguity tests FAIL (today `check` returns `{:ok, _}` — the silent overwrite — or an unrelated error; record which). **The "qualified calls reach their own module's body" test is ALSO expected to fail at this point, for a distinct, already-verified reason** — `resolve_qualified(env, name, :value)` only matches ctors today (never `env.defs`), and empirically a qualified call to a real, non-ctor stdlib function (`Std.Nat.plus(...)`) returns `{:error, :unknown_global}` on this checkout independent of collisions (see Global Constraints ground truth). Do not expect this test to go green until Task 2 Steps 4-5 land — record the actual failure (`:unknown_global` or similar) so the red is attributed correctly rather than assumed to be collision-related. The local-shadow and no-collision tests may pass or fail depending on current bare-resolution handling — record the actual split; any currently-green test is regression cover, not a red gate.
- [ ] **Step 4:** Commit: `git add test/cure/elab/global_namespace_soundness_test.exs && git commit -m "test(elab): pin cross-module global-def collision gap (red)"` — committing red tests as their own commit before the fix lands is this repo's established discipline, not a deviation: recent history has multiple standalone red/pin commits later followed by fix commits (e.g. `38f63ec test(shadow): red repro for local Nat shadowing missing_branch bug`, `24c9832 test(elab): pin global/ctor name-collision soundness + record decline`). The suite gate at the end of Task 4 is where everything must be green.

### Task 2: Re-keying — ownership scan, classify, rekey defs + certified

**Files:**
- Modify: `lib/cure/elab/program.ex` (`shadow_resolved_imports/1`, new `owned_def_names/1`)
- Modify: `lib/cure/elab/resolution.ex` (`rekey_module_env/4` → also move def keys + `certified`; `classify/2` reused as-is — it is shape-generic over `%{name => owners}`, verified: it only pattern-matches on the `%{name => MapSet.t(owner)}` shape and a `MapSet` of local names, nothing family-specific; `resolve_qualified/3`'s `:value` clause extended to match `defs`)
- Modify: `lib/cure/elab/elaborator.ex` (`elaborate_named_call/5` gains a new `cond` clause for qualified-def calls — Step 5; this is IN ADDITION TO Task 3's separate `resolve_free/2` changes, different function)

**Interfaces:**
- Produces: `rekey_module_env(env, module_id, owned_family_names, shadowed_ctor_names, owned_def_names)` (new 5th arg, defaulted `MapSet.new()` so existing callers/tests are unaffected), which additionally: adds `owned_def_names ∩ collision set` to `amap`, moves those `defs` KEYS via the amap, and rebuilds `certified` membership through the amap.
- Produces: `resolve_qualified(env, name, :value)` now also resolves to a `defs` key (Step 4), and `elaborate_named_call/5` now dispatches on that key for a qualified, non-ctor call (Step 5) — together these make `A.foo(x)` work for plain functions for the first time, independent of collisions (previously ctor-only).

- [ ] **Step 1:** In `program.ex`, add `owned_def_names/1` next to `owned_family_names/1` (`:489`), mirroring its file-read/lex/parse wrapper shape exactly, but for the name-extraction step REUSE the existing public `local_def_names/1` (`program.ex:154-167`, verified: already takes an `ast` and returns `[atom()]` of `:function_def` names) instead of writing a new scanner — `owned_family_names` uses the private `declared_type_names/1` only because no public equivalent already existed for types; for defs, `local_def_names/1` already IS that function. `owned_def_names(path)` is therefore just `owned_family_names/1`'s parse wrapper with `local_def_names(ast)` (wrapped in `MapSet.new/1`) substituted for `declared_type_names(ast)`.
- [ ] **Step 2:** In `shadow_resolved_imports/1`, build `def_owners` exactly parallel to `family_owners` (same transitive walk — do it in the SAME `Enum.reduce` pass to avoid re-walking), classify against `MapSet.new(local_def_names(ast))`, union the def losers into the per-slice re-key call (pass as the new 5th arg), and union def collisions into the residual-cleanup set ONLY if a `drop_bare_def` analog proves necessary (first try without it; the family `drop_bare_family` exists because of seeded builtins — defs have no seeding, so residual bare copies should not arise. If the Task 1 no-collision test fails from residue, add the analog and note it).
- [ ] **Step 3:** In `resolution.ex` `rekey_module_env`, extend `amap` with the owned-and-colliding def names, change `rekey_defs/2` to ALSO move keys present in `amap` (today it only rewrites references inside values — keep that, add the key move), and add `certified: rekey_certified(env.certified, amap)` to the returned struct (`MapSet` map-through). Update the moduledoc sentence "Functions keep their bare `defs` keys." — it becomes false.
- [ ] **Step 4:** Extend `resolve_qualified(env, name, :value)` (`resolution.ex:190-195`, via its `try_keys` presence predicate at `resolution.ex:301-306`) so the `:value` slot ALSO matches `env.defs`, not only `Inductive.get_ctor/2`. **This is required, not conditional** — verified on this checkout (Global Constraints ground truth) that today it does not: a qualified call to a real, non-ctor stdlib function (`Std.Nat.plus(...)`) elaborates to `{:error, :unknown_global}` independent of any collision. Change the `:value` predicate to `fn k -> not is_nil(Inductive.get_ctor(env, k)) or Map.has_key?(env.defs, k) end` (or equivalent), so `resolve_qualified` returns the rekeyed-or-bare `defs` key when one exists.
- [ ] **Step 5 (new):** Extending `resolve_qualified` alone is not sufficient — `elaborate_named_call/5`'s `cond` (`elaborator.ex:253-365`) only acts on the qualified `resolved` value in the ctor clause (`elaborator.ex:275`, `Inductive.get_ctor(env, resolved)`); every later clause (`ambiguous_modules(env, atom)`, `implicit_def?(env, atom)`, the catch-all) uses the original `atom`/`name`, so a qualified def call still falls through to the catch-all, which re-elaborates from the raw dotted `name` via `resolve_free/2` and can never find a `Mod#name`/bare key spelled with a literal `.`. Add a new `cond` clause — placed after the ctor clause, before the `ambiguous_modules` check — keyed on `Map.has_key?(env.defs, resolved)`, that elaborates the call against `resolved` directly (mirror the existing ctor clause's argument-elaboration shape, or reuse `elaborate_global_app/4` the same way the `implicit_def?` clause does at `elaborator.ex:311-315`, just supplying `resolved` instead of `atom`). Red test: Task 1's "qualified calls reach their own module's body despite the collision" test (still failing after Step 4 alone, per Task 1 Step 3's note) is the gate — do not mark Task 2 done while it is red.
- [ ] **Step 6:** Run the Task 1 file. Expected: qualified/no-collision/local tests now green (Steps 4-5 are what make the qualified-call test pass — it does not "already work"). The two ambiguity tests stay red (bare resolution sites not wired yet — that is Task 3).
- [ ] **Step 7:** Commit: `feat(elab): re-key colliding global defs across module slices + qualified-def call resolution (Approach B)`

### Task 3: Ambiguity trichotomy at both resolution sites + E089

**Files:**
- Modify: `lib/cure/elab/resolution.ex` (`ambiguous_modules/2` consults defs too; `resolve_bare_shadowed/2` returns the unique re-keyed def when exactly one import provides it)
- Modify: `lib/cure/elab/elaborator.ex` (`elaborate_named_call/5` — the existing R7 check now fires for defs via the generalized `ambiguous_modules`; `resolve_free/2` — add the same check + unique-import mapping before the `{:global, atom}` fallthrough)
- Modify: `lib/cure/compiler/errors.ex` (E089 `format_error` clause + catalog entry for `{:ambiguous_name, name, modules}`)
- Test: `test/cure/compiler/dep_graph_errors_format_test.exs`-style new file NOT needed — add the formatter test into `test/cure/elab/global_namespace_soundness_test.exs` describe, asserting `Errors.format_error({:ambiguous_name, :helper, ["Std.CollA", "Std.CollB"]}, "x.cure")` mentions `E089`, both modules, and the qualified-form hint.

- [ ] **Step 1:** Generalize `ambiguous_modules/2`: same suffix scan over `Map.keys(env.defs)` unioned with the existing families scan (still `[]` when the bare key exists in EITHER map — a winner exists). Keep the spec `@doc` honest about both namespaces. Note (non-goal, not a red test): the union means a bare name could theoretically be reported ambiguous from a rekeyed FAMILY in one module colliding (by spelling only) with an unrelated rekeyed DEF in another — families and defs are classified independently (separate owner maps, Task 2 Step 2), so this is a real cross-namespace coincidence, not prevented by construction. It is not addressed here: Cure's convention is capitalized type/family names vs lowercase def names, making the spelling collision practically impossible, and the existing landed decision that same-named fn/ctor coexistence is accepted (within one module, `global_namespace_soundness_test.exs`) already establishes that cross-namespace name reuse is a supported pattern this design does not tighten.
- [ ] **Step 2:** `resolve_bare_shadowed/2` (`resolution.ex:224`): extend to defs — when `bare` is absent from `defs` but exactly ONE `Mod#bare` def key exists, return `{:ok, that_key}` (mirrors the family/ctor unique-loser rule; read the existing clauses first and follow their exact precedence).
- [ ] **Step 3:** `resolve_free/2` in `elaborator.ex`: before the final fallthrough, mirror the trichotomy:

```elixir
  defp resolve_free(name, env) do
    atom = String.to_atom(name)

    cond do
      Inductive.get_ctor(env, atom) -> {:ok, {:ctor, atom, []}}
      Inductive.family?(env, atom) -> {:ok, {:data, atom, [], []}}
      length(Cure.Elab.Resolution.ambiguous_modules(env, atom)) >= 2 ->
        {:error, {:ambiguous_name, atom, Cure.Elab.Resolution.ambiguous_modules(env, atom)}}
      true ->
        case Cure.Elab.Resolution.resolve_bare_shadowed(env, atom) do
          {:ok, key} -> {:ok, {:global, key}}
          _ -> {:ok, {:global, atom}}
        end
    end
  end
```

CAUTION (resolved — verified, not open): `resolve_free/2` has exactly two callers on this checkout (see Global Constraints ground truth), and both already propagate `{:error, _}` transparently — `elaborate_expr_typed/4`'s `{:variable,...}` clause via a `with` chain, `elaborate_expr/3`'s `{:variable,...}` clause as a direct `case` return, both functions' own `@spec`/sibling clauses already returning `{:error, _}` shapes. No caller edit is needed for this change; still re-grep at implementation time in case an intervening commit added a new caller, but do not budget time for "widening" work that this checkout does not require.
- [ ] **Step 4:** E089 in errors.ex: `format_diagnostic("error", "ambiguous name (E089)", file, 1, "…'#{name}' is provided by #{Enum.join(modules, " and ")}; qualify the call (e.g. #{hd(modules)}.#{name}(...)) or define a local #{name} to shadow them.")` + catalog `"E089"` entry in neighboring prose style. **Placement is load-bearing, verified against this checkout**: `format_error/2` is a sequence of pattern-matched function clauses (one per error shape, `errors.ex:21-368`) ending in a generic catch-all at `errors.ex:372` (`def format_error(error, file) do ... "compilation error" ... end`, immediately followed by an unrelated `@doc`-catalog section at `errors.ex:378`). Elixir tries clauses in source order, so the new `format_error({:ambiguous_name, name, modules}, file)` clause MUST be inserted BEFORE line 372 (e.g. right after the `:unresolved_import` clause, before the `# -- Catch-all --` comment) — appending it after the catch-all (the more natural-looking place to "add a clause" at the bottom of the module) would compile fine but the clause would NEVER be reached, since the catch-all pattern matches unconditionally first. The E089 catalog entry (a separate lookup map/attribute, unaffected by clause order) has no such constraint.
- [ ] **Step 5:** Run the Task 1 test file → ALL green now. Then the formatter test → green.
- [ ] **Step 6:** Commit: `feat(elab): E089 ambiguous-name trichotomy at call and bare-value resolution (defs join families)`

### Task 4: Certificate survival + full gate

**Files:**
- Modify: `test/cure/elab/global_namespace_soundness_test.exs` (append the certificate test, spec §4.3)

- [ ] **Step 1:** Append this test INSIDE the same `describe "cross-module global def collisions (design 2026-07-08)"` block from Task 1 (reuse its `setup`/`tmp`/override — do not stand up a second `stdlib_source_dir` override in the same file). Either add a certified-total colliding function to the existing `colla.cure`/`collb.cure` fixtures or extend them with one, structured so the fixture module's def gets a certificate (mirror how existing totality/conversion tests arrange certification — see `test/cure/elab/totality_closure_test.exs` and `test/cure/elab/totality_wiring_test.exs` for the established pattern) and whose UNFOLDING is required for a conversion to succeed in the importing module via its QUALIFIED name. Assert `{:ok, _}`. Red check: temporarily assert against current behavior only if the test can be written red-first (if re-keying already carries certified from Task 2, this is regression cover — say so rather than manufacturing a fake red).
- [ ] **Step 2:** Full gate, sequential: `mix test 2>&1 | tail -5` (expect 0 failures), `mix cure.check.examples 2>&1 | tail -2` (expect 44 passed).
- [ ] **Step 3:** Commit: `test(elab): certificate survives global-def re-keying + gate`

## Self-review notes

- Spec §2.1 → Task 2 Steps 1-3 (incl. the certified MapSet step the spec calls out); §2.2 rules 1-3 both sites → Task 3; §2.2 rule 4 (qualified) → Task 2 Steps 4-5, REQUIRED (verified NOT already working for defs — see Global Constraints — corrected from the spec's "always works" framing, which is only true for ctors); §3 table → Tasks 2/3; §4.1-4.5 → Tasks 1/3/4; §4.6 → Task 4.
- The `{:ambiguous_name, name, mods}` tuple shape is IDENTICAL to the existing family R7 error — one concept, one formatter (E089), zero new tuple shapes.
- Unknowns surfaced to the implementer that this review COULD resolve by reading code, and did — not left as guesses: the cross-module fixture mechanism (Task 1 Step 1 — `cross_module_names_test.exs` is NOT usable as a precedent; the real mechanism is the `:stdlib_source_dir` override + a copied real stdlib dir, verified against `test/cure/stdlib/paths_test.exs`/`preload_test.exs`), `resolve_free` caller safety (verified exactly 2 callers, both already error-transparent — no widening work needed), qualified-def call resolution (verified broken today via an empirical throwaway test — `Std.Nat.plus(...)` → `:unknown_global` — and traced to two concrete gaps: `resolve_qualified/3`'s ctor-only `:value` predicate, and `elaborate_named_call/5` never consulting `resolved` outside the ctor clause; both are now required Task 2 steps with the qualified-call test as their red gate).
- Remaining genuine unknown, left for the implementer (not resolvable by static reading alone): residual-cleanup necessity for defs (Task 2 Step 2's `drop_bare_def` contingency) — depends on runtime behavior of the no-collision test, which requires actually running the suite mid-implementation.
