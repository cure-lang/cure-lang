# `@group` Decorator Placement Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Move `@group(:core)` from inside the `mod` body to immediately above the `mod` declaration, where a decorator unambiguously annotates the module it precedes.

**Architecture:** Expand → migrate → contract. First teach the parser to attach a pre-`mod` `@group` to the module container and teach `compiler.ex` to read the group from that container meta (both *additive* — the in-body form still works). Then migrate all 13 stdlib files. Only then flip the in-body form to a hard parse error. Every task leaves a green tree; the end state is the hard cutover the spec mandates.

**Tech Stack:** Elixir; Cure's hand-written lexer/parser (`lib/cure/compiler/parser.ex`), the shared compile driver (`lib/cure/compiler.ex`), the stdlib preload machinery (`lib/cure/stdlib/preload.ex`). ExUnit.

## Global Constraints

- Ghost-writer commits: `git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>"`; NO `Co-Authored-By`, no Claude signature.
- Explicit-pathspec staging only: `git add -- <path>`; NEVER `git add -A`/`git add .`. New files are `git add -- <path>` first.
- One `mix` build at a time. Prefer scoped `mix test <file>`; run the full suite once, alone, at the gate.
- This work is the shared frontend (`lib/cure/compiler/parser.ex`) + the classic compile driver (`lib/cure/compiler.ex`) + stdlib sources — NOT the dependent kernel. No `lib/cure/core/*` edits in this plan, so no TCB gate applies here.
- Tests are behavioral and immutable once green.

---

### Task 1: Parser attaches a pre-`mod` `@group` to the module (additive)

Teach `parse_at/1` that when a module-level decorator (`@group`) is immediately followed by a `mod` keyword, it parses the module and attaches the decorator to the module container's meta. When NOT followed by `mod`, behavior is unchanged (standalone node) — so the in-body form keeps working this task.

**Files:**
- Modify: `lib/cure/compiler/parser.ex:4910-4919` (the `@module_level_decorators` branch inside `parse_at/1`)
- Test: `test/cure/compiler/group_decorator_test.exs` (create)

**Interfaces:**
- Consumes: `parse_module/1` (`parser.ex:2833`, returns `{{:container, meta, body}, state}`); `attach_decorator/3` generic container clause (`parser.ex:4977-4978`, writes `Keyword.put(meta, :decorator, {String.to_atom(dec_name), args})`).
- Produces: for source `@group(:core)\nmod M\n…\nend`, a single top-level `{:container, meta, body}` where `Keyword.get(meta, :decorator) == {:group, [{:literal, _, :core}]}`.

- [ ] **Step 1: Write the failing test**

Create `test/cure/compiler/group_decorator_test.exs`:

```elixir
defmodule Cure.Compiler.GroupDecoratorTest do
  @moduledoc """
  `@group(:g)` placed ABOVE `mod` attaches to the module container (spec
  2026-07-10-group-decorator-placement). This test file grows across the
  expand→migrate→contract tasks; Task 4 adds the hard-error case.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}

  # Parse a source string to the top-level AST list, asserting no parse errors.
  defp parse!(src) do
    {:ok, tokens} = Lexer.tokenize(src)
    {ast, %{errors: []}} = Parser.parse_program(tokens)
    ast
  end

  # The module container node in a parsed program (unwraps a {:block, _, items}).
  defp module_node(ast) do
    items = case ast do
      {:block, _, xs} -> xs
      xs when is_list(xs) -> xs
      other -> [other]
    end
    Enum.find(items, &match?({:container, meta, _} when is_list(meta), &1))
  end

  test "@group above mod attaches the group to the module container meta" do
    ast = parse!("@group(:core)\nmod M\n  fn f(x: Int) -> Int = x\nend\n")
    {:container, meta, _body} = module_node(ast)
    assert {:group, [{:literal, _, :core}]} = Keyword.get(meta, :decorator)
  end
end
```

- [ ] **Step 2: Verify the exact entry points before coding**

Run: `grep -n "def parse_program\|def tokenize\|def parse\b" lib/cure/compiler/parser.ex lib/cure/compiler/lexer.ex`
If `parse_program/1` or `tokenize/1` differ in name/return shape, adjust `parse!/1` in the test to match the real public API (do this now, before running — the harness for the frontend is stable, only the entry names may differ). Confirm the parsed program is a `{:block, _, items}` or bare list and fix `module_node/1` accordingly.

- [ ] **Step 3: Run the test to verify it fails**

Run: `mix test test/cure/compiler/group_decorator_test.exs`
Expected: FAIL — the module node's meta has no `:decorator` key (today `@group` becomes a standalone sibling node, so `Keyword.get(meta, :decorator)` is `nil`).

- [ ] **Step 4: Implement the pre-`mod` attach**

In `lib/cure/compiler/parser.ex`, replace the `@module_level_decorators` branch (currently lines 4914-4916):

```elixir
    # Module-level decorators (e.g. `@group(:core)`) describe the module, not
    # the next declaration. They always stand alone, whatever follows.
    if dec_name in @module_level_decorators do
      ast = {:decorator, [name: dec_name, line: token.line, col: token.col], args}
      {ast, state}
    else
      parse_at_attach(state, token, dec_name, args)
    end
```

with:

```elixir
    # Module-level decorators (e.g. `@group(:core)`) describe the MODULE. The
    # canonical form is `@group(:g)` directly above `mod`, where it attaches to
    # the module container (spec 2026-07-10-group-decorator-placement). Any
    # other position still parses as a standalone node here (Task 4 will make
    # that a hard error, once the stdlib is migrated).
    if dec_name in @module_level_decorators do
      case peek(state) do
        %Token{type: :keyword, value: :mod} ->
          {mod_ast, state} = parse_module(state)
          {attach_decorator(mod_ast, dec_name, args), state}

        _ ->
          ast = {:decorator, [name: dec_name, line: token.line, col: token.col], args}
          {ast, state}
      end
    else
      parse_at_attach(state, token, dec_name, args)
    end
```

- [ ] **Step 5: Run the test to verify it passes**

Run: `mix test test/cure/compiler/group_decorator_test.exs`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add -- lib/cure/compiler/parser.ex test/cure/compiler/group_decorator_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(parser): attach a pre-mod @group decorator to the module container"
```

---

### Task 2: `compiler.ex` reads the group from the container meta

The `-group([:g])` BEAM attribute is spliced by `inject_group_attribute/2` via `group_atoms/1`, which today only finds a standalone `{:decorator, name: "group"}` node. Add a clause that also reads the group from a module container's attached `:decorator` meta, so the above-`mod` form still emits the attribute. Additive — the standalone clause stays this task.

**Files:**
- Modify: `lib/cure/compiler.ex:334-347` (`group_atom/1` + `group_atoms/1`)
- Test: `test/cure/compiler/group_attribute_test.exs` (create)

**Interfaces:**
- Consumes: the container meta shape from Task 1 — `Keyword.get(meta, :decorator) == {:group, [{:literal, _, atom}]}`.
- Produces: `Cure.Compiler` still splices `{:attribute, 1, :group, [atom]}` into the compiled forms for a module whose group is attached above `mod`.

- [ ] **Step 1: Write the failing test**

Create `test/cure/compiler/group_attribute_test.exs`:

```elixir
defmodule Cure.Compiler.GroupAttributeTest do
  @moduledoc """
  The `-group([:g])` BEAM attribute is emitted whether `@group` is attached
  above `mod` (container meta) or, transitionally, as an in-body standalone
  node. Guards `Cure.Compiler.inject_group_attribute/2` (spec
  2026-07-10-group-decorator-placement).
  """
  use ExUnit.Case, async: true

  # Compile a Cure source string to Erlang abstract forms and return them.
  # (Verify the real entry point in Step 2 and adjust if the name differs.)
  defp forms!(src) do
    {:ok, forms, _warnings} = Cure.Compiler.compile_to_forms(src)
    forms
  end

  defp group_attr(forms) do
    Enum.find_value(forms, fn
      {:attribute, _, :group, [g]} -> g
      _ -> nil
    end)
  end

  test "above-mod @group still emits the -group BEAM attribute" do
    forms = forms!("@group(:sensors)\nmod M\n  fn f(x: Int) -> Int = x\nend\n")
    assert group_attr(forms) == :sensors
  end
end
```

- [ ] **Step 2: Find the real compile-to-forms entry point**

Run: `grep -n "def compile\|inject_group_attribute\|{:ok, forms" lib/cure/compiler.ex`
`compile_to_forms/1` is a placeholder name. Identify the public function that returns `{:ok, forms, warnings}` with `forms` a list of Erlang abstract forms (the one whose `{:ok, forms, warnings} when is_list(forms)` result feeds `inject_group_attribute/2` at `compiler.ex:308-310`). Update `forms!/1` in the test to call it. If the public API only exposes a full `compile/2` that writes a `.beam`, instead test `Cure.Compiler.inject_group_attribute/2` directly by making it (or a thin wrapper) reachable — but first prefer a real compile entry that returns forms.

- [ ] **Step 3: Run the test to verify it fails**

Run: `mix test test/cure/compiler/group_attribute_test.exs`
Expected: FAIL — `group_atoms/1` does not descend into container `:decorator` meta, so no `:group` attribute is emitted and `group_attr(forms)` is `nil`.

- [ ] **Step 4: Add a container-meta clause to `group_atoms/1`**

In `lib/cure/compiler.ex`, add this clause immediately BEFORE the generic `group_atoms({_tag, _meta, children})` clause (currently `compiler.ex:343-344`):

```elixir
  # A module container with `@group(:g)` attached above `mod` carries the group
  # in its meta (`decorator: {:group, [{:literal, _, atom}]}`). Read it there,
  # then still descend into the body for the transitional standalone form.
  defp group_atoms({:container, meta, children}) when is_list(meta) and is_list(children) do
    from_meta =
      case Keyword.get(meta, :decorator) do
        {:group, [{:literal, _, atom}]} when is_atom(atom) -> [atom]
        _ -> []
      end

    from_meta ++ Enum.flat_map(children, &group_atoms/1)
  end
```

- [ ] **Step 5: Run the test to verify it passes**

Run: `mix test test/cure/compiler/group_attribute_test.exs`
Expected: PASS.

- [ ] **Step 6: Run the parser test too (no regression)**

Run: `mix test test/cure/compiler/group_decorator_test.exs test/cure/compiler/group_attribute_test.exs`
Expected: PASS (both).

- [ ] **Step 7: Commit**

```bash
git add -- lib/cure/compiler.ex test/cure/compiler/group_attribute_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(compiler): emit -group BEAM attribute from above-mod @group container meta"
```

---

### Task 3: Migrate all 13 stdlib files to the above-`mod` form

Move `@group(:core)` from inside the body to immediately above `mod` in every stdlib source that uses it. Both forms parse right now (Tasks 1-2 were additive), so this task leaves a green tree and is verifiable independently.

**Files (Modify):** each of these, relocating its `@group(:core)` line to directly above its `mod` line:
`lib/std/functor.cure`, `lib/std/bool.cure`, `lib/std/ord.cure`, `lib/std/equatable.cure`, `lib/std/bounded.cure`, `lib/std/equivalent.cure`, `lib/std/core.cure`, `lib/std/decision.cure`, `lib/std/sigma.cure`, `lib/std/binary.cure`, `lib/std/nat.cure`, `lib/std/proof.cure`, `lib/std/show.cure`
- Test: `test/cure/stdlib/group_placement_test.exs` (create)

**Interfaces:**
- Consumes: nothing new.
- Produces: every `lib/std/*.cure` file that contains `@group(` has it on a line whose next non-blank line is the `mod` declaration.

- [ ] **Step 1: Write the failing structural test**

Create `test/cure/stdlib/group_placement_test.exs`:

```elixir
defmodule Cure.Stdlib.GroupPlacementTest do
  @moduledoc """
  Every stdlib source that declares `@group(:g)` places it ABOVE its `mod`
  line, not inside the body (spec 2026-07-10-group-decorator-placement). This
  is the migration guard: it goes red if any file keeps the legacy in-body
  placement.
  """
  use ExUnit.Case, async: true

  @std_dir Path.join([File.cwd!(), "lib", "std"])

  test "no stdlib file has @group inside the mod body" do
    offenders =
      @std_dir
      |> Path.join("*.cure")
      |> Path.wildcard()
      |> Enum.filter(&group_below_mod?/1)

    assert offenders == [],
           "these stdlib files still have @group inside the mod body: " <>
             Enum.map_join(offenders, ", ", &Path.basename/1)
  end

  # True iff the file's `@group(` line appears AFTER its `mod ` line.
  defp group_below_mod?(path) do
    lines = path |> File.read!() |> String.split("\n")
    group_idx = Enum.find_index(lines, &(&1 =~ ~r/^\s*@group\(/))
    mod_idx = Enum.find_index(lines, &(&1 =~ ~r/^\s*mod\s/))
    group_idx != nil and mod_idx != nil and group_idx > mod_idx
  end
end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/cure/stdlib/group_placement_test.exs`
Expected: FAIL — the assertion lists all 13 files (each currently has `@group` below `mod`).

- [ ] **Step 3: Migrate each file**

For every file listed above, cut its `@group(:core)` line (and the blank line that follows it, if any) from the body and paste `@group(:core)` on its own line immediately above `mod <Name>`. Example for `lib/std/nat.cure`:

Before:
```cure
mod Std.Nat
  ## docs …

  @group(:core)

  ...
```
After:
```cure
@group(:core)
mod Std.Nat
  ## docs …

  ...
```

Do this for all 13. Leave every other line untouched (docs, `use`, decorators like `@builtin`, definitions).

- [ ] **Step 4: Run the migration guard to verify it passes**

Run: `mix test test/cure/stdlib/group_placement_test.exs`
Expected: PASS (offenders empty).

- [ ] **Step 5: Verify the groups still resolve (both consumer paths)**

Run: `mix test test/cure/compiler/group_decorator_test.exs test/cure/compiler/group_attribute_test.exs`
Expected: PASS. Then confirm the preload association is intact:
Run: `mix run -e 'IO.inspect(Map.get(Cure.Stdlib.Preload.module_groups(), :"Cure.Std.Binary"))'`
Expected: prints `:core`.

- [ ] **Step 6: Commit**

```bash
git add -- lib/std/functor.cure lib/std/bool.cure lib/std/ord.cure lib/std/equatable.cure lib/std/bounded.cure lib/std/equivalent.cure lib/std/core.cure lib/std/decision.cure lib/std/sigma.cure lib/std/binary.cure lib/std/nat.cure lib/std/proof.cure lib/std/show.cure test/cure/stdlib/group_placement_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "refactor(std): move @group above mod in all stdlib modules"
```

---

### Task 4: Contract — make an out-of-place `@group` a hard error

Now that no stdlib file uses the in-body form, flip it to a hard parse error: `@group` is only valid directly above `mod`. This is the cutover the spec mandates.

**Files:**
- Modify: `lib/cure/compiler/parser.ex` (the `@module_level_decorators` branch from Task 1)
- Modify: `lib/cure/compiler.ex:338-341` (drop the now-dead standalone `group_atoms` clause)
- Test: `test/cure/compiler/group_decorator_test.exs` (add a case)

**Interfaces:**
- Consumes: `add_error/2` (`parser.ex:5386`, accumulates `{...}` into `state.errors` and returns the state).
- Produces: a program containing an in-body (or otherwise non-pre-`mod`) `@group` parses with a non-empty `state.errors`.

- [ ] **Step 1: Write the failing test**

Add to `test/cure/compiler/group_decorator_test.exs`:

```elixir
  # Parse and RETURN errors instead of asserting none.
  defp parse_errors(src) do
    {:ok, tokens} = Lexer.tokenize(src)
    {_ast, state} = Parser.parse_program(tokens)
    state.errors
  end

  test "an in-body @group is a hard parse error" do
    src = "mod M\n  @group(:core)\n  fn f(x: Int) -> Int = x\nend\n"
    errors = parse_errors(src)
    assert Enum.any?(errors, &match?({:group_not_above_module, _, _}, &1)),
           "expected a :group_not_above_module error, got: #{inspect(errors)}"
  end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/cure/compiler/group_decorator_test.exs`
Expected: FAIL on the new case — today an in-body `@group` parses to a standalone node with no error.

- [ ] **Step 3: Flip the non-pre-`mod` branch to a hard error**

In `lib/cure/compiler/parser.ex`, change the `_ ->` arm added in Task 1 from emitting a standalone node to recording an error:

```elixir
    if dec_name in @module_level_decorators do
      case peek(state) do
        %Token{type: :keyword, value: :mod} ->
          {mod_ast, state} = parse_module(state)
          {attach_decorator(mod_ast, dec_name, args), state}

        other ->
          # `@group` is only valid directly above `mod` (spec
          # 2026-07-10-group-decorator-placement). Anywhere else is an error.
          state = add_error(state, {:group_not_above_module, other.line, other.col})
          ast = {:decorator, [name: dec_name, line: token.line, col: token.col], args}
          {ast, state}
      end
    else
      parse_at_attach(state, token, dec_name, args)
    end
```

(The placeholder `{:decorator, …}` node is still returned so parsing can continue and collect further errors; the non-empty `state.errors` is what fails the parse.)

- [ ] **Step 4: Run the test to verify it passes**

Run: `mix test test/cure/compiler/group_decorator_test.exs`
Expected: PASS (all three cases: attach, and the new hard-error, plus Task 1's).

- [ ] **Step 5: Drop the dead standalone `group_atoms` clause**

In `lib/cure/compiler.ex`, remove the now-unreachable standalone-decorator clause (`compiler.ex:338-341`):

```elixir
  defp group_atoms({:decorator, meta, [{:literal, _, atom}]})
       when is_list(meta) and is_atom(atom) do
    if Keyword.get(meta, :name) == "group", do: [atom], else: []
  end
```

The container-meta clause from Task 2 is now the sole group source. Keep the generic `{_tag, _meta, children}` and list clauses.

- [ ] **Step 6: Run the group + attribute tests**

Run: `mix test test/cure/compiler/group_decorator_test.exs test/cure/compiler/group_attribute_test.exs test/cure/stdlib/group_placement_test.exs`
Expected: PASS (all).

- [ ] **Step 7: Full suite gate**

Run: `mix test`
Expected: all green (the stdlib parses with the above-`mod` form; no in-body `@group` remains). If any non-stdlib fixture used an in-body `@group`, migrate it the same way and re-run — that is the only expected fallout.

- [ ] **Step 8: Commit**

```bash
git add -- lib/cure/compiler/parser.ex lib/cure/compiler.ex test/cure/compiler/group_decorator_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(parser): reject @group anywhere but directly above mod (hard cutover)"
```

---

## Self-Review

**Spec coverage:**
- Spec §Design 1 (parser attach + reject elsewhere) → Task 1 (attach) + Task 4 (reject). ✓
- Spec §Design 2 (codegen emits `-group` from container meta) → Task 2. ✓
- Spec §Design 3 (migrate 13 files) → Task 3 (all 13 named). ✓
- Spec §Design 4 (hard cutover, no back-compat) → Task 4. ✓
- Spec §Testing (parser test, association via `module_groups`, migration guard, full suite) → Task 1/4 (parser), Task 3 Step 5 (`module_groups`), Task 3 (guard), Task 4 Step 7 (full suite). ✓
- Spec §Testing BEAM-attribute path (`group_from_beam`) → covered by Task 2 (the attribute is emitted); the `module_groups` regex path is position-agnostic and confirmed in Task 3 Step 5. ✓

**Placeholder scan:** Two test helpers (`parse!`/`forms!`) name entry points (`parse_program`, `compile_to_forms`) that Step 2 of their tasks explicitly verifies against the real API before running — these are guarded, not placeholders. No TODO/TBD.

**Type consistency:** The container meta shape `{:group, [{:literal, _, atom}]}` is produced by Task 1 (`attach_decorator` → `{String.to_atom("group"), args}` = `{:group, args}`), consumed identically by Task 2 (`group_atoms` container clause) and referenced by Task 4. The error tuple `{:group_not_above_module, line, col}` is produced in Task 4 Step 3 and matched in Task 4 Step 1. Consistent.
