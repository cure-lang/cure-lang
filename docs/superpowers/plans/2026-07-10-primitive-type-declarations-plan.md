# `primitive` Type Declarations Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Give `Int`/`Float`/`Binary` visible, inspectable Std declarations via a new `primitive` keyword + `@builtin(:tag)` marker, resolving to their existing Core nodes (`{:int_type}`/`{:float_type}`/`{:binary_type}`) instead of hardcoded name-magic.

**Architecture:** Marker-keyed, mirroring the seeded-plus-declared-plus-preluded `Std.Bool`/`Std.Nat`/`Std.Sigma` pattern. A `primitives` map on `Cure.Core.Env` holds `name → Core node`; `Cure.Core.Builtins.seed/2` seeds the three as a floor (so bare `x: Int` resolves with no import); each `@builtin(:tag) primitive Name` declaration confirms the same binding via its marker; `resolve_index_name/2` consults `env.primitives` and the hardcoded `primitive_type/1` is deleted. The three modules join the auto-prelude.

**Tech Stack:** Elixir; Cure lexer/parser (`lib/cure/compiler/{lexer,parser}.ex`), the trusted core (`lib/cure/core/{inductive,builtins}.ex` — Env + seed), the untrusted elaborator (`lib/cure/elab/{declarations,program}.ex`), Cure stdlib sources. ExUnit + Antigen.

## Global Constraints

- **Prerequisite:** the `@group`-placement plan (`2026-07-10-group-decorator-placement-plan.md`) has landed. The new `Std.Int`/`Std.Float` modules and the edit to `Std.Binary` use `@group(:core)` in the **above-`mod`** position; an in-body `@group` is now a hard parse error.
- Ghost-writer commits: `git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>"`; NO `Co-Authored-By`, no Claude signature.
- Explicit-pathspec staging only: `git add -- <path>`; NEVER `git add -A`/`git add .`.
- One `mix` build at a time. Scoped `mix test <file>` during tasks; full suite once, alone, at the gate.
- **TCB gate:** Task 3 edits `lib/cure/core/*` (Env struct + seed). It gets the full gate: strict red-green, a new Antigen antibody, the full Antigen suite, and the full test suite. Alignment: this adds an inert name→node resolution floor; it introduces NO new Core node (the three nodes already exist and were gated by the #2/#3 batch) and changes NO kernel judgement.
- Tests are behavioral and immutable once green.

## Interfaces produced (used across tasks)

- Parser: `primitive Name` → `{:container, [container_type: :primitive, name: "Int", line:, col:], []}`. `@builtin(:int) primitive Int` → the same container with `Keyword.get(meta, :decorator) == {:builtin, [{:literal, _, :int}]}`.
- Env: `Cure.Core.Env` gains `primitives: %{}` (String.t → Core node). Helpers in `inductive.ex`: `Env.put_primitive(env, name, node)` and `Env.primitive(env, name)` (returns node or nil).
- Tag→node table (elaborator, `declarations.ex`): `:int → {:int_type}`, `:float → {:float_type}`, `:binary → {:binary_type}`; any other tag → error.

---

### Task 1: Lexer — the `primitive` keyword

**Files:**
- Modify: `lib/cure/compiler/lexer.ex:47-48` (`@keywords`)
- Test: `test/cure/compiler/primitive_lex_test.exs` (create)

**Interfaces:**
- Produces: the source word `primitive` lexes to `{:keyword, :primitive}` (falls through the generic keyword→token clause, exactly like `opaque`).

- [ ] **Step 1: Write the failing test**

Create `test/cure/compiler/primitive_lex_test.exs`:

```elixir
defmodule Cure.Compiler.PrimitiveLexTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.Lexer

  test "`primitive` lexes as a keyword token" do
    {:ok, tokens} = Lexer.tokenize("primitive Int\n")
    assert Enum.any?(tokens, &match?(%{type: :keyword, value: :primitive}, &1))
  end
end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/cure/compiler/primitive_lex_test.exs`
Expected: FAIL — `primitive` lexes as an identifier, not `{:keyword, :primitive}`.

- [ ] **Step 3: Add `primitive` to `@keywords`**

In `lib/cure/compiler/lexer.ex`, add `primitive` to the `@keywords` list (line 48), next to `opaque`:

```elixir
    mod fn let type typealias opaque primitive indexed indices rec proto impl fsm local use as
```

- [ ] **Step 4: Run the test to verify it passes**

Run: `mix test test/cure/compiler/primitive_lex_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/compiler/lexer.ex test/cure/compiler/primitive_lex_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(lexer): add the \`primitive\` keyword"
```

---

### Task 2: Parser — `primitive Name` and `@builtin(:tag) primitive Name`

Parse `primitive Int` to a primitive container, and let `@builtin(:int)` attach to it. `@builtin` is not a module-level decorator, so it flows through `parse_at_attach/4`, which needs a `:primitive` clause (mirroring its `:type` clause at `parser.ex:4945`).

**Files:**
- Modify: `lib/cure/compiler/parser.ex` — statement dispatch (add `:primitive ->` near `:opaque`, ~line 1340) + a new `parse_primitive_def/1` + a `:primitive` clause in `parse_at_attach/4` (~line 4945)
- Test: `test/cure/compiler/primitive_parse_test.exs` (create)

**Interfaces:**
- Consumes: `attach_decorator/3` generic container clause (writes `decorator: {:builtin, args}` into container meta).
- Produces: the two AST shapes named in "Interfaces produced" above.

- [ ] **Step 1: Write the failing test**

Create `test/cure/compiler/primitive_parse_test.exs`:

```elixir
defmodule Cure.Compiler.PrimitiveParseTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp parse!(src) do
    {:ok, tokens} = Lexer.tokenize(src)
    {ast, %{errors: []}} = Parser.parse_program(tokens)
    ast
  end

  defp primitive_node(ast) do
    ast
    |> List.wrap()
    |> flatten()
    |> Enum.find(fn
      {:container, meta, _} when is_list(meta) ->
        Keyword.get(meta, :container_type) == :primitive
      _ -> false
    end)
  end

  # Unwrap {:block, _, items} / module containers to a flat node list.
  defp flatten({:block, _, items}), do: Enum.flat_map(items, &flatten/1)
  defp flatten({:container, meta, body} = c) when is_list(meta) do
    [c | Enum.flat_map(List.wrap(body), &flatten/1)]
  end
  defp flatten(other), do: [other]

  test "`primitive Int` parses to a primitive container carrying its name" do
    node = primitive_node(parse!("primitive Int\n"))
    assert {:container, meta, []} = node
    assert Keyword.get(meta, :name) == "Int"
  end

  test "`@builtin(:int) primitive Int` attaches the builtin tag to the container" do
    node = primitive_node(parse!("@builtin(:int) primitive Int\n"))
    {:container, meta, []} = node
    assert {:builtin, [{:literal, _, :int}]} = Keyword.get(meta, :decorator)
  end
end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/cure/compiler/primitive_parse_test.exs`
Expected: FAIL — `:primitive` has no dispatch clause, so parsing errors or produces no primitive container.

- [ ] **Step 3: Add the statement dispatch + parser function**

In `lib/cure/compiler/parser.ex`, add a dispatch clause next to `:opaque` (after line 1343):

```elixir
      # `primitive Name` — an irreducible machine base type (Int/Float/Binary).
      # No constructors, no `=`; the `@builtin(:tag)` marker names its Core node.
      :primitive ->
        parse_primitive_def(state)
```

Then add the parser function (place it near `parse_module/1`, ~line 2850):

```elixir
  # `primitive Name` → a constructor-less primitive-type container. The optional
  # `@builtin(:tag)` decorator is threaded on by `attach_decorator/3` when the
  # form is written `@builtin(:tag) primitive Name`.
  defp parse_primitive_def(state) do
    token = peek(state)
    state = advance(state)

    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)
    state = skip_newlines(state)

    meta = [container_type: :primitive, name: name, language: :cure, line: token.line, col: token.col]
    {{:container, meta, []}, state}
  end
```

- [ ] **Step 4: Add the `:primitive` clause to `parse_at_attach/4`**

In `lib/cure/compiler/parser.ex`, in `parse_at_attach/4`, add a clause alongside the `:type` clause (after `parser.ex:4948`):

```elixir
      # `@builtin(:tag) primitive Name` attaches the decorator to the primitive
      # container (the generic {:container, …} attach_decorator clause writes it
      # into :decorator meta, like `@builtin(:key) type Name`).
      %Token{type: :keyword, value: :primitive} ->
        {prim_ast, state} = parse_primitive_def(state)
        prim_ast = attach_decorator(prim_ast, dec_name, args)
        {prim_ast, state}
```

- [ ] **Step 5: Run the test to verify it passes**

Run: `mix test test/cure/compiler/primitive_parse_test.exs`
Expected: PASS (both cases).

- [ ] **Step 6: Commit**

```bash
git add -- lib/cure/compiler/parser.ex test/cure/compiler/primitive_parse_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(parser): parse \`primitive Name\` + attach @builtin tag"
```

---

### Task 3: Core — `Env.primitives` field + seeded floor (TCB-gated)

Add a `primitives` map to `Cure.Core.Env` and seed the three canonical bindings in `Builtins.seed/2`, so bare `Int`/`Float`/`Binary` resolve in every `env0` — the floor that makes name resolution work without imports and during self-compilation.

**Files:**
- Modify: `lib/cure/core/inductive.ex` — `Env` defstruct (line 12) + `Env.put_primitive/3` + `Env.primitive/2`
- Modify: `lib/cure/core/builtins.ex:116-124` (`seed/2`) — add `seed_primitives/1`
- Test: `test/cure/core/primitive_seed_test.exs` (create)
- Antibody: `test/antigen/primitive_seed_antibody_test.exs` (create)

**Interfaces:**
- Produces: `Env.primitive(Builtins.seed(Env.empty()), "Int") == {:int_type}` (and `"Float"`/`"Binary"`); unknown name → `nil`.

- [ ] **Step 1: Write the failing test**

Create `test/cure/core/primitive_seed_test.exs`:

```elixir
defmodule Cure.Core.PrimitiveSeedTest do
  @moduledoc """
  The primitive-type floor (spec 2026-07-10-primitive-type-declarations): every
  seeded env0 resolves the three machine base names to their Core nodes, so bare
  `x: Int` works with no import.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Builtins, Env}

  defp seeded, do: Builtins.seed(Env.empty())

  test "the seed floor binds the three machine base types" do
    env = seeded()
    assert Env.primitive(env, "Int") == {:int_type}
    assert Env.primitive(env, "Float") == {:float_type}
    assert Env.primitive(env, "Binary") == {:binary_type}
  end

  test "a non-primitive name has no primitive binding" do
    assert Env.primitive(seeded(), "Nat") == nil
  end
end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/cure/core/primitive_seed_test.exs`
Expected: FAIL — `Env` has no `primitives` field / `Env.primitive/2` is undefined.

- [ ] **Step 3: Add the `primitives` field + helpers**

In `lib/cure/core/inductive.ex`, add `primitives: %{}` to the `Env` defstruct (line 12 block):

```elixir
  defstruct families: %{},
            ctors: %{},
            ctor_to_family: %{},
            defs: %{},
            certified: nil,
            builtins: %{},
            interfaces: %{},
            coherence: nil,
            constrained: %{},
            primitives: %{}
```

Add the helpers in the `Cure.Core.Env` module (near the other `Env.*` functions in `inductive.ex`):

```elixir
  @doc "Register a primitive base type: surface name → its Core type node."
  @spec put_primitive(t(), String.t(), tuple()) :: t()
  def put_primitive(%__MODULE__{primitives: p} = env, name, node) when is_binary(name),
    do: %{env | primitives: Map.put(p, name, node)}

  @doc "The Core node a primitive surface name resolves to, or nil."
  @spec primitive(t(), String.t()) :: tuple() | nil
  def primitive(%__MODULE__{primitives: p}, name) when is_binary(name), do: Map.get(p, name)
```

- [ ] **Step 4: Seed the floor in `Builtins.seed/2`**

In `lib/cure/core/builtins.ex`, extend `seed/2` (line 117-123) to call `seed_primitives/1`:

```elixir
  def seed(%Env{} = env, exclude \\ MapSet.new()) do
    env
    |> maybe_seed(:bool, bool_family(), bool_ctors(), exclude)
    |> maybe_seed(:nat, nat_family(), nat_ctors(), exclude)
    |> maybe_seed(:eq, eq_family(), eq_ctors(), exclude)
    |> maybe_seed(:sigma, sigma_family(), sigma_ctors(), exclude)
    |> maybe_seed(:list, list_family(), list_ctors(), exclude)
    |> seed_ops()
    |> seed_primitives()
  end

  # The machine base types' name→node floor (spec 2026-07-10-primitive-type-
  # declarations). These are the canonical bindings the Std `@builtin(:tag)
  # primitive Name` declarations mirror and confirm.
  defp seed_primitives(%Env{} = env) do
    env
    |> Env.put_primitive("Int", {:int_type})
    |> Env.put_primitive("Float", {:float_type})
    |> Env.put_primitive("Binary", {:binary_type})
  end
```

- [ ] **Step 5: Run the test to verify it passes**

Run: `mix test test/cure/core/primitive_seed_test.exs`
Expected: PASS.

- [ ] **Step 6: Write the Antigen antibody**

Create `test/antigen/primitive_seed_antibody_test.exs`:

```elixir
defmodule Antigen.PrimitiveSeedAntibodyTest do
  @moduledoc """
  TCB antibody — seeding the primitive name→node floor (spec 2026-07-10-
  primitive-type-declarations) is INERT with respect to the kernel. It adds a
  surface-resolution table only; it introduces no Core node (the three nodes
  predate it, gated by the #2/#3 batch) and changes no kernel judgement.

  Two properties:
    * EXACTLY-THREE-CANONICAL — the seeded floor is precisely {Int→int_type,
      Float→float_type, Binary→binary_type}: no extra bindings, each mapping to
      the already-gated canonical node. A drifted binding would silently
      repoint a base type.
    * KERNEL-INERT — inference/conversion on the three primitive nodes is
      identical whether or not the primitives floor is present. The floor is a
      resolution convenience, never consulted by the TCB.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Builtins, Context, Conv, Env, Kernel}

  test "EXACTLY-THREE-CANONICAL: the floor is precisely the three canonical bindings" do
    env = Builtins.seed(Env.empty())

    assert Env.primitive(env, "Int") == {:int_type}
    assert Env.primitive(env, "Float") == {:float_type}
    assert Env.primitive(env, "Binary") == {:binary_type}
    assert map_size(env.primitives) == 3
  end

  test "KERNEL-INERT: primitive-node judgements ignore the floor" do
    with_floor = Builtins.seed(Env.empty())
    without = %{with_floor | primitives: %{}}

    for node <- [{:int_type}, {:float_type}, {:binary_type}] do
      assert Kernel.infer(Context.empty(with_floor), node) ==
               Kernel.infer(Context.empty(without), node),
             "kernel inference on #{inspect(node)} must not depend on the primitives floor"
    end

    # The three nodes stay mutually non-convertible either way (no floor-induced collapse).
    refute Conv.conv?({:int_type}, {:binary_type}, [], 0, with_floor)
    refute Conv.conv?({:float_type}, {:binary_type}, [], 0, with_floor)
  end
end
```

- [ ] **Step 7: Run the antibody**

Run: `mix test test/cure/core/primitive_seed_test.exs test/antigen/primitive_seed_antibody_test.exs`
Expected: PASS (all).

- [ ] **Step 8: Commit**

```bash
git add -- lib/cure/core/inductive.ex lib/cure/core/builtins.ex test/cure/core/primitive_seed_test.exs test/antigen/primitive_seed_antibody_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(core): Env.primitives floor seeding Int/Float/Binary name→node bindings"
```

---

### Task 4: Elaborator — elaborate a `primitive` declaration (marker → confirm)

When a `{:container, container_type: :primitive}` declaration elaborates, read its `@builtin(:tag)`, map the tag to a Core node via a fixed 3-entry table, and confirm the binding against the seeded floor — rejecting a missing marker, an unknown tag, or a tag that disagrees with the floor.

**Files:**
- Modify: `lib/cure/elab/declarations.ex` — add a `:primitive` clause to the container-elaboration dispatch (the same `elaborate({:container, meta, _}, env)` area that handles `:opaque`) + a `primitive_tag_node/1` table
- Test: `test/cure/elab/primitive_decl_test.exs` (create)

**Interfaces:**
- Consumes: `Env.put_primitive/3`, `Env.primitive/2` (Task 3); container meta `decorator: {:builtin, [{:literal, _, tag}]}` (Task 2).
- Produces: elaborating `@builtin(:int) primitive Int` leaves `Env.primitive(env, "Int") == {:int_type}`; a bad tag/marker → `{:error, …}`.

- [ ] **Step 1: Write the failing test**

Create `test/cure/elab/primitive_decl_test.exs`:

```elixir
defmodule Cure.Elab.PrimitiveDeclTest do
  @moduledoc """
  `@builtin(:tag) primitive Name` elaborates by confirming the surface name maps
  to its Core node via the marker (spec 2026-07-10-primitive-type-declarations).
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program
  alias Cure.Core.Env

  test "a well-formed primitive declaration confirms its binding" do
    {:ok, env} = Program.elaborate("mod M\n  @builtin(:float) primitive Float\nend\n")
    assert Env.primitive(env, "Float") == {:float_type}
  end

  test "a primitive with no @builtin marker is rejected" do
    assert {:error, _} = Program.elaborate("mod M\n  primitive Widget\nend\n")
  end

  test "a primitive with an unknown @builtin tag is rejected" do
    assert {:error, _} = Program.elaborate("mod M\n  @builtin(:sparkle) primitive Sparkle\nend\n")
  end

  test "a primitive whose tag disagrees with the name's floor is rejected" do
    # Int's floor is {:int_type}; tagging it :float contradicts the floor.
    assert {:error, _} = Program.elaborate("mod M\n  @builtin(:float) primitive Int\nend\n")
  end
end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/cure/elab/primitive_decl_test.exs`
Expected: FAIL — the `:primitive` container has no elaboration clause (elaboration errors or ignores it, so `Env.primitive` is unset and the bad cases are not rejected).

- [ ] **Step 3: Find the container-elaboration dispatch**

Run: `grep -n "container_type\|def elaborate({:container\|:opaque ->" lib/cure/elab/declarations.ex`
Identify the clause/`case` that dispatches on `Keyword.get(meta, :container_type)` and already handles `:opaque` (added in the opaque-former batch). The `:primitive` handling goes alongside it.

- [ ] **Step 4: Implement the `:primitive` elaboration**

In `lib/cure/elab/declarations.ex`, add a `:primitive` branch to the container dispatch found in Step 3. It reads the tag, maps it, and confirms against the floor:

```elixir
      :primitive ->
        name = Keyword.get(meta, :name)

        with {:ok, tag} <- primitive_builtin_tag(meta),
             {:ok, node} <- primitive_tag_node(tag),
             :ok <- confirm_primitive_floor(env, name, node) do
          {:ok, Env.put_primitive(env, name, node)}
        end
```

Add these helpers (near `primitive_type/1`, which Task 5 deletes):

```elixir
  # The `@builtin(:tag)` on a primitive container, or an error if absent.
  defp primitive_builtin_tag(meta) do
    case Keyword.get(meta, :decorator) do
      {:builtin, [{:literal, _, tag}]} when is_atom(tag) -> {:ok, tag}
      _ -> {:error, {:primitive_missing_builtin, Keyword.get(meta, :name)}}
    end
  end

  # The fixed tag→Core-node table — the ONLY inherent mapping (keyed by builtin
  # tag, not by surface name). Exactly three tags are legal.
  defp primitive_tag_node(:int), do: {:ok, {:int_type}}
  defp primitive_tag_node(:float), do: {:ok, {:float_type}}
  defp primitive_tag_node(:binary), do: {:ok, {:binary_type}}
  defp primitive_tag_node(other), do: {:error, {:unknown_primitive_tag, other}}

  # A declaration's node must match the seeded floor for that name (consistency
  # contract — mirrors the Bool/Nat seeded-look-alike agreement).
  defp confirm_primitive_floor(env, name, node) do
    case Env.primitive(env, name) do
      nil -> :ok
      ^node -> :ok
      other -> {:error, {:primitive_floor_mismatch, name, node, other}}
    end
  end
```

- [ ] **Step 5: Run the test to verify it passes**

Run: `mix test test/cure/elab/primitive_decl_test.exs`
Expected: PASS (all four cases).

- [ ] **Step 6: Commit**

```bash
git add -- lib/cure/elab/declarations.ex test/cure/elab/primitive_decl_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): elaborate \`primitive\` declarations via the @builtin marker"
```

---

### Task 5: Elaborator — resolve via `env.primitives`, delete `primitive_type/1`

Repoint `resolve_index_name/2` to consult `Env.primitive/2` instead of the hardcoded `primitive_type/1`, then delete the name-magic function.

**Files:**
- Modify: `lib/cure/elab/declarations.ex:1287-1289` (`resolve_index_name/2` primitive branch) and `1319-1322` (`primitive_type/1` — delete)
- Also check: `declarations.ex:1419` (the second `primitive_type` call site found earlier) — repoint it too
- Test: `test/cure/elab/primitive_resolve_test.exs` (create)

**Interfaces:**
- Consumes: `Env.primitive/2` (Task 3), always seeded in `env0`.
- Produces: in a module with NO imports, `fn f(x: Int) -> Int = x` elaborates to `{:pi, {:int_type}, {:int_type}}` (and Float/Binary analogues).

- [ ] **Step 1: Write the failing test**

Create `test/cure/elab/primitive_resolve_test.exs`:

```elixir
defmodule Cure.Elab.PrimitiveResolveTest do
  @moduledoc """
  Bare `Int`/`Float`/`Binary` resolve to their Core nodes via the seeded floor,
  with no import (spec 2026-07-10-primitive-type-declarations). This is the
  behaviour the deleted `primitive_type/1` provided; it must survive on the
  env floor.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  for {name, node} <- [{"Int", {:int_type}}, {"Float", {:float_type}}, {"Binary", {:binary_type}}] do
    test "bare #{name} resolves to #{inspect(node)} with no import" do
      {:ok, env} = Program.elaborate("mod M\n  fn f(x: #{unquote(name)}) -> #{unquote(name)} = x\nend\n")
      assert env.defs[:f].type == {:pi, unquote(Macro.escape(node)), unquote(Macro.escape(node))}
    end
  end
end
```

- [ ] **Step 2: Run the test to verify it PASSES (baseline) — then we refactor under green**

Run: `mix test test/cure/elab/primitive_resolve_test.exs`
Expected: PASS already (the current `primitive_type/1` resolves these). This test pins the behavior we must preserve while deleting `primitive_type/1`. (This is a refactor guarded by an existing-behavior test, not red-green of new behavior.)

- [ ] **Step 3: Repoint `resolve_index_name/2` to the env floor**

In `lib/cure/elab/declarations.ex`, change the first `cond` branch of `resolve_index_name/2` (lines 1287-1289):

```elixir
    cond do
      primitive_type(name) != nil ->
        primitive_type(name)
```

to:

```elixir
    cond do
      Env.primitive(env, name) != nil ->
        Env.primitive(env, name)
```

- [ ] **Step 4: Repoint the other `primitive_type/1` call site**

At `declarations.ex:1419` (the `case primitive_type(name) do` found in the earlier survey), repoint it to `Env.primitive(env, name)`. Confirm the surrounding function has `env` in scope; if it does not, thread it from the caller (the plan's Step 3 branch shows `env` is available in `resolve_index_name/2`; for the 1419 site, run `grep -n "defp " lib/cure/elab/declarations.ex | sort -t: -k1 -n` to find the enclosing function and confirm its arity carries `env`). If `env` is genuinely unavailable at 1419, leave a thin `primitive_floor_names/0` returning `["Int","Float","Binary"]` for that purely-syntactic check — but prefer threading `env`.

- [ ] **Step 5: Delete `primitive_type/1`**

Remove the four `primitive_type` clauses at `declarations.ex:1319-1322`:

```elixir
  defp primitive_type("Int"), do: {:int_type}
  defp primitive_type("Float"), do: {:float_type}
  defp primitive_type("Binary"), do: {:binary_type}
  defp primitive_type(_), do: nil
```

- [ ] **Step 6: Run the test + a compile check**

Run: `mix test test/cure/elab/primitive_resolve_test.exs`
Expected: PASS (behavior preserved via the floor). If the compiler warns about an unused/undefined `primitive_type`, ensure every call site was repointed (Steps 3-4).

- [ ] **Step 7: Commit**

```bash
git add -- lib/cure/elab/declarations.ex test/cure/elab/primitive_resolve_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "refactor(elab): resolve primitives via env floor; delete primitive_type/1 name-magic"
```

---

### Task 6: Std modules — `Std.Int`, `Std.Float`, and `primitive Binary` in `Std.Binary`

Create the two new modules and add the declaration to the existing `Std.Binary`, all with `@group(:core)` above `mod` (per the prerequisite plan).

**Files:**
- Create: `lib/std/int.cure`
- Create: `lib/std/float.cure`
- Modify: `lib/std/binary.cure` (add the `primitive Binary` declaration)
- Test: `test/cure/stdlib/primitive_modules_test.exs` (create)

**Interfaces:**
- Produces: `Std.Int`/`Std.Float`/`Std.Binary` each declare their primitive; all three dependent-elaborate cleanly.

- [ ] **Step 1: Write the failing test**

Create `test/cure/stdlib/primitive_modules_test.exs`:

```elixir
defmodule Cure.Stdlib.PrimitiveModulesTest do
  @moduledoc """
  The machine base types have visible, inspectable Std homes (spec 2026-07-10-
  primitive-type-declarations): Std.Int, Std.Float, and Std.Binary each declare
  their `@builtin(:tag) primitive Name` and elaborate cleanly.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program
  alias Cure.Core.Env

  test "Std.Int declares Int and elaborates cleanly" do
    {:ok, env} = Program.elaborate(File.read!("lib/std/int.cure"))
    assert Env.primitive(env, "Int") == {:int_type}
  end

  test "Std.Float declares Float and elaborates cleanly" do
    {:ok, env} = Program.elaborate(File.read!("lib/std/float.cure"))
    assert Env.primitive(env, "Float") == {:float_type}
  end

  test "Std.Binary still elaborates with the primitive Binary declaration" do
    assert {:ok, _env} = Program.elaborate(File.read!("lib/std/binary.cure"))
  end
end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/cure/stdlib/primitive_modules_test.exs`
Expected: FAIL — `lib/std/int.cure` / `lib/std/float.cure` do not exist.

- [ ] **Step 3: Create `lib/std/int.cure`**

```cure
@group(:core)
mod Std.Int
  ## The primitive machine integer.
  ##
  ## `Int` is an irreducible BEAM integer — not an inductive, not a postulate.
  ## Arithmetic and bitwise operations on `Int` are provided as builtin
  ## operators (`+`, `-`, `band`, `bsl`, …); this module gives the type itself a
  ## visible, documented home.
  @builtin(:int) primitive Int
```

- [ ] **Step 4: Create `lib/std/float.cure`**

```cure
@group(:core)
mod Std.Float
  ## The primitive machine floating-point number.
  ##
  ## `Float` is an irreducible BEAM float — not an inductive, not a postulate.
  ## Floating-point operators (`+.`-style builtin ops) act on it; this module
  ## gives the type itself a visible, documented home.
  @builtin(:float) primitive Float
```

- [ ] **Step 5: Add `primitive Binary` to `lib/std/binary.cure`**

Insert the declaration immediately after the module's doc block, before `use Std.Bounded` (so the type is declared up front). The `@group(:core)` is already above `mod` from the prerequisite plan:

```cure
  @builtin(:binary) primitive Binary
```

- [ ] **Step 6: Run the test to verify it passes**

Run: `mix test test/cure/stdlib/primitive_modules_test.exs`
Expected: PASS (all three).

- [ ] **Step 7: Commit**

```bash
git add -- lib/std/int.cure lib/std/float.cure lib/std/binary.cure test/cure/stdlib/primitive_modules_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(std): visible primitive homes — Std.Int, Std.Float, primitive Binary"
```

---

### Task 7: Auto-prelude the three primitive modules + full gate

Add `Std.Int`/`Std.Float`/`Std.Binary` to the dependent auto-prelude so their declarations (and Binary's `to_binary`/`from_binary`/`Char`) are available in every module without `use`.

**Files:**
- Modify: `lib/cure/elab/program.ex:234` (`@auto_prelude`) and `:240` (`@auto_prelude_types`)
- Test: `test/cure/stdlib/primitive_prelude_test.exs` (create)

**Interfaces:**
- Consumes: the modules from Task 6.
- Produces: a bare module (no `use`) can name `Binary` and call `to_binary` / use `Char`.

- [ ] **Step 1: Write the failing test**

Create `test/cure/stdlib/primitive_prelude_test.exs`:

```elixir
defmodule Cure.Stdlib.PrimitivePreludeTest do
  @moduledoc """
  Std.Binary is wholesale auto-preluded (spec 2026-07-10-primitive-type-
  declarations §3): `Binary`, `to_binary`/`from_binary`, and `Char` are all
  available in a bare module with no `use`.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  test "to_binary and Char are available with no `use`" do
    src = "mod M\n  fn enc(cs: List(Char)) -> Binary = to_binary(cs)\nend\n"
    assert {:ok, _env} = Program.elaborate(src)
  end
end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/cure/stdlib/primitive_prelude_test.exs`
Expected: FAIL — without `use Std.Binary`, `to_binary`/`Char` do not resolve.

- [ ] **Step 3: Add the three modules to the auto-prelude**

In `lib/cure/elab/program.ex`, extend `@auto_prelude` (line 234):

```elixir
  @auto_prelude ~w(Std.Bool Std.Nat Std.Sigma Std.Int Std.Float Std.Binary)
```

and `@auto_prelude_types` (line 240) — the canonical type each provides, to keep the "module locally declares a same-named type ⇒ skip" collision guard correct:

```elixir
  @auto_prelude_types %{
    "Std.Bool" => :Bool,
    "Std.Nat" => :Nat,
    "Std.Sigma" => :Sigma,
    "Std.Int" => :Int,
    "Std.Float" => :Float,
    "Std.Binary" => :Binary
  }
```

Note: `@auto_prelude_types` maps to the family-name atom used for the collision skip; for primitives the surface name atom (`:Int`, `:Float`, `:Binary`) is the right key — a module that declares its own same-named type still skips the prelude, and a bare user module (the common case) never does.

- [ ] **Step 4: Run the test to verify it passes**

Run: `mix test test/cure/stdlib/primitive_prelude_test.exs`
Expected: PASS. If it fails because a primitive module does not meet the auto-prelude clean-elaboration gate, run `mix run -e 'IO.inspect(Cure.Elab.Program.elaborate(File.read!("lib/std/binary.cure")))'` to see the error and fix the module source (all three were verified to elaborate cleanly during design).

- [ ] **Step 5: TCB gate — full Antigen suite + full test suite**

Run: `mix test`
Expected: all green, Antigen shape-coverage intact, expected immune responses only. This is the gate for the Task 3 core edit and the whole feature. Investigate any failure before proceeding; do not weaken a test.

- [ ] **Step 6: Commit**

```bash
git add -- lib/cure/elab/program.ex test/cure/stdlib/primitive_prelude_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): auto-prelude Std.Int/Std.Float/Std.Binary"
```

---

## Self-Review

**Spec coverage:**
- §Design 1 (surface: `primitive` keyword + `@builtin(:tag)`, three legal tags, reject others) → Task 1 (lexer), Task 2 (parse), Task 4 (tag table + reject unknown/missing/mismatch). ✓
- §Design 2 (marker-keyed: seed floor + declaration confirm + auto-prelude; replace `primitive_type/1`) → Task 3 (seed floor), Task 4 (declaration confirm), Task 5 (resolve via floor + delete `primitive_type/1`), Task 7 (auto-prelude). ✓
- §Design 3 (Std.Binary wholesale prelude → `to_binary`/`from_binary`/`Char` universal) → Task 7 Step 1 test asserts `to_binary` + `Char` with no `use`. ✓
- §Interaction (new modules born in above-`mod` `@group`) → Task 6 sources use `@group(:core)` above `mod`; prerequisite noted in Global Constraints. ✓
- §Testing (parse; bare resolution; marker agreement; inspection; auto-prelude; regression + TCB gate) → Tasks 2, 5, 4, 6, 7, and Task 3 antibody + Task 7 Step 5 full gate. ✓

**Placeholder scan:** No TODO/TBD. Task 5 Step 4 carries a conditional (thread `env` vs. a syntactic fallback) with an exact command to decide it — a guarded decision, not a placeholder; the primary path (thread `env`) is fully specified. Test helper `parse_program`/`tokenize` names match the frontend API used in the sibling plan.

**Type consistency:** `Env.primitive/2` / `Env.put_primitive/3` are defined in Task 3 and consumed identically in Tasks 4, 5, 6. The container meta `decorator: {:builtin, [{:literal, _, tag}]}` is produced in Task 2 and destructured in Task 4 (`primitive_builtin_tag/1`). The tag→node table (`:int→{:int_type}` etc.) in Task 4 matches the floor bindings in Task 3. `container_type: :primitive` is produced in Task 2 and dispatched in Task 4. Consistent.
