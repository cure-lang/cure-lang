# Compile-time Typeclasses — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace runtime `proto`/`impl` protocol dispatch with compile-time typeclasses in the dependent pipeline: interfaces elaborate to Core record types, implementations to dictionary values, instance selection resolves statically (inlined at concrete sites, threaded as an implicit dictionary parameter through polymorphic code), `Functor` is genuinely higher-kinded, and `struct_eq`/`struct_ne` + the 4-way `==` dispatch are retired in favour of `Equatable`.

**Architecture:** Dictionary-passing (Idris2-faithful). Reuses existing dependent-record Core (no new kernel node anticipated). A new elaborator-scoped **coherence registry** keys anonymous instances by `(interface, head type constructor)` and named instances by name. Resolution recovers a head key from the method's interface-head argument type — directly for kind-`Type` interfaces, via Miller-pattern-fragment unification for the higher-kinded `Functor`.

**Tech Stack:** Elixir; Cure dependent elaborator (`lib/cure/elab/*`) + kernel (`lib/cure/core/*`); parser (`lib/cure/compiler/parser.ex`, `lexer.ex`). Spec: `docs/superpowers/specs/types/2026-07-10-typeclasses-design.md` (read it — this plan implements it).

## Global Constraints

- **Ghost-writer commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, NO `Co-Authored-By`, no Claude signature.
- **Explicit-pathspec staging only:** `git add -- <path>`; NEVER `git add -A`/`git add .` (a concurrent agent shares this worktree; there is also an unrelated dirty file `docs/superpowers/plans/2026-07-09-string-char-value-surface-plan.md` that must stay untouched).
- **Branch:** stay on `autopilot/kernel-parity-batch` (no new worktree).
- **One build at a time.** Never run two `mix` suites concurrently. Prefer scoped `mix test <file>`; full suite once, alone, at the gate. **Warnings are errors under `mix test`** (merged from idris-parity) — a compile warning fails the build; keep clauses of the same function contiguous and no unused vars.
- **Strict red-green TDD.** Failing test first, watch it fail for the right reason, minimal implementation, green, commit. Behavioural tests (elaborate real `.cure` source; assert Core shape and/or run emitted BEAM), not implementation-coupled.
- **Tests immutable once green** — go green by changing implementation, never by weakening a test, unless the test provably encodes wrong behavior (state why first). The one licensed deletion: tests that assert `struct_eq`/`struct_ne` seeding/behaviour, which this work deliberately retires (Task 6).
- **Two pipelines:** dependent machinery is ONLY `lib/cure/elab/*` + `lib/cure/core/*`. IGNORE `lib/cure/compiler/{codegen,pattern_compiler}.ex` and `lib/cure/types/*` (non-dependent decoys). The classic `proto`/`impl` parser (`parser.ex:parse_proto`) is the OLD surface being replaced — do not route new work through it.
- **TCB discipline:** no kernel (`lib/cure/core/*`) change is anticipated (dictionaries reuse dependent records). If one proves necessary, STOP and treat it as its own reviewed change (red-green + Antigen antibody + full Antigen suite + full `mix test`); pre-approved only if it aligns with Agda/Lean.

## File Structure

- `lib/cure/compiler/lexer.ex` — add `interface`, `implementation`, `deriving` keywords (Task 1).
- `lib/cure/compiler/parser.ex` — parse the three surface forms → AST nodes (Task 1).
- `lib/cure/elab/interface.ex` *(new)* — interface elaboration: AST → Core record type, head-kind inference, method-field + default-method extraction (Task 2).
- `lib/cure/elab/coherence.ex` *(new)* — the coherence registry (data structure + register/lookup + overlap/orphan checks) carried in the elaboration env/signature (Task 3).
- `lib/cure/elab/implementation.ex` *(new)* — implementation elaboration: AST → dictionary value + registration (Task 3).
- `lib/cure/elab/resolve.ex` *(new)* — method-call resolution (head-key recovery, concrete inline vs. dict-param projection), first-order (Task 4) then higher-kinded (Task 5).
- `lib/cure/elab/deriving.ex` *(new)* — structural instance generation for Equatable/Ord/Show (Task 7).
- `lib/cure/elab/elaborator.ex` — wire interface/impl/method-call into the expression + declaration dispatchers; repoint `==`/`<`/… (Task 4, 6).
- `lib/cure/elab/program.ex` — register interfaces/impls during module elaboration; thread the coherence registry (Task 2, 3).
- `lib/cure/core/inductive.ex` — this is where `Cure.Core.Env`'s struct + accessors actually live (there is no `lib/cure/core/env.ex` file); add the `interfaces` field + `put_interface`/`get_interface` (Task 2) and the `coherence` field + `put_coherence`/`coherence` (Task 3).
- `lib/cure/core/builtins.ex`, `normalise.ex`; `lib/cure/elab/emit.ex`, `guard_lint.ex` — remove `struct_eq`/`struct_ne` (Task 6).
- `lib/std/{equatable,ord,show,functor,access}.cure` — migrate to `interface`/`implementation` (Task 8).
- `test/cure/elab/*`, `test/oracle/typeclass/*` — tests per task.

**Task dependency order:** 1 → 2 → 3 → 4 → (5, 7 depend on 4) → 6 (depends on 4) → 8 (depends on 4,5,6,7) → 9. Each task ends green and committed before the next.

---

### Task 1: Surface — `interface` / `implementation` / `deriving` parsing

**Files:** Modify `lib/cure/compiler/lexer.ex` (keyword list ~48), `lib/cure/compiler/parser.ex` (`@definition_keywords` ~50, the definition dispatcher ~1321, new `parse_interface`/`parse_implementation`, `deriving` clause in type parsing). Test: `test/cure/compiler/typeclass_parse_test.exs` (new).

**Interfaces:**
- Produces AST nodes consumed by Tasks 2–3 & 7:
  - `{:interface, meta, methods}` — `meta` carries `:name`, `:params` (head vars), `:defaults` (method name → default body expr, or absent); `methods` is a list of method signatures (reuse the existing signature-only parse at `parser.ex:2402`).
  - `{:implementation, meta, methods}` — `meta` carries `:interface`, `:for` (head type expr), `:as` (name | nil for anonymous); `methods` are `fn` clauses.
  - `{:deriving, meta, interfaces}` attached to a `type` decl's meta (decl-attached form), and a standalone `{:derive, meta}` with `:interface` + `:for`.

- [ ] **Step 1: Write the failing parser test**

```elixir
defmodule Cure.Compiler.TypeclassParseTest do
  # interface/implementation/deriving are the compile-time typeclass surface
  # (replacing runtime proto/impl). This pins the AST the elaborator consumes.
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  # `Parser.parse/2` takes a TOKEN LIST, not raw source (@spec parse([Token.t()],
  # keyword())) — mirror the tokenize-then-parse convention every other parser
  # test uses (e.g. test/cure/compiler/builtin_decorator_parse_test.exs). The
  # parsed AST is a plain `{atom(), keyword(), term()}` tuple, not a struct, so
  # there is no `.definitions` field — a `mod ... end` block parses to
  # `{:container, [container_type: :module, ...], body}`; `body` is the
  # definitions list.
  defp defs(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    {:container, _meta, body} = ast
    body
  end

  test "an interface with a method and a default method parses" do
    src = """
    mod M
      interface Equatable(a)
        fn eq(x: a, y: a) -> Bool
        fn ne(x: a, y: a) -> Bool = true
    end
    """
    # `fn ne` must be indented to the SAME level as `fn eq` — i.e. nested
    # INSIDE the interface block, not a sibling of the `interface` line — or
    # it parses as an unrelated top-level def referencing an unbound `a` and
    # is never captured as a default at all.
    assert Enum.any?(defs(src), &match?({:interface, _, _}, &1))
    {:interface, meta, methods} = Enum.find(defs(src), &match?({:interface, _, _}, &1))
    assert Keyword.get(meta, :name) == "Equatable"
    assert Keyword.get(meta, :params) == ["a"]
    assert length(methods) >= 1
    assert Map.has_key?(Keyword.get(meta, :defaults, %{}), "ne")
  end

  test "an anonymous implementation parses with interface + for-type" do
    src = """
    mod M
      implementation Equatable for Int
        fn eq(x: Int, y: Int) -> Bool = int_eq(x, y)
    end
    """
    {:implementation, meta, _methods} = Enum.find(defs(src), &match?({:implementation, _, _}, &1))
    assert Keyword.get(meta, :interface) == "Equatable"
    assert Keyword.get(meta, :as) == nil
  end

  test "a named implementation records its name" do
    src = """
    mod M
      implementation Equatable for Int as strictInt
        fn eq(x: Int, y: Int) -> Bool = int_eq(x, y)
    end
    """
    {:implementation, meta, _} = Enum.find(defs(src), &match?({:implementation, _, _}, &1))
    assert Keyword.get(meta, :as) == "strictInt"
  end

  test "decl-attached deriving is recorded on the type" do
    src = """
    mod M
      type Color = R | G | B deriving Equatable
    end
    """
    # An ADT type def parses to `{:container, meta, variants}` with
    # `meta[:container_type] == :enum` and a STRING `:name` (there is no
    # `{:type, meta, _}` node anywhere in the parser — confirmed against
    # `parse_type_def_adt`/`builtin_decorator_parse_test.exs`'s own
    # `find_type_decl/2` convention). Matching on `:type` here would never
    # find anything, deriving suffix or not.
    type_def =
      Enum.find(defs(src), fn
        {:container, meta, _} ->
          Keyword.get(meta, :container_type) == :enum and Keyword.get(meta, :name) == "Color"

        _ ->
          false
      end)

    {:container, meta, _} = type_def
    assert "Equatable" in Keyword.get(meta, :deriving, [])
  end
end
```

- [ ] **Step 2: Run it, watch it fail**

Run: `mix test test/cure/compiler/typeclass_parse_test.exs`
Expected: FAIL — `interface`/`implementation` are not keywords, so they lex as identifiers and the definition dispatcher errors (`{:unexpected_token, …}` / parse error); the `deriving` suffix is unparsed.

- [ ] **Step 3: Add the keywords**

In `lib/cure/compiler/lexer.ex` keyword list (~48), add `interface implementation deriving`. In `parser.ex` `@definition_keywords` (~50), add `:interface, :implementation`.

- [ ] **Step 4: Implement `parse_interface` / `parse_implementation` and the `deriving` suffix**

In `parser.ex` definition dispatcher (~1321), add `:interface -> parse_interface(state)` and `:implementation -> parse_implementation(state)`. Model `parse_interface` on `parse_proto` (~3406) but emit `{:interface, meta, methods}` with `:params` parsed from the head `Name(a, …)` and method signatures via the existing signature-only path (~2402); collect any `fn … = body` inside the block as `:defaults`. Model `parse_implementation` on the existing `parse_impl` (the `:impl` path) but emit `{:implementation, meta, methods}` with `:interface`, `:for` (parse a type expr after `for`), and optional `as <name>`. In the `type` declaration parser, after the constructor list, accept an optional `deriving <Name>{, <Name>}` and store the list in the type's `meta[:deriving]`; also add a standalone `derive <Iface> for <Type>` definition-keyword form emitting `{:derive, meta}`.

- [ ] **Step 5: Run green**

Run: `mix test test/cure/compiler/typeclass_parse_test.exs`
Expected: PASS (4 tests).

- [ ] **Step 6: Scoped regression + commit**

Run: `mix test test/cure/compiler/`
Expected: PASS.
```bash
git add -- lib/cure/compiler/lexer.ex lib/cure/compiler/parser.ex test/cure/compiler/typeclass_parse_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(parser): interface/implementation/deriving surface syntax"
```

---

### Task 2: Interface elaboration → Core record type

**Files:** Create `lib/cure/elab/interface.ex`. Modify `lib/cure/elab/program.ex` (dispatch `{:interface, …}` during module elaboration), `lib/cure/core/inductive.ex` (the `interfaces` `Env` field + accessors — this is where `Cure.Core.Env` lives, not a separate `env.ex`). Test: `test/cure/elab/interface_elab_test.exs` (new).

**Interfaces:**
- Consumes `{:interface, meta, methods}` (Task 1).
- Produces: registers, in the env, an interface record type former `Iface : Π(h : K). Type` where `K` is the **inferred head kind** (`Type`, or `Type → Type` when the head appears applied — §3.1), and `Iface(h) ≙ record{ method : field-type, … }`. Records the interface descriptor (name, head var, head kind, method names + field types, default bodies) in a new `Env` field `interfaces` for Tasks 3–7. Head used inconsistently ⇒ `{:error, {:inconsistent_head_kind, name}}`.

- [ ] **Step 1: Write the failing test**

```elixir
defmodule Cure.Elab.InterfaceElabTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program
  alias Cure.Core.Env

  test "a kind-Type interface registers a record type former and descriptor" do
    src = """
    mod M
      interface Showable(a)
        fn show(x: a) -> Bool
    end
    """
    assert {:ok, env} = Program.elaborate(src)
    desc = Env.get_interface(env, :Showable)
    assert desc.head_kind == :type
    assert :show in Map.keys(desc.methods)
  end

  test "Functor's head kind is inferred as Type -> Type (applied head)" do
    src = """
    mod M
      interface Functor(f)
        fn fmap(container: f(a), g: a -> b) -> f(b)
    end
    """
    assert {:ok, env} = Program.elaborate(src)
    desc = Env.get_interface(env, :Functor)
    assert desc.head_kind == {:arrow, :type, :type}
  end

  test "an inconsistently-kinded head is rejected" do
    src = """
    mod M
      interface Bad(a)
        fn m1(x: a) -> Bool
        fn m2(y: a(a)) -> Bool
    end
    """
    # `m2` MUST be indented to the same level as `m1` — nested inside the
    # interface block — or it parses as an unrelated top-level def with a
    # free/unbound `a`, and `Bad` ends up with only the (consistent) `m1`,
    # never exercising the inconsistent-head-kind check at all.
    assert {:error, {:inconsistent_head_kind, :Bad}} = Program.elaborate(src)
  end
end
```

- [ ] **Step 2: Run it, watch it fail**

Run: `mix test test/cure/elab/interface_elab_test.exs`
Expected: FAIL — `{:interface, …}` is not handled in `program.ex`, so elaboration errors (`{:unsupported_definition, …}` or `Env.get_interface/2` undefined).

- [ ] **Step 3: Implement `Cure.Elab.Interface` + Env plumbing + head-kind inference**

Add `Env` field `interfaces: %{}` with `put_interface/3`, `get_interface/2`. In `interface.ex`: infer the head kind by scanning method signatures for the head var's occurrences (bare ⇒ `:type`; applied `f(_)` ⇒ `{:arrow, :type, :type}`; both ⇒ error). Build the record type former using the existing dependent-record Core machinery (the same path dependent records take — see `dependent-records-finding`), one field per method with its (implicit-generalised) signature. Capture default bodies. In `program.ex`, dispatch `{:interface, …}` to `Interface.elaborate/2` and store the descriptor + register the type former as a def.

- [ ] **Step 4: Run green; Step 5: scoped regression + commit**

Run: `mix test test/cure/elab/interface_elab_test.exs test/cure/elab/`
```bash
git add -- lib/cure/elab/interface.ex lib/cure/core/inductive.ex lib/cure/elab/program.ex test/cure/elab/interface_elab_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): interface -> Core record type former + head-kind inference"
```

---

### Task 3: Coherence registry + implementation → dictionary value

**Files:** Create `lib/cure/elab/coherence.ex`, `lib/cure/elab/implementation.ex`. Modify `program.ex` (dispatch `{:implementation, …}`), `lib/cure/core/inductive.ex` (carry the coherence registry — this is where `Cure.Core.Env` lives, not a separate `env.ex`). Test: `test/cure/elab/implementation_elab_test.exs` (new).

**Interfaces:**
- Consumes `{:implementation, meta, methods}` (Task 1) + interface descriptor (Task 2).
- Produces: a dictionary value (record literal of the interface record type) as a def; registers it in the coherence registry keyed `(iface, head_ctor)` for anonymous, or by name for named. Errors: `{:overlapping_instance, iface, head}`, `{:orphan_instance, iface, head}`, `{:no_such_interface, iface}`, `{:missing_method, iface, m}` (no clause and no default). `Coherence` API: `register_anon/4`, `register_named/4`, `lookup_anon/3`, `lookup_named/2`. Primitive head types (Int/Float/Bool/String/Atom, no defining module) are orphan-exempt (§3.4).

- [ ] **Step 1: Write the failing test**

```elixir
defmodule Cure.Elab.ImplementationElabTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Coherence}
  alias Cure.Core.Env

  defp env!(src), do: (fn -> {:ok, e} = Program.elaborate(src); e end).()

  test "an anonymous implementation registers a dictionary for (iface, head)" do
    e = env!("""
    mod M
      interface Eqs(a)
        fn eqs(x: a, y: a) -> Bool
      implementation Eqs for Int
        fn eqs(x: Int, y: Int) -> Bool = int_eq(x, y)
    end
    """)
    assert {:ok, _dict_ref} = Coherence.lookup_anon(Env.coherence(e), :Eqs, :Int)
  end

  test "a duplicate anonymous instance is an overlap error" do
    assert {:error, {:overlapping_instance, :Eqs, :Int}} = Program.elaborate("""
    mod M
      interface Eqs(a)
        fn eqs(x: a, y: a) -> Bool
      implementation Eqs for Int
        fn eqs(x: Int, y: Int) -> Bool = int_eq(x, y)
      implementation Eqs for Int
        fn eqs(x: Int, y: Int) -> Bool = int_eq(x, y)
    end
    """)
  end

  test "an implementation omitting a method with a default is filled from the default" do
    e = env!("""
    mod M
      interface Eqs(a)
        fn eqs(x: a, y: a) -> Bool
        fn nes(x: a, y: a) -> Bool = true
      implementation Eqs for Int
        fn eqs(x: Int, y: Int) -> Bool = int_eq(x, y)
    end
    """)
    # `nes` must be indented to the same level as `eqs` — nested inside the
    # interface — to be captured as a default at all; otherwise it's an
    # unrelated top-level def with a free `a`, and `Eqs` has only `eqs`, so
    # the `implementation` below is a complete (not omitting) impl and never
    # exercises the default-fill path this test is named for. The dictionary
    # value's `nes` field is a live, running default; deeper behavioural
    # verification of the filled-in default's VALUE happens once method-call
    # resolution exists (Task 4) and via the stdlib's real `Equatable.ne`
    # default (Task 8) — here we assert only that registration succeeds
    # despite the omission.
    {:ok, _} = Coherence.lookup_anon(Env.coherence(e), :Eqs, :Int)
  end
end
```

- [ ] **Step 2: Run it, watch it fail**

Run: `mix test test/cure/elab/implementation_elab_test.exs`
Expected: FAIL — `{:implementation, …}` unhandled; `Coherence`/`Env.coherence` undefined.

- [ ] **Step 3: Implement `Coherence`, `Implementation`, Env plumbing**

`Coherence`: a struct `%{anon: %{ {iface, head} => ref }, named: %{ name => ref }}` with the register/lookup fns; `register_anon` raises the overlap/orphan errors. `Implementation.elaborate/3`: look up the interface descriptor; for each method, take the impl clause or the interface default (closed over this instance's other methods, §3.3); build a record-literal dictionary value of type `Iface(head)`; register it. `program.ex`: dispatch `{:implementation, …}`, thread the coherence registry through module elaboration; `Env.coherence/1` + `put_coherence/2`. Head-ctor extraction for the key uses the head type expr's outermost constructor.

- [ ] **Step 4: Run green; Step 5: scoped regression + commit**

```bash
git add -- lib/cure/elab/coherence.ex lib/cure/elab/implementation.ex lib/cure/core/inductive.ex lib/cure/elab/program.ex test/cure/elab/implementation_elab_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): coherence registry + implementation -> dictionary value"
```

---

### Task 4: First-order resolution — method calls + constraints (kind-`Type`)

**Files:** Create `lib/cure/elab/resolve.ex`. Modify `elaborator.ex` (method-call elaboration in the expr dispatchers; constraint `where`-clause → implicit dict param; erasure demotion), `declarations.ex` (constraint param insertion; the erasure occurs-check demotion, §3.5). Test: `test/cure/elab/resolve_firstorder_test.exs` (new).

**Interfaces:**
- Consumes interface descriptors + coherence registry.
- Produces: an interface-method call at a concrete site elaborates to the **inlined** implementation method (no dict value); at an abstract site (rigid head var under a `where Iface(a)` constraint) elaborates to a **projection** off the implicit dict param; `{:no_instance, iface, T}` otherwise. A `where Iface(a)` constraint inserts an implicit param `dict_<Iface>_<var> : Iface(a)`, demoted to quantity `0` iff an occurs-check finds no method use.

- [ ] **Step 1: Write the failing test** (concrete inline, abstract projection, no-instance, erasure)

```elixir
defmodule Cure.Elab.ResolveFirstOrderTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}
  alias Cure.Core.Env

  defp run(src, mod, fun, args) do
    {:ok, env} = Program.elaborate(src)
    {:ok, m} = Emit.compile_and_load(env, module: mod, functions: [fun])
    apply(m, fun, args)
  end

  test "concrete method call inlines the implementation and runs" do
    src = """
    mod C1
      interface Eqs(a)
        fn eqs(x: a, y: a) -> Bool
      implementation Eqs for Int
        fn eqs(x: Int, y: Int) -> Bool = int_eq(x, y)
      fn test(x: Int, y: Int) -> Bool = eqs(x, y)
    end
    """
    assert run(src, :"Cure.C1", :test, [3, 3]) == true
    assert run(src, :"Cure.C1", :test, [3, 4]) == false
  end

  test "polymorphic constrained fn resolves via the implicit dictionary, two instances" do
    src = """
    mod C2
      interface Eqs(a)
        fn eqs(x: a, y: a) -> Bool
      implementation Eqs for Int
        fn eqs(x: Int, y: Int) -> Bool = int_eq(x, y)
      implementation Eqs for Bool
        fn eqs(x: Bool, y: Bool) -> Bool = eq(x, y)
      fn same({a: Type}, x: a, y: a) -> Bool where Eqs(a) = eqs(x, y)
      fn sameInt(x: Int, y: Int) -> Bool = same(x, y)
      fn sameBool(x: Bool, y: Bool) -> Bool = same(x, y)
    end
    """
    # `same`'s dict parameter is a REAL runtime argument (spec §8: v1 threads
    # runtime dictionaries at abstract sites, no monomorphisation) — its own
    # emitted arity is 3 (dict, x, y), so it cannot be called directly via a
    # bare 2-arg `apply/3` from outside Cure (that would be a permanent
    # arity mismatch, not a red-then-green test). `sameInt`/`sameBool` call
    # `same` from a concrete call site, where Resolve supplies the resolved
    # dictionary reference as the extra argument; the wrappers get a clean
    # 2-arg emitted arity and are what this test actually invokes — mirroring
    # the established `functions: [:id, :g]` multi-function convention
    # (test/cure/elab/polymorphic_function_test.exs), not the single-function
    # `run/4` helper above.
    {:ok, env} = Program.elaborate(src)

    {:ok, m} =
      Emit.compile_and_load(env, module: :"Cure.C2", functions: [:same, :sameInt, :sameBool])

    assert apply(m, :sameInt, [1, 1]) == true
    assert apply(m, :sameBool, [true, false]) == false
  end

  test "a method call on a type with no instance is a clean no_instance error" do
    src = """
    mod C3
      interface Eqs(a)
        fn eqs(x: a, y: a) -> Bool
      type Foo = MkFoo
      fn test(x: Foo, y: Foo) -> Bool = eqs(x, y)
    end
    """
    assert {:error, {:no_instance, :Eqs, _}} = Program.elaborate(src)
  end
end
```

- [ ] **Step 2: Run it, watch it fail** — `mix test test/cure/elab/resolve_firstorder_test.exs`; expected: method calls elaborate as ordinary unknown calls / `{:unbound, :eqs}` or `{:no_instance}` missing.

- [ ] **Step 3: Implement `Resolve` (first-order) + constraint plumbing.** `Resolve.method_call/5`: detect the callee is an interface method; infer the head-arg type; recover the head ctor; `lookup_anon` → inline that dictionary field's body applied to the args; else if the head is a rigid var with an in-scope constraint → project `dict.<m>`; else `{:no_instance, …}`. In `declarations.ex`, parse the `where Iface(a)` clause into an implicit `dict` param placed after the type params; after elaborating the body, run an occurs-check for dict uses and set quantity `0`/`ω` (safe demotion only — never promote; see `erasure-relevance-check-decision`). Wire `Resolve.method_call` into the expression-application dispatchers in `elaborator.ex`.

- [ ] **Step 4: Add the erasure test**

```elixir
  test "an unused dictionary is erased (quantity 0), a used one is present" do
    src = """
    mod C4
      interface Eqs(a)
        fn eqs(x: a, y: a) -> Bool
      implementation Eqs for Int
        fn eqs(x: Int, y: Int) -> Bool = int_eq(x, y)
      fn ignore({a: Type}, x: a) -> a where Eqs(a) = x
      fn same({a: Type}, x: a, y: a) -> Bool where Eqs(a) = eqs(x, y)
    end
    """
    {:ok, env} = Program.elaborate(src)
    forms = Emit.module_forms(env, :"Cure.C4", [:ignore, :same])
    arities = for {:function, _line, name, arity, _clauses} <- forms, into: %{}, do: {name, arity}

    # ignore/1's body never calls `eqs` -> the occurs-check demotes the dict
    # to erased; only the runtime-relevant `x` survives emission (arity 1).
    assert arities[:ignore] == 1
    # same/2's body calls `eqs(x, y)` via the dict -> it stays present
    # (arity 3: dict, x, y — the {a: Type} param is erased either way).
    assert arities[:same] == 3
  end
```
Implement the occurs-check demotion until this passes.

- [ ] **Step 5: Run green; scoped regression + commit**

```bash
git add -- lib/cure/elab/resolve.ex lib/cure/elab/elaborator.ex lib/cure/elab/declarations.ex test/cure/elab/resolve_firstorder_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): first-order typeclass resolution + constraint dict params + erasure"
```

---

### Task 5: Higher-kinded resolution (Functor) via pattern-fragment unification

**Files:** Extend `lib/cure/elab/resolve.ex`. Test: `test/cure/elab/resolve_hkt_test.exs` (new).

**Interfaces:**
- Consumes a `{:arrow, :type, :type}`-headed interface (Task 2).
- Produces: for a higher-kinded interface method, recover the type constructor by solving `?f(?a) =?= T` in the Miller pattern fragment (§3.4), key on `?f`'s constructor, then resolve as in Task 4. Non-`C(_)` head arg ⇒ `{:no_instance, iface, T}`.

- [ ] **Step 1: Write the failing test**

```elixir
defmodule Cure.Elab.ResolveHktTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  defp run(src, mod, fun, args) do
    {:ok, env} = Program.elaborate(src)
    {:ok, m} = Emit.compile_and_load(env, module: mod, functions: [fun])
    apply(m, fun, args)
  end

  test "fmap over List resolves via type-constructor extraction and runs; element type changes" do
    src = """
    mod H1
      use Std.List
      interface Functor(f)
        fn fmap(container: f(a), g: a -> b) -> f(b)
      implementation Functor for List
        fn fmap(container: List(a), g: a -> b) -> List(b) = Std.List.map(container, g)
      fn bump(xs: List(Int)) -> List(Int) = fmap(xs, fn(x) -> x + 10)
    end
    """
    assert run(src, :"Cure.H1", :bump, [[1, 2, 3]]) == [11, 12, 13]
  end

  test "a Functor method on a non-applied type is a clean no_instance error" do
    src = """
    mod H2
      interface Functor(f)
        fn fmap(container: f(a), g: a -> b) -> f(b)
      fn bad(x: Int) -> Int = fmap(x, fn(y) -> y)
    end
    """
    assert {:error, {:no_instance, :Functor, _}} = Program.elaborate(src)
  end
end
```

- [ ] **Step 2: Run it, watch it fail** — expected: no HKT head-key recovery yet, so `fmap` on `List(Int)` fails to resolve (`{:no_instance}` or a unification failure) even though the instance exists.

- [ ] **Step 3: Implement HKT head-key recovery.** In `Resolve`, when the interface head kind is `{:arrow, :type, :type}`: take the method-signature position where the head appears applied (`f(a)`), unify the corresponding argument's inferred type against `?f(?a)` restricted to the Miller pattern fragment (reuse the existing index-metavariable solver — `deferred-domain-metavar-finding`/`return-type-flow-finding`), extract `?f`'s constructor as the key, then resolve as Task 4. Anything outside the fragment ⇒ `{:no_instance, …}` (never a divergent solve). **If the existing solver cannot be reused without a `lib/cure/core/*` change, STOP** (TCB hard-stop) and report before proceeding.

- [ ] **Step 4: Run green; scoped regression + commit**

```bash
git add -- lib/cure/elab/resolve.ex test/cure/elab/resolve_hkt_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): higher-kinded (Functor) resolution via pattern-fragment unification"
```

---

### Task 6: Retire `struct_eq`/`struct_ne` + repoint `==`/`<` to resolution

**Files:** Modify `lib/cure/core/builtins.ex` (`@struct_ops` ~73, body-less seeding), `lib/cure/core/normalise.ex` (fold ~335), `lib/cure/elab/emit.ex` (~303, ~334), `lib/cure/elab/guard_lint.ex` (~100), `lib/cure/elab/elaborator.ex` (`build_binop` `:==`/`:!=` ~725 and the `<`/`<=`/… arms). Tests: modify `test/cure/elab/resolve_firstorder_test.exs` additions; delete/replace struct_eq-asserting tests (licensed). New: `test/cure/elab/eq_retirement_test.exs`.

**Interfaces:**
- Consumes Equatable/Ord resolution (Tasks 4/8).
- Produces: `==`/`!=` on any type resolve to `Equatable.eq`/`ne`; `<`/`<=`/`>`/`>=` to `Ord` methods; `struct_eq`/`struct_ne` globals no longer exist; a type with no `Equatable` instance under `==` is `{:no_instance, Equatable, T}` (behavioural change from struct_eq's accept-anything).

- [ ] **Step 1: Write the failing test** (`eq_retirement_test.exs`): (a) `struct_eq` absent from the seeded env (`refute` it is a known global); (b) `==` on an ADT **with** a derived/declared `Equatable` instance runs; (c) `==` on an ADT with **no** instance ⇒ `{:no_instance, Equatable, _}`; (d) `==` on `Int` still runs and still emits `int_eq` (assert via `Emit.module_forms` the `:==`/`int_eq` op, unchanged code).

- [ ] **Step 2: Run it, watch it fail** — struct_eq still seeded; `==` on ADT still routes to struct_eq (accepts anything), so (a) and (c) fail.

- [ ] **Step 3: Implement.** Delete the `struct_eq`/`struct_ne` entries from `builtins.ex` `@struct_ops` + their seeding; remove the `normalise.ex` fold arm, `emit.ex` `lower_builtin_op`/`builtin_op_wrapper` arms, and `guard_lint.ex` handling. In `elaborator.ex` `build_binop`, replace the 4-way `:==`/`:!=` dispatch (and the `<`/… arms) with a call to `Resolve.method_call` for `Equatable.eq`/`ne` (resp. `Ord.*`) on the operand type — the primitive `Int`/`Float`/… cases now resolve through the (Task 8) primitive instances and inline `int_eq`/… (identical emitted code).

- [ ] **Step 4: Delete the licensed struct_eq tests.** Find tests asserting struct_eq/struct_ne seeding or behaviour (the Stage-1 review noted ≥2) and remove/replace them — this is the one licensed test change (state it in the commit). Everything else must stay green by implementation.

- [ ] **Step 5: Run green; scoped regression + commit**

```bash
git add -- lib/cure/core/builtins.ex lib/cure/core/normalise.ex lib/cure/elab/emit.ex lib/cure/elab/guard_lint.ex lib/cure/elab/elaborator.ex test/cure/elab/eq_retirement_test.exs test/cure/core/builtin_op_test.exs test/cure/elab/binop_lowering_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat: retire struct_eq/struct_ne; == and < resolve via Equatable/Ord

Removes the polymorphic structural-equality builtin-op and the 4-way == dispatch;
primitive types now resolve through their Equatable/Ord instances (identical
emitted code). Deletes the tests that asserted the retired struct_eq behaviour."
```

---

### Task 7: Deriving — structural Equatable / Ord / Show

**Files:** Create `lib/cure/elab/deriving.ex`. Modify `program.ex` (expand `type … deriving I` and standalone `derive`). Test: `test/cure/elab/deriving_test.exs` (new).

**Interfaces:**
- Consumes a `type` descriptor + a target interface.
- Produces: a generated `implementation I for T` (registered like a hand-written one) whose method is structural — matches constructors, compares/renders fields pairwise via **their own** instance (recursively resolved; self-recursion memoised by name). Covers `Equatable`, `Ord`, `Show`. Mutual recursion across a batch: two-pass (signatures then bodies) OR a documented v1 scope-cut (§7).

- [ ] **Step 1: Write the failing test** — `deriving Equatable` on a recursive ADT (`type Tree = Leaf | Node(Tree, Int, Tree)`), assert two equal trees compare `true`, unequal `false`; `deriving Show` renders a nested value; `deriving Ord` orders by constructor then field. **Invoke the interface methods directly** — `eq(t1, t2)` / `lt(t1, t2)` / `show(t)` — **not** the `==`/`<` infix operators. Task 7 depends only on Task 4 and may run before Task 6 (they're independent siblings in the dependency order); until Task 6 retires it, `==`/`<` on an ADT still fall through the OLD 4-way `build_binop` dispatch to `struct_eq`/`struct_ne` (which lowers straight to BEAM's native `==`, itself a real deep structural comparator — see Task 6 §Interfaces) or the primitive int/float arms, so `t1 == t2` on two equal `Tree` values would already evaluate `true` with **no** `Equatable` instance registered at all. A test phrased with `==`/`<` would not go red before Task 7's implementation exists, defeating the point of the red test. Calling `eq`/`lt`/`show` as ordinary interface methods routes through Task 4's `Resolve.method_call`, independent of whichever order Tasks 6/7 land in.

- [ ] **Step 2: Run it, watch it fail** — `deriving` currently parsed (Task 1) but no instance generated ⇒ `eq(t1, t2)`/`show(t)`/`lt(t1, t2)` on the ADT is `{:no_instance, …}` (an unresolved interface method call, per Task 4's contract).

- [ ] **Step 3: Implement `Deriving.generate/3`** for each of the three interfaces: build the method AST structurally from the type's constructors/fields, emit an `{:implementation, …}` and route it through Task 3's registration. Memoise `(interface, head)` during generation so a recursive field resolves to the in-progress instance by name.

- [ ] **Step 4: Run green; scoped regression + commit**

```bash
git add -- lib/cure/elab/deriving.ex lib/cure/elab/program.ex test/cure/elab/deriving_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): deriving Equatable/Ord/Show (structural, recursion-safe)"
```

---

### Task 8: Migrate the 5 stdlib protocol modules

**Files:** `lib/std/{equatable,ord,show,functor,access}.cure`. Test: `test/cure/stdlib/typeclass_migration_test.exs` (new).

**Interfaces:** each module rewritten `proto`/`impl` → `interface`/`implementation`, elaborates through the dependent pipeline, methods resolve + run. **Circularity fix:** primitive `Equatable`/`Ord` impls reference the builtin-op directly (`int_eq(a,b)`, not `a == b` — §4.2). Functor → true HKT (§3.1/Task 5). `String`/`Atom` equality: use the correct primitive (or a documented BEAM-`==` special case — the review noted no `string_eq`/`atom_eq` builtin-op exists; add one or special-case, do NOT invent a repoint). **Access risk (§7):** `access.cure`'s keyword-list helpers (e.g. `kw_fetch`, `access.cure:532`) use `==`/`!=` on statically `Any`-typed operands — §3.4's resolution has no rule for `Any` at all (neither a concrete head nor a rigid var under a constraint), so this is expected, not a surprise, to hit the §5 blocker rule; if it does, STOP and document it as a blocker rather than inventing an ad-hoc `Any` resolution rule.

- [ ] **Step 1: Write the failing test** — for each module, elaborate it (`Program.elaborate(File.read!(...))`) and run a representative method: `eq(1,1)`, `Std.Ord` `lt`, `show` of a value, `fmap([1,2,3], …)`, an `Access` getter. Assert results.

- [ ] **Step 2: Run it, watch it fail** — modules still use `proto`/`impl`; the new pipeline doesn't elaborate them as interfaces.

- [ ] **Step 3: Migrate each module** in dependency order (Equatable → Ord → Show → Functor → Access). For each: convert `proto` → `interface`, `impl … for …` → `implementation … for …`, fix the primitive-impl circularity, and (Ord) add the `Ordering` `Equatable` instance its helpers need. If a module cannot elaborate for reasons unrelated to typeclasses (§5 blocker rule), STOP, document the blocker in the commit + a note, and continue with the rest — do not paper over it.

- [ ] **Step 4: Run green; scoped regression + commit** (one commit per module or one for the batch; each module's test green before moving on).

```bash
git add -- lib/std/equatable.cure test/cure/stdlib/typeclass_migration_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(std): migrate Equatable to interface/implementation"
# ... repeat per module ...
```

---

### Task 9: Differential oracle cluster (cure-porting)

**Files:** `test/oracle/typeclass/*.cure` + `*.idr` pairs; run via `mix cure.oracle typeclass`; freeze `verdicts.json`; `test/oracle_replay_test.exs` stays green.

**Interfaces:** paired Cure/Idris2 programs verifying Cure's accept/reject matches Idris2 for: basic interface+implementation+method call; a constrained polymorphic function; coherence overlap (both reject); a missing instance (both reject); deriving; Functor/HKT resolution.

- [ ] **Step 1** Author the paired probes (faithful transliterations, `%default total`, no `module` line on the `.idr`).
- [ ] **Step 2** `mix cure.oracle typeclass`; triage each divergence by the relation contract (`same` / `cure_stricter` with written reason / `idris_only`); a Cure-accepts/Idris-rejects is a STOP-and-report soundness surprise.
- [ ] **Step 3** Freeze `verdicts.json`; `mix test test/oracle_replay_test.exs` green.
- [ ] **Step 4** Commit.

```bash
git add -- test/oracle/typeclass/ test/oracle_replay_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "test(oracle): typeclass differential cluster vs Idris2"
```

---

## Final gate

- [ ] Run the full suite ONCE, alone: `mix test`. Expected: green. Triage every newly-failing `==`/`<` site (Task 6 blast radius) as real regression vs. a type that legitimately now needs a derived instance — fixing by *adding the instance*, never by restoring struct_eq. Confirm `struct_eq`/`struct_ne` are gone and all 5 migrated modules run.
