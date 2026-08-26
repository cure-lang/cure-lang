# `Std.Otp` Conformance Fixes — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Close the conformance defects the executed audit found in Cure's typed BEAM process algebra — the typed layer must stop claiming things the BEAM does not deliver.

**Architecture:** Three elaborator additions (`@erases(<class>)`, so a constructor-less FFI carrier can declare the Erlang guard that recognises its erasure; `:pid`/`:reference` union member classes; and permitting an `@extern` to return `Effect(<union>)`) unlock five stdlib repairs (phantom-tagged `Pid` vs `GenServer`; a `whereis` that can fail and cannot lie about the message type; honest raw result types; distinct `MonitorRef`/`TimerRef`; a precise `ExitReason`). No kernel change.

**Tech Stack:** Elixir (the compiler), Cure (the stdlib, `lib/std/*.cure`), ExUnit.

## Global Constraints

- **TCB delta: zero.** `lib/cure/core/**` is the kernel. The ONLY file under it this plan touches is `lib/cure/core/inductive.ex`, and only to add an `erasure` field to the opaque-family *record* (a map key with a `nil` default). No typing rule, no conversion rule, no elimination rule changes. If a task finds itself editing `kernel.ex`, `normalise.ex`, `conv.ex`, or `context.ex`, **stop** — the design is wrong.
- **Spec:** `docs/superpowers/specs/beam/2026-07-14-otp-conformance-fixes-design.md`, **including its §7 planning amendments**, which supersede §3.2 and §3.3 where they conflict. **Evidence base:** `https://github.com/cure-lang/cure-otp/tree/main/docs/research/process-types/raw-algebra-conformance-checklist.md`.
- **Out of scope, do not implement:** F-1 (grounding the pid index — Rung 2), the honest `start_link` return, `try_call`, retargeting `send_after` at `start_timer/3`. Spec §2 and §6.
- **Test discipline:** strict red-green-refactor. Write the test, run it, confirm it fails *for the stated reason*, then write the minimal code to pass. A green test is immutable — never weaken or delete one to accommodate a later step. **Two pre-existing tests are the sole sanctioned exception** (Tasks 4 and 7), named there explicitly because they encode the very defects this batch closes.
- **One build at a time.** Never launch concurrent `mix test` runs.
- **Commit after every task.**
- Author stdlib in `lib/std/`, never `priv/std/` (that is a generated bundle).

## Verified surface facts

These were probed against the compiler while planning. Do not re-derive them; do not
"fix" code that conforms to them.

- A union **member must be ground**. `Box(a) | :undefined` with `a` a type variable is
  rejected: `{:union_member_not_ground, …}`. `Box(Empty, Empty, Tag)` — all arguments
  ground — is accepted.
- A union **match has no catch-all**. One arm per member: a type member binds with an
  ascription (`n: Int -> …`), a literal member is the bare literal (`:undefined -> …`).
  A non-exhaustive match is rejected by the coverage check.
- **Kinded type parameters do not exist.** `type Box(a, k: Kind)` is rejected with
  `{:conversion_failure, {:data, :Kind, [], []}, {:type, 0}}`. Every type parameter is at
  kind `Type`. Phantom tags are the encoding (spec §7.1).
- A **zero-constructor type** is written `type NoMessage = |` (precedent:
  `lib/std/decision.cure:27`).
- `Option`/`Some`/`None` come from `use Std.Option`; the unit value is `unit()`.

---

## File Structure

**Elaborator (new capability):**
- `lib/cure/compiler/parser.ex` — attach a decorator to an `opaque type`.
- `lib/cure/elab/declarations.ex` — read and validate `@erases(:class)`; let an `@extern` return `Effect(<union>)`; update its two callers of the now-`env`-first `Union.discriminable/2` and `Union.family_key/2`.
- `lib/cure/core/inductive.ex` — `opaque_family/4` carries an `erasure` field.
- `lib/cure/elab/union.ex` — resolve a member's runtime class from the declared erasure; `:pid`/`:reference` classes and their overlap rules; `env` threaded to the class resolver.
- `lib/cure/elab/emit.ex` — `env` threaded to the union-dispatch emitter; `is_pid`/`is_reference` guards; look through `Effect` when re-tagging.
- `lib/cure/elab/resolution.ex` — update its one caller of the now-`env`-first `Union.family_key/2`.
- `lib/cure/compiler/errors.ex` — a `format_error` clause naming the admissible `@erases` classes (spec §4 item 2).

**Stdlib (the repairs):**
- `lib/std/otp_raw.cure` — the sealed raw base.
- `lib/std/otp.cure` — the typed surface.

**Tests:**
- `test/cure/elab/erases_decorator_test.exs` — new.
- `test/cure/elab/union_test.exs` — extend (`:pid`/`:reference` members, `Effect(<union>)` externs).
- `test/cure/stdlib/otp_test.exs` — extend + two sanctioned edits.
- `test/cure/stdlib/otp_raw_pin_test.exs` — new. The regression pin.

---

## Task 1: `@erases(<class>)` — declare an opaque carrier's runtime shape

**Why:** `Union.discriminable/1` rejects any member whose runtime class is `:unsupported`. An `opaque type` has zero constructors and therefore no inferable erasure, so `RawPid(…) | :undefined` is rejected today. The shape must be *declared*.

**Files:**
- Modify: `lib/cure/compiler/parser.ex` (`parse_at_attach/4`, ~line 6466)
- Modify: `lib/cure/elab/declarations.ex` (the `:opaque` declaration branch, ~line 100)
- Modify: `lib/cure/core/inductive.ex` (`opaque_family/3`, line 322)
- Modify: `lib/cure/compiler/errors.ex` — a `format_error` clause for `:unknown_erasure_class` (spec §4 item 2 requires the error to name the admissible set; see Step 5b).
- Test: `test/cure/elab/erases_decorator_test.exs` (create)

**Interfaces:**
- Produces: `Cure.Core.Inductive.opaque_family(name, param_tele, level, erasure \\ nil)` — the family map gains `erasure: nil | :pid | :reference | :integer | :float | :binary | :atom | :boolean | :list`.
- Produces: `@erasure_classes` in `declarations.ex` — the admissible set.
- Produces: errors `{:unknown_erasure_class, name, class}` and `{:erases_on_non_opaque, name}`.
- Produces: `Cure.Compiler.Errors.format_error({:unknown_erasure_class, name, class}, file)` — names the admissible set in the rendered message (spec §4 item 2).

- [ ] **Step 1: Write the failing test**

Create `test/cure/elab/erases_decorator_test.exs`:

```elixir
defmodule Cure.Elab.ErasesDecoratorTest do
  @moduledoc """
  `@erases(<class>)` — an opaque FFI carrier declares the Erlang guard that recognises
  its erasure. An `opaque type` has no constructors, so its runtime shape cannot be
  inferred; it is asserted by the author of the sealed `unsafe` module. Spec §3.1.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.Inductive
  alias Cure.Elab.Program

  test "an @erases class is recorded on the opaque family" do
    src = """
    mod M
      @erases(:pid)
      opaque type Handle
    end
    """

    assert {:ok, env} = Program.elaborate(src)
    assert %{opaque: true, erasure: :pid} = Inductive.get_family(env, :Handle)
  end

  test "an opaque type without @erases has no declared erasure" do
    src = """
    mod M
      opaque type Handle
    end
    """

    assert {:ok, env} = Program.elaborate(src)
    assert %{opaque: true, erasure: nil} = Inductive.get_family(env, :Handle)
  end

  test "an unrecognised erasure class is a compile error" do
    src = """
    mod M
      @erases(:banana)
      opaque type Handle
    end
    """

    assert {:error, {:unknown_erasure_class, :Handle, :banana}} = Program.elaborate(src)
  end

  test "the unrecognised-class error names the admissible set (spec §4 item 2)" do
    error = {:unknown_erasure_class, :Handle, :banana}
    message = Cure.Compiler.Errors.format_error(error, "test.cure")

    for class <- [:pid, :reference, :integer, :float, :binary, :atom, :boolean, :list] do
      assert message =~ Atom.to_string(class),
             "the rendered message must name every admissible class; missing #{class}:\n#{message}"
    end
  end

  test "@erases on a type WITH constructors is a compile error" do
    src = """
    mod M
      @erases(:pid)
      type Colour = Red | Green
    end
    """

    assert {:error, {:erases_on_non_opaque, :Colour}} = Program.elaborate(src)
  end
end
```

- [ ] **Step 2: Run it and confirm it fails**

Run: `mix test test/cure/elab/erases_decorator_test.exs`
Expected: all five FAIL. The first two on the missing `erasure` key; the third and fourth because `@erases` is silently dropped — `parse_at_attach/4` has no `:opaque` branch, so elaboration returns `{:ok, _}`; the fifth (admissible-set message) because `Cure.Compiler.Errors.format_error/2` has no clause for `:unknown_erasure_class` yet and falls through to the generic `inspect(error)` catch-all, which does not name any class.

- [ ] **Step 3: Carry the erasure on the family record**

In `lib/cure/core/inductive.ex`, replace `opaque_family/3` (line 322 — keep the existing `@doc`, appending the new paragraph):

```elixir
  `erasure` is the runtime class its values take on the BEAM — declared by
  `@erases(<class>)`, since a family with NO constructors has no erasure to infer. `nil`
  means undeclared, which is what every opaque type that never crosses an anonymous union
  wants. The kernel never reads it; it is elaborator metadata riding on the family record.
  """
  @spec opaque_family(atom(), telescope(), non_neg_integer(), atom() | nil) :: family()
  def opaque_family(name, param_tele, level, erasure \\ nil),
    do: %{
      name: name,
      params: param_tele,
      indices: [],
      level: level,
      opaque: true,
      erasure: erasure
    }
```

- [ ] **Step 4: Attach the decorator to an `opaque type`**

In `lib/cure/compiler/parser.ex`, inside `parse_at_attach/4`'s `case peek(state) do`, add a branch beside the existing `:type` branch. `parse_type_def/2`'s opaque path already produces a `{:container, meta, []}` node and `attach_decorator/3`'s generic `{:container, …}` clause already writes `:decorator` into its meta — the only missing link is that `parse_at_attach/4` never dispatches on the `opaque` keyword:

```elixir
      # `@erases(:pid) opaque type Name` — the opaque container is a {:container, …}
      # node, which attach_decorator/3's generic clause threads :decorator meta into.
      # Without this branch the decorator is silently dropped and the carrier is left
      # with no declared erasure.
      %Token{type: :keyword, value: :opaque} ->
        {type_ast, state} = parse_type_def(advance(state), opaque: true)
        {attach_decorator(type_ast, dec_name, args), state}
```

Read the neighbouring `:type` branch first and match its exact call convention for
`parse_type_def/2` and `attach_decorator/3` — mirror it rather than retyping from here.

- [ ] **Step 5: Read, validate, and store the class**

In `lib/cure/elab/declarations.ex`, add the admissible set beside the other module attributes:

```elixir
  # The runtime classes an `@erases(<class>)` may name. Each maps to exactly one TOTAL
  # Erlang guard in `Cure.Elab.Emit.class_guard/1`, which is what makes an opaque carrier
  # discriminable inside an anonymous union.
  @erasure_classes [:pid, :reference, :integer, :float, :binary, :atom, :boolean, :list]
```

In the `:opaque` branch (~line 100), thread the class through. Preserve the branch's
existing param handling exactly — only the `with` and the final call change:

```elixir
      :opaque ->
        name = meta |> Keyword.fetch!(:name) |> String.to_atom()
        params = Keyword.get(meta, :type_params, []) |> Enum.map(&{:param, [], &1})

        with :ok <- reject_reserved_family_name(name),
             {:ok, erasure} <- erasure_class(meta, name),
             {:ok, param_tele} <-
               elaborate_index_telescope(params, name, env, [], :duplicate_parameter) do
          declare_opaque_at_min_level(env, name, param_tele, 0, erasure)
        end
```

Add the reader:

```elixir
  # `@erases(<class>)` on an opaque carrier. Absent → nil (undeclared, the common case).
  # Present but not admissible → a compile error naming the class, rather than a silently
  # undeclared carrier that fails much later inside union discrimination with an
  # unrelated message.
  defp erasure_class(meta, name) do
    case Keyword.get(meta, :decorator) do
      {:erases, [{:literal, _, class}]} when class in @erasure_classes -> {:ok, class}
      {:erases, [{:literal, _, class}]} -> {:error, {:unknown_erasure_class, name, class}}
      _ -> {:ok, nil}
    end
  end
```

Confirm the decorator's argument shape by reading `attach_decorator/3` — if an atom
literal arrives as something other than `{:literal, _, class}`, match what it actually
produces.

Widen the level-search helper (~line 2169) to carry `erasure`. Its current body is
**not** a single checked call — `Inductive.declare/3` returns `Env.t()` directly (no
`:ok`/`:error` tuple), and well-formedness is a *separate* `Kernel.check_family/2` call
against the freshly-declared family. Read its current bodies and change only the arity,
the `opaque_family` call, and the extra `erasure` argument threaded through the
recursive/ceiling calls:

```elixir
  defp declare_opaque_at_min_level(env, name, param_tele, level, erasure) when level <= @ceiling do
    family = Inductive.opaque_family(name, param_tele, level, erasure)
    env2 = Inductive.declare(env, family, [])

    case Kernel.check_family(env2, Inductive.get_family(env2, name)) do
      :ok ->
        {:ok, env2}

      {:error, :universe_level} ->
        declare_opaque_at_min_level(env, name, param_tele, level + 1, erasure)

      {:error, _} = err ->
        err
    end
  end

  defp declare_opaque_at_min_level(_env, _name, _param_tele, _level, _erasure),
    do: {:error, :universe_ceiling}
```

Then reject `@erases` on a type that has constructors — such a type already has an
inferable erasure, and a declared class could only contradict it. Add:

```elixir
  # `@erases` asserts the runtime shape of a carrier that has NO constructors and so no
  # inferable erasure. A type with constructors erases to a bare atom (nullary) or a
  # tagged tuple; a declared class could only ever disagree with that.
  defp reject_erases_on_non_opaque(meta) do
    case {Keyword.get(meta, :container_type), Keyword.get(meta, :decorator)} do
      {ct, {:erases, _}} when ct != :opaque ->
        {:error, {:erases_on_non_opaque, meta |> Keyword.fetch!(:name) |> String.to_atom()}}

      _ ->
        :ok
    end
  end
```

and call it as the first step of the container-declaration entry point — the function whose
`case` selects `:opaque` / `:enum` / `:struct` / `:primitive` — so every non-opaque branch
is covered by one check rather than three.

- [ ] **Step 5b: Name the admissible set in the rendered error**

Spec §4 item 2 requires the unrecognised-class error to name the admissible set, not just
the one bad value. `errors.ex` has an exact precedent for this: `known_editions_hint/0`
synthesises the valid-editions list at render time for `:edition_pragma_unknown` /
`:edition_error` (`lib/cure/compiler/errors.ex:237-256`) — the error tuple itself does not
carry the list; the `format_error` clause looks it up independently. Follow the same shape.
No existing elaborator-level error (`:extern_union_indistinct`, `:union_member_not_ground`,
etc.) has a dedicated `format_error` clause — they fall through to the generic
`inspect(error)` catch-all at the bottom of the file — so this is a new clause, not an
existing one to extend.

In `lib/cure/elab/declarations.ex`, export the admissible set so `errors.ex` can read it
without duplicating the list:

```elixir
  # Exposed for Cure.Compiler.Errors — the admissible @erases(<class>) set, named in the
  # :unknown_erasure_class message.
  def erasure_classes, do: @erasure_classes
```

In `lib/cure/compiler/errors.ex`, beside `known_editions_hint/0`, add:

```elixir
  def format_error({:unknown_erasure_class, name, class}, file) do
    format_diagnostic(
      "error",
      "unknown erasure class",
      file,
      0,
      "`@erases(#{inspect(class)})` on `#{name}` is not a known erasure class; " <>
        "known classes: #{known_erasure_classes_hint()}"
    )
  end
```

```elixir
  defp known_erasure_classes_hint,
    do: Cure.Elab.Declarations.erasure_classes() |> Enum.map_join(", ", &to_string/1)
```

Place the `format_error` clause with the other elaborator-error clauses (near
`{:type_mismatch, …}`), not with the parse/edition clauses — it is a semantic error, not a
lexical one. `known_erasure_classes_hint/0` belongs beside `known_editions_hint/0`.

- [ ] **Step 6: Run the test and confirm it passes**

Run: `mix test test/cure/elab/erases_decorator_test.exs`
Expected: 5 tests, 0 failures.

- [ ] **Step 7: Run the suites that could regress**

Run: `mix test test/cure/elab/ test/cure/compiler/`
Expected: 0 failures. `opaque_family/4`'s new argument defaults, so existing callers are unchanged.

- [ ] **Step 8: Commit**

```bash
git add lib/cure/compiler/parser.ex lib/cure/elab/declarations.ex lib/cure/core/inductive.ex lib/cure/compiler/errors.ex test/cure/elab/erases_decorator_test.exs
git commit -m "feat(elab): @erases(<class>) declares an opaque carrier's runtime shape

An opaque type has zero constructors and so no inferable erasure. Its runtime shape
must be declared before it can be discriminated inside an anonymous union."
```

---

## Task 2: `:pid` and `:reference` union member classes

**Why:** `Union.runtime_class/1` answers a member's class from a fixed name table and returns `:unsupported` otherwise, so `discriminable/1` rejects any opaque member. It must consult the family's declared `erasure` (Task 1). Members are rebuilt from their family key by `members_of/2`, so the class cannot be cached at canonicalisation — it must be resolvable from the key at every use, which means `env`.

**Files:**
- Modify: `lib/cure/elab/union.ex`
- Modify: `lib/cure/elab/emit.ex`
- Modify: `lib/cure/elab/declarations.ex` — two external callers of the widened functions
  (see below).
- Modify: `lib/cure/elab/resolution.ex` — one external caller of `family_key`.
- Test: `test/cure/elab/union_test.exs` (extend)

**Interfaces:**
- Consumes: `Inductive.get_family(env, name).erasure` (Task 1).
- Produces: `Union.runtime_class(env, member)`, `Union.disjoint_only?(env, members)`, `Union.family_key(env, members)`, `Union.discriminable(env, members)`, `Union.discrimination_order(env, members)` — every class-dependent function takes `env` **first**.
- Produces: `Emit.class_guard(:pid) → :is_pid`, `Emit.class_guard(:reference) → :is_reference`.

**Real external callers that break, and must be fixed in the same task.** `discriminable/1`
and `family_key/1` are called *outside* `union.ex`/`emit.ex` today, at three call sites —
verified by grepping the tree, not assumed:
- `lib/cure/elab/declarations.ex:441`, inside `check_extern_not_union/2`:
  `case Cure.Elab.Union.discriminable(Cure.Elab.Union.members_of(env, ukey)) do`. `env` is
  already bound in that function. Change to
  `Cure.Elab.Union.discriminable(env, Cure.Elab.Union.members_of(env, ukey))`.
- `lib/cure/elab/declarations.ex:1800`, inside `idx_to_core/5` (the anonymous-union index
  case): `{:ok, {:data, Cure.Elab.Union.family_key(ms), [], []}}`. `env` is a parameter of
  the enclosing clause. Change to
  `{:ok, {:data, Cure.Elab.Union.family_key(env, ms), [], []}}`.
- `lib/cure/elab/resolution.ex:231`: `new_key = Cure.Elab.Union.family_key(members)`. Confirm
  `env` is in scope in that function (it rekeys families during shadowing resolution); if the
  enclosing function does not already bind `env`, thread it in from its caller rather than
  widening `family_key`'s contract to make this one caller easier — the function-level
  `env` binding is the existing pattern used everywhere else in this task.

Without these three edits, `union.ex` compiles but the tree does not: `mix compile` fails
before a single test can run, because Elixir resolves `Union.discriminable/1` and
`Union.family_key/1` at compile time against the now-`/2` definitions. Step 7 below exists
specifically to catch a *missed* caller, not to serve as the mechanism for fixing these
three *known* ones — they are fixed here, in Step 5, alongside the rest of the widening.

- [ ] **Step 1: Write the failing test**

Append to `test/cure/elab/union_test.exs`:

```elixir
  describe "opaque carriers with a declared erasure" do
    test "an @erases(:pid) carrier is a legal union member" do
      src = """
      mod M
        @erases(:pid)
        opaque type Handle
        fn f(x: Handle | :undefined) -> Int = match x
          h: Handle -> 1
          :undefined -> 0
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      assert Inductive.family?(env, :"Union<Atom#:undefined|Handle>")
    end

    test "a pid carrier and a reference carrier do not collide" do
      src = """
      mod M
        @erases(:pid)
        opaque type Handle
        @erases(:reference)
        opaque type Tok
        fn f(x: Handle | Tok) -> Int = match x
          h: Handle -> 1
          t: Tok -> 2
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      assert Inductive.family?(env, :"Union<Handle|Tok>")
    end

    test "an @extern returning a pid-or-atom union is accepted and discriminated" do
      src = """
      mod EPX
        @erases(:pid)
        opaque type Handle

        @extern(:erlang, :whereis, 1)
        fn look(name: Atom) -> Handle | :undefined
      end
      """

      assert {:ok, _} = Cure.Compiler.compile_and_load(src)

      # An unregistered name yields the bare atom `undefined`, which the FFI wrapper
      # must re-tag into the literal member's nullary constructor.
      assert apply(:"Cure.EPX", :look, [:definitely_not_registered]) ==
               :"Union<Atom#:undefined|Handle>$Atom#:undefined"

      # A registered name yields a real pid, re-tagged by the is_pid guard.
      true = Process.register(self(), :epx_probe)
      assert {:"Union<Atom#:undefined|Handle>$Handle", pid} = apply(:"Cure.EPX", :look, [:epx_probe])
      assert pid == self()
      Process.unregister(:epx_probe)
    end

    test "an opaque member WITHOUT @erases is still rejected at an @extern boundary" do
      src = """
      mod EPY
        opaque type Handle

        @extern(:erlang, :whereis, 1)
        fn look(name: Atom) -> Handle | :undefined
      end
      """

      assert {:error, {:extern_union_indistinct, :look, _}} = Program.elaborate(src)
    end
  end
```

The two `compile_and_load` assertions pin the wrapper's exact re-tagged shape. If the
constructor key or tuple shape differs from what the existing union tests show, match what
`Union.ctor_key/2` actually produces — the *behaviour* being pinned is that a pid is
routed to the `Handle` member and a bare atom to the `:undefined` member, not the spelling.

- [ ] **Step 2: Run it and confirm it fails**

Run: `mix test test/cure/elab/union_test.exs`
Expected: the first three FAIL — `Handle` classifies as `:unsupported`, so the extern is rejected and the plain unions fail discrimination. The fourth (no `@erases`) should already pass; it is the guard proving `@erases` is what makes the difference.

- [ ] **Step 3: Resolve the class from the declared erasure**

In `lib/cure/elab/union.ex`, widen the class resolver to take `env` and consult the family first:

```elixir
  @spec runtime_class(Env.t(), member()) :: atom()
  def runtime_class(_env, %{payload: nil, lit_type_key: t}), do: class_of_type_key(t)
  def runtime_class(env, %{payload: ty}), do: class_of_core(env, ty)

  defp class_of_core(_env, {:int_type}), do: :integer
  defp class_of_core(_env, {:float_type}), do: :float
  defp class_of_core(_env, {:binary_type}), do: :binary
  defp class_of_core(_env, {:atom_type}), do: :atom

  # A family's DECLARED erasure (`@erases(<class>)`) wins: it is the only source of truth
  # for a constructor-less carrier, which has no erasure to infer. Fall back to the
  # built-in name table for the families whose erasure the compiler knows intrinsically
  # (Bool/Nat/Bounded/List), then to `:unsupported`.
  defp class_of_core(env, {:data, name, _p, _i}) do
    case Inductive.get_family(env, name) do
      %{erasure: class} when class != nil -> class
      _ -> class_of_data_name(bare_family_name(name))
    end
  end

  defp class_of_core(_env, _other), do: :unsupported
```

Keep every other existing `class_of_core/1` clause, widened with the `_env` first argument.

- [ ] **Step 4: Give the two new classes their overlap rules**

Read the existing overlap logic before editing — clause ORDER is load-bearing, and the
existing `:unsupported`/`:atom` handling must keep its current position relative to the
catch-all. A pid and a reference each occupy their own erased world: `is_pid` and
`is_reference` accept nothing any other class accepts, and nothing a Cure ADT erases to.
Two *different* carriers that both erase to a pid DO overlap, which is what correctly
makes `Handle | OtherPidHandle` inadmissible at an `@extern` — no guard order separates
them. Add, above the `:unsupported` clauses:

```elixir
  # A pid and a reference are their own erased worlds — `is_pid` and `is_reference` accept
  # nothing any other class accepts. But two DIFFERENT carriers that both erase to a pid
  # overlap, which is what correctly makes `Handle | OtherPidHandle` inadmissible.
  defp class_overlap?(:pid, :pid), do: true
  defp class_overlap?(:reference, :reference), do: true
  defp class_overlap?(:pid, _), do: false
  defp class_overlap?(_, :pid), do: false
  defp class_overlap?(:reference, _), do: false
  defp class_overlap?(_, :reference), do: false
```

`union.ex` may express overlap through a differently-named function (read `disjoint_only?/1`,
`discriminable/1` and `refines?/2` to see how classes are actually compared) — if so, add
the equivalent rules there instead. The requirement is the behaviour above, not this
function name.

- [ ] **Step 5: Thread `env` through the class-dependent functions**

In `union.ex`, widen `disjoint_only?`, `family_key`, `discriminable` and `discrimination_order`
to take `env` first and pass it to `runtime_class/2`. `canonicalise/3`, `declare/3` and
`declare_family/2` already bind `env`, so their internal calls are a mechanical widening.
`specificity/1` is applied to the *result* of `runtime_class` and needs no change.

Then fix the three external callers this widening breaks (listed above, under **Files**),
in the same step — these are compile-time breaks, not test failures, so they cannot be
deferred to Step 7:
- `lib/cure/elab/declarations.ex:441` — `Union.discriminable(members)` → `Union.discriminable(env, members)`.
- `lib/cure/elab/declarations.ex:1800` — `Union.family_key(ms)` → `Union.family_key(env, ms)`.
- `lib/cure/elab/resolution.ex:231` — `Union.family_key(members)` → `Union.family_key(env, members)`.

In `lib/cure/elab/emit.ex`, thread `env` from `function_form/2` (which already binds it)
down the chain that has none: `extern_form/4` → `union_dispatch/2` → `type_clause/1` →
`class_test/1` → `Union.runtime_class/2`, and `union_dispatch/2` → `Union.discrimination_order/2`.
Each gains `env` as its first parameter. No new control flow.

Then add the two guards beside the existing six in `class_guard/1`:

```elixir
  defp class_guard(:pid), do: :is_pid
  defp class_guard(:reference), do: :is_reference
```

- [ ] **Step 6: Run the union suites and confirm they pass**

Run: `mix test test/cure/elab/union_test.exs test/cure/elab/union_canonical_test.exs test/cure/elab/union_identity_test.exs test/cure/elab/union_namespace_test.exs`
Expected: 0 failures.

- [ ] **Step 7: Run the full suite once**

Run: `mix test`
Expected: 0 failures — Step 5 already fixed the three known external callers
(`declarations.ex:441`, `declarations.ex:1800`, `resolution.ex:231`). This run's job is to
catch a caller *missed* by that grep, not to be the mechanism that fixes a known one: `mix
test` cannot even start if a caller fails to compile, so a failure here means Step 5 missed
a site — go back and grep again (`grep -rn "Union\.\(discriminable\|family_key\|disjoint_only?\|discrimination_order\)\b" lib/`
excluding `union.ex`/`emit.ex`), fix it, and rerun.

- [ ] **Step 8: Commit**

```bash
git add lib/cure/elab/union.ex lib/cure/elab/emit.ex lib/cure/elab/declarations.ex lib/cure/elab/resolution.ex test/cure/elab/union_test.exs
git commit -m "feat(elab): :pid and :reference union member classes

A union resolves a member's runtime class from the family's declared @erases first,
falling back to the built-in name table. Threads env to the class resolver, since
members are rebuilt from their family key and cannot cache it."
```

---

## Task 3: An `@extern` may return `Effect(<union>)`

**Why:** **Every** op in `Std.Otp.Raw` is `Effect`-typed, and Tasks 5 and 6 give two of them union returns. A union under `Effect` is rejected today (`{:extern_returns_union, …}`): the declaration check and the wrapper emitter both match the codomain against a union family *exactly* and neither looks through `Effect`. Without this, **neither F-2c nor F-4's `cancel_timer` is expressible at all**.

`Effect(T)` has no runtime representation — the elaborator injects `{:effect_pure, …}` and `emit.ex` lowers it away — so an extern declared `Effect(Int | Bool)` hands back exactly the same untagged Erlang value as one declared `Int | Bool`, and the re-tagging wrapper is byte-for-byte identical.

**Files:**
- Modify: `lib/cure/elab/declarations.ex` (`check_extern_not_union/2`, ~line 435)
- Modify: `lib/cure/elab/emit.ex` (`extern_union_members/2`, ~line 232)
- Test: `test/cure/elab/union_test.exs` (extend)

**Interfaces:**
- Consumes: Task 2's classes.
- Produces: an `@extern` whose codomain is `{:effect_type, {:data, <union>, [], []}}` is accepted and re-tagged exactly as the bare union is. A union nested in a real structure stays rejected.

- [ ] **Step 1: Write the failing test**

Append to `test/cure/elab/union_test.exs`:

```elixir
  describe "an @extern returning Effect(<union>)" do
    test "the union is discriminated through the Effect wrapper" do
      src = """
      mod EFU
        @extern(:erlang, :abs, 1)
        fn raw(n: Int) -> Effect(Int | Binary)

        fn use_it(n: Int) -> Effect(Int) =
          let r = raw(n)
          match r
            i: Int -> i
            b: Binary -> 0
      end
      """

      assert {:ok, _} = Cure.Compiler.compile_and_load(src)

      # Effect is erased, so the wrapper must re-tag exactly as it would without it.
      assert apply(:"Cure.EFU", :raw, [-5]) == {:"Union<Binary|Int>$Int", 5}
      assert apply(:"Cure.EFU", :use_it, [-5]) == 5
    end

    test "indistinguishable members are still rejected under Effect" do
      src = """
      mod EFN
        @extern(:erlang, :abs, 1)
        fn raw(n: Int) -> Effect(Int | Nat)
      end
      """

      assert {:error, {:extern_union_indistinct, :raw, _}} = Program.elaborate(src)
    end

    test "a union nested in a real structure is still rejected" do
      src = """
      mod EFS
        @extern(:erlang, :tl, 1)
        fn raw(xs: List(Int)) -> Effect(List(Int | Bool))
      end
      """

      assert {:error, {:extern_returns_union, :raw, _}} = Program.elaborate(src)
    end
  end
```

- [ ] **Step 2: Run it and confirm it fails**

Run: `mix test test/cure/elab/union_test.exs`
Expected: the first two FAIL with `{:error, {:extern_returns_union, :raw, {:effect_type, …}}}` — the union is invisible under `Effect`, so it is treated as a *nested* union and rejected outright (and the indistinct check never even runs). The third should already pass.

- [ ] **Step 3: Look through `Effect` at the declaration check**

In `lib/cure/elab/declarations.ex`, in `check_extern_not_union/2`, strip a single `Effect` before the `case`:

```elixir
  defp check_extern_not_union(sig, env) do
    codomain =
      sig.pi
      |> extern_codomain(length(sig.quantities || []))
      |> strip_effect()

    case codomain do
```

(leave the `case` body exactly as it is) and add:

```elixir
  # `Effect(T)` has NO runtime representation — the elaborator injects `{:effect_pure, …}`
  # and `Emit.lower/2` erases it. An extern declared `Effect(Int | Bool)` therefore hands
  # back exactly the same untagged Erlang value as one declared `Int | Bool`, and the
  # re-tagging wrapper is identical. So look through it.
  #
  # A union nested in a real STRUCTURE (`List(Int | Bool)`) stays rejected by the `case`'s
  # fallback clause: re-tagging would have to walk the structure. `Effect` is not a
  # structure — it is a phantom.
  defp strip_effect({:effect_type, t}), do: t
  defp strip_effect(t), do: t
```

- [ ] **Step 4: Look through `Effect` at the wrapper emitter**

In `lib/cure/elab/emit.ex`, in `extern_union_members/2`, strip the same wrapper so the wrapper is actually generated:

```elixir
  defp extern_union_members(env, %{type: pi, quantities: quantities}) do
    case pi |> codomain_of(length(quantities || [])) |> strip_effect() do
      {:data, ukey, [], []} ->
        if Cure.Elab.Union.union_family?(ukey) do
          env
          |> Cure.Elab.Union.members_of(ukey)
          |> Enum.map(&Map.put(&1, :ctor, Cure.Elab.Union.ctor_key(ukey, &1)))
        end

      _ ->
        nil
    end
  end

  # See `Declarations.strip_effect/1`: Effect is erased at lowering, so a union under it
  # has exactly the runtime shape of the bare union and takes exactly the same wrapper.
  defp strip_effect({:effect_type, t}), do: t
  defp strip_effect(t), do: t
```

- [ ] **Step 5: Run the test and confirm it passes**

Run: `mix test test/cure/elab/union_test.exs`
Expected: 0 failures.

- [ ] **Step 6: Commit**

```bash
git add lib/cure/elab/declarations.ex lib/cure/elab/emit.ex test/cure/elab/union_test.exs
git commit -m "feat(elab): an @extern may return Effect(<union>)

Effect has no runtime representation, so a union under it has the same erased shape
as the bare union and takes the same re-tagging wrapper. Both the declaration check
and the emitter now look through it. A union nested in a real structure stays
rejected. Every op in the raw OTP base is Effect-typed, so nothing there could
return a union until now."
```

---

## Task 4: `Plain` / `Server` phantom tags — separating `Pid` from `GenServer` (F-2a)

**Why:** `typealias Pid(m) = RawPid(m, m)` and `typealias GenServer(q, r) = RawPid(q, r)` are aliases of the same constructor, so `Pid(m)` **is** `GenServer(m, m)`. `call`/`cast`/`stop` on a plain spawned process typecheck; at runtime the caller blocks 5 s and then exits `timeout`.

Per spec §7.1 the discriminator is a **phantom type tag at kind `Type`**, not a kinded index — kinded type parameters do not exist. Kind-polymorphic ops quantify `{k: Type}`.

**Files:**
- Modify: `lib/std/otp_raw.cure`
- Modify: `lib/std/otp.cure`
- Modify: `test/cure/stdlib/otp_test.exs` (extend + one sanctioned edit)

**Interfaces:**
- Produces: `Std.Otp.Raw`: `opaque type Plain`, `opaque type Server`, `@erases(:pid) opaque type RawPid(m, r, k)`.
- Produces: `Std.Otp`: `typealias Pid(m) = RawPid(m, m, Plain)`, `typealias GenServer(q, r) = RawPid(q, r, Server)`.
- Produces: `call`/`cast`/`stop` are `Server`-only. `tell`/`send_after`/`link`/`unlink`/`monitor`/`exit`/`is_alive`/`register` are tag-polymorphic (`{k: Type}`). `spawn`/`spawn_link`/`self` produce `Plain`.

- [ ] **Step 1: Write the failing tests**

Append to `test/cure/stdlib/otp_test.exs`. The existing `app/1` helper (line 15) wraps a body in `mod App` with `use Std.Otp` and `type Cmd = Inc | Dec`.

```elixir
  describe "Pid(m) and GenServer(q,r) are distinct (F-2a)" do
    test "call on a plain Pid is a compile error" do
      assert {:error, _} = app("  fn go(p: Pid(Cmd)) -> Effect(Int) =\n    call(p, Dec())\n")
    end

    test "cast on a plain Pid is a compile error" do
      assert {:error, _} = app("  fn go(p: Pid(Cmd)) -> Effect(Unit) =\n    cast(p, Inc())\n")
    end

    test "stop on a plain Pid is a compile error" do
      assert {:error, _} = app("  fn go(p: Pid(Cmd)) -> Effect(Unit) =\n    stop(p)\n")
    end

    test "call on a GenServer still succeeds" do
      assert {:ok, _} =
               app("  fn go(s: GenServer(Cmd, Int)) -> Effect(Int) =\n    call(s, Dec())\n")
    end

    test "tell accepts BOTH handles — a raw send to a gen_server lands in handle_info" do
      assert {:ok, _} = app("  fn go(p: Pid(Cmd)) -> Effect(Unit) =\n    tell(p, Inc())\n")

      assert {:ok, _} =
               app("  fn go(s: GenServer(Cmd, Int)) -> Effect(Unit) =\n    tell(s, Inc())\n")
    end

    test "link accepts both handles" do
      assert {:ok, _} = app("  fn go(p: Pid(Cmd)) -> Effect(Unit) =\n    link(p)\n")

      assert {:ok, _} =
               app("  fn go(s: GenServer(Cmd, Int)) -> Effect(Unit) =\n    link(s)\n")
    end
  end
```

- [ ] **Step 2: Run and confirm they fail**

Run: `mix test test/cure/stdlib/otp_test.exs`
Expected: the three "is a compile error" tests FAIL by *succeeding* — `call`/`cast`/`stop` on a `Pid(Cmd)` typecheck today. That is the defect. The three positive tests already pass.

- [ ] **Step 3: Add the tags and the third parameter in the raw base**

In `lib/std/otp_raw.cure`, above the `RawPid` declaration:

```cure
  ## Which BEAM protocol a process handle speaks — a PHANTOM TAG, carried as `RawPid`'s
  ## third type argument. A plain process answers only raw sends; a `gen_server`
  ## additionally answers `call`/`cast`/`stop`. Neither tag has values and neither reaches
  ## the BEAM: the distinction is erased entirely.
  opaque type Plain
  opaque type Server

  ## An opaque process identifier — the raw `erlang:pid()`. `@erases(:pid)` declares the
  ## guard that recognises it, which is what lets it appear in a union (see `raw_whereis`).
  @erases(:pid)
  opaque type RawPid(m, r, k)
```

Give every raw op that mentions a `RawPid` the third argument. `raw_self`, `raw_spawn`, `raw_spawn_link` produce `Plain`:

```cure
  @extern(:erlang, :self, 0)
  fn raw_self({m: Type}) -> Effect(RawPid(m, m, Plain))

  @extern(:erlang, :spawn, 1)
  fn raw_spawn({m: Type}, thunk: () -> Unit) -> Effect(RawPid(m, m, Plain))

  @extern(:erlang, :spawn_link, 1)
  fn raw_spawn_link({m: Type}, thunk: () -> Unit) -> Effect(RawPid(m, m, Plain))
```

`raw_send`, `raw_monitor`, `raw_send_after`, `raw_link`, `raw_unlink`, `raw_exit`, `raw_is_alive`, `raw_register` are tag-polymorphic — add `{k: Type}` and thread `k`:

```cure
  @extern(:erlang, :send, 2)
  fn raw_send({m: Type}, {r: Type}, {k: Type}, dest: RawPid(m, r, k), msg: m) -> Effect(Unit)

  @extern(:erlang, :link, 1)
  fn raw_link({m: Type}, {r: Type}, {k: Type}, pid: RawPid(m, r, k)) -> Effect(Unit)
```

…and the same shape for `raw_unlink`, `raw_is_alive`, `raw_register`, `raw_monitor`, `raw_send_after` — widen only the pid parameter to `RawPid(m, r, k)` and add `{k: Type}`, exactly as `raw_link` does above.

`raw_exit` is **not** the same shape as `raw_link` — it additionally takes the reason
parameter (`{x: Type}, reason: x`), which is not part of this task's change and must
survive it. Only the pid parameter widens:

```cure
  @extern(:erlang, :exit, 2)
  fn raw_exit({m: Type}, {r: Type}, {k: Type}, {x: Type}, pid: RawPid(m, r, k), reason: x) -> Effect(Unit)
```

(Task 6 later narrows this op's *return* type to `Effect(Bool)` — the signature above is
this task's contribution, the parameter list, unchanged from here on.)

`raw_cast`, `raw_call`, `raw_stop` are `Server`-only:

```cure
  @extern(:gen_server, :cast, 2)
  fn raw_cast({q: Type}, {r: Type}, server: RawPid(q, r, Server), msg: q) -> Effect(Unit)

  @extern(:gen_server, :call, 2)
  fn raw_call({q: Type}, {r: Type}, server: RawPid(q, r, Server), req: q) -> Effect(r)

  @extern(:gen_server, :stop, 1)
  fn raw_stop({q: Type}, {r: Type}, pid: RawPid(q, r, Server)) -> Effect(Unit)
```

Leave every *result* type as it is — Task 6 makes those honest. This task changes only the pid type. `raw_whereis` keeps its current return for now (Task 5 replaces it); give it the shape `fn raw_whereis({m: Type}, name: Atom) -> Effect(RawPid(m, m, Plain))`.

- [ ] **Step 4: Split the typed aliases**

In `lib/std/otp.cure`:

```cure
  ## A typed handle to a plain BEAM process accepting messages of type `m`. It answers
  ## raw sends, and nothing else.
  typealias Pid(m) = RawPid(m, m, Plain)

  ## A typed `gen_server` taking requests `q` and replying `r`. DISTINCT from `Pid(m)`:
  ## `call`/`cast`/`stop` are gen_server protocol operations, and a plain spawned process
  ## cannot answer them — it would block the caller for 5s and then exit it.
  typealias GenServer(q, r) = RawPid(q, r, Server)
```

`call` and `cast` already declare `server: GenServer(q, r)` — the alias split alone makes
them `Server`-only, no signature edit needed. `stop` does **not**: today it is
`fn stop({m: Type}, pid: Pid(m)) -> Effect(Unit) = raw_stop(pid)` — it takes a `Pid(m)`
only because `Pid(m)` and `GenServer(q,r)` are currently the same constructor. After the
alias split `Pid(m)` is `RawPid(m, m, Plain)`, which no longer unifies with `raw_stop`'s
new `RawPid(q, r, Server)` requirement, so `stop` needs an explicit rewrite:

```cure
  fn stop({q: Type}, {r: Type}, server: GenServer(q, r)) -> Effect(Unit) = raw_stop(server)
```

Make `tell`, `send_after`, `link`, `unlink`, `monitor`, `exit`, `is_alive`, `register` tag-polymorphic so they accept both handles:

```cure
  ## Send a well-typed message. Accepts BOTH handles: a raw send to a gen_server is
  ## legitimate BEAM practice — it lands in `handle_info`.
  fn tell({m: Type}, {r: Type}, {k: Type}, dest: RawPid(m, r, k), msg: m) -> Effect(Unit) =
    raw_send(dest, msg)

  fn link({m: Type}, {r: Type}, {k: Type}, pid: RawPid(m, r, k)) -> Effect(Unit) = raw_link(pid)

  fn unlink({m: Type}, {r: Type}, {k: Type}, pid: RawPid(m, r, k)) -> Effect(Unit) = raw_unlink(pid)

  fn is_alive({m: Type}, {r: Type}, {k: Type}, pid: RawPid(m, r, k)) -> Effect(Bool) =
    raw_is_alive(pid)

  fn register({m: Type}, {r: Type}, {k: Type}, name: Atom, pid: RawPid(m, r, k)) -> Effect(Unit) =
    raw_register(name, pid)

  fn monitor({m: Type}, {r: Type}, {k: Type}, kind: Atom, pid: RawPid(m, r, k)) -> Effect(Ref) =
    raw_monitor(kind, pid)

  fn send_after({m: Type}, {r: Type}, {k: Type}, delay: Int, pid: RawPid(m, r, k), msg: m) -> Effect(Ref) =
    raw_send_after(delay, pid, msg)

  fn exit({m: Type}, {r: Type}, {k: Type}, {x: Type}, pid: RawPid(m, r, k), reason: x) -> Effect(Unit) =
    raw_exit(pid, reason)
```

`spawn`, `spawn_link` and `self` keep returning `Pid(m)` (now `Plain`) — no signature change.

- [ ] **Step 5: Update the one pre-existing test this breaks (sanctioned)**

In `test/cure/stdlib/otp_test.exs`, the test `"beam_ops expands every initial operation to ordinary algebra calls"` declares:

```cure
fn stop_it(p: Pid(Cmd)) -> Effect(Unit) = beam_ops stop p
```

`stop` is now `Server`-only, so this no longer typechecks — it was asserting the defect. Change that one line to:

```cure
fn stop_it(s: GenServer(Cmd, Int)) -> Effect(Unit) = beam_ops stop s
```

This is one of the **two** sanctioned pre-existing-test edits in this plan. Change nothing else in that test — its assertions stay as they are.

- [ ] **Step 6: Run the OTP tests and confirm they pass**

Run: `mix test test/cure/stdlib/otp_test.exs`
Expected: 0 failures, including the six new tests.

- [ ] **Step 7: Commit**

```bash
git add lib/std/otp_raw.cure lib/std/otp.cure test/cure/stdlib/otp_test.exs
git commit -m "fix(std): separate Pid from GenServer with an erased phantom tag

Pid(m) and GenServer(q,r) were typealiases of the same constructor, so call/cast/stop
on a plain spawned process typechecked and then blocked the caller for 5s before
exiting it. The tag is a phantom at kind Type: zero runtime cost."
```

---

## Task 5: `whereis` can fail, and cannot lie about the message type (F-2c)

**Why:** `raw_whereis : Atom -> Effect(RawPid(m, m))` **asserts the lookup succeeds**. The BEAM returns the bare atom `undefined` for an unregistered name, so a well-typed `Pid(m)` could *be* that atom and the next `tell` would emit `erlang:send(undefined, …)` → `badarg`.

Per spec §7.2, the fix cannot preserve the `m` claim: a union member must be ground, so the pid member cannot mention `m`, and no cast exists to re-attach it (`believe_me` was deleted). This is not a limitation to route around — today's signature tells *two* lies (the lookup succeeds; the result carries `m`), and founding the message type is exactly what F-1 defers. Both lies go.

`BarePid` is not crippled: `link`, `unlink`, `monitor`, `exit` and `is_alive` accept it unchanged, since they are message-type-polymorphic. Only `tell` becomes uncallable — it would need a `NoMessage` argument, and `NoMessage` has no constructors. That is the honest content of a registry lookup.

**Files:**
- Modify: `lib/std/otp_raw.cure`
- Modify: `lib/std/otp.cure`
- Modify: `test/cure/stdlib/otp_test.exs` (extend)

**Interfaces:**
- Consumes: Task 2 (`:pid` class), Task 3 (`Effect(<union>)`), Task 4 (`RawPid(m, r, k)`).
- Produces: `Std.Otp.Raw`: `type NoMessage = |`, `typealias BarePid = RawPid(NoMessage, NoMessage, Plain)`, `raw_whereis(name: Atom) -> Effect(BarePid | :undefined)`.
- Produces: `Std.Otp`: `whereis(name: Atom) -> Effect(Option(BarePid))`.

- [ ] **Step 1: Write the failing test**

Append to `test/cure/stdlib/otp_test.exs`:

```elixir
  describe "whereis reintroduces the failure case (F-2c)" do
    test "using the result of whereis WITHOUT matching is a compile error" do
      assert {:error, _} =
               app("  fn go() -> Effect(Unit) =\n    let p = whereis(:server)\n    link(p)\n")
    end

    test "matching the Option and linking the Some branch succeeds" do
      assert {:ok, _} =
               app("""
                 fn go() -> Effect(Unit) =
                   let found = whereis(:server)
                   match found
                     Some(p) -> link(p)
                     None() -> unit()
               """)
    end

    test "a looked-up pid cannot be SENT to — nothing founds its message type" do
      assert {:error, _} =
               app("""
                 fn go() -> Effect(Unit) =
                   let found = whereis(:server)
                   match found
                     Some(p) -> tell(p, Inc())
                     None() -> unit()
               """)
    end
  end
```

- [ ] **Step 2: Run and confirm it fails**

Run: `mix test test/cure/stdlib/otp_test.exs`
Expected: "using the result WITHOUT matching is a compile error" FAILS by *succeeding* — that is F-2c verbatim. The other two fail because `whereis` returns no `Option` yet (and today `tell` on its result is wrongly accepted, which is the F-1 half).

- [ ] **Step 3: Make the raw op honest**

In `lib/std/otp_raw.cure`, beside the tags from Task 4:

```cure
  ## An uninhabited message type. `BarePid` carries it, which is what makes a pid
  ## recovered from the registry UNSENDABLE: `tell` would demand a `NoMessage` value and
  ## no constructor produces one.
  type NoMessage = |

  ## A process handle with NO message-type claim — what a registry lookup can honestly
  ## give you. Supervisable (`link`/`monitor`/`exit`/`is_alive` never cared about the
  ## message type) but not sendable. Recovering a TYPED handle from a name needs a
  ## name-to-code association nothing builds yet; that is F-1 (see the audit, §6).
  typealias BarePid = RawPid(NoMessage, NoMessage, Plain)
```

and replace `raw_whereis`:

```cure
  ## The registry operations deliberately remain raw and effect-typed. `whereis` returns
  ## the bare atom `undefined` when the name is not registered — that is the BIF's real
  ## contract, and typing it as a pid would let a well-typed handle BE the atom
  ## `undefined`. The typed facade reintroduces the failure case as an `Option`.
  @extern(:erlang, :whereis, 1)
  fn raw_whereis(name: Atom) -> Effect(BarePid | :undefined)
```

The FFI boundary re-tags the result: the literal `:undefined` is matched by exact value and ordered first; the `BarePid` member is matched by the `is_pid` guard from `@erases(:pid)`. There is deliberately no catch-all — a shape outside the declared union raises a `CaseClauseError` naming the offending value.

- [ ] **Step 4: Reintroduce the failure case in the typed facade**

In `lib/std/otp.cure`, ensure the module has `use Std.Option`, then replace `whereis`:

```cure
  ## Look up a registered name. `None` when the name is not registered — the BIF returns
  ## the atom `undefined` there, and the old signature asserted a pid.
  ##
  ## The result is a `BarePid`: you may `link`, `monitor`, `exit` or `is_alive` it, but you
  ## cannot `tell` to it. Nothing associates a registered NAME with a message TYPE, so a
  ## typed handle cannot be recovered from one (audit F-1 / parent spec §13.7).
  fn whereis(name: Atom) -> Effect(Option(BarePid)) =
    let found = raw_whereis(name)
    match found
      p: BarePid -> Some(p)
      :undefined -> None()
```

Note the match has **one arm per union member and no catch-all** — that is required, not stylistic.

- [ ] **Step 5: Run and confirm it passes**

Run: `mix test test/cure/stdlib/otp_test.exs`
Expected: 0 failures.

- [ ] **Step 6: Commit**

```bash
git add lib/std/otp_raw.cure lib/std/otp.cure test/cure/stdlib/otp_test.exs
git commit -m "fix(std): whereis returns Option(BarePid) — the lookup can fail

raw_whereis asserted the lookup succeeds AND that the result carries messages of type
m. The BEAM returns the bare atom undefined for an unknown name, so a well-typed Pid(m)
could BE that atom. Nothing associates a registered name with a message type, so the
honest result is an unsendable handle: supervisable, not tellable."
```

---

## Task 6: Honest raw result types (F-4)

**Why:** Ten raw ops declare `Effect(Unit)` for BIFs that return real terms. `emit.ex` performs no result coercion, so the value inhabiting `Unit` (runtime atom `unit`) is in fact the message, `true`, `ok`, or — worst — an integer. This violates the parent spec §3.1's "most permissive **honest** BEAM type".

**Files:**
- Modify: `lib/std/otp_raw.cure`
- Modify: `lib/std/otp.cure`
- Modify: `test/cure/stdlib/otp_test.exs` (extend)

**Interfaces:**
- Consumes: Task 3 (`Effect(<union>)`, for `cancel_timer`).
- Produces (raw): `raw_send → Effect(m)`; `raw_link`/`raw_unlink`/`raw_exit`/`raw_register`/`raw_unregister`/`raw_demonitor` → `Effect(Bool)`; `raw_cast`/`raw_stop` → `Effect(Atom)`; `raw_cancel_timer → Effect(Int | Bool)`.
- Produces (typed): every wrapper keeps its current result type by discarding, **except** `cancel_timer(ref) -> Effect(Option(Int))`.
- `raw_start_link` and friends keep `Effect(Tuple)` — the `ignore` case is deferred (spec §2); it gains a docstring in Task 9.

- [ ] **Step 1: Write the failing test**

Append to `test/cure/stdlib/otp_test.exs`:

```elixir
  describe "honest raw result types (F-4)" do
    test "cancel_timer surfaces the remaining milliseconds as an Option" do
      assert {:ok, _} =
               app("  fn go(t: Ref) -> Effect(Option(Int)) =\n    cancel_timer(t)\n")
    end

    test "the typed wrappers still return Unit — the raw result is discarded" do
      assert {:ok, _} = app("  fn go(p: Pid(Cmd)) -> Effect(Unit) =\n    tell(p, Inc())\n")
      assert {:ok, _} = app("  fn go(p: Pid(Cmd)) -> Effect(Unit) =\n    link(p)\n")
      assert {:ok, _} = app("  fn go(s: GenServer(Cmd, Int)) -> Effect(Unit) =\n    cast(s, Inc())\n")
    end
  end
```

`Ref` becomes `TimerRef` in Task 7 Step 4 — that is a *pre-planned narrowing of a test written to anticipate it*, not a weakening.

- [ ] **Step 2: Run and confirm it fails**

Run: `mix test test/cure/stdlib/otp_test.exs`
Expected: the `cancel_timer` test FAILS — it returns `Effect(Unit)` today, not `Effect(Option(Int))`. The discard test already passes; it is the guard that the typed surface does not shift under the raw retyping.

- [ ] **Step 3: Retype the raw ops honestly**

In `lib/std/otp_raw.cure`, apply the audited table. Each op keeps its parameters (as Task 4 left them); only the result changes:

```cure
  ## `erlang:send/2` returns the MESSAGE, not `ok`.
  @extern(:erlang, :send, 2)
  fn raw_send({m: Type}, {r: Type}, {k: Type}, dest: RawPid(m, r, k), msg: m) -> Effect(m)

  ## `gen_server:cast/2` and `gen_server:stop/1` return the atom `ok`.
  @extern(:gen_server, :cast, 2)
  fn raw_cast({q: Type}, {r: Type}, server: RawPid(q, r, Server), msg: q) -> Effect(Atom)

  @extern(:gen_server, :stop, 1)
  fn raw_stop({q: Type}, {r: Type}, pid: RawPid(q, r, Server)) -> Effect(Atom)

  ## These all return `true`.
  @extern(:erlang, :link, 1)
  fn raw_link({m: Type}, {r: Type}, {k: Type}, pid: RawPid(m, r, k)) -> Effect(Bool)

  @extern(:erlang, :unlink, 1)
  fn raw_unlink({m: Type}, {r: Type}, {k: Type}, pid: RawPid(m, r, k)) -> Effect(Bool)

  @extern(:erlang, :exit, 2)
  fn raw_exit({m: Type}, {r: Type}, {k: Type}, {x: Type}, pid: RawPid(m, r, k), reason: x) -> Effect(Bool)

  @extern(:erlang, :register, 2)
  fn raw_register({m: Type}, {r: Type}, {k: Type}, name: Atom, pid: RawPid(m, r, k)) -> Effect(Bool)

  @extern(:erlang, :unregister, 1)
  fn raw_unregister(name: Atom) -> Effect(Bool)

  @extern(:erlang, :demonitor, 1)
  fn raw_demonitor(ref: Ref) -> Effect(Bool)

  ## `erlang:cancel_timer/1` returns the REMAINING MILLISECONDS, or `false` once the timer
  ## has already fired or been cancelled. It is not `Unit` and never was — the sharpest of
  ## the Effect(Unit) lies.
  @extern(:erlang, :cancel_timer, 1)
  fn raw_cancel_timer(ref: Ref) -> Effect(Int | Bool)
```

`raw_is_alive` already returns `Effect(Bool)`; leave it. Do not change `raw_call` or the `start_link` family.

- [ ] **Step 4: Discard the raw result in the typed wrappers**

In `lib/std/otp.cure`, every wrapper whose raw op now returns a real term binds and drops it. The effect elaborator sequences the `let` and injects `{:effect_pure, …}` for the pure tail, which `emit.ex` lowers away — no runtime cost:

```cure
  fn tell({m: Type}, {r: Type}, {k: Type}, dest: RawPid(m, r, k), msg: m) -> Effect(Unit) =
    let _sent = raw_send(dest, msg)
    unit()

  fn cast({q: Type}, {r: Type}, server: GenServer(q, r), request: q) -> Effect(Unit) =
    let _ok = raw_cast(server, request)
    unit()

  fn stop({q: Type}, {r: Type}, server: GenServer(q, r)) -> Effect(Unit) =
    let _ok = raw_stop(server)
    unit()

  fn link({m: Type}, {r: Type}, {k: Type}, pid: RawPid(m, r, k)) -> Effect(Unit) =
    let _linked = raw_link(pid)
    unit()

  fn unlink({m: Type}, {r: Type}, {k: Type}, pid: RawPid(m, r, k)) -> Effect(Unit) =
    let _unlinked = raw_unlink(pid)
    unit()

  fn register({m: Type}, {r: Type}, {k: Type}, name: Atom, pid: RawPid(m, r, k)) -> Effect(Unit) =
    let _registered = raw_register(name, pid)
    unit()

  fn unregister(name: Atom) -> Effect(Unit) =
    let _unregistered = raw_unregister(name)
    unit()
```

`exit` is rewritten in Task 8 (its reason type changes); give it the same discard shape there.

`cancel_timer` surfaces its result rather than discarding it, because the result is real:

```cure
  ## Cancel a timer. `Some(ms)` — the milliseconds that were left. `None` — the timer had
  ## already fired or been cancelled.
  ##
  ## ⚠ AtomVM: `erlang:send_after/3` registers its timer under a DIFFERENT ref than the one
  ## it returns (timer_manager.erl:87-91), so on AtomVM cancelling a `send_after` ref always
  ## yields `None` AND THE MESSAGE STILL FIRES. Cancellation is reliable on OTP; on AtomVM it
  ## is not. See the audit, §5.
  fn cancel_timer(ref: Ref) -> Effect(Option(Int)) =
    let remaining = raw_cancel_timer(ref)
    match remaining
      ms: Int -> Some(ms)
      b: Bool -> None()
```

One arm per member, no catch-all. Do **not** reach for `assert_type` if this resists — an unchecked cast is the exact class of defect this batch removes. If it does resist, the union machinery is at fault and belongs in Task 2 or 3.

- [ ] **Step 5: Run and confirm it passes**

Run: `mix test test/cure/stdlib/otp_test.exs`
Expected: 0 failures.

- [ ] **Step 6: Commit**

```bash
git add lib/std/otp_raw.cure lib/std/otp.cure test/cure/stdlib/otp_test.exs
git commit -m "fix(std): honest result types for the raw OTP externs

Ten ops declared Effect(Unit) for BIFs returning real terms — send returns the message,
link/exit/register return true, cast/stop return ok, and cancel_timer returns an
integer. emit.ex does no result coercion, so those values were inhabiting Unit. The
typed wrappers discard; cancel_timer surfaces Option(Int)."
```

---

## Task 7: Distinct `MonitorRef` / `TimerRef`, and `demonitor` flushes (F-5)

**Why:** `typealias MonitorRef = Ref` and `typealias TimerRef = Ref` are the same type, so `cancel_timer(monitor_ref)` typechecks. And `demonitor/1` omits `flush`, so a stale `DOWN` can outlive the call.

**Files:**
- Modify: `lib/std/otp_raw.cure`
- Modify: `lib/std/otp.cure`
- Modify: `test/cure/stdlib/otp_test.exs` (extend + one sanctioned edit)

**Interfaces:**
- Consumes: Task 1 (`@erases`).
- Produces (raw): `@erases(:reference) opaque type MonitorRef` and `@erases(:reference) opaque type TimerRef`, alongside the existing `opaque type Ref`.
- Produces (raw): `raw_demonitor_flush(ref: MonitorRef, opts: List(Atom)) -> Effect(Bool)` → `@extern(:erlang, :demonitor, 2)`.
- Produces (typed): `monitor → Effect(MonitorRef)`; `send_after → Effect(TimerRef)`; `demonitor(ref: MonitorRef)`; `cancel_timer(ref: TimerRef) -> Effect(Option(Int))`.

Scope note: the raw `opaque type Ref` is **not** deleted. What is replaced is `otp.cure`'s two *typealiases* of it. `raw_demonitor` (arity-1) stays in the raw base typed over `Ref`, honest and driving no typed wrapper — `raw_term` is the existing precedent for that.

- [ ] **Step 1: Write the failing test**

Append to `test/cure/stdlib/otp_test.exs`:

```elixir
  describe "monitor and timer references are distinct types (F-5)" do
    test "cancelling a monitor ref is a compile error" do
      assert {:error, _} =
               app("  fn go(r: MonitorRef) -> Effect(Option(Int)) =\n    cancel_timer(r)\n")
    end

    test "demonitoring a timer ref is a compile error" do
      assert {:error, _} = app("  fn go(r: TimerRef) -> Effect(Unit) =\n    demonitor(r)\n")
    end

    test "each ref is accepted by its own operation" do
      assert {:ok, _} =
               app("  fn go(r: TimerRef) -> Effect(Option(Int)) =\n    cancel_timer(r)\n")

      assert {:ok, _} = app("  fn go(r: MonitorRef) -> Effect(Unit) =\n    demonitor(r)\n")
    end
  end
```

- [ ] **Step 2: Run and confirm it fails**

Run: `mix test test/cure/stdlib/otp_test.exs`
Expected: both "is a compile error" tests FAIL by *succeeding* — `MonitorRef` and `TimerRef` are the same type today.

- [ ] **Step 3: Add the two carriers and the flushing demonitor**

In `lib/std/otp_raw.cure`, beside the existing `opaque type Ref`:

```cure
  ## A monitor reference — the `erlang:reference()` returned by `erlang:monitor/2`.
  ## DISTINCT from `TimerRef`: cancelling a monitor or demonitoring a timer is nonsense,
  ## and the BEAM will not tell you.
  @erases(:reference)
  opaque type MonitorRef

  ## A timer reference — the `erlang:reference()` returned by `erlang:send_after/3`.
  @erases(:reference)
  opaque type TimerRef
```

Retype the ops that produce and consume them:

```cure
  @extern(:erlang, :monitor, 2)
  fn raw_monitor({m: Type}, {r: Type}, {k: Type}, kind: Atom, pid: RawPid(m, r, k)) -> Effect(MonitorRef)

  @extern(:erlang, :send_after, 3)
  fn raw_send_after({m: Type}, {r: Type}, {k: Type}, delay: Int, pid: RawPid(m, r, k), msg: m) -> Effect(TimerRef)

  @extern(:erlang, :cancel_timer, 1)
  fn raw_cancel_timer(ref: TimerRef) -> Effect(Int | Bool)

  ## `erlang:demonitor/2` with `[flush]` — removes the monitor AND discards a `DOWN` that
  ## has already been delivered. The option list is a real parameter, not baked in. With
  ## `flush` and no `info`, the BIF always returns `true`.
  @extern(:erlang, :demonitor, 2)
  fn raw_demonitor_flush(ref: MonitorRef, opts: List(Atom)) -> Effect(Bool)
```

`raw_demonitor : Ref -> Effect(Bool)` (arity-1) stays exactly as Task 6 left it.

- [ ] **Step 4: Point the typed layer at the new carriers**

In `lib/std/otp.cure`, **delete** these two lines:

```cure
  typealias MonitorRef = Ref
  typealias TimerRef = Ref
```

(`Std.Otp` imports `Std.Otp.Raw`, so both names remain in scope as the raw base's opaque types.)

Retype the typed ops:

```cure
  fn monitor({m: Type}, {r: Type}, {k: Type}, kind: Atom, pid: RawPid(m, r, k)) -> Effect(MonitorRef) =
    raw_monitor(kind, pid)

  fn send_after({m: Type}, {r: Type}, {k: Type}, delay: Int, pid: RawPid(m, r, k), msg: m) -> Effect(TimerRef) =
    raw_send_after(delay, pid, msg)

  ## Remove a monitor AND flush any `DOWN` already sitting in the mailbox — without `flush`
  ## a stale `DOWN` outlives the call and the receiving code has to handle it.
  fn demonitor(ref: MonitorRef) -> Effect(Unit) =
    let _removed = raw_demonitor_flush(ref, [:flush])
    unit()
```

and change `cancel_timer`'s parameter from `Ref` to `TimerRef` (its body is unchanged from Task 6). If the bare list literal `[:flush]` does not check against `List(Atom)`, ascribe it — `assert_type [:flush] : List(Atom)` — which is a *checked* ascription, not a cast, and is legitimate.

Then narrow Task 6's `cancel_timer` test from `Ref` to `TimerRef`, as flagged there. That test is green by now and this narrowing is the one it was written to anticipate; if it is somehow red, stop and diagnose rather than editing it.

- [ ] **Step 5: Update the one pre-existing test this breaks (sanctioned)**

In `test/cure/stdlib/otp_test.exs`, the test `"beam_ops expands lifecycle, timer, monitor, and link operations"` types its refs as the bare `Ref` and asserts `cancel(r: Ref) -> Effect(Unit)`. Both the types and `cancel`'s return change:

```cure
fn timer(p: Pid(Atom)) -> Effect(TimerRef) = beam_ops send_after 10 p :tick
fn cancel(r: TimerRef) -> Effect(Option(Int)) = beam_ops cancel_timer r
fn observe(p: Pid(Atom)) -> Effect(MonitorRef) = beam_ops monitor :process p
fn unobserve(r: MonitorRef) -> Effect(Unit) = beam_ops demonitor r
fn connect(p: Pid(Atom)) -> Effect(Unit) = beam_ops link p
fn disconnect(p: Pid(Atom)) -> Effect(Unit) = beam_ops unlink p
```

This is the **second and last** sanctioned pre-existing-test edit. The test's assertions are unchanged — only the Cure source it elaborates.

- [ ] **Step 6: Run and confirm it passes**

Run: `mix test test/cure/stdlib/otp_test.exs`
Expected: 0 failures.

- [ ] **Step 7: Commit**

```bash
git add lib/std/otp_raw.cure lib/std/otp.cure test/cure/stdlib/otp_test.exs
git commit -m "fix(std): distinct MonitorRef and TimerRef; demonitor flushes

They were two aliases of one Ref, so cancel_timer(monitor_ref) typechecked. demonitor
now passes [flush], so a stale DOWN cannot outlive the call."
```

---

## Task 8: A precise `ExitReason` (F-3)

**Why:** The three exit rules of the reference semantics case on `reason ∈ {normal, kill, other}` crossed with the target's `trap_exit` flag and the signal's link flag. A fully polymorphic `reason` cannot express which of the three outcomes a given `exit` can have.

**Files:**
- Modify: `lib/std/otp.cure`
- Modify: `test/cure/stdlib/otp_test.exs` (extend)

**Interfaces:**
- Consumes: Task 4 (tag-polymorphic `exit`), Task 6 (`raw_exit -> Effect(Bool)`).
- Produces: `Std.Otp`: `type ExitReason = Normal | Kill | Because(Atom)`; `exit({m}, {r}, {k}, pid: RawPid(m, r, k), reason: ExitReason) -> Effect(Unit)`.

The **raw** op stays permissive (`{x: Type}`) — the raw base carries the most permissive *honest* type (parent spec §3.1). Only the typed layer narrows.

- [ ] **Step 1: Write the failing test**

Append to `test/cure/stdlib/otp_test.exs`:

```elixir
  describe "the exit reason is a precise sum (F-3)" do
    test "the three reasons the semantics distinguishes are accepted" do
      assert {:ok, _} = app("  fn go(p: Pid(Cmd)) -> Effect(Unit) =\n    exit(p, Normal())\n")
      assert {:ok, _} = app("  fn go(p: Pid(Cmd)) -> Effect(Unit) =\n    exit(p, Kill())\n")

      assert {:ok, _} =
               app("  fn go(p: Pid(Cmd)) -> Effect(Unit) =\n    exit(p, Because(:shutdown))\n")
    end

    test "an arbitrary term is no longer a valid exit reason" do
      assert {:error, _} = app("  fn go(p: Pid(Cmd)) -> Effect(Unit) =\n    exit(p, 5)\n")
    end
  end
```

- [ ] **Step 2: Run and confirm it fails**

Run: `mix test test/cure/stdlib/otp_test.exs`
Expected: "an arbitrary term is no longer a valid exit reason" FAILS by *succeeding* (`reason` is `{x: Type}` today, so `5` is accepted), and the three-reasons test fails because `ExitReason` does not exist.

- [ ] **Step 3: Declare the sum and narrow the typed op**

In `lib/std/otp.cure`:

```cure
  ## Why a process is being asked to exit. The BEAM's three exit rules turn on exactly this
  ## distinction, crossed with the target's trap_exit flag and the signal's link flag:
  ##
  ##   * `Normal`          — dropped by a non-trapping target (unless it is the caller
  ##                         itself, which does terminate).
  ##   * `Kill`            — untrappable when sent explicitly with `exit/2`: the target dies
  ##                         and propagates the reason `killed`. (Sent THROUGH A LINK it is
  ##                         trappable — but this op only ever sends explicitly.)
  ##   * `Because(reason)` — terminates a non-trapping target; a trapping target receives
  ##                         `{'EXIT', From, reason}` at the END of its mailbox.
  ##
  ## `exit` makes NO type-level claim that the target dies — correctly: which of the three
  ## outcomes occurs depends on the target's trap_exit flag, which the sender cannot see.
  type ExitReason = Normal | Kill | Because(Atom)

  local fn exit_atom(reason: ExitReason) -> Atom =
    match reason
      Normal() -> :normal
      Kill() -> :kill
      Because(why) -> why

  fn exit({m: Type}, {r: Type}, {k: Type}, pid: RawPid(m, r, k), reason: ExitReason) -> Effect(Unit) =
    let _sent = raw_exit(pid, exit_atom(reason))
    unit()
```

- [ ] **Step 4: Run and confirm it passes**

Run: `mix test test/cure/stdlib/otp_test.exs`
Expected: 0 failures.

- [ ] **Step 5: Commit**

```bash
git add lib/std/otp.cure test/cure/stdlib/otp_test.exs
git commit -m "fix(std): exit takes a precise ExitReason, not any term

The BEAM's three exit rules turn on normal/kill/other crossed with trap_exit and the
link flag. A polymorphic reason erased exactly that distinction."
```

---

## Task 9: Honest docstrings, and the raw-return regression pin

**Why:** Two things remain. (a) `Std.Otp.Raw`'s header says the effect discipline "forbids duplicating, dropping, or reordering a `send`/`call`" — that is about the *program's effect sequence*, not mailbox arrival, and reads as a delivery guarantee the BEAM does not give. (b) F-4's root cause is that the parent spec's §12 `no_widening_narrow` validator was never built. It cannot be automated in general — that needs an oracle for every BIF's return type — but the audited table *can* be pinned, so a future widening becomes a failing test instead of a silent lie.

**Files:**
- Modify: `lib/std/otp_raw.cure` (module docstring; `raw_call` and `raw_start_link` docstrings)
- Modify: `lib/std/otp.cure` (module docstring; `call` docstring)
- Test: `test/cure/stdlib/otp_raw_pin_test.exs` (create)

**Interfaces:**
- Consumes: every raw op's final type, from Tasks 4–8.

- [ ] **Step 1: Write the failing test**

Create `test/cure/stdlib/otp_raw_pin_test.exs`. It pins the SOURCE text deliberately: the
claim being pinned is what each `@extern` *declares*, and reading it from the source is
both exact and immune to elaborator API drift.

```elixir
defmodule Cure.Stdlib.OtpRawPinTest do
  @moduledoc """
  The concrete `no_widening_narrow` validator (parent spec §12).

  Every op in `Std.Otp.Raw` is an `@extern` over a stock BEAM BIF, and the parent spec
  (§3.1) requires each to carry its most permissive HONEST type. That cannot be checked
  automatically — it would need an oracle for every BIF's return type — so this pins the
  table the executed conformance audit established by probing each BIF's real return value
  (https://github.com/cure-lang/cure-otp/tree/main/docs/research/process-types/raw-algebra-conformance-checklist.md, §4 F-4).

  A change here is not a test to update. It is a claim about what the BEAM returns, and it
  needs the evidence the audit produced: run the BIF and look.
  """
  use ExUnit.Case, async: true

  @source "lib/std/otp_raw.cure"

  # raw op => the exact return type its declaration must carry.
  @pinned %{
    "raw_self" => "Effect(RawPid(m, m, Plain))",
    "raw_spawn" => "Effect(RawPid(m, m, Plain))",
    "raw_spawn_link" => "Effect(RawPid(m, m, Plain))",
    "raw_send" => "Effect(m)",
    "raw_cast" => "Effect(Atom)",
    "raw_stop" => "Effect(Atom)",
    "raw_call" => "Effect(r)",
    "raw_link" => "Effect(Bool)",
    "raw_unlink" => "Effect(Bool)",
    "raw_exit" => "Effect(Bool)",
    "raw_register" => "Effect(Bool)",
    "raw_unregister" => "Effect(Bool)",
    "raw_demonitor" => "Effect(Bool)",
    "raw_demonitor_flush" => "Effect(Bool)",
    "raw_is_alive" => "Effect(Bool)",
    "raw_monitor" => "Effect(MonitorRef)",
    "raw_send_after" => "Effect(TimerRef)",
    "raw_cancel_timer" => "Effect(Int | Bool)",
    "raw_whereis" => "Effect(BarePid | :undefined)",
    "raw_start_link" => "Effect(Tuple)",
    "raw_start_link_unnamed" => "Effect(Tuple)",
    "raw_statem_start_link" => "Effect(Tuple)",
    "raw_statem_start_link_unnamed" => "Effect(Tuple)",
    "raw_supervisor_start_link" => "Effect(Tuple)",
    "raw_term" => "RawTerm"
  }

  defp declarations do
    @source
    |> File.read!()
    |> String.split("\n")
    |> Enum.filter(&(&1 =~ ~r/^\s*fn raw_\w+\(/))
    |> Map.new(fn line ->
      [_, name] = Regex.run(~r/fn (raw_\w+)\(/, line)
      {name, line}
    end)
  end

  test "every raw op is pinned, and every pinned op still exists" do
    declared = declarations() |> Map.keys() |> MapSet.new()
    pinned = @pinned |> Map.keys() |> MapSet.new()

    assert MapSet.difference(pinned, declared) |> Enum.empty?(),
           "pinned ops that no longer exist: #{inspect(MapSet.difference(pinned, declared))}"

    assert MapSet.difference(declared, pinned) |> Enum.empty?(),
           "raw ops with no pinned return type — add them to @pinned WITH evidence from " <>
             "the BIF's actual return value: #{inspect(MapSet.difference(declared, pinned))}"
  end

  test "each raw op declares exactly its audited return type" do
    decls = declarations()

    for {op, expected} <- @pinned do
      line = Map.fetch!(decls, op)

      assert String.contains?(line, "-> " <> expected),
             "#{op} no longer returns #{expected}.\n  declared: #{String.trim(line)}\n" <>
               "  This is a claim about what the BEAM returns. Re-probe the BIF before repinning."
    end
  end

  test "no raw op declares Effect(Unit) — none of these BIFs returns unit" do
    for {op, line} <- declarations() do
      refute String.contains?(line, "-> Effect(Unit)"),
             "#{op} declares Effect(Unit). Ten ops did, and emit.ex does no result " <>
               "coercion, so the BIF's real return value was inhabiting Unit. See the audit, F-4."
    end
  end
end
```

- [ ] **Step 2: Run and confirm it fails**

Run: `mix test test/cure/stdlib/otp_raw_pin_test.exs`
Expected: it runs. If a pinned signature does not match the source byte-for-byte, the failure names the op and prints the declared line — reconcile `@pinned` to the source **only where the source is what Tasks 4–8 intended**; if the source is wrong, fix the source. The `Effect(Unit)` test must pass outright (Task 6 removed the last one); if it fails, Task 6 is incomplete — go back rather than weakening this test.

- [ ] **Step 3: Make the docstrings honest**

In `lib/std/otp_raw.cure`, replace the delivery/ordering claim in the module header:

```cure
  ## Every operation that performs a BEAM side effect returns `Effect(T)`. The effect
  ## discipline forbids duplicating, dropping, or reordering an OPERATION — that is a
  ## statement about the PROGRAM'S EFFECT SEQUENCE, not about the mailbox. The BEAM itself
  ## guarantees far less, and nothing here may assume otherwise:
  ##
  ##   * NO DELIVERY. A `send` to a dead process silently succeeds. Nothing here promises a
  ##     message arrives, and no typed op sequences on arrival.
  ##   * ORDERING IS PAIRWISE ONLY. Signals from the SAME sender to the SAME target arrive
  ##     in order — messages and exit signals alike. Order between DIFFERENT senders is
  ##     unspecified.
  ##
  ## (Bereczky/Horpácsi/Thompson, *A Formalisation of Core Erlang*, Thm. 2 and Ex. 3;
  ## verified against AtomVM in https://github.com/cure-lang/cure-otp/tree/main/docs/research/process-types/raw-algebra-conformance-checklist.md.)
```

Add the two hazard docstrings the audit requires be visible at the op, not only in a research doc:

```cure
  ## Synchronous `gen_server` call.
  ##
  ## ⚠ PARTIAL. On timeout (default 5000 ms) or server death the CALLER EXITS. No value is
  ## returned at the wrong type — there is simply no continuation — so `Effect(r)` is sound
  ## but not total. A `try_call` that reifies the failure needs a try/catch shim and is
  ## deferred (audit §6).
  @extern(:gen_server, :call, 2)
  fn raw_call({q: Type}, {r: Type}, server: RawPid(q, r, Server), req: q) -> Effect(r)
```

and above the `start_link` family:

```cure
  ## ⚠ The return is typed `Effect(Tuple)`, which is honest on AtomVM (whose gen_server init
  ## result is `{ok, State} | {stop, Reason}`) but NOT on OTP, where an `init/1` returning
  ## `ignore` makes `start_link` return the BARE ATOM `ignore`. Typing that honestly means
  ## producing a TYPED handle from an untyped BEAM tuple — the same unfounded assertion as
  ## F-1, and deferred with it (audit §6).
```

In `lib/std/otp.cure`, carry the same `call` partiality warning onto the typed `call`, and correct the module header's effect-discipline sentence the same way.

- [ ] **Step 4: Run the full suite**

Run: `mix test`
Expected: 0 failures.

- [ ] **Step 5: Commit**

```bash
git add lib/std/otp_raw.cure lib/std/otp.cure test/cure/stdlib/otp_raw_pin_test.exs
git commit -m "docs(std): honest OTP docstrings; pin every raw op's return type

The raw base implied a delivery guarantee the BEAM does not give (it promises pairwise
sender-to-target ordering only, and no delivery at all). The pin test is the concrete
no_widening_narrow validator: a future widening now fails a test instead of becoming a
silent lie."
```

---

## Verification

Run once, at the end:

```bash
mix test
```

Expected: 0 failures.

Then confirm the audit's defects are actually closed — these are the tests added in Tasks 4–8, all in `mix test test/cure/stdlib/otp_test.exs`. Each was **red by succeeding** before its task:

- `call`/`cast`/`stop` on a plain `Pid` → compile error (was: accepted, then hung 5 s at runtime)
- the result of `whereis` used without matching → compile error (was: accepted)
- `tell` to a looked-up pid → compile error (was: accepted, on an unfounded message type)
- `cancel_timer(monitor_ref)` → compile error (was: accepted)
- `exit(p, 5)` → compile error (was: accepted)
- no raw op declares `Effect(Unit)` (was: ten did)

## Deferred, unchanged

F-1 (code derivation grounding the pid index), the honest `start_link` return, `try_call`
over a `cure_std_otp` shim, and retargeting `send_after` at `start_timer/3`. Recorded in
audit §6 and spec §6; nothing in this plan closes them, and Task 5's `BarePid` makes the
F-1 gap *visible in the types* rather than papering it with an unfounded index.
