# Trust Ledger (Axiom Surface, Phase 0) Implementation Plan

> **STATUS (2026-07-11): all 7 tasks LANDED** on `autopilot/axiom-surface` (unmerged) — commits `d18b842`, `27c8250`, `c03e8a5`, `4c2f441`, `bcf19a2`, `8963a37`, `215bfd2`, plus review fixes `75f209c`/`ad6f5fb`. The unchecked boxes below are the original as-written plan, kept for historical reference; two as-built corrections are inline (unresolved-globals, below). The Phase-1 conformance harness landed separately (`160af53`).

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Ship `cure audit trust <Module>`, a deterministic report of every assumption a Cure module makes without proof.

**Architecture:** A collector reads the elaborated `Cure.Core.Env` (never source text, so macro-emitted axioms are seen), determines which defs the audited module actually owns by diffing against a prelude-only env, walks reachability with a **fail-closed** term walker that raises on unknown Core nodes, classifies each axiom by its target MFA into `OTP` / `CURE RUNTIME` / `CURE BRIDGE`, and renders a byte-stable text or JSON report. Nothing here can influence kernel checking.

**Tech Stack:** Elixir, ExUnit, `Cure.Elab.Program.elaborate/1`, `Cure.Core.Env`, `Antigen.Backend.StreamData` (test-only), `OptionParser`.

**Spec:** `docs/superpowers/specs/language/2026-07-10-axiom-surface-design.md` — Phase 0 (§4) only. Phases 1–3 are out of scope.

## Global Constraints

- **Nothing in this plan enters the TCB.** `Cure.Audit.*` and `Cure.Core.Printer` read a kernel-checked env and cannot influence checking. A bug here produces a wrong report, never an unsound program.
- **Never wired into `cure build`.** The audit is a separate verb; a compiler that refuses to build over an audit trains people to hate the audit.
- **Determinism is load-bearing.** Sorted output, no timestamps, no absolute paths, no map-iteration order. `cure audit trust Std.List | diff -` is the ratchet.
- **Every section prints even when empty**, so `(0)` → `(1)` is a diff rather than a new line appearing from nowhere.
- **Exit codes:** always `0` when a report was produced. `--strict` exits non-zero **iff** `UNAUDITED` is non-empty.
- **Avoid `Registry` and `persistent_term`** — absent on AtomVM.
- **Only one full build/test run at any moment.** Never launch concurrent suites.
- **Commits are never co-signed.** Write them as the user only.
- **Strict TDD, every task.** Step 1 writes the test, Step 2 confirms it fails, Step 3 writes only enough implementation to pass it, Step 4 confirms green. Do not write implementation code before its test exists and has been run red. A test, once it correctly encodes intended behavior, is never weakened or deleted to reach green — the implementation changes, not the test. Task 7 Step 3 is the plan's one sanctioned exception, and it states why the test (not the code) was wrong before touching it: fix the implementation code, not the test, unless you can make the same kind of explicit case.

## Verified Facts (measured on this branch; do not re-derive)

These were confirmed by running the real elaborator. Tasks depend on them.

| Fact | Value |
|---|---|
| `Cure.Core.Term.term?/1` clauses | `type, var, pi, lam, let, app, data, ctor, case, global, int_type, int_lit, nat_lit, bounded_lit, float_type, float_lit, binary_type, atom_type, atom_lit, hole, absurd` (`lib/cure/core/term.ex:61-97`) |
| `Program.global_refs/1` | **had no `:let` clause** (fixed `9166433`); still ends in a fail-open `defp global_refs(_leaf), do: []` — which is exactly why `Audit.Refs` raises instead |
| Prelude-only env (`"mod Probe.Empty\nend\n"`) | 42 defs |
| `Std.List` full env | 82 defs, 31 `builtin_op`, 3 externs |
| `Std.List` **own** defs (env minus prelude) | 40 |
| `Std.List` own externs | exactly `length: {:erlang, :length, 1}` |
| `Std.List` own uncertified, excluding builtin_ops + externs | exactly `[:drop, :last, :reverse, :take]` |
| `env.certified` | a `MapSet`, but **defaults to `nil`** in the struct — guard before `MapSet.member?/2` |
| `add_def/5` def record | `%{name:, type:, body:, quantities:}` — **no `:builtin_op` key** unless `register_builtin_op/3` ran. Use `Map.get(def, :builtin_op)`, never `%{builtin_op: op}` pattern-match on an unregistered def |
| Extern body sentinel | `{:extern, {m, f, a}}` — not a `Core.Term` |
| Builtin-op body sentinel | Every `builtin_op`-tagged def has **`body: nil`** (confirmed: exactly the 31 `Builtins.seed_ops`-registered defs, e.g. `int_add`, `struct_eq`, in `Std.List`'s env — none untagged). `def.type` is always a real `Core.Term` for these; only `body` is `nil`. Reproduced by running the plan's own code: without a walker clause for `nil`, `Cure.Audit.Refs.walk/2` raises `unknown Core term in Audit.Refs: nil` — and it fires on **both** Task 3's `x + x` divergence test and the Task 7 `Std.List` golden test, because Ledger's reachability walk (unlike codegen's) does not skip `builtin_op` defs and calls `Refs.globals/scan` directly on every reachable def's `body`. Task 2 must add a `nil` clause to `Refs.walk/2` before Task 3 can pass. |

**Roots strategy (resolves a gap in the spec).** The spec says the ledger reports axioms "reachable from a module" but never defines the roots. `env.defs` for a single module also contains the 42 prelude defs, including two externs (`unicode:characters_to_list/1`, `unicode:characters_to_binary/1`) that `Std.List` does not declare. Roots diff the module env against a prelude-only env:

```
roots(module_env) = { name | (name, body) in module_env.defs, (name, body) not in prelude_env.defs }
```

**As-built correction (`ad6f5fb`):** the original plan diffed on NAME alone (`Map.keys(module_env.defs) -- Map.keys(prelude_env.defs)`). That is fail-open — a module redefining a prelude name (e.g. `fn eq(...) = @extern(...)`), if unreferenced elsewhere, vanished from the report. The diff keys on `(name, body)`; a shadowing redefinition has a different body while a genuine prelude def is byte-identical across the two (deterministic) elaborations. Keeps the collector reading `Core.Env` and reproduces both spec-mandated outputs for `Std.List`.

## File Structure

| File | Responsibility |
|---|---|
| Create `lib/cure/core/printer.ex` | `Cure.Core.Printer` — render a `Core.Term` to text. Untrusted. |
| Create `lib/cure/audit/refs.ex` | `Cure.Audit.Refs` — one exhaustive, fail-closed walk. Returns globals, holes, absurd count. |
| Create `lib/cure/audit/ledger.ex` | `Cure.Audit.Ledger` — prelude diff, reachability, classification. Produces `%Report{}`. |
| Create `lib/cure/audit/targets.ex` | `Cure.Audit.Targets` — hand-maintained per-target capability table. |
| Create `lib/cure/audit/format.ex` | `Cure.Audit.Format` — `%Report{}` → deterministic text or JSON. |
| Create `lib/cure/audit/source.ex` | `Cure.Audit.Source` — locate `Std.X` → `lib/std/x.cure` by scanning `mod` headers. |
| Create `lib/cure/audit/cli.ex` | `Cure.Audit.CLI` — pure `run/2`: locate, audit, format, decide `--strict`. No `System.halt/1`; the escript clause in `lib/cure/cli.ex` does that. |
| Modify `lib/cure/cli.ex` | Add the `["audit", "trust", mod]` verb and its switches. |
| Create `test/cure/core/printer_test.exs` | |
| Create `test/cure/audit/refs_test.exs` | |
| Create `test/cure/audit/ledger_test.exs` | |
| Create `test/cure/audit/format_test.exs` | |
| Create `test/cure/audit/trust_cli_test.exs` | |

Fixtures are **inline source strings** passed to `Program.elaborate/1`, not files on disk. No fixture directory.

### Spec §4.8 test → task mapping

| Spec test | Task |
|---|---|
| 1. extern yields one `ffi_postulate`; widening the type changes the rendered line | Task 3 |
| 2. divergence test — `builtin_op` present here, absent from `reachable_def_names/2` | Task 3 |
| 3. `refs` raises on a bogus node; Antigen corpus passes | Task 2 |
| 4. `opaque type` yields `opaque_family`; empty inductive does not | Task 3 |
| 5. `Std.List` reports exactly `reverse, last, drop, take` as not-proven-total | Task 7 |
| 6. `Std.Time` lands in `UNAUDITED`; `--strict` exits non-zero, default exits 0 | Task 6 |
| 7. `--target atomvm` reports `:re`, omits section without the flag | Task 4, Task 6 |
| 8. two runs produce byte-identical output | Task 5 |

---

### Task 1: `Cure.Core.Printer`

Nothing in the tree renders a `Core.Term` to text; every dependent-pipeline type error currently `inspect`s a raw Elixir tuple. The report needs readable types, and this independently improves those errors.

**Files:**
- Create: `lib/cure/core/printer.ex`
- Test: `test/cure/core/printer_test.exs`

**Interfaces:**
- Consumes: nothing.
- Produces: `Cure.Core.Printer.print(term :: Core.Term.t()) :: String.t()` and `print(term, names :: [String.t()]) :: String.t()`. Raises `ArgumentError` on an unknown node.

**Rendering rules (fixed — later tasks assert on these):**
- `{:pi, {:type, _}, cod}` where `cod` uses var 0 → `∀ {a}. <cod>` (type parameters are implicit in Cure surface, so braces).
- `{:pi, dom, cod}` where `cod` does **not** use var 0 → `<dom> -> <cod>` (non-dependent arrow).
- `{:pi, dom, cod}` otherwise → `(a : <dom>) -> <cod>`.
- Application chains flatten to spines: `f a b`, not `((f a) b)`.
- Binder names are `a, b, c, …` then `a1, b1, …`; shadowing appends a digit.

So `erlang:length/1`'s elaborated type renders as `∀ {a}. List(a) -> Int`, matching spec §4.7.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/core/printer_test.exs
defmodule Cure.Core.PrinterTest do
  use ExUnit.Case, async: true
  alias Cure.Core.Printer

  test "renders base types and literals" do
    assert Printer.print({:type, 0}) == "Type"
    assert Printer.print({:type, 2}) == "Type2"
    assert Printer.print({:int_type}) == "Int"
    assert Printer.print({:int_lit, -3}) == "-3"
    assert Printer.print({:atom_lit, :ok}) == ":ok"
    assert Printer.print({:binary_type}) == "Binary"
    assert Printer.print({:absurd}) == "absurd"
    assert Printer.print({:hole, "goal"}) == "?goal"
  end

  test "renders a non-dependent arrow without naming the binder" do
    # Int -> Int   (cod does not mention var 0)
    assert Printer.print({:pi, {:int_type}, {:int_type}}) == "Int -> Int"
  end

  test "renders a type parameter as an implicit forall" do
    # (a : Type) -> List(a) -> Int   ==>  ∀ {a}. List(a) -> Int
    ty =
      {:pi, {:type, 0},
       {:pi, {:data, :List, [{:var, 0}], []}, {:int_type}}}

    assert Printer.print(ty) == "∀ {a}. List(a) -> Int"
  end

  test "renders a dependent arrow with a named binder" do
    # (a : Int) -> Vec(a)
    ty = {:pi, {:int_type}, {:data, :Vec, [{:var, 0}], []}}
    assert Printer.print(ty) == "(a : Int) -> Vec(a)"
  end

  test "a non-dependent arrow shifts names so an outer binder stays reachable" do
    # ∀ {a}. Int -> a   ==  {:pi, {:type,0}, {:pi, {:int_type}, {:var,1}}}
    #
    # The inner pi is non-dependent (its own cod, `{:var,1}`, does not mention
    # ITS var 0), so `non_dependent_arrow` fires and must NOT name the inner
    # binder — but `a` (the outer forall's binder) is still referenced one
    # level deeper as `{:var,1}`, and printing the inner cod without pushing a
    # placeholder onto `names` misaligns every outer index by one. Verified
    # against the real implementation: dropping the `["_" | names]` push here
    # renders this as "∀ {a}. Int -> ?1" instead of "∀ {a}. Int -> a" — wrong,
    # and every other test in this file passes either way, because none of
    # them nest a non-dependent arrow inside a binder whose variable survives
    # past it.
    ty = {:pi, {:type, 0}, {:pi, {:int_type}, {:var, 1}}}
    assert Printer.print(ty) == "∀ {a}. Int -> a"
  end

  test "flattens application spines" do
    t = {:app, {:app, {:global, :f}, {:int_lit, 1}}, {:int_lit, 2}}
    assert Printer.print(t) == "f 1 2"
  end

  test "renders let and lambda binders" do
    assert Printer.print({:lam, {:int_type}, {:var, 0}}) == "\\a. a"

    assert Printer.print({:let, {:int_type}, {:int_lit, 1}, {:var, 0}}) ==
             "let a : Int = 1 in a"
  end

  test "raises on an unknown node rather than printing garbage" do
    assert_raise ArgumentError, ~r/unknown Core term/, fn ->
      Printer.print({:bogus, 1})
    end
  end
end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/cure/core/printer_test.exs`
Expected: FAIL — `Cure.Core.Printer` is undefined (`UndefinedFunctionError`).

- [ ] **Step 3: Write the implementation**

```elixir
# lib/cure/core/printer.ex
defmodule Cure.Core.Printer do
  @moduledoc """
  Render a `Cure.Core.Term` to readable text.

  **Untrusted.** This module is outside the TCB: it reads terms and produces
  strings. It cannot influence checking, and a bug here yields an ugly or wrong
  message, never an unsound program.

  Nothing else in the tree does this — `Quote.reify/2` returns a term and error
  sites hand it to `inspect/1`. Every dependent-pipeline type error that mentions
  a type therefore prints a raw Elixir tuple today.
  """

  @letters ~w(a b c d e f g h i j k l m n o p q r s t u v w x y z)

  @spec print(Cure.Core.Term.t()) :: String.t()
  def print(term), do: print(term, [])

  @spec print(Cure.Core.Term.t(), [String.t()]) :: String.t()
  def print({:type, 0}, _names), do: "Type"
  def print({:type, level}, _names), do: "Type#{level}"
  def print({:var, k}, names), do: Enum.at(names, k) || "?#{k}"
  def print({:int_type}, _names), do: "Int"
  def print({:int_lit, n}, _names), do: Integer.to_string(n)
  def print({:nat_lit, n}, _names), do: Integer.to_string(n)
  def print({:bounded_lit, n}, _names), do: Integer.to_string(n)
  def print({:float_type}, _names), do: "Float"
  def print({:float_lit, f}, _names), do: Float.to_string(f)
  def print({:binary_type}, _names), do: "Binary"
  def print({:atom_type}, _names), do: "Atom"
  def print({:atom_lit, a}, _names), do: ":" <> Atom.to_string(a)
  def print({:global, name}, _names), do: Atom.to_string(name)
  def print({:hole, name}, _names), do: "?" <> name
  def print({:absurd}, _names), do: "absurd"

  def print({:pi, {:type, _} = dom, cod}, names) do
    if uses_var0?(cod) do
      name = fresh(names)
      "∀ {#{name}}. #{print(cod, [name | names])}"
    else
      non_dependent_arrow(dom, cod, names)
    end
  end

  def print({:pi, dom, cod}, names) do
    if uses_var0?(cod) do
      name = fresh(names)
      "(#{name} : #{print(dom, names)}) -> #{print(cod, [name | names])}"
    else
      non_dependent_arrow(dom, cod, names)
    end
  end

  def print({:lam, _dom, body}, names) do
    name = fresh(names)
    "\\#{name}. #{print(body, [name | names])}"
  end

  def print({:let, ty, val, body}, names) do
    name = fresh(names)
    "let #{name} : #{print(ty, names)} = #{print(val, names)} in #{print(body, [name | names])}"
  end

  def print({:app, _, _} = t, names) do
    {head, args} = unspine(t, [])
    Enum.map_join([head | args], " ", &atomic(&1, names))
  end

  def print({:data, name, params, indices}, names),
    do: applied(Atom.to_string(name), params ++ indices, names)

  def print({:ctor, name, args}, names),
    do: applied(Atom.to_string(name), args, names)

  def print({:case, scrut, _motive, branches}, names) do
    arms =
      Enum.map_join(branches, "; ", fn {ctor, arity, body} ->
        binders = Enum.map(0..max(arity - 1, 0), fn i -> "x#{i}" end)
        binders = if arity == 0, do: [], else: binders
        head = Enum.join([Atom.to_string(ctor) | binders], " ")
        "#{head} -> #{print(body, Enum.reverse(binders) ++ names)}"
      end)

    "case #{print(scrut, names)} of #{arms}"
  end

  def print(other, _names) do
    raise ArgumentError, "unknown Core term in printer: #{inspect(other)}"
  end

  # -- helpers ---------------------------------------------------------------

  defp non_dependent_arrow(dom, cod, names) do
    # `cod` was built under a binder that it does not use; shift is unnecessary
    # for printing because no `{:var, 0}` occurs, but indices above 0 are off by
    # one. Push a placeholder so `Enum.at/2` stays aligned.
    "#{atomic(dom, names)} -> #{print(cod, ["_" | names])}"
  end

  defp applied(head, [], _names), do: head
  defp applied(head, args, names), do: "#{head}(#{Enum.map_join(args, ", ", &print(&1, names))})"

  defp unspine({:app, f, a}, acc), do: unspine(f, [a | acc])
  defp unspine(head, acc), do: {head, acc}

  # Parenthesise anything whose rendering could bind looser than application.
  defp atomic({:app, _, _} = t, names), do: "(" <> print(t, names) <> ")"
  defp atomic({:pi, _, _} = t, names), do: "(" <> print(t, names) <> ")"
  defp atomic({:lam, _, _} = t, names), do: "(" <> print(t, names) <> ")"
  defp atomic({:let, _, _, _} = t, names), do: "(" <> print(t, names) <> ")"
  defp atomic({:case, _, _, _} = t, names), do: "(" <> print(t, names) <> ")"
  defp atomic(t, names), do: print(t, names)

  defp fresh(names) do
    taken = MapSet.new(names)

    Stream.concat([@letters, Stream.flat_map(1..1000, fn i -> Enum.map(@letters, &"#{&1}#{i}") end)])
    |> Enum.find(fn c -> not MapSet.member?(taken, c) end)
  end

  # Does the term mention de Bruijn index 0 at its own binding depth?
  defp uses_var0?(term), do: uses_var?(term, 0)

  defp uses_var?({:var, k}, depth), do: k == depth
  defp uses_var?({:pi, d, c}, depth), do: uses_var?(d, depth) or uses_var?(c, depth + 1)
  defp uses_var?({:lam, d, b}, depth), do: uses_var?(d, depth) or uses_var?(b, depth + 1)

  defp uses_var?({:let, t, v, b}, depth),
    do: uses_var?(t, depth) or uses_var?(v, depth) or uses_var?(b, depth + 1)

  defp uses_var?({:app, f, a}, depth), do: uses_var?(f, depth) or uses_var?(a, depth)

  defp uses_var?({:data, _n, ps, is}, depth),
    do: Enum.any?(ps ++ is, &uses_var?(&1, depth))

  defp uses_var?({:ctor, _n, args}, depth), do: Enum.any?(args, &uses_var?(&1, depth))

  defp uses_var?({:case, s, m, brs}, depth) do
    uses_var?(s, depth) or uses_var?(m, depth) or
      Enum.any?(brs, fn {_c, arity, body} -> uses_var?(body, depth + arity) end)
  end

  defp uses_var?(_leaf, _depth), do: false
end
```

- [ ] **Step 4: Run the test to verify it passes**

Run: `mix test test/cure/core/printer_test.exs`
Expected: PASS, 8 tests.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/core/printer.ex test/cure/core/printer_test.exs
git commit -m "feat(core): add an untrusted Core.Term pretty-printer"
```

---

### Task 2: `Cure.Audit.Refs` — the fail-closed walker

`Program.global_refs/1` ends in `defp global_refs(_leaf), do: []`. For codegen that is benign. For a ledger it is fatal: when the Core grammar grows a node, reachability silently under-reports and the ledger stops finding axioms. **This was not hypothetical — `global_refs/1` had no `:let` clause** (fixed `9166433` after `reachability_let_test.exs` reproduced it), so any global referenced only inside a `let` was invisible to it. The fail-open catch-all remains, which is why the ledger uses the fail-closed `Audit.Refs` instead.

`Audit.Refs` enumerates every clause of `Core.Term.term?/1` explicitly and **raises** on anything else.

**Files:**
- Create: `lib/cure/audit/refs.ex`
- Test: `test/cure/audit/refs_test.exs`

**Interfaces:**
- Consumes: nothing.
- Produces:
  - `Cure.Audit.Refs.scan(term_or_extern) :: %{globals: [atom()], holes: [String.t()], absurd: non_neg_integer()}` — one exhaustive walk. Lists are deduplicated and sorted. Raises `ArgumentError` on an unknown node.
  - `Cure.Audit.Refs.globals(term_or_extern) :: [atom()]` — `scan/1 |> Map.fetch!(:globals)`.
  - Accepts two non-Core sentinels that occupy a def's `body` slot, both returning the empty scan: `{:extern, {m, f, a}}`, and **`nil`** — every `builtin_op`-tagged def has a `nil` body (see Verified Facts). Without this clause, `Ledger`'s reachability walk (Task 3), which deliberately does not skip `builtin_op` defs, raises the instant it reaches one — which happens for any module using arithmetic, comparison, or `struct_eq`, `Std.List` included.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/audit/refs_test.exs
defmodule Cure.Audit.RefsTest do
  use ExUnit.Case, async: true
  alias Cure.Audit.Refs

  test "collects globals from every child position" do
    t = {:app, {:global, :f}, {:global, :g}}
    assert Refs.globals(t) == [:f, :g]
  end

  test "collects globals inside a let — the clause global_refs/1 lacks" do
    t = {:let, {:global, :ty}, {:global, :val}, {:global, :body}}
    assert Refs.globals(t) == [:body, :ty, :val]
  end

  test "collects globals from case scrutinee, motive, and branches" do
    t = {:case, {:global, :s}, {:global, :m}, [{:Cons, 2, {:global, :b}}]}
    assert Refs.globals(t) == [:b, :m, :s]
  end

  test "collects globals from data params and indices, and ctor args" do
    t = {:data, :Vec, [{:global, :p}], [{:global, :i}]}
    assert Refs.globals(t) == [:i, :p]
    assert Refs.globals({:ctor, :Cons, [{:global, :x}]}) == [:x]
  end

  test "deduplicates and sorts" do
    t = {:app, {:global, :f}, {:app, {:global, :f}, {:global, :a}}}
    assert Refs.globals(t) == [:a, :f]
  end

  test "reports holes and absurd" do
    t = {:app, {:hole, "goal"}, {:absurd}}
    assert Refs.scan(t) == %{globals: [], holes: ["goal"], absurd: 1}
  end

  test "accepts the extern body sentinel" do
    assert Refs.scan({:extern, {:erlang, :length, 1}}) ==
             %{globals: [], holes: [], absurd: 0}
  end

  test "accepts nil — a builtin op's absent body" do
    # Every `builtin_op`-tagged def (`Builtins.seed_ops`) has `body: nil`, not a
    # Core.Term. Ledger's reachability walk does not skip builtin_op defs (Task
    # 3), so it calls `Refs.scan/1` on one for any module that reaches `+`,
    # `==`, etc. — which is most of them. Without this clause, `mix test` on
    # Task 3's divergence test and the Task 7 `Std.List` golden test both raise
    # `unknown Core term in Audit.Refs: nil`.
    assert Refs.scan(nil) == %{globals: [], holes: [], absurd: 0}
  end

  test "raises on an unknown node instead of silently returning []" do
    assert_raise ArgumentError, ~r/unknown Core term/, fn -> Refs.scan({:bogus}) end
  end

  test "every term Antigen generates walks without raising" do
    # Antigen already generates well-formed Core terms. This guard upgrades
    # automatically as the Core grammar grows: a new former that Refs does not
    # handle makes this test raise.
    terms =
      Antigen.Backend.StreamData.sample_seeded(
        Antigen.Generators.Term.default_gen(),
        200,
        20_260_710
      )

    for t <- terms do
      assert is_map(Refs.scan(t))
    end
  end
end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/cure/audit/refs_test.exs`
Expected: FAIL — `Cure.Audit.Refs` undefined.

Note: two implementation clauses below are already load-bearing for Task 3, not
speculative hardening — `walk(nil, acc)` in particular. Skipping it here means
Task 3's own test suite fails with a raised `ArgumentError`, not a normal
assertion failure.

- [ ] **Step 3: Write the implementation**

```elixir
# lib/cure/audit/refs.ex
defmodule Cure.Audit.Refs do
  @moduledoc """
  A **fail-closed** walk over `Cure.Core.Term`.

  `Cure.Elab.Program.global_refs/1` ends in a catch-all `_leaf -> []`. That is
  benign for codegen and fatal for an audit: when the Core grammar grows a
  former, reachability silently under-reports and the ledger quietly stops
  finding axioms. (It had already happened — `global_refs/1` had no `:let`
  clause until `9166433`; the fail-open catch-all it still ends in is why the
  ledger uses this fail-closed walker instead.)

  Every clause of `Cure.Core.Term.term?/1` is enumerated here explicitly, and
  anything else raises. Untrusted; outside the TCB.
  """

  @type scan :: %{globals: [atom()], holes: [String.t()], absurd: non_neg_integer()}

  @empty %{globals: [], holes: [], absurd: 0}

  @spec globals(term()) :: [atom()]
  def globals(t), do: scan(t).globals

  @spec scan(term()) :: scan()
  def scan(t) do
    acc = walk(t, @empty)
    %{acc | globals: acc.globals |> Enum.uniq() |> Enum.sort(), holes: Enum.sort(acc.holes)}
  end

  # The non-Core sentinel occupying an extern def's `body` slot.
  defp walk({:extern, {m, f, a}}, acc) when is_atom(m) and is_atom(f) and is_integer(a), do: acc

  # The non-Core sentinel occupying a builtin_op def's `body` slot (`int_add`,
  # `struct_eq`, …: `Builtins.seed_ops` never gives them a body). Ledger's
  # reachability walk does not skip builtin_op defs, so this fires on ordinary
  # input (any module using `+`/`==`), not on malformed input — required, not
  # defensive.
  defp walk(nil, acc), do: acc

  defp walk({:global, name}, acc), do: %{acc | globals: [name | acc.globals]}
  defp walk({:hole, name}, acc), do: %{acc | holes: [name | acc.holes]}
  defp walk({:absurd}, acc), do: %{acc | absurd: acc.absurd + 1}

  defp walk({:type, _}, acc), do: acc
  defp walk({:var, _}, acc), do: acc
  defp walk({:int_type}, acc), do: acc
  defp walk({:int_lit, _}, acc), do: acc
  defp walk({:nat_lit, _}, acc), do: acc
  defp walk({:bounded_lit, _}, acc), do: acc
  defp walk({:float_type}, acc), do: acc
  defp walk({:float_lit, _}, acc), do: acc
  defp walk({:binary_type}, acc), do: acc
  defp walk({:atom_type}, acc), do: acc
  defp walk({:atom_lit, _}, acc), do: acc

  defp walk({:pi, dom, cod}, acc), do: acc |> then(&walk(dom, &1)) |> then(&walk(cod, &1))
  defp walk({:lam, dom, body}, acc), do: acc |> then(&walk(dom, &1)) |> then(&walk(body, &1))

  defp walk({:let, ty, val, body}, acc),
    do: acc |> then(&walk(ty, &1)) |> then(&walk(val, &1)) |> then(&walk(body, &1))

  defp walk({:app, f, a}, acc), do: acc |> then(&walk(f, &1)) |> then(&walk(a, &1))

  defp walk({:data, _name, params, indices}, acc),
    do: Enum.reduce(params ++ indices, acc, &walk/2)

  defp walk({:ctor, _name, args}, acc), do: Enum.reduce(args, acc, &walk/2)

  defp walk({:case, scrut, motive, branches}, acc) do
    acc
    |> then(&walk(scrut, &1))
    |> then(&walk(motive, &1))
    |> then(fn a -> Enum.reduce(branches, a, fn {_c, _arity, body}, a2 -> walk(body, a2) end) end)
  end

  defp walk(other, _acc) do
    raise ArgumentError, "unknown Core term in Audit.Refs: #{inspect(other)}"
  end
end
```

- [ ] **Step 4: Run the test to verify it passes**

Run: `mix test test/cure/audit/refs_test.exs`
Expected: PASS, 10 tests.

If the Antigen guard raises on some former, that is the walker doing its job: add the missing clause to `walk/2` and re-run. Do **not** add a catch-all. (`nil` and `{:extern, _}` are the two deliberate, documented exceptions to that rule — both are non-`Core.Term` sentinels that occupy a def's `body` slot, not unknown grammar.)

- [ ] **Step 5: Commit**

```bash
git add lib/cure/audit/refs.ex test/cure/audit/refs_test.exs
git commit -m "feat(audit): fail-closed Core.Term reference walker"
```

---

### Task 3: `Cure.Audit.Ledger` — roots, reachability, classification

**Files:**
- Create: `lib/cure/audit/ledger.ex`
- Test: `test/cure/audit/ledger_test.exs`

**Interfaces:**
- Consumes: `Cure.Audit.Refs.scan/1`, `Cure.Core.Printer.print/1`.
- Produces:
  - `%Cure.Audit.Ledger.Axiom{mfa: {atom, atom, non_neg_integer}, type: String.t(), via: atom(), bucket: :otp | :cure_runtime | :cure_bridge}`
  - `%Cure.Audit.Ledger.Report{axioms: [Axiom.t()], opaque: [atom()], builtin_count: non_neg_integer(), holes: [String.t()], absurd: non_neg_integer(), not_proven_total: [atom()], unaudited: [{String.t(), term()}]}`
  - `Cure.Audit.Ledger.prelude_env() :: Env.t()`
  - `Cure.Audit.Ledger.roots(Env.t()) :: [atom()]`
  - `Cure.Audit.Ledger.audit_source(source :: String.t(), label :: String.t()) :: Report.t()`
  - `Cure.Audit.Ledger.bucket({m, f, a}) :: :otp | :cure_runtime | :cure_bridge`

**Classification.** By target module atom: a name beginning `cure_std_` is `:cure_runtime`; a name beginning `Elixir.Cure.` is `:cure_bridge`; everything else is `:otp`.

**Axiom identity** is `{mfa, type}` — never the Cure def name, which is a bare atom pre-rekey. Two wrappers of one MFA at two types are two axioms; one MFA at one type reached by two names is one axiom. `via` records one reaching def name for display only.

**Reachability** starts at `roots/1` and walks both a def's **type** and its **body** (a type-level global is reachable). Unlike `Program.reachable_def_names/2`, it does **not** skip `builtin_op` defs or type-level defs. **Correction (as-built):** the original plan said an unresolved global *raises*, on the theory that `Kernel.infer/2` rejects dangling globals so the case is unreachable. That is false for a def's **type** — a bodyless `@extern` postulates its signature unchecked, so `Std.Fsm` elaborates with `Pid`/`Any`/`Map`/`Tuple`/`String` undefined. The ledger instead resolves each global against `defs → families → ctors` and reports the remainder under an `UNRESOLVED` section (the `%Report{}` struct carries a `unresolved: [atom()]` field for this). See spec §4.6.

**`not_proven_total`** = reachable roots absent from `env.certified`, **excluding** externs (no body to certify) and `builtin_op`s. Guard `env.certified` for `nil`.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/audit/ledger_test.exs
defmodule Cure.Audit.LedgerTest do
  use ExUnit.Case, async: true
  alias Cure.Audit.Ledger

  defp audit(src), do: Ledger.audit_source(src, "Test")

  test "an @extern yields exactly one ffi_postulate with its MFA and rendered type" do
    src = """
    mod Test.One
      @extern(:erlang, :length, 1)
      fn len(xs: List(t)) -> Int
    end
    """

    report = audit(src)
    assert [axiom] = report.axioms
    assert axiom.mfa == {:erlang, :length, 1}
    assert axiom.bucket == :otp
    assert axiom.type == "∀ {a}. List(a) -> Int"
  end

  test "widening the declared type changes the rendered line" do
    narrow = """
    mod Test.Narrow
      @extern(:erlang, :length, 1)
      fn len(xs: List(Int)) -> Int
    end
    """

    wide = """
    mod Test.Wide
      @extern(:erlang, :length, 1)
      fn len(xs: List(t)) -> Int
    end
    """

    [a] = audit(narrow).axioms
    [b] = audit(wide).axioms
    assert a.mfa == b.mfa
    refute a.type == b.type
  end

  test "buckets by target module" do
    assert Ledger.bucket({:erlang, :length, 1}) == :otp
    assert Ledger.bucket({:cure_std_crdt, :or_add, 4}) == :cure_runtime
    assert Ledger.bucket({:"Elixir.Cure.FSM.Builtins", :spawn_fsm, 2}) == :cure_bridge
  end

  test "divergence: builtin_op is an axiom here and invisible to codegen reachability" do
    src = """
    mod Test.Arith
      fn double(x: Int) -> Int = x + x
    end
    """

    {:ok, env} = Cure.Elab.Program.elaborate(src)
    roots = Ledger.roots(env)

    # The ledger counts every builtin operator in the env.
    assert audit(src).builtin_count == 31

    # Codegen's walk deliberately drops them ("never emitted as a function form").
    codegen_reachable = Cure.Elab.Program.reachable_def_names(env, roots)
    builtin_names = for {n, d} <- env.defs, Map.get(d, :builtin_op), do: n
    assert Enum.all?(builtin_names, fn n -> n not in codegen_reachable end)
    refute builtin_names == []
  end

  test "an opaque type is reported; a genuinely empty inductive is not" do
    opaque = """
    mod Test.Opaque
      opaque type Effect
    end
    """

    empty = """
    mod Test.Empty
      type Void =
        |
    end
    """

    assert audit(opaque).opaque == [:Effect]
    assert audit(empty).opaque == []
  end

  test "roots exclude the prelude" do
    src = """
    mod Test.Roots
      fn f(x: Int) -> Int = x
    end
    """

    {:ok, env} = Cure.Elab.Program.elaborate(src)
    assert Ledger.roots(env) == [:f]
  end

  test "prelude externs are not attributed to the audited module" do
    src = """
    mod Test.NoPreludeLeak
      fn f(x: Int) -> Int = x
    end
    """

    assert audit(src).axioms == []
  end

  test "a module that fails to elaborate is recorded as unaudited" do
    report = Ledger.audit_source("mod Test.Broken\n  fn f(x: Int) -> = \nend\n", "Test.Broken")
    assert [{"Test.Broken", _reason}] = report.unaudited
    assert report.axioms == []
  end
end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/cure/audit/ledger_test.exs`
Expected: FAIL — `Cure.Audit.Ledger` undefined.

- [ ] **Step 3: Write the implementation**

```elixir
# lib/cure/audit/ledger.ex
defmodule Cure.Audit.Ledger do
  @moduledoc """
  Enumerate what a module assumes without proof.

  Reads the elaborated `Cure.Core.Env`, never source text: a macro may emit an
  `@extern`, and macro output is re-elaborated, so `Core.Env` is the only vantage
  point that observes every axiom. Untrusted; outside the TCB.
  """

  alias Cure.Audit.Refs
  alias Cure.Core.Printer
  alias Cure.Core.Env
  alias Cure.Elab.Program

  defmodule Axiom do
    @moduledoc false
    defstruct [:mfa, :type, :via, :bucket]
    @type t :: %__MODULE__{}
  end

  defmodule Report do
    @moduledoc false
    defstruct axioms: [],
              opaque: [],
              builtin_count: 0,
              holes: [],
              absurd: 0,
              not_proven_total: [],
              unaudited: []

    @type t :: %__MODULE__{}
  end

  # Verified to elaborate on this branch, yielding 42 defs.
  @prelude_probe "mod Probe.Empty\nend\n"

  @doc "The defs every module gets for free. Computed once per call; cheap."
  @spec prelude_env() :: Env.t()
  def prelude_env do
    {:ok, env} = Program.elaborate(@prelude_probe)
    env
  end

  @doc """
  The defs the audited module owns: everything in its env that the prelude env
  does not already have. A macro-emitted def appears here, which is the point.
  """
  # As-built (ad6f5fb): diff on (name, body), NOT name alone — a module
  # redefining a prelude name with an @extern body would otherwise vanish.
  @spec roots(Env.t()) :: [atom()]
  def roots(%Env{defs: defs}) do
    prelude = prelude_env().defs

    names =
      for {name, d} <- defs,
          Map.get(prelude, name) == nil or Map.get(prelude, name).body != d.body,
          do: name

    Enum.sort(names)
  end

  @spec bucket({atom(), atom(), non_neg_integer()}) :: :otp | :cure_runtime | :cure_bridge
  def bucket({m, _f, _a}) do
    s = Atom.to_string(m)

    cond do
      String.starts_with?(s, "cure_std_") -> :cure_runtime
      String.starts_with?(s, "Elixir.Cure.") -> :cure_bridge
      true -> :otp
    end
  end

  @spec audit_source(String.t(), String.t()) :: Report.t()
  def audit_source(source, label) do
    case Program.elaborate(source) do
      {:ok, env} -> audit_env(env)
      {:error, reason} -> %Report{unaudited: [{label, reason}]}
    end
  end

  @spec audit_env(Env.t()) :: Report.t()
  def audit_env(%Env{} = env) do
    reachable = reachable(env, roots(env))

    axioms =
      for name <- reachable,
          def = Map.fetch!(env.defs, name),
          match?({:extern, _}, def.body) do
        {:extern, mfa} = def.body
        %Axiom{mfa: mfa, type: Printer.print(def.type), via: name, bucket: bucket(mfa)}
      end
      |> Enum.uniq_by(fn a -> {a.mfa, a.type} end)
      |> Enum.sort_by(&sort_key/1)

    scans = for name <- reachable, do: Refs.scan(Map.fetch!(env.defs, name).body)

    %Report{
      axioms: axioms,
      opaque: env.families |> Map.keys() |> Enum.filter(&Cure.Core.Inductive.opaque?(env, &1)) |> Enum.sort(),
      builtin_count: Enum.count(env.defs, fn {_n, d} -> Map.get(d, :builtin_op) end),
      holes: scans |> Enum.flat_map(& &1.holes) |> Enum.sort(),
      absurd: scans |> Enum.map(& &1.absurd) |> Enum.sum(),
      not_proven_total: not_proven_total(env, reachable),
      unaudited: []
    }
  end

  # Sorted, stable, and independent of map iteration order.
  defp sort_key(%Axiom{mfa: {m, f, a}, type: t}), do: {Atom.to_string(m), Atom.to_string(f), a, t}

  # Our own walk. NOT Program.reachable_def_names/2, whose collect_reachable/4
  # skips builtin_op defs and type-level defs — correct for codegen, and
  # catastrophic here, because the first drops arithmetic, which is an axiom.
  defp reachable(env, roots) do
    Enum.reduce(roots, MapSet.new(), fn root, seen -> collect(env, root, seen) end)
    |> MapSet.to_list()
    |> Enum.sort()
  end

  defp collect(env, name, seen) do
    cond do
      MapSet.member?(seen, name) ->
        seen

      true ->
        case Map.get(env.defs, name) do
          nil ->
            # Kernel.infer/2 already rejects dangling globals on a checked env.
            raise ArgumentError, "unresolved global #{inspect(name)}: caller skipped check_def"

          def ->
            seen = MapSet.put(seen, name)
            refs = Refs.globals(def.type) ++ Refs.globals(def.body)
            Enum.reduce(refs, seen, fn ref, s -> collect(env, ref, s) end)
        end
    end
  end

  # A completeness limit, not an assumption: an uncertified def never δ-unfolds,
  # so the kernel cannot use it to inhabit a type. Externs have no body to
  # certify, and builtin ops are a kernel baseline; both are excluded.
  defp not_proven_total(%Env{certified: nil}, _reachable), do: []

  defp not_proven_total(%Env{} = env, reachable) do
    for name <- reachable,
        def = Map.fetch!(env.defs, name),
        not MapSet.member?(env.certified, name),
        is_nil(Map.get(def, :builtin_op)),
        not match?({:extern, _}, def.body),
        do: name
  end
end
```

- [ ] **Step 4: Run the test to verify it passes**

Run: `mix test test/cure/audit/ledger_test.exs`
Expected: PASS, 8 tests.

If `audit_source` on the `opaque type Effect` fixture fails to elaborate, drop that fixture to the minimal declaration the parser accepts and keep the assertion. Do not weaken the assertion itself.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/audit/ledger.ex test/cure/audit/ledger_test.exs
git commit -m "feat(audit): axiom ledger — prelude-diff roots, own reachability, MFA identity"
```

---

### Task 4: `Cure.Audit.Targets` — the capability table

Data, not analysis. A wrong entry produces a wrong report and nothing worse.

**Files:**
- Create: `lib/cure/audit/targets.ex`
- Test: append to `test/cure/audit/ledger_test.exs`

**Interfaces:**
- Consumes: nothing.
- Produces: `Cure.Audit.Targets.known() :: [atom()]`, `Cure.Audit.Targets.unavailable(target :: atom()) :: MapSet.t(atom())`, `Cure.Audit.Targets.unavailable?(target :: atom(), mfa) :: boolean()`.

- [ ] **Step 1: Write the failing test**

```elixir
# append to test/cure/audit/ledger_test.exs
defmodule Cure.Audit.TargetsTest do
  use ExUnit.Case, async: true
  alias Cure.Audit.Targets

  test "atomvm lacks re, inets, httpc, persistent_term and Registry" do
    for m <- [:re, :inets, :httpc, :persistent_term, :"Elixir.Registry"] do
      assert Targets.unavailable?(:atomvm, {m, :any, 0}), "expected #{m} unavailable"
    end
  end

  test "atomvm has erlang and lists" do
    refute Targets.unavailable?(:atomvm, {:erlang, :length, 1})
    refute Targets.unavailable?(:atomvm, {:lists, :reverse, 1})
  end

  test "an unknown target has nothing unavailable" do
    assert Targets.unavailable(:no_such_vm) == MapSet.new()
  end

  test "atomvm is a known target" do
    assert :atomvm in Targets.known()
  end
end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/cure/audit/ledger_test.exs`
Expected: FAIL — `Cure.Audit.Targets` undefined.

- [ ] **Step 3: Write the implementation**

```elixir
# lib/cure/audit/targets.ex
defmodule Cure.Audit.Targets do
  @moduledoc """
  Which BEAM modules are absent on which target VM.

  Hand-maintained data. The ledger already knows every axiom's target MFA, so
  this table is all that stands between it and a portability report. A wrong
  entry yields a wrong report and nothing worse.

  Sources: the AtomVM dead-ends enumerated in `esp32-beam/CLAUDE.md`.
  """

  @unavailable %{
    atomvm:
      MapSet.new([
        :re,
        :inets,
        :httpc,
        :persistent_term,
        :"Elixir.Registry"
      ])
  }

  @spec known() :: [atom()]
  def known, do: @unavailable |> Map.keys() |> Enum.sort()

  @spec unavailable(atom()) :: MapSet.t(atom())
  def unavailable(target), do: Map.get(@unavailable, target, MapSet.new())

  @spec unavailable?(atom(), {atom(), atom(), non_neg_integer()}) :: boolean()
  def unavailable?(target, {m, _f, _a}), do: MapSet.member?(unavailable(target), m)
end
```

- [ ] **Step 4: Run the test to verify it passes**

Run: `mix test test/cure/audit/ledger_test.exs`
Expected: PASS, 12 tests (8 from `LedgerTest` + 4 from `TargetsTest`, both in this file).

- [ ] **Step 5: Commit**

```bash
git add lib/cure/audit/targets.ex test/cure/audit/ledger_test.exs
git commit -m "feat(audit): per-target capability table"
```

---

### Task 5: `Cure.Audit.Format` — deterministic text and JSON

**Files:**
- Create: `lib/cure/audit/format.ex`
- Test: `test/cure/audit/format_test.exs`

**Interfaces:**
- Consumes: `%Ledger.Report{}`, `Cure.Audit.Targets`.
- Produces: `Cure.Audit.Format.to_text(Report.t(), opts :: keyword()) :: String.t()` and `to_json(Report.t(), opts) :: String.t()`. `opts` accepts `target: atom() | nil`.

`UNAVAILABLE ON TARGET` is emitted **only** when `target` is non-nil. Every other section always prints, even at `(0)`.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/audit/format_test.exs
defmodule Cure.Audit.FormatTest do
  use ExUnit.Case, async: true
  alias Cure.Audit.{Format, Ledger}
  alias Cure.Audit.Ledger.{Axiom, Report}

  defp report do
    %Report{
      axioms: [
        %Axiom{mfa: {:erlang, :length, 1}, type: "∀ {a}. List(a) -> Int", via: :length, bucket: :otp}
      ],
      builtin_count: 31,
      not_proven_total: [:reverse, :last, :drop, :take]
    }
  end

  test "renders every section, including empty ones" do
    text = Format.to_text(report(), [])

    assert text =~ "AXIOMS — OTP (1)"
    assert text =~ "erlang:length/1"
    assert text =~ "∀ {a}. List(a) -> Int"
    assert text =~ "AXIOMS — CURE RUNTIME (0)"
    assert text =~ "AXIOMS — CURE BRIDGE (0)"
    assert text =~ "OPAQUE TYPES (0)"
    assert text =~ "31 builtin operators"
    assert text =~ "HOLES (0)"
    assert text =~ "ABSURD (0)"
    assert text =~ "NOT PROVEN TOTAL (4)"
    assert text =~ "cannot be used in proofs; not assumptions"
    assert text =~ "UNAUDITED (0)"
  end

  test "omits the target section unless --target was given" do
    refute Format.to_text(report(), []) =~ "UNAVAILABLE ON TARGET"
    assert Format.to_text(report(), target: :atomvm) =~ "UNAVAILABLE ON TARGET (0)"
  end

  test "reports an unavailable axiom for the named target" do
    r = %Report{axioms: [%Axiom{mfa: {:re, :run, 3}, type: "Binary -> Binary", via: :run, bucket: :otp}]}
    text = Format.to_text(r, target: :atomvm)
    assert text =~ "UNAVAILABLE ON TARGET (1)"
    assert text =~ "re:run/3"
    assert text =~ ":re absent on atomvm"
  end

  test "output is byte-identical across runs" do
    assert Format.to_text(report(), []) == Format.to_text(report(), [])
    assert Format.to_json(report(), []) == Format.to_json(report(), [])
  end

  test "json carries a schema version and the same axiom set" do
    # `Jason` is NOT a dependency of this project (checked mix.exs: metastatic,
    # marcli, makeup, makeup_cure, md, telemetry, toml, stream_data, and the
    # dev/test-only tooling). Do not add one. Assert on the emitted string.
    json = Format.to_json(report(), [])
    assert json =~ ~s("schema":1)
    assert json =~ ~s("mfa":"erlang:length/1")
    assert json =~ ~s("bucket":"otp")
    assert json =~ ~s("builtin_count":31)
    assert String.ends_with?(json, "}\n")
  end
end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/cure/audit/format_test.exs`
Expected: FAIL — `Cure.Audit.Format` undefined.

- [ ] **Step 3: Write the implementation**

```elixir
# lib/cure/audit/format.ex
defmodule Cure.Audit.Format do
  @moduledoc """
  Render a `Cure.Audit.Ledger.Report` deterministically.

  Determinism is load-bearing: `cure audit trust Std.List | diff -` is the
  ratchet that makes a new axiom a reviewable diff. Sorted, no timestamps, no
  absolute paths, no map-iteration order. Every section prints even when empty,
  so a `(0)` becoming a `(1)` is a diff rather than a new line from nowhere.
  """

  alias Cure.Audit.{Ledger, Targets}
  alias Cure.Audit.Ledger.Axiom

  @spec to_text(Ledger.Report.t(), keyword()) :: String.t()
  def to_text(report, opts) do
    target = Keyword.get(opts, :target)

    [
      bucket_section("AXIOMS — OTP", report.axioms, :otp),
      bucket_section("AXIOMS — CURE RUNTIME", report.axioms, :cure_runtime),
      bucket_section("AXIOMS — CURE BRIDGE", report.axioms, :cure_bridge),
      list_section("OPAQUE TYPES", Enum.map(report.opaque, &Atom.to_string/1)),
      "KERNEL BUILTINS\n  #{report.builtin_count} builtin operators (Cure.Core.Builtins)",
      list_section("HOLES", report.holes),
      "ABSURD (#{report.absurd})",
      not_total_section(report.not_proven_total),
      target_section(report.axioms, target),
      list_section("UNAUDITED", Enum.map(report.unaudited, fn {label, _} -> label end))
    ]
    |> Enum.reject(&is_nil/1)
    |> Enum.join("\n\n")
    |> Kernel.<>("\n")
  end

  @spec to_json(Ledger.Report.t(), keyword()) :: String.t()
  def to_json(report, _opts) do
    axioms =
      Enum.map(report.axioms, fn a ->
        ~s({"mfa":"#{mfa(a)}","type":"#{escape(a.type)}","via":"#{a.via}","bucket":"#{a.bucket}"})
      end)

    ~s({"schema":1,"axioms":[#{Enum.join(axioms, ",")}],) <>
      ~s("opaque":[#{Enum.map_join(report.opaque, ",", &~s("#{&1}"))}],) <>
      ~s("builtin_count":#{report.builtin_count},) <>
      ~s("holes":[#{Enum.map_join(report.holes, ",", &~s("#{escape(&1)}"))}],) <>
      ~s("absurd":#{report.absurd},) <>
      ~s("not_proven_total":[#{Enum.map_join(report.not_proven_total, ",", &~s("#{&1}"))}],) <>
      ~s("unaudited":[#{Enum.map_join(report.unaudited, ",", fn {l, _} -> ~s("#{l}") end)}]}) <>
      "\n"
  end

  # -- sections --------------------------------------------------------------

  defp bucket_section(title, axioms, bucket) do
    rows = Enum.filter(axioms, &(&1.bucket == bucket))
    header = "#{title} (#{length(rows)})"

    case rows do
      [] -> header
      _ -> header <> "\n" <> Enum.map_join(rows, "\n", &"  #{pad(mfa(&1))} #{&1.type}")
    end
  end

  defp list_section(title, []), do: "#{title} (0)"

  defp list_section(title, items),
    do: "#{title} (#{length(items)})\n" <> Enum.map_join(items, "\n", &"  #{&1}")

  defp not_total_section([]),
    do: "NOT PROVEN TOTAL (0)   — cannot be used in proofs; not assumptions"

  defp not_total_section(names) do
    "NOT PROVEN TOTAL (#{length(names)})   — cannot be used in proofs; not assumptions\n" <>
      "  " <> Enum.map_join(names, ", ", &Atom.to_string/1)
  end

  defp target_section(_axioms, nil), do: nil

  defp target_section(axioms, target) do
    rows = Enum.filter(axioms, &Targets.unavailable?(target, &1.mfa))
    header = "UNAVAILABLE ON TARGET (#{length(rows)})"

    case rows do
      [] ->
        header

      _ ->
        header <>
          "\n" <>
          Enum.map_join(rows, "\n", fn a ->
            {m, _f, _a} = a.mfa
            "  #{pad(mfa(a))} via #{a.via}   — :#{m} absent on #{target}"
          end)
    end
  end

  # -- helpers ---------------------------------------------------------------

  defp mfa(%Axiom{mfa: {m, f, a}}), do: "#{m}:#{f}/#{a}"
  defp pad(s), do: String.pad_trailing(s, 24)
  defp escape(s), do: s |> String.replace("\\", "\\\\") |> String.replace("\"", "\\\"")
end
```

- [ ] **Step 4: Run the test to verify it passes**

Run: `mix test test/cure/audit/format_test.exs`
Expected: PASS, 5 tests.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/audit/format.ex test/cure/audit/format_test.exs
git commit -m "feat(audit): deterministic text and JSON report formatting"
```

---

### Task 6: `Cure.Audit.Source` + the `cure audit trust` CLI verb

**Files:**
- Create: `lib/cure/audit/source.ex`
- Modify: `lib/cure/cli.ex` (add switches to the `OptionParser.parse/2` call around line 36; add a `["audit", "trust", mod]` clause to the command `case` near the `["migrate" | paths]` clause around line 139)
- Test: `test/cure/audit/trust_cli_test.exs`

**Interfaces:**
- Consumes: `Cure.Audit.Ledger.audit_source/2`, `Cure.Audit.Format`.
- Produces:
  - `Cure.Audit.Source.locate(module :: String.t()) :: {:ok, Path.t()} | {:error, :not_found}` — scans `lib/std/*.cure` for a `mod <Module>` header. Filename does not determine module name (`Std.NonEmpty` lives in `non_empty.cure`, `Std.CRDT` in `crdt.cure`), so the header is authoritative.
  - `Cure.Audit.CLI.run(module :: String.t(), opts :: keyword()) :: {:ok, String.t()} | {:strict_failure, String.t()} | {:error, :not_found}` — pure; returns the report text and whether `--strict` should fail, or propagates `Source.locate/1`'s miss. The CLI clause calls `System.halt/1`, the function does not, so it stays testable.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/audit/trust_cli_test.exs
defmodule Cure.Audit.TrustCLITest do
  use ExUnit.Case, async: true
  alias Cure.Audit.{CLI, Source}

  test "locates a stdlib module by its mod header, not its filename" do
    assert {:ok, path} = Source.locate("Std.NonEmpty")
    assert Path.basename(path) == "non_empty.cure"

    assert {:ok, path} = Source.locate("Std.CRDT")
    assert Path.basename(path) == "crdt.cure"
  end

  test "an unknown module is not found" do
    assert Source.locate("Std.NoSuchModule") == {:error, :not_found}
  end

  test "CLI.run propagates a not-found module — the path the halt(1) clause depends on" do
    # Source.locate/1 returning {:error, :not_found} is tested above; this pins
    # that CLI.run/2's `with` actually propagates it rather than raising or
    # swallowing it, since that is the exact tuple the CLI command clause
    # pattern-matches on to print "no such module" and halt(1).
    assert CLI.run("Std.NoSuchModule", []) == {:error, :not_found}
  end

  test "Std.List produces a report and does not fail --strict" do
    assert {:ok, text} = CLI.run("Std.List", [])
    assert text =~ "AXIOMS — OTP (1)"
    assert text =~ "UNAUDITED (0)"
    assert {:ok, _} = CLI.run("Std.List", strict: true)
  end

  test "Std.Time does not elaborate, so it lands in UNAUDITED" do
    assert {:ok, text} = CLI.run("Std.Time", [])
    assert text =~ "UNAUDITED (1)"
    assert text =~ "Std.Time"
  end

  test "--strict fails iff UNAUDITED is non-empty" do
    assert {:strict_failure, _} = CLI.run("Std.Time", strict: true)
    assert {:ok, _} = CLI.run("Std.Time", [])
  end

  test "--target adds the section; its absence omits it" do
    {:ok, with_target} = CLI.run("Std.List", target: :atomvm)
    {:ok, without} = CLI.run("Std.List", [])
    assert with_target =~ "UNAVAILABLE ON TARGET"
    refute without =~ "UNAVAILABLE ON TARGET"
  end

  test "two runs are byte-identical" do
    {:ok, a} = CLI.run("Std.List", [])
    {:ok, b} = CLI.run("Std.List", [])
    assert a == b
  end
end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/cure/audit/trust_cli_test.exs`
Expected: FAIL — `Cure.Audit.Source` undefined.

- [ ] **Step 3: Write the implementation**

```elixir
# lib/cure/audit/source.ex
defmodule Cure.Audit.Source do
  @moduledoc """
  Locate a stdlib module's source by its declared `mod` header.

  The filename does not determine the module name — `Std.NonEmpty` lives in
  `non_empty.cure` and `Std.CRDT` in `crdt.cure` — so the header is authoritative.
  """

  @std_dir Path.expand("../../../lib/std", __DIR__)

  @spec locate(String.t()) :: {:ok, Path.t()} | {:error, :not_found}
  def locate(module) do
    pattern = ~r/^\s*mod\s+#{Regex.escape(module)}\s*$/m

    Path.wildcard(Path.join(@std_dir, "*.cure"))
    |> Enum.sort()
    |> Enum.find(fn path -> Regex.match?(pattern, File.read!(path)) end)
    |> case do
      nil -> {:error, :not_found}
      path -> {:ok, path}
    end
  end
end
```

```elixir
# lib/cure/audit/cli.ex
defmodule Cure.Audit.CLI do
  @moduledoc """
  `cure audit trust <Module>` — print the unproved assumptions reachable from a
  module. Never wired into `cure build`: a compiler that refuses to build over an
  audit trains people to hate the audit.
  """

  alias Cure.Audit.{Format, Ledger, Source}

  @spec run(String.t(), keyword()) :: {:ok, String.t()} | {:strict_failure, String.t()} | {:error, term()}
  def run(module, opts) do
    with {:ok, path} <- Source.locate(module) do
      report = Ledger.audit_source(File.read!(path), module)
      text = Format.render(report, opts)

      cond do
        Keyword.get(opts, :strict, false) and report.unaudited != [] -> {:strict_failure, text}
        true -> {:ok, text}
      end
    end
  end
end
```

Add to `Cure.Audit.Format`:

```elixir
  @spec render(Ledger.Report.t(), keyword()) :: String.t()
  def render(report, opts) do
    case Keyword.get(opts, :format, "text") do
      "json" -> to_json(report, opts)
      _ -> to_text(report, opts)
    end
  end
```

In `lib/cure/cli.ex`, add these switches to the existing `OptionParser.parse/2` `switches:` keyword list (it already carries `filter: :string` and friends):

```elixir
          target: :string,
          format: :string,
```

**`strict: :boolean` already exists** in that list (used today by `cure migrate --strict`) — do **not** add it again. `target:` and `format:` are the only genuinely new keys; `cure audit trust --strict` reads the same global `opts[:strict]` every other verb reads, exactly as `verbose` and the other shared flags already do.

and add this clause to the command `case`, immediately before the `["migrate" | paths]` clause:

```elixir
        ["audit", "trust", module] ->
          audit_opts = [
            strict: Keyword.get(opts, :strict, false),
            format: Keyword.get(opts, :format, "text")
          ]

          audit_opts =
            case Keyword.get(opts, :target) do
              nil -> audit_opts
              # `String.to_existing_atom/1` would raise ArgumentError on any
              # target string nothing has interned yet — every real target
              # (:atomvm) is already an atom because `Targets` module-attributes
              # it, but a typo'd --target would crash the CLI outright, which
              # contradicts Task 4's own test that an unknown target degrades
              # to "nothing unavailable," not a crash. `to_atom/1` is the
              # deliberate choice: bounded human CLI input, not untrusted
              # network/JSON input, so the usual atom-exhaustion objection
              # does not apply.
              t -> Keyword.put(audit_opts, :target, String.to_atom(t))
            end

          case Cure.Audit.CLI.run(module, audit_opts) do
            {:ok, text} ->
              IO.write(text)
              :ok

            {:strict_failure, text} ->
              IO.write(text)
              System.halt(1)

            {:error, :not_found} ->
              IO.puts(:stderr, "no such module: #{module}")
              System.halt(1)
          end
```

- [ ] **Step 4: Run the test to verify it passes**

Run: `mix test test/cure/audit/trust_cli_test.exs`
Expected: PASS, 8 tests.

Note `strict: :boolean` already exists in the switches list (verified: `lib/cure/cli.ex`, used by `cure migrate --strict`) — the Step 3 edit above adds only `target:` and `format:` for this reason. `OptionParser` would not complain about a duplicate key, but the plan's intent is one entry per switch.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/audit/source.ex lib/cure/audit/cli.ex lib/cure/audit/format.ex lib/cure/cli.ex test/cure/audit/trust_cli_test.exs
git commit -m "feat(cli): cure audit trust <Module>"
```

---

### Task 7: The `Std.List` golden test

The spec's §4.7 sample output is normative. Pin it end to end, so a change to any component that alters the report is a visible diff.

**Files:**
- Test: `test/cure/audit/trust_cli_test.exs` (append)

**Interfaces:**
- Consumes: `Cure.Audit.CLI.run/2`.
- Produces: nothing.

- [ ] **Step 1: Write the failing test**

```elixir
# append to test/cure/audit/trust_cli_test.exs
defmodule Cure.Audit.GoldenTest do
  use ExUnit.Case, async: true
  alias Cure.Audit.CLI

  @expected """
  AXIOMS — OTP (1)
    erlang:length/1          ∀ {a}. List(a) -> Int

  AXIOMS — CURE RUNTIME (0)

  AXIOMS — CURE BRIDGE (0)

  OPAQUE TYPES (0)

  KERNEL BUILTINS
    31 builtin operators (Cure.Core.Builtins)

  HOLES (0)

  ABSURD (0)

  NOT PROVEN TOTAL (4)   — cannot be used in proofs; not assumptions
    reverse, last, drop, take

  UNAUDITED (0)
  """

  test "Std.List matches the spec's sample report" do
    {:ok, text} = CLI.run("Std.List", [])
    assert text == @expected
  end

  test "not-proven-total lists exactly the four value defs, and no axioms" do
    {:ok, text} = CLI.run("Std.List", [])
    [_, tail] = String.split(text, "NOT PROVEN TOTAL (4)", parts: 2)
    [names, _] = String.split(tail, "\n\n", parts: 2)

    for n <- ~w(reverse last drop take), do: assert(names =~ n)
    # length/1 is an extern and struct_eq is a builtin op: neither belongs here.
    refute names =~ "length"
    refute names =~ "struct_eq"
  end
end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/cure/audit/trust_cli_test.exs`
Expected: FAIL on the golden comparison, showing the real output beside `@expected`.

- [ ] **Step 3: Reconcile**

The four names' **order** is `reverse, last, drop, take` in the spec but `not_proven_total/2` returns them sorted by the reachability walk. Decide once, here, and make both the spec and the implementation agree: sort `not_proven_total` alphabetically (`drop, last, reverse, take`), update `@expected` and spec §4.7 to match, and note the change in the commit body. Determinism beats matching a hand-written sample.

Do **not** special-case the ordering to preserve the spec's prose.

- [ ] **Step 4: Run the test to verify it passes**

Run: `mix test test/cure/audit/trust_cli_test.exs`
Expected: PASS, 10 tests.

- [ ] **Step 5: Run the full suite once**

Run: `mix test`
Expected: PASS. No concurrent suites.

- [ ] **Step 6: Commit**

```bash
git add test/cure/audit/trust_cli_test.exs docs/superpowers/specs/language/2026-07-10-axiom-surface-design.md
git commit -m "test(audit): golden Std.List report; sort not-proven-total"
```

---

## Self-Review

**Spec coverage.** §4 CLI → Task 6. §4.1 `Core.Env` collector → Task 3 (`audit_source/2` elaborates, never greps). §4.2 five trust classes → Task 3 (`ffi_postulate` via extern body, `builtin_op` via `builtin_count`, `opaque_family` via `opaque?/2`, `hole`/`absurd` via `Refs.scan/1`); uncertified-is-not-an-assumption → `not_proven_total/2` with its own heading. §4.3 identity `{mfa, type}` → Task 3 `Enum.uniq_by/2`. §4.4 origin tagging → Task 3 `bucket/1`, Task 5 three sections. §4.5 target availability → Tasks 4 and 6. §4.6 all three components → Tasks 1, 2, 3. §4.7 output → Tasks 5 and 7. §4.8 all eight tests → mapped in the table above.

**Gaps found and closed.** The spec never defines reachability roots; `env.defs` includes 42 prelude defs, two of them externs. Task 3 defines `roots/1` as a prelude diff and Task 3's test `"prelude externs are not attributed to the audited module"` pins it.

**Deviation.** The spec's §4.7 orders `NOT PROVEN TOTAL` as `reverse, last, drop, take`. Task 7 Step 3 sorts alphabetically and amends the spec, because determinism is a Global Constraint and insertion order is not stable.

**Placeholder scan.** No TBDs. Every code step shows the code. Task 6's `Format.render/2` is defined inline rather than referenced.

**Type consistency.** `Refs.scan/1` returns `%{globals:, holes:, absurd:}` in Task 2 and is consumed with those keys in Task 3. `Ledger.audit_source/2` returns `%Report{}` in Task 3 and is consumed in Task 6. `Format.to_text/2` and `to_json/2` in Task 5 are wrapped by `render/2` in Task 6. `Axiom` fields `mfa, type, via, bucket` are used identically in Tasks 3, 5, 7.
