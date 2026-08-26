# SP1 T8 — Macro-Expansion Soundness Firewall — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: superpowers:executing-plans (autopilot Stage 4). Steps use `- [ ]`. Builds on milestone 2 (local macro use-site expansion, commits d66bf57/0bd320f/94c33a6/6e01715).

**Goal:** Lock a central safety claim about the **dependent-elaboration entry point** — **a macro's expansion is type-checked exactly like hand-written code, with no bypass, at `Program.elaborate/1`** — as a permanent regression firewall. Concretely: for a battery of macro programs, `Program.elaborate/1` returns the *identical* verdict (accept, or reject with the identical error term) as the hand-written program the macro expands to. **Scope note (see "Known gap" below): this locks the property only for callers of `Program.elaborate/1` — it is NOT, by itself, an end-to-end guarantee about `cure build`/the CLI, which for non-dependent programs (including all four of this task's own examples) is checked by a wholly separate code path this task does not touch.**

**Architecture:** Macro expansion happens at **parse time** (`Parser.parse` substitutes the template in place), so a macro use-site produces ordinary surface AST that flows through the *unchanged* elaborator+kernel — `Cure.Elab.Program.elaborate/1` (`lib/cure/elab/program.ex:16`) neither knows nor cares that a macro was involved. This task adds **no production code**: it is a soundness firewall test that proves — and forever guards — that this is true *for `Program.elaborate/1` itself*. If any future change let macro output reach `Program.elaborate/1`'s codegen consumer (`check_ast_with_locals/1`, used by `Cure.Compiler`'s dependent-codegen branch, `lib/cure/compiler.ex:373`) without full elaboration, this test breaks. It does **not** guard the classic-pipeline branch — see "Known gap" immediately below.

**Known gap (surfaced by plan review — verified against this tree, HALT-flagged for the operator, not silently patched over):** `Cure.Compiler.compile_string/2` (the function `cure build`/the CLI/`mix cure.compile` actually call) type-checks a parsed AST via `Cure.Types.Checker.check_module/2` (classic) whenever `Cure.Elab.Program.dependent?(ast)` is `false`, and only then dispatches to the classic `Cure.Compiler.Codegen.compile_module/2` — entirely bypassing `Program.elaborate/1` and `check_ast_with_locals/1`. Verified live against this worktree: parsing all four of this task's sample programs and calling `Program.dependent?/1` on each returns `false` for all four (`zero`, `inc`, `bad`, `tt`). Compiling them via the real `Cure.Compiler.compile_string/2` confirms the classic path is what actually runs, and it produces an entirely different, line-numbered error vocabulary — e.g. for `bad` (`nonexistent_thing`): `{:error, {:type_error, [{:unbound_variable, "undefined variable 'nonexistent_thing'", [line: 3]}]}}`; for `tt` (`true` as `Int`): `{:error, {:type_error, [{:type_mismatch, "function 'f' declared return type Int but body has type Bool", [line: 4]}]}}` — vs. `Program.elaborate/1`'s `:unknown_global` / `{:conversion_failure, {:data, :Bool, [], []}, {:int_type}}`. (For what it's worth, the underlying soundness property does appear to hold on the classic route too — macro and hand-written verdicts are equal once the `[line: N]` key is stripped — but **this task's test never exercises that path**, so a regression there would go undetected.) **This task, as scoped, provides no regression protection for `cure build` on non-dependent macro-using programs.** Whether to (a) add a companion classic-pipeline firewall as a follow-up task, or (b) explicitly accept this as acceptable given the classic-pipeline-deletion roadmap (macros are intended to be dependent-pathway-only long term), is an operator decision — not resolved by this plan-hardening pass. See also the "Task boundary" section at the end.

**Tech Stack:** Elixir; ExUnit; `Cure.Elab.Program.elaborate/1`.

## Global Constraints

- **TCB delta ZERO** — no `lib/cure/core/*`, no `lib/cure/elab/*`, no `lib/cure/compiler/*` changes. This task is a **test only**. If executing it seems to require a production change, STOP and record why — it means expansion is *not* in fact re-elaborated, which is a HALT-level finding, not a code tweak.
- **Ghost commits** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no Co-Authored-By. `git add -- <path>`, never `-A`.
- **One build at a time.** Run `mix test test/cure/elab/macro_expansion_soundness_test.exs` scoped; full `mix test` only at the milestone gate.
- **Run mix from the worktree root** (`.claude/worktrees/core-let-binder`), NEVER the parent clone `/Users/ch/Develop/esp32-beam/cure-lang` (which lacks the macro code and yields phantom failures).
- **Tests immutable once green.**

## TDD framing (read before executing — this is an honest exception)

This is a **firewall / characterization test over already-correct behavior**, not a red-green feature test — the same shape as milestone-2's Task-1 pin and the existing `test/cure/elab/emit_hole_firewall_test.exs`. The behavior it asserts (expanded AST is elaborated identically to hand-written) *already works*; the test's value is permanently *locking* it. So Step "run and expect FAIL" does **not** apply to the accept/reject assertions — they pass immediately. What IS genuinely falsifiable and MUST be demonstrated red-first is the **negative control** (Step 2 below): a deliberately-broken variant of the equality helper that would pass a bypassing implementation, shown to fail, proving the test has teeth. See Task 1 Step 2.

**Verified examples (probed live against the current tree with `Program.elaborate/1` — these exact verdicts are real, not assumed):**
- `zero`→`0` used as `Int` ⇒ `{:ok, _}` (accept). Hand-written `fn f() -> Int = 0` ⇒ `{:ok, _}`.
- `inc <x: Code>`→`x + 1`, `inc n` on an `Int` param ⇒ `{:ok, _}` (accept, hole substituted).
- `bad`→`nonexistent_thing` used as `Int` ⇒ `{:error, :unknown_global}`. Hand-written `fn f() -> Int = nonexistent_thing` ⇒ **the same** `{:error, :unknown_global}`.
- `tt`→`true` used as `Int` ⇒ `{:error, {:conversion_failure, {:data, :Bool, [], []}, {:int_type}}}`. Hand-written `fn f() -> Int = true` ⇒ **the same** term. (Error terms here are position-free, so `==` between macro and hand-written verdicts is exact.)

---

### Task 1: The macro-expansion soundness firewall

**Files:**
- Create: `test/cure/elab/macro_expansion_soundness_test.exs`

**Interfaces:**
- Consumes: `Cure.Elab.Program.elaborate/1` — `{:ok, Env.t()} | {:error, term()}`.
- Produces: nothing importable — a test module. Its value is the locked property, exercised by SP3's generative fuzz later (SP3 calls `Program.elaborate` directly; this task does not build a wrapper — YAGNI).

- [ ] **Step 1: Write the firewall test file**

The core property is `verdict(macro_src) == verdict(handwritten_src)`, where `verdict/1` reduces an elaborate result to a position-free comparable shape. Because the accept case's `Env` is large and not value-comparable, `verdict/1` maps `{:ok, _} -> :accept` and passes `{:error, term}` through verbatim (the four chosen error terms are position-free — asserted by the negative control in Step 2).

```elixir
# test/cure/elab/macro_expansion_soundness_test.exs
defmodule Cure.Elab.MacroExpansionSoundnessTest do
  # SOUNDNESS FIREWALL for the Program.elaborate/1 entry point: a macro's
  # expansion is type-checked exactly like hand-written code there — expansion
  # is a parse-time surface-AST rewrite, so the *unchanged* elaborator+kernel
  # judges it (TCB delta zero for this call). This test proves it by
  # verdict-equality: each macro program elaborates to the IDENTICAL result as
  # the hand-written program it expands to — accepting when well-typed, and
  # rejecting with the SAME error term when ill-typed (well-formed-but-mistyped
  # included). If a future change ever lets macro output reach
  # check_ast_with_locals/1 (Cure.Compiler's dependent-codegen consumer)
  # without going through this same elaboration, one of these equalities
  # breaks. NOTE: this does NOT cover `cure build`'s classic-pipeline route
  # (Cure.Types.Checker.check_module/2 + Cure.Compiler.Codegen.compile_module/2),
  # which is what actually runs for non-dependent programs — see the plan's
  # "Known gap" section.
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  # Reduce an elaborate result to a position-free comparable verdict. Accept
  # collapses to :accept (the Env is large and not meaningfully ==); reject
  # keeps its error term verbatim (the terms exercised here carry no line/col).
  defp verdict(src) do
    case Program.elaborate(src) do
      {:ok, _env} -> :accept
      {:error, term} -> {:reject, term}
    end
  end

  # {label, macro_program, hand_written_equivalent}. Each macro_program's
  # expansion is textually the hand_written_equivalent's body.
  @cases [
    {"zero-hole accept: zero => 0",
     "mod M\n  macro Zero\n    syntax zero becomes 0\n  fn f() -> Int = zero\n",
     "mod M\n  fn f() -> Int = 0\n"},
    {"one-hole accept: inc <x> => x + 1",
     "mod M\n  macro Inc\n    syntax inc <x: Code> becomes x + 1\n  fn f(n: Int) -> Int = inc n\n",
     "mod M\n  fn f(n: Int) -> Int = n + 1\n"},
    {"reject (unknown global): bad => nonexistent_thing",
     "mod M\n  macro Bad\n    syntax bad becomes nonexistent_thing\n  fn f() -> Int = bad\n",
     "mod M\n  fn f() -> Int = nonexistent_thing\n"},
    {"reject (type mismatch): tt => true used as Int",
     "mod M\n  macro T\n    syntax tt becomes true\n  fn f() -> Int = tt\n",
     "mod M\n  fn f() -> Int = true\n"}
  ]

  for {label, macro_src, hand_src} <- @cases do
    test "macro verdict equals hand-written verdict — #{label}" do
      assert verdict(unquote(macro_src)) == verdict(unquote(hand_src))
    end
  end

  # Pin the accept/reject SENSE too, so an implementation that made *both* sides
  # equally broken (e.g. every program rejects) can't pass by trivial equality.
  test "the two well-typed cases genuinely accept" do
    assert verdict("mod M\n  macro Zero\n    syntax zero becomes 0\n  fn f() -> Int = zero\n") == :accept
    assert verdict("mod M\n  macro Inc\n    syntax inc <x: Code> becomes x + 1\n  fn f(n: Int) -> Int = inc n\n") == :accept
  end

  test "the two ill-typed cases genuinely reject with a position-free error term" do
    assert {:reject, :unknown_global} =
             verdict("mod M\n  macro Bad\n    syntax bad becomes nonexistent_thing\n  fn f() -> Int = bad\n")

    assert {:reject, {:conversion_failure, {:data, :Bool, [], []}, {:int_type}}} =
             verdict("mod M\n  macro T\n    syntax tt becomes true\n  fn f() -> Int = tt\n")
  end
end
```

- [ ] **Step 2: Prove the firewall has teeth (negative control, red-first)**

Before trusting the green suite, demonstrate the test would CATCH a bypass. Temporarily add this throwaway test to the file, run it, confirm it FAILS, then delete it (it is a scaffold, not part of the committed suite):

```elixir
  # THROWAWAY — delete after confirming it fails. Simulates a "bypass" where the
  # macro program were NOT elaborated (verdict forced to :accept regardless).
  # If verdict-equality had no teeth, this would pass; it must fail on the
  # ill-typed pair, proving the real tests detect an un-elaborated expansion.
  test "NEGATIVE CONTROL (delete me)" do
    bypass = fn _src -> :accept end
    hand = verdict("mod M\n  fn f() -> Int = true\n")   # {:reject, {:conversion_failure, ...}}
    assert bypass.("...") == hand                        # :accept == {:reject,...} -> FAILS
  end
```

Run: `mix test test/cure/elab/macro_expansion_soundness_test.exs`
Expected: the NEGATIVE CONTROL test FAILS (`:accept` ≠ `{:reject, {:conversion_failure, …}}`); all six real tests PASS. This is the red evidence that the equality assertions are non-trivial. **Then delete the NEGATIVE CONTROL test.**

- [ ] **Step 3: Run the committed test file — expect all green**

Run: `mix test test/cure/elab/macro_expansion_soundness_test.exs`
Expected: 6 passed (4 verdict-equality + accept-sense + reject-sense), 0 failures, negative control removed.

- [ ] **Step 4: Confirm zero production delta**

Run: `git -C . status --porcelain`
Expected: the ONLY change is the new untracked `test/cure/elab/macro_expansion_soundness_test.exs`. No `lib/**` file modified. (If any `lib/**` changed, the task was mis-executed — revert and reassess: this task is test-only by construction.)

- [ ] **Step 5: Full suite — no regression**

Run: `mix test` (once, alone). Expected: green at the milestone-2 baseline (4099, per commit `c835de1`) + the 6 new tests in this file = ~4105 passed (exact count may drift slightly with unrelated concurrent work; treat `~` as approximate), antigen coverage intact. Confirm `test/antigen/seeds.sexp` and `corpus.sexp` are untouched.

- [ ] **Step 6: Commit**

```bash
git add -- test/cure/elab/macro_expansion_soundness_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "test(macros): soundness firewall — macro expansion elaborated identically to hand-written (SP1 T8)"
```

---

### Task 2: Transitional classic-pipeline soundness firewall

**Files:**
- Create: `test/cure/compiler/macro_expansion_classic_soundness_test.exs`

**Interfaces:**
- Consumes: `Cure.Compiler.compile_string/2` — `{:ok, module_atom, forms} | {:error, term()}` (the CLI/`cure build` entry). Accept is a **3-tuple** `{:ok, _mod, _forms}`, NOT `{:ok, _}`.
- Produces: a test module. **Transitional:** delete this file when the classic-pipeline-deletion initiative removes `Cure.Types.Checker`/classic `Codegen`. The file header must say so.

**Why line-stripping:** classic error terms embed `[line: N]` (verified: `bad` → `{:type_error, [{:unbound_variable, "undefined variable 'nonexistent_thing'", [line: 3]}]}`; the macro version sits on the template's line). Macro vs hand-written verdicts are equal only after stripping `:line`/`:col` — confirmed live that all four pairs are then `equal=true`.

- [ ] **Step 1: Write the classic-pipeline firewall test file**

```elixir
# test/cure/compiler/macro_expansion_classic_soundness_test.exs
defmodule Cure.Compiler.MacroExpansionClassicSoundnessTest do
  # TRANSITIONAL SOUNDNESS FIREWALL for the CLASSIC pipeline entry that
  # `cure build`/the CLI actually calls (`Cure.Compiler.compile_string/2`) on
  # non-dependent macro-using programs. Same property as the dependent firewall
  # (`test/cure/elab/macro_expansion_soundness_test.exs`): a macro's expansion
  # is type-checked identically to hand-written code — verdict-equality, here
  # with `[line:/col:]` metadata stripped since the classic error vocabulary is
  # position-bearing. DELETE THIS FILE when the classic-pipeline-deletion
  # initiative removes Cure.Types.Checker + classic Codegen; the dependent
  # firewall is the permanent guard.
  use ExUnit.Case, async: true
  alias Cure.Compiler

  # Recursively drop :line/:col pairs so macro (template-line) and hand-written
  # (source-line) verdicts compare equal. Leaves every other term shape intact.
  defp strip(t) when is_list(t) do
    t |> Enum.reject(&match?({k, _} when k in [:line, :col], &1)) |> Enum.map(&strip/1)
  end

  defp strip(t) when is_tuple(t),
    do: t |> Tuple.to_list() |> Enum.map(&strip/1) |> List.to_tuple()

  defp strip(t), do: t

  defp verdict(src) do
    case Compiler.compile_string(src, []) do
      {:ok, _mod, _forms} -> :accept
      {:error, term} -> {:reject, strip(term)}
    end
  end

  @cases [
    {"zero-hole accept: zero => 0",
     "mod M\n  macro Zero\n    syntax zero becomes 0\n  fn f() -> Int = zero\n",
     "mod M\n  fn f() -> Int = 0\n"},
    {"one-hole accept: inc <x> => x + 1",
     "mod M\n  macro Inc\n    syntax inc <x: Code> becomes x + 1\n  fn f(n: Int) -> Int = inc n\n",
     "mod M\n  fn f(n: Int) -> Int = n + 1\n"},
    {"reject (unbound var): bad => nonexistent_thing",
     "mod M\n  macro Bad\n    syntax bad becomes nonexistent_thing\n  fn f() -> Int = bad\n",
     "mod M\n  fn f() -> Int = nonexistent_thing\n"},
    {"reject (type mismatch): tt => true used as Int",
     "mod M\n  macro T\n    syntax tt becomes true\n  fn f() -> Int = tt\n",
     "mod M\n  fn f() -> Int = true\n"}
  ]

  for {label, macro_src, hand_src} <- @cases do
    test "classic macro verdict equals hand-written verdict — #{label}" do
      assert verdict(unquote(macro_src)) == verdict(unquote(hand_src))
    end
  end

  test "the two well-typed cases genuinely accept (classic)" do
    assert verdict("mod M\n  macro Zero\n    syntax zero becomes 0\n  fn f() -> Int = zero\n") == :accept
    assert verdict("mod M\n  macro Inc\n    syntax inc <x: Code> becomes x + 1\n  fn f(n: Int) -> Int = inc n\n") == :accept
  end

  test "the two ill-typed cases genuinely reject (classic)" do
    assert {:reject, _} = verdict("mod M\n  macro Bad\n    syntax bad becomes nonexistent_thing\n  fn f() -> Int = bad\n")
    assert {:reject, _} = verdict("mod M\n  macro T\n    syntax tt becomes true\n  fn f() -> Int = tt\n")
  end
end
```

- [ ] **Step 2: Prove teeth (negative control, red-first) — then delete**

Add a throwaway that forces the macro side to `:accept`; run, confirm it FAILS on an ill-typed pair (proving the equality is non-trivial), then delete it:

```elixir
  test "NEGATIVE CONTROL classic (delete me)" do
    hand = verdict("mod M\n  fn f() -> Int = true\n")   # {:reject, {:type_error, ...}}
    assert :accept == hand                               # FAILS
  end
```

Run: `mix test test/cure/compiler/macro_expansion_classic_soundness_test.exs` → NEGATIVE CONTROL fails, all 6 real tests pass. **Delete the negative control.**

- [ ] **Step 3: Run the committed file — expect 6 green**

Run: `mix test test/cure/compiler/macro_expansion_classic_soundness_test.exs` → 6 passed.

- [ ] **Step 4: Confirm zero production delta**

`git status --porcelain` shows ONLY the two new untracked test files (Task 1's + Task 2's). No `lib/**` change.

- [ ] **Step 5: Commit**

```bash
git add -- test/cure/compiler/macro_expansion_classic_soundness_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "test(macros): transitional classic-pipeline soundness firewall (SP1 T8)"
```

---

## Task boundary + what remains in SP1

T8 locks the DONE-criterion clause **"expands to well-typed Core"** with a permanent guard: macro output is proven indistinguishable from hand-written code at the elaborator, so it cannot smuggle an ill-typed (or well-formed-but-mistyped) term past the kernel — **for callers of `Program.elaborate/1`**. SP3's generative expansion proof will *fuzz* this same `Program.elaborate` primitive across randomly-generated use-sites; T8 is the hand-picked, position-exact anchor that fuzzing generalizes.

**Gap surfaced by review — RESOLVED here by Task 2 (driver decision, recorded in prose per project convention):** `cure build`/the CLI compiles via `Cure.Compiler.compile_string/2`, which for non-dependent programs (verified: all four examples classify as non-dependent per `Program.dependent?/1`) type-checks through the classic `Cure.Types.Checker.check_module/2` + `Cure.Compiler.Codegen.compile_module/2`, never touching `Program.elaborate/1`. Task 1 alone therefore does not firewall the classic-pipeline route `cure build` actually takes for these programs today. **Decision:** firewall BOTH entry points. Task 1 guards the dependent `Program.elaborate/1` path (the permanent guard — this is the "well-typed Core" path the DONE criterion names, and it survives the classic-pipeline rip-out). Task 2 adds a **transitional** classic-pipeline firewall via `compile_string/2` (line-stripped verdict-equality — confirmed live that the property holds there too, all four `equal=true`). Task 2 is explicitly marked to be deleted alongside the classic pipeline when the classic-pipeline-deletion initiative lands; until then it gives `cure build` real regression protection. Both tasks are test-only (zero production delta). Rationale for doing both rather than accepting the gap: cheap, zero-risk, and it closes the "a user's macro run via `cure build` is soundness-guarded" hole in the DONE criterion's spirit today; rationale for keeping Task 1 as the permanent one: the DONE criterion says "Core," which only the dependent path produces.

**Remaining SP1 tasks** (subsequent Stage-2 rounds, in priority order):
- **T7 — hygiene:** `<fresh Name>` gensym in templates + capture-avoidance, so a template-introduced binder cannot capture a use-site name and vice-versa. Milestone-2 expansion is deliberately unhygienic; T7 makes name-binding templates safe. Needs its own grounding (a template-binder example, a capture repro) and its own plan `…-sp1d-plan.md`. This is a real red-green feature (capture repro → red → gensym fix → green).
- **T4 — `literal` rules + numeric-suffix lexer** (`500ms`): the one lexer change; also unblocks bounded hole+literal segment matching.
- **T9 — cross-module (imported) macros + import scoping + same-keyword conflict; two-pass name resolution.**

When T7/T4/T9 are executed + code-reviewed, run SP1's own Stage 6 (full `mix test`), update the state file, and start **SP2** (Tier 3 + the self-proving typed-error obligations). The end-to-end DONE proof ("its expansion runs") is a final integration step after SP3.
