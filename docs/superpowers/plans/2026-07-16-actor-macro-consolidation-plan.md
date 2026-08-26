# Actor-macro consolidation (Stage 1: actor) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Collapse `Std.Actor`'s two expander entry points into one, templatize the fixed-parameter GenServer callbacks with `quote`, and give the structured surface the extra-declarations body passthrough that only the legacy templates had — all byte-identical to today's output.

**Architecture:** `Std.Actor` currently has three expansion surfaces (Gen A `becomes` templates, Gen B `derive` shorthand via `derive_actor`, Gen C structured family via `derive_actor_family`) funnelling into one backend pair `emit_actor_parts`/`emit_actor_call_parts`. This plan (a) rewrites `derive_actor` as a thin adapter that builds an `ActorDefinitionSyntax` and delegates to `derive_actor_family`, deleting the `emit_actor`/`emit_actor_call` wrappers; (b) rewrites the four fixed-parameter callbacks in both emitters as `quote (fn … = $(body))` templates; (c) adds an `optional body Declarations` family field threaded into the generated module. The `becomes` templates (Gen A) and whole-module `quote` are **out of scope for this run** (see Deferred).

**Tech Stack:** Cure stdlib (`lib/std/actor.cure`); Elixir/ExUnit host tests; the SP5.1 `quote`/`$()` quasiquotation surface; the BEAM-SHA256 golden harness.

## Global Constraints

_Every task's requirements implicitly include this section. Values copied verbatim from the spec (`docs/superpowers/specs/macros/2026-07-16-actor-macro-consolidation-design.md`) and the standing operator directives._

- **TCB delta: zero.** No change to `lib/cure/core/*`. This run touches only `lib/std/actor.cure` and test files. (The optional parser step 1c that the spec places in the P-layer is **deferred**, so no P-layer change occurs here either.)
- **Author stdlib in `lib/std/`, never `priv/std/`** (`priv/std` is a generated bundle).
- **Ghost-writer commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`. NO `Co-Authored-By`, no Claude signature.
- **Explicit-pathspec staging only:** `git add -- <path>` / `git commit -- <path>`. NEVER `git add -A` / `git add .` (a concurrent agent may share the worktree).
- **One `mix` build at a time.** Never run two `mix` suites concurrently (a past concurrent full-suite run caused a kernel panic). Prefer scoped `mix test <file>`; run the full suite once, alone, at the Stage-6 gate.
- **The byte-identical goldens are immutable and must NOT be re-blessed in this run.** `test/cure/compiler/actor_quote_golden_test.exs` (`GDerived`, `GStructuredCall`, `GLifecycle`, `GFsmDerived`, `GSup`, `GApp`) and the 19 behavioral tests in `test/cure/compiler/actor_computed_test.exs` are the anti-regression spine. If any golden SHA diverges, STOP and report per the autopilot Halt protocol — do not edit the expected SHA.
- **Every command runs from inside the worktree** `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/actor-macro-consolidation` (cited as `<worktree>` below).

## Empirical grounding (already verified on this branch)

Before this plan was written, each risky premise was probed live (edit → run goldens → revert), so no task below rests on an unverified assumption:

- **Task 1 fold is byte-identical.** Rewriting `derive_actor` to build an `ActorDefinitionSyntax` and delegate to `derive_actor_family` (deleting `emit_actor`/`emit_actor_call`) kept all 6 goldens **and** all 19 behavioral tests green. `ActorDefinitionSyntax{…}` is constructible from ordinary Cure; the family's empty-meta match reconstruction produces identical BEAM (source position does not reach the SHA).
- **Task 2 callback templatization is byte-identical.** Replacing `function("handle_cast", …)` with `quote (fn handle_cast(message: Message, state: State) -> Effect(Tuple(Atom, State)) = $(handler_body))` kept all 6 goldens green. `quote (fn …)` ≡ the `function(…)` builder, and source `Tuple(Atom, State)` ≡ the builder's `tuple_type([...])` in codegen.
- **Task 3 `Declarations` is a valid family shape.** `lib/cure/compiler/macro_family.ex` `shape_type/1` lists `"Declarations"` → `DeclarationsSyntax`, so `optional body Declarations` parses.
- **Gen A parity target for Task 3:** the legacy `with`/bare-body templates (`lib/std/actor.cure` ~222–270) place the user's `body` declarations **inside** the generated GenServer module (after `start_link`). Task 3 must therefore append extra declarations into `gen_server_module`'s declaration list, not the enclosing block.

## File Structure

- **`lib/std/actor.cure`** — the only production file changed. Tasks 1–3 all edit it.
  - Task 1: `derive_actor` (~320) rewritten; new helper `derive_cases`; `emit_actor` (~393) and `emit_actor_call` (~416) deleted.
  - Task 2: `emit_actor_parts` (~396) and `emit_actor_call_parts` (~419) — four callbacks each become `quote` templates.
  - Task 3: `ActorDefinition` family (~10–19) gains `optional body Declarations`; `derive_actor_family` (~23), `emit_actor_parts`, `emit_actor_call_parts`, and the Task-1 adapter thread `extra_declarations`.
- **`test/cure/compiler/actor_computed_test.exs`** — Task 3 appends **one** new behavioral test (body passthrough). The existing 19 tests are immutable.
- **`test/cure/compiler/actor_quote_golden_test.exs`** — never edited; it is the characterization guard run after each task.

## Testing discipline note (read before executing)

Tasks 1 and 2 are **behavior-preserving refactors**, verified against the existing immutable goldens and 19 behavioral tests (characterization tests). They add no new behavior, so there is deliberately **no new red test** for them — the "red→green" they must satisfy is "the whole golden + behavioral set was green before the edit and is byte-identical green after." Each records the baseline-green run before editing and the still-green run after. Task 3 adds new behavior (`body` passthrough) and follows **strict red-green**: a failing test first, then the minimal change to pass it. The new test written in Task 3 Step 1 is, once it exists, **immutable in the same sense as the pre-existing 19**: Steps 3–7 must turn it green by editing `lib/std/actor.cure` only, never by weakening or rewriting the test itself. The sole exception is discovering the test asserts genuinely wrong behavior — in that case the implementer must first state why the test is wrong before touching it, not edit it to match whatever the code currently does.

---

### Task 1: Fold `derive_actor` into `derive_actor_family`; delete the wrappers

**Files:**
- Modify: `lib/std/actor.cure` — `derive_actor` (~line 320), delete `emit_actor` (~393–394) and `emit_actor_call` (~416–417); add helper `derive_cases`.
- Characterization guard: `test/cure/compiler/actor_quote_golden_test.exs`, `test/cure/compiler/actor_computed_test.exs` (both immutable).

**Interfaces:**
- Consumes: `derive_actor_family(name: ModuleNameSyntax, definition: ActorDefinitionSyntax) -> Syntax` (existing, ~line 23); the auto-generated capture record `ActorSyntax` with fields `.name`, `.state_type`, `.cast_body`, `.call_body` (produced by the `derive` rule's `computed by derive_actor`); the auto-generated `ActorDefinitionSyntax` record with fields `state, messages, initial, init, on_cast, on_call, on_info, terminate, code_change`; `children/1`, `Node/3`, `Raw/1`, `SOpaque`, `Some/1`, `None/0`.
- Produces: `derive_actor(input: ActorSyntax) -> Syntax` (same name/signature, still the `computed by derive_actor` target — the `derive` rule at ~line 75 is unchanged); `derive_cases(body: Syntax) -> Syntax`.

**Note on `ActorSyntax`:** it is **not** retired. It is auto-generated by the `computed by derive_actor` rule from that rule's holes; `derive_actor` still receives it and now merely adapts it into an `ActorDefinitionSyntax`. Only `emit_actor`/`emit_actor_call` are deleted.

- [ ] **Step 1: Record the baseline-green characterization run**

Run: `cd <worktree> && mix test test/cure/compiler/actor_quote_golden_test.exs test/cure/compiler/actor_computed_test.exs`
Expected: PASS — `6 passed` (goldens) and `19 passed` (behavioral). This is the invariant Task 1 must preserve.

- [ ] **Step 2: Rewrite `derive_actor` as an adapter and add `derive_cases`**

Replace the whole `derive_actor` function body (currently the `let module_name … / let module_expr … / match derive_pattern_heads(input.cast_body) …` form) with:

```cure
  fn derive_actor(input: ActorSyntax) -> Syntax =
    let on_call = match input.call_body
      Raw(_) -> None()
      value -> Some(derive_cases(value))
    let definition = ActorDefinitionSyntax{state: input.state_type, messages: None(), initial: None(), init: None(), on_cast: derive_cases(input.cast_body), on_call: on_call, on_info: None(), terminate: None(), code_change: None()}
    derive_actor_family(input.name, definition)

  fn derive_cases(body: Syntax) -> Syntax = match children(body)
    [_scrutinee | arms] -> Node(:cases, [], arms)
    _ -> Node(:cases, [], [])
```

Why `derive_cases`: `input.cast_body`/`input.call_body` are full `:pattern_match` nodes (scrutinee + arms). The family expects each `Cases` field's `children` to be **arms only** — it re-prepends `variable("message")`/`variable("request")` itself. `derive_cases` drops the scrutinee.

- [ ] **Step 3: Delete the `emit_actor` wrapper**

Remove:

```cure
  fn emit_actor(input: ActorSyntax, module_name: SynLit, module_expr: Syntax, heads: List(Syntax)) -> Syntax =
    emit_actor_parts(module_name, module_expr, input.state_type, default_actor_init(input.state_type), variable("ActorMessage"), [enum_type("ActorMessage", heads)], input.cast_body, Raw(SOpaque), Raw(SOpaque), Raw(SOpaque), heads)
```

- [ ] **Step 4: Delete the `emit_actor_call` wrapper**

Remove:

```cure
  fn emit_actor_call(input: ActorSyntax, module_name: SynLit, module_expr: Syntax, message_heads: List(Syntax), request_heads: List(Syntax), reply_type: Syntax) -> Syntax =
    emit_actor_call_parts(module_name, module_expr, input.state_type, default_actor_init(input.state_type), variable("ActorMessage"), [enum_type("ActorMessage", message_heads)], input.cast_body, input.call_body, Raw(SOpaque), Raw(SOpaque), Raw(SOpaque), message_heads, request_heads, reply_type)
```

(After Steps 3–4 the sole callers of `emit_actor_parts`/`emit_actor_call_parts` are the two call sites inside `derive_actor_family`.)

- [ ] **Step 5: Run the characterization guard**

Run: `cd <worktree> && mix test test/cure/compiler/actor_quote_golden_test.exs test/cure/compiler/actor_computed_test.exs`
Expected: PASS — `6 passed` and `19 passed`, byte-identical. If any golden SHA diverges: STOP and report (Halt protocol). Do NOT edit an expected SHA.

- [ ] **Step 6: Commit**

```bash
cd <worktree>
git add -- lib/std/actor.cure
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "refactor(std): fold derive_actor into derive_actor_family"
```

---

### Task 2: Templatize the four fixed-parameter callbacks in both emitters

**Files:**
- Modify: `lib/std/actor.cure` — `emit_actor_parts` (~396) and `emit_actor_call_parts` (~419).
- Characterization guard: `test/cure/compiler/actor_quote_golden_test.exs` (immutable) **and** `test/cure/compiler/actor_computed_test.exs` (immutable) — both emitters are also the backend the `derive` surface (Task 1's `derive_actor` adapter) routes through, so the 19 behavioral tests exercise the same four callbacks this task templatizes; the golden fixtures alone don't cover every edge case those 19 tests pin (guarded-head rejection, catch-all rejection, typed payload, multi-arm call, etc.). Bookend the task with both files (Steps 1 and 7); the intermediate Steps 3 and 5 may stay golden-only for fast iteration.

**Interfaces:**
- Consumes: the `quote`/`$()` surface; the local bindings already computed in each emitter (`handler_body`/`cast_body`, `info_handler`, `terminate_handler`, `code_change_handler`).
- Produces: no signature change; the four callbacks are emitted via `quote` instead of `function(…)`.

**Scope boundary:** Only the four **fixed-parameter** callbacks become templates: `handle_cast`, `handle_info`, `terminate`, `code_change`. `init`, `handle_call`, and `start_link` KEEP their `function(…)` builder calls — their parameters are dynamic (`init_spec.parameter`, `init_spec.start_parameters`), linear (`parameter_linear("from", …)`), or dependently typed (`Reply(reply_type)`), which the literal-parameter template form cannot express. Do not attempt to templatize those three in this run.

- [ ] **Step 1: Record the baseline-green characterization run**

Run: `cd <worktree> && mix test test/cure/compiler/actor_quote_golden_test.exs test/cure/compiler/actor_computed_test.exs`
Expected: PASS — `6 passed` (goldens) and `19 passed` (behavioral). This is the invariant Task 2 must preserve.

- [ ] **Step 2: Templatize `handle_cast` and `handle_info` in `emit_actor_parts`**

In `emit_actor_parts`, inside the `gen_server_module(module_name, state_type, [ … ])` declaration list, replace these two lines:

```cure
            function("handle_cast", [parameter("message", variable("Message")), parameter("state", variable("State"))], result_type, handler_body),
            function("handle_info", [parameter("message", variable("Message")), parameter("state", variable("State"))], result_type, info_handler),
```

with:

```cure
            quote (fn handle_cast(message: Message, state: State) -> Effect(Tuple(Atom, State)) = $(handler_body)),
            quote (fn handle_info(message: Message, state: State) -> Effect(Tuple(Atom, State)) = $(info_handler)),
```

- [ ] **Step 3: Run the golden guard for `emit_actor_parts` so far**

Run: `cd <worktree> && mix test test/cure/compiler/actor_quote_golden_test.exs`
Expected: PASS — `6 passed`, byte-identical. If a SHA diverges, STOP and report.

- [ ] **Step 4: Templatize `terminate` and `code_change` in `emit_actor_parts`**

Replace:

```cure
            function("terminate", [parameter("reason", variable("Atom")), parameter("state", variable("State"))], call("Effect", [variable("Atom")]), terminate_handler),
            function("code_change", [parameter("old", variable("Atom")), parameter("state", variable("State")), parameter("extra", variable("Atom"))], result_type, code_change_handler),
```

with:

```cure
            quote (fn terminate(reason: Atom, state: State) -> Effect(Atom) = $(terminate_handler)),
            quote (fn code_change(old: Atom, state: State, extra: Atom) -> Effect(Tuple(Atom, State)) = $(code_change_handler)),
```

- [ ] **Step 5: Run the golden guard**

Run: `cd <worktree> && mix test test/cure/compiler/actor_quote_golden_test.exs`
Expected: PASS — `6 passed`, byte-identical.

- [ ] **Step 6: Templatize the same four callbacks in `emit_actor_call_parts`**

In `emit_actor_call_parts`, note the local shadow `let cast_body: Syntax = actor_handler(cast_body)` (the handler-wrapped body is bound to `cast_body`, not `handler_body`). Replace the four callback lines:

```cure
        function("handle_cast", [parameter("message", variable("Message")), parameter("state", variable("State"))], cast_result_type, cast_body),
        function("handle_info", [parameter("message", variable("Message")), parameter("state", variable("State"))], cast_result_type, info_handler),
        function("terminate", [parameter("reason", variable("Atom")), parameter("state", variable("State"))], call("Effect", [variable("Atom")]), terminate_handler),
        function("code_change", [parameter("old", variable("Atom")), parameter("state", variable("State")), parameter("extra", variable("Atom"))], cast_result_type, code_change_handler),
```

with:

```cure
        quote (fn handle_cast(message: Message, state: State) -> Effect(Tuple(Atom, State)) = $(cast_body)),
        quote (fn handle_info(message: Message, state: State) -> Effect(Tuple(Atom, State)) = $(info_handler)),
        quote (fn terminate(reason: Atom, state: State) -> Effect(Atom) = $(terminate_handler)),
        quote (fn code_change(old: Atom, state: State, extra: Atom) -> Effect(Tuple(Atom, State)) = $(code_change_handler)),
```

Leave `handle_call`, `init`, and `start_link` (and the `alias_node`/`request_type` lines) exactly as they are.

- [ ] **Step 7: Run the full characterization guard for both emitters**

Run: `cd <worktree> && mix test test/cure/compiler/actor_quote_golden_test.exs test/cure/compiler/actor_computed_test.exs`
Expected: PASS — `6 passed` (goldens byte-identical — this exercises `GStructuredCall`/`GLifecycle`, which hit `emit_actor_call_parts`) and `19 passed` (behavioral, byte-identical-in-effect — these route through the now-templatized `emit_actor_parts`/`emit_actor_call_parts` via Task 1's `derive_actor` adapter). If a golden SHA diverges, STOP and report; if a behavioral test regresses, STOP and report (Halt protocol) — do not weaken or edit the immutable test.

- [ ] **Step 8: Commit**

```bash
cd <worktree>
git add -- lib/std/actor.cure
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "refactor(std): templatize fixed-param actor callbacks with quote"
```

---

### Task 3: Body passthrough — `optional body Declarations` threaded into the generated module

**Files:**
- Modify: `lib/std/actor.cure` — `ActorDefinition` family (~10–19); `derive_actor_family` (~23); `emit_actor_parts` (~396); `emit_actor_call_parts` (~419); the Task-1 `derive_actor` adapter (add `body: None()`).
- Test: `test/cure/compiler/actor_computed_test.exs` — append one new test.
- Characterization guard: `test/cure/compiler/actor_quote_golden_test.exs` (no-body goldens must stay byte-identical) **and** the pre-existing 19 tests in `test/cure/compiler/actor_computed_test.exs` (must stay green alongside the new 20th test — see Step 9).

**Interfaces:**
- Consumes: the `Declarations` family shape → auto-generated field `body: Option(DeclarationsSyntax)` on `ActorDefinitionSyntax`; `children/1`; `append/2`; `Cure.Compiler.compile_and_load/2`.
- Produces: `emit_actor_parts(module_name, module_expr, state_type, init_spec, message_type, message_declarations, cast_body, info_body, terminate_body, code_change_body, heads, extra_declarations)` (new trailing param `extra_declarations: List(Syntax)`); `emit_actor_call_parts(…, request_heads, reply_type, extra_declarations)` (new trailing param); both append `extra_declarations` **inside** the `gen_server_module` declaration list (Gen A parity), after `start_link`.

- [ ] **Step 1: Write the failing behavioral test**

Append to `test/cure/compiler/actor_computed_test.exs` (before the final `end`):

```elixir
  test "structured actor threads a body declaration into the generated module" do
    source = """
    mod M
      use Std.Actor

      actor Cure.Generated.WithBody
        state Int
        on_cast
          Inc -> state + 1
        body
          fn bump(n: Int) -> Int = n + 1

    fn make_message() -> ActorMessage = Inc
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert module == :"Cure.M"
    assert apply(:"Cure.Generated.WithBody", :bump, [4]) == 5
    assert apply(:"Cure.Generated.WithBody", :handle_cast, [:Inc, 0]) == {:noreply, 1}
  end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `cd <worktree> && mix test test/cure/compiler/actor_computed_test.exs -k "threads a body declaration"`
Expected: FAIL — the `body` field is not part of the `ActorDefinition` family yet, so the source is rejected (unknown field / parse failure) and `compile_and_load` does not return `{:ok, _}`.

- [ ] **Step 3: Add the `body` field to the family**

In the `syntax family ActorDefinition` block, add a line after `optional code_change Code`:

```cure
      optional code_change Code
      optional body Declarations
```

- [ ] **Step 4: Extract `extra_declarations` in `derive_actor_family` and pass it through**

In `derive_actor_family`, add after the `let code_change_body = …` block (before `let init_spec = …`):

```cure
    let extra_declarations = match definition.body
      None() -> []
      Some(value) -> children(value)
```

Then add `extra_declarations` as the final argument to **both** emitter calls:

```cure
          NoCall -> emit_actor_parts(module_name, module_expr, definition.state, init_spec, message_type, message_declarations, body, info_body, terminate_body, code_change_body, heads, extra_declarations)
          InvalidCall(reason) -> Failure(reason, [])
          CallContract(request_heads, reply_type) -> emit_actor_call_parts(module_name, module_expr, definition.state, init_spec, message_type, message_declarations, body, call_body, info_body, terminate_body, code_change_body, heads, request_heads, reply_type, extra_declarations)
```

- [ ] **Step 5: Add the `body: None()` field to the Task-1 `derive_actor` adapter**

The `ActorDefinitionSyntax` record now has ten fields; the adapter must supply `body`. Update the `let definition = …` line in `derive_actor` to include `body: None()`:

```cure
    let definition = ActorDefinitionSyntax{state: input.state_type, messages: None(), initial: None(), init: None(), on_cast: derive_cases(input.cast_body), on_call: on_call, on_info: None(), terminate: None(), code_change: None(), body: None()}
```

- [ ] **Step 6: Thread `extra_declarations` into `emit_actor_parts`**

Add the trailing parameter to the signature and append it inside `gen_server_module`. Change the signature line to end with `, heads: List(Syntax), extra_declarations: List(Syntax)) -> Syntax =`, then wrap the `gen_server_module` declaration list with `append(…, extra_declarations)`:

```cure
        block(append(message_declarations, [
          gen_server_module(module_name, state_type, append([
            alias_node("Message", message_type),
            function("init", [init_spec.parameter], init_type, init_spec.body),
            quote (fn handle_cast(message: Message, state: State) -> Effect(Tuple(Atom, State)) = $(handler_body)),
            quote (fn handle_info(message: Message, state: State) -> Effect(Tuple(Atom, State)) = $(info_handler)),
            quote (fn terminate(reason: Atom, state: State) -> Effect(Atom) = $(terminate_handler)),
            quote (fn code_change(old: Atom, state: State, extra: Atom) -> Effect(Tuple(Atom, State)) = $(code_change_handler)),
            function("start_link", init_spec.start_parameters, start_type, call("Std.Otp.start_link", [module_expr, init_spec.start_argument]))
          ], extra_declarations))
        ]))
```

The only change in this step versus the post-Task-2 file is structural: the declaration list passed to `gen_server_module` is wrapped in `append([ … ], extra_declarations)`. `init` and `start_link` stay `function(…)` builder calls (Task 2 scope boundary); `handle_cast`/`handle_info`/`terminate`/`code_change` are already the Task-2 `quote` templates and are shown here only for context — do not re-edit them.

- [ ] **Step 7: Thread `extra_declarations` into `emit_actor_call_parts`**

Add `, extra_declarations: List(Syntax)` as the final parameter after `reply_type: Syntax`. Wrap that emitter's `gen_server_module` declaration list the same way as Step 6 — this needs **two** edits to the list passed to `gen_server_module`: insert `append(` immediately before its opening `[`, and change its closing `]` to `], extra_declarations)` immediately before the `)` that closes `gen_server_module(...)`. The post-Task-2 body reads:

```cure
    block(append(message_declarations, [
      request_type,
      gen_server_module(module_name, state_type, [
        alias_node("Message", message_type),
        alias_node("Request", variable("ActorRequest")),
        function("init", [init_spec.parameter], init_type, init_spec.body),
        function("handle_call", [parameter("request", variable("Request")), parameter_linear("from", call("Reply", [reply_type])), parameter("state", variable("State"))], cast_result_type, call_body),
        quote (fn handle_cast(message: Message, state: State) -> Effect(Tuple(Atom, State)) = $(cast_body)),
        quote (fn handle_info(message: Message, state: State) -> Effect(Tuple(Atom, State)) = $(info_handler)),
        quote (fn terminate(reason: Atom, state: State) -> Effect(Atom) = $(terminate_handler)),
        quote (fn code_change(old: Atom, state: State, extra: Atom) -> Effect(Tuple(Atom, State)) = $(code_change_handler)),
        function("start_link", init_spec.start_parameters, start_type, call("Std.Otp.start_link", [module_expr, init_spec.start_argument]))
      ])
    ]))
```

becomes:

```cure
    block(append(message_declarations, [
      request_type,
      gen_server_module(module_name, state_type, append([
        alias_node("Message", message_type),
        alias_node("Request", variable("ActorRequest")),
        function("init", [init_spec.parameter], init_type, init_spec.body),
        function("handle_call", [parameter("request", variable("Request")), parameter_linear("from", call("Reply", [reply_type])), parameter("state", variable("State"))], cast_result_type, call_body),
        quote (fn handle_cast(message: Message, state: State) -> Effect(Tuple(Atom, State)) = $(cast_body)),
        quote (fn handle_info(message: Message, state: State) -> Effect(Tuple(Atom, State)) = $(info_handler)),
        quote (fn terminate(reason: Atom, state: State) -> Effect(Atom) = $(terminate_handler)),
        quote (fn code_change(old: Atom, state: State, extra: Atom) -> Effect(Tuple(Atom, State)) = $(code_change_handler)),
        function("start_link", init_spec.start_parameters, start_type, call("Std.Otp.start_link", [module_expr, init_spec.start_argument]))
      ], extra_declarations))
    ]))
```

Do not touch `handle_call`, `init`, `alias_node`, or the outer `request_type` sibling. The extra `extra_declarations` argument must land on the list passed to `gen_server_module` (via `append`), not as a fourth positional argument to `gen_server_module` itself — `gen_server_module/3` takes exactly three parameters (see `lib/std/actor.cure:447`), so appending it anywhere else is an arity error.

- [ ] **Step 8: Run the new test to verify it passes**

Run: `cd <worktree> && mix test test/cure/compiler/actor_computed_test.exs -k "threads a body declaration"`
Expected: PASS — `bump/1` is exported by `Cure.Generated.WithBody` and `handle_cast(:Inc, 0) == {:noreply, 1}`.

- [ ] **Step 9: Run the full actor guard set (no-body paths unchanged)**

Run: `cd <worktree> && mix test test/cure/compiler/actor_quote_golden_test.exs test/cure/compiler/actor_computed_test.exs`
Expected: PASS — `6 passed` (goldens byte-identical: no-body actors emit an empty `extra_declarations = []`, so `append([...], [])` leaves the list unchanged) and `20 passed` (19 immutable + the new body test). If a golden SHA diverges, STOP and report.

- [ ] **Step 10: Commit**

```bash
cd <worktree>
git add -- lib/std/actor.cure test/cure/compiler/actor_computed_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(std): thread actor body declarations into the generated module"
```

---

## Deferred (not in this run — follow-up autopilot runs)

These spec steps are intentionally out of scope here; each is either optional infrastructure or carries migration risk unsuited to a hands-off run. The Stage-6 completion report must list them.

- **Spec 1c — whole-module `quote`.** A P-layer parser extension (indented declaration block + `$(decls ...)` group-splice). Optional infra; the spec explicitly allows deferring it. Belongs in its own run because it changes the parser (still zero-TCB, but a distinct surface with its own round-trip tests).
- **Spec 1e — terse shorthand + remove Gen A.** Re-expressing the 16 `becomes` templates as delegating forms and migrating the 12 demos (`examples/cure_motif/cure_src/{voice,sequencer,clock}.cure`, `cure_atelier/cure_src/{painter,curator}.cure`, `cure_colony/cure_src/{echo,worker}.cure`, `cure_forge/cure_src/{metrics,logger,queue,pool}.cure`, `vicure/test_syntax.cure`) then deleting the templates. This is the riskiest step (mechanism fork between keyword-alias vs thin adapter; a 12-file demo migration whose guard is each demo's own build), so it gets its own probe-first run.
- **Stage 2 (fsm/supervisor/app) and Stage 3 (Tier-3 typed macros).** Per the spec, replayed/added after the actor reference lands.

Consequence of deferring 1e: the Gen A `becomes` templates remain in `lib/std/actor.cure` alongside the folded `derive`/structured surfaces. That is expected — this run delivers "one expander" (Tasks 1) + the quasiquote elegance on the fixed-param backend (Task 2) + the body-passthrough capability (Task 3), not the template deletion.

## Self-Review

- **Spec coverage:** Spec §4 steps 1a (Task 1), 1b (Task 2, scoped to fixed-param callbacks), 1d (Task 3) are covered. Steps 1c and 1e are explicitly deferred with rationale (see Deferred). Stages 2–3 are out of scope per the spec's own sequencing.
- **Placeholder scan:** No "TBD"/"handle edge cases"/"similar to Task N" — every code step shows the exact Cure/Elixir to write.
- **Type consistency:** `derive_cases`, `emit_actor_parts`'s new `extra_declarations` param, and `ActorDefinitionSyntax`'s `body: None()` are named identically across Tasks 1 and 3. The Task-3 signature-change note (Produces block) matches the call-site edits in Step 4. `handler_body` (in `emit_actor_parts`) vs the shadowed `cast_body` (in `emit_actor_call_parts`) distinction is called out in Task 2 Step 6 so the splice targets the right binding.
- **Testing discipline:** Tasks 1–2 are characterization-guarded refactors (documented; no new red test because no new behavior); Task 3 is strict red-green with a named failing test. Goldens are immutable and never re-blessed.
