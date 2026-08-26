# Precedence Groups + Operator Overloading Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace Cure's hardcoded operator system with a declaration-driven Swift-style precedence-group system in which every overloadable operator — symbolic or word — desugars to a call to an ordinary overloaded function of the same name, resolved by the existing type-directed overload/coherence machinery.

**Architecture:** Three ordered, independently-shippable phases. Phase 1 moves typeclass-instance elaboration onto the kernel (whnf coherence key + kernel conversion for signature checks), a self-contained cleanup. Phase 2 expands the interface library (superinterfaces, minimal-basis `Equatable`/`Comparable`, arithmetic interfaces) and re-routes today's operator *elaboration* through it with no syntax change (differential oracle: identical evaluation). Phase 3 replaces the static precedence table with `precedencegroup`/`infix`/`prefix`/`postfix` declarations, moves the built-in operators into a preloaded `Std.Operators` module, and flips the parser so operators desugar to overloaded-name calls.

**Tech Stack:** Elixir (compiler in `lib/cure/`), Cure (stdlib in `lib/std/`), ExUnit. Kernel = `lib/cure/core/**` (the TCB). Elaborator = `lib/cure/elab/**`. Parser/lexer = `lib/cure/compiler/**`.

## Global Constraints

- **Zero TCB change.** `lib/cure/core/**` (kernel: `normalise.ex`, `conv.ex`, `kernel.ex`, `inductive.ex`, `builtins.ex`, `value.ex`, `eval.ex`, `quote.ex`) is not modified by any task. Phase 1 *calls into* existing kernel entry points (`Normalise.whnf_value/3`, `Conv.conv?/5`) but adds nothing to them. If a task appears to need a kernel change, stop and escalate.
- **Descriptive naming** (operator standing directive): spell names out in all new Cure code — `Equivalent` not `Eq`, `Additive`/`Multiplicative`/`Divisible`, `negate` not `neg`. Do not abbreviate.
- **Differential correctness for Phases 2–3.** No task in Phase 2 or 3 may change the *evaluation result* of any operator expression that compiles today. Each such task carries a differential test proving byte-identical behavior before/after.
- **One build/test run at a time.** Never launch concurrent `mix test` / full-suite runs (a past concurrent full-suite run caused a kernel panic). Serialize.
- **Full gate before declaring a phase done.** `mix test` green (the suite is ~75s per the suite-wallclock memory) plus the Antigen metatheory assays.
- **Author commits as the user only.** No `Co-Authored-By` / `Claude-Session` trailers on any commit.
- **OTP 26–28** for building Cure (unchanged; not exercised by these tasks but the environment constraint stands).

---

# Phase 1 — Kernel-routed instance elaboration

**Deliverable:** `Cure.Elab.Implementation` computes the coherence key by whnf-ing the elaborated Core head and checks method signatures via kernel conversion; `normalize_head`, `head_atom`, `check_method_signature`, `alpha_equal?`, `alpha`, `alpha_name`, `type_var?` are deleted. Existing typeclass suites stay green; two new regression tests pin the whnf-key and the conversion-based signature check.

**Key files (from exploration):**
- `lib/cure/elab/implementation.ex` — `register/2` (lines 30–51); `normalize_head/2,3` (66–80) + `head_atom/4` (82–87) to delete; `check_method_signature/5` (172–187) + `alpha_equal?/2` (193) + `alpha/3` (195–221) + `alpha_name/3` (223–242) + `type_var?/1` (246–247) to delete; `subst_head/3` (283–298) and `default_fn_def/4` (255–275) stay.
- `lib/cure/elab/declarations.ex` — `lower_type/3` (line 1840): `lower_type(ast, scope, env) :: {:ok, core_term} | {:error, reason}`.
- `lib/cure/core/normalise.ex` — `whnf_value(value, sig, opts \\ [])` (line 56), returns a Value; `whnf/3` (line 26) returns a read-back Term.
- `lib/cure/core/eval.ex` — `Eval.eval(term, value_env)` produces a Value (`Eval.eval(core_ty, [])` for a closed head).
- `lib/cure/core/conv.ex` — `conv?(t1, t2, value_env, depth, sig \\ nil) :: boolean()` (line 49); `conv_values?(v1, v2, depth, sig \\ nil) :: boolean()` (line 56).
- Value head shapes (`lib/cure/core/value.ex` 56–74): `{:vint_type}`, `{:vfloat_type}`, `{:vbinary_type}`, `{:vatom_type}`, `{:vdata, name, args}`, `{:vneutral, {:nglobal, name}}`. **No `:vstring_type`** — `String` is `{:vdata, :String, _}`.
- Interface descriptor (`lib/cure/elab/interface.ex` 36–43): `%{name, head_var, head_kind, methods, method_order, defaults}`; `desc.methods[m] = %{name, params, return_type, type_ast}`; `desc.head_var` is a string like `"a"`.

## Task 1.1: Whnf-computed coherence key (retire `normalize_head`)

**Files:**
- Modify: `lib/cure/elab/implementation.ex` — `register/2` head computation (line 32); delete `normalize_head/2` (66), `normalize_head/3` (68–80), `head_atom/4` (82–87).
- Test: `test/cure/elab/instance_whnf_key_test.exs` (create).

**Interfaces:**
- Consumes: `Cure.Elab.Declarations.lower_type/3`, `Cure.Core.Eval.eval/2`, `Cure.Core.Normalise.whnf_value/3`.
- Produces: `head_key(for_type_ast, env) :: atom()` — the coherence key atom, replacing `meta[:for] |> String.to_atom() |> normalize_head(env)`.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/elab/instance_whnf_key_test.exs
defmodule Cure.Elab.InstanceWhnfKeyTest do
  @moduledoc """
  Phase 1: the coherence key of an instance head is computed by whnf-ing the
  elaborated Core head, so a transparent type synonym files under the same key
  as the type it unfolds to (via the kernel's δ-reduction, not surface spelling).
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  test "an instance for a transparent synonym collides with the underlying type" do
    src = """
    mod M
      use Std.Equatable
      typealias MyInt = Int
      implementation Equatable for MyInt
        fn eq(a: MyInt, b: MyInt) -> Bool = Std.Builtin.int_eq(a, b)
    end
    """

    # Std.Equatable already provides `Equatable for Int`. Registering a second
    # anonymous instance for `MyInt` (which whnf's to Int) must collide.
    assert {:error, {:overlapping_instance, :Equatable, :Int}} = Program.elaborate(src)
  end

  test "an instance for a genuine data type registers under its family name" do
    src = """
    mod M
      use Std.Equatable
      type Color = Red | Green | Blue
      implementation Equatable for Color
        fn eq(a: Color, b: Color) -> Bool = Std.Builtin.struct_eq(Color, a, b)
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end
```

- [ ] **Step 2: Run it to confirm it fails**

Run: `mix test test/cure/elab/instance_whnf_key_test.exs`
Expected: the first test FAILS — today `MyInt` keys under the atom `:MyInt` (its surface spelling is only unfolded through `normalize_head`'s def-lookup path, which handles a `typealias` but via a separate mechanism), and `Std.Builtin.int_eq` is not yet callable (Task 2.1) — so this test also depends on Task 2.1's fix. **Sequencing note:** if `Std.Builtin.int_eq` resolution is not yet in place, temporarily use `a == b` as the body to isolate the key behavior, then restore the primitive spelling after Task 2.1. Record which form was used.

- [ ] **Step 3: Add the `head_key/2` helper**

Add to `implementation.ex` (near the old `normalize_head`):

```elixir
  # The coherence key: elaborate the instance head to a Core type, whnf it, and
  # read the head constructor's canonical name. Transparent synonyms unfold via
  # the kernel's δ-reduction of certified globals, so `MyInt = Int` keys as `:Int`.
  defp head_key(for_type_ast, env) do
    with {:ok, core_ty} <- Declarations.lower_type(for_type_ast, [], env) do
      core_ty
      |> Cure.Core.Eval.eval([])
      |> Cure.Core.Normalise.whnf_value(env, [])
      |> whnf_head_atom()
    else
      _ -> :error_head
    end
  end

  defp whnf_head_atom({:vint_type}), do: :Int
  defp whnf_head_atom({:vfloat_type}), do: :Float
  defp whnf_head_atom({:vbinary_type}), do: :Binary
  defp whnf_head_atom({:vatom_type}), do: :Atom
  defp whnf_head_atom({:vdata, name, _args}), do: name
  # A stuck global (uncertified / open synonym) falls back to its own name — the
  # same behavior the old `head_atom` fallback gave.
  defp whnf_head_atom({:vneutral, {:nglobal, name}}), do: name
  defp whnf_head_atom(other), do: other
```

Add `alias Cure.Elab.Declarations` if not already aliased (it is aliased at line 20: `alias Cure.Elab.{Coherence, Declarations, Resolve}`).

- [ ] **Step 4: Rewire `register/2` to use `head_key/2`**

In `register/2`, replace line 32:

```elixir
    head = meta |> Keyword.fetch!(:for) |> String.to_atom() |> normalize_head(env)
```

with:

```elixir
    head = head_key(Keyword.fetch!(meta, :for_type), env)
```

(`meta[:for_type]` is the surface AST of the head; `meta[:for]` remains available but is no longer the key source.)

- [ ] **Step 5: Delete the retired code**

Delete `normalize_head/2` (line 66), `normalize_head/3` (lines 68–80), and `head_atom/4` (lines 82–87), plus their doc comment (lines 53–65). Remove the now-unused `Inductive` alias reference if `head_key` doesn't use it — check `alias Cure.Core.{Env, Inductive}` at line 19; `Inductive` may still be used elsewhere, so only drop it if grep shows no other use in the file.

- [ ] **Step 6: Run the new test + the existing coherence suites**

Run: `mix test test/cure/elab/instance_whnf_key_test.exs`
Expected: PASS (both tests).

Run: `mix test test/cure/elab/` (the elaborator suite, including anonymous-instance and coherence tests)
Expected: PASS — no regression. If any instance suite that relied on surface-spelling keys breaks, that is a real semantic difference to investigate, not a test to edit.

- [ ] **Step 7: Commit**

```bash
git add lib/cure/elab/implementation.ex test/cure/elab/instance_whnf_key_test.exs
git commit -m "feat(coherence): compute instance key by whnf-ing the elaborated head"
```

## Task 1.2: Signature conformance via kernel conversion (retire `check_method_signature`/`alpha_equal?`)

**Files:**
- Modify: `lib/cure/elab/implementation.ex` — `check_method_signature/5` (172–187) replaced by a kernel-conversion check; delete `alpha_equal?/2` (193), `alpha/3` (195–221), `alpha_name/3` (223–242), `type_var?/1` (246–247), `param_type/1` if unused after (189).
- Test: `test/cure/elab/instance_signature_conversion_test.exs` (create).

**Interfaces:**
- Consumes: `Declarations.lower_type/3`, `Cure.Core.Conv.conv?/5`, `desc.methods[m].type_ast` (the interface method's full function-type surface AST), `desc.head_var`, `subst_head/3` (existing, lines 283–298).
- Produces: `check_method_signature(desc, iface, method, for_type, fn_decl, origin) :: :ok | {:error, {:method_signature_mismatch, iface, method}}` — same name/arity, kernel-backed body.

**Approach (why conversion works here):** The interface method's declared type (`desc.methods[m].type_ast`, e.g. `a -> a -> Bool`) with `head_var` substituted by `for_type` gives the *expected* Pi type; the instance clause's own params+return give the *actual* Pi type. Both are elaborated to closed Core Pi types with `lower_type/3` and compared with `Conv.conv?/5`. Kernel conversion is up-to-α and up-to-δ by construction, so it subsumes the hand-rolled `alpha_equal?` (including `fmap`'s `a`/`b` renaming: the method's other type variables become bound Π domains, and conversion of two Π types alpha-varies them automatically). Method type variables other than the head are already universally bound in `type_ast`; `lower_type` lowers them to bound `{:var, idx}` de Bruijn indices, and conversion matches them positionally.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/elab/instance_signature_conversion_test.exs
defmodule Cure.Elab.InstanceSignatureConversionTest do
  @moduledoc """
  Phase 1: an instance method whose type does not match the interface's
  (head-substituted) signature is rejected by kernel conversion with a
  `:method_signature_mismatch` sited at the implementation.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  test "a mismatched return type is rejected at the implementation" do
    src = """
    mod M
      use Std.Equatable
      type Color = Red | Green | Blue
      implementation Equatable for Color
        fn eq(a: Color, b: Color) -> Color = a
    end
    """

    assert {:error, {:method_signature_mismatch, :Equatable, :eq}} = Program.elaborate(src)
  end

  test "a correctly-typed instance passes conversion" do
    src = """
    mod M
      use Std.Equatable
      type Color = Red | Green | Blue
      implementation Equatable for Color
        fn eq(a: Color, b: Color) -> Bool = Std.Builtin.struct_eq(Color, a, b)
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end
```

- [ ] **Step 2: Run it to confirm it fails as expected**

Run: `mix test test/cure/elab/instance_signature_conversion_test.exs`
Expected: the first test currently PASSES already via the surface `alpha_equal?` path (a `Color` return where `Bool` is expected is caught). This test's purpose is to pin the behavior *through the new kernel path*; to make it a true red test, first delete the old `check_method_signature` body (Step 3) — after deletion the mismatch would go uncaught (registering, then failing downstream with a bare `conversion_failure` at the call site), which is the failure this task fixes. Run after Step 3 to see it fail, then Step 4 to make it pass.

- [ ] **Step 3: Delete the surface signature-check machinery**

Delete `alpha_equal?/2` (193), `alpha/3` (195–221), `alpha_name/3` (223–242), `type_var?/1` (246–247), and the two-clause body of `check_method_signature/5` (172–187). Keep the `:default` clause behavior (a synthesized default conforms by construction — no check needed). If `param_type/1` (line 189) is used only by the deleted code, delete it too (grep first: `default_fn_def` and others may use it — it is referenced at 178 and 180 which are being deleted, and in `subst_head` region; verify).

- [ ] **Step 4: Implement the kernel-conversion check**

```elixir
  # A synthesized default conforms to the interface signature by construction.
  defp check_method_signature(_desc, _iface, _method, _for_type, _fn_decl, :default), do: :ok

  # An instance clause must declare the interface method's type with the head
  # variable replaced by this instance's head type, up to definitional equality.
  # We elaborate both the expected (interface, head-substituted) and actual
  # (instance clause) function types to closed Core Pi types and compare with the
  # kernel's conversion — which handles α-renaming of the method's other type
  # variables and δ-unfolding of synonyms for free.
  defp check_method_signature(desc, iface, method, for_type, {:function_def, m, _b}, :instance, env) do
    info = Map.fetch!(desc.methods, method)

    expected_ast = subst_head(info.type_ast, desc.head_var, for_type)
    actual_ast = function_type_ast(Keyword.get(m, :params, []), Keyword.get(m, :return_type))

    with {:ok, expected_core} <- Declarations.lower_type(expected_ast, [], env),
         {:ok, actual_core} <- Declarations.lower_type(actual_ast, [], env),
         true <- Cure.Core.Conv.conv?(expected_core, actual_core, [], 0, env) do
      :ok
    else
      _ -> {:error, {:method_signature_mismatch, iface, method}}
    end
  end

  # Build the surface function-type AST `T1 -> ... -> Tn -> R` from a param list
  # and return type, matching how `Interface.build_method_map` synthesizes
  # `type_ast` (interface.ex:140-143) so the two are convertible.
  defp function_type_ast(params, return_type) do
    param_types = Enum.map(params, fn {:param, pm, _name} -> Keyword.fetch!(pm, :type) end)
    Enum.reduce(Enum.reverse(param_types), return_type, fn dom, cod ->
      {:function_call, [function_type: true], [dom, cod]}
    end)
  end
```

**Note:** `check_method_signature` now needs `env`. Thread it: `build_methods/6` (currently `/6` at line 117, called at line 43 with `env`) already has `env` in scope; update the call at line 122 from `check_method_signature(desc, iface, method, for_type, fn_decl, origin)` to pass `env` as the final arg, and update the arity/clauses accordingly. Verify `function_type_ast` matches `Interface`'s `type_ast` arrow-encoding exactly (read `interface.ex:140-143`); if `Interface` uses a different node shape for the arrow, mirror that shape here instead so conversion sees identical structure.

- [ ] **Step 5: Run the new test + full elaborator suite**

Run: `mix test test/cure/elab/instance_signature_conversion_test.exs`
Expected: PASS (both).

Run: `mix test test/cure/elab/`
Expected: PASS. Higher-kinded interfaces (`Functor for List`, `fmap`'s `a`/`b`) are the ones most likely to expose an arrow-encoding mismatch between `function_type_ast` and `Interface`'s `type_ast`; if a `Functor` test fails on `:method_signature_mismatch`, the encodings differ — align them (Step 4 note).

- [ ] **Step 6: Commit**

```bash
git add lib/cure/elab/implementation.ex test/cure/elab/instance_signature_conversion_test.exs
git commit -m "feat(coherence): check instance signatures by kernel conversion"
```

## Task 1.3: Phase-1 gate

- [ ] **Step 1: Full suite**

Run: `mix test`
Expected: green (~75s). Investigate any regression as a real semantic difference.

- [ ] **Step 2: Antigen assays**

Run the Antigen metatheory gate as configured (the kernel-soundness / coherence assays). Expected: no new violations — Phase 1 touched no kernel code, so Antigen kernel-cover is unchanged.

- [ ] **Step 3: Commit any incidental fixes, then tag the phase mentally complete.** No further code beyond fixes needed to reach green.

---

# Phase 2 — Expanded typeclasses (no syntax change)

**Deliverable:** Every built-in operator has a real interface/function to resolve to, on a minimal `==`/`<` basis with superinterface constraints; today's operator *elaboration* re-routes through these interfaces with byte-identical evaluation. No parser change — `{:binary_op}`/`{:unary_op}` nodes are still produced; only their elaboration target moves.

**Preconditions verified during exploration:**
- **Backtick-escaped identifiers already exist and work** (`lib/cure/compiler/lexer.ex` `lex_quoted_identifier/1` line 742). `` `+` ``, `` `and` `` lex as ordinary `:identifier` tokens carrying `"+"`/`"and"`. **The spec's "Step 2.0 backtick prerequisite" is already satisfied** — no lexer work; add only a confirming test (Task 2.0).
- **`Std.Bool` already defines the connectives as backtick functions** (`` `and` ``/`` `or` ``/`` `not` ``/`` `eq` ``/`` `ne` ``, `lib/std/bool.cure`), and the elaborator already lowers the `and`/`or`/`not` operators to Std.Bool prelude globals. **The spec's "Step 2.4 Bool connectives" is already substantially done** — Task 2.5 only verifies it survives the re-route.

## Task 2.0: Confirm backtick-named operator functions are callable (guard test)

**Files:**
- Test: `test/cure/elab/backtick_operator_names_test.exs` (create).

- [ ] **Step 1: Write the test**

```elixir
# test/cure/elab/backtick_operator_names_test.exs
defmodule Cure.Elab.BacktickOperatorNamesTest do
  @moduledoc "Phase 2: a function may be named by an operator lexeme via backticks."
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  test "a function named `+` elaborates and is callable by that name" do
    src = """
    mod M
      fn `+`(a: Int, b: Int) -> Int = Std.Builtin.int_add(a, b)
      fn use_it(x: Int) -> Int = `+`(x, x)
    end
    """
    assert {:ok, _env} = Program.elaborate(src)
  end
end
```

- [ ] **Step 2: Run it**

Run: `mix test test/cure/elab/backtick_operator_names_test.exs`
Expected: this depends on Task 2.1 (`Std.Builtin.int_add` callable). Run it after Task 2.1; if you want an isolated green now, use body `= a` and drop the `int_add` call. The point of this test is to lock that backtick operator-named defs stay callable through all later changes.

- [ ] **Step 3: Commit**

```bash
git add test/cure/elab/backtick_operator_names_test.exs
git commit -m "test(operators): pin backtick operator-named functions callable"
```

## Task 2.1: Make builtin-op globals callable from surface (`Std.Builtin.<op>`)

**Rationale:** Interface leaf methods for primitive types must bottom out in the builtin ops (`int_eq`, `int_add`, `struct_eq`, …) — not in the operators that desugar to them, or the post-flip desugaring loops. The builtin ops are registered as globals `Std.Builtin#<op>` with a Pi type but `quantities: nil` (`lib/cure/core/builtins.ex` `seed_binops/4` line 214 calls `Env.add_def/4`, leaving quantities nil). A surface qualified call `Std.Builtin.int_eq(a, b)` resolves to that global (`Cure.Elab.Resolution.resolve_qualified/3` builds exactly `Std.Builtin#int_eq`) but then crashes in `elaborate_global_app` at `length(quantities)` on nil (`lib/cure/elab/elaborator.ex:8049-8050`). This task adds a dedicated resolution arm that emits the raw builtin app spine for a `builtin_op`-marked global, mirroring how `build_binop` already emits it — **no kernel change**.

**Files:**
- Modify: `lib/cure/elab/elaborator.ex` — `elaborate_named_call_resolved/8` `cond` (around line 225–344); add a `builtin_op`-global arm before the general `elaborate_global_app` arm.
- Test: `test/cure/elab/builtin_op_surface_call_test.exs` (create).

**Interfaces:**
- Consumes: `Env.get_def/2` (returns `%{builtin_op: bop}` when set — see `lib/cure/core/inductive.ex:298`), `Env.builtin_op/2` (accessor at inductive.ex:307-311 returning the op key or nil).
- Produces: a `{:app, {:app, {:global, key}, a}, b}` (binary) or `{:app, {:global, key}, a}` (unary) / three-arg spine (`struct_eq`) Core term, typed via `Kernel.infer`.

- [ ] **Step 1: Write the failing test (the probe from exploration)**

```elixir
# test/cure/elab/builtin_op_surface_call_test.exs
defmodule Cure.Elab.BuiltinOpSurfaceCallTest do
  @moduledoc """
  Phase 2: a builtin primitive op is callable from surface by its qualified name
  `Std.Builtin.<op>`, so interface leaf methods can bottom out in it.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  test "Std.Builtin.int_eq and int_add are callable" do
    src = """
    mod M
      fn my_eq(a: Int, b: Int) -> Bool = Std.Builtin.int_eq(a, b)
      fn my_add(a: Int, b: Int) -> Int = Std.Builtin.int_add(a, b)
    end
    """
    assert {:ok, _env} = Program.elaborate(src)
  end

  test "Std.Builtin.struct_eq (three-arg, erased type) is callable" do
    src = """
    mod M
      type Color = Red | Green | Blue
      fn ceq(a: Color, b: Color) -> Bool = Std.Builtin.struct_eq(Color, a, b)
    end
    """
    assert {:ok, _env} = Program.elaborate(src)
  end
end
```

- [ ] **Step 2: Run it to confirm it crashes**

Run: `mix test test/cure/elab/builtin_op_surface_call_test.exs`
Expected: FAIL — `ArgumentError: :erlang.length(nil)` at `elaborator.ex:8050` (the crash reproduced during exploration).

- [ ] **Step 3: Add the builtin-op resolution arm**

In `elaborate_named_call_resolved/8`, add an arm to the `cond` *before* the general global-application arms (so it intercepts `Std.Builtin#*` names). Use the existing helpers `app2/3` (line 1213) and `builtin_op_global/1` is not needed here (the name is already the resolved key). Read the exact `cond` shape at 225–344 first; insert:

```elixir
      # A saturated call to a registered builtin primitive op (Std.Builtin#int_add,
      # struct_eq, …). These globals are body-less with `quantities: nil`, so the
      # general `elaborate_global_app` path (which does `length(quantities)`) can't
      # apply them. Emit the raw app spine directly and let the kernel infer the type.
      match?(%{builtin_op: op} when not is_nil(op), Env.get_def(env, atom)) ->
        with {:ok, arg_terms} <- elaborate_all_args(args, names, ctx, env),
             term = build_app_spine({:global, atom}, arg_terms),
             {:ok, type} <- Kernel.infer(ctx, term) do
          {:ok, term, type}
        end
```

Add helpers (near `app2/3`):

```elixir
  # Left-nested application of a head to a list of argument terms.
  defp build_app_spine(head, arg_terms), do: Enum.reduce(arg_terms, head, &{:app, &2, &1})

  defp elaborate_all_args(args, names, ctx, env) do
    Enum.reduce_while(args, {:ok, []}, fn a, {:ok, acc} ->
      case elaborate_expr_typed(a, names, ctx, env) do
        {:ok, term, _ty} -> {:cont, {:ok, acc ++ [term]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end
```

**`struct_eq` note:** its type has an erased type param first (`{:pi, w, {:type,0}, ...}` with quantities `[:erased, :unrestricted, :unrestricted]`, builtins.ex:203). The surface call `Std.Builtin.struct_eq(Color, a, b)` passes the type explicitly as the first arg; `build_app_spine` applies all three positionally and `Kernel.infer` checks them. If `Kernel.infer` rejects the explicit erased type arg (relevance), fall back to reifying/erasing as `build_binop`'s `struct_eq_binop` does (elaborator.ex:1190-1198) — but prefer the direct spine first and only add complexity if the test demands it.

- [ ] **Step 4: Run the test**

Run: `mix test test/cure/elab/builtin_op_surface_call_test.exs`
Expected: PASS (both).

- [ ] **Step 5: Run the elaborator suite (no regression on named-call routing)**

Run: `mix test test/cure/elab/`
Expected: PASS. The new arm only fires for `builtin_op`-marked globals, which no user code currently calls, so nothing else changes.

- [ ] **Step 6: Commit**

```bash
git add lib/cure/elab/elaborator.ex test/cure/elab/builtin_op_surface_call_test.exs
git commit -m "feat(elab): make builtin primitive ops callable by qualified name"
```

## Task 2.2: Superinterface constraints (`interface C(t) requires D(t)`)

**Files:**
- Modify: `lib/cure/compiler/parser.ex` — `parse_interface/1` (6228–6268): parse an optional `requires` clause between the param list (ends ~6246) and `skip_newlines` (6248); add `requires:` to the interface node meta.
- Modify: `lib/cure/elab/interface.ex` — `elaborate/2` (29–50): read `meta[:requires]`, store `super: [...]` in the descriptor (36–43); add a conformance/scope check hook.
- Modify: `lib/cure/elab/implementation.ex` — `register/2`: after computing `head`, verify each superinterface has an instance for `head`, else `{:missing_superinterface, iface, super_iface, head}`.
- Test: `test/cure/elab/superinterface_test.exs` (create).

**Interfaces:**
- Produces: descriptor gains `super: [atom()]` (list of required interface names; `[]` when none). `parse_interface` node meta gains `requires: [String.t()]`.
- Consumes: `Coherence.lookup_anon/3` (coherence.ex:59) to check a superinterface instance exists.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/elab/superinterface_test.exs
defmodule Cure.Elab.SuperinterfaceTest do
  @moduledoc "Phase 2: `interface C(t) requires D(t)` obliges a D instance and scopes D's methods in C's defaults."
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  test "implementing the sub-interface without the super-interface is rejected" do
    src = """
    mod M
      interface Small(t)
        fn small(a: t) -> Bool
      interface Big(t) requires Small(t)
        fn big(a: t) -> Bool

      type Color = Red | Green | Blue
      implementation Big for Color
        fn big(a: Color) -> Bool = True()
    end
    """
    assert {:error, {:missing_superinterface, :Big, :Small, :Color}} = Program.elaborate(src)
  end

  test "providing both instances succeeds" do
    src = """
    mod M
      interface Small(t)
        fn small(a: t) -> Bool
      interface Big(t) requires Small(t)
        fn big(a: t) -> Bool

      type Color = Red | Green | Blue
      implementation Small for Color
        fn small(a: Color) -> Bool = True()
      implementation Big for Color
        fn big(a: Color) -> Bool = True()
    end
    """
    assert {:ok, _env} = Program.elaborate(src)
  end
end
```

- [ ] **Step 2: Run it to confirm parse/elaborate does not yet understand `requires`**

Run: `mix test test/cure/elab/superinterface_test.exs`
Expected: FAIL — `requires` is currently unparsed (parse error or the clause is swallowed), so neither the obligation nor the success path holds.

- [ ] **Step 3: Parse the `requires` clause**

In `parse_interface/1`, after the param-list `case` (line ~6246) and before `skip_newlines`, mirror the `where`-peek pattern used at parser.ex:6297-6305:

```elixir
    {requires, state} =
      case peek(state) do
        %Token{type: :keyword, value: :requires} ->
          state = advance(state)
          parse_superinterface_list(state)   # returns {["Small(t)"...] as parsed constraints}, state}
        _ ->
          {[], state}
      end
```

Reuse the existing constraint parser (`parse_constraint_list`, referenced at 6297-6305) if its output shape (`{iface_name, tyvar}`) fits; the descriptor only needs the interface *names*, so extract those. Add `requires: requires` to the interface node `meta` (line 6258-6264). **Add `requires` to the lexer keyword table** (`@keywords`, lexer.ex:40-51) so `:requires` lexes as a keyword — verify it is not already present; if adding a keyword risks breaking existing identifiers named `requires`, gate it as a contextual keyword recognized only in interface-head position (prefer contextual to avoid a breaking reservation).

- [ ] **Step 4: Store `super` in the descriptor**

In `interface.ex` `elaborate/2`, read `requires = Keyword.get(meta, :requires, [])`, normalize to interface-name atoms, and add `super: requires_atoms` to the `desc` map (lines 36–43).

- [ ] **Step 5: Enforce the obligation at instance registration**

In `implementation.ex` `register/2`, after `head = head_key(...)` and fetching `desc`, add before `build_methods`:

```elixir
    with :ok <- check_superinterfaces(desc, head, env),
         ...
```

```elixir
  defp check_superinterfaces(%{super: supers} = _desc, head, env) do
    coherence = Env.coherence(env) || Coherence.new()
    Enum.reduce_while(supers, :ok, fn sup, :ok ->
      case Coherence.lookup_anon(coherence, sup, head) do
        {:ok, _ref} -> {:cont, :ok}
        {:error, _} -> {:halt, {:error, {:missing_superinterface, _desc.name, sup, head}}}
      end
    end)
  end
  defp check_superinterfaces(_desc, _head, _env), do: :ok  # descriptor without :super
```

(Handle the `:super` key possibly being absent on older descriptors by defaulting to `[]` when building `desc`.)

- [ ] **Step 6: Run the test + elaborator suite**

Run: `mix test test/cure/elab/superinterface_test.exs`
Expected: PASS (both).

Run: `mix test test/cure/elab/`
Expected: PASS — existing interfaces have no `requires`, so `super: []` and `check_superinterfaces` is a no-op for them.

- [ ] **Step 7: Commit**

```bash
git add lib/cure/compiler/parser.ex lib/cure/compiler/lexer.ex lib/cure/elab/interface.ex lib/cure/elab/implementation.ex test/cure/elab/superinterface_test.exs
git commit -m "feat(interface): superinterface constraints (requires clause)"
```

## Task 2.3: Superinterface method scope in default bodies

**Rationale:** `Comparable`'s derived `compare` default calls `==` (from `Equatable`, the superinterface). The default body is elaborated against the instance head; the superinterface's methods must resolve in that scope. Because instances are registered as ordinary mangled globals dispatched by coherence, an `Equatable` instance for the head already exists (Task 2.2 guarantees it), so a bare `eq`/`==` call in the default resolves through the normal method-dispatch path. This task confirms that and adds any missing scoping.

**Files:**
- Test: `test/cure/elab/superinterface_default_scope_test.exs` (create).
- Modify (only if the test fails): `lib/cure/elab/implementation.ex` `default_fn_def/4` (255–275) / the body-pass registration to bring superinterface methods into scope.

- [ ] **Step 1: Write the test**

```elixir
# test/cure/elab/superinterface_default_scope_test.exs
defmodule Cure.Elab.SuperinterfaceDefaultScopeTest do
  @moduledoc "Phase 2: a sub-interface default body may call a super-interface method."
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  test "Big's default calls Small's method" do
    src = """
    mod M
      use Std.Bool
      interface Small(t)
        fn small(a: t) -> Bool
      interface Big(t) requires Small(t)
        fn big(a: t) -> Bool
        fn bigger(a: t) -> Bool = small(a)   # default references the superinterface method

      type Color = Red | Green | Blue
      implementation Small for Color
        fn small(a: Color) -> Bool = True()
      implementation Big for Color
        fn big(a: Color) -> Bool = True()
    end
    """
    assert {:ok, _env} = Program.elaborate(src)
  end
end
```

- [ ] **Step 2: Run it**

Run: `mix test test/cure/elab/superinterface_default_scope_test.exs`
Expected: likely PASS already (method dispatch is coherence-driven, head-typed). If it FAILS with `{:no_instance, :Small, ...}` or an unresolved `small`, the default body is being elaborated before the `Small` instance is visible — fix by ordering: ensure superinterface instance registration precedes sub-interface default body elaboration (both are in the body pass; the coherence registry is populated in the register pass, so this should already hold). Only add code if red.

- [ ] **Step 3: Commit**

```bash
git add test/cure/elab/superinterface_default_scope_test.exs
git commit -m "test(interface): superinterface method visible in subinterface default"
```

## Task 2.4: Minimal-basis `Equatable` / `Comparable` (`==`, `<` primitive; `compare` derived)

**Files:**
- Modify: `lib/std/equatable.cure` — method `eq` → `` `==` ``; add derived `` `!=` `` default; leaf bodies use `Std.Builtin.<op>`; add `Equatable for Char`.
- Modify: `lib/std/comparable.cure` — `interface Comparable(t) requires Equatable(t)`; sole primitive method `` `<` ``; derive `` `<=` ``/`` `>` ``/`` `>=` `` and `compare`/`Ordering` as overridable defaults; leaf `<` bodies use `Std.Builtin.<op>`.
- Test: `test/cure/std/minimal_basis_test.exs` (create) + Cure fixtures under a suitable stdlib test harness (`phase35/run-on-unix.sh` for evaluation, or the existing stdlib ExUnit harness — check `test/cure/std/`).

**Important — `priv/std` is generated:** author ONLY in `lib/std/*.cure`; `priv/std/*.cure` is a gitignored generated copy (per memory `priv-std-generated-bundle`). Regenerate/rebuild after editing (`mix escript.build` rebuilds and re-preloads).

**Design (from spec §2.2, LATTER model):**
- `Equatable(t)`: sole obligation `` `==`(a: t, b: t) -> Bool ``; `` `!=` `` is a derived default `not (a == b)` written without the operator to avoid regress — use `Std.Bool.\`not\`(\`==\`(a,b))` or a `pickup`. Leaf instances (Int/Float/String/Bool/Atom/Char) supply `` `==` `` = `Std.Builtin.<eq>` (`int_eq`, `float_eq`, `struct_eq` for String/Bool/Atom/Char as today's `==` lowering dictates — Bool/Atom/Char and String go through `struct_eq`; Int/Float through `int_eq`/`float_eq`; consult `build_binop`'s `{:==,:!=}` clause elaborator.ex:1134-1153 for the exact per-type primitive).
- `Comparable(t) requires Equatable(t)`: sole obligation `` `<`(a: t, b: t) -> Bool ``; derived defaults `` `<=` ``, `` `>` ``, `` `>=` ``, and `compare(a,b) -> Ordering` = `if a == b then EqualTo else if a < b then LessThan else GreaterThan` (written with `pickup`, referencing `==` from the superinterface and `<`). `Ordering` type stays. Leaf `<` bodies: Int `Std.Builtin.int_lt`, Float `Std.Builtin.float_lt`, Char `Std.Builtin.int_lt(code_point(a), code_point(b))`, String a lexicographic recursion (keep `compare_string`, but rebase it to produce `<` or override `compare`).

**Migration caution:** `Equatable`/`Comparable` are consumed across the stdlib and by the elaborator's `combine_call`/`compare_op_call`. Renaming the method from `eq`/`compare` to `` `==` ``/`` `<` `` changes the method-name the elaborator dispatches to. **Coordinate with Task 2.6** (elaborator re-route) — these two tasks land together or the elaborator's `compare_op_call` (which calls `compare`) breaks. Sequence: implement 2.4 and 2.6 as one reviewable unit if the suite cannot be green between them; otherwise keep `compare` as a derived default (still present) so `compare_op_call` keeps working until 2.6 replaces it.

- [ ] **Step 1: Write the failing differential test**

```elixir
# test/cure/std/minimal_basis_test.exs
defmodule Cure.Std.MinimalBasisTest do
  @moduledoc """
  Phase 2: the minimal-basis Equatable/Comparable derive the full comparison
  surface from `==` and `<`, with identical results to the pre-migration stdlib.
  """
  use ExUnit.Case, async: true
  # Use the project's stdlib evaluation harness. Prefer the same helper the
  # existing comparable/equatable tests use — locate it under test/cure/std/.

  # Each case asserts an evaluated Cure expression's value. Replace `eval_bool/1`
  # with the actual harness call used elsewhere in test/cure/std/.
  test "derived comparison operators match direct computation" do
    assert eval_bool("1 == 1") == true
    assert eval_bool("1 != 2") == true
    assert eval_bool("1 < 2") == true
    assert eval_bool("2 <= 2") == true
    assert eval_bool("3 > 2") == true
    assert eval_bool("3 >= 3") == true
  end

  test "compare is derived and still returns Ordering" do
    assert eval_ordering("compare(1, 2)") == :LessThan
    assert eval_ordering("compare(2, 2)") == :EqualTo
    assert eval_ordering("compare(3, 2)") == :GreaterThan
  end

  test "Float NaN equality stays IEEE-correct (not derived from compare)" do
    # NaN == NaN must be false with `==` primitive.
    assert eval_bool("nan() == nan()") == false
  end

  test "Char equality works via the new Char instance" do
    assert eval_bool("'a' == 'a'") == true
    assert eval_bool("'a' < 'b'") == true
  end
end
```

Before writing: **read an existing `test/cure/std/` test to copy its evaluation harness** (module, helper names, how it compiles+runs a Cure snippet). Do not invent `eval_bool`/`eval_ordering` — bind them to the real harness. If no per-expression eval harness exists, use `phase35/run-on-unix.sh` with a small fixture `.cure` that prints results, asserted via a shell-driven test (heavier; prefer the ExUnit harness).

- [ ] **Step 2: Run it to confirm failure**

Run: `mix test test/cure/std/minimal_basis_test.exs`
Expected: FAIL — the new operators/instances don't exist yet on the new basis (and `nan()`/Char cases exercise not-yet-present behavior). Some cases may pass on the *current* stdlib (which is the differential baseline — record the current results first by running the same expressions against `main`/pre-change to lock expected values).

- [ ] **Step 3: Rewrite `lib/std/equatable.cure`**

```cure
@group(:core)
mod Std.Equatable
  use Std.String
  use Std.Char
  use Std.Bool

  interface Equatable(t)
    fn `==`(a: t, b: t) -> Bool
    ## `!=` derived from `==`, written without the operator to avoid regress.
    fn `!=`(a: t, b: t) -> Bool = Std.Bool.`not`(`==`(a, b))

  implementation Equatable for Int
    fn `==`(a: Int, b: Int) -> Bool = Std.Builtin.int_eq(a, b)

  implementation Equatable for Float
    fn `==`(a: Float, b: Float) -> Bool = Std.Builtin.float_eq(a, b)

  implementation Equatable for String
    fn `==`(a: String, b: String) -> Bool = Std.Builtin.struct_eq(String, a, b)

  implementation Equatable for Bool
    fn `==`(a: Bool, b: Bool) -> Bool = Std.Builtin.struct_eq(Bool, a, b)

  implementation Equatable for Atom
    fn `==`(a: Atom, b: Atom) -> Bool = Std.Builtin.struct_eq(Atom, a, b)

  implementation Equatable for Char
    fn `==`(a: Char, b: Char) -> Bool = Std.Builtin.int_eq(code_point(a), code_point(b))
```

Verify the exact primitive per type against `build_binop`'s `{:==,:!=}` clause (elaborator.ex:1134-1153): Int→`int_eq`, Float→`float_eq`, Bool→`eq` (Std.Bool) — for Bool, prefer `Std.Bool.\`==\`` if that is the canonical primitive rather than `struct_eq`; String/Atom/Char via `struct_eq`/`int_eq` as shown. Adjust to match today's lowering so evaluation is identical.

- [ ] **Step 4: Rewrite `lib/std/comparable.cure`**

```cure
@group(:core)
mod Std.Comparable
  use Std.Char
  use Std.String
  use Std.Bool
  use Std.Equatable

  type Ordering = LessThan | EqualTo | GreaterThan

  interface Comparable(t) requires Equatable(t)
    fn `<`(a: t, b: t) -> Bool
    fn `<=`(a: t, b: t) -> Bool = Std.Bool.`or`(`<`(a, b), `==`(a, b))
    fn `>`(a: t, b: t) -> Bool = `<`(b, a)
    fn `>=`(a: t, b: t) -> Bool = Std.Bool.`or`(`<`(b, a), `==`(a, b))
    ## Derived tripartite compare; overridable. References `==` (superinterface) and `<`.
    fn compare(a: t, b: t) -> Ordering =
      pickup
        `==`(a, b) -> EqualTo
        `<`(a, b)  -> LessThan
        else       -> GreaterThan

  implementation Comparable for Int
    fn `<`(a: Int, b: Int) -> Bool = Std.Builtin.int_lt(a, b)

  implementation Comparable for Float
    fn `<`(a: Float, b: Float) -> Bool = Std.Builtin.float_lt(a, b)

  implementation Comparable for Char
    fn `<`(a: Char, b: Char) -> Bool = Std.Builtin.int_lt(code_point(a), code_point(b))

  ## Lexicographic `<` over String = List(Char).
  fn string_lt(a: String, b: String) -> Bool =
    match a
      [] ->
        match b
          []      -> False()
          [_ | _] -> True()
      [ha | ta] ->
        match b
          []        -> False()
          [hb | tb] ->
            pickup
              Std.Builtin.int_lt(code_point(ha), code_point(hb)) -> True()
              Std.Builtin.int_lt(code_point(hb), code_point(ha)) -> False()
              else                                               -> string_lt(ta, tb)

  implementation Comparable for String
    fn `<`(a: String, b: String) -> Bool = string_lt(a, b)
```

Confirm `pickup` supports an `else` arm and that guard expressions may be method calls (the current `comparable.cure` uses `a < b` guards, so method-call guards are fine). Confirm `code_point` is in scope via `use Std.Char`.

- [ ] **Step 5: Rebuild the stdlib and run the differential test**

Run: `mix escript.build` (regenerates `priv/std`, recompiles stdlib beams).
Run: `mix test test/cure/std/minimal_basis_test.exs`
Expected: PASS — derived operators equal direct computation; `compare` still returns `Ordering`; `NaN == NaN` is false; Char works.

- [ ] **Step 6: Run the stdlib + elaborator suites**

Run: `mix test test/cure/std/ test/cure/elab/`
Expected: PASS. Failures here are most likely other stdlib modules that called `eq`/`compare` by name — grep `lib/std/` for `eq(`/`compare(`/`ne(` and update call sites to the new method names where they were the *interface* methods (not unrelated local `eq`s). This is the coordination surface flagged above.

- [ ] **Step 7: Commit**

```bash
git add lib/std/equatable.cure lib/std/comparable.cure test/cure/std/minimal_basis_test.exs
git commit -m "feat(std): minimal-basis Equatable/Comparable on ==/< with derived compare"
```

## Task 2.5: Arithmetic interfaces (`Additive` / `Multiplicative` / `Divisible`)

**Files:**
- Create: `lib/std/arithmetic.cure` (`@group(:core)`, module `Std.Arithmetic`) — the three interfaces + Int/Float instances.
- Test: `test/cure/std/arithmetic_interfaces_test.exs` (create).

**Design (spec §2.3):** split rather than one `Num`, motivated by `Std.Measurements` (`Duration` has `add`/`sub`/`scale` but no `Duration * Duration` — measurements.cure:84-90). `%` (remainder) is Int-specific and does **not** go in `Divisible` (Float has no clean total modulo on AtomVM); pin it as an Int-only `` `%` `` method on a small `Integral`-style interface or an Int-only free function — **decision: put `` `%` `` on `Additive`? No.** Put `` `%` `` as an Int-only method in a separate `interface Integral(t)` with only `Int` conforming. Float never implements `%`.

```cure
@group(:core)
mod Std.Arithmetic
  interface Additive(t)
    fn `+`(a: t, b: t) -> t
    fn `-`(a: t, b: t) -> t
    fn negate(a: t) -> t

  interface Multiplicative(t)
    fn `*`(a: t, b: t) -> t

  interface Divisible(t)
    fn `/`(a: t, b: t) -> t

  interface Integral(t)
    fn `%`(a: t, b: t) -> t

  implementation Additive for Int
    fn `+`(a: Int, b: Int) -> Int = Std.Builtin.int_add(a, b)
    fn `-`(a: Int, b: Int) -> Int = Std.Builtin.int_sub(a, b)
    fn negate(a: Int) -> Int = Std.Builtin.int_neg(a)
  implementation Multiplicative for Int
    fn `*`(a: Int, b: Int) -> Int = Std.Builtin.int_mul(a, b)
  implementation Divisible for Int
    fn `/`(a: Int, b: Int) -> Int = Std.Builtin.int_div(a, b)
  implementation Integral for Int
    fn `%`(a: Int, b: Int) -> Int = Std.Builtin.int_rem(a, b)

  implementation Additive for Float
    fn `+`(a: Float, b: Float) -> Float = Std.Builtin.float_add(a, b)
    fn `-`(a: Float, b: Float) -> Float = Std.Builtin.float_sub(a, b)
    fn negate(a: Float) -> Float = Std.Builtin.float_neg(a)
  implementation Multiplicative for Float
    fn `*`(a: Float, b: Float) -> Float = Std.Builtin.float_mul(a, b)
  implementation Divisible for Float
    fn `/`(a: Float, b: Float) -> Float = Std.Builtin.float_div(a, b)
```

Confirm builtin op names against `@int_binop_globals`/`@float_binop_globals` (elaborator.ex:1104-1129) and `neg_global` (1203-1209): `int_neg`/`float_neg` exist. `int_rem` exists (`:rem` → `int_rem`).

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/std/arithmetic_interfaces_test.exs
defmodule Cure.Std.ArithmeticInterfacesTest do
  use ExUnit.Case, async: true
  # bind eval helpers to the real stdlib harness (see Task 2.4 Step 1)

  test "Additive/Multiplicative/Divisible methods compute on Int and Float" do
    assert eval_int("`+`(2, 3)") == 5
    assert eval_int("`*`(2, 3)") == 6
    assert eval_int("`/`(6, 2)") == 3
    assert eval_int("`%`(7, 3)") == 1
    assert eval_int("negate(5)") == -5
    assert eval_float("`+`(2.0, 0.5)") == 2.5
  end
end
```

- [ ] **Step 2: Run to confirm failure**

Run: `mix test test/cure/std/arithmetic_interfaces_test.exs`
Expected: FAIL — `Std.Arithmetic` doesn't exist yet.

- [ ] **Step 3: Create `lib/std/arithmetic.cure`** (content above).

- [ ] **Step 4: Rebuild + run**

Run: `mix escript.build && mix test test/cure/std/arithmetic_interfaces_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/std/arithmetic.cure test/cure/std/arithmetic_interfaces_test.exs
git commit -m "feat(std): Additive/Multiplicative/Divisible/Integral arithmetic interfaces"
```

## Task 2.6: Re-route operator elaboration through the interfaces (differential)

**Files:**
- Modify: `lib/cure/elab/elaborator.ex` — `elaborate_expr_typed({:binary_op, ...})` (727–753), `combine_call` (941–944), `compare_op_call` (963–975), `build_binop`'s `{:==,:!=}` and comparison clauses; `elaborate_expr_typed({:unary_op, ...})` (676–708).
- Modify: `lib/cure/elab/deriving.ex` (+ its caller `lib/cure/elab/program.ex` `body_register_pass`/`register_derived`) — auto-synthesise a structural `Equatable` instance for every data type lacking a hand-written one.
- Modify: `lib/std/equatable.cure` / `lib/std/comparable.cure` — mark `@prelude`-ambient (per the `@prelude` decorator) so `==`/`<` resolve with no import.
- Test: `test/cure/elab/operator_reroute_differential_test.exs` (create), plus `test/cure/elab/auto_derive_equatable_test.exs` (create).

**Design (spec §2.5 — SOLE-ROUTE invariant):** operators desugar to a bare-name method call `{:function_call, [name: <op-lexeme>], [l, r]}` resolved by `Resolve.method_call` / `Overload.resolve`, and the typeclass becomes the **only** route to `==`/`!=`/`<`/`<=`/`>`/`>=`. Concretely:
- **Remove `build_binop`'s per-type hardcoding** for `==`/`!=` (int_eq/float_eq/struct_eq/Std.Bool.eq) and for the comparison operators. Those primitives now live *only* in the leaf instance bodies (Task 2.4). Static instance selection on a concrete operand type lowers `1 == 2` to the identical Core spine as today — so the fast path is preserved as an optimisation of the single route, not a second definition.
- **No `struct_eq` last-resort outside the typeclass.** Universal structural `==` on ADTs is retained by **auto-deriving a structural `Equatable`** for any data type without a hand-written instance (coherence-safe, per-type — never a blanket instance). The derived instance *is* field-wise `struct_eq`, reached through coherence; a hand-written `Equatable for T` supersedes it (override). Primitives stay locked (a second `Equatable for Int` is a coherence error).
- **`Comparable`/`<` is NOT auto-derived** (no universal structural order). `<`/`<=`/`>`/`>=` on a type with no `Comparable` instance rejects with `{:no_instance, Comparable, T}`.
- **`@prelude` ambience + bootstrap DAG audit.** Mark `Std.Equatable`/`Std.Comparable` ambient so use sites need no import. Audit the stdlib compile order: no module below `Std.Equatable` in the DAG may use `==` (primitive leaf defs like `Std.Bool.` `` `eq` `` are plain functions, safe). If the audit finds a lower module using `==`, rewrite that use to the primitive or lift the module — do NOT reintroduce a builtin `==` path.
- **Derived ops are top-level `where`-functions, not interface methods (as landed in Task 2.4).** `` `!=` ``/`` `<=` ``/`` `>` ``/`` `>=` ``/`compare` are `fn … where Equatable(t)`/`where Comparable(t)` top-level functions whose bodies re-dispatch `` `==` ``/`` `<` `` through the coherence dictionary — so they DO reflect a user's overridden instance (verified). Consequence for this task: the `@prelude` ambience must make these derived FUNCTIONS ambient too (not just the interface instances), or `a <= b` desugaring to `` `<=`(a,b) `` won't resolve without an explicit `use Std.Comparable`. When re-routing, `a <= b` resolves to the top-level `` `<=` `` function (an ordinary constrained global), not an interface-method lookup — both `Resolve` paths must be considered.

**Scope note:** this task grew from a pure "re-route" into "re-route + delete the parallel path + auto-derive + prelude". If the auto-derive + bootstrap audit make a single reviewable unit too large, split into **2.6a** (re-route operators to methods; delete `build_binop`'s `==`/`<` hardcoding; prelude + DAG audit) and **2.6b** (auto-derive structural `Equatable`, override + no-instance-error tests). Land 2.6a green first (it needs auto-derive OR a temporary explicit `Equatable` for the test ADTs to keep `==`-on-ADT green — prefer landing 2.6a+2.6b together if ADT `==` would otherwise regress).

**Minimal, low-risk staging:** change the method *targets* and prove identity via the differential regression lock at every edit before deleting the old hardcoding. Because the leaf methods emit exactly the builtin spine `build_binop` emitted, an expression that goes through the method path yields the same Core term — the differential test is the guard. Delete the `build_binop` `==`/`<` hardcoding only once every operator expression routes through methods with identical evaluated results.

- [ ] **Step 1: Write the differential test**

```elixir
# test/cure/elab/operator_reroute_differential_test.exs
defmodule Cure.Elab.OperatorRerouteDifferentialTest do
  @moduledoc "Phase 2: re-routed operators evaluate identically to the builtin path."
  use ExUnit.Case, async: true
  # eval helpers bound to the real harness

  test "arithmetic, comparison, equality, boolean — Int/Float/ADT/List" do
    assert eval("1 + 2 * 3") == 7
    assert eval("10 / 2 - 1") == 4
    assert eval("1 < 2") == true
    assert eval("2 >= 2") == true
    assert eval("1 == 1") == true
    assert eval("[1,2] <> [3]") == [1,2,3]      # Semigroup path unchanged
    assert eval("true and false") == false
    assert eval("not true") == false
    assert eval("\"a\" == \"a\"") == true         # String Equatable instance
    # ADT structural == now reached via the auto-derived Equatable instance,
    # evaluating identically to today's struct_eq (see auto_derive_equatable_test).
    assert eval("Some(1) == Some(1)") == true
    assert eval("Some(1) == None()") == false
  end
end
```

Record the expected values by running each expression against the pre-change build first (differential baseline). The two ADT `==` cases are the regression lock proving the auto-derived structural instance matches the old builtin `struct_eq` exactly.

- [ ] **Step 2: Run — establish current green baseline**

Run: `mix test test/cure/elab/operator_reroute_differential_test.exs`
Expected: PASS on the current elaborator (these all compile today). This test is a *regression lock*, not initially red — its job is to fail if any re-route step changes a result.

- [ ] **Step 3: Point the arithmetic/comparison fallbacks at the new method names**

Update `combine_call` (unchanged — still `"combine"`) and `compare_op_call`: since `Comparable` now exposes `` `<` `` directly, replace the `compare(a,b) == Ordering` desugaring with a direct method call to the operator lexeme:

```elixir
  defp compare_op_call(cmp, l, r, names, ctx, env) do
    name = Atom.to_string(cmp)   # "<", ">", "<=", ">="
    elaborate_expr_typed({:function_call, [name: name], [l, r]}, names, ctx, env)
  end
```

And the `:+` fallback (`combine_call` at 739–740) stays for `<>`/non-numeric `+`. Add fallbacks for `*`/`/`/`-`/`%` that route to the arithmetic method by lexeme when `build_binop` returns `{:unsupported_operand_type, op}` for a non-primitive operand:

```elixir
        {:error, {:unsupported_operand_type, op}}
        when op in [:+, :-, :*, :/, :rem] ->
          arith_method_call(op, l, r, names, ctx, env)
```

```elixir
  defp arith_method_call(op, l, r, names, ctx, env) do
    name = op_lexeme(op)   # :+ -> "+", :rem -> "%", etc.
    elaborate_expr_typed({:function_call, [name: name], [l, r]}, names, ctx, env)
  end
```

- [ ] **Step 4: Run the differential test after each edit**

Run: `mix test test/cure/elab/operator_reroute_differential_test.exs`
Expected: PASS unchanged after every edit. If a value changes, the re-route diverged — stop and reconcile (usually a wrong leaf primitive in Task 2.4/2.5).

- [ ] **Step 5: Auto-derive structural `Equatable` for un-conformed ADTs**

Before deleting `build_binop`'s `struct_eq` path, make the typeclass cover what it covered. In `lib/cure/elab/deriving.ex` (+ `program.ex` registration), synthesise a structural `Equatable` instance for every data type that has no hand-written `Equatable` — field-wise equality that emits the SAME `struct_eq` spine the builtin used. Per-type only (skip types with an explicit instance; never a blanket instance). Write `test/cure/elab/auto_derive_equatable_test.exs`:

```elixir
defmodule Cure.Elab.AutoDeriveEquatableTest do
  @moduledoc "Phase 2: ADTs get structural Equatable auto-derived; user instances override; primitives stay locked."
  use ExUnit.Case, async: true
  # eval helpers bound to the real harness (Program.elaborate -> reachable_def_names -> Emit.compile_and_load -> apply)

  test "un-conformed ADT gets structural == identical to old struct_eq" do
    assert eval_bool("Some(1) == Some(1)") == true
    assert eval_bool("Some(1) == Some(2)") == false
  end

  test "a hand-written Equatable for T overrides the derived structural one (no overlap error)" do
    # define `type Mod3 = ...` with a custom `Equatable for Mod3`; assert its == wins.
  end

  test "a second Equatable for Int is rejected by coherence (primitives locked)" do
    assert {:error, {:overlapping_instance, :Equatable, :Int}} = Program.elaborate(dup_int_instance_src)
  end
end
```

Run: `mix test test/cure/elab/auto_derive_equatable_test.exs` — Expected: PASS.

- [ ] **Step 6: Delete `build_binop`'s `==`/`<` hardcoding + mark interfaces `@prelude`; audit the DAG**

Remove the `{:==,:!=}` per-type clause and the comparison-operator hardcoding from `build_binop` so the ONLY route is the method desugar. Mark `Std.Equatable`/`Std.Comparable` `@prelude`-ambient (`lib/std/equatable.cure`, `lib/std/comparable.cure`) so `==`/`<` resolve with no import. Audit the stdlib compile order: grep for `==`/`<` uses in modules compiled below `Std.Equatable`; each must be rewritten to a primitive or the module lifted — do NOT reintroduce a builtin `==`. Add a `{:no_instance, Comparable, T}` rejection test for `<` on a type with no `Comparable` instance.

Run: `mix escript.build && mix test test/cure/elab/operator_reroute_differential_test.exs` — Expected: PASS unchanged (the differential lock proves deletion changed nothing).

- [ ] **Step 7: Run the full elaborator + stdlib suites**

Run: `mix test test/cure/elab/ test/cure/std/`
Expected: PASS. Any red here is a use site that lost its `==`/`<` builtin path — fix it through the typeclass (add/derive an instance or import), never by restoring the hardcoding.

- [ ] **Step 8: Commit**

```bash
git add lib/cure/elab/elaborator.ex lib/cure/elab/deriving.ex lib/cure/elab/program.ex lib/std/equatable.cure lib/std/comparable.cure test/cure/elab/operator_reroute_differential_test.exs test/cure/elab/auto_derive_equatable_test.exs
git commit -m "feat(elab): route ==/< solely through Equatable/Comparable; auto-derive structural Equatable"
```

## Task 2.7: Phase-2 gate

- [ ] **Step 1:** Run `mix test` — full suite green (~75s).
- [ ] **Step 2:** Run the Antigen assays — no new violations (no kernel change).
- [ ] **Step 3:** Spot-check a hardware-adjacent value program on generic-unix AtomVM: `phase35/run-on-unix.sh Cure.<Demo> <file>.cure` for a small arithmetic/comparison program, confirming operators still evaluate on the VM (per repo convention: validate on unix before assuming). Fix any regression before proceeding.

---

# Phase 3 — Precedence groups + fixity declarations + the flip

**Deliverable:** the static `Precedence` table is replaced by a declaration-driven fixity table assembled from `precedencegroup`/`infix`/`prefix`/`postfix` declarations; built-in operators are declared in a preloaded `Std.Operators` module with the old table's associativity/ordering; word and custom operators parse and dispatch through Phase-2 interfaces; built-in *syntactic* operators (`.`/`|>`/`<-|`/`=`/`..`) keep precedence membership but fixed non-overloadable meaning.

**Key files:**
- `lib/cure/compiler/parser/precedence.ex` — the static table to replace with a session-assembled lookup.
- `lib/cure/compiler/parser.ex` — Pratt loop `parse_infix/3` (2184–2213), `build_infix_op/3` (2692–2743), `parse_unary/2` (2656–2664), `reject_non_assoc_chain/3` (2226–2242); new `parse_precedencegroup`/`parse_fixity` decl parsers.
- `lib/cure/compiler/lexer.ex` — keyword-remap `case kw do` (816–837); new keywords `precedencegroup`/`infix`/`prefix`/`postfix`; generic operator-lexeme lexing.
- `lib/cure/stdlib/preload.ex` — `Std.Operators` picked up automatically (compile-time scan); ensure preload order.

**Sequencing risk (spec §Risks):** bootstrapping — the modules that *define* operator meanings (`Std.Equatable`, `Std.Comparable`, `Std.Arithmetic`, `Std.Bool`, `Std.Operators`) must parse before their operators exist. They already avoid infix operators in the relevant bodies (leaf bodies are `Std.Builtin.<op>` calls; defaults use `pickup`/`Std.Bool.\`x\``; connectives use `match`). Task 3.1's bootstrap test locks this.

## Task 3.1: Fixity table assembled from declarations (parse `precedencegroup`/`infix`/`prefix`/`postfix`)

**Files:**
- Create: `lib/cure/compiler/parser/fixity_table.ex` — session-scoped `%FixityTable{}` mapping `lexeme -> {fixity, group, assoc}` + computed binding powers from the group partial order; replaces `Precedence.infix_bp/prefix_bp/non_assoc?`.
- Modify: `lib/cure/compiler/lexer.ex` — add `precedencegroup infix prefix postfix` to `@keywords` (contextually if reservation breaks identifiers); lex generic symbolic operator lexemes.
- Modify: `lib/cure/compiler/parser.ex` — `parse_precedencegroup/1`, `parse_fixity/1`; feed decls into the table before expression parsing.
- Test: `test/cure/compiler/fixity_table_test.exs` (create).

- [ ] **Step 1: Write the failing test (table computation in isolation)**

```elixir
# test/cure/compiler/fixity_table_test.exs
defmodule Cure.Compiler.FixityTableTest do
  @moduledoc "Phase 3: a fixity table computes binding powers from group relations."
  use ExUnit.Case, async: true
  alias Cure.Compiler.Parser.FixityTable

  test "higher_than/lower_than yield a consistent binding-power order" do
    t =
      FixityTable.new()
      |> FixityTable.add_group(:Comparison, assoc: :none, higher_than: [], lower_than: [:Additive])
      |> FixityTable.add_group(:Additive, assoc: :left, higher_than: [:Comparison], lower_than: [:Multiplicative])
      |> FixityTable.add_group(:Multiplicative, assoc: :left, higher_than: [:Additive], lower_than: [])
      |> FixityTable.add_infix("+", :Additive)
      |> FixityTable.add_infix("*", :Multiplicative)
      |> FixityTable.add_infix("<", :Comparison)

    {lp_plus, _} = FixityTable.infix_bp(t, "+")
    {lp_star, _} = FixityTable.infix_bp(t, "*")
    {lp_lt, _}  = FixityTable.infix_bp(t, "<")
    assert lp_lt < lp_plus and lp_plus < lp_star
    assert FixityTable.non_assoc?(t, "<")
    assert FixityTable.infix_bp(t, "unknown") == :not_infix
  end

  test "incomparable groups are detected" do
    t =
      FixityTable.new()
      |> FixityTable.add_group(:A, assoc: :left, higher_than: [], lower_than: [])
      |> FixityTable.add_group(:B, assoc: :left, higher_than: [], lower_than: [])
      |> FixityTable.add_infix("<?>", :A)
      |> FixityTable.add_infix("<!>", :B)

    assert FixityTable.incomparable?(t, "<?>", "<!>")
  end
end
```

- [ ] **Step 2: Run to confirm failure**

Run: `mix test test/cure/compiler/fixity_table_test.exs`
Expected: FAIL — `Cure.Compiler.Parser.FixityTable` does not exist.

- [ ] **Step 3: Implement `FixityTable`**

Create `lib/cure/compiler/parser/fixity_table.ex` with a struct holding groups (name → `%{assoc, higher_than, lower_than}`), operator entries (lexeme → `%{fixity, group}`), and a memoized topological ranking of groups into integer binding powers (compute once via `Cure.Compiler.DepGraph.toposort` — reused from preload, per exploration — or a small local Kahn sort over the relation edges). `infix_bp/2` returns `{left_bp, right_bp}` with `right = left + 1` for `:left`/`:none`, `right = left` for `:right`; `non_assoc?/2` true when the operator's group assoc is `:none`; `incomparable?/3` true when neither group reaches the other in the relation closure. Keep lookups O(1) maps (heed the parser-quadratic memory).

- [ ] **Step 4: Add the keywords + declaration parsers**

Add `precedencegroup infix prefix postfix` as keywords (lexer.ex:40-51); if reserving them breaks existing identifiers, make them contextual (recognized only at declaration start). Add `parse_precedencegroup/1` (parses `precedencegroup Name` + indented `associativity:`/`higher_than:`/`lower_than:` lines) and `parse_fixity/1` (parses `infix|prefix|postfix <op-lexeme-or-word> : Group`) to the parser, producing `{:precedencegroup, meta, []}` and `{:fixity, meta, []}` AST nodes. The op-lexeme is a backtick identifier or a bare word/symbol.

- [ ] **Step 5: Run the table test**

Run: `mix test test/cure/compiler/fixity_table_test.exs`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add lib/cure/compiler/parser/fixity_table.ex lib/cure/compiler/lexer.ex lib/cure/compiler/parser.ex test/cure/compiler/fixity_table_test.exs
git commit -m "feat(parser): declaration-driven fixity table"
```

## Task 3.2: `Std.Operators` — declare the built-in operators with the old precedences

**Files:**
- Create: `lib/std/operators.cure` (`@group(:core)`, module `Std.Operators`) — `precedencegroup` + `infix`/`prefix` declarations reproducing the `Precedence` table (precedence.ex:42-96) exactly: assignment(5,right), melquiades(8,none, builtin), pipe(10,left, builtin), or(20,left), and(30,left), comparison(40,none), range(50,none, builtin), string_concat(60,right), additive(70,left), multiplicative(80,left), prefix minus/not(90), dot(100,left, builtin). Mark `.`/`|>`/`<-|`/`=`/`..`/augmented-assign as `builtin` (non-overloadable).
- Modify: `lib/cure/stdlib/preload.ex` — confirm `Std.Operators` is scanned (automatic via `@stdlib_sources`) and loads early; add `use` edges if a specific order is needed.
- Test: `test/cure/std/operators_module_test.exs` (create) — parse `Std.Operators`, assemble the table, assert it reproduces the legacy binding powers.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/std/operators_module_test.exs
defmodule Cure.Std.OperatorsModuleTest do
  @moduledoc "Phase 3: Std.Operators reproduces the legacy precedence order."
  use ExUnit.Case, async: true
  alias Cure.Compiler.Parser.FixityTable

  test "assembled built-in table matches legacy relative order" do
    t = Cure.Stdlib.Preload.builtin_fixity_table()   # new accessor: table from Std.Operators
    {and_lp, _} = FixityTable.infix_bp(t, "and")
    {or_lp, _}  = FixityTable.infix_bp(t, "or")
    {plus_lp, _} = FixityTable.infix_bp(t, "+")
    {star_lp, _} = FixityTable.infix_bp(t, "*")
    {lt_lp, _}  = FixityTable.infix_bp(t, "<")
    assert or_lp < and_lp
    assert and_lp < lt_lp
    assert lt_lp < plus_lp
    assert plus_lp < star_lp
    assert FixityTable.non_assoc?(t, "<")
    assert FixityTable.non_assoc?(t, "==")
  end
end
```

- [ ] **Step 2: Run to confirm failure**

Run: `mix test test/cure/std/operators_module_test.exs`
Expected: FAIL — `Std.Operators` and `builtin_fixity_table/0` don't exist.

- [ ] **Step 3: Write `lib/std/operators.cure`**

Reproduce the legacy table. Example fragment (complete it for every operator in precedence.ex:42-96):

```cure
@group(:core)
mod Std.Operators
  precedencegroup Assignment
    associativity: right
  precedencegroup LogicalOr
    associativity: left
    higher_than: Assignment
  precedencegroup LogicalAnd
    associativity: left
    higher_than: LogicalOr
  precedencegroup Comparison
    associativity: none
    higher_than: LogicalAnd
  precedencegroup Concat
    associativity: right
    higher_than: Comparison
  precedencegroup Additive
    associativity: left
    higher_than: Concat
  precedencegroup Multiplicative
    associativity: left
    higher_than: Additive

  infix or  : LogicalOr
  infix and : LogicalAnd
  infix ==  : Comparison
  infix !=  : Comparison
  infix <   : Comparison
  infix >   : Comparison
  infix <=  : Comparison
  infix >=  : Comparison
  infix `<>` : Concat
  infix `+` : Additive
  infix `-` : Additive
  infix `*` : Multiplicative
  infix `/` : Multiplicative
  infix `%` : Multiplicative
  prefix `-`  : Multiplicative
  prefix not  : Multiplicative
```

Built-in syntactic operators (`.`, `|>`, `<-|`, `=`, `+=`…, `..`, `..=`) get `precedencegroup` membership marked `builtin` (add a `builtin` modifier to the fixity syntax, or a separate `builtin infix ..`) so the flip keeps their fixed meaning and rejects user rebinding.

- [ ] **Step 4: Add `builtin_fixity_table/0` to preload** that parses `Std.Operators` and assembles the `FixityTable`. Ensure it is available before user expression parsing.

- [ ] **Step 5: Rebuild + run**

Run: `mix escript.build && mix test test/cure/std/operators_module_test.exs`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add lib/std/operators.cure lib/cure/stdlib/preload.ex test/cure/std/operators_module_test.exs
git commit -m "feat(std): Std.Operators declares built-in operators and precedences"
```

## Task 3.3: Flip the Pratt loop onto the fixity table; desugar overloadable operators to method calls

**Files:**
- Modify: `lib/cure/compiler/parser.ex` — `parse_infix/3` (2184–2213) consults the session `FixityTable` (threaded through parser `state`) instead of `Precedence.infix_bp`; `parse_unary/2` (2656–2664) via `FixityTable` prefix bp; `reject_non_assoc_chain/3` (2226–2242) via `FixityTable.non_assoc?`; `build_infix_op/3` (2692–2743) — overloadable operators build `{:binary_op, [operator: <lexeme-atom>], [l,r]}` (unchanged shape) while built-in syntactic ops keep their dedicated nodes; add incomparable-group rejection.
- Modify: `lib/cure/compiler/lexer.ex` — stop remapping `and`/`or`/`not` to `:and_op`/`:or_op`/`:not_op` *only if* the parser now treats them as fixity-table words; symbolic operators lex to a generic operator-lexeme token carrying the string. **Stage carefully** — keep the old token atoms working until the parser consults the table, to keep the suite green between commits.
- Modify: `lib/cure/elab/elaborator.ex` — `{:binary_op}` with an overloadable `operator:` lexeme desugars to `{:function_call, [name: lexeme], [l,r]}`; keep the primitive/`struct_eq` fast paths from Phase 2 as the resolution of the resulting method call.
- Test: `test/cure/compiler/operator_flip_test.exs` (create) + re-run the Phase-2 differential test (must stay green through the flip).

- [ ] **Step 1: Write the failing test (word + custom operators through the table)**

```elixir
# test/cure/compiler/operator_flip_test.exs
defmodule Cure.Compiler.OperatorFlipTest do
  @moduledoc "Phase 3: operators parse via the fixity table; words and custom operators work."
  use ExUnit.Case, async: true
  # eval helper bound to the real harness

  test "word operators resolve to their functions" do
    assert eval("true and false") == false
    assert eval("not true") == false
  end

  test "a user-declared operator dispatches to its function" do
    src = """
    mod M
      use Std.Operators
      precedencegroup Custom
        associativity: left
        higher_than: Additive
      infix `<?>` : Custom
      fn `<?>`(a: Int, b: Int) -> Int = Std.Builtin.int_add(a, b)
      fn go() -> Int = 1 <?> 2 <?> 3
    end
    """
    assert eval_in(src, "go()") == 6
  end

  test "incomparable operators without parens are rejected" do
    src = """
    mod M
      use Std.Operators
      precedencegroup GroupA
        associativity: left
      precedencegroup GroupB
        associativity: left
      infix `<?>` : GroupA
      infix `<!>` : GroupB
      fn `<?>`(a: Int, b: Int) -> Int = a
      fn `<!>`(a: Int, b: Int) -> Int = b
      fn bad() -> Int = 1 <?> 2 <!> 3
    end
    """
    assert {:error, {:ambiguous_precedence, _, _}} = Cure.Elab.Program.elaborate(src)
  end

  test "a fixity declaration with no function errors at use" do
    src = """
    mod M
      use Std.Operators
      infix `<@>` : Additive
      fn nope() -> Int = 1 <@> 2
    end
    """
    assert {:error, {:no_operator_meaning, _}} = Cure.Elab.Program.elaborate(src)
  end
end
```

- [ ] **Step 2: Run to confirm failure**

Run: `mix test test/cure/compiler/operator_flip_test.exs`
Expected: FAIL — custom operators, incomparable rejection, and no-meaning errors are not yet wired.

- [ ] **Step 3: Thread the fixity table through the parser state**

Add a `fixity_table` field to the parser state, initialized from `Cure.Stdlib.Preload.builtin_fixity_table()` and extended as `precedencegroup`/`infix`/… decls in the current module are parsed (two-pass over the module: collect fixity decls first, then parse expressions — mirror how `defaults` are collected before bodies). Replace `Precedence.infix_bp(token.type)` (2199) with `FixityTable.infix_bp(state.fixity_table, lexeme_of(token))`, where `lexeme_of` returns the operator string (`token.value` for backtick/symbolic, the word for `and`/`or`/`not`).

- [ ] **Step 4: Overloadable vs built-in node building**

In `build_infix_op/3`, keep the special `:pipe`/`:melquiades`/`:dot`/`:range`/`:assign`/augmented cases (built-in syntactic — fixed meaning). For a generic overloadable operator, build `{:binary_op, [operator: String.to_atom(lexeme), category: :overloaded, line:, col:], [l, r]}`. Add incomparable-group detection adjacent to `reject_non_assoc_chain` (compare the current and next operator groups via `FixityTable.incomparable?`), recording `{:ambiguous_precedence, g1, g2}`.

- [ ] **Step 5: Elaborator desugar**

In `elaborate_expr_typed({:binary_op, meta, [l,r]})`, when `category == :overloaded` (or the operator lexeme is not one of the built-in syntactic set), desugar to `{:function_call, [name: Atom.to_string(op)], [l, r]}` and elaborate that (routing through `Resolve.method_call`/`Overload.resolve` from Phase 2). Keep the `<>`→combine, primitive fast-path, and `struct_eq` last-resort. When resolution finds no function/instance for the operator name, surface `{:no_operator_meaning, op}`.

- [ ] **Step 6: Run the flip test + the Phase-2 differential**

Run: `mix test test/cure/compiler/operator_flip_test.exs test/cure/elab/operator_reroute_differential_test.exs`
Expected: PASS — custom/word operators work, incomparable/no-meaning errors fire, and the differential stays byte-identical.

- [ ] **Step 7: Commit**

```bash
git add lib/cure/compiler/parser.ex lib/cure/compiler/lexer.ex lib/cure/elab/elaborator.ex test/cure/compiler/operator_flip_test.exs
git commit -m "feat(parser): flip operators onto the fixity table with method desugaring"
```

## Task 3.4: Unary minus / `negate` and built-in-operator protection

**Files:**
- Modify: `lib/cure/compiler/parser.ex` `parse_unary/2`, `lib/cure/elab/elaborator.ex` unary path (676–708) — prefix `-` desugars to `negate` (the `Additive` method); `not` to `Std.Bool.\`not\``.
- Modify: parser/elaborator — reject a `infix`/`prefix` declaration that rebinds a `builtin` operator lexeme (`.`, `|>`, `<-|`, `=`, `..`).
- Test: extend `test/cure/compiler/operator_flip_test.exs`.

- [ ] **Step 1: Write the failing tests**

```elixir
  test "prefix minus desugars to negate" do
    assert eval("-(5)") == -5
    assert eval("- 5 + 2") == -3
  end

  test "rebinding a builtin syntactic operator is rejected" do
    src = """
    mod M
      use Std.Operators
      infix `|>` : Additive
    end
    """
    assert {:error, {:builtin_operator_not_overloadable, :|>}} = Cure.Elab.Program.elaborate(src)
  end
```

- [ ] **Step 2: Run to confirm failure.**

Run: `mix test test/cure/compiler/operator_flip_test.exs`
Expected: the two new cases FAIL.

- [ ] **Step 3: Implement.** Prefix `-` → `{:function_call, [name: "negate"], [operand]}`; `not` → `{:function_call, [name: "not"], [operand]}` (resolves to `Std.Bool.\`not\``). In the fixity-decl elaboration, if the target lexeme is marked `builtin` in the table, reject with `{:builtin_operator_not_overloadable, lexeme}`.

- [ ] **Step 4: Run.**

Run: `mix test test/cure/compiler/operator_flip_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/compiler/parser.ex lib/cure/elab/elaborator.ex test/cure/compiler/operator_flip_test.exs
git commit -m "feat(operators): unary negate desugar + builtin-operator protection"
```

## Task 3.5: Retire the static `Precedence` table

**Files:**
- Modify/Delete: `lib/cure/compiler/parser/precedence.ex` — remove `infix_bp`/`prefix_bp`/`non_assoc?` once no caller remains; keep `operator_symbol`/`operator_category` only if still referenced, else delete the module.
- Modify: any remaining callers (grep `Precedence\.`).
- Test: `mix test` full suite.

- [ ] **Step 1: Grep for residual callers**

Run: `grep -rn "Parser.Precedence\|Precedence\." lib/cure/`
Expected: only the sites migrated in 3.1–3.4. Migrate any stragglers to `FixityTable`.

- [ ] **Step 2: Delete the dead table**

Remove `infix_bp/1`, `prefix_bp/1`, `non_assoc?/1` (and `operator_symbol`/`operator_category` if unused). If the whole module is unused, delete `lib/cure/compiler/parser/precedence.ex`.

- [ ] **Step 3: Run full suite**

Run: `mix test`
Expected: green.

- [ ] **Step 4: Commit**

```bash
git add -A
git commit -m "refactor(parser): remove static precedence table"
```

## Task 3.6: Bootstrap + Phase-3 gate

- [ ] **Step 1: Bootstrap test** — a test that parses `Std.Operators`, `Std.Equatable`, `Std.Comparable`, `Std.Arithmetic`, `Std.Bool` against an *empty* fixity table and confirms they parse (no reliance on operators they themselves define). Create `test/cure/std/operator_bootstrap_test.exs`.

```elixir
# test/cure/std/operator_bootstrap_test.exs
defmodule Cure.Std.OperatorBootstrapTest do
  use ExUnit.Case, async: true
  @modules ~w(operators.cure equatable.cure comparable.cure arithmetic.cure bool.cure)

  test "operator-defining stdlib modules parse without a pre-existing operator table" do
    for f <- @modules do
      src = File.read!(Path.join([File.cwd!(), "lib", "std", f]))
      assert {:ok, _ast} = Cure.Compiler.Parser.parse(src),
             "#{f} must parse against an empty fixity table"
    end
  end
end
```

Run: `mix test test/cure/std/operator_bootstrap_test.exs` — Expected: PASS. If a module fails, it uses an infix operator in a body that isn't yet declared; rewrite that body in `pickup`/`Std.Builtin.<op>`/`match` form.

- [ ] **Step 2: Full suite** — `mix test` green (~75s).
- [ ] **Step 3: Antigen assays** — no new violations.
- [ ] **Step 4: Generic-unix VM check** — `phase35/run-on-unix.sh` on a small program mixing arithmetic, comparison, boolean, and a custom operator; confirm evaluation on AtomVM. Per repo convention, validate on unix before assuming.
- [ ] **Step 5: Commit any fixes.** Phase 3 (and the program) complete when all gates are green.

---

## Cross-cutting notes

- **Test harness discovery (do first, once):** before Task 2.4, read an existing `test/cure/std/*` test to bind the real evaluation helpers (`eval`, `eval_bool`, `eval_ordering`, `eval_in`). The pseudo-helpers in this plan's test code are placeholders for whatever the codebase actually provides; do not ship invented helpers.
- **`priv/std` is generated** — author only in `lib/std/`, rebuild with `mix escript.build` after each stdlib edit (memory `priv-std-generated-bundle`).
- **Naming** — spell out interface/method names (`Additive`, `Multiplicative`, `negate`); no terse abbreviations (operator directive).
- **Escalate, don't work around**, if any task appears to need a `lib/cure/core/**` change — the zero-TCB constraint is a hard line for this program.
