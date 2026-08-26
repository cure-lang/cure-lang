# Antigen Tier A Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build the schema-directed half of Antigen — the harness plus four known-label assays — so it catches the confirmed mutual-recursion totality hole two independent ways, with zero dependence on a general dependent-term generator.

**Architecture:** A backend-neutral reified generator DSL (`Antigen.Gen`) interpreted by a quarantined `Backend.StreamData`; three known-label generators that build `Cure.Core` terms and `Cure.Core.Env` directly (bypassing the elaborator); four pure assays that run the real kernel; two committed, never-pruned, generator-independent corpora; and a runner with explore/generate/replay modes. Phase 2 adds process-local fuel instrumentation to the `Cure.Core.Conv` δ-path so `reflexivity-as-normalization` can bound conversion deterministically.

**Tech Stack:** Elixir, ExUnit, StreamData (new test-only dep), the existing `Cure.Core.*` kernel (`Term`, `Env`, `Context`, `Certificate`, `Kernel`, `Conv`, `Eval`, `Inductive`, `Serialize`).

**Design spec:** `docs/superpowers/specs/antigen/2026-07-01-antigen-tier-a-design.md` (hardened). **Umbrella:** `docs/superpowers/specs/antigen/2026-07-01-antigen-design.md`.

## Global Constraints

- **Architecture rule (spec §6, umbrella §4):** nothing under `Antigen.Generators.*` or `Antigen.Assays.*` may reference `StreamData`. Only `Antigen.Backend.StreamData` may. Enforced by an architecture test (Task 12).
- **Antigen detects, never fixes (spec §1).** No task in this plan modifies `Certificate`, and no task "fixes" the mutual-recursion hole. The only kernel file touched is `Cure.Core.Conv` (Task 13), and only to *add* fuel instrumentation — pure step-counting, no semantic change to the existing `conv?/5` path.
- **Compile Cure with OTP 26–28.** Antigen runs on the dev host under `mix`, never ships to AtomVM; host-only constructs (process dictionary, `throw`/`catch`) are acceptable here and only here.
- **Fuel is a FIXED committed constant (spec §8):** a δ-unfold step count baked into `Antigen.Assays.Reflexivity`, identical on every machine and run mode, so committed antibodies replay identically. Never machine- or wall-clock-derived.
- **Two corpora are never pruned, C2-serialized, generator-independent (spec §7):** `test/antigen/corpus.sexp` (antibodies, admit-any) and `test/antigen/seeds.sexp` (valid/seed bank, admit-if-coverage-novel). Replay decodes and runs the assay *through the kernel*; the generator is never on the read path.
- **`mix test` never mutates a corpus (spec §2 crit. 4).** Only the explorer/generate runner appends; the replayer is read-only. CI stays git-clean.
- **Ghost-written commits.** Commit per task; author as the user only, never co-sign.
- **One full build/test run at any moment.** Never launch concurrent `mix test`/`mix compile` — a past concurrent full-suite run caused a kernel panic. Serialize all suite runs.
- **Tests are immutable once green-by-design.** A red test written in Step 1 is fixed by changing the Step 3 implementation, never by editing, weakening, skipping, or deleting the test in Step 4. The only exception: the test itself is proven wrong (states the wrong expected behavior) — in that case, fix the test only after writing down why it's wrong, and treat that correction itself as a new Step 1/2 (re-verify it now fails for the *right* reason before touching implementation).

## Kernel API reference (verified against source — use these exact signatures)

**`Cure.Core.Term`** (`lib/cure/core/term.ex`) — Core AST is plain tagged tuples, de Bruijn indices:
`{:type, level}` · `{:var, k}` · `{:pi, dom, cod}` · `{:lam, dom, body}` · `{:app, f, a}` · `{:sigma, a, b}` · `{:pair, a, b}` · `{:fst, p}` · `{:snd, p}` · `{:data, name, params, indices}` · `{:ctor, name, args}` · `{:case, scrut, motive, branches}` (branches `[{ctor_name, arity, body}]`) · `{:global, name}` · `{:eq, ty, a, b}` · `{:refl, a}` · `{:rewrite, proof, motive, body}`. This is the complete node set `term.ex`'s own `term?/1`, `subst/3`, `shift/3`, and `to_external/1` recognize; its moduledoc explicitly disclaims "implicits, holes, or erasure annotations." **Caveat, verified against source:** `{:int_type}`, `{:int_lit, n}`, `{:bool_type}`, `{:bool_lit, b}`, `{:float_type}`, `{:float_lit, f}`, `{:prim, op, args}`, and `{:hole, name}` nodes *do* exist and are handled by `Eval`, `Kernel.infer/check`, `Serialize`, `Quote`, and `Value` — but **`Term.term?/1` has no clauses for any of them** (falls through to `false`). None of Tasks 9–11's generators need these nodes (they build Peano-style naturals via `:global`/`:ctor`/`:case`), so this gap is inert for Tier A — but if a future task's self-test asserts `Term.term?/1` on a term containing one of these nodes, expect a false negative; that would be a pre-existing kernel gap outside this plan's scope, not an Antigen bug.
- `Term.subst(t, k, u) :: t()` (term.ex:122) — substitute de Bruijn index `k` with `u`.
- `Term.shift(t, d, cutoff) :: t()` (term.ex:84) — lift free vars.
- `Term.term?(t) :: boolean()` (term.ex:47) — shape check.

**`Cure.Core.Env`** (defined in `lib/cure/core/inductive.ex:12-63`) — the global signature:
- `Env.empty() :: t()` — `%Env{families: %{}, ctors: %{}, ctor_to_family: %{}, defs: %{}, certified: MapSet.new()}`.
- `Env.add_def(env, name, type_term, body_term) :: t()` (inductive.ex:31) — register a global def; stored as `%{name, type, body, quantities: nil}` in `env.defs[name]`. Both type and body are `Term.t()`.
- `Env.get_def(env, name) :: %{name:, type:, body:, quantities:} | nil` (inductive.ex:52).
- `Env.certify(env, name) :: t()` (inductive.ex:57) — add `name` to the certified set.
- `Env.certified?(env, name) :: boolean()` (inductive.ex:61).

**`Cure.Core.Certificate`** (`lib/cure/core/certificate.ex`):
- `Certificate.terminating?(name, body_term) :: boolean()` (certificate.ex:33) — caller passes `Env.get_def(env, name).body`. `calls?/2` (certificate.ex:165) matches only `{:global, ^name}` → **a body of `f` calling `{:global, :g}` makes `calls?(:f, body_f) == false`, so `terminating?(:f, body_f) == true` immediately. This is the hole.**

**`Cure.Core.Kernel`** (`lib/cure/core/kernel.ex`):
- `Kernel.infer(ctx, term) :: {:ok, Value.t()} | {:error, term()}` (kernel.ex:24).
- `Kernel.check(ctx, term, type_value) :: :ok | {:error, term()}` (kernel.ex:256).
- `Kernel.check_def(env, name) :: :ok | {:error, term()}` (kernel.ex:276).
- `Kernel.validate_certificate(env, name) :: {:ok, env} | {:error, term()}` (kernel.ex:298) — runs `check_def` + `Certificate.terminating?`, returns env with `name` certified iff both pass.

**`Cure.Core.Conv`** (`lib/cure/core/conv.ex`):
- `Conv.conv?(t1, t2, nbe_env, depth, sig \\ nil) :: boolean()` (conv.ex:27). `sig` is an `Env.t()`.
- δ path: `whnf_delta/2` (conv.ex:89) recurses `{:ok, reduced} -> whnf_delta(reduced, sig)`; `unfold_head/2` (conv.ex:98) returns `:stuck` unless the head global is `Env.certified?`. **The unbounded loop for a wrongly-certified cycle lives entirely in `whnf_delta`'s self-recursion.**
- `same_neutral_no_delta?/3` (conv.ex:179) short-circuits two *structurally identical* neutrals as equal before δ — why literal `conv(t,t)` tests nothing (spec §4.3).

**`Cure.Core.Eval`** (`lib/cure/core/eval.ex`): `Eval.eval(term, env_values) :: Value.t()` (eval.ex:20); `Eval.apply(v, arg) :: Value.t()` (eval.ex:86).

**`Cure.Core.Inductive`** (`lib/cure/core/inductive.ex`):
- telescope `:: [{atom(), Term.t()}]`; `family :: %{name, params, indices, level}`; `ctor :: %{name, args, result_indices, quantities}`.
- `Inductive.family(name, params, indices, level) :: family()` (inductive.ex:95).
- `Inductive.ctor(name, args, result_indices) :: ctor()` (inductive.ex:104) / `ctor/4` with quantities (inductive.ex:109).
- `Inductive.declare(env, family, ctors) :: Env.t()` (inductive.ex:114).
- `Inductive.positive?(env, family) :: :ok | {:error, {:non_strictly_positive, atom()}}` (inductive.ex:208) — strict-positivity checker; ctors looked up from env, so `declare` first.

**`Cure.Core.Serialize`** (`lib/cure/core/serialize.ex`): `Serialize.encode(term) :: binary()` (serialize.ex:18) and `Serialize.decode(binary) :: {:ok, term()} | {:error, term()}` (serialize.ex:69). **Encodes/decodes a single `Term.t()` only — NOT an `Env` or def-group.** This is why `Antigen.Corpus` needs its own record envelope that composes `Serialize` over each term piece (Task 5).

**Test house style** (`test/cure/core/kernel_test.exs`): `use ExUnit.Case, async: true`; `alias Cure.Core.{Kernel, Context, Eval}`; build a context with `Context.empty/0..1` + `Context.extend/2`; assert `{:ok, value}` / `:ok` / `{:error, _}` from kernel entry points.

---

## Phase 1 — harness skeleton

Delivers a runnable engine driven by a **stub assay + stub generator** so the whole explore/generate/replay/report/corpus/coverage data flow is exercised end-to-end before any real assay exists. The stub `Challenge` carries a single `Term.t()` payload, which pins down the corpus envelope and coverage key on the simplest possible object; Phase 2 adds the real `Challenge` kinds without changing the line format.

### Task 1: Add StreamData dependency + Antigen path skeleton

**Files:**
- Modify: `mix.exs` (deps + `preferred_cli_env`)
- Create: `lib/antigen/challenge.ex`
- Test: `test/antigen/challenge_test.exs`

**Interfaces:**
- Produces: `Antigen.Challenge` struct `%Antigen.Challenge{kind, assay, label, payload, seed, note}` where `kind :: :stub | :def_group | :family | :forcing_pair`, `assay :: String.t()`, `label :: :terminating | :diverging | :positive | :negative | :none`, `payload :: term()`, `seed :: integer() | nil`, `note :: String.t() | nil`. Phase-1 stub payload is `%{term: Term.t()}`.

- [ ] **Step 1: Write the failing test**

```elixir
# test/antigen/challenge_test.exs
defmodule Antigen.ChallengeTest do
  use ExUnit.Case, async: true
  alias Antigen.Challenge

  test "a stub challenge holds a single Core term and defaults" do
    c = Challenge.stub({:type, 0})
    assert %Challenge{kind: :stub, assay: "stub", label: :none} = c
    assert c.payload == %{term: {:type, 0}}
    assert c.seed == nil
  end

  test "new/1 fills fields from a keyword list" do
    c = Challenge.new(kind: :stub, assay: "stub", label: :none, payload: %{term: {:var, 0}}, seed: 7)
    assert c.seed == 7
    assert c.payload.term == {:var, 0}
  end
end
```

- [ ] **Step 2: Run it, verify it fails**

Run: `mix test test/antigen/challenge_test.exs`
Expected: FAIL — `Antigen.Challenge` undefined.

- [ ] **Step 3: Add the dep and the struct**

In `mix.exs`, add to `deps/0`: `{:stream_data, "~> 1.0", only: [:test]}`. This repo's `mix.exs` declares a `def cli do [preferred_envs: [...]] end` callback (Elixir ≥ 1.15 style) rather than a `preferred_cli_env:` key in `project/0` — **the latter is silently ignored by Mix whenever `cli/0` is defined** (verified directly: with both present, only the `cli/0` entry takes effect). Since the `antigen` task's default env (`:dev`) already matches Mix's own default when no env is specified, no entry is strictly required; if one is added for explicitness, append `antigen: :dev` to the existing `def cli do [preferred_envs: [...]] end` list, not to `project/0`. Then:

```elixir
# lib/antigen/challenge.ex
defmodule Antigen.Challenge do
  @moduledoc "A generated challenge injected into the kernel (umbrella §3)."
  @enforce_keys [:kind, :assay, :label, :payload]
  defstruct [:kind, :assay, :label, :payload, :seed, :note]

  @type kind :: :stub | :def_group | :family | :forcing_pair
  @type label :: :terminating | :diverging | :positive | :negative | :none
  @type t :: %__MODULE__{
          kind: kind(), assay: String.t(), label: label(),
          payload: map(), seed: integer() | nil, note: String.t() | nil
        }

  @spec new(keyword()) :: t()
  def new(fields), do: struct!(__MODULE__, Keyword.merge([label: :none, seed: nil, note: nil], fields))

  @spec stub(Cure.Core.Term.t()) :: t()
  def stub(term), do: new(kind: :stub, assay: "stub", label: :none, payload: %{term: term})
end
```

- [ ] **Step 4: Run it, verify it passes**

Run: `mix deps.get && mix test test/antigen/challenge_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add mix.exs mix.lock lib/antigen/challenge.ex test/antigen/challenge_test.exs
git commit -m "feat(antigen): challenge struct + stream_data dep"
```

### Task 2: `Antigen.Gen` — reified generator DSL

**Files:**
- Create: `lib/antigen/gen.ex`
- Test: `test/antigen/gen_test.exs`

**Interfaces:**
- Produces: constructors returning reified nodes — `Gen.return(x) :: {:return, x}`, `Gen.member_of(list) :: {:member_of, list}`, `Gen.one_of(gens) :: {:one_of, gens}`, `Gen.frequency(weighted) :: {:frequency, [{pos_integer, gen}]}`, `Gen.bind(g, f) :: {:bind, g, f}`, `Gen.sized(f) :: {:sized, f}`, `Gen.resize(n, g) :: {:resize, n, g}`, `Gen.int(lo, hi) :: gen` (derived, = `member_of` over the range). `Gen.tag(gen, :unsized | :size_monotonic) :: {:tagged, tag, gen}`. `Gen.support(gen) :: {:finite, MapSet.t()} | :over_approx` (structural support set; `bind` yields `:over_approx`).

The DSL is data only — **no interpretation here** (that is the backend, Task 3). No `filter` primitive (spec §6): the generate-then-filter anti-pattern is excluded.

- [ ] **Step 1: Write the failing test**

```elixir
# test/antigen/gen_test.exs
defmodule Antigen.GenTest do
  use ExUnit.Case, async: true
  alias Antigen.Gen

  test "constructors reify to inspectable tagged tuples" do
    assert Gen.return(3) == {:return, 3}
    assert Gen.member_of([1, 2]) == {:member_of, [1, 2]}
    assert {:frequency, [{2, {:return, :a}}, {1, {:return, :b}}]} =
             Gen.frequency([{2, Gen.return(:a)}, {1, Gen.return(:b)}])
    assert {:bind, {:return, 1}, _f} = Gen.bind(Gen.return(1), fn x -> Gen.return(x + 1) end)
  end

  test "int/2 is derived from member_of over the range" do
    assert Gen.int(0, 2) == {:member_of, [0, 1, 2]}
  end

  test "support is finite for member_of/one_of/return and over-approx through bind" do
    assert Gen.support(Gen.member_of([1, 2, 3])) == {:finite, MapSet.new([1, 2, 3])}
    assert Gen.support(Gen.one_of([Gen.return(:a), Gen.return(:b)])) == {:finite, MapSet.new([:a, :b])}
    assert Gen.support(Gen.bind(Gen.return(1), fn _ -> Gen.return(2) end)) == :over_approx
  end

  test "tag records size hygiene" do
    assert Gen.tag(Gen.member_of([1]), :unsized) == {:tagged, :unsized, {:member_of, [1]}}
  end
end
```

- [ ] **Step 2: Run it, verify it fails**

Run: `mix test test/antigen/gen_test.exs`
Expected: FAIL — `Antigen.Gen` undefined.

- [ ] **Step 3: Implement the DSL**

```elixir
# lib/antigen/gen.ex
defmodule Antigen.Gen do
  @moduledoc "Reified, inspectable generator AST (spec §6). Data only; interpreted by a Backend."
  @type t ::
          {:return, term()}
          | {:member_of, [term()]}
          | {:one_of, [t()]}
          | {:frequency, [{pos_integer(), t()}]}
          | {:bind, t(), (term() -> t())}
          | {:sized, (non_neg_integer() -> t())}
          | {:resize, non_neg_integer(), t()}
          | {:tagged, :unsized | :size_monotonic, t()}

  def return(x), do: {:return, x}
  def member_of(list) when is_list(list), do: {:member_of, list}
  def one_of(gens) when is_list(gens), do: {:one_of, gens}
  def frequency(weighted) when is_list(weighted), do: {:frequency, weighted}
  def bind(g, f) when is_function(f, 1), do: {:bind, g, f}
  def sized(f) when is_function(f, 1), do: {:sized, f}
  def resize(n, g) when is_integer(n) and n >= 0, do: {:resize, n, g}
  def tag(g, t) when t in [:unsized, :size_monotonic], do: {:tagged, t, g}
  def int(lo, hi) when lo <= hi, do: member_of(Enum.to_list(lo..hi))

  @doc "Structural support over-approximation (spec §6). `bind`'s continuation is opaque."
  @spec support(t()) :: {:finite, MapSet.t()} | :over_approx
  def support({:return, x}), do: {:finite, MapSet.new([x])}
  def support({:member_of, xs}), do: {:finite, MapSet.new(xs)}
  def support({:one_of, gs}), do: union_support(gs)
  def support({:frequency, ws}), do: union_support(Enum.map(ws, fn {_w, g} -> g end))
  def support({:resize, _n, g}), do: support(g)
  def support({:tagged, _t, g}), do: support(g)
  def support({:sized, _f}), do: :over_approx
  def support({:bind, _g, _f}), do: :over_approx

  defp union_support(gs) do
    Enum.reduce_while(gs, {:finite, MapSet.new()}, fn g, {:finite, acc} ->
      case support(g) do
        {:finite, s} -> {:cont, {:finite, MapSet.union(acc, s)}}
        :over_approx -> {:halt, :over_approx}
      end
    end)
  end
end
```

- [ ] **Step 4: Run it, verify it passes**

Run: `mix test test/antigen/gen_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/gen.ex test/antigen/gen_test.exs
git commit -m "feat(antigen): reified Gen DSL with support-set over-approximation"
```

### Task 3: `Antigen.Backend` behaviour + `Backend.StreamData`

**Files:**
- Create: `lib/antigen/backend.ex`
- Create: `lib/antigen/backend/stream_data.ex`
- Test: `test/antigen/backend/stream_data_test.exs`

**Interfaces:**
- Consumes: `Antigen.Gen` nodes (Task 2).
- Produces: `Antigen.Backend` behaviour with `@callback interp(Gen.t()) :: term()` (backend-native generator), `@callback sample(gen_native, opts) :: [term()]`. `Backend.StreamData.interp/1 :: StreamData.t()`. `Backend.StreamData.sample(streamdata, count) :: [term()]`. This is the ONLY module permitted to reference `StreamData` (enforced Task 12).

- [ ] **Step 1: Write the failing test**

```elixir
# test/antigen/backend/stream_data_test.exs
defmodule Antigen.Backend.StreamDataTest do
  use ExUnit.Case, async: true
  alias Antigen.{Gen, Backend}

  test "interp maps each Gen primitive to a StreamData generator that samples in-support" do
    gen = Gen.one_of([Gen.return(:a), Gen.return(:b)])
    samples = Backend.StreamData.sample(Backend.StreamData.interp(gen), 20)
    assert Enum.all?(samples, &(&1 in [:a, :b]))
    assert length(samples) == 20
  end

  test "bind maps to StreamData.bind (integrated shrinking preserved)" do
    gen = Gen.bind(Gen.member_of([1, 2, 3]), fn n -> Gen.return(n * 10) end)
    samples = Backend.StreamData.sample(Backend.StreamData.interp(gen), 30)
    assert Enum.all?(samples, &(&1 in [10, 20, 30]))
  end

  test "member_of over a range covers the whole range across enough samples" do
    samples = Backend.StreamData.sample(Backend.StreamData.interp(Gen.int(0, 4)), 200)
    assert MapSet.subset?(MapSet.new(0..4), MapSet.new(samples))
  end
end
```

- [ ] **Step 2: Run it, verify it fails**

Run: `mix test test/antigen/backend/stream_data_test.exs`
Expected: FAIL — modules undefined.

- [ ] **Step 3: Implement the behaviour + StreamData interpreter**

```elixir
# lib/antigen/backend.ex
defmodule Antigen.Backend do
  @moduledoc "Behaviour: interpret a Gen program in a concrete PBT backend (umbrella §4.1)."
  alias Antigen.Gen
  @callback interp(Gen.t()) :: term()
  @callback sample(native :: term(), count :: non_neg_integer()) :: [term()]
end
```

```elixir
# lib/antigen/backend/stream_data.ex
defmodule Antigen.Backend.StreamData do
  @moduledoc "The StreamData backend — the ONLY module allowed to reference StreamData."
  @behaviour Antigen.Backend
  alias Antigen.Gen

  @impl true
  def interp({:return, x}), do: StreamData.constant(x)
  def interp({:member_of, xs}), do: StreamData.member_of(xs)
  def interp({:one_of, gs}), do: StreamData.one_of(Enum.map(gs, &interp/1))
  def interp({:frequency, ws}), do: StreamData.frequency(Enum.map(ws, fn {w, g} -> {w, interp(g)} end))
  def interp({:bind, g, f}), do: StreamData.bind(interp(g), fn x -> interp(f.(x)) end)
  def interp({:sized, f}), do: StreamData.sized(fn n -> interp(f.(n)) end)
  def interp({:resize, n, g}), do: StreamData.resize(interp(g), n)
  def interp({:tagged, _tag, g}), do: interp(g)

  @impl true
  def sample(native, count), do: native |> Enum.take(count)
end
```

- [ ] **Step 4: Run it, verify it passes**

Run: `mix test test/antigen/backend/stream_data_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/backend.ex lib/antigen/backend/stream_data.ex test/antigen/backend/stream_data_test.exs
git commit -m "feat(antigen): backend behaviour + quarantined StreamData interpreter"
```

### Task 4: `Antigen.Coverage` — the coverage key

**Files:**
- Create: `lib/antigen/coverage.ex`
- Test: `test/antigen/coverage_test.exs`

**Interfaces:**
- Consumes: `Antigen.Challenge` (Task 1).
- Produces: `Coverage.key(Challenge.t()) :: coverage_key` where `coverage_key :: {constructors :: MapSet.t(atom()), depth_bucket :: :b0_2 | :b3_5 | :b6_9 | :b10p, flags :: MapSet.t(atom()), label :: Challenge.label()}`. `Coverage.key_string(coverage_key) :: String.t()` (canonical, for dedup + serialization). `Coverage.terms_of(Challenge.t()) :: [Term.t()]` (all Core terms in a challenge — the surface the key is computed over; Phase 1 stub → `[payload.term]`).

The key is a **feature vector, not a full-shape hash** (spec §7.2): it plateaus. Depth buckets: `0..2 → :b0_2`, `3..5 → :b3_5`, `6..9 → :b6_9`, `10+ → :b10p`. Flags computed over the terms: `:has_shadowing` (a binder whose body rebinds the same de Bruijn slot — approximated as any nested `:lam`/`:pi`/`:sigma` under another binder), `:has_mutual_group` (challenge kind `:def_group`/`:forcing_pair` with ≥2 defs), plus one `:<elim>_present` flag per eliminator kind actually used (`:app_present`, `:case_present`, `:fst_present`, `:snd_present`, `:rewrite_present`).

- [ ] **Step 1: Write the failing test**

```elixir
# test/antigen/coverage_test.exs
defmodule Antigen.CoverageTest do
  use ExUnit.Case, async: true
  alias Antigen.{Challenge, Coverage}

  test "constructor set and depth bucket for a small term" do
    c = Challenge.stub({:app, {:lam, {:type, 0}, {:var, 0}}, {:type, 0}})
    {ctors, bucket, _flags, label} = Coverage.key(c)
    assert :app in ctors and :lam in ctors and :type in ctors and :var in ctors
    assert bucket == :b0_2
    assert label == :none
  end

  test "app_present flag is set when an application occurs" do
    c = Challenge.stub({:app, {:var, 0}, {:var, 1}})
    {_ctors, _bucket, flags, _label} = Coverage.key(c)
    assert :app_present in flags
    refute :case_present in flags
  end

  test "depth bucket climbs into b3_5 for a deeper term" do
    deep = {:app, {:app, {:app, {:var, 0}, {:var, 0}}, {:var, 0}}, {:var, 0}}
    {_c, bucket, _f, _l} = Coverage.key(Challenge.stub(deep))
    assert bucket == :b3_5
  end

  test "key_string is stable and identical for equal keys" do
    c = Challenge.stub({:type, 0})
    assert Coverage.key_string(Coverage.key(c)) == Coverage.key_string(Coverage.key(c))
    assert is_binary(Coverage.key_string(Coverage.key(c)))
  end

  test "has_shadowing flag fires for a binder nested under another binder, not for a single binder" do
    single = {:lam, {:type, 0}, {:var, 0}}
    {_c, _b, flags1, _l} = Coverage.key(Challenge.stub(single))
    refute :has_shadowing in flags1

    curried_pi = {:pi, {:type, 0}, {:pi, {:type, 0}, {:type, 0}}}
    {_c, _b, flags2, _l} = Coverage.key(Challenge.stub(curried_pi))
    assert :has_shadowing in flags2
  end
end
```

- [ ] **Step 2: Run it, verify it fails**

Run: `mix test test/antigen/coverage_test.exs`
Expected: FAIL — `Antigen.Coverage` undefined.

- [ ] **Step 3: Implement coverage**

```elixir
# lib/antigen/coverage.ex
defmodule Antigen.Coverage do
  @moduledoc "The coverage key: a plateauing feature vector for dedup + the health gate (spec §7.2, §9)."
  alias Antigen.Challenge

  @elim_flags %{app: :app_present, case: :case_present, fst: :fst_present,
                snd: :snd_present, rewrite: :rewrite_present}

  @spec key(Challenge.t()) :: {MapSet.t(atom()), atom(), MapSet.t(atom()), Challenge.label()}
  def key(%Challenge{} = c) do
    terms = terms_of(c)
    ctors = terms |> Enum.flat_map(&constructors/1) |> MapSet.new()
    depth = terms |> Enum.map(&depth/1) |> Enum.max(fn -> 0 end)
    flags = flags(c, terms, ctors)
    {ctors, bucket(depth), flags, c.label}
  end

  @spec key_string({MapSet.t(), atom(), MapSet.t(), atom()}) :: String.t()
  def key_string({ctors, bucket, flags, label}) do
    cs = ctors |> Enum.sort() |> Enum.join(",")
    fs = flags |> Enum.sort() |> Enum.join(",")
    "ctors=[#{cs}]|depth=#{bucket}|flags=[#{fs}]|label=#{label}"
  end

  @spec terms_of(Challenge.t()) :: [Cure.Core.Term.t()]
  def terms_of(%Challenge{kind: :stub, payload: %{term: t}}), do: [t]
  # Phase 2 adds :def_group / :family / :forcing_pair clauses (Tasks 9–11).

  defp bucket(d) when d <= 2, do: :b0_2
  defp bucket(d) when d <= 5, do: :b3_5
  defp bucket(d) when d <= 9, do: :b6_9
  defp bucket(_), do: :b10p

  defp flags(%Challenge{kind: kind}, terms, ctors) do
    base = for {c, flag} <- @elim_flags, MapSet.member?(ctors, c), into: MapSet.new(), do: flag
    base = if kind in [:def_group, :forcing_pair], do: MapSet.put(base, :has_mutual_group), else: base
    base = if Enum.any?(terms, &has_shadowing?/1), do: MapSet.put(base, :has_shadowing), else: base
    base
  end

  # `:has_shadowing` (spec §7.2): a coarse approximation — any `:lam`/`:pi`/`:sigma`
  # binder nested underneath another such binder. A single top-level binder does
  # not count; only nesting (e.g. a curried `{:pi, _, {:pi, _, _}}`) does.
  defp has_shadowing?(t), do: nested_binder?(t, false)

  defp nested_binder?(t, inside?) when is_tuple(t) do
    tag = elem(t, 0)
    binder? = tag in [:lam, :pi, :sigma]
    here = binder? and inside?
    children = t |> Tuple.to_list() |> tl()
    here or Enum.any?(children, fn c -> nested_binder?(c, inside? or binder?) end)
  end
  defp nested_binder?(list, inside?) when is_list(list), do: Enum.any?(list, &nested_binder?(&1, inside?))
  defp nested_binder?(_, _), do: false

  # structural helpers over the tagged-tuple AST
  defp constructors(t), do: fold(t, [], fn node, acc -> [tag(node) | acc] end) |> Enum.reject(&is_nil/1)
  defp depth(t), do: fold_depth(t)
  defp tag(t) when is_tuple(t), do: elem(t, 0)
  defp tag(_), do: nil

  defp fold(t, acc, f) when is_tuple(t) do
    acc = f.(t, acc)
    t |> Tuple.to_list() |> Enum.reduce(acc, fn child, a -> fold(child, a, f) end)
  end
  defp fold(list, acc, f) when is_list(list), do: Enum.reduce(list, acc, fn c, a -> fold(c, a, f) end)
  defp fold(_leaf, acc, _f), do: acc

  # A node's depth is 1 + the max depth of its *term-shaped* children (nested
  # tuples/lists); non-term children (the leading tag atom, bare integers/de
  # Bruijn indices, plain atoms) don't count, so a primitive leaf like
  # `{:type, 0}` or `{:var, 0}` has depth 0, not 1 — verified against the
  # Step-1 fixtures: `{:app, {:lam, {:type,0}, {:var,0}}, {:type,0}}` computes
  # to depth 2 (bucket `:b0_2`, matching the first test) and the four-`:app`
  # `deep` fixture in the third test computes to depth 3 (bucket `:b3_5`).
  defp fold_depth(t) when is_tuple(t) do
    child_depths =
      t
      |> Tuple.to_list()
      |> Enum.filter(&(is_tuple(&1) or is_list(&1)))
      |> Enum.map(&fold_depth/1)

    case child_depths do
      [] -> 0
      ds -> 1 + Enum.max(ds)
    end
  end
  defp fold_depth(list) when is_list(list), do: Enum.max([0 | Enum.map(list, &fold_depth/1)])
  defp fold_depth(_), do: 0
end
```

*Note:* the atom-tag first element (`:app`, `:var`, …) is itself a tuple element but is not a tuple, so `constructors/1`'s `tag/1` (called only on the node `t` itself during `fold`, never on `t`'s individual elements) only records tuple heads — the `ctors` set correctly excludes bare atoms and the de Bruijn index `0`. `fold_depth`'s explicit `is_tuple/is_list` filter (above) similarly keeps primitive payload (atoms, integers) from inflating depth.

- [ ] **Step 4: Run it, verify it passes**

Run: `mix test test/antigen/coverage_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/coverage.ex test/antigen/coverage_test.exs
git commit -m "feat(antigen): plateauing coverage-key feature vector"
```

### Task 5: `Antigen.Corpus` — record envelope, decode, dedup, append, replay

**Files:**
- Create: `lib/antigen/corpus.ex`
- Test: `test/antigen/corpus_test.exs`

**Interfaces:**
- Consumes: `Antigen.Challenge` (Task 1), `Coverage.key_string/1` (Task 4), `Cure.Core.Serialize` (`encode/1`, `decode/1`).
- Produces:
  - `Corpus.encode_record(Challenge.t()) :: String.t()` — one newline-free line.
  - `Corpus.decode_record(String.t()) :: {:ok, Challenge.t()} | {:error, term()}`.
  - `Corpus.append(path, Challenge.t(), dedup_key :: String.t()) :: :appended | :duplicate` — atomic single-write append, idempotent on `dedup_key`.
  - `Corpus.stream(path) :: Enumerable.t({:ok, Challenge.t()} | {:decode_error, line})` — one entry per line, decode errors surfaced not raised (spec §7.1).
  - `Corpus.dedup_key(Challenge.t(), :antibody | :seed) :: String.t()` — antibody key = canonical encode of `(assay, terms)`; seed key = `Coverage.key_string`.
  - `Corpus.encode_scaffold(map()) :: String.t()` / `Corpus.decode_scaffold(String.t()) :: map()` — the generic (non-`Term`) metadata channel. Phase 1's only scaffold value is `%{}`; Phase 2 (Tasks 9–11) populate it with plain data (atoms, integers, lists/maps thereof) that isn't itself a `Cure.Core.Term.t()` — e.g. `:def_group`'s `focus` name list. **This is decided now, not deferred**: the record grammar gets its `scaffold=` field in this task so Phase 2 never has to touch `corpus.ex` or change the on-disk grammar (spec §7.1 "fixed now, stable forever").

Record grammar (fixed now, stable forever — spec §7.1). One line, a tab-separated envelope where the last field carries the term pieces so `Serialize`'s space-delimited s-exprs never collide with the field delimiter:

```
antigen-record\tkind=<kind>\tassay=<assay>\tlabel=<label>\tseed=<seed|->\tnote=<b64|->\tscaffold=<b64|->\tkey=<dedup_key_b64>\tpieces=<piece1>;;<piece2>;;...
```

Each `<piece>` is `<piece_id>::<base64(Serialize.encode(term))>`. Base64 guarantees no `\t`, `;;`, or `::` inside a piece. Phase-1 stub emits a single piece `term::<...>`; Phase 2 emits `type:f`, `body:f`, … via `Challenge.to_pieces/1` (added in Task 9). Corpus delegates challenge↔pieces to `Antigen.Challenge` so the envelope never hard-codes kinds. `scaffold=-` means an empty map (Phase-1's only case); otherwise it's `Base.encode64(:erlang.term_to_binary(scaffold))`, decoded with `:erlang.binary_to_term(bin, [:safe])` — **`[:safe]` refuses to create new atoms**, so any atom a scaffold carries (e.g. a generated def/family name like `:f`/`:g`) must already exist in the atom table at decode time. Concretely: Phase 2 generators (Tasks 9–11) must draw def/family/ctor names from a small **fixed, literal, closed set hardcoded in the generator module's source** (so the atoms exist the moment the module is compiled/loaded) — never mint them dynamically via `String.to_atom/1` at generation time, or a fresh process replaying a committed corpus (one that never ran the generator) will crash decoding a perfectly valid record.

**Add to `Antigen.Challenge` (Task 1 module) the piece bridge** — implement here as part of this task since Corpus needs it:
- `Challenge.to_pieces(Challenge.t()) :: {scaffold :: map(), [{piece_id :: String.t(), Term.t()}]}` — Phase-1: `{%{}, [{"term", term}]}` for `:stub`.
- `Challenge.from_pieces(kind, assay, label, seed, note, scaffold, pieces) :: Challenge.t()` — Phase-1: rebuild `:stub`.

- [ ] **Step 1: Write the failing test**

```elixir
# test/antigen/corpus_test.exs
defmodule Antigen.CorpusTest do
  use ExUnit.Case, async: true
  alias Antigen.{Challenge, Corpus}

  @tmp "tmp/antigen_test"

  setup do
    File.rm_rf!(@tmp); File.mkdir_p!(@tmp)
    on_exit(fn -> File.rm_rf!(@tmp) end)
    :ok
  end

  test "encode → decode round-trips a stub challenge identically (C2 stability)" do
    c = Challenge.new(kind: :stub, assay: "stub", label: :none,
                      payload: %{term: {:app, {:lam, {:type, 0}, {:var, 0}}, {:type, 0}}}, seed: 42, note: "hi")
    line = Corpus.encode_record(c)
    refute String.contains?(line, "\n")
    assert {:ok, c2} = Corpus.decode_record(line)
    assert c2.payload.term == c.payload.term
    assert c2.assay == "stub" and c2.seed == 42 and c2.note == "hi"
  end

  test "append is idempotent on the dedup key" do
    path = Path.join(@tmp, "corpus.sexp")
    c = Challenge.stub({:type, 0})
    key = Corpus.dedup_key(c, :antibody)
    assert :appended == Corpus.append(path, c, key)
    assert :duplicate == Corpus.append(path, c, key)
    assert File.read!(path) |> String.split("\n", trim: true) |> length() == 1
  end

  test "stream surfaces a decode error as a distinct entry and keeps going" do
    path = Path.join(@tmp, "corpus.sexp")
    Corpus.append(path, Challenge.stub({:type, 0}), Corpus.dedup_key(Challenge.stub({:type, 0}), :antibody))
    File.write!(path, File.read!(path) <> "this-is-not-a-record\n")
    results = Corpus.stream(path) |> Enum.to_list()
    assert Enum.any?(results, &match?({:ok, %Challenge{}}, &1))
    assert Enum.any?(results, &match?({:decode_error, _}, &1))
  end

  test "scaffold round-trips non-Term metadata through the record line (proves Phase-2 def_group/family carry-through)" do
    scaffold = %{"focus" => ["f", "g"], "arity" => 2}
    line = Corpus.encode_scaffold(scaffold)
    refute String.contains?(line, "\t") or String.contains?(line, "\n")
    assert Corpus.decode_scaffold(line) == scaffold
  end

  test "an empty scaffold encodes to the `-` sentinel and decodes back to an empty map" do
    assert Corpus.encode_scaffold(%{}) == "-"
    assert Corpus.decode_scaffold("-") == %{}
  end
end
```

- [ ] **Step 2: Run it, verify it fails**

Run: `mix test test/antigen/corpus_test.exs`
Expected: FAIL — `Antigen.Corpus` undefined.

- [ ] **Step 3: Implement the corpus + challenge piece bridge**

Add to `lib/antigen/challenge.ex`:

```elixir
  @spec to_pieces(t()) :: {map(), [{String.t(), Cure.Core.Term.t()}]}
  def to_pieces(%__MODULE__{kind: :stub, payload: %{term: t}}), do: {%{}, [{"term", t}]}

  @spec from_pieces(atom(), String.t(), atom(), integer() | nil, String.t() | nil, map(), [{String.t(), Cure.Core.Term.t()}]) :: t()
  def from_pieces(:stub, assay, label, seed, note, _scaffold, [{"term", t}]),
    do: new(kind: :stub, assay: assay, label: label, payload: %{term: t}, seed: seed, note: note)
```

Then `lib/antigen/corpus.ex`:

```elixir
defmodule Antigen.Corpus do
  @moduledoc "Committed, never-pruned, generator-independent stores (spec §7). Replay runs the kernel, not the generator."
  alias Antigen.{Challenge, Coverage}
  alias Cure.Core.Serialize

  @marker "antigen-record"

  @spec encode_record(Challenge.t()) :: String.t()
  def encode_record(%Challenge{} = c) do
    {scaffold, pieces} = Challenge.to_pieces(c)
    piece_str = pieces |> Enum.map(fn {id, t} -> "#{id}::#{Base.encode64(Serialize.encode(t))}" end) |> Enum.join(";;")
    key = dedup_key(c, if(c.kind == :stub, do: :antibody, else: :antibody))
    Enum.join([
      @marker, "kind=#{c.kind}", "assay=#{c.assay}", "label=#{c.label}",
      "seed=#{c.seed || "-"}", "note=#{enc_opt(c.note)}", "scaffold=#{encode_scaffold(scaffold)}",
      "key=#{Base.encode64(key)}", "pieces=#{piece_str}"
    ], "\t")
  end

  @spec decode_record(String.t()) :: {:ok, Challenge.t()} | {:error, term()}
  def decode_record(line) do
    with [@marker | fields] <- String.split(String.trim_trailing(line, "\n"), "\t"),
         m <- Map.new(fields, fn f -> List.to_tuple(String.split(f, "=", parts: 2)) end),
         {:ok, pieces} <- decode_pieces(m["pieces"]) do
      kind = String.to_existing_atom(m["kind"])
      label = String.to_existing_atom(m["label"])
      seed = if m["seed"] == "-", do: nil, else: String.to_integer(m["seed"])
      scaffold = decode_scaffold(m["scaffold"] || "-")
      {:ok, Challenge.from_pieces(kind, m["assay"], label, seed, dec_opt(m["note"]), scaffold, pieces)}
    else
      other -> {:error, {:bad_record, other}}
    end
  rescue
    e -> {:error, e}
  end

  @doc "Encode arbitrary (non-Term) challenge metadata for the `scaffold=` field. `%{}` → `\"-\"`."
  @spec encode_scaffold(map()) :: String.t()
  def encode_scaffold(scaffold) when scaffold == %{}, do: "-"
  def encode_scaffold(scaffold), do: Base.encode64(:erlang.term_to_binary(scaffold))

  @doc "Decode the `scaffold=` field. `:safe` refuses to mint new atoms on decode — see the safety note above."
  @spec decode_scaffold(String.t()) :: map()
  def decode_scaffold("-"), do: %{}
  def decode_scaffold(b64), do: :erlang.binary_to_term(Base.decode64!(b64), [:safe])

  @spec append(String.t(), Challenge.t(), String.t()) :: :appended | :duplicate
  def append(path, %Challenge{} = c, dedup_key) do
    File.mkdir_p!(Path.dirname(path))
    if seen?(path, dedup_key) do
      :duplicate
    else
      # single append syscall — atomic per record (spec §7.1)
      File.write!(path, encode_record(c) <> "\n", [:append])
      :appended
    end
  end

  @spec stream(String.t()) :: Enumerable.t()
  def stream(path) do
    if File.exists?(path) do
      path |> File.stream!() |> Stream.map(fn line ->
        case decode_record(line) do
          {:ok, c} -> {:ok, c}
          {:error, _} -> {:decode_error, String.trim(line)}
        end
      end)
    else
      []
    end
  end

  @spec dedup_key(Challenge.t(), :antibody | :seed) :: String.t()
  def dedup_key(%Challenge{} = c, :seed), do: Coverage.key_string(Coverage.key(c))
  def dedup_key(%Challenge{assay: a} = c, :antibody) do
    {_s, pieces} = Challenge.to_pieces(c)
    a <> "|" <> (pieces |> Enum.map(fn {id, t} -> id <> Serialize.encode(t) end) |> Enum.join("|"))
  end

  defp seen?(path, key) do
    File.exists?(path) and
      (path |> File.stream!() |> Enum.any?(fn line -> extract_key(line) == key end))
  end

  defp extract_key(line) do
    line |> String.split("\t") |> Enum.find_value(fn f ->
      case String.split(f, "=", parts: 2) do
        ["key", b64] -> Base.decode64!(String.trim(b64))
        _ -> nil
      end
    end)
  rescue
    _ -> nil
  end

  defp decode_pieces(nil), do: {:error, :no_pieces}
  defp decode_pieces(""), do: {:ok, []}
  defp decode_pieces(str) do
    str |> String.split(";;") |> Enum.reduce_while({:ok, []}, fn piece, {:ok, acc} ->
      case String.split(piece, "::", parts: 2) do
        [id, b64] ->
          case Serialize.decode(Base.decode64!(b64)) do
            {:ok, t} -> {:cont, {:ok, [{id, t} | acc]}}
            err -> {:halt, err}
          end
        _ -> {:halt, {:error, {:bad_piece, piece}}}
      end
    end)
    |> case do
      {:ok, ps} -> {:ok, Enum.reverse(ps)}
      err -> err
    end
  end

  defp enc_opt(nil), do: "-"
  defp enc_opt(s), do: Base.encode64(s)
  defp dec_opt("-"), do: nil
  defp dec_opt(b64), do: Base.decode64!(b64)
end
```

*Note on dedup key in `encode_record`:* the antibody vs. seed choice is passed by the caller (Runner, Task 7), not inferred here — refactor `encode_record` to accept the precomputed key from the caller if the Step-1 tests reveal the inline `dedup_key` call is wrong for seeds. Keep the stored `key=` field equal to whatever key the append used.

- [ ] **Step 4: Run it, verify it passes**

Run: `mix test test/antigen/corpus_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/corpus.ex lib/antigen/challenge.ex test/antigen/corpus_test.exs
git commit -m "feat(antigen): corpus record envelope, atomic append, dedup, fault-tolerant replay stream"
```

### Task 6: `Antigen.Report` — tmp reports + stdout breadcrumb

**Files:**
- Create: `lib/antigen/report.ex`
- Test: `test/antigen/report_test.exs`

**Interfaces:**
- Consumes: `Antigen.Challenge` (Task 1), `Coverage` (Task 4).
- Produces: `Report.write_infection(dir, Challenge.t(), detail :: term(), health :: map()) :: {:ok, path}` — writes `dir/failure-<seed>-<assay_slug>-<n>.txt` AND updates `dir/latest.txt`, **flushing to disk before returning** (spec §10). `Report.breadcrumb(Challenge.t(), path) :: String.t()` — one grep-surviving stdout line.

- [ ] **Step 1: Write the failing test**

```elixir
# test/antigen/report_test.exs
defmodule Antigen.ReportTest do
  use ExUnit.Case, async: true
  alias Antigen.{Challenge, Report}

  @tmp "tmp/antigen_report_test"
  setup do
    File.rm_rf!(@tmp); on_exit(fn -> File.rm_rf!(@tmp) end); :ok
  end

  test "write_infection writes a full report and updates latest.txt before returning" do
    c = Challenge.new(kind: :stub, assay: "totality/diverging", label: :diverging, payload: %{term: {:type, 0}}, seed: 12345)
    assert {:ok, path} = Report.write_infection(@tmp, c, {:violation, :wrongly_certified}, %{discard_rate: 0.0})
    assert File.exists?(path)
    body = File.read!(path)
    assert body =~ "totality/diverging"
    assert body =~ "12345"
    assert body =~ "wrongly_certified"
    assert File.read!(Path.join(@tmp, "latest.txt")) =~ Path.basename(path)
  end

  test "breadcrumb is a single grep-surviving line naming the assay, seed, and file" do
    c = Challenge.new(kind: :stub, assay: "totality/diverging", label: :diverging, payload: %{term: {:type, 0}}, seed: 999)
    line = Report.breadcrumb(c, "tmp/antigen/failure-999-totality_diverging-1.txt")
    refute line =~ "\n"
    assert line =~ "ANTIGEN INFECTION" and line =~ "totality/diverging" and line =~ "seed=999"
  end
end
```

- [ ] **Step 2: Run it, verify it fails**

Run: `mix test test/antigen/report_test.exs`
Expected: FAIL — `Antigen.Report` undefined.

- [ ] **Step 3: Implement reporting** (compute a fresh `<n>` per `(seed, assay)`, pretty-print the challenge, embed the C2 pieces and a decode-and-run repro snippet; `File.write!` then it is flushed on return).

```elixir
# lib/antigen/report.ex
defmodule Antigen.Report do
  @moduledoc "Ephemeral full failure reports; never lose a failure to a filtered pipe (spec §10, umbrella §8.1)."
  alias Antigen.{Challenge, Corpus}

  @spec write_infection(String.t(), Challenge.t(), term(), map()) :: {:ok, String.t()}
  def write_infection(dir, %Challenge{} = c, detail, health) do
    File.mkdir_p!(dir)
    slug = slug(c.assay)
    n = next_index(dir, c.seed, slug)
    path = Path.join(dir, "failure-#{c.seed}-#{slug}-#{n}.txt")
    File.write!(path, render(c, detail, health))
    File.write!(Path.join(dir, "latest.txt"), Path.basename(path))
    {:ok, path}
  end

  @spec breadcrumb(Challenge.t(), String.t()) :: String.t()
  def breadcrumb(%Challenge{} = c, path),
    do: "ANTIGEN INFECTION [#{c.assay}] seed=#{c.seed} → #{path}"

  defp render(c, detail, health) do
    """
    ANTIGEN INFECTION
    assay:      #{c.assay}
    label:      #{c.label}  (ground truth)
    seed:       #{c.seed}
    detail:     #{inspect(detail)}
    health:     #{inspect(health)}
    note:       #{c.note}

    -- antigen (C2 record, generator-independent repro) --
    #{Corpus.encode_record(c)}

    -- repro --
    decode the record above and run Antigen.Runner.replay_one/1
    """
  end

  defp slug(assay), do: String.replace(assay, ~r/[^a-zA-Z0-9]+/, "_")

  defp next_index(dir, seed, slug) do
    existing = Path.wildcard(Path.join(dir, "failure-#{seed}-#{slug}-*.txt"))
    length(existing) + 1
  end
end
```

- [ ] **Step 4: Run it, verify it passes**

Run: `mix test test/antigen/report_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/report.ex test/antigen/report_test.exs
git commit -m "feat(antigen): failure reports flushed before stdout + breadcrumb"
```

### Task 7: `Antigen.Runner` — explore / generate / replay + a stub assay/generator

**Files:**
- Create: `lib/antigen/runner.ex`
- Create: `lib/antigen/assays/stub.ex`
- Create: `lib/antigen/generators/stub.ex`
- Test: `test/antigen/runner_test.exs`

**Interfaces:**
- Consumes: `Backend.StreamData` (Task 3), `Corpus` (Task 5), `Report` (Task 6), `Coverage` (Task 4).
- Produces:
  - `Runner.explore(opts) :: %{infections: non_neg_integer(), seeds_banked: non_neg_integer(), health: map()}` — generate + assay + bank; keeps going on infection (spec §8). `opts`: `:count` (rounds, default 200), `:gen`, `:assay`, `:corpus_path`, `:seeds_path`, `:report_dir`.
  - `Runner.generate(opts) :: %{seeds_banked: non_neg_integer()}` — harvest-only; skips assays; runs until `:count` or an injected `:until` predicate (the SIGTERM trap for a clean summary lives in the Mix task, Task 8 — the runner takes a bounded count so it is unit-testable; Ctrl+C/SIGINT is not application-interceptable and simply kills the VM, which is safe since every record is already durably appended — see Task 8).
  - `Runner.replay(paths, assays) :: [%{entry: term(), verdict: :ok | {:violation, term()} | {:decode_error, String.t()}}]` — read-only, non-fail-fast over both stores (spec §8 replayer).
  - `Runner.replay_one(Challenge.t()) :: :ok | {:violation, term()}` — dispatch one challenge to its assay by `assay` id.
- Produces (stub): `Antigen.Assays.Stub.run(Challenge.t()) :: :ok | {:violation, term()}` — violates iff the term is exactly `{:global, :boom}` (a deterministic fake infection to exercise the pipeline). `Antigen.Generators.Stub.gen() :: Gen.t()` — yields stub challenges, occasionally the `:boom` one.

The assay dispatch table maps `assay` string → module; Phase 2 registers the real four. Stub proves the loop end-to-end.

- [ ] **Step 1: Write the failing test**

```elixir
# test/antigen/runner_test.exs
defmodule Antigen.RunnerTest do
  use ExUnit.Case, async: true
  alias Antigen.{Runner, Challenge, Generators, Assays}

  @tmp "tmp/antigen_runner_test"
  setup do
    File.rm_rf!(@tmp); File.mkdir_p!(@tmp); on_exit(fn -> File.rm_rf!(@tmp) end)
    [opts: [gen: Generators.Stub.gen(), assay: Assays.Stub,
            corpus_path: Path.join(@tmp, "corpus.sexp"),
            seeds_path: Path.join(@tmp, "seeds.sexp"),
            report_dir: @tmp, count: 300]]
  end

  test "explore harvests the planted infection, banks it, and keeps going", %{opts: opts} do
    result = Runner.explore(opts)
    assert result.infections >= 1
    assert File.exists?(opts[:corpus_path])
    assert Enum.any?(File.stream!(opts[:corpus_path]), &(&1 =~ "assay=stub"))
  end

  test "explore banks coverage-novel seeds and dedups repeats", %{opts: opts} do
    Runner.explore(opts)
    lines = File.stream!(opts[:seeds_path]) |> Enum.to_list()
    assert length(lines) == (lines |> Enum.uniq() |> length())  # no duplicate seed lines
  end

  test "generate harvests seeds without running any assay (no reports written)", %{opts: opts} do
    %{seeds_banked: n} = Runner.generate(opts)
    assert n >= 1
    refute File.exists?(Path.join(@tmp, "latest.txt"))  # assays skipped ⇒ no infection reports
  end

  test "replay re-runs the assay through the kernel and reports the planted violation", %{opts: opts} do
    boom = Challenge.new(kind: :stub, assay: "stub", label: :none, payload: %{term: {:global, :boom}}, seed: 1)
    Antigen.Corpus.append(opts[:corpus_path], boom, Antigen.Corpus.dedup_key(boom, :antibody))
    results = Runner.replay([opts[:corpus_path]], %{"stub" => Assays.Stub})
    assert Enum.any?(results, &match?(%{verdict: {:violation, _}}, &1))
  end
end
```

- [ ] **Step 2: Run it, verify it fails**

Run: `mix test test/antigen/runner_test.exs`
Expected: FAIL — modules undefined.

- [ ] **Step 3: Implement stub gen/assay + runner**

```elixir
# lib/antigen/generators/stub.ex
defmodule Antigen.Generators.Stub do
  @moduledoc "A trivial generator to exercise the harness end-to-end (Phase 1 only)."
  alias Antigen.{Gen, Challenge}
  def gen do
    Gen.frequency([
      {1, Gen.return(Challenge.new(kind: :stub, assay: "stub", label: :none, payload: %{term: {:global, :boom}}))},
      {9, Gen.bind(Gen.int(0, 3), fn n ->
        Gen.return(Challenge.new(kind: :stub, assay: "stub", label: :none, payload: %{term: {:var, n}}))
      end)}
    ])
  end
end
```

```elixir
# lib/antigen/assays/stub.ex
defmodule Antigen.Assays.Stub do
  @moduledoc "Fake assay: {:global, :boom} is the planted infection (Phase 1 only)."
  alias Antigen.Challenge
  def run(%Challenge{payload: %{term: {:global, :boom}}}), do: {:violation, :boom}
  def run(%Challenge{}), do: :ok
end
```

```elixir
# lib/antigen/runner.ex
defmodule Antigen.Runner do
  @moduledoc "Explore / generate / replay orchestration (spec §8)."
  alias Antigen.{Backend, Corpus, Report, Coverage, Challenge}

  def explore(opts) do
    count = Keyword.get(opts, :count, 200)
    challenges = draw(opts[:gen], count)
    Enum.reduce(challenges, %{infections: 0, seeds_banked: 0}, fn c, acc ->
      c = %{c | seed: seed_of(c)}
      acc = bank_seed(c, opts, acc)
      case apply(opts[:assay], :run, [c]) do
        :ok -> acc
        {:violation, detail} = v ->
          {:ok, path} = Report.write_infection(opts[:report_dir], c, v, health(acc))
          IO.puts(Report.breadcrumb(c, path))
          Corpus.append(opts[:corpus_path], c, Corpus.dedup_key(c, :antibody))
          _ = detail
          %{acc | infections: acc.infections + 1}
      end
    end)
    |> Map.put(:health, %{})
  end

  def generate(opts) do
    count = Keyword.get(opts, :count, 200)
    draw(opts[:gen], count)
    |> Enum.reduce(%{seeds_banked: 0}, fn c, acc -> bank_seed(%{c | seed: seed_of(c)}, opts, acc) end)
    |> Map.take([:seeds_banked])
  end

  def replay(paths, assays) do
    Enum.flat_map(paths, fn path ->
      Corpus.stream(path) |> Enum.map(fn
        {:ok, c} ->
          verdict = case Map.fetch(assays, c.assay) do
                      {:ok, mod} -> apply(mod, :run, [c])
                      :error -> {:violation, {:unknown_assay, c.assay}}
                    end
          %{entry: c, verdict: verdict}
        {:decode_error, line} -> %{entry: line, verdict: {:decode_error, line}}
      end)
    end)
  end

  def replay_one(%Challenge{assay: a} = c), do: apply(assay_module(a), :run, [c])

  # Phase 2 registers the real assay modules here.
  defp assay_module("stub"), do: Antigen.Assays.Stub

  defp bank_seed(c, opts, acc) do
    case Corpus.append(opts[:seeds_path], c, Corpus.dedup_key(c, :seed)) do
      :appended -> %{acc | seeds_banked: acc.seeds_banked + 1}
      :duplicate -> acc
    end
  end

  defp draw(gen, count), do: Backend.StreamData.interp(gen) |> Enum.take(count)
  defp seed_of(c), do: c.seed || :erlang.phash2({c.kind, c.payload})
  defp health(_acc), do: %{}
end
```

*Note:* `bank_seed` in `generate` accumulates only `:seeds_banked`; ensure it does not call any assay. The `seeds_banked` count reflects newly-appended (coverage-novel) seeds, not total drawn.

- [ ] **Step 4: Run it, verify it passes**

Run: `mix test test/antigen/runner_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/runner.ex lib/antigen/assays/stub.ex lib/antigen/generators/stub.ex test/antigen/runner_test.exs
git commit -m "feat(antigen): runner explore/generate/replay driven by a stub assay+generator"
```

### Task 8: `Mix.Tasks.Antigen` — `mix antigen [generate]` with SIGTERM-safe summary

**Files:**
- Create: `lib/mix/tasks/antigen.ex`
- Test: `test/antigen/mix_task_test.exs`

**Interfaces:**
- Consumes: `Antigen.Runner` (Task 7).
- Produces: `mix antigen` (explore; `--count N`, `--budget Nm` override the default rounds), `mix antigen generate` (harvest-only, runs until interrupted). Paths default to `test/antigen/corpus.sexp`, `test/antigen/seeds.sexp`, `tmp/antigen/`. `Mix.Tasks.Antigen.budget_to_count(String.t()) :: pos_integer()` — the pure `"Nm" -> round count` conversion (via the fixed rounds-per-minute constant), exposed and tested directly so `--budget`'s behavior has a red test independent of a real timed run.
- Signal handling (spec §8 crit. 5), corrected against the real API: **`System.trap_signal/2,3` cannot trap `:sigint`** — verified directly (`System.trap_signal(:sigint, fn -> :ok end)` raises `FunctionClauseError`; the only signals accepted are `:sigquit`, `:sigterm`, `:sigusr1`, `:sighup`, `:sigabrt`, `:sigalrm`, `:sigusr2`, `:sigchld`, `:sigstop`, `:sigtstp`). Ctrl+C (SIGINT) delivered to a `-noshell` `mix` invocation terminates the VM directly and is not interceptable at the application level. This is safe because `Corpus.append` already performs a synchronous, atomic, per-record write (Task 5) — every banked seed or antibody is durable on disk the instant it's appended, so an untrapped SIGINT loses at most the in-flight record, never a previously-appended one, and there is no buffered state to flush. Trap `:sigterm` only (via `System.trap_signal/2`) so an operator-issued `kill -TERM` (or a supervising process) gets a clean final summary line instead of an abrupt exit; do not claim SIGINT is trapped anywhere in code, docs, or the task's moduledoc.

- [ ] **Step 1: Write the failing test**

```elixir
# test/antigen/mix_task_test.exs
defmodule Mix.Tasks.AntigenTest do
  use ExUnit.Case, async: false
  import ExUnit.CaptureIO

  @tmp "tmp/antigen_task_test"
  setup do
    File.rm_rf!(@tmp); File.mkdir_p!(@tmp); on_exit(fn -> File.rm_rf!(@tmp) end); :ok
  end

  test "mix antigen --count runs the explorer and prints a summary" do
    out = capture_io(fn ->
      Mix.Tasks.Antigen.run(["--count", "50",
        "--corpus", Path.join(@tmp, "corpus.sexp"),
        "--seeds", Path.join(@tmp, "seeds.sexp"),
        "--report-dir", @tmp])
    end)
    assert out =~ "antigen" and (out =~ "infection" or out =~ "banked")
  end

  test "mix antigen generate --count harvests seeds and writes no infection reports" do
    Mix.Tasks.Antigen.run(["generate", "--count", "50",
      "--seeds", Path.join(@tmp, "seeds.sexp"), "--report-dir", @tmp])
    assert File.exists?(Path.join(@tmp, "seeds.sexp"))
    refute File.exists?(Path.join(@tmp, "latest.txt"))
  end

  test "budget_to_count converts minutes to a round count via the fixed rounds-per-minute constant" do
    one_minute = Mix.Tasks.Antigen.budget_to_count("1m")
    assert one_minute > 0
    assert Mix.Tasks.Antigen.budget_to_count("2m") == one_minute * 2
  end
end
```

- [ ] **Step 2: Run it, verify it fails**

Run: `mix test test/antigen/mix_task_test.exs`
Expected: FAIL — task undefined.

- [ ] **Step 3: Implement the Mix task** (parse args; dispatch to `Runner.explore/1` or `Runner.generate/1`; in `generate`, install a `:sigterm` trap via `System.trap_signal/2` that prints the summary and returns cleanly — do not attempt to trap `:sigint`, it is not a valid `System.trap_signal/2,3` signal; default the generator+assay to the Phase-1 stub, which Phase 2's Task 14 swaps for the real registry). Implement `budget_to_count/1` as a pure function (parse the leading integer off `"Nm"`, multiply by a `@rounds_per_minute` module attribute documented in the moduledoc) and route `--budget` through it before passing `:count` to `Runner.explore/1`/`generate/1`.

- [ ] **Step 4: Run it, verify it passes**

Run: `mix test test/antigen/mix_task_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/mix/tasks/antigen.ex test/antigen/mix_task_test.exs
git commit -m "feat(antigen): mix antigen [generate] task with SIGTERM-safe harvest summary"
```

**Phase 1 gate (run once, serially):** `mix test test/antigen/` — the whole harness is green end-to-end on the stub. Commit nothing new; this is a checkpoint.

---

## Phase 2 — schema-directed generators, real assays, fuel instrumentation

Replaces the stub with the three known-label generators, the four real assays, and the `Conv` fuel instrumentation the reflexivity assay needs. Completion satisfies success criteria #1–#3 (spec §2).

### Task 9: `Antigen.Generators.Totality` + `:def_group` challenge encoding

**Files:**
- Create: `lib/antigen/generators/totality.ex`
- Modify: `lib/antigen/challenge.ex` (add `:def_group` to `to_pieces`/`from_pieces`)
- Modify: `lib/antigen/coverage.ex` (add `terms_of` for `:def_group`)
- Test: `test/antigen/generators/totality_test.exs`

**Interfaces:**
- Consumes: `Antigen.Gen` (Task 2), `Cure.Core.{Term, Env}`.
- Produces: `Generators.Totality.gen(opts) :: Gen.t()` yielding `Challenge` of `kind: :def_group`, `label ∈ {:terminating, :diverging}`, `payload: %{defs: [%{name: atom, type: Term, body: Term}], focus: [atom]}` (`focus` = the names whose termination the assay checks — all group members). `Generators.Totality.env_of(Challenge.t()) :: Env.t()` — rebuild the `Env` by folding `Env.add_def/4` over `payload.defs`.
- `:def_group` piece encoding: pieces `type:<name>` and `body:<name>` per def (names as strings, e.g. `type:f`/`body:f`); scaffold `%{"names" => ["f", "g", ...], "focus" => ["f", "g", ...]}` (string names, not atoms — decoded with `String.to_existing_atom/1` in `from_pieces`, same safety discipline as the record envelope's `kind`/`label` fields, Task 5). The record's `scaffold=` field already exists (added generically in Task 5) — this task only needs to change `Challenge.to_pieces/from_pieces`; **`lib/antigen/corpus.ex` is not touched, and the on-disk grammar does not change.** Per Task 5's safety note, `diverging_mutual_pair/0` and `structural_terminating/0` (below) must use fixed literal atoms (`:f`, `:g`, …) — never `String.to_atom/1` on generator-time data.

**Label correctness is the oracle (spec §5, umbrella §6) — the generator self-test (Task 12) is non-optional.** Generation shapes:
- `:terminating` — non-recursive; single structural-recursion defs (self-call on a `{:var, _}` bound by a `case` branch at the guarded position); well-founded mutual groups (even/odd) whose cross-calls pass a structural subterm.
- `:diverging` — direct self-loop with a non-decreasing arg; **mutual `f→g→f` with non-decreasing args (the confirmed hole)**; non-structural recursion.

- [ ] **Step 1: Write the failing test** (assert the generator emits, for a fixed seed/opts, a `:diverging` mutual pair whose two bodies are `{:global, :g}`-headed / `{:global, :f}`-headed, and that `env_of` rebuilds an `Env` where `Env.get_def(env, :f).body` calls `{:global, :g}`; assert a `:terminating` structural def calls itself on a `case`-bound var; assert the `:def_group` challenge round-trips through `Corpus.encode_record/1` + `Corpus.decode_record/1` with `focus` intact — this is the concrete proof that Task 5's generic scaffold plumbing actually carries `:def_group` metadata, closing the loop flagged in Task 5).

```elixir
# test/antigen/generators/totality_test.exs
defmodule Antigen.Generators.TotalityTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.Totality
  alias Antigen.Corpus
  alias Cure.Core.Env

  test "emits the confirmed diverging mutual cycle f→g→f as a labeled challenge" do
    c = Totality.diverging_mutual_pair()   # deterministic constructor used by the gen + self-tests
    assert c.label == :diverging and c.kind == :def_group
    env = Totality.env_of(c)
    assert %{body: bf} = Env.get_def(env, :f)
    assert %{body: bg} = Env.get_def(env, :g)
    assert calls_global?(bf, :g)   # f's body references g
    assert calls_global?(bg, :f)   # g's body references f
  end

  test "emits a terminating structural def labeled :terminating" do
    c = Totality.structural_terminating()
    assert c.label == :terminating
  end

  test "a :def_group challenge's focus list survives a corpus encode/decode round trip" do
    c = Totality.diverging_mutual_pair()
    line = Corpus.encode_record(c)
    assert {:ok, c2} = Corpus.decode_record(line)
    assert Enum.sort(c2.payload.focus) == Enum.sort(c.payload.focus)
    assert Map.keys(Totality.env_of(c2).defs) |> Enum.sort() == Map.keys(Totality.env_of(c).defs) |> Enum.sort()
  end

  defp calls_global?({:global, n}, n), do: true
  defp calls_global?(t, n) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&calls_global?(&1, n))
  defp calls_global?(l, n) when is_list(l), do: Enum.any?(l, &calls_global?(&1, n))
  defp calls_global?(_, _), do: false
end
```

- [ ] **Step 2: Run it, verify it fails** — `mix test test/antigen/generators/totality_test.exs` → FAIL.
- [ ] **Step 3: Implement the generator** (the deterministic constructors `diverging_mutual_pair/0`, `structural_terminating/0` used by both `gen/1` and the self-tests; `gen/1` composes them and parametric variants via `Antigen.Gen`; `env_of/1` folds `Env.add_def/4`; extend `Challenge.to_pieces/from_pieces` and `Coverage.terms_of` for `:def_group`). Show the exact Core terms for `f (S y) = g y` / `g y = f (S y)` using `{:global, ...}`, `{:ctor, :s, [...]}`, `{:case, ...}`.
- [ ] **Step 4: Run it, verify it passes.**
- [ ] **Step 5: Commit** — `feat(antigen): totality generator (known-label terminating/diverging def groups)`.

### Task 10: `Antigen.Generators.Positivity` + `:family` challenge encoding

**Files:**
- Create: `lib/antigen/generators/positivity.ex`
- Modify: `lib/antigen/challenge.ex`, `lib/antigen/coverage.ex` (`:family` clauses)
- Test: `test/antigen/generators/positivity_test.exs`

**Interfaces:**
- Consumes: `Cure.Core.Inductive` (`family/4`, `ctor/3,4`, `declare/3`).
- Produces: `Generators.Positivity.gen(opts) :: Gen.t()` yielding `kind: :family`, `label ∈ {:positive, :negative}`, `payload: %{family: Inductive.family(), ctors: [Inductive.ctor()]}`. `Generators.Positivity.env_of(Challenge.t()) :: Env.t()` via `Inductive.declare/3`. Deterministic constructors `positive_family/0`, `negative_family/0` (a recursive occurrence left of an arrow in a ctor arg type) for the self-tests.
- `:family` pieces: encode each telescope entry's `Term` and each `result_index` `Term` as pieces, with a scaffold recording binder-name **strings** (decoded via `String.to_existing_atom/1`, same discipline as Task 9's `:def_group` names — never `String.to_atom/1`), arities (integers), and quantities (`"erased"`/`"present"` strings mapped back to the fixed `:erased`/`:present` atoms). As with Task 9, this reuses the `scaffold=` field Task 5 already added — `lib/antigen/corpus.ex` is not touched.

- [ ] **Step 1: Write the failing test** (assert `negative_family/0` is labeled `:negative` and, when declared, `Inductive.positive?(env, family)` returns `{:error, {:non_strictly_positive, _}}`; `positive_family/0` labeled `:positive` and `positive?` returns `:ok` — this cross-checks the generator's label against the real checker on the *known-good* set; assert both challenges round-trip through `Corpus.encode_record/1` + `Corpus.decode_record/1` with the family's telescope/ctor structure intact, i.e. `Inductive.positive?/2`'s verdict on the decoded challenge's `env_of/1` matches the original).
- [ ] **Step 2: Run it, verify it fails.**
- [ ] **Step 3: Implement** (the two deterministic families with explicit `Inductive.family/4` + `Inductive.ctor/3,4` terms; `gen/1`; `env_of/1`; challenge + coverage clauses).
- [ ] **Step 4: Run it, verify it passes.**
- [ ] **Step 5: Commit** — `feat(antigen): positivity generator (±strictly-positive families)`.

### Task 11: `Antigen.Generators.Forcing` + `:forcing_pair` challenge encoding

**Files:**
- Create: `lib/antigen/generators/forcing.ex`
- Modify: `lib/antigen/challenge.ex`, `lib/antigen/coverage.ex` (`:forcing_pair` clauses)
- Test: `test/antigen/generators/forcing_test.exs`

**Interfaces:**
- Consumes: `Generators.Totality` (Task 9), `Cure.Core.{Term, Env, Certificate}`.
- Produces: `Generators.Forcing.gen(opts) :: Gen.t()` yielding `kind: :forcing_pair`, `label: :diverging`, `payload: %{defs: [...], focus: [atom], t: Term, tprime: Term}`. `Generators.Forcing.certified_env_of(Challenge.t()) :: Env.t()` — folds `Env.add_def/4`, then **runs the real certifier** (`Certificate.terminating?(name, Env.get_def(env,name).body)` per member; on the wrong `true`, `Env.certify(env, name)`), reproducing the hole's effect (spec §5.3). Deterministic `forcing_pair/0` constructor for the self-test.
- `t = {:app, {:global, :f}, n}`; `t' =` one manual β/ι step of `f`'s body applied to `n`, landing head `{:global, :g}` — built with `Term.subst/3` (β) and a direct `case`-branch selection (ι), with `n` chosen so the one step reaches the `g`-calling branch. **`t` and `t'` must be structurally distinct** (guards against the `same_neutral_no_delta?` short-circuit, spec §4.3).
- `:forcing_pair` piece/scaffold encoding reuses Task 9's `:def_group` convention for `defs`/`focus` (`type:<name>`/`body:<name>` pieces, string `"names"`/`"focus"` scaffold entries), plus two more pure-term pieces `t`/`tprime`. No new corpus-envelope work: same `scaffold=` field from Task 5, still untouched `lib/antigen/corpus.ex`.

- [ ] **Step 1: Write the failing test** (assert `t != tprime`; assert `tprime` is headed by `{:global, :g}` and `t` by `{:global, :f}`; assert `certified_env_of/1` yields an env where `Env.certified?(env, :f)` is `true` — i.e. the certifier wrongly certified it).
- [ ] **Step 2: Run it, verify it fails.**
- [ ] **Step 3: Implement** (the exact `t`, `t'` Core terms via `Term.subst/3`; `certified_env_of/1`; challenge + coverage clauses).
- [ ] **Step 4: Run it, verify it passes.**
- [ ] **Step 5: Commit** — `feat(antigen): forcing generator (structurally-distinct δ-forcing term pair)`.

### Task 12: Generator self-tests + architecture test + support-set characterization

**Files:**
- Create: `test/antigen/architecture_test.exs`
- Create: `test/antigen/generators/self_test.exs`

**Interfaces:**
- Consumes: all three generators (Tasks 9–11), `Cure.Core.{Certificate, Inductive}`.

This task is **all tests** (the artifact is the generators' correctness proof — they are the oracle, spec §5, §12). No new lib code; if a self-test fails, fix the *generator* from the relevant Task, not the test.

- [ ] **Step 1: Write the architecture test**

```elixir
# test/antigen/architecture_test.exs
defmodule Antigen.ArchitectureTest do
  use ExUnit.Case, async: true

  test "no Generators.* or Assays.* source references StreamData" do
    offenders =
      Path.wildcard("lib/antigen/{generators,assays}/**/*.ex")
      |> Enum.filter(fn f -> File.read!(f) =~ ~r/\bStreamData\b/ end)
    assert offenders == [], "StreamData leaked into: #{inspect(offenders)}"
  end
end
```

- [ ] **Step 2: Run it** — `mix test test/antigen/architecture_test.exs` → PASS (should already hold; it guards regressions).
- [ ] **Step 3: Write the generator self-tests** — for Totality: every `:terminating` sample from a fixed known-good set is accepted by `Certificate.terminating?`; every `:diverging` sample's genuine non-termination is asserted structurally (back-edge present, non-decreasing arg) — **including the confirmed mutual cycle**. For Positivity: `:positive` ⇒ `Inductive.positive?/2` returns `:ok`; `:negative` ⇒ `{:error, _}`. For Forcing: `t ≠ t'`, both force the registered global under plain (non-δ) evaluation, and are not structurally identical (guards the §4.3 regression). Also a `check all`-style soundness meta-test per generator: sampled challenges are well-formed (`Generators.*.env_of` succeeds; terms pass `Term.term?/1`).

*Note:* the self-tests import the deterministic constructors from Tasks 9–11 (`diverging_mutual_pair/0`, `negative_family/0`, `forcing_pair/0`) so the "known-bad" set is fixed and version-stable, per spec §12.

- [ ] **Step 4: Run them** — `mix test test/antigen/generators/` → PASS. If the diverging self-test's structural assertion contradicts a generator output, the *generator* is mislabeling — fix it.
- [ ] **Step 5: Commit** — `test(antigen): generator self-tests (label correctness) + StreamData architecture guard`.

### Task 13: Fuel instrumentation on `Cure.Core.Conv` (TCB — additive only)

**Files:**
- Modify: `lib/cure/core/conv.ex`
- Test: `test/cure/core/conv_fuel_test.exs`

**Interfaces:**
- Produces: `Conv.conv_within?(t1, t2, nbe_env, depth, sig, fuel) :: {:ok, boolean()} | :fuel_exhausted` — runs the existing algorithm but bounds total δ-unfolds to `fuel`. **The existing `conv?/5` path is byte-for-byte behaviorally unchanged:** the fuel counter lives in the process dictionary and is only consulted when set, which `conv?/5` never does.

Implementation — the ONLY edits to `conv.ex`:

1. Add a module attribute `@fuel_key {__MODULE__, :fuel}` and the public entry:

```elixir
@spec conv_within?(Cure.Core.Term.t(), Cure.Core.Term.t(), [Cure.Core.Value.t()], non_neg_integer(), Env.t() | nil, pos_integer()) ::
        {:ok, boolean()} | :fuel_exhausted
def conv_within?(term1, term2, env, depth, sig, fuel) when is_integer(fuel) and fuel > 0 do
  Process.put(@fuel_key, fuel)
  try do
    {:ok, conv?(term1, term2, env, depth, sig)}
  catch
    :throw, {@fuel_key, :exhausted} -> :fuel_exhausted
  after
    Process.delete(@fuel_key)
  end
end
```

2. Insert a single fuel decrement at the δ-unfold recursion in `whnf_delta/2` (conv.ex:89-94) — the exact and only place the wrongly-certified cycle loops:

```elixir
defp whnf_delta({:vneutral, neutral} = v, sig) do
  case unfold_head(neutral, sig) do
    {:ok, reduced} -> whnf_delta(spend_fuel(reduced), sig)
    :stuck -> v
  end
end
```

3. Add the guard-clean helper (a no-op when fuel is unset, so the pure path is untouched):

```elixir
defp spend_fuel(reduced) do
  case Process.get(@fuel_key) do
    nil -> reduced
    0 -> throw({@fuel_key, :exhausted})
    n -> Process.put(@fuel_key, n - 1); reduced
  end
end
```

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/core/conv_fuel_test.exs
defmodule Cure.Core.ConvFuelTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Conv, Env}
  alias Antigen.Generators.Forcing

  test "conv_within? returns {:ok, _} for a terminating conversion" do
    # two obviously-equal closed terms, no divergence
    assert {:ok, true} = Conv.conv_within?({:type, 0}, {:type, 0}, [], 0, nil, 1000)
  end

  test "conv_within? reports :fuel_exhausted on the wrongly-certified diverging pair" do
    c = Forcing.forcing_pair()
    env = Forcing.certified_env_of(c)
    assert :fuel_exhausted = Conv.conv_within?(c.payload.t, c.payload.tprime, [], 0, env, 200)
  end

  test "the un-fueled conv?/5 path is unaffected (no fuel key leaks)" do
    assert Conv.conv?({:type, 0}, {:type, 0}, [], 0, nil) == true
    assert Process.get({Conv, :fuel}) == nil
  end
end
```

- [ ] **Step 2: Run it, verify it fails** — `mix test test/cure/core/conv_fuel_test.exs` → FAIL (`conv_within?` undefined). The diverging test would hang on the current `whnf_delta`; that is exactly what the fuel fixes — do not run the diverging case until Step 3 adds the bound. (Run only the first test at Step 2: `mix test test/cure/core/conv_fuel_test.exs:LINE`.)
- [ ] **Step 3: Apply the three edits above to `conv.ex`.**
- [ ] **Step 4: Run the full file, verify it passes** — `mix test test/cure/core/conv_fuel_test.exs`. Then run the existing conversion suite to confirm no regression: `mix test test/cure/core/conv_test.exs`.
- [ ] **Step 5: Commit** — `feat(core): additive δ-unfold fuel instrumentation for conversion (Antigen reflexivity assay)`.

### Task 14: The four real assays + runner registry

**Files:**
- Create: `lib/antigen/assays/totality.ex` (`totality/terminating` + `totality/diverging`)
- Create: `lib/antigen/assays/positivity.ex`
- Create: `lib/antigen/assays/reflexivity.ex`
- Modify: `lib/antigen/runner.ex` (register the real assays in `assay_module/1`), `lib/mix/tasks/antigen.ex` (default gen = the three real generators; default assay dispatch)
- Test: `test/antigen/assays/totality_test.exs`, `positivity_test.exs`, `reflexivity_test.exs`

**Interfaces:**
- `Assays.Totality.run(Challenge.t()) :: :ok | {:violation, detail}` — rebuild env via `Generators.Totality.env_of/1`; for each `focus` name call `Certificate.terminating?(name, Env.get_def(env,name).body)`; **`totality/diverging`** (label `:diverging`) violates iff the certifier returns `true` for any member; **`totality/terminating`** (label `:terminating`) violates iff it returns `false`. Assay id chosen by label.
- `Assays.Positivity.run(Challenge.t()) :: :ok | {:violation, detail}` — `env = Generators.Positivity.env_of/1`; `Inductive.positive?(env, family)`; label `:negative` must be `{:error, _}`, `:positive` must be `:ok`.
- `Assays.Reflexivity.run(Challenge.t()) :: :ok | {:violation, detail}` — `env = Generators.Forcing.certified_env_of/1`; `Conv.conv_within?(t, tprime, [], 0, env, @fuel)` where `@fuel` is the **fixed committed constant** (spec §8); `:fuel_exhausted ⇒ {:violation, {:non_normalizing, ...}}`, `{:ok, _} ⇒ :ok`.

- [ ] **Step 1: Write the failing tests** — one per assay: the diverging challenge from Task 9 makes `Assays.Totality.run` return `{:violation, _}` (the live hole); the terminating challenge returns `:ok`; a labeled-negative family makes `Assays.Positivity.run` return `:ok` (checker correctly rejects) and a mislabel would violate; the forcing pair makes `Assays.Reflexivity.run` return `{:violation, {:non_normalizing, _}}`.
- [ ] **Step 2: Run them, verify they fail** — modules undefined.
- [ ] **Step 3: Implement the three assay modules + register them** in `Runner.assay_module/1` (`"totality/diverging"`, `"totality/terminating"`, `"positivity"`, `"reflexivity"`) and swap the Mix task's default generator/assay set from stub to real.
- [ ] **Step 4: Run them, verify they pass** — `mix test test/antigen/assays/`.
- [ ] **Step 5: Commit** — `feat(antigen): four schema-directed assays wired to the real kernel`.

### Task 15: End-to-end explore run + corpus replayer test + health reporting

**Files:**
- Modify: `lib/antigen/runner.ex` (populate the `health` map: discard rate + coverage buckets hit, per spec §9), `lib/antigen/report.ex` (embed health summary)
- Create: `test/antigen/corpus_replay_test.exs` (the `mix test` replayer over both committed stores)
- Create: `test/antigen/e2e_test.exs`
- Create (committed data): `test/antigen/corpus.sexp`, `test/antigen/seeds.sexp` (seeded from a real explore run)

**Interfaces:**
- Consumes: everything above.
- Produces: `Runner.explore/1` now returns `health: %{discard_rate: float, coverage: MapSet.t()}` (discard = attempts that failed to produce a well-formed candidate; distinct from coverage-duplicate rejection — spec §9). The `corpus_replay_test.exs` is the permanent regression harness: it decodes `test/antigen/corpus.sexp` + `test/antigen/seeds.sexp` and asserts each entry's assay invariant, **reporting every failure non-fail-fast** and never mutating the files.

- [ ] **Step 1: Write the e2e failing test** — `Runner.explore/1` with the real Totality generator + `Assays.Totality` produces `infections >= 1` (the live hole), writes a `tmp/` report, appends an antibody; `result.health.coverage` includes `:has_mutual_group`.
- [ ] **Step 2: Run it, verify it fails** — health map absent / generator not wired.
- [ ] **Step 3: Implement health tracking** in the runner (count discards vs. dedup-rejections; union coverage buckets) and the replayer test. Seed the committed `corpus.sexp`/`seeds.sexp` by running `mix antigen --count <n>` once and committing the produced files (these are the first antibodies — spec §2 crit. 1).
- [ ] **Step 4: Run the replayer + e2e** — `mix test test/antigen/corpus_replay_test.exs test/antigen/e2e_test.exs`. While the kernel hole is live, the antibody entries' `totality/diverging` invariant ("kernel must NOT certify") **fails on replay — this is correct and expected** (spec §7.1: a live infection turns `mix test` red until the kernel is fixed). Document this in the replayer test's moduledoc so CI red is understood, and gate it behind a `@tag :antigen_live_hole` so the suite's default green/red policy is a deliberate choice, not an accident. **Decision required at execution time:** confirm with the operator (via the Stage-5 report) whether the live-hole replay should be `@tag`-excluded by default or left red — do not silently pick.
- [ ] **Step 5: Commit** — `feat(antigen): end-to-end explore, health reporting, committed corpus + replayer`.

**Phase 2 gate (run once, serially):** `mix test test/antigen/ test/cure/core/conv_fuel_test.exs` — success criteria #1–#3, #6 hold; criteria #4–#5 hold from Phase 1 + Task 15. Note the live-hole replay tag decision in the completion report.

---

## Self-review (checklist run against the spec)

- **Spec coverage:** §3 architecture → Tasks 2–8 (Phase 1) + 9–14 (Phase 2). §4 four assays → Task 14 (+ generators 9–11, fuel 13). §5 generators → Tasks 9–11. §6 Gen DSL → Task 2 (+ backend Task 3). §7 corpus → Task 5 (+ coverage Task 4). §8 run modes/budget → Tasks 7–8; fuel §8 → Task 13. §9 health gate → Task 15. §10 reporting → Task 6. §11 phasing → the two phases. §12 testing Antigen → Task 12 + per-task tests. §2 success criteria: #1 Task 15, #2 Tasks 13+14, #3 Task 14, #4 Task 15 replayer, #5 Task 8, #6 Task 12.
- **Placeholder scan:** all code steps show real code or (Phase 2 Tasks 9–11, 14–15) name the exact functions, terms, and assertions to write with the verified kernel signatures; no "TBD"/"handle edge cases".
- **Type consistency:** `Challenge` fields, `Env.add_def/4`, `Certificate.terminating?/2`, `Inductive.positive?/2`, `Conv.conv_within?/6`, `Serialize.encode/decode`, `Coverage.key/1` used identically across tasks. `env_of/1` (Totality/Positivity) and `certified_env_of/1` (Forcing) are the consistent rebuild entry points consumed by the assays.
- **Open decision surfaced, not buried:** Task 15 Step 4 flags the live-hole replay tagging as an operator decision for the Stage-5 report (it changes whether default `mix test` is red), consistent with spec §2's sequencing note.
