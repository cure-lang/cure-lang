# Deterministic, parallel-safe stdlib in the Cure test suite — Design

**Status:** approved (design gate), 2026-07-17
**Branch:** `autopilot/stdlib-test-isolation` (cut from `feature/idris-parity`)

## Problem

The Cure compiler emits every module as a real BEAM module loaded under its
**canonical global name** (`Cure.Std.Iter`, `Cure.Std.String`, …). The BEAM has
exactly one global code table — one slot per module name for the whole VM. Any
test that exercises the compiler end-to-end (elaborate → emit → `:code.load` →
call it) must install its module into that shared slot.

`test_helper` compiles the canonical, full stdlib once at startup. Then
individual **producer** tests emit *their own* version of some stdlib module and
load it under the same name, overwriting the canonical one for every later test.
The versions differ in two ways, both observed as live failures:

- **Pared-down surface** — a test tree-shakes and emits only the functions it
  needs, so its `Cure.Std.Map` is missing `get/2`. A later consumer calling
  `get/2` fails.
- **Different lowering** — a test emits a module with an older/different
  constructor lowering, so it returns `{:done}` where the canonical returns
  `:Done`, or leaks an `:Emit` effect atom into a runtime tuple.

Because loading a new version forces a purge of the old (BEAM keeps at most two
versions), "reload" mechanically means "purge + load," and the resident version
after a clobber is whatever the last producer installed.

This is **order-dependent contamination**: the failing files
(`test/cure/stdlib/iter_test.exs`, `test/cure/stdlib/stdlib_test.exs`) pass in
isolation (124/124) but fail in the full suite (a run showed 10 failures). It is
also *why* ~44 test files carry `async: false` — serialization is a band-aid
that reduces, but does not remove, the clobber.

The structural root is that `Cure.Elab.Emit.remote_target/2` (`emit.ex:195`)
lowers a cross-module call to a **hardcoded** remote target
(`{Cure.Std.Map, size}`) baked into the *caller*, so a callee must be loadable
under its exact canonical name. That hardcoded name forces every test onto the
same global slot.

## Goal

Make the suite **correct under parallelism** and keep it a **single suite**:
eliminate the clobber flakes and unlock `async: true` for the tests currently
forced serial by them. Non-goals: partitioning into multiple OS processes (a
sledgehammer we explicitly rejected in favor of the root fix), reducing test
count, or changing production compiler behavior.

## Architecture

Two complementary mechanisms plus carve-outs:

- **Stick the canonical stdlib** protects *consumers* — the majority that just
  call `Cure.Std.X.f`. Once the full canonical surface is resident and made
  sticky, nothing can *reload* it via `:code.load_binary`/`load_file`, so
  consumers always see the correct module. (Sticking does not block
  `:code.purge`/`:code.delete`, which can still evict a stuck module and clear
  its sticky flag — this is a distinct, narrower hazard than reload-clobbering
  and is handled separately; see C1's "Purge/delete is not blocked by sticky"
  bullet.)
- **Namespace the producers** isolates the *emitter-verifying* tests — those
  that deliberately emit their own version to assert on the emitter's output.
  Each producer's emitted group loads under a unique per-test prefix, so it
  never touches the canonical slot.

Sticky + namespacing compose: namespacing removes the producers' reason to touch
the shared slot; sticky is the enforcement that guarantees nothing ever
regresses the canonical and turns any missed producer into a loud, deterministic
`:sticky_directory` failure instead of a silent flake.

## Components

### C1 — Startup: load-all + stick (`test/test_helper.exs`)

After `Mix.Task.run("cure.compile_stdlib")`, enumerate every compiled canonical
stdlib beam, `:code.ensure_loaded` each, and `:code.stick_mod` each.

- **Source of the module list:** the beams `cure.compile_stdlib` writes to
  `_build/cure/ebin/Cure.*.beam` (the same glob `Cure.Stdlib.Preload` loads from
  at `preload.ex:592`). Module name = `Path.basename(path, ".beam") |> String.to_atom`.
- **Full-surface guarantee:** every module a consumer references must be loaded
  *before* sticking, or a consumer could still hit a not-loaded module. A
  hardcoded sentinel list alone cannot deliver this: `cure.compile_stdlib`
  already `exit`s the whole `mix test` process if any `.cure` file fails to
  *compile* (`err_count > 0` in `lib/mix/tasks/cure.compile_stdlib.ex`), but a
  module can still go missing *upstream* of that check — e.g. a `DepGraph.scan`/
  `Path.wildcard` omission that never attempts to compile a source file at all,
  which a 5-name sample would only catch by accident. The implementation
  therefore asserts the load set is non-empty AND that its size/name-set matches
  an independently-derived expected set. **That expected set must come from
  each file's own declared module name, not from a basename→name guess.**
  `preload.ex` already solves this problem once, at `@std_module_groups`
  (`preload.ex:110`): for every `lib/std/*.cure` file, regex-match the first
  `mod|proof|actor|fsm|sup|app <Name>` declaration (`@mod_regex`,
  `preload.ex:103`) and prefix it with `"Cure."`. Reuse that map (or an
  identical scan) as the expected set — do **not** attempt to invert
  `source_path_for/2`'s basename transform (dotted segments after `Std`,
  joined with `_`, downcased) to go the other direction, basename → expected
  module: that transform is **not invertible**. `lib/std/non_empty.cure`
  declares `mod Std.NonEmpty` — one CamelCase segment, no dot — but
  `source_path_for/2` computes `Path.join(["Std","NonEmpty"] |> tl()
  |> Enum.join("_") |> String.downcase())` = `"nonempty"` (no underscore),
  which does not match the actual `non_empty.cure` filename; conversely
  `otp_call.cure` declares `mod Otp.Meta.Call` — two dotted segments — whose
  forward transform *does* produce `otp_call`. Both source files have the
  identical `word_word.cure` shape, but one came from a single merged
  CamelCase segment and the other from two dotted segments; nothing in the
  basename alone tells you which, so any "expected module = f(basename)"
  scheme is unsound in general, and `non_empty.cure` is a live counter-example
  today (verified: `source_path_for(:"Cure.Std.NonEmpty", source_dir)` returns
  `:not_found` because it looks for `nonempty.cure`, which does not exist).
  Reusing `@std_module_groups`'s source-declaration scan (regex over each
  file's own `mod`/`proof`/… line) sidesteps this entirely, since it reads the
  true module name straight from each file rather than reconstructing it from
  the filename. **Caveat:** `@std_module_groups` itself is a module attribute
  baked at *`preload.ex`'s own compile time*, via `@external_resource` on each
  currently-known `lib/std/*.cure` file — that mechanism recompiles
  `preload.ex` when a *tracked* file's mtime changes, but cannot detect a
  brand-new `.cure` file that did not exist (and so was not yet an
  `@external_resource`) the last time `preload.ex` itself was compiled. Do
  **not** call `Preload.module_groups()`/read `@std_module_groups` directly
  for the completeness check — that risks comparing against a stale
  snapshot from a prior compile in exactly the "new file, nobody wired it up"
  scenario this bullet exists to catch. Instead, run the *same regex scan*
  (`@mod_regex`'s pattern over `Path.wildcard("lib/std/*.cure")`) freshly, at
  suite-startup runtime, in `test_helper.exs` itself — a plain file read, no
  compile-manifest/`@external_resource` involved, so it always reflects the
  files actually on disk for this run. Any mismatch between the loaded set
  and this expected set (missing OR unexpectedly extra) fails the suite at
  startup with a clear message rather than flaking later. A short
  named-sentinel check (`Cure.Std.String`, `Cure.Std.Core`, `Cure.Std.Iter`,
  `Cure.Std.Map`, `Cure.Std.List`) is kept *in addition*, purely so the
  common-case failure message names a familiar module instead of a diff — it
  is not itself the completeness guarantee.
- **Safety under sticky:** `Cure.Stdlib.Preload.load_if_present/2`
  (`preload.ex:605`) already maps `{:error, _}` (including `:sticky_directory`)
  to `:ok`, so re-preload calls no-op instead of crashing. This is a
  precondition the plan verifies with a test, not an assumption.
- **Scope:** stick only `Cure.Std.*` (and any other canonical `Cure.*` stdlib
  module emitted by `compile_stdlib`). Never stick user/test-emitted modules.
- **Per-process:** sticking happens once per suite process; each `mix test`
  starts a fresh BEAM, so there is no cross-run state. **Exception:** see the
  next bullet — a specific existing test must re-stick a module mid-suite.
- **Purge/delete is not blocked by sticky.** `:code.stick_mod/1` only rejects
  `:code.load_binary`/`load_file` (verified: reload of a stuck module, even
  with byte-identical input, returns `{:error, :sticky_directory}`). It does
  **not** protect against `:code.purge/1` + `:code.delete/1`, which succeed
  unconditionally on a stuck module — evicting it from the code table *and*
  clearing its sticky flag, so a subsequent `:code.load_binary` under the same
  name succeeds again with no protection. This is not hypothetical:
  `test/cure/stdlib/preload_test.exs` has **two** such sites, both of which
  purge + delete a C1 sentinel and reload it, and both must re-stick:
  1. `"recovers an unloaded module by compiling it from source"` (under
     `describe "compile_missing_from_sources/1"`) intentionally purges +
     deletes `Cure.Std.List` to test `Preload.compile_missing_from_sources/1`'s
     JIT-recovery path.
  2. `"honours :stdlib_beam_dir app-env override"` (under `describe
     "preload/1"`) purges + deletes whatever `staged_sample_beam/0` harvests —
     which is hardcoded to read `Cure.Std.Core.beam` specifically, so in
     practice this is always `Cure.Std.Core`, a second C1 sentinel, not an
     arbitrary/incidental module.

  Both are legitimate coverage of real functionality, not producers to migrate
  away (C2/C3 do not apply). Left unaddressed, either test would silently
  un-stick its target module (`Cure.Std.List` or `Cure.Std.Core` respectively)
  for every test that runs after it in the same suite process, reopening
  exactly the clobber vulnerability C1 exists to close — silently, the
  opposite of this design's goal of turning flakes into loud failures. Site 2
  is the easier one to miss: its `after` block today only restores the
  `:stdlib_beam_dir` app-env and removes the tmp dir — it has no re-stick call
  at all, unlike site 1 which at least reloads through a path that makes the
  gap easy to spot. **Fix:** any test that legitimately purges/deletes a
  canonical `Cure.Std.*` module must re-stick it (`:code.stick_mod/1`) in its
  cleanup before returning control to the suite — both sites use a plain
  `try/after` block today (neither uses ExUnit's `on_exit/1` callback); add
  `:code.stick_mod(module)` to both sites' `after` blocks, immediately after
  reloading it. This is an explicit, audited exception to "sticking happens
  once per suite process"; any future test that evicts a canonical module must
  do the same or be migrated to a namespaced fixture module instead.
  `preload_test.exs` must stay `async: false` (it is not a C5 candidate — its
  global code-table manipulation is exactly the "genuine non-clobber global
  state" C5 excludes). This is sufficient, not merely best-effort: verified
  empirically against this project's ExUnit (1.20.1) that the `async: false`
  queue only begins after every `async: true` module has fully finished, so no
  async consumer test can ever run concurrently with either purge→delete→
  reload→re-stick window and observe `Cure.Std.List` or `Cure.Std.Core`
  evicted or non-sticky.

### C2 — Producer namespacing (`lib/cure/elab/emit.ex` + producer tests)

Thread an optional module-name **prefix** through the emit entry points so a
producer's whole emitted group is installed and cross-linked under that prefix.

**Scope:** this mechanism lives entirely in `Cure.Elab.Emit`
(`compile_and_load/2`, `compile_forms/3`, `remote_target`). It does **not**
reach the separate, higher-level `Cure.Compiler.compile_and_load/2`
(`lib/cure/compiler.ex:196`) entry point — the whole-source-string compiler
used by, e.g., `test/cure/stdlib/stdlib_test.exs` (one of the two files named
in the Problem section) via its `compile_stdlib(name)` helper, which compiles
`lib/std/#{name}.cure` directly under its own canonical module name. A
producer built on `Cure.Compiler.compile_and_load/2` cannot be namespaced by
C2 as scoped here; it is a C3 candidate instead (see below) — it must not be
left unclassified on the assumption that "producer namespacing" trivially
covers it.

- **`remote_target/2` → `remote_target/3`** (or an added prefix+local-owner
  argument): for an owner in the *locally emitted group* (`owner ∈
  local_owners`), target `{String.to_atom(prefix <> "Cure." <> owner), base}`;
  for an owner **not** in the emitted group, keep the bare canonical
  `{String.to_atom("Cure." <> owner), base}` so the call resolves to the sticky
  canonical. At `prefix: ""` both formulas reduce to the same string
  (`"Cure." <> owner`) regardless of `local_owners`, which is what makes the
  byte-identity invariant below hold unconditionally, not just in the common
  case. `:local` (the `emit_aliases` branch) is unchanged. The `origins`-routed
  branch (`Map.get(origins, name)`) is also unchanged — always canonical, never
  prefixed — because it is structurally disjoint from a producer's own
  local-group delegation: per `remote_target`'s own comment, every ordinary
  owner-qualified global goes through the owner branch above during real
  dependent-pipeline elaboration, so `origins` only ever resolves names that
  arrive *unqualified* (the legacy-compat path some direct-emitter tests, e.g.
  `map_parameterized_test.exs`'s synthetic caller module, still use to reach
  the canonical stdlib as a pure consumer). A local-group owner can therefore
  never be origins-routed in practice; no prefix logic is needed on that
  branch.
- **`compile_and_load/2` and `compile_forms/3`** accept `prefix` and
  `local_owners` (a `MapSet` of owner *strings*, in the exact form
  `Cure.Elab.Name.owner/1` returns them — e.g. `"Std.Map"`, not `:"Std.Map"`
  and not `"Cure.Std.Map"`) in `opts`, default `prefix: ""` and
  `local_owners: <derived from functions>`. That default is per-call
  (`Name.owner/1` applied to the `functions` being emitted in *this* call) and
  is only correct for a single-owner emission; a producer whose group spans
  multiple `compile_and_load` calls (the Set+Map case below) MUST pass the same
  explicit, whole-group `local_owners` to every call in the group — the default
  is insufficient there by construction, not just by omission. With the default
  empty prefix, byte-for-byte output is **identical** to today — this is
  the invariant that keeps golden tests and production compilation unchanged.
- **Producer tests** pass `prefix: prefix_for(__MODULE__)` where `prefix_for`
  sanitizes the module name into a valid atom-name segment (e.g.
  `Cure.Stdlib.SetDependentRunTest` → `T_Cure_Stdlib_SetDependentRunTest.`),
  and read back their module under the prefixed name.
- **Delegation faithfulness:** a producer that emits a group (e.g. Set + Map)
  passes the *whole* group's owners as `local_owners`, so Set's delegated call
  to Map lowers to `{Prefix.Cure.Std.Map, size}` and exercises the genuine
  cross-module remote-call path inside the sandbox — not a bundle-into-one-module
  shortcut (which the existing `set_dependent_run_test` comment explicitly warns
  against).

### C3 — Simplify pure consumers

Tests that emit/load their own stdlib module **only for historical safety** (not
to assert on emitter output) drop the emission and call the sticky canonical
directly. Identified by: the test does not assert on the *bytes/shape/name* of
the emitted artifact, only on runtime results that the canonical module also
produces.

**Named instance:** `test/cure/stdlib/stdlib_test.exs` is a C3 case, not C2
(per the C2 scope note above, its `Cure.Compiler.compile_and_load/2` path
cannot be namespaced by C2 anyway). Every one of its `describe` blocks recompiles
a `lib/std/*.cure` file under its real canonical name purely to call runtime
functions (`m.abs/1`, `m.sqrt/1`, …) that the sticky canonical module already
provides identically, then purges the module in `on_exit`. The fix drops
`compile_stdlib/1` and the `purge/1` helper entirely and calls
`:"Cure.Std.Math".abs(-5)` etc. directly against the sticky canonical — which
also removes this file's contribution to the sticky/purge hazard below.

**The Problem section's other named file, `test/cure/stdlib/iter_test.exs`,
needs no C2/C3 migration and is not classified above because it isn't a
producer at all:** it never calls `compile_and_load`/`compile_string`/
`compile_file`/`:code.load_binary` anywhere in the file — its `setup_all`
only calls `Cure.Stdlib.Preload.preload(examples: false, kind: :all)` (a
no-op against an already-sticky canonical, per C1's "Safety under sticky"
bullet) and every test calls straight into whatever `Cure.Std.Iter` is
resident. It was failing purely as a consumer-side victim of *other* files'
clobbers — the exact pattern the Problem section describes — so C1 alone
(the sticky canonical) fixes it with zero changes to the file itself.

### C4 — Golden carve-out

Tests that SHA-256 or byte-compare the compiled BEAM bake the module name into
the compared bytes. The one instance in this suite is
`test/cure/compiler/actor_quote_golden_test.exs` (`beam_sha256/2` calls
`Cure.Compiler.compile_string(src, output_dir: dir, ...)`, reads the `.beam`
bytes straight off disk with `File.read!`, and hashes them). Note this file
never calls `:code.load_binary` at all — it writes to a `System.unique_integer`
-suffixed temp dir and never installs its module into the shared VM code
table — so, unlike the C1/C2/C3 producer/consumer split, it was never at risk
from the clobber problem this design fixes; it stays `async: false` today for
reasons orthogonal to this design (temp-dir/file-I/O caution), not because
this design's mechanisms constrain it. It is also, like `stdlib_test.exs`,
built on the `Cure.Compiler.*` family the C2 scope note excludes, so C2's
prefix cannot reach it regardless. Verify it still passes byte-identical after
C1/C2/C3/C5 land (it should be unaffected by all of them) rather than
migrating it. (`test/cure/compiler/actor_family_raw_test.exs` is a
similarly-named but unrelated file — despite its docstring comments
referencing now-*retired* byte-golden checks, the file itself asserts on
`Cure.Compiler.compile_and_load/2` runtime behavior, not BEAM bytes; it is not
a C4 instance and is out of this design's scope entirely, since its fixture
modules use bespoke `Cure.Generated.*` names, never `Cure.Std.*`.) Consequence
stated honestly: "all async" is ~95%, not 100%, entirely due to this one file.

### C5 — Reclassify to async

Once a producer is namespaced (C2), simplified to a pure consumer (C3), or —
like `iter_test.exs` — was already a pure consumer needing no migration at
all, and it has no other genuine global-state reason (telemetry handlers,
`Application` env, cwd), flip it to `async: true`. Files with genuine non-clobber global state
(`telemetry_test`, `otel_test`, `observe_test`, `profiler_test`, most
`antigen/*` with shared coverage tallies) stay `async: false`.

## Baseline already landed

The Path B elaboration cache (`perf(elab): memoize module_slice_env by path`,
commit `0c36c631`) is the measured baseline: full suite ~22 min → ~6 min. It is
orthogonal to this work — keyed by source path at *elaboration* time, unaffected
by emit-time module names — and stays. This design is what makes that fast suite
trustworthy under parallelism.

## Data flow

1. Suite start: `compile_stdlib` writes `_build/cure/ebin/Cure.*.beam`; C1 loads
   + sticks them → canonical surface is resident and protected against reload
   (`:code.load_binary`/`load_file` refused). Not literally immutable: two
   audited `preload_test.exs` sites legitimately purge + delete + reload +
   re-stick a single sentinel each mid-suite — see C1's "Purge/delete is not
   blocked by sticky" bullet — but every other module, and every other test,
   sees the canonical surface as unchanging.
2. Consumer test runs: calls `Cure.Std.X.f` → hits the sticky canonical. No
   emission, no clobber.
3. Producer test runs: emits its group under `prefix`, loads
   `Prefix.Cure.Std.X`, calls it. `remote_target` keeps intra-group calls
   prefixed and extra-group calls pointed at the sticky canonical. No canonical
   slot is touched.
4. A missed producer (still emitting a bare canonical name): its `load_binary`
   is refused with `:sticky_directory` → deterministic failure naming the file,
   converted from a silent flake into a worklist item.

## Error handling

- `:code.load_binary` of a stuck module → `{:error, :sticky_directory}`.
  Preload tolerates it (no-op). A producer using `{:ok, _} = compile_and_load`
  under a bare name will crash — that is the intended forcing function and is
  resolved by namespacing that producer, not by loosening sticky.
- Loaded set doesn't match the expected `lib/std/*.cure`-derived set → fail the
  suite immediately with a message pointing at `compile_stdlib` (naming the
  missing sentinel when the gap includes one, else the raw diff).
- Either of `preload_test.exs`'s two purge sites (the JIT-recovery test on
  `Cure.Std.List`, or the `:stdlib_beam_dir` override test on `Cure.Std.Core`)
  fails to re-stick its module after purge+delete+reload → the corresponding
  added `:code.is_sticky/1` assertion (Testing strategy) fails that specific
  test immediately, rather than surfacing as an unrelated clobber failure
  elsewhere later in the run.
- `prefix_for/1` must always yield a valid atom segment; an unexpected module
  name shape raises at emit time rather than producing a malformed module atom.

## Testing strategy

The suite is its own integration test; determinism is the property under test.
Every test named below is written red-first and, once it correctly encodes
the intended behavior, is immutable: a regression is fixed by changing
implementation code, never by weakening, skipping, or deleting the test
(the sole exception is proving the test itself encodes the wrong behavior).

- **Preload-tolerates-sticky** (C1 precondition): a unit test sticks a throwaway
  module and asserts `load_if_present` returns `:ok` and does not raise.
- **Re-stick after legitimate eviction** (C1 purge/delete exception): both of
  `preload_test.exs`'s purge sites need this assertion, not just one — after
  the JIT-recovery test purges, deletes, and recompiles `Cure.Std.List`,
  assert `:code.is_sticky(:"Cure.Std.List") == true`; after the
  `:stdlib_beam_dir` override test purges, deletes, and reloads
  `Cure.Std.Core` (via `staged_sample_beam/0`), assert
  `:code.is_sticky(:"Cure.Std.Core") == true`. Both assertions run before
  their respective test ends, proving the invariant is restored rather than
  left silently broken for the rest of the suite.
- **Empty-prefix byte-identity** (C2 invariant): emit a fixed module with
  `prefix: ""` and assert the loaded module's exported functions and results
  match the pre-change canonical emission (guards production/golden unchanged).
- **Prefixed isolation** (C2): emit a stdlib group under two distinct prefixes
  in one process and assert both coexist, are independently callable, and do not
  clobber the canonical (canonical still returns its own results afterward).
- **Prefixed delegation** (C2): a namespaced Set+Map group's delegated call
  returns correct results, proving the intra-group remote target was prefixed.
- **Determinism gate:** run the full suite twice at two fixed seeds; zero
  failures both times. Before this work, the 10-failure run reproduces the
  clobber; after, both seeds are green.
- **Timing:** record wall-clock; expect ≤ the ~6 min Path B baseline, ideally
  lower as more files go async.

## Sequencing (also the falsification plan)

1. C1 sticky + full-load (the "Preload-tolerates-sticky" and "Re-stick after
   legitimate eviction" tests first — red, then green — same discipline as
   step 2 below), including the expected-vs-loaded completeness check
   and the `preload_test.exs` re-stick fix + assertion (both purge/delete
   hazards are fixed before anything else, since they can silently undermine
   every later step). Run the gate → the producer worklist appears as
   `:sticky_directory` failures. This also proves Path B never touched the
   clobber failures (they are a code-table layer, not elaboration).
2. C2 emit.ex prefix threading (empty-prefix byte-identity test first — red,
   then green — before any producer is migrated).
3. Migrate each producer on the worklist: namespace (C2), or simplify (C3) —
   including `stdlib_test.exs`, which is C3-only per the C2 scope note.
4. C4 golden carve-out — confirm `actor_quote_golden_test.exs` (the one
   byte-compare test) still passes un-namespaced.
5. C5 flip isolated files to async.
6. Determinism gate (two fixed seeds green) + timing.

## Risks

- **`emit.ex` is TCB-adjacent.** The kernel re-checks emitter output, but codegen
  changes still require the full gate. Empty-prefix byte-identity is the guard
  that the default path is untouched.
- **Incomplete canonical surface at startup.** If `compile_stdlib` does not emit
  a module a consumer needs, sticking cannot cover it. Mitigated by C1's
  expected-vs-loaded set comparison (not the 5 named sentinels alone, which
  only sample the surface — see C1).
- **Delegation tests short-circuiting.** If `local_owners` is set wrong, an
  intra-group call could hit the canonical instead of the sandbox, weakening the
  test. Mitigated by the prefixed-delegation test (C2).
- **Atom/code accumulation.** Each namespaced module is a new resident atom/module,
  never purged. Bounded (hundreds, small); negligible. Optional `on_exit` purge
  if it ever matters.
- **Stale/missing re-stick after a legitimate purge.** `preload_test.exs`'s
  two purge sites (see C1: the JIT-recovery test on `Cure.Std.List`, and the
  `:stdlib_beam_dir` override test on `Cure.Std.Core`) must each re-stick the
  module they evict. If a re-stick is missing or runs before the reload
  completes, that module is left non-sticky for the remainder of the suite —
  silently, since nothing errors. Mitigated by an explicit assertion in each
  test (`Code.ensure_loaded?/1` + a direct `:code.is_sticky/1` check)
  immediately after the re-stick, so a regression here fails loudly in the
  same test rather than showing up as an
  unrelated clobber flake later in the run.
