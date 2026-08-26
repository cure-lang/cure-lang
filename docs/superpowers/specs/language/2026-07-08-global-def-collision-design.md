# Global-def collision protection — Design

**Date:** 2026-07-08
**Status:** Approved (operator batch authorization, autopilot run; first of three
sequenced initiatives — identity-type-as-inductive and the parity queue follow)
**Topic:** global-def-collision

## 1. Problem — a genuine E-layer soundness gap

When two modules in scope both define a global function `foo`, the later one
silently overwrites the earlier one. Flagged during K12 slice-4; never landed.

Ground truth (verified on this checkout):

- `Cure.Elab.Program.merge_env/2` (`lib/cure/elab/program.ex:629`) merges
  imported environment slices with `Map.merge(left.defs, right.defs)` — on a
  key collision the right slice wins, silently.
- The shadowing machinery (`lib/cure/elab/resolution.ex`, the locked
  Approach-B design: E-layer resolution over bare atoms, collision-triggered
  re-keying to `"Mod#Name"` atoms) protects **families and constructors
  only**. Its own doc comment states the gap verbatim: *"Functions keep their
  bare `defs` keys."* (`resolution.ex:62-63`; `rekey_module_env/3-4` re-keys
  `families`/`ctors`/`ctor_to_family` and only *renames references inside*
  `defs` bodies, never the def keys themselves.)

Consequence: `use A` + `use B` where both define `helper/1` gives whichever
slice merged last — the program type-checks and runs against the *other*
module's function. Proof-relevant code can silently call the wrong lemma. This
is exactly the class of silent-wrong-binding the family/ctor re-keying was
built to prevent; globals were left out.

## 2. Design — extend Approach B to `defs`, faithfully

No new mechanism. The locked type-shadowing decision (Approach B:
collision-triggered re-keying over bare atoms + qualified escape hatch,
core/TCB untouched) is extended to the third and last unprotected namespace.

### 2.1 Collision-triggered re-keying for def keys

In the import-merge path (`shadow_resolved_imports/1` →
`Resolution.rekey_module_env/…`):

- Detect def-name collisions across slices exactly as family/ctor collisions
  are detected today (bare-atom key intersection, including against the
  importing module's own locally-declared def names).
- A colliding def owned by an imported slice is re-keyed to
  `rekey_atom(module_id, name)` (`"Mod#name"`), and — as with ctors — every
  reference to it inside that slice's def bodies/types and telescopes is
  rewritten via the existing `rekey_term/2` atom map. `quantities` (the
  per-parameter erasure markers) lives *inside* each def's own `defs` map
  value (`Env.add_def/5`, `lib/cure/core/inductive.ex`) alongside `type` and
  `body`, so it travels for free when `rekey_defs/2` moves that value to its
  new key — no extra step needed. `certified`, by contrast, is a **separate
  top-level `Env` field** (a bare `MapSet.t()` of def-name atoms,
  `lib/cure/core/inductive.ex:12`) that today's `rekey_module_env/4` does
  *not* touch at all in its returned struct (`resolution.ex:94-101` rewrites
  `families`/`ctors`/`ctor_to_family`/`defs`/`builtins` only). Extending
  re-keying to `defs` means `rekey_module_env` must explicitly add a
  `certified: rekey the member atoms via amap` step — this is the one field a
  literal reading of "re-key defs" would miss, and forgetting it silently
  drops δ-unfolding for every re-keyed certified def (`Env.certified?/2`,
  `lib/cure/core/inductive.ex:86`, is a bare `MapSet.member?` keyed on the
  post-re-key atom).
- Non-colliding defs keep bare keys (zero cost for the common case; identical
  to family/ctor behavior).

### 2.2 Reference resolution, same rules as types/ctors

For a bare reference `foo` where collisions were re-keyed:

1. The **local** module's own `foo` wins (local shadows import — mirrors the
   existing family/ctor rule and every real language's shadowing).
2. Otherwise, if exactly one import provides `foo`, that one (its re-keyed or
   bare atom) is used.
3. Otherwise — two or more imports provide `foo` and no local exists — the
   reference is an **ambiguity error**, a new E-code carrying the candidate
   modules, matching Idris's "Ambiguous name" / Agda's ambiguous-identifier
   errors. Silent picking is precisely the bug being fixed, so no default
   winner. The error text names the qualified escape hatch.
4. **Qualified CALL references always work**: `A.foo(x)` resolves through
   module identity regardless of collisions (existing qualified machinery,
   `elaborate_named_call`'s `String.contains?(name, ".")` branch,
   `elaborator.ex:236-240`; the elaborator maps it to the re-keyed atom when
   one exists). This covers call syntax only — a *bare-value* qualified
   reference (`A.foo` with no call parens, e.g. passed to a higher-order
   function) is not a collision-re-keying question: dotted expressions parse
   to `{:attribute_access, ...}` (`parser.ex:542-549`), not a single dotted
   `:variable` token, and `elaborate_expr_typed`'s attribute-access clause
   (`elaborator.ex:410`) has no module-qualification handling at all — it
   always treats the base as a record value. So `A.foo` without parens fails
   before module identity even enters the picture, regardless of whether
   `foo` collides. This is a pre-existing, general dot-syntax limitation
   (tracked in the parity queue, not this design) — out of scope here; see §5.

**Two resolution sites, not one.** Ground truth (verified on this checkout):
bare-name resolution for values currently happens at two independent places in
`lib/cure/elab/elaborator.ex`, and they are not symmetric today:

- **Call position** — `elaborate_named_call/5` (`elaborator.ex:231`), used for
  `foo(x)`. This already has ambiguity-check precedent for ctors: it calls
  `Resolution.ambiguous_modules/2` at `elaborator.ex:304-305` before falling
  through to the global/implicit-def branches. Rule 1-3 above extend naturally
  here — this check currently only inspects `env.families`, so it must also
  consult def-owners.
- **Bare-value position** — `resolve_free/2` (`elaborator.ex:4641-4649`),
  reached from `elaborate_expr_typed({:variable, ...})` whenever a top-level
  function name is referenced **without call syntax** (passed as a first-class
  value, e.g. a higher-order-function argument). This is a real, tested,
  currently-working Cure feature — see
  `test/cure/elab/first_class_function_test.exs` (`ap(inc, S(Z()))`, a bare
  `inc` reference resolved as a value) and `test/oracle/poly/pl07_endo_map.cure`
  (`emap(s, mklist())`). `resolve_free/2` today runs **zero** ambiguity
  checking for anything (ctors included) — it falls straight through to
  `{:global, atom}`, which the kernel then either resolves via the flat
  (post-re-key) `defs` map or fails as a generic `:unknown_global` — never an
  ambiguity diagnostic.

  Rules 1-3 must therefore also be wired into this path. Skipping it would
  leave exactly the kind of silent-wrong/misleading-error behavior this design
  exists to close: an ambiguous colliding function passed bare as a
  higher-order argument would surface a confusing "unknown global" instead of
  the ambiguity error, while the identical name called with parens correctly
  errors — an inconsistency a user would have no way to explain from the
  error text alone.

  Both sites raise the **same** new E-code (§3) for the same underlying
  condition — one ambiguity concept, two call sites, not two error codes.

### 2.3 What is NOT changed

- **Kernel/TCB untouched.** Re-keyed defs are just differently-named globals
  to the kernel; `{:global, name}` semantics, conversion, certificates are
  oblivious (same argument that carried the family/ctor re-keying).
- **AtomVM/runtime tags untouched.** Def re-keying is an elaboration-env
  concern; emitted BEAM function names derive from the module actually being
  compiled (its own defs are local and bare). Cross-module *runtime* calls
  already go through qualified/remote resolution (codegen), not env keys.
- The classic (non-dependent) checker path is out of scope: its module
  compilation is per-file against loaded beams, and cross-module value calls
  resolve at codegen (see the auto-import-order spec §2). This gap is the
  dependent elaborator's env merge.
- No surface-syntax change. (The qualified escape hatch already exists.)

## 3. Error handling

| Condition | Behavior |
|---|---|
| Import collides with local def | Local wins; import re-keyed; both reachable (qualified for the import) |
| Two imports collide, bare reference used | New E-code ambiguity error listing candidates + qualified-form hint |
| Two imports collide, no reference to the name | No error (collision is latent; both re-keyed and reachable qualified) |
| Certified def re-keyed | Certificate follows the key; δ-unfolding unaffected |

E-code: next free number in the shared E/W/H sequence at implementation time
(089 expected — 086/088 were taken as warnings (W086, W088) and 087 as an
error (E087) by the auto-import-order work; E089 verified absent from the
registry at `lib/cure/compiler/errors.ex` as of this writing; implementation
re-verifies against the registry).

## 4. Testing (TDD; red first, immutable once correct)

1. **Red reproduction of the gap**: two stdlib-style fixture modules both
   defining `helper/1` with observably different bodies (e.g. returning
   distinct constants); a third module `use`s both and calls `helper`
   qualified — assert each qualified call reaches ITS module's body. Then the
   bare-call case (`elaborate_named_call`): assert the ambiguity error (this
   is the case that today silently returns the last-merged body — the red
   test pins today's wrong value and goes green on the error). Then the
   **bare-value case** (no call syntax — `helper` passed as a first-class
   argument to a higher-order function, per §2.2's two-resolution-sites note,
   e.g. mirroring `test/cure/elab/first_class_function_test.exs`'s
   `ap(inc, ...)` shape): assert the same ambiguity error is raised via
   `resolve_free`, not a generic unknown-global failure.
2. **Local-shadows-import**: importing module defines its own `helper`; bare
   call resolves locally; qualified call still reaches the import.
3. **Certificate survival**: a certified-total colliding def remains
   δ-unfoldable after re-keying (conversion test that requires unfolding, in
   the style of the existing totality tests).
4. **No-collision fast path**: unrelated imports keep bare keys (assert env
   keys directly — guards against re-keying everything).
5. **Regression pin, same style as the K12 slice-4 finding**: ground truth
   correction — the K12 slice-4 probe that flagged this gap is
   `test/cure/elab/global_namespace_soundness_test.exs` (plain `ExUnit.Case`
   against `Program.check_ast/1`), not an Antigen antibody; there is no
   existing "global-def" Antigen family to mirror (`test/antigen/` has zero
   probes touching module-merge/namespace collision — its antibodies are all
   kernel/certifier-soundness probes: size-change termination, cycle rule,
   lazy unfold, Eq-inductive, unify-indices, certify-hardening). Add the new
   cross-module-merge regression test to
   `test/cure/elab/global_namespace_soundness_test.exs` (extending its
   existing within-module/fn-ctor-coexistence coverage with the cross-module
   `use A; use B` + bare-call case this design fixes), asserting the overwrite
   is impossible. If an Antigen-style REACH/CONTROL probe is *also* wanted for
   this class of bug going forward, that is a new family to establish, not an
   existing one to slot into — track separately, not silently reframed as
   already-existing infrastructure.
6. Full `mix test`, `mix cure.check.examples` — green, sequentially.

## 5. Out of scope

- Identity-type-as-inductive (next initiative in this batch).
- Classic-checker cross-module semantics; codegen resolution (covered by
  auto-import-order W088 work).
- Renaming/re-exporting surface syntax.
- Bare (non-call) qualified value references (`A.foo` with no parens) —
  unsupported today independent of collisions (§2.2 rule 4 note); a
  pre-existing dot-syntax gap, not something this design introduces or fixes.
