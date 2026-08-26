# Gap-Design Gate — Core cleanup complete, awaiting operator sign-off

**Status (2026-07-08):** The dependent-kernel Core-cleanup grind has reached its
terminal state. The Core is clean to **Idris-2 parity minus linear types on the
soundness dimension** — see spec §J.1 and the audit FINAL-STATE banner. The
unattended cron's next phase is the deferred feature **gaps**, and per its own
instruction those require **operator design sign-off** before any implementation.
This file is the durable hand-off: it frames the gaps so a brainstorming session can
start the moment the operator returns. **No gap work has been started.**

## Why we paused here

The cron authorized unattended *Core cleanup* (soundness/boundary tightening) but
explicitly gated *features* behind design approval. Everything remaining is a
feature or a faithfulness-only representation change — none is an open soundness
hole — so the autonomous mandate is exhausted. Brainstorming is interactive (it asks
one question at a time and needs your answers), so it cannot run unattended.

## What's done (so you can trust the "Core clean" claim)

- **All K1–K14 resolved.** Soundness LANDED or kernel-enforced (K1a, K2 §G.1, K3,
  K4, K5a, K6 545/599, K11a, K12 slices 1–2, K13, K14). Faithfulness-only items
  declined-with-recorded-proof (K1b `{:rewrite}` Phase B, K2 `{:prim}` migration).
- **Eight E-layer hygiene holes closed** beyond the audit (duplicate def/type/ctor
  per module, param, field, family index, GADT-ctor named domain, non-linear
  pattern) + a self-audit fix scoping those checks per module.
- **Six dependent-soundness axes probed sound:** telescope linearity, strict
  positivity, match coverage, termination (partial-by-default; δ never unfolds a
  non-terminating global), erasure relevance, universe consistency (predicative,
  `Type₀ : Type₁`, no `Type:Type`).
- Suite green at **3107** (HEAD `238b90f`).

## The deferred gaps — pick one to design first

### Group A — the cron's named feature gaps
1. **Unsafe-hole taxonomy** *(grade-wave-coupled — NOT the quick win it first looks)*.
   The 3 position-kinds (type / proof / body) + an `unsafe` keyword, with a per-hole
   safety flag `{:hole, name, safety}`. The DECISION is locked (memory
   `holes-unsafe-taxonomy-decision`) and Wave-1 K3 shipped the firewall
   (`no_hole: :reject` at release, commits f7cfa6e→a2409a8). BUT the full taxonomy's
   proof-vs-body split *is* erased-vs-relevant, so the locked note explicitly
   sequences it **with the grade wave** and calls it "its OWN brainstorm/spec". So
   this gap first needs a decision on grade-wave sequencing — a real design
   conversation, not a rubber-stamp. (Note: the `{0,ω}` erasure *soundness* is
   already enforced via the relevance check; what the grade wave adds is the
   per-binder grade *field* — a representation/faithfulness change, so this gap is a
   feature, not a soundness fix.)
2. **Bucket B / C stdlib-dependent extensions — ✅ ALREADY DONE** *(codebase audit
   2026-07-08; the `stdlib-dependent-expansion` memory was stale)*. `Std.Bounded`
   (`type Bounded indices (n: Nat)` with `First`/`Next` = Fin's FZ/FS) is complete
   and used by `Std.Vector` for length-safe indexing; `Std.Vector` is extensively
   fleshed out (singleton/replicate/is_empty/head/tail/lookup/update/set/map/zip_with/
   append/foldl/foldr/count/length/any/all); `Std.Ord` has `type Ordering = LessThan
   | EqualTo | GreaterThan` (inductive) + `compare` + the `Ord(T)` protocol. **Not a
   gap — no design needed.**
3. **FRP reactive runtime** *(already DESIGNED at scale; the gap is IMPLEMENTATION +
   one architecture fork — needs your direction, not a fresh design)*. Two things
   are already in place: (a) the **type-system foundation** — Dec/Init index algebra,
   `switch` typing, loop well-formedness — landed and oracle-tested
   (`test/oracle/frp/frp01–12`); (b) a **3314-line canonical design bible** (v12,
   `docs/cure_reactive_runtime_design_bible_v12_release_hierarchical.md`; memory
   `reactive-runtime-design-bible`) with a staged **0.34–0.37 roadmap** (0.34
   Libraries + Flow DSL → 0.35 Resource → 0.36 Reactor → 0.37 Program), plus the
   `2026-06-30-cure-dependent-types-frp-design.md` spec. What's missing is the
   **implementation**: no `Std.Signal`/`Std.Flow`/`Std.Clock` modules or
   `Cure.Compiler.FlowIR` exist in-tree yet. Because the design already exists, the
   decisions you'd own are **(i) which 0.34 slice to implement first** (e.g. the
   `Std.Signal`/`Signal.Event` core + operators, or `FlowIR` + flow lowering), and
   **(ii) the architecture fork** the bible flags: keep 0.34's **runtime
   validators**, or lift `FlowDesc`(Init/Dec/clock/type) into **static type indices**
   (Sculthorpe–Nilsson) now so verification is compile-time and codegen can erase the
   runtime graph — the "dependent-types marriage" (memory
   `dependent-types-frp-initiative`). That fork is a real prose design conversation,
   which is why it's gated on you.

### Group B — declined/deferred K-features (optional, faithfulness/parity)
4. **Canonical `Eq` transport (K1b / K5b).** Retire the `{:rewrite}` node → genuine
   J-eliminator / `Eq.rec`. Declined twice as Phase B (empirical parity regressions);
   would need a kernel-conversion improvement that removes the `bridge_step`
   workaround first. No soundness gain — pure faithfulness.
5. **Universe-level polymorphism (K7).** Level variables, `Type ℓ`, globals carrying
   level args. Soundness already met (predicative); this is ergonomics/parity.
6. **Qualified `Sym` (K12).** Module-path-qualified globals/ctors replacing bare
   atoms; enables principled cross-module disambiguation (subsumes the fn-vs-ctor
   name-collision decline) and robust serialization. Large representation change.

## Recommended next step

A codebase audit (2026-07-08) found **gap #2 already fully landed**, so the real
remaining Group-A gaps are just **#1 (unsafe-hole taxonomy)** and **#3 (FRP reactive
library/runtime)** — both substantial, neither a quick win:

- **#3 (FRP reactive runtime)** is the most design-progressed: its type foundation is
  landed + oracle-tested and it has a staged design bible, so the next step is
  designing the first runtime increment (e.g. `Std.Signal`/`Std.Flow` surface). This
  is the strongest candidate if you want to build on existing momentum.
- **#1 (unsafe-hole taxonomy)** is smaller but needs a grade-wave sequencing decision
  first.

Either is a real design conversation — which is why this stays gated on your input.
Group B (canonical `Eq` transport, universe-level polymorphism, qualified `Sym`) is
opt-in parity work with no soundness urgency.

**To proceed:** reply with a gap. For **#3 (FRP reactive runtime)** — the recommended
default — the design already exists (bible v12), so I don't need to re-design it; I
need two directions from you: **(i)** which 0.34 slice to implement first (suggest the
`Std.Signal` + `Signal.Event` core + functional operators as the smallest standalone
unit), and **(ii)** the runtime-validators-vs-static-type-indices fork. Give me those
and I'll implement the slice with per-task red-green + full gate. For **#1
(unsafe-hole taxonomy)** I'd first need the grade-wave sequencing decision. Either
way, no code lands until you've signed off on the direction.
