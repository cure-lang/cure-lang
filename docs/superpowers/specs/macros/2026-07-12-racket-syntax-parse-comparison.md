# Racket `syntax-parse` vs. Our Self-Proving Macros — Concrete Comparison

**Date:** 2026-07-12
**Source read:** `~/Develop/racket` (shallow clone), specifically
`racket/collects/syntax/parse/report-config.rkt` (46 lines) and
`racket/collects/syntax/parse/private/{runtime-report.rkt (830), residual.rkt, rep.rkt}`.
**Purpose:** ground `2026-07-11-self-proving-macros-design.md` against the system it
names as the error-quality ceiling — where we match it (and should port its
machinery), where we are strictly stronger, and what to steal.

## 1. What syntax-parse actually does (grounded)

syntax-parse is the reference for *parse-error quality*. Its algorithm, from
`runtime-report.rkt`:

1. A failing parse produces a **failure SET**, not a single error — every way the
   parse could have gone, each carrying a **progress** (how far it got) and an
   **expectation stack** (what was expected at each frame).
2. `handle-failureset` → `invert-failureset` → **`maximal-failures`**: select the
   failures that made the *most progress* (`maximal/progress`, a lexicographic-ish
   order over frames, `:108-127`). **You do not report the first failure; you report
   the one that got furthest.** (A hard-won lesson — the `:47-50` comment records that
   pre-6.4 versions grouped differently.)
3. Render a **`report`** = `(message context stx within-stx)` (`:79`): the message
   (from expectations), a **context trace** (the `(Listof String)` of "while parsing
   X" frames), and — the subtle UX bit — an **"at" vs "within"** pair of syntax
   objects (`:81-96`): the *precise* error point and the *closest enclosing original*
   term, because the error often isn't at a real subterm (a too-short list blames the
   tail, `()`, "within" the whole form).
4. **Descriptions are OPTIONAL.** `#:description` on a syntax class defaults to `#f`
   (`rep.rkt:214`), falling back to the class *name*; `expect:thing`'s `description`
   field is `String/#f` (`residual.rkt:319`); `report-config.rkt` is a 46-line
   *parameter* of four rendering defaults (`literal-to-what`, etc.) you *may* override.
   Semantic guards (`#:fail-when`/`#:fail-unless`, `~describe`) attach *ad-hoc string*
   messages. Nothing is ever required.
5. `current-failure-handler` is a **parameter** — the whole failure-handling step is a
   replaceable seam.

## 2. Where our design MATCHES it — and should PORT its machinery

Our base spec's "default error machinery" (§2) is, essentially, syntax-parse
rediscovered, and our self-proving §3 builds on it. These are the same and we should
adopt syntax-parse's *implementation*, not reinvent it:

- **Progress-ordered "parsed furthest" selection.** Our §2 says this in one line;
  syntax-parse's `maximal-failures`/`invert-ps` is the battle-tested realization.
  **Port it** — SP2's `Diagnosis` selection should be "collect the failure set, pick
  maximal-by-progress," not "first failure wins."
- **Automatic expectation messages from typed holes** (our §2 = their `expect:thing`).
- **A parsing context trace** ("while parsing transition edge … in reducer Door", our
  §2 = their `report` `context`).
- **Optional author descriptions** (our `describe`/`explain` = their `#:description`/
  `~describe`) and a rendering-customization seam (our nothing-yet = their
  `report-config`).

## 3. Where we are STRICTLY STRONGER — and why

Three of these are type-system dividends Racket structurally cannot collect, because
**Racket is untyped**: there is no "well-typed expansion" for it to check, so several
of our guarantees are not even *expressible* there.

1. **Descriptions are required and exhaustive, by type.** syntax-parse *permits*
   `#:description`; we *require* it — an undescribed failure point in the derived
   `Diagnosis` is a compile error in the macro (self-proving §3.2, exhaustiveness like
   case-coverage). Racket's default-to-name is exactly the "convenient but silent" gap
   we close. This one is achievable in Racket-in-principle (it is a policy, not a type
   need) — but Racket does not do it.
2. **Semantic failures are first-class and exhaustively described.** syntax-parse's
   `#:fail-when` produces an ad-hoc string; our `fail C(args)` + required `explain`
   (§3.4) folds semantic failures into the *same* typed enumeration and the *same*
   exhaustiveness check as structural ones. Their semantic errors are unstructured; ours
   are enumerated, typed, and can't be left undescribed.
3. **Generative expansion proof — the one Racket cannot have.** syntax-parse has
   *nothing* like self-proving §4. It proves nothing about what an accepted program
   *expands to*; a Racket macro can expand to broken code and you learn at use-time (or
   from your own tests). We fuzz the closed, typed grammar and **prove every accepted
   program expands to well-typed Core** (full run every compile). This is impossible in
   Racket precisely because there is no type the expansion must preserve. **This is the
   headline divergence: our type system converts "the author tested well" into "the
   compiler proved it," and Racket's untypedness forecloses it.**
4. **Required per-rule worked examples** (§5) — no syntax-parse analog.
5. **Total, terminating expansion.** Our elab functions are size-change-certified total
   (base §5), so Cure compilation provably terminates *with* user macros — "a property
   Lean does not have," and one Racket's expander (fuel-bounded, not total) does not
   guarantee either.

## 4. What to STEAL — concrete, with anchors

1. **The failure-SET + progress-maximal algorithm** (`runtime-report.rkt`
   `handle-failureset`/`maximal-failures`/`invert-ps`, `:53-135`). Report the furthest
   failure(s), not the first. This is the core of parse-error quality and it is subtle;
   do not reinvent it in SP2.
2. **The "at" vs "within" error-point pair** (`:79-96`). Point the error at the precise
   spot *and* name the enclosing original form. We would otherwise mis-point errors on
   too-short/too-long forms. Adopt the `report` struct shape directly:
   `(message, context-frames, at-stx, within-stx)`.
3. **A `current-failure-handler`-style seam** — a facility-level override of the whole
   failure-handling step, above per-macro `explain`. Useful for composition (a
   stacked-DSL outer macro reframing an inner failure) and tooling (LSP consuming the
   raw failure set). Cheap to add; keep it.
4. **Expectation dedup/simplification** (the `:18-20` TODO: "expected D" rather than
   "expected D or D for R"). A rendering polish that materially improves messages.
5. **`report-config`'s rendering-parameter idea** — a small, overridable table of "how
   to render a literal/datum/kind in a message," so message *style* is centrally
   consistent and localizable, independent of the *content* each macro's `explain`
   supplies.

## 5. The load-bearing conclusion

Racket sets the ceiling for **parse-error quality**, and we should meet it by *porting*
syntax-parse's failure-set/progress/at-within machinery as the substrate for
self-proving Mechanism 1 — reinventing it worse would be the likeliest way to ship
mediocre errors. On top of that substrate we add the one thing Racket declines to do
(make descriptions a required, exhaustive, type-checked obligation, structural *and*
semantic), and then the thing Racket *cannot* do (prove, by generation against the
kernel, that every accepted program expands soundly). **Match Racket where it is the
ceiling; exceed it exactly where our types give leverage it structurally lacks.**

## 6. Feed-forward into the plan

- **SP2** (Tier 3 + typed errors): implement `Diagnosis` selection as syntax-parse's
  maximal-by-progress over a failure set (steal #1); use the `(message, context, at,
  within)` report shape (steal #2); add the failure-handler seam (steal #3).
- **SP1** (grammar/hole parsing): the progress instrumentation must be threaded from
  the start — record how far each rule got when matching a use-site, so the furthest
  wins. Retrofitting progress later is painful (syntax-parse's own history shows it).
- **SP3** (generative proof) has no Racket source to borrow — it is genuinely ours; the
  Antigen generator + kernel-check gate is the reference, not `syntax-parse`.
