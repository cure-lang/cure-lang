# Actor-macro consolidation — one templated expander, three tiers

**Status:** design approved, implementation pending.
**Scope:** `lib/std/actor.cure` first (reference implementation), then `fsm`/`supervisor`/`app`, then a deferred Tier‑3 typed layer.
**Layer:** P (parser, for the optional whole‑module `quote` step and 1e's family raw‑body branch) + stdlib Cure (`lib/std/*.cure`). **TCB delta: zero** — no change to `lib/cure/core/*`.

## 1. Motivation

`Std.Actor` grew three redundant expansion backends as the macro facility matured toward quasiquotation:

- **Gen A** — 16 positional `becomes lift module name` templates (`actor X state T messages M handle_cast …`), each re‑spelling all six GenServer callbacks inline just to vary one.
- **Gen B** — the `derive` shorthand (`… derive <cast_body> (call <call_body>)? computed by derive_actor`), whose expander `derive_actor` calls the thin wrappers `emit_actor`/`emit_actor_call`.
- **Gen C** — the structured surface (`macro actor` + `syntax family ActorDefinition` + `expands with derive_actor_family`).

All three funnel into one backend pair, `emit_actor_parts`/`emit_actor_call_parts`. Gen C is a strict output‑superset of Gen B: the wrappers `emit_actor`/`emit_actor_call` merely pre‑fill the same defaults (`default_actor_init`, the `ActorMessage` enum, `Raw(SOpaque)` bodies) that `derive_actor_family` computes richly from optional family fields.

Two problems follow. First, **duplication**: three surfaces, three expander entry points, ~200 lines of repeated GenServer skeletons. Second, **inelegance**: the surviving backend is hand‑assembled AST — `gen_server_module(module_name, state_type, [function("init", [parameter(...)], init_type, body), …])` and raw surgery like `Node(:match_arm, values, [block([let_binding("answered", call("Std.Otp.reply", [...])), tuple([...])])])`. `quote` appears only at the leaves. The expander reads like AST plumbing, not like the code it emits — the opposite of the Template‑Haskell / Lean ergonomics we are targeting ("as much user friendliness as possible… in line with meta‑languages people actually like using").

The goal: **one expander over one backend, written as quasiquote templates**, reached by a terse Tier‑1 shorthand and a structured Tier‑2 family, with a typed Tier‑3 layer added last.

## 2. Background: `computed by` vs `expands with`

Both reach the same runtime contract — *call an elaborator function with a record, get `Syntax` back* — which is why the three generations can be folded into one.

- **`computed by <fn>`** (`kind: :computed`, `parser.ex` ~6466) is the low‑level primitive: a positional `syntax <pattern>` whose holes are captured into an auto‑generated record; at expansion the compiler calls `<fn>(record) -> Syntax`.
- **`expands with <fn>`** (`kind: :expands_with`) is the structured surface built on top. A named `syntax family` (typed fields, `optional` markers, keyword labels, composable via `includes`) + `accepts` + `expands with <fn>` is **lowered into a `:computed` rule** by `MacroFamily.computed_rule/2` (`lib/cure/compiler/macro_family.ex`:34‑97): it generates the `<Family>Syntax` record, packs the leading holes plus a `definition` record as the elab inputs, and sets `elab: <fn>`.

`expands with` is therefore `computed by` plus a generated, typed, optional‑aware record schema and block parsing. Because `derive_actor` and `derive_actor_family` are the *same kind of thing* (elab functions for `:computed` rules) and the latter is a strict superset, every actor surface can route through `derive_actor_family` alone.

## 3. Verified feasibility: what `quote` can hold

`parse_quote` (`parser.ex`:7694) parses the inner form with the ordinary expression grammar (`parse_expr(state, 0)`). Empirically probed on this branch:

| Form | Result |
| --- | --- |
| `quote (fn init(x: Int) -> Int = x)` | **parses** — single `:function_def` |
| `quote %[:ok, initial]` | **parses** — expression body |
| `quote (mod Gen … multiple decls …)` | **fails** — `expected :rparen, got :keyword` |
| `quote` + indented multi‑declaration block | **fails** — `unexpected_token :newline` |

**Verdict:** `quote` holds exactly one form — a single expression *or* a single declaration — but not a `mod` block and not an indented declaration block.

**Implication:** the templated rewrite is available *now* at per‑declaration granularity. Each `function("handle_cast", [parameter("message", variable("Message")), parameter("state", variable("State"))], result_type, body)` becomes

```
quote (fn handle_cast(message: Message, state: State) -> Effect(Tuple(Atom, State)) = $(body))
```

which reads like the code it emits. The module wrapper (`mod … behaviour … [decls]`) still needs the thin `gen_server_module` assembler. Closing that last gap — one template for the whole module — is a self‑contained parser feature (§4, step 1c), not a blocker.

## 4. Stage 1 — Actor (Tiers 1 & 2, templated)

The reference implementation. Every step is independently green‑gated; the byte‑identical goldens are the spine that lets a backend rewrite be *proven* safe, not assumed.

### 1a — Fold to one expander
Retire the standalone bodies of `derive_actor`, `emit_actor`, `emit_actor_call`, and the `ActorSyntax` capture record. `emit_actor`/`emit_actor_call` are deleted outright (their only caller, the old `derive_actor` body, is gone). `derive_actor` is *rewritten in place* — same name, same `syntax … computed by derive_actor` target in `ActorContainers`, so that grammar rule needs no change — into a one-line adapter: it builds an `ActorDefinitionSyntax` (name→`ModuleName`, `state_type`→`state`, `cast_body`→`on_cast`, `call_body`→`on_call`, remaining optionals `None`) and delegates to `derive_actor_family`. Every surface then routes through `derive_actor_family` → `emit_actor_parts`/`emit_actor_call_parts`. This routes the `derive` rule through the family so 1a is independently gate‑able. It works precisely because `derive`'s body **is** Cases (`cast_body → on_cast` type‑checks); the 15 raw `becomes` forms are **not** Cases and do **not** route this way (see the 1e correction — they keep their raw bodies through the family's raw branch). Output is byte‑identical because Gen C fills the same defaults the wrappers hardcoded.
**Guard:** `GDerived` BEAM‑SHA256 golden byte‑identical + the 19 behavioral tests in `test/cure/compiler/actor_computed_test.exs` (immutable — they pin the `derive` surface).

### 1b — Templatize the backend
Rewrite `emit_actor_parts`/`emit_actor_call_parts` and the handler transforms (`actor_call_handler_arm_node` et al.) as per‑declaration `quote` templates with `$()` splices; a thin `gen_server_module` assembles the templated declarations and the variable‑length message enum. The expander now reads as literal Cure.
**Guard:** the same goldens, still byte‑identical.

### 1c — (optional infra) Whole‑module `quote`
Extend `quote` to accept an indented declaration block and a `$(decls ...)` group‑splice into a module body, collapsing the skeleton into a single template. Sequenced *after* 1b so 1b stands on its own; if this proves thorny it slips to its own follow‑up without blocking Stage 1. P‑layer only — outside the TCB.
**Guard:** goldens byte‑identical + new `quote` round‑trip tests (parse → print → reparse) covering the block and group‑splice forms.

### 1d — Body passthrough (the Gen C gap)
Add `optional body Declarations` to the `ActorDefinition` family; thread a `List(Syntax)` of extra user declarations through the emitters and `append` them into the emitted block. This gives the structured surface the arbitrary‑trailing‑declarations power only the Gen A `with`/bare‑body templates had.
**Guard:** a new behavioral test for a user‑declaration‑carrying actor; no‑body goldens unchanged.

### 1e — Terse shorthand + consolidate Gen A backends

**Correction to the original framing (2026‑07‑16).** The original 1e treated all 16 Gen A `becomes lift module name` forms as one homogeneous set of "terse forms delegating to the expander," to be deleted after routing through `derive_actor_family`. That is **wrong for 15 of the 16**, and the error is a category confusion. Delegation works by building an `ActorDefinitionSyntax` with `cast_body → on_cast` — but `on_cast` is typed to accept **Cases** (constructor‑pattern arms) and rejects everything else (`guarded_handler`, `non_constructor_pattern`). Only the `derive`/`call` rule's body *is* Cases (`match message / Inc -> …`); the other 15 forms' bodies are **raw callback expressions** (`%[:noreply, state]`, or a `pickup` value‑equality block with `else`). `cast_body → on_cast` is a category error for them. The 16 forms are therefore **two populations**:

- **Derived shorthand** (`derive`/`call`, Gen B): body is Cases → genuinely folds into `derive_actor_family`, **byte‑identical**, and is genuine Tier‑1 sugar. Keep the 1a adapter / mechanism‑(b) routing here.
- **Raw callback surface** (the 15 `becomes` templates): an **escape hatch** (Tier‑0, see §7), not sugar over the derived family. It carries expressiveness the derived surface has no grammar for — value‑equality dispatch, `else`, guards, hand‑written callbacks. It is **preserved**, not deleted. What consolidates is the *backend*: the 16 duplicate spelled‑out templates collapse into **one shared raw emitter**.

**Mechanism (decided at planning, 2026‑07‑16): A — unified family.** The `ActorDefinition` family gains a **raw‑body branch** as an alternative to the `on_cast` Cases branch, so one family is the single home for both surfaces: the Cases branch lowers to `emit_actor_parts` (byte‑identical); the raw branch lowers to the shared raw emitter. (Mechanisms (a) keyword‑alias and (b) thin `computed by` adapters were the original options; both presumed the raw body was Cases, so both are superseded for the raw population.)

**Byte‑identical is not the guard for the raw fold.** Traced end‑to‑end (`parser.ex:parse_lift_module` → `lift_module.ex:ordinary_module_ast`): templates split `callback` lines into `meta[:callbacks]`, emitted **first** (`callback_defs ++ declarations`); the computed builders have no callbacks slot (all → `declarations`) and set `inherit_imports:false`. Function order and that split both reach the `.beam` bytes, so a byte‑identical computed emitter would have to reconstruct the parser's callback‑map machinery — deep and fragile. The raw fold's guard is therefore **behavioral‑equivalence**: the ~30 immutable behavioral tests (`container_macro_test.exs`, `actor_computed_test.exs`) + each demo's Mix suite + full suite. The 15 raw characterization goldens (`Raw01…Raw16`, task #23) are a *re‑freezable* net — re‑bless them to the consolidated output with justification when the fold intentionally reshapes emission. Strict byte‑identical stays the bar only for the 6 original quote‑port goldens.

**Tier‑3 seam.** The consolidation isolates the procedural reply‑type analysis (`derive_reply_contract`/`infer_reply_type`, the literal‑subtype sniffing §6 flags) behind a single clearly‑marked function the family calls, so a future typed elaborator swaps it at one site.

**Demo migration is mostly a no‑op.** For a value‑dispatch or custom‑callback actor the "surviving surface" *is* the raw one, so it stays. Only demos whose dispatch is genuinely constructor‑arms move to `derive`/`call`. `logger`/`clock` (value‑dispatch + `else`) and `curator` (custom callbacks) stay raw; the other nine (`voice`, `sequencer`, `painter`, `echo`, `worker`, `metrics`, `queue`, `pool`, `vicure/test_syntax`) are audited case‑by‑case. Nothing deletes the raw *surface*; only duplicate backend templates are removed.

**Already done:** the dead `L177` form (no‑`state` `initial`+`handle_cast`, callbacks typed against free `p`, never pinned → fails to compile, referenced nowhere) was dropped ahead of the fold (`d1fa8dc9`).

**Guard (summary):** behavioral‑equivalence for the raw fold (immutable behavioral suite + demo suites + full suite); byte‑identical for the derived shorthand and the 6 quote‑port goldens. (`phase35/run-on-unix.sh` is a generic‑unix AtomVM harness in the separate `esp32-beam` repo, not part of `cure-lang` — not applicable here.)

## 5. Stage 2 — fsm / supervisor / app

Replay 1a–1e per sibling against its own golden (`GFsmDerived`, `GSup`, `GApp` in `actor_quote_golden_test.exs`), one file at a time, each independently gated:

- **`fsm`** mirrors actor — it has a Gen B `derive_fsm` + `emit_fsm`/`emit_fsm_parts` and a `FsmSyntax` record to fold, plus `syntax family FsmDefinition` + `derive_fsm_family`.
- **`supervisor`** / **`app`** are lighter — `syntax family …Definition` + `derive_…_family` + `…Containers` templates, no separate Gen B layer.

If 1c landed in Stage 1, all four collapse to whole‑module single templates here. These are near‑mechanical replays of the proven actor pattern.

## 6. Stage 3 — Tier 3: typed, Lean‑`MetaM`‑style macros (deferred)

An elaborator‑integrated macro that sees inferred types and datatype structure, added last. It removes the one irreducibly‑uncouth remainder of Stages 1–2: syntax **analysis**. Quasiquotation makes *synthesis* (producing output) elegant, but it does nothing for *analysis* (inspecting the user's syntax). The reply‑type derivation `derive_reply_contract` / `infer_reply_type` / `reply_expr_type` walks the user's `call` body and sniffs literal subtypes (`:integer → Int`, `:float → Float`, `:symbol → Atom`, `:boolean → Bool`) to *guess* the reply type — a hack that is irreducibly procedural at Tier 2. A typed macro asks the elaborator for the *inferred* type instead.

Tier 3 is also the principled home for deriving and the OTP‑metatheory pid‑index / `ReplyOf(req)` work (see `https://github.com/cure-lang/cure-otp/tree/main/docs/research/process-types/`). It gets its own brainstorm → spec → plan when we reach it; recorded here as direction, not detail.

## 7. Roadmap context: the Lean‑style three tiers

The end state realizes the Lean‑4 macro architecture:

| Tier | Lean analog | Cure realization |
| --- | --- | --- |
| 0 — raw escape hatch | raw `syntax` + hand‑written `elab` | the raw callback surface: hand‑written GenServer callbacks with arbitrary bodies (value‑dispatch, `else`, guards). Preserved permanently; after 1e it routes through one shared raw emitter behind the `ActorDefinition` family's raw branch, not 16 duplicate templates |
| 1 — declarative shorthand | `macro` / `macro_rules` | `derive`/`call`: terse forms whose body *is* Cases, delegating to the Tier‑2 expander (byte‑identical) |
| 2 — procedural expander | `elab` / `elab_rules` | `syntax family` + quote‑based `expands with` expander over one backend |
| 3 — typed metaprogramming | `MetaM` / elaborator reflection | typed access to inferred types + datatype structure; swaps the procedural reply‑type analysis at the single seam 1e isolates (Stage 3) |

Tier 0 is not a stage of the progression but the escape hatch beneath it — the tiers are a progression of *structure and typing*, and a raw hand‑written‑callback surface sits outside that progression by definition (as Lean's raw `elab` sits under `macro`/`macro_rules`). Retiring Tier 0 becomes conceivable only if a Tier‑3 typed elaborator grows expressive enough to subsume value‑dispatch + guards + custom callbacks — a "maybe never," and acceptable as such. Stages 1–2 build tiers 1–2 and consolidate Tier 0's backend; Stage 3 adds tier 3.

## 8. Testing and guards

- **Byte‑identical goldens** (`actor_quote_golden_test.exs`: `GDerived`, `GStructuredCall`, `GLifecycle`, `GFsmDerived`, `GSup`, `GApp`) are the anti‑regression spine for the derived surface. Any derived‑path edit keeps them byte‑identical, or is consciously re‑blessed with justification.
- **Raw characterization goldens** (`Raw01…Raw16` in the same file, task #23) are the raw fold's *re‑freezable* net, not a byte‑identical spine — the raw fold is guarded by behavioral‑equivalence (see 1e), and these are re‑blessed to the consolidated output with justification when the fold intentionally reshapes emission.
- **Behavioral tests** (`actor_computed_test.exs`, `container_macro_test.exs`, immutable) pin both the `derive` surface and the raw callback surface across the fold — this is the raw fold's real guard.
- **New tests** cover body passthrough (1d), init‑mode precedence (`initial` wins over `init`, already handled by `derive_actor_init`), and the whole‑module `quote` forms (1c).
- Red‑green throughout; scoped `mix test <file>` during iteration, one full suite alone at each stage gate.

## 9. Constraints

- No change to `lib/cure/core/*` (TCB). The one parser step (1c) is P‑layer.
- Ghost‑writer commits (`--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no co‑sign); explicit‑pathspec staging only.
- Author stdlib in `lib/std/`, never `priv/std/` (generated bundle).
- One `mix` build at a time.

## 10. Open decisions carried to planning

1. **~~Terse delegation mechanism (1e)~~ — RESOLVED 2026‑07‑16.** The original keyword‑alias vs per‑form‑adapter choice was moot: both presumed the raw body was Cases (a category error for 15/16 forms — see the 1e correction). Resolution: mechanism **A** (unified `ActorDefinition` family with a raw‑body branch) preserves the raw surface as Tier‑0; the raw fold is guarded by **behavioral‑equivalence** (immutable behavioral suite + demo suites + full suite), not byte‑identical. Only `derive`/`call` (genuine Cases) stays byte‑identical Tier‑1 sugar.
2. **Whole‑module `quote` (1c):** include in Stage 1 after 1b, or defer to its own follow‑up if the parser extension proves thorny. Neither choice blocks 1a/1b/1d/1e.
