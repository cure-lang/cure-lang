# Ergonomics batch spec: `|>`, `where`, let/where inference, `do`, `beam_ops` evolution

Status: DRAFT / approved-for-implementation. Surface-ergonomics features plus the `Effect`-model analysis that
governs them. Contents: **§0** the `Effect` model (distinct type, `pure` in / no safe `run` out, extraction only via
bind, runtime boundary, functional-core/effectful-shell for replies); **§1** leading `|>`; **§2** `where`; **§3**
let/where type inference; **§4** `do` as a **stdlib macro over a `Monad` interface**; **§5** `beam_ops` evolution
(retire the aliases into `do`+functions; add a typed `receive`/`select` block).

Each is independently shippable; recommended order is **(3) inference → (4) do → (1) pipe → (2) where → (5)
surface**, because inference and `do` remove the most pervasive noise (`: T` annotations and `let _ =`).

Layer key (from the porting charter): **P** = parser/lexer (`lib/cure/compiler/*`), **E** = elaborator
(`lib/cure/elab/*`), **K** = kernel/TCB (`lib/cure/core/*`). Everything here is P + E + stdlib; **no K changes** —
`Effect` itself is unchanged.

---

## 0. The `Effect` model (governs `do`) — verified, not assumed

- `Effect(T)` is a **distinct type**. Conversion is congruence-only (`conv.ex` `conv_struct?({:veffect_type,a},
  {:veffect_type,b},…)`); there is **no** `Effect(T) ≡ T` rule. So `Effect` is *not* structurally transparent.
- Elimination is the **`let`-as-bind**: `let x = e in body` with `e : Effect(T)` binds `x : T`, `body : Effect(U)`
  (the "effects into Core via inert former, let→bind, no dup/inline/erase" decision).
- **Matching directly on an effect scrutinee is REJECTED** (tested): `match subject_receive(s,5) { Some… }` fails;
  you must bind first (`let r = subject_receive(s,5)` then `match r`). So you cannot extract a `T` from `Effect(T)`
  except through the disciplined bind.
- The only "transparency" is **checking-mode auto-`pure`**: under an `Effect(R)` goal a pure expression is checked
  against `R` and lifted with `pure` (`elaborator.ex` `effect_goal?`/`elaborate_effect_branch`, ~lines 6103–6122).

**Ramification for `do`:** none that forces a semantics change. `do` is pure sugar over `let`-as-bind; the last
expression of a `do` block lands in `Effect(R)` position and auto-`pure`-lifts if pure. We do **not** need to make
`Effect` opaque — it already is, appropriately. (If we ever wanted the *stronger* structural guarantee — no
`pure`/`run` boundary leaks — that is a separate, deliberate change, out of scope here.) The one design rule this
implies: `do` must keep the bind explicit (`x <- e`), never silently peel an effect scrutinee in a `match`.

### 0.1 Extraction, the boundary, and reply handling (design invariants)

- **`pure : T -> Effect(T)` exists (injection); there is deliberately NO `run : Effect(T) -> T` (projection).**
  Verified: no `run`/`perform`/`unwrap` in the stdlib. The asymmetry is the whole point — `Effect` *tracks which
  code performs effects*; a safe `run` would let pure-typed code perform effects and reorder/relocate them. This
  is Haskell `IO` / Koka / Frank. Keep it.
- **You never extract into pure code; you bind and stay in the monad.** `let x = e in body` / `x <- e` names the
  result `x : T` but `body : Effect(U)` — the continuation is still effectful. The only "extraction" is the bind,
  which preserves the discipline.
- **The runtime is the boundary.** `start/0`, actor loops, and gen_server callbacks return `Effect(T)`; the BEAM
  *runs* them. Because `Effect` erases to nothing (`Effect(T)` and `T` share a representation — verified: calling an
  emitted `run/0` returns the bare value), "running" is not a callable op — executing the compiled code performs
  the effects and yields the `T`. From the host (Erlang/Elixir/tests) you just call the function.
- **`run` is an ordinary function.** `Effect(T)` and `T` share a runtime
  representation, so `run` adds no wrapper and does not require a language-level
  `unsafe` marker. Unsafe interop operations remain marked individually.
- **Reply-handling corollary (functional core / effectful shell).** Obtaining a reply (`call`/`subject_receive`) is
  effectful, so the reply's *handling context* is in `Effect` — but the reply *logic* stays pure: apply pure
  functions to the bound reply and `pure`-lift (`r <- call(s, q); pure(summarise(r))`). Cure's OTP already embodies
  this — `handle : (r: Req) -> ReplyOf(r)` is a **pure, total** function (where the dependent reply typing and its
  proofs live); only `serve`/`reply` (discharging the linear cap, sending) is effectful. Design rule: keep the
  verifiable per-request reply logic pure; the effect wraps only the `call`/`reply`/`receive` boundary. `do`/`<-`
  is what makes that shell read cleanly.

---

## 1. Leading `|>` on a continuation line (finish multi-line pipes)

**Now:** trailing `|>` works (`a |> \n f()`, fixed 2026-07-19). Leading `|>` — the Gleam/Elixir idiom — fails:
`a\n  |> f()` errors `{:unexpected_token, :pipe}` because the newline (and, when the `|>` line is indented, an
`:indent`) terminates the expression before the Pratt loop sees the pipe.

**Goal:** `a\n  |> f()\n  |> g()` parses identically to `a |> f() |> g()`.

**Design — lexer continuation-line detection (preferred).** A logical line does not end if the **next** line's
first non-whitespace token is a *continuation operator* (`|>`, and reserve the mechanism for `.`-chains too). The
lexer, at a newline, looks ahead: if the next non-blank line begins with `|>`, it suppresses the `:newline` (and the
`:indent`/`:dedent` that the continuation line would otherwise induce) for that break, so the pipe chain is one
logical line. This keeps the indent stack balanced (no orphan `:indent`) and needs no parser change.

- Files: `lib/cure/compiler/lexer.ex` (newline/indent emission).
- Alternative (parser-only): in `parse_infix`, when `peek` is `:newline` and the next non-layout token is `:pipe`,
  skip the layout and continue the loop. **Rejected** as primary: it must consume a balanced `:indent`/`:dedent`
  pair around the pipe line, which risks unbalancing the indent stack the block parser relies on. The lexer
  approach avoids emitting the layout tokens in the first place.

**Edge cases:** a leading `|>` that is *not* a continuation (start of file / block) → the lexer only suppresses the
break when a left operand precedes on the prior logical line; otherwise it's a normal (error) `:pipe`. Blank/comment
lines between the operand and the `|>` are skipped. Trailing `|>` continues to work (unchanged).

**Tests:** extend `pipe_multiline_test.exs` with leading-`|>` forms (indented and same-column), a mixed
leading+trailing chain, and a negative (a `|>` with no left operand). Run the full parser suite + gate (parser
change).

---

## 2. `where` clauses

**Goal:** function-local helper definitions (values *and* functions), scoped to one `fn`, read result-first:
```
fn steps(set: TagSet, s: Session) -> Nat = match s
  SEnd()      -> Z()
  SRecv(t, k) -> steps_pick(member(set, t), steps(set, k))
where
  fn steps_pick(handled: Bool, rest: Nat) -> Nat = match handled
    T() -> S(rest)
    F() -> Z()
```

**Surface:** a `where` block after a `fn`'s body, at the fn's indentation, containing a sequence of `fn …` and
`name = expr` bindings. Bindings are **mutually recursive** and may reference the enclosing fn's parameters and each
other.

**Desugaring (the load-bearing decision):**
- **`where`-VALUES** (`name = expr`) → wrap the body in a `let name = expr in …` chain (innermost = body).
  Recursive value bindings are unusual; disallow value self-reference initially (only functions recurse).
- **`where`-FUNCTIONS** (`fn h(…) = …`) → **lambda-lift to a fresh private top-level definition**, NOT a let-bound
  lambda. Free variables of `h` that are the enclosing fn's parameters become **extra leading parameters** of the
  lifted global, and every call site of `h` in the body is rewritten to pass them. The lifted name is
  gensym-namespaced (`steps$steps_pick$<n>`) and marked `local`/non-exported.
  - **Why lifted, not a lambda:** the kernel's A6 freezing keeps a def folded when unfolding it re-exposes a stuck
    `case`; the `_pick`/decision-as-argument proof idiom depends on the helper being a **global application** so the
    decision stays a visible argument of a frozen global-headed form. A let-bound lambda would change that frozen
    shape and break existing proofs (`mailbox_exhaustive`, merge-sort family). So `where fn` ≡ "private top-level
    fn," semantics-identical to writing it at module scope today.

**Implementation:**
- P: parse the `where` block (attach as `:where` metadata / a sibling node on the `:function_def`).
- E: a pre-elaboration pass (`lib/cure/elab/declarations.ex` or `program.ex`) performs (a) capture analysis of each
  `where fn` over the enclosing params, (b) lambda-lifting to new `{:function_def}`s, (c) call-site rewriting,
  (d) `let`-wrapping for `where` values. Then ordinary elaboration proceeds — the kernel never sees `where`.

**Edge cases:** a `where fn` that captures no params lifts trivially. Name shadowing (a `where` name equal to a
module global) resolves to the `where` binding within that fn. Dependent types in `where fn` signatures work
because it's an ordinary lifted fn. Nested `where` (a `where fn` with its own `where`) — allow, recursively.

**Tests:** `where` value-only, function-only, mixed; a `where fn` capturing a param; a proof using a `where`-lifted
`_pick` still checks (guard against the A6 regression); go-to-def / namespacing (the helper is not visible at module
scope). Golden: a before/after pair proving byte-identical emitted BEAM to the module-scope form.

---

## 3. Infer let/where binding types (drop `: Subject(Cmd)`)

**Problem:** `let s = new_subject()` fails `:let_needs_annotation` / `:unsolved_metavariables`, because
`new_subject : {m:Type} -> Effect(Subject(m))` has a **return-only implicit** `m` that the elaborator tries to solve
at the RHS, before the body's use (`subject_send(s, Inc())`, which forces `m = Cmd`) is seen. Same for `self`,
`new_selector`.

**Goal:** `let s = new_subject()` (no annotation) succeeds, `m` solved from later use.

**Design:** postpone the unsolved return-only metavar past the `let` and solve it from the body's constraints,
reusing the existing postponement machinery (`implicit-argument-postponement`, `deferred-domain metavar`). Concretely
in `elaborate_let` (E): when the RHS elaborates to a type containing unsolved metavars that are *return-only* (not
determined by any explicit argument), do NOT force them at the binding; bind `x` at the metavar-carrying type, elaborate
the body (which adds constraints), then run the solver over the whole `let` and require all metavars solved by the end
of the enclosing definition (else the existing `:unsolved_metavariables` error, now only when genuinely ambiguous).

- The binder type in Core is the *solved* type once the body pins it; if still unsolved at the definition boundary,
  report a **source-located** "cannot infer type of `x`; annotate it" (ties into the diagnostics work).
- `where`-value bindings inherit the same treatment (they desugar to `let`).
- Guard: do not postpone metavars that are *relevant to erasure/coverage decisions* at the binding point; those must
  be solved eagerly (correctness). Only postpone when the metavar is purely a type index awaiting a later use.

**Implementation:** E only — `elaborator.ex` let-elaboration + the unifier/solver (`unify.ex`, `resolution.ex`).
No K change (the kernel still receives fully-solved Core).

**Risks:** over-postponement could accept genuinely-ambiguous programs (a `let s = new_subject()` never used) — keep
the definition-boundary "all solved" check so ambiguity is still rejected, just later. Regression-test that
`:unsolved_metavariables` still fires for truly-unconstrained bindings.

**Tests:** `let s = new_subject()` + use → OK (no annotation); unused `let s = new_subject()` → still rejected with
the new readable message; `self()` and `new_selector()` inference; a chain where the pin comes two `let`s later.

---

## 4. `do`-notation

**Goal:** kill `let _ =` and make bind-vs-perform explicit:
```
do
  s <- new_subject()             -- bind: s : Subject(Cmd)
  subject_send(s, Inc())         -- bare statement (perform, discard) — desugars to let _ =
  msg <- subject_receive(s, 100) -- msg : Option(Cmd)
  match msg
    Some(m) -> handle(m)
    None()  -> timed_out()
```

**`do` is a STDLIB MACRO, not a parser feature.** It is pure syntax→syntax — exactly the "each macro rule produces
ordinary Cure syntax" doctrine that `beam_ops`/`behavior` already follow — so it lives in the stdlib (`Std.Monad` /
prelude), is user-inspectable, revertible without touching the compiler, and needs **zero E/K change**. This
supersedes the earlier "P-layer transform" framing.

**Desugaring (uniform, monad-generic via `and_then`):** a `do` block is an indentation-delimited statement sequence;
the macro walks it and emits:
- `pat <- e`  →  `and_then(e, fn(pat) -> <rest>)`
- bare `e` (non-final) → `and_then(e, fn(_) -> <rest>)`
- `let pat = e` (pure) → `let pat = e in <rest>` (a genuinely pure binding; distinct from `<-` for the reader)
- final `e` → `e` (the block's result; auto-`pure`-lifts if pure, via existing `effect_goal?` handling)

`and_then` is resolved by coherence on the block's monad. This one macro covers **`Effect` AND `Option`/`Result`/
`List`/`Parse`** with no special-casing, because:

- A `Monad` interface (`pure`, `and_then`) is introduced; the per-type instances are nearly free — `flat_map`/
  `and_then` already exist (`option.cure`, `result.cure`, `list.cure`, `iter.cure`).
- **`Effect`'s instance is just the `let`-bind wrapped in a function:** `fn and_then({a},{b}, e: Effect(a),
  f: (a) -> Effect(b)) -> Effect(b) = let x = e in f(x)`, with `pure` = the existing effect embedding. So `Effect`
  `do` bottoms out at exactly today's disciplined `let`-as-bind — no new Core, discipline intact.

**Grammar dependency: `<-` must be lexable.** The macro has to tell `pat <- e` from a bare statement from `let`.
Either (a) add `<-` as a token (small P change; it is currently free and distinct from the `<-|` Melquiades op) and
dispatch on the resulting node, or (b) capture the `do` body as a raw `block-until-dedent` and split on `<-` inside
the derive (the `<body: … until dedent>` capture already exists for `behavior`/`actor`). Prefer (a).

**Span-stamping (the real risk).** A macro-expanded `do` reports elaboration errors against the synthesized
`and_then`/`let` chain, so a type error inside a `do` can point at generated syntax instead of the user's statement.
The derive MUST stamp every generated node with the source span of the statement it came from, or `do` interacts
badly with the diagnostics work (the #1 ergonomics item). A parser-level `do` would get span locality for free; the
macro trades that for stdlib-consistency and revertibility, so budget the span-stamping explicitly.

**Bang (`!`) as inline bind — follow-on.** `f(!e)` inside a `do` desugars to `and_then(e, fn(x$) -> f(x$))` (Idris
bang-notation), letting `match !subject_receive(s,100) { … }` collapse the bind. Term-level partner of Cure's
**type-level** `! Effects` annotation; disambiguated by position (postfix/type-row vs prefix bang). Ship `do` first.

**Interaction with §0 (no match-through):** `do` never peels an effect scrutinee. `match e` where `e : Effect(T)` is
still an error inside `do`; you write `x <- e` then `match x`, or `match !e`. Every sequencing point stays visible —
a feature. Also (§0.1): reply *handling* is in `Effect`, reply *logic* is pure — `r <- call(s, q); pure(f(r))`.

**Implementation:** a `Std.Monad` module (the `Monad` interface + `Effect`/`Option`/`Result`/… instances) + the
`do` macro (a `syntax`/derive rule). P change is only the `<-` token (option a). E change is only ordinary interface
coherence for `and_then` (which exists). No K change.

**Tests:** the Subject/Selector examples rewritten in `do` (compile + run, identical results to the `let _ =`
versions); bare-statement discard; `<-` bind; pure `let` inside `do`; final-expression auto-`pure`; a negative
(`match` on an unbound effect scrutinee still errors). Later: `do` over `Option`/`Result`.

---

## 5. `beam_ops` evolution: subtract the aliases, add a `receive`/`select` block

**Insight:** once `do` exists, most of `beam_ops` is redundant. `beam_ops` today is two things: (a) a per-verb
*alias* macro (`beam_ops call s req` → `Std.Otp.call(s, req)` — actually *more* keystrokes than `call(s, req)`), and
(b) a *reserved-word bridge* for verbs that collide with keywords (`send` is the reserved Melquiades word;
`spawn`/`self` are keyword-ish). Inside a `do` block with `use Std.Otp`, every effectful op is just its function,
sequenced — strictly nicer than the prefix. So the ergonomic move is **subtractive**, plus one genuinely macro-shaped
addition.

**(a) Retire the per-verb aliases.** `call`/`cast`/`tell`/`stop`/`monitor`/`link`/`timer`… become plain functions in
`do`. Deprecate the corresponding `beam_ops` rules (keep them during a deprecation window; remove after). This is a
minor breaking change — hence the window.

**(b) Keep a slim reserved-word bridge.** Only the verbs that can't be plain calls (`send`/`spawn`/`self`) need a
syntactic form — a handful of `beam_ops` rules, or dedicated operators (the Melquiades `pid <-| msg` already gives
`send` an operator). Everything else is a function.

**(c) Add a typed `receive`/`select` block — the one thing `do` + functions can't express.** Sequencing is `do`'s
job; *dispatching heterogeneous inbound subjects to pattern arms* is not (it has a `match`-like arm structure). This
is where a macro earns its place (the "real macro win" from the parity work):
```
receive within 100
  commands as c -> handle_cmd(c)
  notes    as n -> handle_note(n)
  timeout      -> retry()
```
desugars to: build a `Selector` (`new_selector() |> select_map(commands, fn(c) -> …) |> …`), `selector_receive`, and
`match` the resulting `Option`, with the `timeout` arm as the `None` case. Built programmatically like
`derive_behavior_family` (avoids the `becomes`-template walls), spans stamped per arm, and its safety is exactly what
`Otp.Meta.SelectiveReceive` already proves. Purely additive.

**Net surface:** `do` for "perform these effects in order," `receive`/`select` for "wait on these typed channels,"
plain functions for everything else, a tiny reserved-word bridge for `send`/`spawn`/`self`. Fewer, more coherent
surfaces — as close to Gleam's ergonomics as possible while keeping the effect discipline.

## Sequencing & risk summary

| Feature | Layer | New Core? | Risk | Depends on |
|---|---|---|---|---|
| 3. let/where inference | E | no | medium (over-postponement) | — |
| 4. `do` (macro + `Monad` iface) | stdlib + P (`<-` token) + E (coherence) | no | low–medium (span-stamping) | benefits from 3 |
| 1. leading `|>` | P (lexer) | no | low–medium (indent stack) | — |
| 2. `where` | P + E | no | medium (lambda-lift + A6) | benefits from 3 |
| 5a. retire `beam_ops` aliases | stdlib | no | low (deprecation window) | 4 |
| 5b. `receive`/`select` block | stdlib macro (derive) | no | medium (macro + spans) | Subject/Selector (done) |
| 4b. `!`-bang inline | stdlib macro + P | no | low | 4 |

The load order that maximises early payoff: **inference (3)** removes the annotations, then **`do` (4)** removes the
`let _ =` — together they clean up every OTP example — then **`|>` (1)** and **`where` (2)** polish readability, and
**§5** reshapes the OTP surface (`do` + functions replace the `beam_ops` aliases; a `receive`/`select` block adds the
one control shape they can't express). `do` is a **stdlib macro over a `Monad` interface** whose `Effect` instance is
the existing `let`-bind, so nothing touches the kernel; all features are additive and independently revertible.
`Effect` stays as-is (§0): distinct type, `pure` in, no safe `run` out, extraction only via bind, boundary at the
runtime. Cross-check every step against the full gate (parser/elaborator changes are broad); for `where`, keep an
explicit A6 proof-regression guard; for `do`/`receive`, verify per-statement/per-arm source spans in error messages.
