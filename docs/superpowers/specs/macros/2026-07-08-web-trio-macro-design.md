# The Web Trio — `api`, `view`, `form`: the Elm Architecture, Completed

**Date:** 2026-07-08
**Status:** design (operator-requested). Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
(§7.1); sibling of
[`2026-07-08-protocol-macro-design.md`](2026-07-08-protocol-macro-design.md)
(an `api` route is a two-step session — relation §8, unification ledgered).
All three built as `macro`s (parent §5) — zero compiler special-casing.

---

## 1. Purpose & the Elm-architecture story

`reducer` (parent §5.5) already **is** Elm's update function: the model is a
state-indexed GADT, transitions carry typed `emits`/`rejects` streams, and the
whole thing lowers onto the Flow runtime as a `Signal.scan`. What Elm calls
"the architecture" is three-quarters missing without the rest of the loop.
The trio completes it:

- **`api`** — requests in. Routes with refinement-validated params, total
  handlers, per-request supervision, a generated typed client, OpenAPI export.
- **`view`** — `Signal(Model) -> Html(Msg)`: LiveView-grade server-rendered UI
  on the Flow runtime. Pure function of the model; re-run on model Signal
  changes; diffs shipped over a websocket. Event attributes send typed `Msg`s
  straight into the reducer.
- **`form`** — multi-step input as typestate: step 3's type does not exist
  without step 2's data, and one field declaration produces both client-side
  hints and server-side validation.

The loop is exactly Elm's (and SwiftUI's — that analogy is load-bearing across
this project): messages flow into a `reducer`, the model `Signal` flows into a
`view`, the rendered events flow back as messages. Nothing here is a new
runtime; it is the Flow runtime with HTTP and HTML at its edges.

### Target honesty: host first, device ledgered

AtomVM has **no `:inets`/`:httpc`** — a proven dead-end in this project
(`Std.Http` is on the known-dead list). So **v1 of `api` and `view` targets
host BEAM** (full OTP, generic-unix or server deployment), where HTTP servers
are ordinary. That is not a consolation prize: the trio's natural home is the
host node of a `fleet` — device `Signal`s arriving over `protocol` sessions,
rendered live by `view`, poked by `api`. A minimal **socket-based** HTTP
listener for ESP32-class devices (AtomVM does have socket support) is
technically feasible and genuinely attractive ("your sensor serves its own
status page") — but it is a **ledgered option (§8.1), not v1**. Nothing in the
surfaces below assumes OTP-only machinery except the listener itself, so the
device path stays open.

---

## 2. `api` — routes in, typed all the way down

### 2.1 Surface

```cure
api Todos
  rejects: TodoError                      # NotFound(id: Int) | Invalid(field: String)

  get    /todos                           -> List(Todo)
  get    /todos/$id:{i: Int | i > 0}      -> Todo
  post   /todos  body: NewTodo            -> Todo
  delete /todos/$id:{i: Int | i > 0}      -> Unit

  on get() ->
    store.all()

  on get(id) ->
    store.find(id) else reject NotFound(id)

  on post(body) ->
    store.insert(body)

  on delete(id) ->
    store.remove(id) else reject NotFound(id)
```

- Path params are `$name:{refinement}`; query params and `body:` schemas are
  ordinary (refinable) types, JSON via `codec`.
- Handlers are total Cure; `else reject` names a constructor of the declared
  `rejects` type. Rejections map to HTTP statuses by a declared (or
  convention-default) table — `NotFound -> 404`, `Invalid -> 422`.
- `reject` here is the reducer's `reject`, deliberately: same word, same
  typed-rejection discipline, same explainer vocabulary.

### 2.2 Invisible machinery

- **The parse IS the validation.** Path/query/body schemas compile to indexed
  parsers — the `packet` machinery (parent §6.3) pointed at HTTP. A handler
  body can only ever see an `id : {i: Int | i > 0}`; there is no "validate
  then trust" phase to forget, because an unvalidated value has no type to be
  passed as. Refinement failure is a 400 before user code runs (§5).
- **Route table correct-by-construction** (hiding principle 2): every declared
  route must have exactly one handler and vice versa; a route shadowed by an
  earlier more-general route is a compile error, not a runtime surprise; a
  declared param unused by its handler is flagged. No unreachable routes, no
  unparsed params — inexpressible, not merely rejected.
- **Per-request supervision.** Each request runs in its own supervised
  process; a crashed handler is a clean 500 (with a request id), never a
  crashed server. This is BEAM's founding pitch and Cure gets it for free —
  market it exactly that way.
- **Generated artifacts:** a typed Cure client (`Todos.Client.get_todo(id)`
  with the same refinement on `id` — wrong calls fail at the *caller's*
  compile), and **OpenAPI export** for non-Cure consumers. Refinements export
  as OpenAPI constraints where the vocabulary allows (`minimum`, `pattern`,
  `maxLength`); fidelity limits ledgered (§8.8).
- Sessions on the wire: a route is a two-step `protocol` session
  (request, then response-or-reject) — see §7.

## 3. `view` — the model Signal, rendered

### 3.1 Surface

The HTML surface is a Cure-idiomatic **builder** — indentation-structured
element blocks, one `from` clause per model state, in the same
clause-per-state idiom as `reducer` bodies. Not string templates: templates
reintroduce the untyped hole the whole architecture exists to close.

```cure
view TodoPage over Todos.Model
  from Loading ->
    div class: "page"
      spinner
      p "Fetching your todos…"

  from Loaded with (payload) ->
    div class: "page"
      h1 "Todos (#{payload.items.length})"
      ul
        for item in payload.items
          li key: item.id
            checkbox checked: item.done, on_toggle: Toggle(item.id)
            span item.title
      button on_click: Refresh
        "Refresh"

  from Failed with (payload) ->
    banner level: :error
      p "Couldn't load: #{show(payload.reason)}"
      button on_click: Retry
        "Try again"
```

- Elements are calls (`div`, `ul`, `button`, …) whose children are the
  indented block; attributes are keyword args; text is a string literal or
  interpolation. `for`/`match`/`pickup` work inside blocks — it is ordinary
  Cure expression syntax producing `Html(Msg)` values.
- **Event attributes carry typed `Msg`s** (`on_click: Refresh`,
  `on_toggle: Toggle(item.id)`), which are constructors of the reducer's
  derived `Todos.Msg`. A view cannot emit a message its reducer does not
  handle — the type says so.

### 3.2 Invisible machinery

- **Impossible UI states are unrepresentable.** The model is the reducer's
  state-indexed GADT, so `from Loaded with (payload)` refines the index —
  `payload.items` exists in that clause and is a compile error in
  `from Loading`. The loading spinner **cannot** render beside the error
  banner: there is no model value in which both states hold, so no view code
  can be written that shows both. This is the flagship demo sentence for the
  whole trio.
- **Pure function on the Flow runtime.** `view` elaborates to
  `Signal(Model) -> Html(Msg)` and is re-run whenever the reducer's model
  Signal steps — exactly a SwiftUI `body` / Elm `view`. Server-side, the
  runtime diffs consecutive `Html` trees and ships minimal patches over a
  websocket (LiveView-style); events travel back the same socket as `Msg`s
  into the reducer's input `Event`. One connected client = one supervised
  session process holding the socket; the reducer itself is shared or
  per-session by declaration.
- Coverage: a `view` must have a clause for every reachable model state
  (reachability read off the reducer's edge graph) — a missing state is a
  compile error naming it.
- Raw HTML injection does not exist in the builder; an escape hatch, if any,
  is `unsafe`-marked (ledgered, §8.5). Text nodes are always escaped.

## 4. `form` — wizards as typestate

### 4.1 Surface

```cure
form Signup
  step Account
    email:    Email
    password: {s: String | s.length >= 12}

  step Profile needs Account
    handle:   {s: String | s.length >= 3 and s.length <= 20}
    display:  String = account.email |> local_part()      # defaults may read earlier steps

  step Confirm needs Profile
    accept_tos: {b: Bool | b == true}

  on complete(data) ->                     # data: all three steps, fully refined
    store.create_user(data.account, data.profile)
```

### 4.2 Invisible machinery

- **Step ordering is typestate** — the same GADT-index-per-step machinery as
  `protocol` handles and `driver` init states. `Profile`'s payload type is
  indexed by `Account`'s completed data; a `Confirm` submission without a
  `Profile` in hand is not a runtime check that fires, it is a type that
  does not exist. Skipping, reordering, or replaying steps is inexpressible.
- **One source of truth for validation.** Each field refinement generates
  *both* ends: client-side hints in the rendered form (`maxlength`,
  `minlength`, `pattern`, `min`/`max`, `required` — best-effort projection of
  the refinement into HTML's constraint vocabulary) and the authoritative
  server-side check, which is again just the parse (§2.2). The pitch: you
  cannot have the classic bug where the browser allows what the server
  rejects, because there is exactly one declaration.
- Forms render through `view` (each step is a model state of a derived
  reducer) and submit through `api` (each step transition is a route) — the
  macro wires the trio together so the user declares fields, not plumbing.
- `on complete` receives the concatenated, fully-refined record — total, no
  `Option`s to unwrap, because the types made partial submissions impossible.

## 5. Explainers (parent §4 — errors ARE the UX)

- **Route param refinement failure** (runtime, 400):

  ```
  400 Bad Request
  id must be a positive integer (got -3).
  ```

  The **same explainer text** serves the compile-time route test (a `check`
  template feeding the route its own bad inputs) and the runtime response —
  written once in the macro's `explain` block, field-named, never leaking
  `cannot_unify` shapes.

- **View field not in current state** (compile):

  ```
  error[E170]: in state Loading there is no `items`
    --> todo_page.cure:9
    `items` belongs to the Loaded state. Check the model's `over` block
    (todos.cure:14), or move this element into the `from Loaded` clause.
  ```

- **Form step ordering violation** (compile):

  ```
  error[E171]: step Confirm needs Profile, which is not complete here
    --> signup.cure:31
    Steps run Account -> Profile -> Confirm. A Confirm submission only
    exists once Profile's data does.
  ```

## 6. `check` integration (parent §7.5 — macro-shipped templates)

- **`api`**: every route parses its own generated requests (generators derived
  from the param/body refinements — valid by construction, no discards); every
  rejection produced by any handler is a constructor of the declared
  `rejects` type; generated *invalid* params always yield the 400 explainer,
  never a handler entry.
- **`view`**: renders **every reachable model state without crashing** — the
  state generator is derived from the reducer's own state space and edge
  graph, so the suite is literally "your reducer writes your view's tests."
  Static-discharge applies: states proved unreachable report as such, 0 runs.
- **`form`**: step generators produce valid multi-step submissions end-to-end
  (each step's generator is narrowed by its refinements); out-of-order
  submission attempts are unrepresentable, which the report states as
  *proved by construction* rather than pretending to test them.

## 7. Relations

- **`reducer`** (parent §5.5) — the update function; `view` consumes its model
  Signal, `view`/`form` events feed its input Event. The trio adds no state
  machinery of its own.
- **`protocol`** — an `api` route is a two-step session (request →
  response|reject); lowering `api` onto `protocol` internally is ledgered
  there (protocol spec §10.7) and inherited here (§8.2 references it): unify
  after all three exist, not before.
- **`bot`** (parent §7.3) — same conversation machinery, different transport;
  a `form` wizard and a bot dialogue are the same typestate walk.
- **`schema`** (parent §7.2) — `store.find`/`insert` in §2.1 are schema
  operations; refinements agree end to end because they are the same types.
- **`fleet` / `dashboard`** (parent §7.4) — the flagship deployment: device
  `Signal`s arrive at a host node and render through `view`; `dashboard` is
  morally a pre-built `view` over fleet telemetry.
- **`codec`** — JSON request/response bodies; round-trip properties inherited
  centrally.

## 8. Open decisions (ledger)

1. **Device-hosted mini-server** — socket-based HTTP/1.1 listener on AtomVM
   (sockets exist; `:inets` does not). v1 is host-only; the device listener
   is a follow-up with its own perf/memory budget and a reduced `view`
   story (full-page render, no websocket diffing?). Decide after v1 ships.
2. **Websocket diff protocol** — bespoke, or declared as a Cure `protocol`
   (eating our own dogfood, and folding into protocol spec §10.7's
   api-on-protocol unification)? Leaning protocol-declared; confirm once the
   diff format stabilizes.
3. **Auth / session story** — middleware surface (`api` blocks compose a
   `with auth` layer?), where the session id lives, and how `secret`
   (IFC axis) constrains what a handler may echo into a response.
4. **Static assets** — out of macro scope (serve from a directory,
   pass-through) vs. content-hashed and typed references from `view`.
5. **Raw-HTML escape hatch** — none at all vs. `unsafe raw(s)` per the locked
   holes/unsafe taxonomy. Leaning `unsafe raw`: greppable pressure valve
   beats template-language creep (hiding principle 4).
6. **SSR-only vs. future client compilation** — v1 is server-rendered only;
   compiling `view` to a client-side target later is possible in principle
   but explicitly not designed here.
7. **Streaming responses** — server-sent events / chunked bodies for
   long-lived `Signal`s exposed over `api` (a Signal *is* a stream; the
   surface is obvious, the backpressure story is not).
8. **OpenAPI fidelity for refinements** — arbitrary refinements exceed
   OpenAPI's constraint vocabulary; decide the projection rule (best-effort
   constraints + human-readable `description` of the residue?) and whether
   the export marks lossy fields.

## 9. Non-goals

- **No full Phoenix parity** — no channels-general framework, no asset
  pipeline, no plug ecosystem. The trio is the Elm loop, not a web framework.
- **No JS client-side framework compilation in v1** (§8.6) — server-rendered
  with websocket diffs is the product.
- **No CSS framework opinions** — `class:` is a string; styling is the
  user's business.
- **No GraphQL** — routes with refined params cover the target audience;
  a query language is a different product.
