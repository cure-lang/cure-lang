# Applications And Releases

`app` is a standard-library macro that creates a transparent lifted
`Application` module. It comes from `Std.App`, which a unit declaring an
application must `use` — nothing here is ambient. Project metadata stays in
`Cure.toml`; the macro's only job is to wire the OTP application callbacks to a
root supervisor. The same module also carries the typed run-time surface for
reaching a running application.

## Declaring An Application

An application is its name and the supervisor it starts. `root` is not
optional — an application that starts nothing is an application the macro has
no reason to generate:

```cure
use Std.App

app Demo
  root Root
```

The root is named the way any module is named, and the supervisor it refers to
is an ordinary `sup` declared alongside it:

```cure
use Std.App
use Std.Supervisor

sup Root
  strategy OneForOne
  children []

app Demo
  root Root
```

## What The Macro Generates

The expansion is a lifted module carrying the three callbacks OTP asks an
application for:

- `start/2` — calls `Std.Otp.start_supervisor` on the declared root and
  returns `Effect(Tuple)`, the ordinary OTP startup tuple after effect erasure.
- `stop/1` — returns `:ok`.
- `start_phase/3` — returns `:ok` for every phase.

Callback results use erased `Effect(...)` types, so pure results and effectful
bodies share one elaboration path.

Start phases are therefore a manifest-level feature, not a macro-level one:
`[application].start_phases` in `Cure.toml` is what puts them in the generated
`.app` resource, and the generated `start_phase/3` accepts each of them. An
application that needs real work in a phase overrides that callback in its own
module rather than declaring it on the `app` line.

## Project Metadata

The application manifest is declared separately:

```toml
[project]
name = "demo"
version = "0.1.0"

[application]
name = "demo"
vsn = "0.1.0"
applications = ["logger", "crypto"]
start_phases = ["warm_cache", "ready"]

[application.env]
port = 4000

[release]
name = "demo"
vsn = "0.1.0"
include_erts = false
```

`Cure.Project.compile_project/2` discovers the lifted application module,
enforces the single-application invariant, checks its name against
`[application].name`, and emits the `<name>.app` resource. Release generation
uses the same compiled modules and manifest data.

## Reaching The Application At Run Time

`Std.App` is not only the macro. The same module wraps OTP's application
controller in typed functions, so starting an application and reading its
environment are ordinary Cure calls. Each one touches VM-global state, so each
returns `Effect(...)`.

Starting answers a closed type rather than an OTP tuple:

```cure
use Std.App

fn boot() -> Effect(AppStart) = ensure_all_started(:demo)

fn running() -> Effect(Bool) =
  let outcome = boot()
  match outcome
    AppStarted()     -> true
    AlreadyStarted() -> true
    AppStartFailed() -> false
```

`AlreadyStarted` is not a failure — OTP reports it as success with an empty list
of newly started applications, and a caller that only asks "is it up" can treat
it exactly like `AppStarted`. The failure case carries no reason, because the
reason OTP supplies is an arbitrary term and typing it as an atom would be a lie
at the boundary. `stop/1` mirrors this: `false` means the application was not
running to begin with.

Environment values arrive as `Option`, since a key that was never set is a real
answer and not an error:

```cure
use Std.App
use Std.Beam
use Std.Option

fn maybe_port() -> Effect(Option(BeamTerm)) = env(:demo, :port)
```

`env/2` hands back an undecoded `BeamTerm` because `[application.env]` may hold
any term at all. When the expected shape is a primitive, the typed readers do
the narrowing and fall back when the key is missing *or* holds something else:

```cure
use Std.App

fn port() -> Effect(Int) = env_int(:demo, :port, 4000)
fn mode() -> Effect(Atom) = env_atom(:demo, :mode, :production)
fn tracing() -> Effect(Bool) = env_bool(:demo, :tracing, false)
fn banner() -> Effect(String) = env_string(:demo, :banner, "demo")
```

The fallback is what makes these total. `env_int(:demo, :port, 4000)` is `4000`
whether `:port` is absent or holds a string — a program reading its own
configuration should not crash over a manifest typo, and the manifest's
`[application.env]` is what decides which answer you actually get.

Anything past these primitives — a list, a nested tuple, a map — comes back from
`env/2` as a `BeamTerm` and is narrowed with `Std.Beam`. Reaching for `@extern`
is only necessary for parts of `:application` this surface does not cover.

## Transparency

The `app` macro expands to ordinary `lift module`, `callback`, and checked
algebra syntax. It does not use an OTP-specific compiler branch, source-string
compilation, or direct code-server loading.
