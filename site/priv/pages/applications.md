%{
  title: "Applications",
  description: "First-class OTP applications and BEAM releases. The app container compiles a supervision tree into an Application callback module; cure release packages it as a bootable release.",
  order: 6
}
---

> **0.34 update:** `app` is a transparent macro over ordinary lifted modules,
> callbacks, and checked OTP operations. It lives in `Std.App` and is not
> ambient -- a unit declaring an application must `use Std.App`. The generated
> declarations pass through the same canonical module interfaces and dependent
> kernel as authored Cure code. The release resource and runtime behavior
> described below remain the output contract.

Cure 0.26.0 takes the supervision surface landed in v0.25.0 and wraps it in a full OTP application lifecycle. A project with a single `app` container compiles to three artefacts in one pass:

1. A loaded BEAM module you refer to by the name the container gives it -- `app MyApp` -- carrying `-behaviour(application)` and the three callbacks `start/2`, `stop/1`, and `start_phase/3`.
2. An OTP `<name>.app` resource file written alongside the project artifact set under `_build/cure/project/ebin/`.
3. A bootable BEAM release under `_build/cure/rel/<name>/`, produced on demand by `cure release` (or `mix cure.release`).

The container slots in next to `actor` and `sup` from v0.25.0, but it is far smaller than either: where those carry callback clauses, `app` carries one clause naming a root supervisor.

## The `app` container

The container is deliberately small. An application is its name and the supervisor it starts, and that is the whole grammar:

```cure
use Std.App

app MyApp
  root MyApp.Root
```

- The name is the lifted module's own name, so it must be `Cure.`-prefixed and dotted. `app MyApp` is rejected as an invalid module name.
- `root` is not optional, and it is the only clause. An application that starts nothing is an application the macro has no reason to generate.
- The root is written the way any module is named -- a dotted path naming the `sup` declared alongside it. There is no `sup Name` prefix form and no atom-literal escape hatch inside `root`.

Everything else an application carries -- version, description, dependencies, environment, start phases -- lives in `Cure.toml`, not in the container. The macro's whole job is wiring the OTP callbacks to that root.

### What the macro generates

The expansion is a lifted module carrying the three callbacks OTP asks an application for:

- `start/2` calls `Std.Otp.start_supervisor` on the declared root and returns `Effect(Tuple)`, the ordinary OTP startup tuple after effect erasure.
- `stop/1` returns `:ok`.
- `start_phase/3` returns `:ok` for every phase.

Start phases are therefore a manifest-level feature. `[application].start_phases` is what puts them in the generated `.app` resource; an application that needs real work in a phase overrides `start_phase/3` in its own module rather than declaring it on the `app`.

### Single-`app` enforcement

`Cure.Project.compile_project/2` scans every `.cure` file under `lib/` and fails if more than one `app` container is declared:

```
error: duplicate application
 --> Cure.toml
  | more than one `app` container in the project:
  | lib/foo_app.cure -> app Foo
  | lib/bar_app.cure -> app Bar
```

The same diagnostic fires when the container's name does not match `[application].name` in `Cure.toml` (both names are normalised through `Macro.underscore/1`, so `app MyApp` matches `name = "my_app"`).

## `Cure.toml`: `[application]` and `[release]`

A project that ships an `app` container declares its application metadata next to the existing `[project]` / `[dependencies]` / `[compiler]` tables:

```toml
[project]
name          = "my_app"
version       = "0.1.0"
source_paths  = ["lib"]

[dependencies]

[compiler]
type_check = true
optimize   = true

[application]
name                  = "my_app"
vsn                   = "0.1.0"
description           = ""
applications          = ["logger", "crypto"]
included_applications = []
start_phases          = ["init", "warm_cache"]

[application.env]
port = 4000

[release]
name         = "my_app"
vsn          = "0.1.0"
include_erts = false
applications = ["logger"]
vm_args      = "rel/vm.args"
sys_config   = "rel/sys.config"
```

Notable rules:

- `[application].name` is the source of truth for the emitted `<name>.app` resource. The container's `app Name` just provides the BEAM module identity; the OTP application atom always comes from TOML.
- `[application].start_phases` is authoritative and is the only place phases are declared. It is what emits them into the `.app` resource; the generated `start_phase/3` accepts each of them and returns `:ok`.
- `[application].applications` is the dependency list. The container does not carry one, so there is nothing to merge it with.
- `[release]` is only consulted by `cure release`. Omitting the whole table is fine; every field has a reasonable default derived from `[application]` and the running VM.
- The TOML parser accepts a minimal subset: scalar string / integer / bool / array-of-strings values, plus nested tables for `[application.env]`. Inline tables and mixed-type arrays are rejected.

## `cure release`

Once the project compiles cleanly, `cure release` (or `mix cure.release`) produces a self-contained BEAM release under `_build/cure/rel/<name>/`:

```
_build/cure/rel/my_app/
  lib/<app>-<vsn>/ebin/*.{beam,app}   # every included app
  releases/<vsn>/<name>.rel
  releases/<vsn>/start.boot
  releases/<vsn>/start.script
  releases/<vsn>/sys.config
  releases/<vsn>/vm.args
  bin/<name>                           # POSIX runner script
```

The runner script uses `${ERL:-erl}` so the release can be tested against any Erlang VM on `PATH`. Pass `--include-erts` (or set `[release].include_erts = true`) to bundle ERTS into the release directory itself -- the resulting tree is then fully self-contained.

### Application closure

The boot script needs a complete list of applications. `Cure.Release` seeds it with `:kernel`, `:stdlib`, `:compiler`, `:elixir`, the project's own application atom, and every entry in `[release].applications`. Out-of-tree dependencies must be loaded by the calling VM (typically by Mix when `cure release` runs through `mix cure.release`); the closure is read from the live code path.

### Runtime env access from Cure

`Std.App` is not only the `app` macro — it also wraps `:application` in typed functions, so a running application is reachable without `@extern`. Each one touches VM-global state, so each returns `Effect(...)`:

```cure
use Std.App

fn boot() -> Effect(AppStart) = ensure_all_started(:my_app)
fn port() -> Effect(Int) = env_int(:my_app, :port, 4000)
```

Starting answers the closed type `AppStart = AppStarted | AlreadyStarted | AppStartFailed` rather than an OTP `{ok, _}` tuple. `AlreadyStarted` is a success: OTP reports it as `{ok, []}`, meaning nothing new had to be started.

The typed readers -- `env_int`, `env_atom`, `env_bool`, `env_string` -- each take a fallback and return it when the key is absent *or* holds a value of another shape, which is what makes them total. For anything past a primitive, `env/2` returns `Effect(Option(BeamTerm))` and you narrow it with `Std.Beam`. See [Applications And Releases](https://github.com/cure-lang/cure-lang/blob/main/docs/APP.md) for the whole surface.

## Failure modes

Application and release problems are reported as project-level errors rather than numbered diagnostics -- there is no `E05x` family, and `cure explain` does not know these:

- `{:duplicate_app, [{path, name}, ...]}` -- more than one `app` container under the project's source paths.
- `{:app_name_mismatch, expected, actual}` -- the container's name disagrees with `[application].name` (falling back to `[project].name`).
- `:missing_app_file` -- `cure release` could not find the `.app` resource for an application it was asked to include.

A malformed container fails earlier still, in the macro itself: a name that is not a valid `Cure.`-prefixed module is `{:invalid_module_name, name}`, and a body that does not match the macro's grammar is a `macro_use_mismatch` parse error.

## Full example

[`examples/cure_forge/`](https://github.com/cure-lang/cure-lang/blob/main/examples/cure_forge) is the canonical end-to-end example. It ships as a small Mix project with three Cure source files wiring an application on top of four cooperating actors:

```cure
use Std.App
use Std.Supervisor

sup Forge.Root
  strategy OneForOne()
  intensity 5
  period more(9)
  children
    worker Forge.Metrics as metrics
    worker Forge.Logger as logger
      restart Permanent()
      shutdown Timeout(2000)
    worker Forge.Queue as queue
      restart Transient()
    worker Forge.Pool as pool
      restart Permanent()

app Forge
  root Forge.Root
```

`period` takes a `Positive`, not a plain number: `more(9)` is 10. `intensity` is an ordinary literal. Each child names its kind (`worker` or `supervisor`), its module, and the identity it is known by inside the tree; `restart` and `shutdown` are optional per child.

Each actor owns a narrow responsibility (counting events, buffering log lines, enqueuing work, or running a small worker pool) and exchanges messages with its peers through the Melquiades Operator `<-|`. The accompanying `CureForge` Elixir facade exposes the running tree to `iex -S mix` and to the ExUnit suite, so you can observe the application booting, exercise every actor, watch the supervisor restart a killed worker, and confirm that the `:warm_cache` start phase executed before the first request.

Read the project's [README](https://github.com/cure-lang/cure-lang/blob/main/examples/cure_forge/README.md) for the walk-through and [`docs/APP.md`](https://github.com/cure-lang/cure-lang/blob/main/docs/APP.md) for the on-disk reference that mirrors this page.
