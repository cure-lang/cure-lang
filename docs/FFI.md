# Foreign Function Interface (`@extern`)

`@extern` is Cure's foreign-function interface. It lets a Cure function stand
in for a function that lives outside Cure -- anything callable on the BEAM:
Erlang/OTP modules (`:erlang`, `:io`, `:math`, ...), Elixir modules, AtomVM NIFs,
or hand-written `Cure.*.Builtins` helpers.

An `@extern` function is a **type-only signature**. You declare its name and
types; the compiler trusts those types and lowers every call to a direct BEAM
remote call. There is no Cure implementation to compile -- the implementation is
the external function.

```cure
@extern(:erlang, :abs, 1)
fn abs(x: Int) -> Int
```

Calling `abs(-42)` at runtime invokes `erlang:abs(-42)`.

## Syntax

```
@extern(<module>, <function>, <arity>)
<visibility?> fn <name>(<typed params>) -> <ReturnType>
```

The decorator takes exactly three arguments:

| Argument | Meaning | Examples |
|----------|---------|----------|
| `<module>` | The target BEAM module | `:erlang`, `:io`, `:math`, `Elixir.MyApp.Native` |
| `<function>` | The target function name (an atom) | `:abs`, `:put_chars`, `:fsm_spawn` |
| `<arity>` | The function's arity; must equal the number of parameters in the head | `0`, `1`, `2` |

### Module names

- **Erlang / OTP modules** are written as plain atoms: `:erlang`, `:io`,
  `:math`, `:lists`, `:maps`.
- **Elixir modules** are written with their fully qualified dotted path under
  the `Elixir.` namespace: `Elixir.MyApp.Native`, `Elixir.Enum`. The
  parser converts the dotted path into the underlying module atom
(`:"Elixir.MyApp.Native"`) for you.

### Visibility

`@extern` composes with the `local` keyword, exactly like a normal function, to
make the FFI binding private to its module:

```cure
@extern(:erlang, :integer_to_binary, 1)
local fn int_to_string(n: Int) -> String
```

## The two rules

A foreign function is opaque to the compiler. Two invariants keep the FFI sound
and honest; both are enforced at type-check time.

### 1. The head must be fully typed (`E056`)

Every parameter must carry a type annotation and a return type must be
declared. The compiler cannot see the external implementation, so the declared
types are the *only* contract it has. Without them the signature would silently
default to `Any` and the type checker would be blind at every call site.

```cure E056
# rejected (E056): parameter `x` and the return type are missing
@extern(:erlang, :abs, 1)
fn abs(x)
```

```cure
@extern(:erlang, :abs, 1)
fn abs(x: Int) -> Int
```

A zero-parameter extern still needs its return type:

```cure
@extern(:math, :pi, 0)
fn pi() -> Float
```

### 2. The declaration must not have a body (`E057`)

An `@extern` function has no Cure body. Codegen lowers it to a direct remote
call, so anything you write as a body is dead code -- never compiled, never
run. To stop that silent discard from misleading a reader, a body is an error.
This applies to both body forms: a `= ...` body and a multi-clause `|`
definition.

```cure E057
# rejected (E057): the `= x` body is ignored by codegen
@extern(:erlang, :abs, 1)
fn abs(x: Int) -> Int = x
```

```cure E057
# rejected (E057): multi-clause bodies are ignored too
@extern(:erlang, :abs, 1)
fn abs(x: Int) -> Int
  | 0 -> 0
  | n -> n
```

```cure
@extern(:erlang, :abs, 1)
fn abs(x: Int) -> Int
```

If you need local logic, write a normal function and call the extern from
inside it:

```cure
@extern(:erlang, :abs, 1)
fn raw_abs(x: Int) -> Int

fn abs_or_zero(x: Int) -> Int =
  pickup
    x < -1000 -> 0
    else      -> raw_abs(x)
```

Run `cure explain E056` or `cure explain E057` for the in-tool reference.

## How it lowers

An `@extern` function compiles to a thin wrapper whose body is a single remote
call. For:

```cure
@extern(:erlang, :abs, 1)
fn abs(x: Int) -> Int
```

codegen emits the Erlang equivalent of:

```erlang
abs(X) -> erlang:abs(X).
```

The parameters are passed straight through to the target function in order. The
wrapper's arity is the number of parameters in the Cure head.

## Type checking and trust

The compiler **trusts** an `@extern` signature; it does not verify the declared
types against the real external function (it cannot -- the function is outside
Cure). At call sites, callers are checked against the declared head as if it
were any other Cure function. The responsibility for matching the external
function's true contract is yours.

A practical consequence: keep the declared types as precise as the external
function actually guarantees. An overly wide type (`Any`) propagates imprecision
into every caller; an overly narrow one invites runtime surprises the checker
will not catch.

## Effects

An earlier version of the compiler inferred a per-`@extern` effect kind
(`:io`, `:state`, `:spawn`, `:extern`, ...) from the target module, as part of
the classic type checker's effect-tracking pass (`Cure.Types.Effects`, added in
v0.15.0). That pass was removed along with the rest of the classic checker and
code generator; the current dependent pipeline does not classify `@extern`
calls by target module or effect kind. The REPL's `:effects expr` command
reports only a coarse pure-vs-effectful verdict based on whether `expr`'s
inferred type is the kernel's `Effect(T)` type former.

## Examples

Erlang stdlib:

```cure
@extern(:erlang, :abs, 1)
fn abs(x: Int) -> Int

@extern(:math, :sqrt, 1)
fn sqrt(x: Float) -> Float

@extern(:io, :put_chars, 1)
fn print(s: String) -> Atom
```

Elixir helpers (note the dotted `Elixir.` module path):

```cure
@extern(Elixir.MyApp.Native, :read_counter, 1)
fn read_counter(key: Atom) -> Int
```

The same name may be bound at several arities, each its own `@extern`:

```cure
@extern(Elixir.MyApp.Native, :get_env, 2)
fn get_env(name: Atom, key: Atom) -> Any

@extern(Elixir.MyApp.Native, :get_env, 3)
fn get_env(name: Atom, key: Atom, default: Any) -> Any
```

## Runtime availability

`@extern` is resolved at runtime by the BEAM, not at compile time by Cure. The
target module and function must exist on the VM that runs the compiled code. A
signature that compiles fine against `:re` or `:httpc`, for example, will still
fail at runtime on a VM (such as AtomVM) that does not ship those modules. When
targeting a constrained runtime, confirm the external function is present
there.

## Related

- `docs/LANGUAGE_SPEC.md` -- the FFI section in the language reference.
- `docs/STDLIB.md` -- the standard library, much of which is `@extern` wrappers.
- `examples/ffi.cure` -- a minimal runnable FFI module.
