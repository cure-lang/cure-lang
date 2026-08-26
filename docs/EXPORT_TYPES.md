# Cross-language type export (`cure export-types`, v0.32.0)

`cure export-types` converts Cure record, enum, and ADT type declarations
to schema definitions for a target language. The generated files are
suitable for polyglot systems that need to share a data-layer contract
without hand-writing schemas.

## Supported targets

| Flag | Output |
|------|--------|
| `--target protobuf` | proto3 `.proto` files (default) |

Additional targets (TypeScript, Rust) are planned for future releases.

## Usage

```bash
# Export all project types to proto3
mix cure.export_types

# Export specific files only
mix cure.export_types lib/types.cure lib/events.cure

# Custom output directory
mix cure.export_types --out src/generated/

# Preview without writing files
mix cure.export_types --dry-run

# Verbose: show one line per file processed
mix cure.export_types --verbose
```

Output files are written to `_build/cure/export/protobuf/` by default,
one `.proto` file per `.cure` source file.

## Protobuf type mapping

| Cure type | Proto3 output |
|-----------|---------------|
| `Int` | `int64` |
| `Float` | `double` |
| `Bool` | `bool` |
| `String` | `string` |
| `Bytes` | `bytes` |
| `Atom` | `string` |
| `List(T)` | `repeated <T>` |
| `Option(T)` | `optional <T>` |
| `Result(T, E)` | `bytes` (with comment; see note below) |
| `rec Foo { f: T }` | `message Foo { T f = 1; }` |
| Pure-enum ADT | `enum Foo { FOO_UNSPECIFIED = 0; A = 1; }` |
| Payload ADT | Wrapper `message` + `oneof value { ... }` |
| Refinement type | `bytes` (with E068 warning comment) |
| Dependent type | `bytes` (with E068 warning comment) |

Field names are converted from Cure `camelCase` to proto3 `snake_case`.
Field numbers are assigned in declaration order, starting at `1`.

### Payload-bearing ADTs

A Cure ADT with payload variants maps to a wrapper `message` containing
a `oneof value` block, plus one synthetic `message` per payload variant:

```cure
type Shape = Circle(Int) | Rectangle(Int, Int) | Point
```

becomes:

```proto3
message Shape {
  oneof value {
    ShapeCirclePayload circle = 1;
    ShapeRectanglePayload rectangle = 2;
    bool point = 3;
  }
}

message ShapeCirclePayload {
  int64 value = 1;
}

message ShapeRectanglePayload {
  int64 field1 = 1;
  int64 field2 = 2;
}
```

### Result(T, E)

`Result(T, E)` in field position cannot be inlined as a proto3 `oneof`
because proto3 does not support anonymous wrapper types at the field
level. The exporter emits a `bytes` field with a comment and raises E068.
Wrap the result in a named `rec` to export it cleanly:

```text
rec ApiResponse
  payload: Result(User, Error)   # E068 on this field

# Instead:
type UserResult = Ok(User) | Err(Error)
rec ApiResponse
  payload: UserResult             # exports as oneof
```

## Refinement and dependent types (E068)

Types that carry runtime-irrelevant propositions (refinement predicates,
length indices, etc.) have no direct proto3 representation. The exporter:

1. Replaces the field with `bytes` in the output.
2. Adds a `// E068: <reason>` comment.
3. Emits an `IO.warn/2` diagnostic to stderr.

The export continues; the output is usable, just with an imprecise type
for that field.

To suppress E068 for a field, annotate it with `@export_as`:

```text
rec Account
  @export_as "int64"
  balance: Positive Int
```

The `@export_as` annotation is read by the exporter and used verbatim
as the proto3 type string.

## Error codes

| Code | Meaning |
|------|---------|
| E068 | Export type unmappable -- field replaced by `bytes` with comment |
