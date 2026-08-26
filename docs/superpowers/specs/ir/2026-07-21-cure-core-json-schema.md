# Cure Canonical Core JSON Schema

**Status:** Normative design specification  
**Version:** `cure-core-0.1`  
**Parent:** `2026-07-21-lean-verified-middle-end-design.md`

## 1. Purpose

This document defines the process boundary between the Cure front end and the
Lean-verified middle-end. The format represents canonical, post-elaboration
Cure Core. It is not source syntax and is not an internal representation for
every compiler pass.

The decoder must reject malformed, unknown, unresolved, or unsupported input.
No JSON field is trusted merely because it contains a type, effect row, or
certificate claim; Lean reconstructs or checks all semantic information.

## 2. Envelope

```json
{
  "schema": "cure-core-0.1",
  "module": "Example",
  "imports": [],
  "data": [],
  "effects": [],
  "definitions": [],
  "concurrency": [],
  "capabilities": [],
  "metadata": {}
}
```

Required fields are `schema`, `module`, and `definitions`. Unknown top-level
fields are rejected in strict mode and preserved only in an explicitly marked
metadata extension in tooling mode. Serialization is deterministic: arrays
are ordered, object keys are canonicalized, and no semantic field depends on
map iteration order.

## 3. Identifiers and bindings

Global identifiers are qualified strings:

```text
Module.Name/arity
```

Local binders use de Bruijn indices. Source names and spans are optional
metadata and never determine binding. Every node may carry:

```json
"origin": {"file": "src.cure", "start": 12, "end": 18, "id": "o42"}
```

Duplicate global definitions, invalid indices, invalid arities, and references
to undeclared globals are rejected.

## 4. Initial schema fragment

### 4.1 Types

The following snippets are grammar notation, not standalone JSON documents;
`<type>`, `<row>`, and similar markers denote recursively embedded objects.

```json
{"kind":"unit"}
{"kind":"bool"}
{"kind":"int"}
{"kind":"named","name":"Module.Type"}
{"kind":"pair","left":<type>,"right":<type>}
{"kind":"sum","left":<type>,"right":<type>}
{"kind":"function","params":[<type>],"result":<type>,"effects":<row>}
{"kind":"computation","result":<type>,"effects":<row>,"index":null}
```

Dependent types use explicit nodes in the schema, even if the first Lean
fragment rejects them:

```json
{"kind":"dependent-function","param":<type>,"body":<type>}
{"kind":"dependent-pair","param":<type>,"body":<type>}
{"kind":"refinement","base":<type>,"predicate":<index-term>}
```

Unsupported dependent nodes produce a versioned diagnostic rather than being
silently erased.

### 4.2 Effects and rows

```json
{
  "labels": [
    {"name":"io.read","category":"primitive","handling":"sealed","control":"ordinary"},
    {"name":"scheduler.yield","category":"suspend","handling":"sealed","control":"suspending"}
  ],
  "tail": null
}
```

Labels are nominal and globally qualified. Category, handling authority, and
control behavior are separate fields. Categories are `primitive`, `abstract`,
`higher-order`, `suspend`, `concurrency`, or `foreign`; `handling` is `open` or
`sealed`; and `control` is `ordinary` or `suspending`. The row tail is either
`null` or an explicit row variable name.

Rows in declarations are checked against the declared effect signatures. A
sealed label cannot be removed by an ordinary user handler.

### 4.3 Values

```json
{"kind":"var","index":0}
{"kind":"literal","type":"int","value":1}
{"kind":"constructor","name":"Option.some","args":[<value>]}
{"kind":"pair","left":<value>,"right":<value>}
{"kind":"lambda","params":[<type>],"body":<computation>}
{"kind":"recursive-lambda","params":[<type>],"body":<computation>}
{"kind":"pure-op","name":"Int.add","args":[<value>,<value>]}
```

Proof terms may be carried as metadata or explicit values, but computations may
not occur inside kernel proof positions.

### 4.4 Computations

```json
{"kind":"return","value":<value>}
{"kind":"let","bound":<computation>,"body":<computation>}
{"kind":"apply","function":<value>,"args":[<value>]}
{"kind":"case","scrutinee":<value>,"branches":[...]}
{"kind":"perform","operation":"io.read","args":[]}
{"kind":"raise","error":<value>}
{"kind":"suspend","operation":"scheduler.yield","args":[]}
{"kind":"handle","body":C,"handler":H}
```

`perform` and `suspend` are computations, never values. A computation stored
for later execution must use an explicitly typed computation-layer wrapper and
retain its latent effect row.

## 5. Actors and deployments

Concurrency declarations contain only generic process operations, message
schemas, callback values with latent computation types, and capability
requirements. Names such as `actor`, `fsm`, `sup`, and `app` must already have
been expanded by Cure macros and must not appear as compiler-owned constructs.
These declarations are checked for effect closure; they do not grant
capabilities implicitly.

## 6. Validation contract

The Lean boundary exposes:

```text
decode : Bytes → Result RawCore Diagnostic
validate : RawCore → Result ValidatedCore Diagnostic
```

Validation checks bindings, declarations, types, rows, arities, constructors,
foreign capabilities, actor references, and supported-fragment restrictions.

Required diagnostics include phase, stable code, message, origin IDs, and
related spans. Resource limits bound JSON size, nesting depth, array lengths,
and total declarations.

## 7. Versioning

Breaking changes increment the schema major version. Additive fields require a
minor version and explicit decoder support. The compiler records the schema
version in generated Core Erlang metadata and build artifacts.

## 8. Initial fixtures

The implementation must include fixtures for:

- pure identity and arithmetic;
- let and case;
- recursion;
- one primitive effect;
- one suspension;
- one invalid de Bruijn index;
- one invalid effect row;
- one unclassified foreign operation;
- one callback with a latent effect;
- one unsupported dependent computation.

The machine-readable validation artifact is
[`cure-core-0.1.schema.json`](cure-core-0.1.schema.json). The JSON Schema is a
structural prefilter; Lean remains authoritative for binding, type, effect, and
semantic validation.
