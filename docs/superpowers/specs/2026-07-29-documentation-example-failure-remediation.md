# Documentation Example Failure Remediation

## Status

Proposed. The documentation checker is authoritative for executable Cure
fences. This specification records how its failures are classified and fixed.

## Goal

Every fence tagged `cure` must either compile with the current language and
stdlib or carry an explicit, reviewed expectation for an intentional compiler
diagnostic. A documentation example must not be made to pass by silently
changing its fence to another language.

## Failure buckets

### Stale or proposed syntax

Examples use syntax that was removed, never released, or exists only in a
roadmap/design document: old `indexed type ... where` declarations, `...`
bodies, legacy FSM/application DSLs, obsolete macro forms, and retired
dependent-type notation.

Remediation:

1. If the document describes current user-facing behavior, rewrite the example
   in current Cure syntax and give it complete type/value context.
2. If it documents a proposal or historical design, retain the example but
   mark it explicitly as pseudocode with a reviewed rationale. It must not be
   counted as an executable Cure example.
3. Never change a current Cure fence to `text` merely to suppress a failure.

### Unsupported expression forms

The parser accepts the source, but elaboration does not support the form in
that position. Fix the compiler only when the syntax is part of the current
language contract; otherwise rewrite the example or classify it as reviewed
pseudocode.

### Missing context or stale names

The snippet contains free variables, missing declarations, or obsolete API
names. Add the smallest surrounding module, type, function, imports, and
values needed to make the example independently meaningful. Shared snippet
support may provide deliberately generic scaffolding, but it must not hide a
public API that the documentation claims users must import.

### Dependent inference failures

The example leaves implicit types or indices unconstrained. Add expected types,
explicit binders, or concrete witnesses. If the example is intended to teach
an unsupported dependent feature, classify it as proposal pseudocode instead
of weakening the checker.

### Intentional diagnostics and warnings

Invalid examples use an `E###` fence tag and must produce exactly that error.
Warnings are failures unless the example explicitly documents and expects the
warning under the checker’s contract.

## Workflow

1. Run `mix cure.check.docs` and capture each failure’s path, fence line,
   diagnostic code, and source category.
2. Fix current examples in the document itself, preserving complete context.
3. Add or update a focused checker regression when runner behavior changes.
4. Rerun the checker and verify that the failure moved to zero or to an
   explicitly reviewed pseudocode/expected-diagnostic category.
5. Keep historical and proposal material separate from everyday executable
   documentation so users are not shown syntax the compiler cannot accept.

## Required final evidence

- zero unexpected failures in current user-facing documentation;
- every remaining non-executable proposal is explicitly classified and
  reported, never silently omitted;
- no fence is converted to another language solely to make the check pass;
- `mix format --check-formatted`, `git diff --check`, and the documentation
  checker pass.
