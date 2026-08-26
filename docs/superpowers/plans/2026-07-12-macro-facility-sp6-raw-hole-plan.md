# SP6 Tier-5 Raw Hole Foundation

## Goal

Add the delimited raw-hole representation needed by embedded DSL macros without
opening the whole Cure file to reader replacement.

## Scope

- Parse `<name: raw until delimiter>` as a distinct macro segment carrying the
  hole name, delimiter, and source location.
- Add a pure token capture helper that returns the content before the matching
  delimiter and preserves token positions.
- Keep raw content opaque to ordinary expression parsing.

## Invariants

- Raw capture is delimiter-bounded and reports a missing delimiter.
- No whole-file lexer or reader override is introduced.
- No trusted Core changes.

## Verification

- Parser preserves raw-hole metadata.
- Token capture handles a matching delimiter and missing delimiter.
- Existing macro parser suite remains green.

