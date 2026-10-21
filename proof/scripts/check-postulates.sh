#!/usr/bin/env bash
# Guard the postulate surface of the mechanised soundness development.
#
# The development (proof/, Agda 2.8.0) is allowed exactly the axioms it
# documents in proof/README.md and docs/SOUNDNESS.md:
#
#   * `funext`       (Core/Syntax.agda)     -- function extensionality, the
#                                              single standard axiom;
#   * `tree-decides` (Proof/Soundness.agda) -- LPO on the outcome path (the
#                                              only classical input).
#
# The former second classical input `never-reached→no-value` was REMOVED: it
# is false for the mechanised `_⇝_` (which reduces under binders, so
# `tm-lam g d Ω` is a `Value` that steps to itself forever). Its honest
# replacement, over NORMAL FORMS, is proved with no postulates in
# Proof/SoundnessConfluence.agda (`soundness-nf`).
#
# A NEW `postulate` is a NEW unproven assumption. It must be a deliberate,
# reviewed change -- never an accident of a proof in progress. This script
# makes any change to the postulate surface a CI failure, and prints the
# expected-vs-actual diff so the fix is obvious.
#
# Usage:
#   proof/scripts/check-postulates.sh            # assert the known surface
#   proof/scripts/check-postulates.sh --list     # just print what is found
set -euo pipefail

cd "$(dirname "$0")/.."

# The exact, reviewed postulate surface. Keep this sorted; the comparison
# below is order-sensitive so the list is the source of truth.
EXPECTED=$(
  cat <<'EOF'
Core/Syntax.agda:funext
Proof/Soundness.agda:tree-decides
EOF
)

# Extract every name declared under a `postulate` block. Agda's syntax is a
# bare `postulate` line followed by one or more declarations indented MORE
# than the `postulate` keyword. A declaration is `name : type` (the type may
# continue on further lines); we take the identifier before the first `:`.
#
# Identifiers may contain Unicode (e.g. `→`, `′`), so we cannot restrict to
# ASCII: we take everything up to the first `:` and trim whitespace.
extract_postulates() {
  awk '
    function indent(s,   i) { i = 0; while (substr(s, i+1, 1) == " ") i++; return i }

    # A `postulate` keyword on its own line opens a block at its indent level.
    /^[[:space:]]*postulate[[:space:]]*$/ {
      inblock = 1
      blockindent = indent($0)
      next
    }

    inblock {
      # Blank lines do not end the block.
      if ($0 ~ /^[[:space:]]*$/) next

      thisindent = indent($0)

      # The block ends at the first line indented at or below the keyword.
      if (thisindent <= blockindent) { inblock = 0; next }

      # Skip comment lines (Agda line comments start with `--`); they may
      # contain a `:` and would otherwise be mistaken for a declaration.
      trimmed = $0
      sub(/^[[:space:]]+/, "", trimmed)
      if (trimmed ~ /^--/) next

      # A declaration line starts with an identifier followed by `:`.
      # Continuation lines (the tail of a type) start with a non-identifier
      # character and are skipped.
      if ($0 ~ /^[[:space:]]+[^[:space:]].*:/) {
        line = $0
        sub(/^[[:space:]]+/, "", line)   # trim leading indent
        sub(/[[:space:]]*:.*$/, "", line) # keep only the identifier
        print FILENAME ":" line
      }
    }
  ' "$@" | sort
}

# Generated inputs and future source subdirectories are trust roots too.
# Scope discovery to all Agda sources without changing the reviewed inventory.
shopt -s globstar nullglob
sources=(**/*.agda)
if ((${#sources[@]} == 0)); then
  printf 'No Agda sources found under proof/.\n' >&2
  exit 1
fi
found=$(extract_postulates "${sources[@]}")

if [[ "${1:-}" == "--list" ]]; then
  echo "$found"
  exit 0
fi

if [[ "$found" == "$EXPECTED" ]]; then
  echo "postulate surface OK:"
  echo "$found" | sed 's/^/  /'
  exit 0
fi

echo "postulate surface CHANGED." >&2
echo >&2
echo "expected:" >&2
echo "$EXPECTED" | sed 's/^/  /' >&2
echo >&2
echo "found:" >&2
echo "$found" | sed 's/^/  /' >&2
echo >&2
echo "If a postulate was intentionally added or removed, update" >&2
echo "EXPECTED in proof/scripts/check-postulates.sh AND the status" >&2
echo "sections of proof/README.md and docs/SOUNDNESS.md in the same" >&2
echo "commit." >&2
exit 1
