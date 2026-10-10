#!/usr/bin/env bash
# Type-check the whole mechanised-soundness development.
#
# Requires Agda 2.8.0 and the Agda standard library registered in
# ~/.config/agda/libraries (see proof/README.md).
set -euo pipefail

cd "$(dirname "$0")"

MODULES=(
  Core/Grade Core/Universe Core/Syntax Core/Value Core/Reduction
  Core/Signature Core/Typing
  Proof/Values Proof/Inversion Proof/CanonicalForms Proof/Substitution
  Proof/Context
  Proof/Progress Proof/Preservation Proof/Soundness
)

fail=0
for m in "${MODULES[@]}"; do
  printf '%-28s ' "$m"
  if out=$(agda "$m.agda" 2>&1); then
    if echo "$out" | grep -qiE 'warning'; then
      echo 'WARNINGS'; echo "$out" | grep -iE 'warning' | head -3; fail=1
    else
      echo 'OK'
    fi
  else
    echo 'FAIL'; echo "$out" | head -20; fail=1
  fi
done

exit "$fail"
